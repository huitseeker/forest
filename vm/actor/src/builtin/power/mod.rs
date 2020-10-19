// Copyright 2020 ChainSafe Systems
// SPDX-License-Identifier: Apache-2.0, MIT

mod policy;
mod state;
mod types;

pub use self::policy::*;
pub use self::state::*;
pub use self::types::*;
use crate::miner::MinerConstructorParams;
use crate::reward::Method as RewardMethod;
use crate::{
    check_empty_params, init, make_map, make_map_with_root, miner, ActorDowncast, Multimap,
    CALLER_TYPES_SIGNABLE, CRON_ACTOR_ADDR, INIT_ACTOR_ADDR, MINER_ACTOR_CODE_ID,
    REWARD_ACTOR_ADDR, SYSTEM_ACTOR_ADDR,
};
use address::Address;
use ahash::AHashSet;
use fil_types::SealVerifyInfo;
use indexmap::IndexMap;
use ipld_blockstore::BlockStore;
use ipld_hamt::Hamt;
use num_bigint::bigint_ser::{BigIntDe, BigIntSer};
use num_bigint::Sign;
use num_derive::FromPrimitive;
use num_traits::FromPrimitive;
use runtime::{ActorCode, Runtime};
use std::ops::Neg;
use vm::{
    actor_error, ActorError, ExitCode, MethodNum, Serialized, TokenAmount, METHOD_CONSTRUCTOR,
};

// * Updated to specs-actors commit: 17d3c602059e5c48407fb3c34343da87e6ea6586 (v0.9.12)

/// GasOnSubmitVerifySeal is amount of gas charged for SubmitPoRepForBulkVerify
/// This number is empirically determined
pub const GAS_ON_SUBMIT_VERIFY_SEAL: i64 = 34721049;

/// Storage power actor methods available
#[derive(FromPrimitive)]
#[repr(u64)]
pub enum Method {
    /// Constructor for Storage Power Actor
    Constructor = METHOD_CONSTRUCTOR,
    CreateMiner = 2,
    UpdateClaimedPower = 3,
    EnrollCronEvent = 4,
    OnEpochTickEnd = 5,
    UpdatePledgeTotal = 6,
    OnConsensusFault = 7,
    SubmitPoRepForBulkVerify = 8,
    CurrentTotalPower = 9,
}

fn validate_miner_has_claim<BS, RT>(rt: &RT, st: &State, miner: &Address) -> Result<(), ActorError>
where
    BS: BlockStore,
    RT: Runtime<BS>,
{
    let claims: Hamt<_, Claim> = make_map_with_root(&st.claims, rt.store()).map_err(
        |_| actor_error!(ErrIllegalState; "failed to load claim in validate_miner_has_claim"),
    )?;
    let _ = claims
        .get(&miner.to_bytes())
        .map_err(|_| actor_error!(ErrIllegalState; "Failed to look up claim in validate_miner_has_claim"))?
        .ok_or_else(||
            actor_error!(ErrForbidden; "Unknown miner forbidden to interact with power actor"),
        )?;
    Ok(())
}
/// Storage Power Actor
pub struct Actor;
impl Actor {
    /// Constructor for StoragePower actor
    fn constructor<BS, RT>(rt: &mut RT) -> Result<(), ActorError>
    where
        BS: BlockStore,
        RT: Runtime<BS>,
    {
        rt.validate_immediate_caller_is(std::iter::once(&*SYSTEM_ACTOR_ADDR))?;

        let empty_map = make_map::<_, ()>(rt.store()).flush().map_err(|e| {
            e.downcast_default(
                ExitCode::ErrIllegalState,
                "Failed to create storage power state",
            )
        })?;

        let empty_mmap = Multimap::new(rt.store()).root().map_err(|e| {
            e.downcast_default(
                ExitCode::ErrIllegalState,
                "Failed to get empty multimap cid",
            )
        })?;

        let st = State::new(empty_map, empty_mmap);
        rt.create(&st)?;
        Ok(())
    }

    fn create_miner<BS, RT>(
        rt: &mut RT,
        params: CreateMinerParams,
    ) -> Result<CreateMinerReturn, ActorError>
    where
        BS: BlockStore,
        RT: Runtime<BS>,
    {
        rt.validate_immediate_caller_type(CALLER_TYPES_SIGNABLE.iter())?;
        let value = rt.message().value_received().clone();
        let seal_type = params.seal_proof_type;
        println!("params : {:?}", params.multiaddrs);

        let constructor_params = Serialized::serialize(MinerConstructorParams {
            owner: params.owner,
            worker: params.worker,
            seal_proof_type: params.seal_proof_type,
            peer_id: params.peer,
            multi_addresses: params.multiaddrs,
            control_addresses: Default::default(),
        })?;

        let init::ExecReturn {
            id_address,
            robust_address,
        } = rt
            .send(
                *INIT_ACTOR_ADDR,
                init::Method::Exec as u64,
                Serialized::serialize(init::ExecParams {
                    code_cid: MINER_ACTOR_CODE_ID.clone(),
                    constructor_params,
                })?,
                value,
            )?
            .deserialize()?;

        rt.transaction(|st: &mut State, rt| {
            let mut claims = make_map_with_root(&st.claims, rt.store()).map_err(|e| {
                e.downcast_default(ExitCode::ErrIllegalState, "failed to load claims")
            })?;
            set_claim(
                &mut claims,
                &id_address,
                Claim {
                    seal_proof_type: seal_type,
                    ..Default::default()
                },
            )
            .map_err(|e| {
                e.downcast_default(
                    ExitCode::ErrIllegalState,
                    "failed to put power in claimed table while creating miner",
                )
            })?;
            st.miner_count += 1;

            st.claims = claims.flush().map_err(|e| {
                e.downcast_default(ExitCode::ErrIllegalState, "failed to flush claims")
            })?;
            Ok(())
        })?;
        Ok(CreateMinerReturn {
            id_address,
            robust_address,
        })
    }

    /// Adds or removes claimed power for the calling actor.
    /// May only be invoked by a miner actor.
    fn update_claimed_power<BS, RT>(
        rt: &mut RT,
        params: UpdateClaimedPowerParams,
    ) -> Result<(), ActorError>
    where
        BS: BlockStore,
        RT: Runtime<BS>,
    {
        rt.validate_immediate_caller_type(std::iter::once(&*MINER_ACTOR_CODE_ID))?;
        let miner_addr = *rt.message().caller();

        rt.transaction(|st: &mut State, rt| {
            let mut claims = make_map_with_root(&st.claims, rt.store()).map_err(|e| {
                e.downcast_default(ExitCode::ErrIllegalState, "failed to load claims")
            })?;

            st.add_to_claim(
                &mut claims,
                &miner_addr,
                &params.raw_byte_delta,
                &params.quality_adjusted_delta,
            )
            .map_err(|e| {
                e.downcast_default(
                    ExitCode::ErrIllegalState,
                    format!(
                        "failed to update power raw {}, qa {}",
                        params.raw_byte_delta, params.quality_adjusted_delta,
                    ),
                )
            })?;

            st.claims = claims.flush().map_err(|e| {
                e.downcast_default(ExitCode::ErrIllegalState, "failed to flush claims")
            })?;
            Ok(())
        })
    }

    fn enroll_cron_event<BS, RT>(
        rt: &mut RT,
        params: EnrollCronEventParams,
    ) -> Result<(), ActorError>
    where
        BS: BlockStore,
        RT: Runtime<BS>,
    {
        rt.validate_immediate_caller_type(std::iter::once(&*MINER_ACTOR_CODE_ID))?;
        let miner_event = CronEvent {
            miner_addr: *rt.message().caller(),
            callback_payload: params.payload.clone(),
        };

        // Ensure it is not possible to enter a large negative number which would cause
        // problems in cron processing.
        if params.event_epoch < 0 {
            return Err(actor_error!(ErrIllegalArgument;
                "cron event epoch {} cannot be less than zero", params.event_epoch));
        }

        rt.transaction(|st: &mut State, rt| {
            let mut events =
                Multimap::from_root(rt.store(), &st.cron_event_queue).map_err(|e| {
                    e.downcast_default(ExitCode::ErrIllegalState, "failed to load cron events")
                })?;

            st.append_cron_event(&mut events, params.event_epoch, miner_event)
                .map_err(|e| {
                    e.downcast_default(ExitCode::ErrIllegalState, "failed to enroll cron event")
                })?;

            st.cron_event_queue = events.root().map_err(|e| {
                e.downcast_default(ExitCode::ErrIllegalState, "failed to flush cron events")
            })?;
            Ok(())
        })?;
        Ok(())
    }

    fn on_epoch_tick_end<BS, RT>(rt: &mut RT) -> Result<(), ActorError>
    where
        BS: BlockStore,
        RT: Runtime<BS>,
    {
        rt.validate_immediate_caller_is(std::iter::once(&*CRON_ACTOR_ADDR))?;

        Self::process_batch_proof_verifies(rt)?;
        Self::process_deferred_cron_events(rt)?;

        let this_epoch_raw_byte_power = rt.transaction(|st: &mut State, rt| {
            let (raw_byte_power, qa_power) = st.current_total_power();
            st.this_epoch_pledge_collateral = st.total_pledge_collateral.clone();
            st.this_epoch_quality_adj_power = qa_power;
            st.this_epoch_raw_byte_power = raw_byte_power;
            // we can now assume delta is one since cron is invoked on every epoch.
            st.update_smoothed_estimate(1);

            st.last_processed_cron_epoch = rt.curr_epoch();
            Ok(Serialized::serialize(&BigIntSer(
                &st.this_epoch_raw_byte_power,
            )))
        })?;

        // Update network KPA in reward actor
        rt.send(
            *REWARD_ACTOR_ADDR,
            RewardMethod::UpdateNetworkKPI as MethodNum,
            this_epoch_raw_byte_power?,
            TokenAmount::from(0),
        )
        .map_err(|e| e.wrap("failed to update network KPI with reward actor"))?;
        println!("Send 276");

        Ok(())
    }

    fn update_pledge_total<BS, RT>(rt: &mut RT, pledge_delta: TokenAmount) -> Result<(), ActorError>
    where
        BS: BlockStore,
        RT: Runtime<BS>,
    {
        rt.validate_immediate_caller_type(std::iter::once(&*MINER_ACTOR_CODE_ID))?;
        rt.transaction(|st: &mut State, rt| {
            validate_miner_has_claim(rt, st, &rt.message().caller())?;
            st.add_pledge_total(pledge_delta);
            Ok(())
        })
    }

    fn on_consensus_fault<BS, RT>(rt: &mut RT, pledge_delta: TokenAmount) -> Result<(), ActorError>
    where
        BS: BlockStore,
        RT: Runtime<BS>,
    {
        rt.validate_immediate_caller_type(std::iter::once(&*MINER_ACTOR_CODE_ID))?;
        let miner_addr = *rt.message().caller();

        rt.transaction(|st: &mut State, rt| {
            let mut claims = make_map_with_root(&st.claims, rt.store()).map_err(|e| {
                e.downcast_default(ExitCode::ErrIllegalState, "failed to load claims")
            })?;

            let (raw_byte_power, quality_adj_power) = get_claim(&claims, &miner_addr)
                .map_err(|e| {
                    e.downcast_default(
                        ExitCode::ErrIllegalState,
                        "failed to read claimed power for fault",
                    )
                })?
                .map(|claim| {
                    (
                        claim.raw_byte_power.clone(),
                        claim.quality_adj_power.clone(),
                    )
                })
                .ok_or_else(|| {
                    actor_error!(ErrNotFound;
                        "miner {} not registered (already slashed?)", miner_addr)
                })?;
            assert_ne!(raw_byte_power.sign(), Sign::Minus);
            assert_ne!(quality_adj_power.sign(), Sign::Minus);

            st.add_to_claim(
                &mut claims,
                &miner_addr,
                &raw_byte_power.neg(),
                &quality_adj_power.neg(),
            )
            .map_err(|e| {
                e.downcast_default(
                    ExitCode::ErrIllegalState,
                    format!("could not add to claim for {}", miner_addr),
                )
            })?;

            st.add_pledge_total(pledge_delta.neg());

            // delete miner actor claims
            claims
                .delete(&miner_addr.to_bytes())
                .map_err(|e| {
                    e.downcast_default(
                        ExitCode::ErrIllegalState,
                        format!("failed to remove miner {}", miner_addr),
                    )
                })?
                .ok_or_else(|| {
                    actor_error!(
                        ErrIllegalState,
                        "failed to remove miner {}: does not exist",
                        miner_addr
                    )
                })?;

            st.miner_count -= 1;

            st.claims = claims.flush().map_err(|e| {
                e.downcast_default(ExitCode::ErrIllegalState, "failed to flush claims")
            })?;
            Ok(())
        })?;

        Ok(())
    }

    fn submit_porep_for_bulk_verify<BS, RT>(
        rt: &mut RT,
        seal_info: SealVerifyInfo,
    ) -> Result<(), ActorError>
    where
        BS: BlockStore,
        RT: Runtime<BS>,
    {
        println!("IN submit posrsp func");
        rt.validate_immediate_caller_type(std::iter::once(&*MINER_ACTOR_CODE_ID))?;
        let state: State = rt.state().unwrap();
        validate_miner_has_claim(rt, &state, &rt.message().caller())?;
        println!("Passed first check");

        rt.transaction(|st: &mut State, rt: &mut RT| {
            let miner_addr = rt.message().caller();
            println!("Caller has address {:?}", miner_addr);
            validate_miner_has_claim(rt, st, &miner_addr)?;
            let mut mmap = if let Some(ref batch) = st.proof_validation_batch {
                Multimap::from_root(rt.store(), batch).map_err(|e| {
                    e.downcast_default(
                        ExitCode::ErrIllegalState,
                        "failed to load proof batching set",
                    )
                })?
            } else {
                Multimap::new(rt.store())
            };
            let arr = mmap
                .get::<SealVerifyInfo>(&miner_addr.to_bytes())
                .map_err(|e| {
                    e.downcast_default(
                        ExitCode::ErrIllegalState,
                        format!("failed to get seal verify infos at addr {}", miner_addr),
                    )
                })?;
            if let Some(arr) = arr {
                if arr.count() >= MAX_MINER_PROVE_COMMITS_PER_EPOCH {
                    return Err(actor_error!(ErrTooManyProveCommits;
                        "miner {} attempting to prove commit over {} sectors in epoch",
                        miner_addr, MAX_MINER_PROVE_COMMITS_PER_EPOCH));
                }
            }

            mmap.add(miner_addr.to_bytes().into(), seal_info)
                .map_err(|e| {
                    e.downcast_default(ExitCode::ErrIllegalState, "failed to insert proof into set")
                })?;

            let mmrc = mmap.root().map_err(|e| {
                e.downcast_default(
                    ExitCode::ErrIllegalState,
                    "failed to flush proofs batch map",
                )
            })?;

            rt.charge_gas("OnSubmitVerifySeal", GAS_ON_SUBMIT_VERIFY_SEAL)?;
            st.proof_validation_batch = Some(mmrc);
            Ok(())
        })?;

        Ok(())
    }

    /// Returns the total power and pledge recorded by the power actor.
    /// The returned values are frozen during the cron tick before this epoch
    /// so that this method returns consistent values while processing all messages
    /// of an epoch.
    fn current_total_power<BS, RT>(rt: &mut RT) -> Result<CurrentTotalPowerReturn, ActorError>
    where
        BS: BlockStore,
        RT: Runtime<BS>,
    {
        rt.validate_immediate_caller_accept_any()?;
        let st: State = rt.state()?;

        Ok(CurrentTotalPowerReturn {
            raw_byte_power: st.this_epoch_raw_byte_power,
            quality_adj_power: st.this_epoch_quality_adj_power,
            pledge_collateral: st.this_epoch_pledge_collateral,
            quality_adj_power_smoothed: st.this_epoch_qa_power_smoothed,
        })
    }

    fn process_batch_proof_verifies<BS, RT>(rt: &mut RT) -> Result<(), ActorError>
    where
        BS: BlockStore,
        RT: Runtime<BS>,
    {
        // Index map is needed here to preserve insertion order, miners must be iterated based
        // on order iterated through multimap.
        let mut verifies = IndexMap::new();
        rt.transaction(|st: &mut State, rt| {
            if st.proof_validation_batch.is_none() {
                return Ok(());
            }
            let mmap = Multimap::from_root(rt.store(), st.proof_validation_batch.as_ref().unwrap())
                .map_err(|e| {
                    e.downcast_default(
                        ExitCode::ErrIllegalState,
                        "failed to load proofs validation batch",
                    )
                })?;

            let claims: Hamt<_, Claim> = make_map_with_root(&st.claims, rt.store())
                .map_err(|_| actor_error!(ErrIllegalState; "Failed to load claims"))?;

            mmap.for_all::<_, SealVerifyInfo>(|k, arr| {
                let addr = Address::from_bytes(&k.0).map_err(|e| {
                    actor_error!(ErrIllegalState, "failed to parse address key: {}", e)
                })?;

                let found = claims
                    .get(&addr.to_bytes())
                    .map_err(|_| actor_error!(ErrIllegalState;"failed to look up claim"))?;

                if found.is_none() {
                    return Ok(());
                }

                let mut infos = Vec::new();
                arr.for_each(|_, svi| {
                    infos.push(svi.clone());
                    Ok(())
                })
                .map_err(|e| {
                    e.downcast_default(
                        ExitCode::ErrIllegalState,
                        format!(
                            "failed to iterate over proof verify array for miner {}",
                            addr
                        ),
                    )
                })?;

                verifies.insert(addr, infos);
                Ok(())
            })
            .map_err(|e| {
                e.downcast_default(ExitCode::ErrIllegalState, "failed to iterate proof batch")
            })?;

            st.proof_validation_batch = None;
            Ok(())
        })?;

        // TODO update this to not need to create vector to verify these things (ref batch_v_s)
        let verif_arr: Vec<(Address, &Vec<SealVerifyInfo>)> =
            verifies.iter().map(|(a, v)| (*a, v)).collect();
        let res = rt
            .syscalls()
            .batch_verify_seals(verif_arr.as_slice())
            .map_err(|e| e.downcast_default(ExitCode::ErrIllegalState, "failed to batch verify"))?;

        for (m, verifs) in verifies.iter() {
            let vres = res.get(m).ok_or_else(
                || actor_error!(ErrNotFound; "batch verify seals syscall implemented incorrectly"),
            )?;

            let mut seen = AHashSet::<_>::new();
            let mut successful = Vec::new();
            for (i, &r) in vres.iter().enumerate() {
                if r {
                    let snum = verifs[i].sector_id.number;
                    if seen.contains(&snum) {
                        continue;
                    }
                    seen.insert(snum);
                    successful.push(snum);
                }
            }
            // Result intentionally ignored
            let _ = rt.send(
                *m,
                miner::Method::ConfirmSectorProofsValid as MethodNum,
                Serialized::serialize(&miner::ConfirmSectorProofsParams {
                    sectors: successful,
                })?,
                Default::default(),
            );
        }
        Ok(())
    }

    fn process_deferred_cron_events<BS, RT>(rt: &mut RT) -> Result<(), ActorError>
    where
        BS: BlockStore,
        RT: Runtime<BS>,
    {
        let rt_epoch = rt.curr_epoch();
        let mut cron_events = Vec::new();
        rt.transaction(|st: &mut State, rt| {
            let mut events =
                Multimap::from_root(rt.store(), &st.cron_event_queue).map_err(|e| {
                    e.downcast_default(ExitCode::ErrIllegalState, "failed to load cron events")
                })?;

            let claims: Hamt<BS, Claim> =
                make_map_with_root(&st.claims, rt.store()).map_err(|e| {
                    e.downcast_default(ExitCode::ErrIllegalState, "failed to load claims")
                })?;

            for epoch in st.first_cron_epoch..rt_epoch + 1 {
                let epoch_events = load_cron_events(&events, epoch).map_err(|e| {
                    e.downcast_default(
                        ExitCode::ErrIllegalState,
                        format!("failed to load cron events at {}", epoch),
                    )
                })?;

                if epoch_events.is_empty() {
                    continue;
                }

                for event in &epoch_events {
                    if let Ok(Some(_)) = claims.get(&event.miner_addr.to_bytes()) {
                        cron_events.push(event.clone());
                    }
                }

                //cron_events.append(&mut epoch_events);

                events.remove_all(&epoch_key(epoch)).map_err(|e| {
                    e.downcast_default(
                        ExitCode::ErrIllegalState,
                        format!("failed to clear cron events at {}", epoch),
                    )
                })?;
            }

            st.first_cron_epoch = rt_epoch + 1;
            st.cron_event_queue = events.root().map_err(|e| {
                e.downcast_default(ExitCode::ErrIllegalState, "failed to flush events")
            })?;

            Ok(())
        })?;

        let mut failed_miner_crons = Vec::new();
        for event in cron_events {
            let res = rt.send(
                event.miner_addr,
                miner::Method::OnDeferredCronEvent as MethodNum,
                event.callback_payload,
                Default::default(),
            );
            // If a callback fails, this actor continues to invoke other callbacks
            // and persists state removing the failed event from the event queue. It won't be tried again.
            // Failures are unexpected here but will result in removal of miner power
            // A log message would really help here.
            if let Err(e) = res {
                log::warn!(
                    "OnDeferredCronEvent failed for miner {}: res {}",
                    event.miner_addr,
                    e
                );
                failed_miner_crons.push(event.miner_addr)
            }
        }
        rt.transaction(|st: &mut State, rt| {
            let mut claims = make_map_with_root(&st.claims, rt.store()).map_err(|e| {
                e.downcast_default(ExitCode::ErrIllegalState, "failed to load claims")
            })?;

            // Remove power and leave miner frozen
            for miner_addr in failed_miner_crons {
                let (rbp, qap) = match get_claim(&claims, &miner_addr) {
                    Err(e) => {
                        log::error!(
                            "failed to get claim for miner {} after \
                            failing OnDeferredCronEvent: {}",
                            miner_addr,
                            e
                        );
                        continue;
                    }
                    Ok(None) => {
                        log::warn!(
                            "miner OnDeferredCronEvent failed for miner {} with no power",
                            miner_addr
                        );
                        continue;
                    }
                    Ok(Some(claim)) => (
                        claim.raw_byte_power.clone(),
                        claim.quality_adj_power.clone(),
                    ),
                };

                // zero out miner power
                let res = st.add_to_claim(&mut claims, &miner_addr, &rbp.neg(), &qap.neg());
                if let Err(e) = res {
                    log::warn!(
                        "failed to remove power for miner {} after to failed cron: {}",
                        miner_addr,
                        e
                    );
                    continue;
                }
            }

            st.claims = claims.flush().map_err(|e| {
                e.downcast_default(ExitCode::ErrIllegalState, "failed to flush claims")
            })?;
            Ok(())
        })?;
        Ok(())
    }
}

impl ActorCode for Actor {
    fn invoke_method<BS, RT>(
        &self,
        rt: &mut RT,
        method: MethodNum,
        params: &Serialized,
    ) -> Result<Serialized, ActorError>
    where
        BS: BlockStore,
        RT: Runtime<BS>,
    {
        match FromPrimitive::from_u64(method) {
            Some(Method::Constructor) => {
                check_empty_params(params)?;
                Self::constructor(rt)?;
                Ok(Serialized::default())
            }
            Some(Method::CreateMiner) => {
                let res = Self::create_miner(rt, params.deserialize()?)?;
                Ok(Serialized::serialize(res)?)
            }
            Some(Method::UpdateClaimedPower) => {
                Self::update_claimed_power(rt, params.deserialize()?)?;
                Ok(Serialized::default())
            }
            Some(Method::EnrollCronEvent) => {
                Self::enroll_cron_event(rt, params.deserialize()?)?;
                Ok(Serialized::default())
            }
            Some(Method::OnEpochTickEnd) => {
                check_empty_params(params)?;
                Self::on_epoch_tick_end(rt)?;
                Ok(Serialized::default())
            }
            Some(Method::UpdatePledgeTotal) => {
                let BigIntDe(param) = params.deserialize()?;
                Self::update_pledge_total(rt, param)?;
                Ok(Serialized::default())
            }
            Some(Method::OnConsensusFault) => {
                let BigIntDe(param) = params.deserialize()?;
                Self::on_consensus_fault(rt, param)?;
                Ok(Serialized::default())
            }
            Some(Method::SubmitPoRepForBulkVerify) => {
                Self::submit_porep_for_bulk_verify(rt, params.deserialize()?)?;
                Ok(Serialized::default())
            }
            Some(Method::CurrentTotalPower) => {
                check_empty_params(params)?;
                let res = Self::current_total_power(rt)?;
                Ok(Serialized::serialize(res)?)
            }
            None => Err(actor_error!(SysErrInvalidMethod; "Invalid method")),
        }
    }
}
