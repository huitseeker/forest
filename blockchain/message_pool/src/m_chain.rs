// Copyright 2020 ChainSafe Systems
// SPDX-License-Identifier: Apache-2.0, MIT

use super::errors::Error;
use crate::provider::Provider;
use crate::utils::{get_gas_perf, get_gas_reward};
use address::Address;
use async_std::sync::{Arc, RwLock};
use blocks::Tipset;
use encoding::Cbor;
use log::warn;
use message::{Message, SignedMessage};
use num_bigint::BigInt;
use slotmap::{new_key_type, Key, SlotMap};
use std::collections::HashMap;
use std::f64::EPSILON;
use std::{cmp::Ordering, os::unix::process::parent_id};

new_key_type! {
    pub struct NodeKey;
}

struct MChain {
    inner: SlotMap<NodeKey, MChainNode>,
}

impl Default for MChain {
    fn default() -> Self {
        Self {
            inner: SlotMap::with_key(),
        }
    }
}

// Chains is an abstraction of a list of nodes
pub struct Chains {
    pub map: SlotMap<NodeKey, MChainNode>,
    pub key_vec: Vec<NodeKey>,
}

impl std::default::Default for Chains {
    fn default() -> Self {
        Self {
            map: SlotMap::with_key(),
            key_vec: vec![],
        }
    }
}

impl Chains {
    // pushing a chain node will give a key
    pub(crate) fn push(&mut self, chain_node: MChainNode) -> NodeKey {
        let key = self.map.insert(chain_node);
        self.key_vec.push(key);
        key
    }

    pub(crate) fn new() -> Self {
        Self {
            map: SlotMap::with_key(),
            key_vec: vec![],
        }
    }

    // pushes a node into the map, and the corresponding key into key vec
    // and links the last and the inserted node with each other
    // The link is required to compute effective performance of a chain node
    // which depends on previous chain nodes
    pub(crate) fn push_and_link(&mut self, mut cur_chain: MChainNode) {
        if let Some(last_node) = self.last_key() {
            cur_chain.prev = Some(*last_node);
        }
        let cur_node_key = self.push(cur_chain);
        if self.key_vec.len() >= 2 {
            let second_last = self.key_vec.get(self.key_vec.len() - 2).map(|s| *s);
            if let Some(sec_last) = second_last {
                if let Some(last_node) = self.map.get_mut(sec_last) {
                    last_node.next = Some(cur_node_key);
                }
            }
        }
    }

    /// Takes the chain vec and replaces with an empty one
    /// NOTE: it's upto the caller to put back the retrieved chain vec. 
    pub(crate) fn take_chain_vec(&mut self) -> Vec<NodeKey> {
        std::mem::replace(&mut self.key_vec, vec![])
    }

    pub(crate) fn sort(&mut self) {
        let mut chains = std::mem::replace(&mut self.key_vec, vec![]);
        chains.sort_by(|a, b| self.map.get(*b).unwrap().compare(&self.map.get(*a).unwrap()));
        let _ = std::mem::replace(&mut self.key_vec, chains);
    }

    pub(crate) fn sort_effective(&mut self) {
        let mut chains = std::mem::replace(&mut self.key_vec, vec![]);
        chains.sort_by(|a, b| self.map.get(*b).unwrap().cmp_effective(&self.map.get(*a).unwrap()));
        let _ = std::mem::replace(&mut self.key_vec, chains);
    }

    pub(crate) fn sort_range_effective(&mut self, range: std::ops::RangeFrom<usize>) {
        let mut chains = std::mem::replace(&mut self.key_vec, vec![]);
        chains[range].sort_by(|a, b| self.map.get(*b).unwrap().cmp_effective(&self.map.get(*a).unwrap()));
        let _ = std::mem::replace(&mut self.key_vec, chains);
    }

    /// Retrieves the msg chain node by the given NodeKey
    pub(crate) fn get_mut(&mut self, k: NodeKey) -> Option<&mut MChainNode> {
        self.map.get_mut(k)
    }

    /// Retrieves the msg chain node by the given NodeKey along with the data
    /// required to set effective performance of this node.
    pub(crate) fn get_mut_with_prev_eff(&mut self, k: NodeKey) -> (Option<&mut MChainNode>, Option<(f64, i64)>) {
        let a = self.map.get(k);
        let prev = if let Some(a) = a {
            if let Some(a_prev) = a.prev {
                let prev_node = self.map.get(a_prev).unwrap();
                Some((prev_node.eff_perf, prev_node.gas_limit))
            } else {
                None
            }
        } else {
            None
        };

        let b = self.map.get_mut(k);
        (b, prev)
    }

    /// Retrieves the msg chain node by the given NodeKey
    pub(crate) fn get(&self, k: NodeKey) -> Option<&MChainNode> {
        self.map.get(k)
    }

    /// Retrieves the msg chain node at the given index
    pub(crate) fn get_mut_at(&mut self, idx: usize) -> Option<&mut MChainNode> {
        if idx < self.key_vec.len() {
            let key = self.key_vec[idx];
            self.get_mut(key)
        } else {
            None
        }
    }

    pub(crate) fn next_at(&self, idx: usize) -> Option<&MChainNode> {
        if idx < self.key_vec.len() {
            self.key_vec.get(idx).and_then(|idx_key|{
                self.get(*idx_key).and_then(|a| a.next.and_then(|n| self.get(n)))
            })
        } else {
            None
        }
    }

    pub(crate) fn next_mut_at(&mut self, idx: usize) -> Option<&mut MChainNode> {
        if idx < self.key_vec.len() {
            let node_key = *self.key_vec.get(idx).unwrap();
            if let Some(n) = self.map.get(node_key) {
                if let Some(nk) = n.next {
                    self.map.get_mut(nk)
                } else {
                    None
                }
            } else {
                None
            }
        } else {
            None
        }
    }

    pub(crate) fn get_key_at(&self, idx: usize) -> Option<NodeKey> {
        if idx < self.key_vec.len() {
            Some(self.key_vec[idx])
        } else {
            None
        }
    }

    pub(crate) fn prev_mut_at(&mut self, idx: usize) -> Option<&mut MChainNode> {
        if idx < self.key_vec.len() {
            let node_key = *self.key_vec.get(idx).unwrap();
            if let Some(n) = self.map.get(node_key) {
                if let Some(nk) = n.prev {
                    self.map.get_mut(nk)
                } else {
                    None
                }
            } else {
                None
            }
        } else {
            None
        }
    }

    pub(crate) fn prev_at(&self, idx: usize) -> Option<&MChainNode> {
        if idx < self.key_vec.len() {
            self.key_vec.get(idx).and_then(|idx_key|{
                self.get(*idx_key).and_then(|a| a.prev.and_then(|n| self.get(n)))
            })
        } else {
            None
        }
    }

    /// Retrieves the msg chain node at the given index
    pub(crate) fn get_at(&mut self, idx: usize) -> Option<&MChainNode> {
        let key = self.key_vec[idx];
        self.map.get(key)
    }

    // useful when the key vec is taken out of the Chain
    // taking out key vec is necessary in some codebase to get around the borrow checker rules.
    pub(crate) fn get_from_vec(&self, key_vec: &Vec<NodeKey>, idx: usize) -> Option<&MChainNode> {
        let node_key = key_vec[idx];
        self.map.get(node_key)
    }

    // useful when the key vec is taken out of the Chain
    // taking out key vec is necessary in some codebase to get around the borrow checker rules.
    pub(crate) fn get_mut_from_vec(&mut self, key_vec: &Vec<NodeKey>, idx: usize) -> Option<&mut MChainNode> {
        let node_key = key_vec[idx];
        self.map.get_mut(node_key)
    }

    pub(crate) fn place_key_vec_back(&mut self, vec: Vec<NodeKey>) {
        let _ = std::mem::replace(&mut self.key_vec, vec);
    }

    pub(crate) fn len(&self) -> usize {
        self.key_vec.len()
    }

    pub(crate) fn is_empty(&self) -> bool {
        // we should check the map because the pointers on key_vec can go stale.
        self.map.is_empty()
    }

    // returns a mutable reference to the last inserted node
    pub(crate) fn last_mut(&mut self) -> Option<&mut MChainNode> {
        let last = self.key_vec.last();
        if let Some(node_key) = last {
            self.map.get_mut(*node_key)
        } else {
            None
        }
    }

    // returns a mutable reference to the last inserted node
    pub(crate) fn last_key(&self) -> Option<&NodeKey> {
        self.key_vec.last()
    }

    pub(crate) fn invalidate(&mut self, idx: usize) {
        let mut i = idx;
        while let Some(node) = self.get_mut_at(i) {
            node.valid = false;
            node.msgs.clear();
            if node.next.is_some() {
                // convert to iterative
                // self.invalidate(idx + 1);
                node.next = None;
            } else {
                break;
            }
            i += 1;
        }
    }

    pub(crate) fn trim_msgs_at(&mut self, idx: usize, gas_limit: i64, base_fee: &BigInt) {
        let prev = match self.get_at(idx - 1) {
            Some(prev) => Some((prev.eff_perf, prev.gas_limit)),
            None => None,
        };
        let chain_node = self.get_mut_at(idx).unwrap();
        let mut i = chain_node.msgs.len() as i64 - 1;

        while i >= 0 && (chain_node.gas_limit > gas_limit || (chain_node.gas_perf < 0.0)) {
            let gas_reward = get_gas_reward(&chain_node.msgs[i as usize], base_fee);
            chain_node.gas_reward -= gas_reward;
            chain_node.gas_limit -= chain_node.msgs[i as usize].gas_limit();
            if chain_node.gas_limit > 0 {
                chain_node.gas_perf = get_gas_perf(&chain_node.gas_reward, chain_node.gas_limit);
                if chain_node.bp != 0.0 {
                    chain_node.set_eff_perf(prev); 
                }
            } else {
                chain_node.gas_perf = 0.0;
                chain_node.eff_perf = 0.0;
            }
            i -= 1;
        }

        if i < 0 {
            chain_node.msgs = Vec::new();
            chain_node.valid = false;
        } else {
            chain_node.msgs.drain(0..i as usize + 1);
        }

        if chain_node.next.is_some() {
            // let next_node = self.get_mut_at(idx + 1).unwrap();
            self.invalidate(idx + 1);
            // chain_node.next = None;
        }
    }

    /// removes all nodes that are marked as invalid
    /// FIXME: currently a very in-efficient one as we re-allocate
    /// a new slotmap and put only valid entries.
    /// Invariant: this should only be performed before any sorting
    /// or linking happens to the Chains structure.
    pub(crate) fn drop_invalid(&mut self) {
        // remove entries from the map
        let mut slotmap = SlotMap::with_key();
        let mut key_vec = vec![];

        for (idx, i) in self.key_vec.iter().enumerate() {
            let valid = self.map.get(*i).map(|s| s.valid).unwrap();
            if valid {
                let node = self.map[*i].clone();
                let key = slotmap.insert(node);
                key_vec.push(key);
            }
        }
        // remove entries from the key_vec
        self.map = slotmap;
        self.key_vec = key_vec;
    }
}

impl std::ops::Index<usize> for Chains {
    type Output = MChainNode;
    fn index(&self, idx: usize) -> &Self::Output {
        self.map.get(self.key_vec[idx]).unwrap()
    }
}

impl std::ops::IndexMut<usize> for Chains {
    fn index_mut(&mut self, idx: usize) -> &mut Self::Output {
        self.map.get_mut(self.key_vec[idx]).unwrap()
    }
}
/// Represents a node in the MsgChain.
#[derive(Clone, Debug)]
pub struct MChainNode {
    pub msgs: Vec<SignedMessage>,
    pub gas_reward: BigInt,
    pub gas_limit: i64,
    pub gas_perf: f64,
    pub eff_perf: f64,
    pub bp: f64,
    pub parent_offset: f64,
    pub valid: bool,
    pub merged: bool,
    pub next: Option<NodeKey>,
    pub prev: Option<NodeKey>,
}

fn approx_cmp(a: f64, b: f64) -> Ordering {
    if (a - b).abs() < EPSILON {
        Ordering::Equal
    } else {
        a.partial_cmp(&b).unwrap()
    }
}

impl MChainNode {
    pub fn compare(&self, other: &Self) -> Ordering {
        approx_cmp(self.gas_perf, other.gas_perf)
            .then_with(|| self.gas_reward.cmp(&other.gas_reward))
    }

    pub fn set_null_effective_perf(&mut self) {
        if self.gas_perf < 0.0 {
            self.eff_perf = self.gas_perf;
        } else {
            self.eff_perf = 0.0;
        }
    }

    pub fn set_eff_perf(&mut self, prev: Option<(f64, i64)>) {
        let mut eff_perf = self.gas_perf * self.bp;
        if let Some(prev) = prev {
            if eff_perf > 0.0 {
                let prev_eff_perf = prev.0;
                let prev_gas_limit = prev.1;
                let eff_perf_with_parent = (eff_perf * self.gas_limit as f64
                    + prev_eff_perf * prev_gas_limit as f64)
                    / (self.gas_limit + prev_gas_limit) as f64;
                self.parent_offset = eff_perf - eff_perf_with_parent;
                eff_perf = eff_perf_with_parent;
            }
        }
        self.eff_perf = eff_perf;
    }

    #[allow(dead_code)]
    pub(crate) fn cmp_effective(&self, other: &Self) -> Ordering {
        self.merged
            .cmp(&other.merged)
            .then_with(|| (self.gas_perf >= 0.0).cmp(&(other.gas_perf >= 0.0)))
            .then_with(|| approx_cmp(self.eff_perf, other.eff_perf))
            .then_with(|| approx_cmp(self.gas_perf, other.gas_perf))
            .then_with(|| self.gas_reward.cmp(&other.gas_reward))
    }
}

impl std::default::Default for MChainNode {
    fn default() -> Self {
        Self {
            msgs: vec![],
            gas_reward: BigInt::default(),
            gas_limit: 0,
            gas_perf: 0.0,
            eff_perf: 0.0,
            bp: 0.0,
            parent_offset: 0.0,
            valid: true,
            merged: false,
            next: None,
            prev: None,
        }
    }
}

// TODO: needs to have a test case where we create multiple message chains from multiple actors
// we should get disjoint chains in the map.
pub async fn create_message_chains<T>(
    api: &RwLock<T>,
    actor: &Address,
    mset: &HashMap<u64, SignedMessage>,
    base_fee: &BigInt,
    ts: &Tipset,
    chains: &mut Chains,
) -> Result<(), Error>
where
    T: Provider,
{
    // collect all messages and sort
    let mut msgs: Vec<SignedMessage> = mset.values().cloned().collect();
    msgs.sort_by_key(|v| v.sequence());

    // sanity checks:
    // - there can be no gaps in nonces, starting from the current actor nonce
    //   if there is a gap, drop messages after the gap, we can't include them
    // - all messages must have minimum gas and the total gas for the candidate messages
    //   cannot exceed the block limit; drop all messages that exceed the limit
    // - the total gasReward cannot exceed the actor's balance; drop all messages that exceed
    //   the balance
    let a = api.read().await.get_actor_after(&actor, &ts)?;

    let mut cur_seq = a.sequence;
    let mut balance = a.balance;
    let mut gas_limit = 0;

    let mut skip = 0;
    let mut i = 0;
    let mut rewards = Vec::with_capacity(msgs.len());
    while i < msgs.len() {
        let m = &msgs[i];
        if m.sequence() < cur_seq {
            warn!(
                "encountered message from actor {} with nonce {} less than the current nonce {}",
                actor,
                m.sequence(),
                cur_seq
            );
            skip += 1;
            i += 1;
            continue;
        }

        if m.sequence() != cur_seq {
            break;
        }
        cur_seq += 1;
        let min_gas = interpreter::price_list_by_epoch(ts.epoch())
            .on_chain_message(m.marshal_cbor()?.len())
            .total();

        if m.gas_limit() < min_gas {
            break;
        }
        gas_limit += m.gas_limit();
        if gas_limit > types::BLOCK_GAS_LIMIT {
            break;
        }

        let required = m.required_funds();
        if balance < required {
            break;
        }

        balance -= required;
        let value = m.value();
        if &balance >= value {
            balance -= value;
        }
        let gas_reward = get_gas_reward(&m, base_fee);
        rewards.push(gas_reward);
        i += 1;
    }

    // check we have a sane set of messages to construct the chains
    let msgs = if i > skip {
        msgs[skip..i].to_vec()
    } else {
        return Ok(());
    };

    // let mut chains = Chains::new();
    let mut cur_chain = MChainNode::default();

    let new_chain = |m: SignedMessage, i: usize| -> MChainNode {
        let gl = m.gas_limit();
        let node = MChainNode {
            msgs: vec![m],
            gas_reward: rewards[i].clone(),
            gas_limit: gl,
            gas_perf: get_gas_perf(&rewards[i], gl),
            eff_perf: 0.0,
            bp: 0.0,
            parent_offset: 0.0,
            valid: true,
            merged: false,
            prev: None,
            next: None,
        };
        node
    };

    for (i, m) in msgs.into_iter().enumerate() {
        if i == 0 {
            cur_chain = new_chain(m, i);
            continue;
        }

        let gas_reward = cur_chain.gas_reward.clone() + &rewards[i];
        let gas_limit = cur_chain.gas_limit + m.gas_limit();
        let gas_perf = get_gas_perf(&gas_reward, gas_limit);

        // try to add the message to the current chain -- if it decreases the gasPerf, then make a
        // new chain
        if gas_perf < cur_chain.gas_perf {
            chains.push_and_link(cur_chain);
            cur_chain = new_chain(m, i);
        } else {
            cur_chain.msgs.push(m);
            cur_chain.gas_reward = gas_reward;
            cur_chain.gas_limit = gas_limit;
            cur_chain.gas_perf = gas_perf;
        }
    }

    chains.push_and_link(cur_chain);
    // chains.last_mut().unwrap().next = None;

    // merge chains to maintain the invariant
    loop {
        let mut merged = 0;
        for i in (1..chains.len()).rev() {
            if chains[i].gas_perf >= chains[i - 1].gas_perf {
                let chain_i_msg = chains[i].msgs.clone();
                chains[i - 1].msgs.extend(chain_i_msg);
                let chain_i_gas_reward = chains[i].gas_reward.clone();
                chains[i - 1].gas_reward = chain_i_gas_reward;
                let chain_i_gas_limit = chains[i].gas_limit;
                chains[i - 1].gas_limit = chain_i_gas_limit;
                let chain_i_gas_perf =
                    get_gas_perf(&chains[i - 1].gas_reward, chains[i - 1].gas_limit);
                chains[i - 1].gas_perf = chain_i_gas_perf;
                chains[i].valid = false;
                merged += 1;
            }
        }
        if merged == 0 {
            break;
        }

        chains.drop_invalid();
    }

    // TODO (for debugging) remove this: 
    for (i, n) in &chains.map {
        let mut f = std::fs::OpenOptions::new().create(true).append(true).write(true).open("./node_data").unwrap();
        use std::io::Write;
        let a = format!("{:?} : {:?} : {:?}\n", n.prev, i, n.next);
        f.write_all(a.as_bytes());
    }

    Ok(())
}

use rand::seq::SliceRandom;
use rand::thread_rng;

pub(crate) fn shuffle_chains(chains: &mut Chains) {
    chains.key_vec.shuffle(&mut thread_rng());
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_mchain() {}
}
