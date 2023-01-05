use std::collections::HashSet;

use crdts::{CmRDT, CvRDT};
use serde::{Deserialize, Serialize};

use super::{Actor, NodeId};

/// The Set of Nodes that store a given Chunk
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ChunkSet(crdts::orswot::Orswot<NodeId, Actor>);

impl Default for ChunkSet {
    fn default() -> Self {
        Self::new()
    }
}

impl crdts::ResetRemove<Actor> for ChunkSet {
    fn reset_remove(&mut self, clock: &crdts::VClock<Actor>) {
        self.0.reset_remove(clock)
    }
}

impl crdts::CmRDT for ChunkSet {
    type Op = <crdts::orswot::Orswot<NodeId, Actor> as CmRDT>::Op;
    type Validation = <crdts::VClock<Actor> as CmRDT>::Validation;

    fn apply(&mut self, op: Self::Op) {
        self.0.apply(op)
    }
    fn validate_op(&self, op: &Self::Op) -> Result<(), Self::Validation> {
        self.0.validate_op(op)
    }
}

impl crdts::CvRDT for ChunkSet {
    type Validation = <crdts::orswot::Orswot<NodeId, Actor> as CvRDT>::Validation;

    fn merge(&mut self, other: Self) {
        self.0.merge(other.0)
    }
    fn validate_merge(&self, other: &Self) -> Result<(), Self::Validation> {
        self.0.validate_merge(&other.0)
    }
}

impl ChunkSet {
    /// Create a new empty List
    pub fn new() -> Self {
        Self(crdts::orswot::Orswot::new())
    }

    /// Adds the given entry to the ChunkSet
    ///
    /// # Example
    /// ```rust
    /// # use hls_core::metadata::{ChunkSet, NodeId};
    /// # let node_id = NodeId::from("test".to_string());
    /// let mut list = ChunkSet::new();
    ///
    /// assert!(!list.contains(&node_id));
    ///
    /// list.add(node_id.clone(), "actor");
    ///
    /// assert!(list.contains(&node_id));
    /// ```
    pub fn add(&mut self, entry: NodeId, actor: impl Into<Actor>) {
        let add_ctx = self.0.read_ctx().derive_add_ctx(actor.into());
        let op = self.0.add(entry, add_ctx);
        self.0.apply(op);
    }

    /// Get the Operation for adding the given Node.
    /// This does not modify the current ChunkSet by itself, only once the Operation has been applied
    pub fn add_op(&self, entry: NodeId, ctx: crdts::ctx::AddCtx<Actor>) -> <Self as CmRDT>::Op {
        self.0.add(entry, ctx)
    }

    /// Remoes the given NodeId from the Set
    pub fn remove(&mut self, entry: NodeId) {
        let rm_ctx = self.0.read_ctx().derive_rm_ctx();
        let op = self.0.rm(entry, rm_ctx);
        self.0.apply(op);
    }

    /// Get the Operation for removign the given Node.
    /// This does not modify the current ChunkSet by itself, only once the Operation has been applied
    pub fn remove_op(&self, entry: NodeId, ctx: crdts::ctx::RmCtx<Actor>) -> <Self as CmRDT>::Op {
        self.0.rm(entry, ctx)
    }

    /// Checks if the ChunkSet contains the given Entry
    pub fn contains(&self, entry: &NodeId) -> bool {
        self.0.contains(entry).val
    }

    /// Gets the ChunkSet as a normal HashSet for other Operations
    pub fn get_set(&self) -> HashSet<NodeId> {
        self.0.read().val
    }
}
