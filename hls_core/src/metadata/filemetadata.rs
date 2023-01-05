use crdts::{CmRDT, CvRDT};
use serde::{Deserialize, Serialize};

use super::{Actor, ChunkId, ChunkSet, NodeId};

/// Stores the Metadata for a single File
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FileMetadata {
    chunks: crdts::map::Map<ChunkId, ChunkSet, Actor>,
}

impl Default for FileMetadata {
    fn default() -> Self {
        Self::new()
    }
}

impl crdts::ResetRemove<Actor> for FileMetadata {
    fn reset_remove(&mut self, clock: &crdts::VClock<Actor>) {
        self.chunks.reset_remove(clock)
    }
}

impl crdts::CmRDT for FileMetadata {
    type Op = <crdts::map::Map<ChunkId, ChunkSet, Actor> as CmRDT>::Op;
    type Validation = <crdts::map::Map<ChunkId, ChunkSet, Actor> as CmRDT>::Validation;

    fn apply(&mut self, op: Self::Op) {
        self.chunks.apply(op)
    }
    fn validate_op(&self, op: &Self::Op) -> Result<(), Self::Validation> {
        self.chunks.validate_op(op)
    }
}

impl CvRDT for FileMetadata {
    type Validation = <crdts::map::Map<ChunkId, ChunkSet, Actor> as CvRDT>::Validation;

    fn merge(&mut self, other: Self) {
        self.chunks.merge(other.chunks)
    }
    fn validate_merge(&self, other: &Self) -> Result<(), Self::Validation> {
        self.chunks.validate_merge(&other.chunks)
    }
}

impl FileMetadata {
    /// Creates a new empty FileMetadata Instance
    pub fn new() -> Self {
        Self {
            chunks: crdts::map::Map::new(),
        }
    }

    /// Load the ChunkSet for a given ChunkId
    pub fn get(&self, chunk: &ChunkId) -> Option<ChunkSet> {
        self.chunks.get(chunk).val
    }

    /// Updates the ChunkSet for the given ID using the provided update function/closure
    ///
    /// # Example
    /// ```rust
    /// # use hls_core::metadata::{FileMetadata, NodeId, ChunkId};
    /// # let chunk_id = ChunkId::from(0);
    /// # let new_node_id = NodeId::from("node".to_string());
    /// let mut filemeta = FileMetadata::new();
    ///
    /// // Previously the Chunk does not exist
    /// assert!(filemeta.get(&chunk_id).is_none());
    ///
    /// // Update the Chunk
    /// filemeta.update(chunk_id.clone(), "test", |set, ctx| {
    ///     set.add_op(new_node_id.clone(), ctx)
    /// });
    ///
    /// // Now the Chunk exists
    /// assert!(filemeta.get(&chunk_id).is_some());
    /// ```
    pub fn update<F>(&mut self, id: ChunkId, actor: impl Into<Actor>, update: F)
    where
        F: FnOnce(&ChunkSet, crdts::ctx::AddCtx<Actor>) -> crdts::orswot::Op<NodeId, Actor>,
    {
        let ctx = self.chunks.read_ctx().derive_add_ctx(actor.into());
        let op = self.update_op(id, update, ctx);
        self.chunks.apply(op);
    }

    /// Returns the Raw Operation that would be executed as part of a [`FileMetadata::update`]
    pub fn update_op<F>(
        &self,
        id: ChunkId,
        update: F,
        ctx: crdts::ctx::AddCtx<Actor>,
    ) -> <Self as CmRDT>::Op
    where
        F: FnOnce(&ChunkSet, crdts::ctx::AddCtx<Actor>) -> crdts::orswot::Op<NodeId, Actor>,
    {
        self.chunks.update(id, ctx, update)
    }

    /// Remove the given ChunkId from the Map
    ///
    /// # Example
    /// ```rust
    /// # use hls_core::metadata::{FileMetadata, NodeId, ChunkId};
    /// # let chunk_id = ChunkId::from(0);
    /// # let new_node_id = NodeId::from("node".to_string());
    /// let mut filemeta = FileMetadata::new();
    ///
    /// // Add the Chunk
    /// filemeta.update(chunk_id.clone(), "test", |set, ctx| {
    ///     set.add_op(new_node_id.clone(), ctx)
    /// });
    /// assert!(filemeta.get(&chunk_id).is_some());
    ///
    /// // Remove the Chunk
    /// filemeta.remove(chunk_id.clone());
    ///
    /// assert!(filemeta.get(&chunk_id).is_none());
    /// ```
    pub fn remove(&mut self, id: ChunkId) {
        let rm_ctx = self.chunks.read_ctx().derive_rm_ctx();
        let op = self.chunks.rm(id, rm_ctx);
        self.chunks.apply(op);
    }
}
