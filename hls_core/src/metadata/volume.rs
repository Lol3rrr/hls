use crdts::{CmRDT, CvRDT};
use serde::{Deserialize, Serialize};

use super::{Actor, FileMetadata, FilePath};

/// Stores the Metadata for a specific Volume
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VolumeMetadata {
    files: crdts::map::Map<FilePath, FileMetadata, Actor>,
    updates: crdts::VClock<Actor>,
}

impl CmRDT for VolumeMetadata {
    type Op = <crdts::map::Map<FilePath, FileMetadata, Actor> as CmRDT>::Op;
    type Validation = <crdts::map::Map<FilePath, FileMetadata, Actor> as CmRDT>::Validation;

    fn apply(&mut self, op: Self::Op) {
        self.files.apply(op)
    }
    fn validate_op(&self, op: &Self::Op) -> Result<(), Self::Validation> {
        self.files.validate_op(op)
    }
}

impl CvRDT for VolumeMetadata {
    type Validation = <crdts::map::Map<FilePath, FileMetadata, Actor> as CvRDT>::Validation;

    fn merge(&mut self, other: Self) {
        self.files.merge(other.files);
        self.updates.merge(other.updates);
    }
    fn validate_merge(&self, other: &Self) -> Result<(), Self::Validation> {
        self.files.validate_merge(&other.files)
    }
}

impl Default for VolumeMetadata {
    fn default() -> Self {
        Self::new()
    }
}

impl VolumeMetadata {
    /// Create a new Instance
    pub fn new() -> Self {
        Self {
            files: crdts::map::Map::new(),
            updates: crdts::VClock::new(),
        }
    }

    /// Update the Entry for the given File
    ///
    /// # Example
    /// ```rust
    /// # use hls_core::metadata::{FilePath, ChunkId, NodeId, VolumeMetadata};
    /// # let file_path = FilePath::from("/path".to_string());
    /// # let chunk_id = ChunkId::from(0);
    /// # let node_id = NodeId::from("node".to_string());
    ///
    /// let mut volume = VolumeMetadata::new();
    /// assert_eq!(0, volume.update_count(&("test".to_string())));
    /// volume.update(file_path.clone(), "test", |filemeta, ctx| {
    ///     filemeta.update_op(chunk_id, |chunks, ctx| {
    ///         chunks.add_op(node_id, ctx)
    ///     }, ctx)
    /// });
    /// assert_eq!(1, volume.update_count(&("test".to_string())));
    /// ```
    pub fn update<F>(&mut self, file: FilePath, actor: impl Into<Actor>, update: F)
    where
        F: FnOnce(&FileMetadata, crdts::ctx::AddCtx<Actor>) -> <FileMetadata as CmRDT>::Op,
    {
        let actor = actor.into();

        let add_ctx = self.files.read_ctx().derive_add_ctx(actor.clone());
        let op = self.files.update(file, add_ctx, update);
        self.files.apply(op);

        self.updates.apply(self.updates.inc(actor));
    }

    /// Get the current Update count of the Volume
    pub fn update_count(&self, actor: &Actor) -> u64 {
        self.updates.get(actor)
    }
}
