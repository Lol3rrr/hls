//! # Metadata
//! Contains all the Datastructures to manage the Metadata for HLS
//!
//! ## Structure
//! The Metadata for a Volume is stored inside a [`VolumeMetadata`].
//!
//! ## Example
//! ### Managing a single Volume
//! ```rust
//! # use hls_core::metadata::{ChunkId, NodeId, FilePath, VolumeMetadata};
//! let file_path = FilePath::from("/test/path.txt".to_string());
//! let chunk_id = ChunkId::from(0);
//! let node_id = NodeId::from("test".to_string());
//! let mut volume = VolumeMetadata::new();
//!
//! // Add the new Node to the Chunk
//! volume.update(file_path.clone(), "actor1", |chunks, ctx| {
//!     chunks.update_op(chunk_id.clone(), |nodes, ctx| {
//!         nodes.add_op(node_id.clone(), ctx)
//!     }, ctx)
//! });
//!
//! // Load the Metadata for the File we just modified
//! let file_meta = volume.get_file(&file_path)
//!                     .expect("We just previously added some metadata for this file");
//!
//! // Load the Metadata for the Chunk
//! let chunk_nodes = file_meta.get(&chunk_id)
//!                     .expect("We just previously added a Node to the Chunk");
//!
//! assert!(chunk_nodes.contains(&node_id));
//! ```

use std::collections::HashMap;

use crdts::CvRDT;
use serde_derive::{Deserialize, Serialize};

mod chunkset;
pub use chunkset::ChunkSet;

mod filemetadata;
pub use filemetadata::FileMetadata;

mod volume;
pub use volume::VolumeMetadata;

/// Identifies a single Chunk of a given File
#[derive(Debug, Hash, PartialEq, Eq, PartialOrd, Ord, Clone, Serialize, Deserialize)]
pub struct ChunkId(usize);

impl From<usize> for ChunkId {
    fn from(value: usize) -> Self {
        Self(value)
    }
}

/// The Path to a file
#[derive(Debug, Hash, PartialEq, Eq, PartialOrd, Ord, Clone, Serialize, Deserialize)]
pub struct FilePath(String);

impl From<String> for FilePath {
    fn from(value: String) -> Self {
        Self(value)
    }
}

/// The ID of a Node
#[derive(Debug, Hash, PartialEq, Eq, PartialOrd, Ord, Clone, Serialize, Deserialize)]
pub struct NodeId(String);

impl From<String> for NodeId {
    fn from(value: String) -> Self {
        Self(value)
    }
}

/// Identifies a single Volume uniquely
#[derive(Debug, Hash, PartialEq, Eq, PartialOrd, Ord, Clone, Serialize, Deserialize)]
pub struct VolumeId(String);

impl From<String> for VolumeId {
    fn from(value: String) -> Self {
        Self(value)
    }
}

type Actor = String;

/// This holds all the Metadata for a Cluster.
///
/// # Note
/// This Datastructure does not support the removal of Volume entries and is not a CRDT like other
/// Metadata Datastructures.
///
/// # Example
/// ```rust
/// # use hls_core::metadata::{ClusterMetadata, VolumeId};
/// # let volume_id = VolumeId::from("test".to_string());
/// let mut cluster = ClusterMetadata::new();
///
/// let mut volume = cluster.create(volume_id.clone())
///                     .cloned().expect("The Cluster is still empty");
///
/// // Do something with the Volume
/// // ...
///
/// cluster.merge_value(volume_id, volume);
/// ```
pub struct ClusterMetadata {
    volumes: HashMap<VolumeId, VolumeMetadata>,
}

impl Default for ClusterMetadata {
    fn default() -> Self {
        Self::new()
    }
}

impl ClusterMetadata {
    /// Creates a new empty Metadata Instance
    pub fn new() -> Self {
        Self {
            volumes: HashMap::new(),
        }
    }

    /// Get the Metadata for the given VolumeId
    pub fn get(&self, volume: &VolumeId) -> Option<&VolumeMetadata> {
        self.volumes.get(volume)
    }

    /// Create a new empty [`VolumeMetadata`] instance for the given [`VolumeId`] and inserts stores
    /// it.
    ///
    /// # Returns
    /// * [`None`] if there already exists a Volume with the given Id
    /// * [`Some`] with a reference to the newly created [`VolumeMetadata`]
    pub fn create(&mut self, key: VolumeId) -> Option<&VolumeMetadata> {
        if self.volumes.contains_key(&key) {
            return None;
        }

        Some(self.volumes.entry(key).or_insert(VolumeMetadata::new()))
    }

    /// This merges the given [`VolumeMetadata`] with the previously stored Version for the given
    /// [`VolumeId`], if there is no previous Version it will be merged with the Default Instance
    pub fn merge_value(&mut self, key: VolumeId, other: VolumeMetadata) {
        let prev = self.volumes.entry(key).or_default();
        prev.merge(other);
    }
}
