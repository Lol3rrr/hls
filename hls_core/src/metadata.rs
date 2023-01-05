//! # Metadata
//! Contains all the Datastructures to manage the Metadata for HLS
//!
//! ## Structure
//! The Metadata for a Volume is stored inside a [`VolumeMetadata`].
//!
//! ## Example
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

type Actor = String;
