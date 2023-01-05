//! # Metadata
//! Contains all the Datastructures to manage the Metadata for HLS

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
