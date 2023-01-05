//! The Core parts of HLS
#![deny(unsafe_code)]
#![warn(missing_docs)]
// #![feature(async_fn_in_trait)]
// #![feature(return_position_impl_trait_in_trait)]

mod server;

pub use server::{Server, ServerHandle};

pub mod metadata;

pub mod network;

/// The Key used to authenticate that a user gets from the Server to show that a Volume is currently
/// used by said User.
pub struct VolumeKey();

/// Identifies a single Volume uniquely
pub struct VolumeId();

/// The Data contained in a single Chunk of a File
pub struct ChunkData(Vec<u8>);

/// The Errors returned by the Storage
pub enum StorageError {
    /// The File that was tried to be created
    FileAlreadyExists(std::path::PathBuf),
    /// The File you tried to access does not exists
    FileDoesntExist(std::path::PathBuf),
    /// The Chunk you tried to access is unknown
    UnknownChunk(std::path::PathBuf, metadata::ChunkId),
}

/// This interface is required to be implemented by all Storage Backends for the Cluster
pub trait Storage: Send + 'static {
    /// Create a new empty File for the given Path
    fn create_file(&self, path: &std::path::Path) -> Result<(), StorageError>;

    /// Remove the File at the given Path
    fn remove_file(&self, path: &std::path::Path) -> Result<(), StorageError>;

    /// Write a given Chunk for a File
    fn write_chunk(
        &self,
        path: &std::path::Path,
        chunk: metadata::ChunkId,
        data: ChunkData,
    ) -> Result<(), StorageError>;

    /// Reads a given Chunk for a File
    fn read_chunk(
        &self,
        path: &std::path::Path,
        chunk: metadata::ChunkId,
    ) -> Result<std::sync::Arc<ChunkData>, StorageError>;
}
