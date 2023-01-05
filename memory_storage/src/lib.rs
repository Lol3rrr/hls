//! Contains an In-Memory implementation of the [`hls_core::Storage`] Trait.
#![warn(missing_docs)]
#![deny(unsafe_code)]
#![feature(async_fn_in_trait)]

use std::{
    collections::HashMap,
    sync::{Arc, Mutex},
};

/// The In-Memory Storage
pub struct MemoryStorage {
    chunks: Mutex<
        HashMap<std::path::PathBuf, HashMap<hls_core::metadata::ChunkId, Arc<hls_core::ChunkData>>>,
    >,
}

/// The Errors returned by the Storage
pub enum MemoryStorageError {
    /// The File that was tried to be created
    FileAlreadyExists(std::path::PathBuf),
    /// The File you tried to access does not exists
    FileDoesntExist(std::path::PathBuf),
    /// The Chunk you tried to access is unknown
    UnknownChunk(std::path::PathBuf, hls_core::metadata::ChunkId),
}

impl MemoryStorage {
    /// Create a new Memory Storage instance
    pub fn new() -> Self {
        Self {
            chunks: Mutex::new(HashMap::new()),
        }
    }
}

impl Default for MemoryStorage {
    fn default() -> Self {
        Self::new()
    }
}

impl hls_core::Storage for MemoryStorage {
    fn create_file(&self, path: &std::path::Path) -> Result<(), hls_core::StorageError> {
        let mut chunks = self.chunks.lock().expect("");

        let path_buf = path.to_path_buf();
        if chunks.contains_key(path) {
            return Err(hls_core::StorageError::FileAlreadyExists(path_buf));
        }

        chunks.insert(path_buf, HashMap::new());

        Ok(())
    }

    fn remove_file(&self, path: &std::path::Path) -> Result<(), hls_core::StorageError> {
        let mut chunks = self.chunks.lock().expect("");

        chunks
            .remove(path)
            .ok_or_else(|| hls_core::StorageError::FileDoesntExist(path.to_path_buf()))
            .map(|_| ())
    }

    fn write_chunk(
        &self,
        path: &std::path::Path,
        chunk: hls_core::metadata::ChunkId,
        data: hls_core::ChunkData,
    ) -> Result<(), hls_core::StorageError> {
        let mut chunks = self.chunks.lock().expect("");

        chunks
            .get_mut(path)
            .ok_or_else(|| hls_core::StorageError::FileDoesntExist(path.to_path_buf()))
            .map(|fchunks| {
                fchunks.insert(chunk, Arc::new(data));
            })
    }

    fn read_chunk(
        &self,
        path: &std::path::Path,
        chunk: hls_core::metadata::ChunkId,
    ) -> Result<std::sync::Arc<hls_core::ChunkData>, hls_core::StorageError> {
        let chunks = self.chunks.lock().expect("");

        let fchunks = chunks
            .get(path)
            .ok_or_else(|| hls_core::StorageError::FileDoesntExist(path.to_path_buf()))?;

        fchunks
            .get(&chunk)
            .ok_or_else(|| hls_core::StorageError::UnknownChunk(path.to_path_buf(), chunk))
            .map(|d| d.clone())
    }
}
