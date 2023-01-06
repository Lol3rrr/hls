//! Contains all the Network related Parts of HLS

use crate::{
    metadata::{ChunkId, VolumeId},
    VolumeKey,
};

/// The Requests send from the Client to the Server
pub enum Request {
    /// A Client wants to acquire a Volume to access it
    AcquireVolume {
        /// The Volume that the client wants to acquire
        volume: VolumeId,
    },
    /// Refresh the lease for the Volume
    RefreshVolume {
        /// The Key to authenticate
        key: VolumeKey,
        /// The relevant Volume
        volume: VolumeId,
        /// The final UpdateCount of the Volumes CRDT
        final_count: u64,
    },
    /// Free a Volume again
    FreeVolume {
        /// The Key to authenticate
        key: VolumeKey,
        /// The Volume to free
        volume: VolumeId,
    },
    /// Read the Chunk of the specified File
    ReadChunk {
        /// The Key to authenticate
        key: VolumeKey,
        /// The Volume in which the File/Chunk is located
        volume: VolumeId,
        /// The Path specifying the File
        path: (),
        /// The Chunk that should be read from said file
        chunk: ChunkId,
    },
    /// Write the Chunk of the specified File
    WriteChunk {
        /// The Key to authenticate
        key: VolumeKey,
        /// The Volume in which the File/Chunk is located
        volume: VolumeId,
        /// The Path of the File
        path: (),
        /// The Chunk of the File
        chunk: ChunkId,
        /// The Data to write to the chunk
        data: (),
        /// If this is a new Chunk that should be created on the Server Side
        new: bool,
    },
    /// Delete the given Chunk
    DeleteChunk {
        /// The Key to authenticate
        key: VolumeKey,
        /// The Volume in which the File/Chunk is located
        volume: VolumeId,
        /// The Path of the File
        path: (),
        /// The Chunk to delete
        chunk: ChunkId,
    },
    /// Delete the entire File, including all the Chunks
    DeleteFile {
        /// The Key to authenticate
        key: VolumeKey,
        /// The Volume in which the File is located
        volume: VolumeId,
        /// The Path of the File to delete
        path: (),
    },
}

/// The Responses that are returned by the Server
pub enum Response {
    /// The Volume was successfully acquired
    AcquiredVolume {
        /// The Key to authenticate future Requests by the Client
        key: VolumeKey,
    },
    /// A Confirmation for the Request that was send
    Confirmation,
    /// The Data in a given Chunk
    ChunkData {
        /// The actual Data
        data: (),
    },
    /// An Error occured while processing the Request
    Error(ErrorResponse),
}

/// All the Error Responses
pub enum ErrorResponse {
    /// The User was not authorized to perform the Requested Action
    NotAuthorized,
    /// There was an error while Acquiring a Volume
    AcquireVolumeError(AcquireVolumeError),
    /// There was an error with a Read Request
    ReadError(FileError),
    /// There was an error with a Write Request
    WriteError(FileError),
    /// There was an error with a Delete Request
    DeleteError(FileError),
}

/// The Errors that could be returned while acquiring a Volume
pub enum AcquireVolumeError {
    /// Unknown Volume
    UnknownVolume,
    /// Volume is already being used by a different User
    AlreadyUsed,
}

/// A general Error that can occur during File Operations
pub enum FileError {
    /// Unknown File
    UnknownFile,
    /// Unknown Chunk
    UnknownChunk,
}

/// All the Client specific Networking Parts
pub mod client {
    use super::{Request, Response};

    /// Abstracts over the underlying Network from the Client Side.
    /// This allows for different Network and Communication Protocols to be used
    pub trait ClientNetwork {
        /// The Error that could be returned during the Communication
        type Error: std::error::Error;

        /// The Address Type used for addressing Nodes in the Cluster
        type Address;

        /// Send a given Request to the target Server
        fn send(&self, target: Self::Address, msg: Request) -> Result<Response, Self::Error>;
    }
}

/// All the Server specific Networking Parts
pub mod server {
    use crate::metadata::{self, VolumeId};
    use serde_derive::{Deserialize, Serialize};

    /// All the Messages send between Servers
    #[derive(Debug, Serialize, Deserialize)]
    pub enum GossipMessage {
        /// The current State of a given Volume
        VolumeState {
            /// The ID of the Volume
            id: VolumeId,
            /// The State of the Volume
            data: metadata::VolumeMetadata,
        },
    }
}
