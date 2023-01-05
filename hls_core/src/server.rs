use crate::Storage;

/// A single Server Instance in a HLS Cluster
///
/// # Usage
/// * Create a Storage Instance
pub struct Server<S> {
    storage: S,
}

/// A Handle to a running Server, to more easily interact with it locally
pub struct ServerHandle {}

impl<S> Server<S>
where
    S: Storage,
{
    /// Create a new Server Instance
    pub fn new(storage: S) -> Self {
        Self { storage }
    }

    /// Start the Server instance and returns a Handle to interact with the Server
    pub fn start(self) -> ServerHandle {
        todo!()
    }
}

impl ServerHandle {}
