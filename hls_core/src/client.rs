//! Contains all the HLS Client related things
//!
//! # Example Flow
//! ```text
//! use hls_core::client::{Client};
//!
//! let networking = {};
//! let cluster_members = {};
//!
//! let client = Client::new(networking, cluster_members);
//!
//! let volume = client.acquire_volume(volume_id).await.unwrap();
//!
//! tokio::task::spawn(volume.refresh());
//!
//! // Use volume to interact with the voluem data
//! ```

use std::{
    future::Future,
    sync::{
        atomic::{self, AtomicU64, AtomicUsize},
        Arc,
    },
};

use crate::{metadata, network, VolumeKey};

/// Mechanism to track which Nodes are Part of the Cluster
pub trait ClusterMembers {
    /// The Address that should be used to communicate with the Nodes
    type Address: Clone;

    /// Select a Random Node from the Members
    fn random_node(&self) -> Option<Self::Address>;
}

/// Static Cluster Membership, this is most useful during Development and for smaller Deployments where the Nodes
/// stay mostly static and don't change much
pub struct StaticMembership<A> {
    members: Vec<A>,
    index: AtomicUsize,
}

impl<A> StaticMembership<A> {
    /// Create a new Instance with the given member Nodes
    pub fn new(members: Vec<A>) -> Self {
        assert!(!members.is_empty());

        Self {
            members,
            index: AtomicUsize::new(0),
        }
    }
}

impl<A> ClusterMembers for StaticMembership<A>
where
    A: Clone,
{
    type Address = A;

    fn random_node(&self) -> Option<Self::Address> {
        let n_index = self.index.load(atomic::Ordering::Relaxed);
        let entry = self.members.get(n_index).cloned();

        self.index.store(
            (n_index + 1) % self.members.len(),
            atomic::Ordering::Relaxed,
        );

        entry
    }
}

/// A HLS Client that can interact with the given HLS Cluster
pub struct Client<N, CM>
where
    N: network::client::ClientNetwork,
    CM: ClusterMembers<Address = N::Address>,
{
    network: Arc<N>,
    cluster_members: Arc<CM>,
}

/// The Errors returned by the Client
pub enum ClientError<N>
where
    N: network::client::ClientNetwork,
{
    /// Could not find any Nodes that belong to the Cluster
    EmptyCluster,
    /// There was an error while sending the Request to a Node in the Cluster
    SendError(N::Error),
    /// The Operation that was attempted failed on the Server Side
    ErrorResponse(network::ErrorResponse),
}

impl<N, CM> Client<N, CM>
where
    N: network::client::ClientNetwork + 'static,
    CM: ClusterMembers<Address = N::Address> + 'static,
{
    /// Creates a new Client instance
    pub fn new(net: N, cm: CM) -> Self {
        Self {
            network: Arc::new(net),
            cluster_members: Arc::new(cm),
        }
    }

    /// This will attempt to acquire the given Volume
    pub async fn acquire_volume(
        &mut self,
        id: metadata::VolumeId,
    ) -> Result<VolumeInstance<N, CM>, ClientError<N>> {
        let req_node_id = self
            .cluster_members
            .random_node()
            .ok_or(ClientError::EmptyCluster)?;

        let req = network::Request::AcquireVolume { volume: id.clone() };

        let res = self
            .network
            .send(req_node_id.clone(), req)
            .await
            .map_err(|e| ClientError::SendError(e))?;

        let (key, volume_meta, latest_count) = match res {
            network::Response::AcquiredVolume {
                key,
                volume_meta,
                latest_count,
            } => (key, volume_meta, latest_count),
            network::Response::Error(e) => return Err(ClientError::ErrorResponse(e)),
            other => {
                todo!("Unexpected Response")
            }
        };

        if volume_meta.update_count() != latest_count {
            todo!("Need to load other Volume Metadata instances")
        }

        let counter = Arc::new(AtomicU64::new(volume_meta.update_count()));
        Ok(VolumeInstance {
            id,
            key,
            network: self.network.clone(),
            cluster_members: self.cluster_members.clone(),
            vol_meta: volume_meta,
            update_counter: counter,
        })
    }
}

/// A Volume Instance allows you to interact with an already acquired Volume
pub struct VolumeInstance<N, CM> {
    id: metadata::VolumeId,
    key: VolumeKey,
    network: Arc<N>,
    cluster_members: Arc<CM>,
    vol_meta: metadata::VolumeMetadata,
    update_counter: Arc<AtomicU64>,
}

impl<N, CM> VolumeInstance<N, CM>
where
    N: network::client::ClientNetwork + 'static,
    CM: ClusterMembers<Address = N::Address> + 'static,
{
    /// Returns a Future that should be run to periodically refresh the Lease on the Volume
    pub fn refresh(&self) -> Box<dyn Future<Output = ()>> {
        let key = self.key.clone();
        let volume_id = self.id.clone();
        let counter = self.update_counter.clone();
        let networking = self.network.clone();
        let members = self.cluster_members.clone();
        let wait_time = std::time::Duration::from_secs(30);

        Box::new(async move {
            loop {
                let req = network::Request::RefreshVolume {
                    key: key.clone(),
                    volume: volume_id.clone(),
                    final_count: counter.load(atomic::Ordering::SeqCst),
                };

                let node = match members.random_node() {
                    Some(n) => n,
                    None => {
                        // If there are no Nodes, we can just exit because there is nothing else we could do
                        break;
                    }
                };

                match networking.send(node, req).await {
                    Ok(network::Response::Confirmation) => {}
                    Ok(other_resp) => {
                        todo!()
                    }
                    Err(e) => {
                        todo!()
                    }
                };

                tokio::time::sleep(wait_time).await;
            }
        })
    }
}
