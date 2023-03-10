# Design
This document outlines the basic Design/Architecture

## File Storage
* each File is split into chunks of fixed max size (only last chunk can be smaller)
* each Chunk is stored independantly

## Structure
### Raft consensus
* Stores which Volume is allocated to which Node (using access tokens not node identifiers)

### Gossip Protocol
* Runs periodically with random varience to reduce load spikes
* Each Node randomly selects a fixed number of other Nodes in the Cluster to update
* Sends its' latest information to the selected Nodes

### Volume CRDTs
* Store all the Contents of the Volumes (Files/Directories)
* Stores all the Chunks for each File
* Stores where all the chunks are being stored (List of Nodes)

## General Flows
### Assign Volume
* 1) The Client requests a volume
* 2) The Cluster checks if the volume is already used
* 2a) If the volume is already used, reject request
* 2b) If the volume is free, generate an access token for the client and store using Raft
* 3) Client loads the most recent Metadata/Info CRDT for the Volume (TODO add more details)
* 4) Client uses the given access token for all requests for this Volume
* 5) Client refreshes the Token every so often (also stored in Raft)

### Free Volume
* 1) Client frees the volume (with the correct access token)
* 2) Cluster validates request
* 3) Cluster sets the volume to free again and stores this using Raft
* 4) Cluster or Client flushes the CRDT for the Volume to the Cluster to try and increase consistency

### Write from Client
* 1) Calculate the corresponding Chunk for the current Write position
* 2) Check if the Chunk already exists
* 2a) Send the new Write to the Nodes that store the Chunk
* 2b-1) Find replica-count many nodes to store the new Chunk
* 2b-2) Send the Write to the selected Nodes
* 2b-3) Update the Volume CRDT with the new Chunk information and send the Updates into the Cluster
* 3) Wait for a given Number of responses for the Writes (depending on the desired consistency garantues)

Handling Node failure


### Read from Client
* 1) Calculate the corresponding Chunk for the current Read position
* 2) Request the Chunk from all or some of the Nodes that store that Chunk
* 3) Wait for some responses to validate their Correctnes (depending on desired correctnes)
* 3a) If they are inconsistent, update the wrong nodes with the correct data (according to the majority or determined otherwise)

TODO Handle Node failure

### A Node crashes/leaves the Cluster
* 1) Go through all the Volumes that were stored on the Node
* 1a) If the Volume is currently used, skip it
* 1b) Otherwise mark the Volume as being repaired up (if a Client requests this Volume, it will be freed up and given to the client to not reduce availability)
* 2) Once the Volume is marked as being repaired, the current Node acts as a Client and tries to relocate the chunks that were stored on the failed Node

### A Node joins the Cluster

## Failure Scenarios
### Server Node Fails during normal Operation

### Client Fails during normal Operation

### Server Fails during Client Write
