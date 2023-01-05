fn main() {
    println!("Starting...");

    let storage_backend = memory_storage::MemoryStorage::new();
    let server = hls_core::Server::new(storage_backend);
}
