use clap::*;
use std::collections::HashMap;
use std::fs;
use sui_distributed_execution::ew_agent::*;
use sui_distributed_execution::server::*;
use sui_distributed_execution::sw_agent::*;
use sui_distributed_execution::types::*;

const FILE_PATH: &str = "crates/sui-distributed-execution/src/configs/1sw4ew.json";

#[derive(Parser)]
#[clap(rename_all = "kebab-case")]

struct Args {
    #[clap(long)]
    pub my_id: UniqueId,
}

#[tokio::main()]
async fn main() {
    // Parse config from json
    let config_json = fs::read_to_string(FILE_PATH).expect("Failed to read config file");
    let global_config: HashMap<UniqueId, ServerConfig> =
        serde_json::from_str(&config_json).unwrap();

    // Parse command line
    let args = Args::parse();
    let my_id = args.my_id;
    assert!(
        global_config.contains_key(&my_id),
        "agent {} not in config",
        &my_id
    );

    // Initialize and run the server
    let kind = global_config.get(&my_id).unwrap().kind.as_str();
    if kind == "SW" {
        let mut server = Server::<SWAgent, SailfishMessage>::new(global_config, my_id);
        server.run().await;
    } else {
        // EW
        let mut server = Server::<EWAgent, SailfishMessage>::new(global_config, my_id);
        server.run().await;
    }
}