use ethereum_newtypes::{Address, Bytes, WU256};

use types::*;

jsonrpc_client!(
    #[derive(Clone, Debug)]
    pub struct ParityClient {
    /// Returns the current blocknumber
    pub fn eth_blockNumber(&mut self) -> RpcRequest<WU256>;

    /// Returns the current coinbase
    pub fn eth_getBlockByNumber(&mut self, number: BlockSelector, as_tx: bool) -> RpcRequest<Block>;

    /// Load the code for a given address and block number
    pub fn eth_getCode(&mut self, address: Address, number: BlockSelector) -> RpcRequest<Bytes>;

    /// Load the balance of a given account at the given blocknumber
    pub fn eth_getBalance(&mut self, address: Address, number: BlockSelector) -> RpcRequest<WU256>;

    pub fn eth_getStorage(&mut self, address: Address, number: BlockSelector) -> RpcRequest<Storage>;
});

#[cfg(test)]
mod tests {
    use super::ParityClient;

    use jsonrpc_client_core::Transport;
    use serde_json as serde;
    use serde_json::Value as JsonValue;
    use std::io;
    use uint::U256;

    use futures::future as futures;
    use futures::future::Future;

    type BoxFuture<T, E> = Box<Future<Item = T, Error = E> + Send>;

    struct ParityTestTransport;

    impl Transport for ParityTestTransport {
        type Future = BoxFuture<Vec<u8>, io::Error>;
        type Error = io::Error;

        fn get_next_id(&mut self) -> u64 {
            1
        }

        fn send(&self, json_data: Vec<u8>) -> Self::Future {
            let data = serde::from_slice::<JsonValue>(&json_data).unwrap();

            let json = match data["method"] {
                serde::Value::String(ref s) if s == "eth_blockNumber" => json!({
                "jsonrpc": "2.0",
                "id": 1,
                "result": "0x5c9728",
            }),
                _ => unreachable!(),
            };
            Box::new(futures::ok(serde::to_vec(&json).unwrap()))
        }
    }

    #[test]
    fn eth_block_number_test() {
        let mut client = ParityClient::new(ParityTestTransport);
        let res = client.eth_blockNumber().call().unwrap();
        assert_eq!(res.0, U256::from_dec_str("6068008").unwrap());
    }
}
