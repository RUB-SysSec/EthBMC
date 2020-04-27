pragma solidity ^0.4.21;

contract hijack {
    function hijack_fn(address to) {
        to.delegatecall(msg.data);
    }
}
