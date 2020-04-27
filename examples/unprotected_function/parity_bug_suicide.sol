pragma solidity ^0.4.18;

contract ParityWalletBugSuicide {
    address owner;

    modifier onlyOwner {
        assert(msg.sender == owner);
        _;
    }

    function _ParityWalletBug() {
        owner = msg.sender;
    }

    function kill() onlyOwner public {
        selfdestruct(owner);
    }
}
