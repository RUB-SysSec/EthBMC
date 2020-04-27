pragma solidity ^0.4.18;

contract ParityWalletBugCall {
    address owner;

    modifier onlyOwner {
        assert(msg.sender == owner);
        _;
    }

    function _ParityWalletBug() {
        owner = msg.sender;
    }

    function send() onlyOwner public {
        owner.send(address(this).balance);
    }
}
