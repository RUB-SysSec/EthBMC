pragma solidity ^0.4.18;

contract ParityWalletBugCallArg {
    address owner;

    modifier onlyOwner {
        assert(msg.sender == owner);
        _;
    }

    function _ParityWalletBug() {
        owner = msg.sender;
    }

    function send(address _to) onlyOwner public {
        _to.send(address(this).balance);
    }
}
