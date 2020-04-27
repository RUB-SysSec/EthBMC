contract MultiOwned {
    uint public m_numOwners;
    uint public m_required;
    uint[256] m_owners;

    mapping(uint => uint) m_ownerIndex;
    mapping(bytes32 => PendingState) m_pending;

    bytes32[] m_pendingIndex;

    struct PendingState {
        uint yetNeeded;
        uint ownersDone;
        uint index;
    }

    modifier onlymanyowners(bytes32 _op) {
        if (confirmAndCheck(_op)) _;
    }

    function confirmAndCheck(bytes32 _op) internal returns (bool) {
        uint ownerIndex = m_ownerIndex[uint(msg.sender)];
        if (ownerIndex == 0) return;

        var pending = m_pending[_op];
        if (pending.yetNeeded == 0) {
            pending.yetNeeded = m_required;
            pending.ownersDone = 0;
            pending.index = m_pendingIndex.length++;
            m_pendingIndex[pending.index] = _op;
        }

        uint ownerIndexBit = 2**ownerIndex;
        if (pending.ownersDone & ownerIndexBit == 0) {
            if (pending.yetNeeded <= 1) {
                delete m_pendingIndex[m_pending[_op].index];
                delete m_pending[_op];
                return true;
            } else {
                pending.yetNeeded--;
                pending.ownersDone |= ownerIndexBit;
            }
        }
    }

    function initMultiowned(address[] _owners, uint _required) {
        m_numOwners = _owners.length + 1;
        m_owners[1] = uint(msg.sender);
        m_ownerIndex[uint(msg.sender)] = 1;
        for (uint i = 0; i < _owners.length; ++i)
        {
            m_owners[2 + i] = uint(_owners[i]);
            m_ownerIndex[uint(_owners[i])] = 2 + i;
        }
        m_required = _required;
    }
    function pay(address to, uint amount) onlymanyowners(sha3(msg.data)) {
        to.transfer(amount);
    }
}
