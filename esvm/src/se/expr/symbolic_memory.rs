use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use petgraph::{
    algo::has_path_connecting,
    graph::{Graph, NodeIndex},
    visit::{depth_first_search, DfsEvent::TreeEdge},
    Directed, Direction,
};

#[cfg(test)]
use crate::se::expr::bval::compare_bval;

use crate::se::{expr::bval::*, symbolic_state::ReadTracker};

pub type MVal = NodeIndex;
pub type SymbolicMemory = Graph<Arc<MemoryInfo>, (), Directed>;

pub fn new_memory() -> SymbolicMemory {
    Graph::<_, _, _>::new()
}

pub fn create_new_memory(
    memory: &mut SymbolicMemory,
    name: String,
    memory_type: MemoryType,
    calldata_size: Option<BVal>,
) -> MVal {
    let info = MemoryInfo::new(name, memory_type, calldata_size.clone());
    let root = memory.add_node(Arc::new(info));
    match memory_type {
        MemoryType::Storage | MemoryType::Memory => {
            memset_unlimited(memory, root, &const_usize(0), &const_usize(0))
        }
        MemoryType::Data => {
            memset_unlimited(memory, root, &calldata_size.unwrap(), &const_usize(0))
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct MemoryInfo {
    pub memory_generation: usize,
    pub memory_type: MemoryType,
    pub op: MemoryOperation,

    name: Arc<String>,
    calldata_size: Option<BVal>,
}

// this function soley exists to compare similar memories when not the entire graph is set up, thus
// the indices do not match
#[cfg(test)]
pub fn memory_info_equal(a: &MemoryInfo, b: &MemoryInfo) -> bool {
    if !(a.memory_generation == b.memory_generation
        && a.memory_type == b.memory_type
        && a.name == b.name
        && a.calldata_size == b.calldata_size)
    {
        return false;
    }

    match (&a.op, &b.op) {
        (MemoryOperation::Init, MemoryOperation::Init) => true,
        (
            MemoryOperation::Write8 {
                address: ref addr_a,
                value: ref val_a,
                ..
            },
            MemoryOperation::Write8 {
                address: ref addr_b,
                value: ref val_b,
                ..
            },
        )
        | (
            MemoryOperation::Write256 {
                address: ref addr_a,
                value: ref val_a,
                ..
            },
            MemoryOperation::Write256 {
                address: ref addr_b,
                value: ref val_b,
                ..
            },
        )
        | (
            MemoryOperation::MemsetUnlimited {
                index: ref addr_a,
                value: ref val_a,
                ..
            },
            MemoryOperation::MemsetUnlimited {
                index: ref addr_b,
                value: ref val_b,
                ..
            },
        ) => compare_bval(addr_a, addr_b) && compare_bval(val_a, val_b),
        (
            MemoryOperation::Memset {
                index: ref a_a,
                value: ref b_a,
                size: ref c_a,
                ..
            },
            MemoryOperation::Memset {
                index: ref a_b,
                value: ref b_b,
                size: ref c_b,
                ..
            },
        ) => compare_bval(a_a, a_b) && compare_bval(b_a, b_b) && compare_bval(c_a, c_b),
        (
            MemoryOperation::Memcopy {
                index: ref a_a,
                index_from: ref b_a,
                size: ref c_a,
                ..
            },
            MemoryOperation::Memcopy {
                index: ref a_b,
                index_from: ref b_b,
                size: ref c_b,
                ..
            },
        ) => compare_bval(a_a, a_b) && compare_bval(b_a, b_b) && compare_bval(c_a, c_b),
        (
            MemoryOperation::MemcopyUnlimited {
                index: ref a_a,
                index_from: ref b_a,
                ..
            },
            MemoryOperation::MemcopyUnlimited {
                index: ref a_b,
                index_from: ref b_b,
                ..
            },
        ) => compare_bval(a_a, a_b) && compare_bval(b_a, b_b),
        _ => false,
    }
}

impl MemoryInfo {
    pub fn new(name: String, memory_type: MemoryType, calldata_size: Option<BVal>) -> Self {
        let memory_generation = 0;
        let name = Arc::new(name);
        let op = MemoryOperation::Init;
        Self {
            memory_generation,
            name,
            memory_type,
            op,
            calldata_size,
        }
    }

    pub fn from_self(info: &Self, op: MemoryOperation) -> Self {
        let memory_generation = info.memory_generation + 1;
        let name = Arc::clone(&info.name);
        let memory_type = info.memory_type;
        let calldata_size = info.calldata_size.clone();
        Self {
            memory_generation,
            name,
            memory_type,
            op,
            calldata_size,
        }
    }

    #[cfg(test)]
    pub fn parent(&self) -> NodeIndex {
        match self.op {
            MemoryOperation::Init => NodeIndex::from(0),
            MemoryOperation::Write8 { parent: id, .. }
            | MemoryOperation::Write256 { parent: id, .. }
            | MemoryOperation::Memset { parent: id, .. }
            | MemoryOperation::MemsetUnlimited { parent: id, .. }
            | MemoryOperation::Memcopy { parent: id, .. }
            | MemoryOperation::MemcopyUnlimited { parent: id, .. } => id,
        }
    }

    pub fn name(&self) -> String {
        format!("{}_{}", self.name, self.memory_generation)
    }

    pub fn index_size(&self) -> usize {
        match self.memory_type {
            _ => 256,
        }
    }

    pub fn elem_size(&self) -> usize {
        match self.memory_type {
            MemoryType::Storage => 256,
            _ => 8,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum MemoryOperation {
    // boolean used to evalute if it should be preinitialized with 0s
    // i.e. memory yes, calldata no
    Init,
    Write8 {
        parent: MVal,
        address: BVal,
        value: BVal,
    },
    Write256 {
        parent: MVal,
        address: BVal,
        value: BVal,
    },
    Memset {
        parent: MVal,
        index: BVal,
        value: BVal,
        size: BVal,
    },
    MemsetUnlimited {
        parent: MVal,
        index: BVal,
        value: BVal,
    },
    Memcopy {
        parent: MVal,
        from: MVal,
        index: BVal,
        index_from: BVal,
        size: BVal,
    },
    MemcopyUnlimited {
        parent: MVal,
        from: MVal,
        index: BVal,
        index_from: BVal,
    },
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum MemoryType {
    Memory,
    Data,
    Storage,
}

pub fn byte_write(memory: &mut SymbolicMemory, parent: NodeIndex, addr: &BVal, val: &BVal) -> MVal {
    let new_info;
    {
        let old_info = &memory[parent];
        new_info = MemoryInfo::from_self(
            old_info,
            MemoryOperation::Write8 {
                parent,
                address: Arc::clone(addr),
                value: Arc::clone(val),
            },
        );
    }
    let new_node = memory.add_node(Arc::new(new_info));
    memory.add_edge(parent, new_node, ());
    new_node
}

pub fn word_write(memory: &mut SymbolicMemory, parent: NodeIndex, addr: &BVal, val: &BVal) -> MVal {
    let new_info;
    {
        let old_info = &memory[parent];
        new_info = MemoryInfo::from_self(
            old_info,
            MemoryOperation::Write256 {
                parent,
                address: Arc::clone(addr),
                value: Arc::clone(val),
            },
        );
    }
    let new_node = memory.add_node(Arc::new(new_info));
    memory.add_edge(parent, new_node, ());
    new_node
}

pub fn memset(
    memory: &mut SymbolicMemory,
    parent: NodeIndex,
    index: &BVal,
    val: &BVal,
    size: &BVal,
) -> MVal {
    if !cfg!(feature = "memcopy") {
        return parent;
    }

    let new_info;
    {
        let old_info = &memory[parent];
        new_info = MemoryInfo::from_self(
            old_info,
            MemoryOperation::Memset {
                parent,
                index: Arc::clone(index),
                value: Arc::clone(val),
                size: Arc::clone(size),
            },
        );
    }
    let new_node = memory.add_node(Arc::new(new_info));
    memory.add_edge(parent, new_node, ());
    new_node
}

pub fn memset_unlimited(
    memory: &mut SymbolicMemory,
    parent: NodeIndex,
    index: &BVal,
    val: &BVal,
) -> MVal {
    if !cfg!(feature = "memcopy") {
        return parent;
    }

    let new_info;
    {
        let old_info = &memory[parent];
        new_info = MemoryInfo::from_self(
            old_info,
            MemoryOperation::MemsetUnlimited {
                parent,
                index: Arc::clone(index),
                value: Arc::clone(val),
            },
        );
    }
    let new_node = memory.add_node(Arc::new(new_info));
    memory.add_edge(parent, new_node, ());
    new_node
}

pub fn memcopy(
    memory: &mut SymbolicMemory,
    parent: NodeIndex,
    from: NodeIndex,
    index: &BVal,
    index_f: &BVal,
    size: &BVal,
) -> MVal {
    if !cfg!(feature = "memcopy") {
        let first_value_from = sload(&memory, from, index_f);
        return word_write(memory, parent, index, &first_value_from);
    }

    let new_info;
    {
        let old_info = &memory[parent];
        new_info = MemoryInfo::from_self(
            old_info,
            MemoryOperation::Memcopy {
                parent,
                from,
                index: Arc::clone(index),
                index_from: Arc::clone(index_f),
                size: Arc::clone(size),
            },
        );
    }
    let new_node = memory.add_node(Arc::new(new_info));
    memory.add_edge(parent, new_node, ());
    memory.add_edge(from, new_node, ());
    new_node
}

#[allow(dead_code)]
pub fn memcopy_unlimited(
    memory: &mut SymbolicMemory,
    parent: NodeIndex,
    from: NodeIndex,
    index: &BVal,
    index_f: &BVal,
) -> MVal {
    let new_info;
    {
        let old_info = &memory[parent];
        new_info = MemoryInfo::from_self(
            old_info,
            MemoryOperation::MemcopyUnlimited {
                parent,
                from,
                index: Arc::clone(index),
                index_from: Arc::clone(index_f),
            },
        );
    }
    let new_node = memory.add_node(Arc::new(new_info));
    memory.add_edge(parent, new_node, ());
    memory.add_edge(from, new_node, ());
    new_node
}

pub fn pretty_print(memory: &SymbolicMemory, node: NodeIndex) -> String {
    let mut res = String::new();
    pretty_print_rec(memory, node, &mut res);
    res
}

fn pretty_print_rec(memory: &SymbolicMemory, node: NodeIndex, s: &mut String) {
    let op = &memory[node].op;
    let generation = &memory[node].memory_generation;
    let name = &memory[node].name();
    let parent;
    match op {
        MemoryOperation::Init => {
            s.push_str(&format!("{}:\tInit {}", generation, name,));
            return;
        }
        MemoryOperation::Write8 {
            parent: par,
            address: addr,
            value: val,
        } => {
            parent = par;
            s.push_str(&format!("{}:\tWrite8 {:?} to {:?}", generation, val, addr,))
        }
        MemoryOperation::Write256 {
            parent: par,
            address: addr,
            value: val,
        } => {
            parent = par;
            s.push_str(&format!(
                "{}:\tWrite256 {:?} to {:?}",
                generation, val, addr,
            ))
        }
        MemoryOperation::Memset {
            parent: par,
            index,
            value,
            size,
        } => {
            parent = par;
            s.push_str(&format!(
                "{}:\tMemset from {:?} up to length {:?} with {:?}",
                generation, index, size, value
            ))
        }

        MemoryOperation::MemsetUnlimited {
            parent: par,
            index,
            value,
        } => {
            parent = par;
            s.push_str(&format!(
                "{}:\tMemset from {:?} with unlimited length to value {:?}",
                generation, index, value
            ))
        }
        MemoryOperation::Memcopy {
            parent: par,
            from,
            index: to_index,
            index_from: from_index,
            size: length,
        } => {
            parent = par;
            s.push_str(&format!(
                "{}:\tMemcopy to index {:?} from {:?} with index {:?} and length {:?}",
                generation,
                to_index,
                memory[*from].name(),
                from_index,
                length,
            ))
        }
        MemoryOperation::MemcopyUnlimited {
            parent: par,
            from,
            index: to_index,
            index_from: from_index,
        } => {
            parent = par;
            s.push_str(&format!(
                "{}:\tMemcopy unlimited to index {:?} from {:?} with index {:?}",
                generation,
                to_index,
                memory[*from].name(),
                from_index,
            ))
        }
    }
    pretty_print_rec(memory, *parent, s);
}

fn compute_copy_superset_for_node(memory: &SymbolicMemory, node: NodeIndex) -> HashSet<NodeIndex> {
    let mut res = vec![];
    let mut stack = vec![memory.neighbors_directed(node, Direction::Outgoing)];
    let mut current;

    while let Some(neighbors) = stack.pop() {
        // iterate over all neighbors
        for neighbor in neighbors {
            current = &memory[neighbor];
            match current.op {
                // if we found memory operation abandon exploring this part of the graph
                MemoryOperation::Memcopy { .. } | MemoryOperation::MemcopyUnlimited { .. } => {
                    res.push(neighbor);
                }
                // otherwise continue till exhaustion
                _ => {
                    stack.push(memory.neighbors_directed(neighbor, Direction::Outgoing));
                }
            }
        }
    }

    res.into_iter().collect()
}

fn find_all_nodes_between(
    memory: &SymbolicMemory,
    src: NodeIndex,
    dst: NodeIndex,
) -> Vec<NodeIndex> {
    let mut predecessor = vec![Vec::new(); memory.node_count()];

    let mut stack = vec![(src, memory.neighbors_directed(src, Direction::Outgoing))];
    let mut current;

    while let Some((last, neighbors)) = stack.pop() {
        // iterate over all neighbors
        for neighbor in neighbors {
            if neighbor == dst {
                predecessor[neighbor.index()].push(last);
                continue;
            }
            current = &memory[neighbor];
            match current.op {
                // if we found memory operation we have an invalid path
                MemoryOperation::Memcopy { .. } | MemoryOperation::MemcopyUnlimited { .. } => {
                    continue;
                }
                // otherwise continue till exhaustion and add to predecessor
                _ => {
                    predecessor[neighbor.index()].push(last);
                    stack.push((
                        neighbor,
                        memory.neighbors_directed(neighbor, Direction::Outgoing),
                    ));
                }
            }
        }
    }

    // dft did not reach dst node
    if predecessor[dst.index()].is_empty() {
        return vec![];
    }

    let mut stack = vec![dst];
    let mut path = vec![];
    while let Some(next) = stack.pop() {
        let pred = &mut predecessor[next.index()];
        for id in pred.iter() {
            if *id != src {
                path.push(*id);
            }
        }
        stack.append(pred);
    }
    path
}

fn descendants(memory: &SymbolicMemory, src: NodeIndex) -> Vec<MVal> {
    let mut descendants = Vec::new();
    depth_first_search(memory, Some(src), |event| {
        // discovered new node
        if let TreeEdge(_, v) = event {
            descendants.push(v);
        }
    });
    descendants
}

pub fn get_needed_read_indices_cached(
    reads: &ReadTracker,
    memory: &SymbolicMemory,
    node: NodeIndex,
    cache: &mut HashMap<NodeIndex, HashSet<BVal>>,
) -> HashSet<BVal> {
    if let Some(reads) = cache.get(&node) {
        return reads.clone();
    }
    let reads = get_needed_read_indices(reads, memory, node, cache);
    cache.insert(node, reads.clone());
    reads
}

fn get_needed_read_indices(
    reads: &ReadTracker,
    memory: &SymbolicMemory,
    node: NodeIndex,
    cache: &mut HashMap<NodeIndex, HashSet<BVal>>,
) -> HashSet<BVal> {
    let mut n = HashSet::new();
    let mut a: HashSet<NodeIndex> = HashSet::new();
    a.insert(node);
    let super_set = compute_copy_superset_for_node(memory, node);
    for copy in &super_set {
        let current = &memory[*copy];
        match current.op {
            MemoryOperation::Memcopy {
                parent,
                from,
                index: ref p,
                index_from: ref q,
                ..
            }
            | MemoryOperation::MemcopyUnlimited {
                parent,
                from,
                index: ref p,
                index_from: ref q,
            } => {
                if has_path_connecting(memory, node, parent, None) {
                    for r in get_needed_read_indices_cached(reads, memory, *copy, cache) {
                        n.insert(r);
                    }
                }
                if has_path_connecting(memory, node, from, None) {
                    for r in get_needed_read_indices_cached(reads, memory, *copy, cache) {
                        n.insert(add(q, &sub(&r, p)));
                    }
                }
            }
            _ => unreachable!(),
        }

        // add all nodes betwwen mem and copy
        for node in find_all_nodes_between(memory, node, *copy) {
            a.insert(node);
        }
    }
    // if we find no copy instruction, just collect all subsequent set/writes
    if super_set.is_empty() {
        for id in descendants(&memory, node) {
            a.insert(id);
        }
    }

    for val in a {
        if let Some(read) = reads.get(&val) {
            for r in read {
                match r.val() {
                    Val256::FCombine32(ref v) => {
                        for l in v {
                            if let Val256::FMLoad(_, ref addr) = l.val() {
                                n.insert(Arc::clone(addr));
                            }
                        }
                    }
                    Val256::FMLoad(_, ref addr) | Val256::FSLoad(_, ref addr) => {
                        n.insert(Arc::clone(addr));
                    }
                    _ => unreachable!(),
                }
            }
        }
    }

    n
}

#[cfg(test)]
mod mem_tests {
    use super::*;

    use std::collections::{HashMap, HashSet};
    use std::iter::FromIterator;

    use crate::se::config::ORIGIN;
    use crate::test_helpers::generate_test_graph;
    use crate::CONFIG;

    #[test]
    fn theory_of_memcopy_compute_copy_superset() {
        let (_, memory, mvals) = generate_state_for_mem_test();

        assert_eq!(
            compute_copy_superset_for_node(&memory, mvals[0]),
            HashSet::from_iter(vec!(mvals[3])),
            "Testing mval[0]",
        );
        assert_eq!(
            compute_copy_superset_for_node(&memory, mvals[1]),
            HashSet::from_iter(vec!(mvals[3], mvals[4])),
            "Testing mval[1]",
        );
        assert_eq!(
            compute_copy_superset_for_node(&memory, mvals[2]),
            HashSet::from_iter(vec!(mvals[4])),
            "Testing mval[2]",
        );
        assert_eq!(
            compute_copy_superset_for_node(&memory, mvals[3]),
            HashSet::from_iter(vec!(mvals[5])),
            "Testing mval[3]",
        );
        assert_eq!(
            compute_copy_superset_for_node(&memory, mvals[4]),
            HashSet::from_iter(vec!(mvals[5], mvals[7])),
            "Testing mval[4]",
        );
        assert_eq!(
            compute_copy_superset_for_node(&memory, mvals[5]),
            HashSet::from_iter(vec!(mvals[7])),
            "Testing mval[5]",
        );
        assert_eq!(
            compute_copy_superset_for_node(&memory, mvals[6]),
            HashSet::from_iter(vec!(mvals[7])),
            "Testing mval[6]",
        );
        assert_eq!(
            compute_copy_superset_for_node(&memory, mvals[7]),
            HashSet::from_iter(vec!()),
            "Testing mval[7]",
        );
        assert_eq!(
            compute_copy_superset_for_node(&memory, mvals[8]),
            HashSet::from_iter(vec!()),
            "Testing mval[8]",
        );
    }

    #[test]
    fn theory_of_memcopy_find_all_nodes_between_test() {
        let (_, memory, mvals) = generate_state_for_mem_test();

        assert_eq!(
            find_all_nodes_between(&memory, mvals[0], mvals[3]),
            vec!(),
            "Testing mval[0] -> mvals[8]",
        );
        assert_eq!(
            find_all_nodes_between(&memory, mvals[4], mvals[7]),
            vec!(mvals[6]),
            "Testing mval[4] -> mvals[7]",
        );
    }

    #[test]
    fn theory_of_memcopy_find_decendants() {
        let (_, memory, mvals) = generate_state_for_mem_test();

        assert_eq!(
            descendants(&memory, mvals[0]),
            vec!(mvals[3], mvals[5], mvals[7], mvals[8]),
        );

        assert_eq!(
            descendants(&memory, mvals[4]),
            vec!(mvals[6], mvals[7], mvals[8], mvals[5],),
        );
    }

    #[test]
    fn theory_of_memcopy_read_indices_test() {
        let (tracker, memory, mvals) = generate_state_for_mem_test();
        let mut cache = HashMap::new();

        // 8
        let mut correct = HashSet::new();
        correct.insert(const_usize(0x5));
        correct.insert(const_usize(0x6));
        cache.clear();
        assert_eq!(
            get_needed_read_indices(&tracker, &memory, mvals[8], &mut cache),
            correct,
        );

        // 7
        let mut correct = HashSet::new();
        correct.insert(const_usize(5));
        correct.insert(const_usize(6));
        correct.insert(const_usize(10));
        correct.insert(const_usize(20));
        cache.clear();
        assert_eq!(
            get_needed_read_indices(&tracker, &memory, mvals[7], &mut cache),
            correct,
        );

        // 4
        let mut correct = HashSet::new();
        correct.insert(const_usize(10)); // read on 4
        correct.insert(const_usize(20)); // read on 4

        // node 5 indicies with pointer arithmetic
        for r in get_needed_read_indices(&tracker, &memory, mvals[5], &mut cache) {
            correct.insert(add(&const_usize(10), &sub(&r, &const_usize(100))));
        }

        // 6
        correct.insert(const_usize(5));
        correct.insert(const_usize(6));

        // 7
        for r in get_needed_read_indices(&tracker, &memory, mvals[5], &mut cache) {
            correct.insert(add(&const_usize(0), &sub(&r, &const_usize(100))));
        }

        cache.clear();
        assert_eq!(
            get_needed_read_indices(&tracker, &memory, mvals[4], &mut cache),
            correct,
        );
    }

    fn generate_state_for_mem_test() -> (ReadTracker, SymbolicMemory, Vec<MVal>) {
        CONFIG.write().unwrap().arithmetic_simplification = false;
        CONFIG.write().unwrap().concrete_load = false;
        let mut memory = new_memory();
        let mut tracker = HashMap::new();
        let mut mvals = Vec::new();

        // 0
        let mut mem = create_new_memory(
            &mut memory,
            "test_memory".to_string(),
            MemoryType::Memory,
            None,
        );
        // 1
        let mut data_1 = create_new_memory(
            &mut memory,
            "test_data_1".to_string(),
            MemoryType::Data,
            Some(const_usize(800)),
        );
        // 2
        let data_2 = create_new_memory(
            &mut memory,
            "test_data_2".to_string(),
            MemoryType::Data,
            Some(const_usize(800)),
        );

        mvals.push(mem);
        mvals.push(data_1);
        mvals.push(data_2);

        // 3
        mem = memcopy(
            &mut memory,
            mem,
            data_1,
            &const_usize(0x0),
            &const_usize(0x0),
            &const_usize(100),
        );
        mvals.push(mem);
        let mut set = HashSet::new();
        set.insert(mload8(&memory, mem, &const_usize(10)));
        set.insert(mload8(&memory, mem, &const_usize(20)));
        tracker.insert(mem, set);

        // 4
        data_1 = memcopy(
            &mut memory,
            data_1,
            data_2,
            &const_usize(0x0),
            &const_usize(0x0),
            &const_usize(100),
        );
        mvals.push(data_1);
        let mut set = HashSet::new();
        set.insert(mload8(&memory, data_1, &const_usize(10)));
        set.insert(mload8(&memory, data_1, &const_usize(20)));
        tracker.insert(data_1, set);

        // 5
        mem = memcopy(
            &mut memory,
            mem,
            data_1,
            &const_usize(100),
            &const_usize(10),
            &const_usize(40),
        );
        mvals.push(mem);
        let mut set = HashSet::new();
        set.insert(mload8(&memory, mem, &const_usize(5)));
        set.insert(mload8(&memory, mem, &const_usize(6)));
        tracker.insert(mem, set);

        // 6
        data_1 = word_write(&mut memory, data_1, &const_usize(5), &const_usize(0xAA));
        mvals.push(data_1);
        let mut set = HashSet::new();
        set.insert(mload8(&memory, data_1, &const_usize(5)));
        set.insert(mload8(&memory, data_1, &const_usize(6)));
        tracker.insert(data_1, set);

        // 7
        mem = memcopy(
            &mut memory,
            mem,
            data_1,
            &const_usize(100),
            &const_usize(0x0),
            &const_usize(100),
        );
        mvals.push(mem);
        let mut set = HashSet::new();
        set.insert(mload8(&memory, mem, &const_usize(10)));
        set.insert(mload8(&memory, mem, &const_usize(20)));
        tracker.insert(mem, set);

        // 8
        mem = word_write(&mut memory, mem, &const_usize(5), &const_usize(0xAA));
        mvals.push(mem);
        let mut set = HashSet::new();
        set.insert(mload8(&memory, mem, &const_usize(5)));
        set.insert(mload8(&memory, mem, &const_usize(6)));
        tracker.insert(mem, set);

        (Arc::new(tracker), memory, mvals)
    }

    // basically all computations in the proxy call integration test, this runs forever when
    // optimizations are disabled
    #[test]
    fn memcopy_complex_test() {
        CONFIG.write().unwrap().arithmetic_simplification = true;
        CONFIG.write().unwrap().concrete_load = true;
        let g = generate_test_graph(vec![]);
        let mut s = g.get_state_by_id(1).clone();

        let mut mem = create_new_memory(
            Arc::make_mut(&mut s.memory),
            "test_mem".to_string(),
            MemoryType::Memory,
            None,
        );
        mem = word_write(
            Arc::make_mut(&mut s.memory),
            mem,
            &const_usize(0x40),
            &const_usize(0x80),
        );
        let load_40 = mload(&s.memory, mem, &const_usize(0x40)); // because this is totally not a constant the compiler just wrote to memory
        s.record_read(&load_40);
        mem = word_write(
            Arc::make_mut(&mut s.memory),
            mem,
            &load_40,
            &mul(
                &const256("26959946667150639794667015087019630673637144422540572481103610249216"),
                &and(&const_usize(0x338ccd78), &const_usize(0xffffffff)),
            ),
        );

        s.mem = mem;
        {
            let mut read_state = s.clone();
            let addr = const_usize(0x80);
            let load = mload(&s.memory, mem, &addr);
            read_state.push_constraint(eql(&var("A"), &load));
            read_state.record_read(&load);
            assert_eq!(
                const256(
                    "23316731960010251736834393304797129967432910816967293405485221482156519325696"
                ),
                read_state.get_value(&var("A")).unwrap()
            );
        }

        let load_40 = mload(&s.memory, mem, &const_usize(0x40)); // yes this is still constant
        let load_data = mload(
            &s.memory,
            s.input_tx().data,
            &add(&const_usize(0x0), &const_usize(0x4)),
        );
        s.record_read(&load_40);
        mem = word_write(
            Arc::make_mut(&mut s.memory),
            mem,
            &add(&load_40, &const_usize(0x04)),
            &and(
                &and(
                    &const256("1461501637330902918203684832716283019655932542975"),
                    &load_data,
                ),
                &const256("1461501637330902918203684832716283019655932542975"),
            ),
        );

        s.mem = mem;
        {
            let mut read_state = s.clone();
            let addr = &const_usize(0x80);
            let load = mload(&read_state.memory, mem, addr);
            read_state.push_constraint(eql(&var("A"), &load));
            read_state.record_read(&load);
            assert_eq!(
                const256(
                    "23316731960010251736834393304797129967432910816967293405485221482156519325696"
                ),
                read_state.get_value(&var("A")).unwrap()
            );
        }

        let calldata_size = var("calldata_size");
        let mut data = create_new_memory(
            Arc::make_mut(&mut s.memory),
            "test_data".to_string(),
            MemoryType::Data,
            Some(Arc::clone(&calldata_size)),
        );

        let load_40 = mload(&s.memory, mem, &const_usize(0x40)); // yes this is still constant
        s.record_read(&load_40);
        data = memcopy(
            Arc::make_mut(&mut s.memory),
            data,
            mem,
            &const_usize(0),
            &load_40,
            &add(&const_usize(0x24), &load_40),
        );

        // set mem and data
        s.mem = mem;
        let acc = Arc::make_mut(&mut s.env).new_account(
            Arc::make_mut(&mut s.memory),
            "test_account",
            &const_usize(0),
            None,
            &const_usize(0),
        );
        let id = Arc::make_mut(&mut s.env).new_output_tx(
            Arc::make_mut(&mut s.memory),
            &"test_tx",
            &acc,
            &const_usize(0),
            &acc,
            &const_usize(0),
            &const_usize(0),
            &calldata_size,
            &const_usize(0),
        );
        Arc::make_mut(&mut s.env).get_tx_mut(&id).data = data;

        let mut jump_con = mload(&s.memory, data, &const_usize(0x0));
        s.record_read(&jump_con);
        jump_con = div(
            &jump_con,
            &const256("26959946667150639794667015087019630673637144422540572481103610249216"),
        );
        jump_con = and(&jump_con, &const_usize(0xffffffff));
        jump_con = eql(&jump_con, &const_usize(0x338ccd78));

        s.push_constraint(jump_con);

        {
            let mut read_state = s.clone();
            let addr = &const_usize(0x00);
            let load = mload(&read_state.memory, data, addr);
            read_state.push_constraint(eql(&var("A"), &load));
            read_state.record_read(&load);
            assert_eq!(
                const256(
                    "23316731960010251736834393304797129967432910816967293405485221482156519325696"
                ),
                read_state.get_value(&var("A")).unwrap()
            );
        }

        assert!(s.check_sat());

        let mut complete_con = mload(&s.memory, data, &add(&const_usize(0x0), &const_usize(0x4)));
        complete_con = and(
            &complete_con,
            &const256("1461501637330902918203684832716283019655932542975"),
        ); // 0xffffffffffffffffffffffffffffffffffffffff
        complete_con = and(
            &complete_con,
            &const256("1461501637330902918203684832716283019655932542975"),
        ); // 0xffffffffffffffffffffffffffffffffffffffff
        complete_con = eql(&complete_con, &const256(ORIGIN));

        s.push_constraint(complete_con);
        {
            let mut read_state = s.clone();
            let addr = &const_usize(0x00);
            let load = mload(&read_state.memory, data, addr);
            read_state.push_constraint(eql(&var("A"), &load));
            read_state.record_read(&load);
            assert_eq!(
                const256(
                    "23316731960010251736834393304797129967451491184946060741393730067923320269036"
                ),
                read_state.get_value(&var("A")).unwrap()
            );
        }

        assert!(s.check_sat());
        CONFIG.write().unwrap().concrete_load = false;
        CONFIG.write().unwrap().arithmetic_simplification = false;
    }
}
