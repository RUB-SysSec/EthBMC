use crate::bytecode::Instr;
use std::collections::HashMap;
use std::collections::HashSet;
use std::io;
use std::io::Cursor;
use std::io::Read;

#[derive(Clone)]
pub struct Disasm {
    pub opcodes: HashMap<usize, Instr>,
    jump_targets: HashSet<usize>,
}

pub struct CodeCoverage {
    coverage: HashMap<usize, bool>,
}

impl CodeCoverage {
    pub fn from_raw(data: &[u8]) -> Self {
        let mut reader = Cursor::new(data.to_owned());
        let mut coverage = HashMap::new();
        while let Ok((offset, _)) = Disasm::read_on_instr(&mut reader) {
            coverage.insert(offset, false);
        }
        CodeCoverage { coverage }
    }

    pub fn taint(&mut self, offset: usize) {
        if let Some(ins) = self.coverage.get_mut(&offset) {
            *ins = true;
        }
    }

    pub fn coverage(&self) -> f64 {
        self.coverage
            .values()
            .filter_map(|visited| if *visited { Some(1) } else { None })
            .sum::<usize>() as f64
            / self.coverage.len() as f64
    }
}

impl Disasm {
    pub fn from_raw(data: &[u8]) -> Self {
        let mut reader = Cursor::new(data.to_owned());
        let mut opcodes = HashMap::new();
        while let Ok((offset, instr)) = Disasm::read_on_instr(&mut reader) {
            opcodes.insert(offset, instr);
        }
        let jump_targets = opcodes
            .keys()
            .filter_map(|a| {
                if opcodes[a] == Instr::IJumpDest {
                    Some(*a)
                } else {
                    None
                }
            })
            .collect::<HashSet<_>>();
        Disasm {
            opcodes,
            jump_targets,
        }
    }

    #[cfg(test)]
    pub fn new(opcode_vec: Vec<Instr>) -> Self {
        let mut offset = 0;
        let mut opcodes = HashMap::new();
        for i in opcode_vec {
            let size = i.size();
            opcodes.insert(offset, i);
            offset += size;
        }
        let jump_targets = opcodes
            .keys()
            .filter_map(|a| {
                if opcodes[a] == Instr::IJumpDest {
                    Some(*a)
                } else {
                    None
                }
            })
            .collect::<HashSet<_>>();
        Disasm {
            opcodes,
            jump_targets,
        }
    }

    pub fn opcodes(&self) -> ::std::collections::hash_map::Values<usize, Instr> {
        self.opcodes.values()
    }

    pub fn jump_targets(&self) -> &HashSet<usize> {
        &self.jump_targets
    }

    pub fn is_jump_target(&self, addr: usize) -> bool {
        self.opcodes.get(&addr) == Some(&Instr::IJumpDest)
    }

    pub fn get_size(&self, addr: usize) -> Option<usize> {
        match self.opcodes.get(&addr) {
            Some(instr) => Some(instr.size()),
            None => None,
        }
    }

    pub fn get(&self, addr: usize) -> Option<Instr> {
        self.opcodes.get(&addr).cloned()
    }

    #[allow(dead_code)]
    pub fn get_ordered_offsets(&self) -> Vec<&usize> {
        let mut ordered_offset: Vec<_> = self.opcodes.keys().collect();
        ordered_offset.sort_by(|a, b| a.cmp(b));
        ordered_offset
    }

    fn read_bytes(c: &mut Cursor<Vec<u8>>, n: usize) -> Result<Vec<u8>, io::Error> {
        let mut buffer = vec![0; n];
        c.read_exact(&mut buffer)?;
        Ok(buffer)
    }

    fn read_byte(c: &mut Cursor<Vec<u8>>) -> Result<u8, io::Error> {
        Ok(Disasm::read_bytes(c, 1)?[0])
    }

    fn read_on_instr(c: &mut Cursor<Vec<u8>>) -> Result<(usize, Instr), io::Error> {
        let offset = c.position();
        let byte = Disasm::read_byte(c)?;
        let instr = match byte {
            0x00 => Instr::IStop,
            0x01 => Instr::IAdd,
            0x02 => Instr::IMul,
            0x03 => Instr::ISub,
            0x04 => Instr::IDiv,
            0x05 => Instr::ISDiv,
            0x06 => Instr::IMod,
            0x07 => Instr::ISMod,
            0x08 => Instr::IAddMod,
            0x09 => Instr::IMulMod,
            0x0a => Instr::IExp,
            0x0b => Instr::ISext,
            //..
            0x10 => Instr::ILt,
            0x11 => Instr::IGt,
            0x12 => Instr::ISLt,
            0x13 => Instr::ISGt,
            0x14 => Instr::IEql,
            0x15 => Instr::IIsZero,
            0x16 => Instr::IAnd,
            0x17 => Instr::IOr,
            0x18 => Instr::IXor,
            0x19 => Instr::INot,
            0x1a => Instr::IByte,
            0x1b => Instr::IShl,
            0x1c => Instr::ILShr,
            0x1d => Instr::IAShr,
            0x20 => Instr::ISHA3,
            //...
            0x30 => Instr::IAddr,
            0x31 => Instr::IBalance,
            0x32 => Instr::IOrigin,
            0x33 => Instr::ICaller,
            0x34 => Instr::ICallValue,
            0x35 => Instr::ICallDataLoad,
            0x36 => Instr::ICallDataSize,
            0x37 => Instr::ICallDataCopy,
            0x38 => Instr::ICodeSize,
            0x39 => Instr::ICodeCopy,
            0x3a => Instr::IGasPrice,
            0x3b => Instr::IExtCodeSize,
            0x3c => Instr::IExtCodeCopy,
            0x3d => Instr::IRDataSize,
            0x3e => Instr::IRDataCopy,
            //...
            0x40 => Instr::IBlockHash,
            0x41 => Instr::ICoinBase,
            0x42 => Instr::ITimeStamp,
            0x43 => Instr::INumber,
            0x44 => Instr::IDifficulty,
            0x45 => Instr::IGasLimit,
            //...
            0x50 => Instr::IPop,
            0x51 => Instr::IMLoad,
            0x52 => Instr::IMStore,
            0x53 => Instr::IMStore8,
            0x54 => Instr::ISLoad,
            0x55 => Instr::ISStore,
            0x56 => Instr::IJump,
            0x57 => Instr::IJumpIf,
            0x58 => Instr::IPC,
            0x59 => Instr::IMSize,
            0x5a => Instr::IGas,
            0x5b => Instr::IJumpDest,
            //...
            0x60 | 0x61 | 0x62 | 0x63 | 0x64 | 0x65 | 0x66 | 0x67 | 0x68 | 0x69 | 0x6a | 0x6b
            | 0x6c | 0x6d | 0x6e | 0x6f => {
                Instr::IPush(Disasm::read_bytes(c, 1 + (byte & 0x0f) as usize)?)
            }
            0x70 | 0x71 | 0x72 | 0x73 | 0x74 | 0x75 | 0x76 | 0x77 | 0x78 | 0x79 | 0x7a | 0x7b
            | 0x7c | 0x7d | 0x7e | 0x7f => {
                Instr::IPush(Disasm::read_bytes(c, (0x11 + (byte & 0x0f)) as usize)?)
            }
            0x80 => Instr::IDup(1),
            0x81 => Instr::IDup(2),
            0x82 => Instr::IDup(3),
            0x83 => Instr::IDup(4),
            0x84 => Instr::IDup(5),
            0x85 => Instr::IDup(6),
            0x86 => Instr::IDup(7),
            0x87 => Instr::IDup(8),
            0x88 => Instr::IDup(9),
            0x89 => Instr::IDup(10),
            0x8a => Instr::IDup(11),
            0x8b => Instr::IDup(12),
            0x8c => Instr::IDup(13),
            0x8d => Instr::IDup(14),
            0x8e => Instr::IDup(15),
            0x8f => Instr::IDup(16),
            //...
            0x90 => Instr::ISwap(1),
            0x91 => Instr::ISwap(2),
            0x92 => Instr::ISwap(3),
            0x93 => Instr::ISwap(4),
            0x94 => Instr::ISwap(5),
            0x95 => Instr::ISwap(6),
            0x96 => Instr::ISwap(7),
            0x97 => Instr::ISwap(8),
            0x98 => Instr::ISwap(9),
            0x99 => Instr::ISwap(10),
            0x9a => Instr::ISwap(11),
            0x9b => Instr::ISwap(12),
            0x9c => Instr::ISwap(13),
            0x9d => Instr::ISwap(14),
            0x9e => Instr::ISwap(15),
            0x9f => Instr::ISwap(16),
            //...
            0xa0 => Instr::ILog(0),
            0xa1 => Instr::ILog(1),
            0xa2 => Instr::ILog(2),
            0xa3 => Instr::ILog(3),
            0xa4 => Instr::ILog(4),
            //...
            0xf0 => Instr::ICreate,
            0xf1 => Instr::ICall,
            0xf2 => Instr::ICallCode,
            0xf3 => Instr::IReturn,
            0xf4 => Instr::IDelegateCall,
            0xfb => Instr::ICreate2,
            0xfd => Instr::IRevert,
            0xfa => Instr::IStaticCall,
            0xff => Instr::ISelfDestruct,
            0xfe | _ => Instr::IInvalid,
        };
        Ok((offset as usize, instr))
    }
}
