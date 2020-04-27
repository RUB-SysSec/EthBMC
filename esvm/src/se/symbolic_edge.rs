use std::io;
use std::io::Write;

use crate::se::symbolic_state::escape_special_chars;

use crate::se::expr::bval::BVal;

#[derive(Debug, Clone)]
pub enum EdgeType {
    Exec,
    CallRet,
    Cond(BVal),
    Terminal,
    Unsat,
}

pub fn edge_exec() -> EdgeType {
    EdgeType::Exec
}

pub fn edge_call_ret() -> EdgeType {
    EdgeType::CallRet
}

pub fn edge_terminal() -> EdgeType {
    EdgeType::Terminal
}

pub fn edge_conditional(val: BVal) -> EdgeType {
    EdgeType::Cond(val)
}

#[derive(Debug, Clone)]
pub struct SymbolicEdge {
    pub from: usize,
    pub to: usize,
    pub etype: EdgeType,
}

impl SymbolicEdge {
    pub fn new(from: usize, to: usize, etype: EdgeType) -> Self {
        SymbolicEdge { from, to, etype }
    }

    pub fn to_dot<W: Write>(&self, w: &mut W) -> Result<(), io::Error> {
        let color = match self.etype {
            EdgeType::Exec => "limegreen",
            EdgeType::CallRet => "blue",
            EdgeType::Cond(_) => "orange",
            EdgeType::Terminal => "crimson",
            EdgeType::Unsat => "red",
        };
        writeln!(w, "{} -> {}[color=\"{}\"]", self.from, self.to, color)?;
        Ok(())
    }

    #[allow(dead_code)]
    pub fn to_dot_with_cond<W: Write>(&self, w: &mut W) -> Result<(), io::Error> {
        let color = match self.etype {
            EdgeType::Exec => "limegreen",
            EdgeType::CallRet => "blue",
            EdgeType::Cond(_) => "orange",
            EdgeType::Terminal => "crimson",
            EdgeType::Unsat => "red",
        };
        match self.etype {
            EdgeType::Cond(ref cond) => {
                writeln!(
                    w,
                    "{} -> {}[color=\"{}\" label=\"{}\"]",
                    self.from,
                    self.to,
                    color,
                    escape_special_chars(format!("{:?}", cond), 300)
                )?;
            }
            _ => {
                writeln!(w, "{} -> {}[color=\"{}\"]", self.from, self.to, color)?;
            }
        }
        Ok(())
    }
}
