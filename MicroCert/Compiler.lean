import MicroCert.StackVM
import MicroCert.RegVM

namespace MicroCert.Compiler

-- single stack instruction -> reg instruction sequence
def compileInstr (i : StackVM.Instr) (d : Nat) : (List RegVM.Instr × Nat) :=
  match i with
  | .push v =>
    ([RegVM.Instr.const d v], d + 1)
  | .add =>
    ([RegVM.Instr.add (d - 2) (d - 2) (d - 1)], d - 1)
  | .mul =>
    ([RegVM.Instr.mul (d - 2) (d - 2) (d - 1)], d - 1)
  | .pop =>
    ([], d - 1)
    
def compileProg (p : StackVM.Prog) (d : Nat := 0) : List RegVM.Instr :=
  match p with
  | [] => []
  | i :: is =>
    let (insts, d') := compileInstr i d
    insts ++ compileProg is d'


def stackProg : StackVM.Prog :=
[
  StackVM.Instr.push 2, StackVM.Instr.push 3, StackVM.Instr.add,
  StackVM.Instr.push 4, StackVM.Instr.mul
]

#eval compileProg stackProg 0
