namespace StackVM

-- instructions
inductive Instr where
  | push (val : Int)
  | add
  | mul
  | pop
  deriving Repr, DecidableEq

-- sequence of instruction
abbrev Prog := List Instr
-- state of stack machine
abbrev State := List Int

-- small step
def step (s : State) (i : Instr) : Option State :=
  match i, s with
  | .push v, stack => some (v :: stack)
  | .add , v1 :: v2 :: rest => some ((v1 + v2) :: rest)
  | .mul , v1 :: v2 :: rest => some ((v1 * v2) :: rest)
  | .pop , _ :: rest => some rest
  | _, _ => none -- should be unreachable

def run (p : Prog) (s : State := []) : Option State :=
  match p with
  | [] => some s
  | i :: is =>
    match step s i with
    | some s' => run is s'
    | none => none

def sampleProg : Prog := [Instr.push 2, Instr.push 3, Instr.add, Instr.push 4, Instr.mul]

#eval run sampleProg

-- type check (stack depth)
def checkInstr (i : Instr) (d : Nat) : Option Nat :=
  match i, d with
  | .push _, d => some (d + 1)
  | .add, d + 2 => some (d + 1)
  | .mul, d + 2 => some (d + 1)
  | .pop, d + 1 => some d
  | _, _ => none
  

def checkProg (p : Prog) (d : Nat := 0) : Option Nat :=
  match p with
  | [] => some d
  | i :: is =>
    match checkInstr i d with
    | some d' => checkProg is d'
    | none => none

#eval checkProg sampleProg 0 -- should be 1

def badProg : Prog := [Instr.add]
#eval checkProg badProg 0 -- should be none

-- type soundness
-- if program passes `checkInstr` it should not be none
theorem step_sound (s : State) (i : Instr) (d' : Nat)
  (h_type : checkInstr i s.length = some d') :
  ∃ s', step s i = some s' ∧ s'.length = d' := by
  match i, s with
  | .push v, stack =>
    injection h_type with h_eq
    exact ⟨v :: stack, rfl, h_eq⟩
  | .add, v1 :: v2 :: rest =>
    injection h_type with h_eq
    exact ⟨(v1 + v2) :: rest, rfl, h_eq⟩
  | .mul, v1 :: v2 :: rest =>
    injection h_type with h_eq
    exact ⟨(v1 * v2) :: rest, rfl, h_eq⟩
  | .pop, v :: rest =>
    injection h_type with h_eq
    exact ⟨rest, rfl, h_eq⟩
