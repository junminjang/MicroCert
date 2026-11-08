namespace RegVM

-- reg 0, 1, 2 ...
abbrev Reg := Nat

-- instructions
inductive Instr where
  | const (rd : Reg) (val : Int) -- rd <- val
  | add (rd rs1 rs2 : Reg)       -- rd <- rs1 + rs2
  | mul (rd rs1 rs2 : Reg)       -- rd <- rs1 * rs2
  deriving Repr, DecidableEq

abbrev Prog := List Instr


-- State (reg → val)
abbrev RegFile := Reg → Option Int

def emptyRegs : RegFile := fun _ => none

def update (rf : RegFile) (r : Reg) (v : Int) : RegFile :=
  fun x => if x = r then some v else rf x

-- small step
def step (rf : RegFile) (i : Instr) : Option RegFile :=
  match i with
  | .const rd val =>
    some (update rf rd val)
  | .add rd rs1 rs2 =>
    match rf rs1, rf rs2 with
    | some v1, some v2 => some (update rf rd (v1 + v2))
    | _, _ => none
  | .mul rd rs1 rs2 =>
    match rf rs1, rf rs2 with
    | some v1, some v2 => some (update rf rd (v1 * v2))
    | _, _ => none


def run (p : Prog) (rf : RegFile := emptyRegs) : Option RegFile :=
  match p with
  | [] => some rf
  | i :: is =>
    match step rf i with
    | some rf' => run is rf'
    | none => none


def sampleRegProg : Prog := [
  Instr.const 0 2,
  Instr.const 1 3,
  Instr.add 2 0 1
]

#eval match run sampleRegProg with
  | some rf => rf 2
  | none => none

def crashProg : Prog := [ Instr.add 0 9 9]
#eval match run crashProg with
  | some rf => rf 0
  | none => none


-- reg number -> initialized? (true / false)
abbrev InitSet := Reg → Bool

def emptyInit : InitSet := fun _ => false

def markInit (st : InitSet) (r : Reg) : InitSet :=
  fun x => if x = r then true else st x

-- type checker
def checkInstr (i : Instr) (st : InitSet) : Option InitSet :=
  match i with
  | .const rd _ => some (markInit st rd)
  | .add rd rs1 rs2 =>
    match st rs1, st rs2 with
    | true, true => some (markInit st rd)
    | _, _ => none
  | .mul rd rs1 rs2 =>
    match st rs1, st rs2 with
    | true, true => some (markInit st rd)
    | _, _ => none

-- invariant: checker says `true` then some v ∈ rf
def WellTyped (rf : RegFile) (st : InitSet) : Prop :=
  ∀ r, st r = true → ∃ v, rf r = some v

theorem wt_update (rf : RegFile) (st : InitSet) (rd : Reg) (val : Int)
  (h_wt : WellTyped rf st) :
  WellTyped (update rf rd val) (markInit st rd) := by
  intro x hx
  dsimp [update, markInit] at hx ⊢
  
  by_cases h : x = rd
  ·
    simp [h]
  ·
    simp [h] at hx ⊢
    exact h_wt x hx

-- type soundness
theorem step_sound (rf : RegFile) (st : InitSet) (i : Instr) (st' : InitSet)
    (h_wt : WellTyped rf st)
    (h_type : checkInstr i st = some st') :
    ∃ rf', step rf i = some rf' ∧ WellTyped rf' st' := by
  match i with
  | .const rd val =>
    injection h_type with h_eq
    have h_wt_new := wt_update rf st rd val h_wt
    rw [h_eq] at h_wt_new
    exact ⟨update rf rd val, rfl, h_wt_new⟩

  | .add rd rs1 rs2 =>
    match h1 : st rs1, h2 : st rs2 with
    | true, true =>
      simp [checkInstr, h1, h2] at h_type
      
      have ⟨v1, hv1⟩ := h_wt rs1 h1
      have ⟨v2, hv2⟩ := h_wt rs2 h2
      have h_wt_new := wt_update rf st rd (v1 + v2) h_wt
      
      rw [h_type] at h_wt_new
      
      exact ⟨update rf rd (v1 + v2), by simp [step, hv1, hv2], h_wt_new⟩

    | false, _ =>
      simp [checkInstr, h1] at h_type
    | true, false =>
      simp [checkInstr, h1, h2] at h_type

  | .mul rd rs1 rs2 =>
    match h1 : st rs1, h2 : st rs2 with
    | true, true =>
      simp [checkInstr, h1, h2] at h_type
      
      have ⟨v1, hv1⟩ := h_wt rs1 h1
      have ⟨v2, hv2⟩ := h_wt rs2 h2
      have h_wt_new := wt_update rf st rd (v1 * v2) h_wt
      
      rw [h_type] at h_wt_new
      
      exact ⟨update rf rd (v1 * v2), by simp [step, hv1, hv2], h_wt_new⟩

    | false, _ =>
      simp [checkInstr, h1] at h_type
    | true, false =>
      simp [checkInstr, h1, h2] at h_type
