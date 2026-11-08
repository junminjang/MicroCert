import MicroCert.StackVM
import MicroCert.RegVM

namespace MicroCert.Compiler

-- single stack instruction -> reg instruction sequence
def compileInstr (i : StackVM.Instr) (d : Nat) : (List RegVM.Instr × Nat) :=
  match i with
  | .push v => ([RegVM.Instr.const d v], d + 1)
  | .add => ([RegVM.Instr.add (d - 2) (d - 1) (d - 2)], d - 1)
  | .mul => ([RegVM.Instr.mul (d - 2) (d - 1) (d - 2)], d - 1)
  | .pop => ([], d - 1)
    
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

-- invariant
def MatchState : List Int → RegVM.RegFile → Nat → Prop
  | [], _, 0 => True
  | v :: vs, rf, d + 1 => rf d = some v ∧ MatchState vs rf d
  | _, _, _ => False

-- lemma 1 : stack depth d = stack.length
theorem match_length {stack rf d} (h : MatchState stack rf d) : d = stack.length := by
  induction stack generalizing d with
  | nil =>
    cases d with
    | zero => rfl
    | succ => simp [MatchState] at h
  | cons x xs ih =>
    cases d with
    | zero => simp [MatchState] at h
    | succ d => simp [ih h.2]

-- lemma 2 : writing at or above depth d preserves MatchState
theorem match_update_above {stack rf d} {idx : Nat} {v : Int}
    (h_idx : d ≤ idx) (h : MatchState stack rf d) :
    MatchState stack (RegVM.update rf idx v) d := by
  induction stack generalizing d with
  | nil => cases d <;> exact h
  | cons x xs ih =>
    cases d with
    | zero => simp [MatchState] at h
    | succ d =>
      exact ⟨by simp [RegVM.update, show d ≠ idx by omega, h.1], ih (by omega) h.2⟩

-- lemma 3 : running p1 ++ p2 = running p1, then p2
theorem reg_run_append (p1 p2 : RegVM.Prog) (rf : RegVM.RegFile) :
    RegVM.run (p1 ++ p2) rf = (RegVM.run p1 rf).bind (RegVM.run p2 ·) := by
  induction p1 generalizing rf with
  | nil => rfl
  | cons i is ih =>
    simp only [List.cons_append, RegVM.run]
    cases RegVM.step rf i with
    | none => rfl
    | some rf' => exact ih rf'

theorem compileProg_cons (i : StackVM.Instr) (is : StackVM.Prog) (d : Nat) :
    compileProg (i :: is) d = (compileInstr i d).1 ++ compileProg is (compileInstr i d).2 := rfl

-- lemma 4 : one stack step is simulated by its compiled register code
theorem compile_step_correct (i : StackVM.Instr) (stack stack' : List Int)
    (rf : RegVM.RegFile) (d : Nat)
    (h_step : StackVM.step stack i = some stack')
    (h_match : MatchState stack rf d) :
    ∃ rf', RegVM.run (compileInstr i d).1 rf = some rf' ∧
      MatchState stack' rf' (compileInstr i d).2 := by
  obtain rfl := match_length h_match
  match i, stack, h_step with
  | .push v, vs, rfl =>
    exact ⟨_, rfl, by simp [RegVM.update], match_update_above (Nat.le_refl _) h_match⟩
  | .add, v1 :: v2 :: vs, rfl =>
    obtain ⟨h1, h2, h_rest⟩ := h_match
    simp only [List.length_cons] at h1
    exact ⟨RegVM.update rf vs.length (v1 + v2),
      by simp [compileInstr, RegVM.run, RegVM.step, h1, h2],
      by simp [RegVM.update], match_update_above (Nat.le_refl _) h_rest⟩
  | .mul, v1 :: v2 :: vs, rfl =>
    obtain ⟨h1, h2, h_rest⟩ := h_match
    simp only [List.length_cons] at h1
    exact ⟨RegVM.update rf vs.length (v1 * v2),
      by simp [compileInstr, RegVM.run, RegVM.step, h1, h2],
      by simp [RegVM.update], match_update_above (Nat.le_refl _) h_rest⟩
  | .pop, _ :: vs, rfl =>
    exact ⟨rf, rfl, h_match.2⟩

-- semantic preservation
theorem compile_run_correct (p : StackVM.Prog) (stack stack_res : List Int)
    (rf : RegVM.RegFile) (d : Nat)
    (h_run : StackVM.run p stack = some stack_res)
    (h_match : MatchState stack rf d) :
    ∃ rf', RegVM.run (compileProg p d) rf = some rf' ∧
      MatchState stack_res rf' stack_res.length := by
  induction p generalizing stack rf d with
  | nil =>
    obtain rfl : stack = stack_res := Option.some.inj h_run
    obtain rfl := match_length h_match
    exact ⟨rf, rfl, h_match⟩
  | cons i is ih =>
    simp only [StackVM.run] at h_run
    cases h_step : StackVM.step stack i with
    | none => simp [h_step] at h_run
    | some stack' =>
      rw [h_step] at h_run
      obtain ⟨rf', h_run', h_match'⟩ := compile_step_correct i stack stack' rf d h_step h_match
      rw [compileProg_cons, reg_run_append, h_run']
      exact ih stack' rf' _ h_run h_match'

end MicroCert.Compiler
