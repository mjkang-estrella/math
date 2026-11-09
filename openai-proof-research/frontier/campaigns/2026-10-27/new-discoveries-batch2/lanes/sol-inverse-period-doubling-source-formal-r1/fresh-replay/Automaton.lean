import Recurrence
import Mathlib.Tactic.DeriveFintype
set_option autoImplicit false
set_option warningAsError true
namespace InversePeriodDoubling

inductive State | S | q2 | q3 | q4 | q5 | q6 | q7 | q8
  deriving DecidableEq
open State

instance : Fintype State := ⟨{S,q2,q3,q4,q5,q6,q7,q8}, by intro x; cases x <;> simp⟩

def delta : State → Bool → State
  | S, false => S | S, true => q2
  | q2, false => q3 | q2, true => q4
  | q3, false => q5 | q3, true => q6
  | q4, false => q3 | q4, true => q2
  | q5, false => q3 | q5, true => q5
  | q6, false => q8 | q6, true => q7
  | q7, false => q8 | q7, true => q6
  | q8, _ => q8

def output (q : State) : ZMod 2 := if q = q2 ∨ q = q6 then 1 else 0
def run (q : State) (w : List Bool) : State := w.foldl delta q

theorem run_append (q : State) (v w : List Bool) : run q (v ++ w) = run (run q v) w :=
  List.foldl_append

theorem leading_zero (w : List Bool) : run S (false :: w) = run S w := rfl

def state : ℕ → State
  | 0 => S
  | n + 1 => delta (state ((n + 1) / 2)) ((n + 1) % 2 == 1)
termination_by n => n
decreasing_by omega

theorem state_step (n : ℕ) (hn : 0 < n) :
    state n = delta (state (n / 2)) (n % 2 == 1) := by
  cases n with
  | zero => omega
  | succ n => rw [state]

theorem state_even (n : ℕ) : state (2 * n) = delta (state n) false := by
  cases n with
  | zero => simp [state, delta]
  | succ n =>
    rw [state_step _ (by omega)]
    simp

theorem state_odd (n : ℕ) : state (2 * n + 1) = delta (state n) true := by
  rw [state_step _ (by omega)]
  rw [show (2 * n + 1) / 2 = n by omega]
  simp

def PairOK (q r : State) : Prop := (q, r) ∈
  [(q2,S),(q2,q3),(q3,q2),(q3,q6),(q4,q3),(q5,q3),(q5,q4),
   (q5,q7),(q6,q5),(q6,q8),(q7,q8),(q8,q5),(q8,q8)]

instance (q r : State) : Decidable (PairOK q r) := by unfold PairOK; infer_instance

theorem pair_even : ∀ q r, PairOK q r → PairOK (delta q false) (delta r true) := by decide
theorem pair_odd : ∀ q r, PairOK q r → PairOK (delta q true) (delta q false) := by decide
theorem pair_output : ∀ q r, PairOK q r →
    output (delta (delta q false) true) = output (delta r true) := by decide

theorem state_pair (n : ℕ) (hn : 1 ≤ n) : PairOK (state n) (state (n - 1)) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h1 : n = 1
    · subst n; simp [state, delta, PairOK]
    have hm : 1 ≤ n / 2 := by omega
    have hi := ih (n / 2) (by omega) hm
    by_cases he : n % 2 = 0
    · have h : n = 2 * (n / 2) := by omega
      have hp : n - 1 = 2 * (n / 2 - 1) + 1 := by omega
      rw [h, state_even, show 2 * (n / 2) - 1 = 2 * (n / 2 - 1) + 1 by omega,
        state_odd]
      exact pair_even _ _ hi
    · have h : n = 2 * (n / 2) + 1 := by omega
      rw [h, state_odd, show 2 * (n / 2) + 1 - 1 = 2 * (n / 2) by omega, state_even]
      exact pair_odd _ _ hi

def auto (n : ℕ) : ZMod 2 := output (state n)

theorem auto_even (n : ℕ) : auto (2 * n) = 0 := by
  simp only [auto, state_even]
  generalize state n = q
  cases q <;> rfl

theorem auto_four_three (n : ℕ) : auto (4 * n + 3) = auto n := by
  rw [show 4 * n + 3 = 2 * (2 * n + 1) + 1 by omega]
  simp only [auto, state_odd]
  generalize state n = q
  cases q <;> rfl

theorem auto_four_one (n : ℕ) (hn : 1 ≤ n) : auto (4 * n + 1) = auto (2 * n - 1) := by
  rw [show 4 * n + 1 = 2 * (2 * n) + 1 by omega,
    show 2 * n - 1 = 2 * (n - 1) + 1 by omega]
  simp only [auto, state_odd, state_even]
  exact pair_output _ _ (state_pair n hn)

theorem auto_eq_u (n : ℕ) : auto n = u n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h0 : n = 0
    · subst n; simpa [auto, state, output] using u_zero.symm
    by_cases h1 : n = 1
    · subst n; simpa [auto, state, output, delta] using u_one.symm
    obtain ⟨m, hm⟩ : ∃ m, n = 2 * m ∨ n = 4 * m + 1 ∨ n = 4 * m + 3 := by
      by_cases he : n % 2 = 0
      · exact ⟨n / 2, Or.inl (by omega)⟩
      · exact ⟨n / 4, Or.inr (by omega)⟩
    rcases hm with rfl | rfl | rfl
    · rw [auto_even, u_even]
    · have hm : 1 ≤ m := by omega
      rw [auto_four_one _ hm, u_four_one _ hm, ih _ (by omega)]
    · rw [auto_four_three, u_four_three, ih _ (by omega)]

def valueFrom : ℕ → List Bool → ℕ
  | n, [] => n
  | n, b :: w => valueFrom (2 * n + if b then 1 else 0) w

def value (w : List Bool) : ℕ := valueFrom 0 w

theorem state_valueFrom (w : List Bool) (n : ℕ) :
    state (valueFrom n w) = run (state n) w := by
  induction w generalizing n with
  | nil => rfl
  | cons b w ih =>
    cases b <;> simp [valueFrom, ih, state_even, state_odd, run, List.foldl]

theorem table1_numeric (w : List Bool) : output (run S w) = u (value w) := by
  have h := state_valueFrom w 0
  simp only [state] at h
  rw [← h]
  exact auto_eq_u _

end InversePeriodDoubling
