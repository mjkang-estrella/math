import Enumeration
import Mathlib.Data.Nat.Fib.Basic
set_option autoImplicit false
set_option warningAsError true
namespace InversePeriodDoubling
open State

def suffixValues (q : State) : ℕ → List ℕ
  | 0 => if output q = 1 then [0] else []
  | t + 1 => suffixValues (delta q false) t ++
      (suffixValues (delta q true) t).map (fun n => 2 ^ t + n)

theorem suffix_count_recurrence (q : State) (t : ℕ) :
    (suffixValues q (t + 1)).length =
      (suffixValues (delta q false) t).length + (suffixValues (delta q true) t).length := by
  simp [suffixValues]

theorem suffix_bound (q : State) (t n : ℕ) (h : n ∈ suffixValues q t) : n < 2 ^ t := by
  induction t generalizing q n with
  | zero => simp only [suffixValues] at h; split_ifs at h <;> simp_all
  | succ t ih =>
    simp only [suffixValues, List.mem_append, List.mem_map] at h
    rcases h with h | ⟨m, hm, rfl⟩
    · have hh := ih _ _ h
      rw [pow_succ]
      omega
    · have hh := ih _ _ hm
      rw [pow_succ]
      omega

theorem suffix_depth_three : ∀ q, suffixValues q 3 = match q with
    | S => [1,5,7] | q2 => [5] | q3 => [1,7] | q4 => [5,7]
    | q5 => [5] | q6 => [] | q7 => [7] | q8 => [] := by decide

theorem valueFrom_formula (n : ℕ) (w : List Bool) :
    valueFrom n w = n * 2 ^ w.length + value w := by
  induction w generalizing n with
  | nil => simp [valueFrom, value]
  | cons b w ih =>
    simp only [valueFrom, List.length_cons, pow_succ, value]
    rw [ih, ih]
    ring

theorem value_cons (b : Bool) (w : List Bool) :
    value (b :: w) = (if b then 2 ^ w.length else 0) + value w := by
  change valueFrom (2 * 0 + if b then 1 else 0) w = _
  rw [valueFrom_formula]
  cases b <;> simp

theorem suffix_semantics (q : State) (t n : ℕ) :
    n ∈ suffixValues q t ↔ ∃ w : List Bool,
      w.length = t ∧ value w = n ∧ output (run q w) = 1 := by
  induction t generalizing q n with
  | zero =>
    simp [suffixValues, List.length_eq_zero_iff, value, valueFrom, run]
    tauto
  | succ t ih =>
    simp only [suffixValues, List.mem_append, List.mem_map, ih]
    constructor
    · rintro (⟨w, hl, hv, ho⟩ | ⟨m, ⟨w, hl, hv, ho⟩, rfl⟩)
      · exact ⟨false :: w, by simp [hl], by simp [value_cons, hv], ho⟩
      · exact ⟨true :: w, by simp [hl], by simp [value_cons, hl, hv], ho⟩
    · rintro ⟨w, hl, hv, ho⟩
      cases w with
      | nil => simp at hl
      | cons b w =>
        have hw : w.length = t := by simpa using hl
        cases b
        · left
          exact ⟨w, hw, by simpa [value_cons] using hv, ho⟩
        · right
          refine ⟨value w, ⟨w, hw, rfl, ho⟩, ?_⟩
          simpa [value_cons, hw] using hv

theorem suffix_source (t n : ℕ) :
    n ∈ suffixValues S t ↔ ∃ w : List Bool,
      w.length = t ∧ value w = n ∧ u (value w) = 1 := by
  rw [suffix_semantics]
  simp only [table1_numeric]

def firstThreshold (t : ℕ) : ℕ := 5 * 2 ^ t - 2 * Nat.fib (t + 2) - 2
def recordGap (t : ℕ) : ℕ := 2 ^ t + if t % 2 = 0 then 1 else 3

end InversePeriodDoubling
