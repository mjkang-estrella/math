import Mathlib.Data.List.Count
import Lean.Elab.Tactic.Omega
set_option autoImplicit false
namespace TraceRecursion
/-- Letter 7 is replaced by a suffix, the first six letters by singletons. -/
def substitute (letters : ℕ → ℕ) (suffix : List ℕ) (w : List ℕ) : List ℕ :=
  w.flatMap (fun i => if i = 7 then suffix else [letters i])

theorem substitute_length (letters : ℕ → ℕ) (suffix : List ℕ) (w : List ℕ) :
    (substitute letters suffix w).length =
      w.count 7 * suffix.length + (w.length - w.count 7) := by
  induction w with
  | nil => simp [substitute]
  | cons a w ih =>
    have hc : w.count 7 ≤ w.length := List.count_le_length
    by_cases h : a = 7
    · subst a
      simp [substitute, Nat.add_mul] at *
      omega
    · simp [substitute, h] at *
      omega

/-- The precise shortening bound for any proper factor of a multilinear reduction. -/
theorem factor_strictly_shortens (letters : ℕ → ℕ) (suffix w : List ℕ)
    (hw : w.length ≤ 6) (h7 : w.count 7 ≤ 1) (hs : 1 ≤ suffix.length) :
    (substitute letters suffix w).length < 6 + suffix.length := by
  rw [substitute_length]
  have hc : w.count 7 = 0 ∨ w.count 7 = 1 := by omega
  rcases hc with hc | hc <;> rw [hc] <;> simp only [Nat.zero_mul, Nat.one_mul] <;> omega
#print axioms factor_strictly_shortens
end TraceRecursion
