import StackSortInj2Doubling
namespace StackSort
open BigOperators
/-- The literal right hand side of RootSplit. -/
def rootRhs (f : ℕ → ℕ) (n : ℕ) : ℕ :=
  4 * f (n-1) + ∑ i ∈ Finset.Icc 1 (n-2), Nat.choose (n-1) i * f i * f (n-1-i)
/-- A structural bottom-up fold. At stage k, the first k values are stored. -/
def lowerFold : ℕ → (ℕ → ℕ) :=
  Nat.rec (fun _ => 0) (fun k f i => if i = k then
    (if k ≤ 20 then seed20[k]! else rootRhs f k) else f i)
def G (n : ℕ) : ℕ := lowerFold (n+1) n

theorem lowerFold_stable {i k : ℕ} (h : i < k) : lowerFold (k+1) i = lowerFold k i := by
  simp [lowerFold, show i ≠ k by omega]
theorem lowerFold_get {i k : ℕ} (h : i < k) : lowerFold k i = G i := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases he : i = k
    · subst i; rfl
    · rw [lowerFold_stable (by omega), ih (by omega)]

theorem G_seed {n : ℕ} (h : n ≤ 20) : G n = seed20[n]! := by
  simp [G, lowerFold, h]
theorem G_step {n : ℕ} (h : 20 < n) : G n = rootRhs G n := by
  change (if n = n then (if n ≤ 20 then seed20[n]! else rootRhs (lowerFold n) n) else lowerFold n n) = rootRhs G n
  simp only [ite_true, show (n ≤ 20) = False from eq_false (by omega), ite_false]
  unfold rootRhs
  rw [lowerFold_get (by omega : n-1<n)]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := Finset.mem_Icc.mp hi
  rw [lowerFold_get (by omega : i<n), lowerFold_get (by omega : n-1-i<n)]

theorem rootRhs_mono {f g : ℕ → ℕ} {n : ℕ} (hn : 2 ≤ n)
    (h : ∀ i < n, f i ≤ g i) : rootRhs f n ≤ rootRhs g n := by
  unfold rootRhs
  apply Nat.add_le_add (Nat.mul_le_mul_left _ (h _ (by omega)))
  apply Finset.sum_le_sum
  intro i hi
  have hi' := Finset.mem_Icc.mp hi
  exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (h _ (by omega))) (h _ (by omega))

theorem G_le_P (hr : RootSplit) (hs : ExactSeeds20) : ∀ n : ℕ, G n ≤ P n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n ≤ 20
    · rw [G_seed hn]
      by_cases hz : n = 0
      · subst n; rw [P_zero]; decide
      · rw [hs n (by omega) hn]
    · rw [G_step (by omega)]
      exact (rootRhs_mono (by omega) ih).trans (hr n (by omega))
end StackSort
