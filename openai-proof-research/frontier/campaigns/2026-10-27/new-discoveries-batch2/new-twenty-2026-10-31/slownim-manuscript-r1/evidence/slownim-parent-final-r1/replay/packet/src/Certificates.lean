import Witness
import Control
namespace SlowNim360653
-- Lists below retain the actual coordinate order and the source's tie-break.
def gmPath : Fin 7 → Pos 3 :=
  ![![4,4,5], ![3,3,5], ![2,3,4], ![1,3,3], ![0,2,3], ![0,1,2], ![0,0,1]]
def devPath : Fin 6 → Pos 3 :=
  ![![4,4,5], ![3,4,4], ![3,3,3], ![2,2,3], ![1,1,3], ![0,0,3]]
def IsPlay {n l} (hl : 2 ≤ l) (s : Profile n l) (x : Pos n) (L : ℕ)
    (path : Fin (L+1) → Pos n) : Prop :=
  path 0 = x ∧ Terminal (path ⟨L, by omega⟩) ∧
  ∀ k : Fin L, ¬ Terminal (path ⟨k.val, by omega⟩) ∧
    move (path ⟨k.val, by omega⟩)
      ((s ⟨k.val % l, Nat.mod_lt _ (by omega)⟩).choose (path ⟨k.val, by omega⟩)) =
    path ⟨k.val+1, by omega⟩
instance {n l} (hl : 2 ≤ l) (s : Profile n l) (x : Pos n) (L)
    (path : Fin (L+1) → Pos n) : Decidable (IsPlay hl s x L path) := by
  unfold IsPlay; infer_instance
 theorem literal_bridge :
    IsPlay (by decide) baseline x0 6 gmPath ∧
    IsPlay (by decide) deviated x0 5 devPath ∧
    length (by decide) baseline x0 = 6 ∧ length (by decide) deviated x0 = 5 ∧
    payoff (by decide) baseline x0 7 0 = -1 ∧ payoff (by decide) deviated x0 7 0 = 1 := by
  exact ⟨by decide, by decide, baseline_length, deviated_length, witness_payoffs⟩
-- An exhausted run would have length fuel. The general bound excludes that.
theorem no_exhaustion {n l} (hn : 2 ≤ n) (hl : 2 ≤ l) (s : Profile n l)
    (k) (x : Pos n) (t) (hk : mass x < k) : run hl s k x t < k := by
  have h := run_bound hn hl s k x t
  have hmul : run hl s k x t ≤ run hl s k x t * (n-1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  omega
theorem gm_minimum {n} (hn : 2 ≤ n) (l : ℕ) (x : Pos n)
    (h : (multiples l x).Nonempty) : x (gm hn l x) % l = 0 ∧
      ∀ j, x j % l = 0 → x (gm hn l x) ≤ x j := by
  rw [gm_value hn l x, pivotValue, dite_eq_left h]
  constructor
  · exact (Finset.mem_filter.mp (Finset.min'_mem (multiples l x) h)).2
  · intro j hj
    apply Finset.min'_le
    simp only [multiples, Finset.mem_filter, values, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨j, rfl⟩, hj⟩
theorem gm_fallback {n} (hn : 2 ≤ n) (l : ℕ) (x : Pos n)
    (h : ¬ (multiples l x).Nonempty) : ∀ j, x j ≤ x (gm hn l x) := by
  intro j
  rw [gm_value hn l x, pivotValue, dite_eq_right h]
  exact Finset.le_max' _ _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
end SlowNim360653
