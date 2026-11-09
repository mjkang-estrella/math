import Cells
import Mathlib.Algebra.BigOperators.Ring.Finset
set_option autoImplicit false
namespace LiteralGame

-- The board immediately BEFORE slot i of the reduced word.
noncomputable def preBoard : Board → List Move → ℕ → Board
  | a, [], _ => a
  | a, _ :: _, 0 => a
  | a, m :: R, i+1 => preBoard (next a m) R i

noncomputable def slotB (a : Board) (R : List Move) (i : ℕ) : ℚ :=
  (legalTypes (next (preBoard a R i) .S2)).card

theorem marked_lt (a : Board) (R : List Move) {i : ℕ}
    (hi : i ∈ markedSlots a R) : i < R.length := by
  induction R generalizing a i with
  | nil => simpa [markedSlots] using hi
  | cons m R ih =>
    cases i with
    | zero => simp
    | succ i =>
      have := ih (next a m) ((marked_succ a m R i).mp hi)
      simpa using Nat.succ_lt_succ this

theorem selected_range (a : Board) (R : List Move) (E : Set ℕ) :
    (selectedFactors a R E).prod =
      ∏ i ∈ Finset.range R.length, if i ∈ E then (slotB a R i)⁻¹ else 1 := by
  classical
  induction R generalizing a E with
  | nil => simp [selectedFactors]
  | cons m R ih =>
    simp only [selectedFactors, List.prod_cons, List.length_cons,
      Finset.prod_range_succ']
    simpa [slotB, preBoard] using congrArg
      (fun x : ℚ => (if 0 ∈ E then (slotB a (m::R) 0)⁻¹ else 1) * x)
      (ih (next a m) {i | i+1 ∈ E})

theorem selected_product (a : Board) (R : List Move) (T : Finset ℕ)
    (hT : T ⊆ markedSlots a R) :
    (selectedFactors a R (T : Set ℕ)).prod = ∏ i ∈ T, (slotB a R i)⁻¹ := by
  classical
  rw [selected_range]
  have ht : T ⊆ Finset.range R.length := fun i hi =>
    Finset.mem_range.mpr (marked_lt a R (hT hi))
  calc
    _ = ∏ i ∈ T, if i ∈ T then (slotB a R i)⁻¹ else 1 :=
      (Finset.prod_subset ht (by intro i _ hi; simp [hi])).symm
    _ = _ := Finset.prod_congr rfl (by intro i hi; simp [hi])

theorem actual_cell_mass_product {N : ℕ} {R : List Move}
    (hR : R ∈ completeWords N) (hr : Reduced R) :
    cellMass N R = P N R *
      ∏ i ∈ markedSlots (initial N) R, (1 + (slotB (initial N) R i)⁻¹) := by
  classical
  rw [actual_cell_mass_sum hR hr]
  congr 1
  calc
    _ = ∑ T ∈ (markedSlots (initial N) R).powerset,
        ∏ i ∈ T, (slotB (initial N) R i)⁻¹ :=
      Finset.sum_congr rfl (fun T hT => selected_product _ _ T (Finset.mem_powerset.mp hT))
    _ = _ := by
      simpa [add_comm] using (Finset.prod_add
        (fun i => (slotB (initial N) R i)⁻¹) (fun _ => (1 : ℚ))
        (markedSlots (initial N) R)).symm

end LiteralGame
