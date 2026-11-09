import Cells
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
set_option autoImplicit false
namespace LiteralGame
attribute [local instance] Classical.propDecidable

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
  | nil => simp [markedSlots] at hi
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
    simpa [slotB, preBoard, mul_comm] using congrArg
      (fun x : ℚ => (if 0 ∈ E then (slotB a (m::R) 0)⁻¹ else 1) * x)
      (ih (next a m) {i | i+1 ∈ E})

theorem selected_product (a : Board) (R : List Move) (T : Finset ℕ)
    (hT : T ⊆ markedSlots a R) :
    (selectedFactors a R (T : Set ℕ)).prod = ∏ i ∈ T, (slotB a R i)⁻¹ := by
  classical
  rw [selected_range]
  simp only [Finset.mem_coe]
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

theorem slotB_pos {a c : Board} {R : List Move} (he : Executes a R c)
    {i : ℕ} (hi : i ∈ markedSlots a R) : 0 < slotB a R i := by
  induction he generalizing i with
  | nil => simp [markedSlots] at hi
  | @cons a b c m R hs ht ih =>
    cases i with
    | zero =>
      obtain ⟨rfl,h2⟩ := (marked_zero a m R).mp hi
      obtain ⟨mid,hS,hC⟩ := diamond_expand hs h2
      have hm := (mem_legalTypes a .S2).mpr ⟨mid,hS⟩
      have hn := step_deterministic (next_step hm) hS
      have hc := (mem_legalTypes mid .C1).mpr ⟨b,hC⟩
      have hp := Finset.card_pos.mpr ⟨Move.C1,hc⟩
      simpa [slotB,preBoard,hn] using (Nat.cast_pos.mpr hp : (0:ℚ) < (legalTypes mid).card)
    | succ i =>
      have hm := (mem_legalTypes a m).mpr ⟨b,hs⟩
      have hn := step_deterministic (next_step hm) hs
      have hh := (marked_succ a m R i).mp hi
      rw [hn] at hh
      simpa [slotB,preBoard,hn] using ih hh

noncomputable def slotP (a : Board) (R : List Move) (i : ℕ) : ℚ :=
  1 / (1 + slotB a R i)

-- Exact finite product is the independent Bernoulli law on the PROVED actual cell.
theorem actual_conditional_bernoulli {N : ℕ} {R : List Move}
    (hR : R ∈ completeWords N) (hr : Reduced R) (T : Finset ℕ)
    (hT : T ⊆ markedSlots (initial N) R) :
    P N (expand R (T : Set ℕ)) / cellMass N R =
      (∏ i ∈ T, slotP (initial N) R i) *
      ∏ i ∈ markedSlots (initial N) R \ T, (1 - slotP (initial N) R i) := by
  classical
  let S := markedSlots (initial N) R
  let b := slotB (initial N) R
  let d := fun i => 1 + (b i)⁻¹
  have hb (i : ℕ) (hi : i ∈ S) : 0 < b i := by
    obtain ⟨c,he,_⟩ := hR
    exact slotB_pos he hi
  have hd (i : ℕ) (hi : i ∈ S) : d i ≠ 0 := by
    have := inv_pos.mpr (hb i hi)
    dsimp [d]; linarith
  have hD : (∏ i ∈ S, d i) ≠ 0 := Finset.prod_ne_zero_iff.mpr hd
  have hP : P N R ≠ 0 := ne_of_gt ((P_positive_iff N R).mpr hR)
  rw [actual_expansion_weight hR hr _ (fun i hi => hT hi),
    selected_product _ _ _ hT, actual_cell_mass_product hR hr]
  change (P N R * ∏ i ∈ T, (b i)⁻¹) / (P N R * ∏ i ∈ S, d i) = _
  rw [mul_div_mul_left _ _ hP]
  have hp (i : ℕ) (hi : i ∈ S) : (b i)⁻¹ / d i = slotP (initial N) R i := by
    have hb0 := ne_of_gt (hb i hi)
    have h1 : 1 + b i ≠ 0 := by have := hb i hi; linarith
    change (b i)⁻¹ / (1 + (b i)⁻¹) = 1 / (1 + b i)
    field_simp [hb0,h1]
    calc
      _ = (1 + b i) * (1 + b i)⁻¹ := by ring
      _ = 1 := mul_inv_cancel₀ h1
  have hq (i : ℕ) (hi : i ∈ S) : 1 / d i = 1 - slotP (initial N) R i := by
    have hb0 := ne_of_gt (hb i hi)
    have h1 : 1 + b i ≠ 0 := by have := hb i hi; linarith
    change 1 / (1 + (b i)⁻¹) = 1 - 1 / (1 + b i)
    field_simp [hb0,h1]
    calc
      _ = b i * ((1 + b i) * (1 + b i)⁻¹) := by ring
      _ = b i := by rw [mul_inv_cancel₀ h1,mul_one]
      _ = _ := by ring
  calc
    _ = (∏ i ∈ T, (b i)⁻¹ / d i) * ∏ i ∈ S \ T, 1 / d i := by
      rw [Finset.prod_div_distrib, Finset.prod_div_distrib]
      simp only [Finset.prod_const_one]
      rw [div_mul_div_comm, mul_one]
      rw [mul_comm (∏ i ∈ T, d i), Finset.prod_sdiff hT]
    _ = _ := congrArg₂ (· * ·)
      (Finset.prod_congr rfl (fun i hi => hp i (hT hi)))
      (Finset.prod_congr rfl (fun i hi => hq i (Finset.mem_sdiff.mp hi).1))

theorem actual_zero_slot_cell {N : ℕ} {R : List Move}
    (hR : R ∈ completeWords N) (hr : Reduced R)
    (hz : markedSlots (initial N) R = ∅) :
    cellDomain N R = {R} ∧ cellMass N R = P N R ∧
      P N R / cellMass N R = 1 := by
  classical
  have hm : cellMass N R = P N R := by rw [actual_cell_mass_product hR hr,hz]; simp
  refine ⟨?_,hm,?_⟩
  · rw [cellDomain_image hR hr,hz]
    simp [expand_empty]
  · rw [hm]; exact div_self (ne_of_gt ((P_positive_iff N R).mpr hR))

-- Set formulation: no restriction to any sampled family of subsets.
theorem actual_conditional_every_subset {N : ℕ} {R : List Move}
    (hR : R ∈ completeWords N) (hr : Reduced R) (E : Set ℕ)
    (hE : E ⊆ (markedSlots (initial N) R : Set ℕ)) :
    P N (expand R E) / cellMass N R =
      (∏ i ∈ (markedSlots (initial N) R).filter (fun i => i ∈ E), slotP (initial N) R i) *
      ∏ i ∈ (markedSlots (initial N) R).filter (fun i => i ∉ E), (1-slotP (initial N) R i) := by
  classical
  let T := (markedSlots (initial N) R).filter (fun i => i ∈ E)
  have hT : T ⊆ markedSlots (initial N) R := Finset.filter_subset _ _
  have heq : (T : Set ℕ) = E := by
    ext i
    simp only [T,Finset.mem_coe,Finset.mem_filter]
    exact ⟨fun h => h.2,fun h => ⟨hE h,h⟩⟩
  have hd : markedSlots (initial N) R \ T =
      (markedSlots (initial N) R).filter (fun i => i ∉ E) := by
    ext i; simp [T]; tauto
  have h := actual_conditional_bernoulli hR hr T hT
  rw [heq,hd] at h
  exact h

theorem actual_N_zero : cellDomain 0 [] = {[]} ∧ cellMass 0 [] = 1 ∧
    P 0 [] / cellMass 0 [] = 1 := by
  have hR : ([] : List Move) ∈ completeWords 0 := by
    apply (domain_exact 0 []).mp
    rw [completeDomain_zero]; simp
  have hr : Reduced ([] : List Move) := by simp [Reduced]
  have h := actual_zero_slot_cell hR hr (by simp [markedSlots])
  simpa [P_zero] using h

end LiteralGame
