import Tail
import Mathlib.Data.Real.Sqrt
set_option autoImplicit false
namespace LiteralGame
attribute [local instance] Classical.propDecidable

theorem expand_length_range (R : List Move) (E : Set ℕ) :
    (expand R E).length = R.length +
      ∑ i ∈ Finset.range R.length, if i ∈ E then 1 else 0 := by
  induction R generalizing E with
  | nil => simp [expand]
  | cons m R ih =>
    rw [List.length_cons, Finset.sum_range_succ']
    have ht := ih {i | i+1 ∈ E}
    by_cases hz : 0 ∈ E <;> simp [expand,hz] at * <;> omega

theorem actual_expanded_length {a : Board} {R : List Move} (T : Finset ℕ)
    (hT : T ⊆ markedSlots a R) :
    (expand R (T : Set ℕ)).length = R.length + T.card := by
  rw [expand_length_range]
  congr 1
  have ht : T ⊆ Finset.range R.length := fun i hi =>
    Finset.mem_range.mpr (marked_lt a R (hT hi))
  calc
    _ = ∑ i ∈ T, if i ∈ (T : Set ℕ) then 1 else 0 :=
      (Finset.sum_subset ht (by intro i _ hi; simp [hi])).symm
    _ = T.card := by simp

theorem slotB_bounds {a c : Board} {R : List Move} (he : Executes a R c)
    {n : ℕ} (hn : 1 ≤ n) (hv : value a < F (n+1))
    {i : ℕ} (hi : i ∈ markedSlots a R) :
    1 ≤ slotB a R i ∧ slotB a R i ≤ (2*n : ℕ) := by
  induction he generalizing i with
  | nil => simp [markedSlots] at hi
  | @cons a b c m R hs ht ih =>
    have hm := (mem_legalTypes a m).mpr ⟨b,hs⟩
    have hnxt := step_deterministic (next_step hm) hs
    cases i with
    | zero =>
      obtain ⟨rfl,h2⟩ := (marked_zero a m R).mp hi
      obtain ⟨mid,hS,hC⟩ := diamond_expand hs h2
      have hlegal := (mem_legalTypes a .S2).mpr ⟨mid,hS⟩
      have hmid := step_deterministic (next_step hlegal) hS
      have hpos := Finset.card_pos.mpr ⟨Move.C1,(mem_legalTypes mid .C1).mpr ⟨b,hC⟩⟩
      have hval : value mid < F (n+1) := by rw [← step_value hS]; exact hv
      have hb := legalTypes_le_two_n hn hval
      simp only [slotB,preBoard,hmid]
      exact ⟨by exact_mod_cast hpos,by exact_mod_cast hb⟩
    | succ i =>
      have hval : value b < F (n+1) := by rw [← step_value hs]; exact hv
      have hh := (marked_succ a m R i).mp hi
      rw [hnxt] at hh
      simpa [slotB,preBoard,hnxt] using ih hval hh

theorem actual_slotP_bounds {N n : ℕ} {R : List Move}
    (hR : R ∈ completeWords N) (hn : 1 ≤ n) (hN : N < F (n+1))
    {i : ℕ} (hi : i ∈ markedSlots (initial N) R) :
    1 / ((2*n+1 : ℕ) : ℚ) ≤ slotP (initial N) R i ∧
      slotP (initial N) R i ≤ 1/2 := by
  obtain ⟨c,he,_⟩ := hR
  have hb := slotB_bounds he hn (by simpa using hN) hi
  have hd : (0:ℚ) < 1 + slotB (initial N) R i := by linarith
  constructor
  · apply one_div_le_one_div_of_le hd
    push_cast; linarith [hb.2]
  · change 1 / (1 + slotB (initial N) R i) ≤ (1:ℚ)/2
    exact one_div_le_one_div_of_le (by norm_num) (by linarith [hb.1])

-- A literal actual-law statement with the length coordinate now identified.
theorem actual_length_bernoulli {N : ℕ} {R : List Move}
    (hR : R ∈ completeWords N) (hr : Reduced R) (T : Finset ℕ)
    (hT : T ⊆ markedSlots (initial N) R) :
    (expand R (T : Set ℕ)).length = R.length + T.card ∧
    0 < cellMass N R ∧
    P N (expand R (T : Set ℕ)) / cellMass N R =
      (∏ i ∈ T, slotP (initial N) R i) *
      ∏ i ∈ markedSlots (initial N) R \ T, (1-slotP (initial N) R i) :=
  ⟨actual_expanded_length T hT,actual_cell_mass_pos hR hr,
    actual_conditional_bernoulli hR hr T hT⟩

end LiteralGame
