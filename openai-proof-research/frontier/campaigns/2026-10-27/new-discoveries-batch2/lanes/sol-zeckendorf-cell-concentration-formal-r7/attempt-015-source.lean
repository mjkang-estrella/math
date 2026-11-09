import Tail
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Nat.Choose.Central
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
      by classical
         convert (Finset.sum_subset (f := fun i => if i ∈ (T : Set ℕ) then (1:ℕ) else 0)
           ht (by intro i _ hi; simp [hi])).symm using 1
         apply Finset.sum_congr rfl
         intro i _
         by_cases hi : i ∈ T <;> simp [hi]
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
  push_cast at hb
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

theorem actual_cell_length_pushforward {N : ℕ} {R : List Move}
    (hR : R ∈ completeWords N) (hr : Reduced R) (f : ℕ → ℚ) :
    (∑ G ∈ cellDomain N R, P N G / cellMass N R * f G.length) =
    ∑ T ∈ (markedSlots (initial N) R).powerset,
      ((∏ i ∈ T, slotP (initial N) R i) *
        ∏ i ∈ markedSlots (initial N) R \ T, (1-slotP (initial N) R i)) *
      f (R.length + T.card) := by
  classical
  obtain ⟨c,he,hc⟩ := hR
  rw [cellDomain_image ⟨c,he,hc⟩ hr,Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro T hT
    have ht := Finset.mem_powerset.mp hT
    rw [actual_expanded_length T ht,actual_conditional_bernoulli ⟨c,he,hc⟩ hr T ht]
  · intro T hT Q hQ heq
    exact Finset.coe_injective (expand_injective he
      (fun i hi => (Finset.mem_powerset.mp hT) hi)
      (fun i hi => (Finset.mem_powerset.mp hQ) hi) heq)

theorem actual_cell_mu_lower {N n M : ℕ} {R : List Move}
    (hR : R ∈ completeWords N) (hn : 1 ≤ n) (hN : N < F (n+1))
    (hM : 0 < M) (hm : M ≤ (markedSlots (initial N) R).card) :
    0 < (2*(M:ℝ)/(2*(n:ℝ)+1)) ∧
    (2*(M:ℝ)/(2*(n:ℝ)+1)) ≤
      2*∑ i ∈ markedSlots (initial N) R, (slotP (initial N) R i : ℝ) := by
  have hd : (0:ℝ) < 2*n+1 := by positivity
  have hs : ((markedSlots (initial N) R).card : ℝ) / (2*n+1) ≤
      ∑ i ∈ markedSlots (initial N) R, (slotP (initial N) R i : ℝ) := by
    calc
      _ = ∑ _i ∈ markedSlots (initial N) R, (1:ℝ)/(2*n+1) := by simp [div_eq_mul_inv]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i hi
        have hp := (actual_slotP_bounds hR hn hN hi).1
        exact_mod_cast hp
  have hm' : (M:ℝ) ≤ (markedSlots (initial N) R).card := by exact_mod_cast hm
  have hb := div_le_div_of_nonneg_right hm' (le_of_lt hd)
  exact ⟨by positivity,by linarith⟩

-- Full vector law after thinning: each summand already sums the fair V
-- coordinates compatible with the specified output T, for the given U.
theorem finite_thinning_vector {ι : Type*} [DecidableEq ι]
    (S T : Finset ι) (p : ι → ℚ) :
    (∑ U ∈ S.powerset,
      (∏ i ∈ U, (2*p i) * (if i ∈ T then (1:ℚ)/2 else 1/2)) *
      ∏ i ∈ S \ U, (1-2*p i) * (if i ∈ T then (0:ℚ) else 1)) =
      ∏ i ∈ S, if i ∈ T then p i else 1-p i := by
  rw [← Finset.prod_add]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ T <;> simp [hi] <;> ring

noncomputable def fairCentral (l : ℕ) : ℚ := (Nat.centralBinom l : ℚ) / 4^l

theorem fairCentral_recurrence (l : ℕ) :
    (2*(l:ℚ)+2)*fairCentral (l+1) = (2*l+1)*fairCentral l := by
  have h : ((l:ℚ)+1)*(Nat.centralBinom (l+1):ℚ) =
      2*(2*l+1)*(Nat.centralBinom l:ℚ) := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ l
  dsimp [fairCentral]
  rw [pow_succ]
  field_simp
  nlinarith

theorem fairCentral_squared (l : ℕ) : ((l:ℚ)+1)*fairCentral l^2 ≤ 1 := by
  induction l with
  | zero => norm_num [fairCentral]
  | succ l ih =>
    have hr := fairCentral_recurrence l
    have hx : (2*(l:ℚ)+2)^2 * fairCentral (l+1)^2 =
        (2*(l:ℚ)+1)^2 * fairCentral l^2 := by
      nlinarith [congrArg (fun x : ℚ => x^2) hr]
    have hp : (2*(l:ℚ)+1)^2*((l:ℚ)+2) ≤
        (2*(l:ℚ)+2)^2*((l:ℚ)+1) := by nlinarith
    have ha := mul_le_mul_of_nonneg_right hp (sq_nonneg (fairCentral l))
    have hb := mul_le_mul_of_nonneg_left ih (sq_nonneg (2*(l:ℚ)+2))
    have hc := congrArg (fun x : ℚ => x*((l:ℚ)+2)) hx
    have hd : 0 < (2*(l:ℚ)+2)^2 := by positivity
    push_cast
    nlinarith

end LiteralGame
