import AllN
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Real
set_option autoImplicit false
namespace LiteralGame
attribute [local instance] Classical.propDecidable
open Filter
open scoped Topology

noncomputable def signedAlpha (N k : ℕ) : ℝ := sSup
  {x | ∃ m, m ≤ duration N ∧ ∃ A B : Set (Outcome N),
    (prefixSigma N m).MeasurableSet' A ∧
    (suffixSigma N (m+k)).MeasurableSet' B ∧
    x = eventProb N (A∩B)-eventProb N A*eventProb N B}

theorem signedAlpha_eq (N k : ℕ) : signedAlpha N k = literalAlpha N k := by
  let S : Set ℝ := {x | ∃ m, m ≤ duration N ∧ ∃ A B : Set (Outcome N),
    (prefixSigma N m).MeasurableSet' A ∧
    (suffixSigma N (m+k)).MeasurableSet' B ∧
    x = eventProb N (A∩B)-eventProb N A*eventProb N B}
  have h0 : (0:ℝ) ∈ S := by
    refine ⟨0,Nat.zero_le _,∅,∅,(prefixSigma N 0).measurableSet_empty,
      (suffixSigma N (0+k)).measurableSet_empty,?_⟩
    simp [eventProb]
  have hb : BddAbove S := ⟨1/4,by
    rintro x ⟨m,hm,A,B,ha,hb,rfl⟩; exact covariance_upper N A B⟩
  have hab : BddAbove {x | ∃ m, m ≤ duration N ∧ ∃ A B : Set (Outcome N),
      (prefixSigma N m).MeasurableSet' A ∧
      (suffixSigma N (m+k)).MeasurableSet' B ∧
      x = |eventProb N (A∩B)-eventProb N A*eventProb N B|} :=
    ⟨1/4,by rintro x ⟨m,hm,A,B,ha,hb,rfl⟩; exact covariance_abs_upper N A B⟩
  apply le_antisymm
  · apply csSup_le ⟨0,h0⟩
    rintro x ⟨m,hm,A,B,ha,hb,rfl⟩
    exact (le_abs_self _).trans (le_csSup hab ⟨m,hm,A,B,ha,hb,rfl⟩)
  · apply csSup_le
    · refine ⟨0,0,Nat.zero_le _,∅,∅,(prefixSigma N 0).measurableSet_empty,
        (suffixSigma N (0+k)).measurableSet_empty,?_⟩
      simp [eventProb]
    · rintro x ⟨m,hm,A,B,ha,hB,rfl⟩
      by_cases h : 0 ≤ eventProb N (A∩B)-eventProb N A*eventProb N B
      · rw [abs_of_nonneg h]; exact le_csSup hb ⟨m,hm,A,B,ha,hB,rfl⟩
      · rw [abs_of_neg (lt_of_not_ge h)]
        apply le_csSup hb
        refine ⟨m,hm,Aᶜ,B,(prefixSigma N m).measurableSet_compl ha,hB,?_⟩
        rw [eventProb_compl,eventProb_inter_compl]
        ring

theorem suffixSigma_bot (N r : ℕ) (hr : duration N < r) : suffixSigma N r = ⊥ := by
  simp [suffixSigma,coordinateSigma,Set.Icc_eq_empty_of_lt hr]

theorem literalAlpha_zero (N k : ℕ) (hk : duration N < k) : literalAlpha N k = 0 := by
  apply le_antisymm
  · apply csSup_le
    · refine ⟨0,0,Nat.zero_le _,∅,∅,(prefixSigma N 0).measurableSet_empty,
        (suffixSigma N (0+k)).measurableSet_empty,?_⟩
      simp [eventProb]
    · rintro x ⟨m,hm,A,B,ha,hb,rfl⟩
      rw [suffixSigma_bot N (m+k) (by omega)] at hb
      rcases MeasurableSpace.measurableSet_bot_iff.mp hb with rfl | rfl
      · simp [eventProb]
      · simp [eventProb_univ]
  · exact (literalAlpha_bounds N k).1

def sourceExponent (δ : ℝ) : ℝ := δ/(4+δ)
theorem sourceExponent_pos {δ : ℝ} (hδ : 0<δ) : 0<sourceExponent δ :=
  div_pos hδ (by linarith)
noncomputable def weightedTerm (δ : ℝ) (N k : ℕ) : ℝ :=
  ((k:ℝ)+1)^2 * (literalAlpha N k) ^ (sourceExponent δ)
theorem weightedTerm_nonneg (δ : ℝ) (N k : ℕ) : 0 ≤ weightedTerm δ N k :=
  mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (literalAlpha_bounds N k).1 _)
theorem weightedTerm_zero {δ : ℝ} (hδ : 0<δ) (N k : ℕ) (hk : duration N < k) :
    weightedTerm δ N k = 0 := by
  simp [weightedTerm,literalAlpha_zero N k hk,Real.zero_rpow (ne_of_gt (sourceExponent_pos hδ))]
theorem weighted_summable {δ : ℝ} (hδ : 0<δ) (N : ℕ) : Summable (weightedTerm δ N) := by
  apply summable_of_ne_finset_zero (s := Finset.range (duration N+1))
  intro k hk
  exact weightedTerm_zero hδ N k (by simpa only [Finset.mem_range,not_lt] using hk)
noncomputable def weightedSeries (δ : ℝ) (N : ℕ) : ℝ := ∑' k, weightedTerm δ N k

theorem weightedSeries_dominates {δ : ℝ} (hδ : 0<δ) (N k : ℕ) :
    weightedTerm δ N k ≤ weightedSeries δ N :=
  (weighted_summable hδ N).le_tsum k (fun j _ => weightedTerm_nonneg δ N j)

theorem weightedSeries_diverges {δ : ℝ} (hδ : 0<δ) :
    Tendsto (weightedSeries δ) atTop atTop := by
  let c : ℝ := (1/9:ℝ) ^ (sourceExponent δ)
  have hc : 0<c := Real.rpow_pos_of_pos (by norm_num) _
  apply tendsto_atTop.2
  intro M
  obtain ⟨b,hb⟩ := exists_nat_gt (M/c)
  filter_upwards [all_N_uniform_alpha_ninth,
    fibIndex_tendsto.eventually (eventually_ge_atTop b)] with N ha hn
  let k := (fibIndex N)^6
  have hk : 1≤k := Nat.one_le_pow 6 _ (fibIndex_pos N)
  have hp : c ≤ (literalAlpha N k) ^ (sourceExponent δ) :=
    Real.rpow_le_rpow (by norm_num) (ha k hk le_rfl) (le_of_lt (sourceExponent_pos hδ))
  have hnk : fibIndex N ≤ k := by
    exact Nat.le_self_pow (by omega) _
  have hb' : (b:ℝ) ≤ (k:ℝ) := by exact_mod_cast hn.trans hnk
  have hsq : (b:ℝ) ≤ ((k:ℝ)+1)^2 := by
    nlinarith [sq_nonneg (k:ℝ),show (0:ℝ)≤k from Nat.cast_nonneg k]
  have hM : M < (b:ℝ)*c := (div_lt_iff₀ hc).mp hb
  have hterm : (b:ℝ)*c ≤ weightedTerm δ N k := by
    exact (mul_le_mul_of_nonneg_right hsq (le_of_lt hc)).trans
      (mul_le_mul_of_nonneg_left hp (sq_nonneg _))
  exact le_of_lt (hM.trans_le (hterm.trans (weightedSeries_dominates hδ N k)))

def SourceClaim : Prop := ∃ δ : ℝ, 0<δ ∧ ∃ C : ℝ, 0<C ∧ ∀ N : ℕ, weightedSeries δ N < C
noncomputable def signedWeightedSeries (δ : ℝ) (N : ℕ) : ℝ :=
  ∑' k : ℕ, ((k:ℝ)+1)^2 * (signedAlpha N k) ^ (sourceExponent δ)
def V1SourceClaim : Prop := ∃ δ : ℝ, 0<δ ∧ ∃ C : ℝ, 0<C ∧ ∀ N : ℕ, signedWeightedSeries δ N < C
theorem signedWeightedSeries_eq (δ : ℝ) (N : ℕ) : signedWeightedSeries δ N = weightedSeries δ N := by
  simp only [signedWeightedSeries,signedAlpha_eq,weightedSeries,weightedTerm]
theorem sourceClaims_equivalent : V1SourceClaim ↔ SourceClaim := by
  simp only [V1SourceClaim,SourceClaim,signedWeightedSeries_eq]
theorem publishedQuestion3_false : ¬ SourceClaim := by
  rintro ⟨δ,hδ,C,hC,h⟩
  have he := (tendsto_atTop.1 (weightedSeries_diverges hδ)) C
  obtain ⟨N,hN⟩ := he.exists
  exact (not_lt_of_ge hN) (h N)
theorem v1Question65_false : ¬ V1SourceClaim :=
  fun h => publishedQuestion3_false (sourceClaims_equivalent.mp h)
end LiteralGame
