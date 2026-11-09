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
        refine ⟨m,hm,Aᶜ,B,(prefixSigma N m).measurableSet_compl A ha,hB,?_⟩
        rw [eventProb_compl,eventProb_inter_compl]
        ring

theorem suffixSigma_bot (N r : ℕ) (hr : duration N < r) : suffixSigma N r = ⊥ := by
  simp [suffixSigma,coordinateSigma,Set.Icc_eq_empty_of_lt hr]

-- The infinity in source Eq.(7) can literally include every padded coordinate.
theorem paddedSuffix_eq (N r : ℕ) : coordinateSigma N (Set.Ici r) = suffixSigma N r := by
  apply le_antisymm
  · unfold coordinateSigma
    apply iSup_le
    intro i
    apply iSup_le
    intro hi
    by_cases hd : i ≤ duration N
    · exact le_iSup_of_le i (le_iSup_of_le (show i ∈ Set.Icc r (duration N) from ⟨hi,hd⟩) le_rfl)
    · have hx : (fun w : Outcome N => X w.val i) = fun _ => 0 := by
        funext w
        exact X_padded _ _ (lt_of_le_of_lt (length_le_duration w.property) (lt_of_not_ge hd))
      rw [hx]
      exact measurable_iff_comap_le.mp measurable_const
  · unfold suffixSigma coordinateSigma
    apply iSup_le
    intro i
    apply iSup_le
    intro hi
    exact le_iSup_of_le i (le_iSup_of_le hi.1 le_rfl)

-- Omitting the constant index zero gives precisely the source prefix.
theorem prefix_without_zero (N m : ℕ) : coordinateSigma N (Set.Icc 1 m) = prefixSigma N m := by
  apply le_antisymm
  · unfold prefixSigma coordinateSigma
    apply iSup_le
    intro i
    apply iSup_le
    intro hi
    exact le_iSup_of_le i (le_iSup_of_le (show i ∈ Set.Icc 0 m from ⟨by omega,hi.2⟩) le_rfl)
  · unfold prefixSigma coordinateSigma
    apply iSup_le
    intro i
    apply iSup_le
    intro hi
    by_cases hz : i=0
    · subst i
      have hx : (fun w : Outcome N => X w.val 0) = fun _ => 0 := by funext w; simp [X]
      rw [hx]
      exact measurable_iff_comap_le.mp measurable_const
    · exact le_iSup_of_le i (le_iSup_of_le (show i ∈ Set.Icc 1 m from ⟨by omega,hi.2⟩) le_rfl)

theorem covariance_empty_suffix (N m k : ℕ) (hm : duration N < m)
    (A B : Set (Outcome N)) (hb : (suffixSigma N (m+k)).MeasurableSet' B) :
    eventProb N (A∩B)-eventProb N A*eventProb N B = 0 := by
  rw [suffixSigma_bot N (m+k) (by omega)] at hb
  rcases MeasurableSpace.measurableSet_bot_iff.mp hb with rfl | rfl
  · simp [eventProb]
  · simp [eventProb_univ]

-- The displayed supremum over all natural cuts has the same value set.
theorem source_value_set_eq (N k : ℕ) (f : ℝ → ℝ) (hf : f 0=0) :
    {x | ∃ m, ∃ A B : Set (Outcome N),
      (prefixSigma N m).MeasurableSet' A ∧
      (coordinateSigma N (Set.Ici (m+k))).MeasurableSet' B ∧
      x=f (eventProb N (A∩B)-eventProb N A*eventProb N B)} =
    {x | ∃ m, m ≤ duration N ∧ ∃ A B : Set (Outcome N),
      (prefixSigma N m).MeasurableSet' A ∧
      (suffixSigma N (m+k)).MeasurableSet' B ∧
      x=f (eventProb N (A∩B)-eventProb N A*eventProb N B)} := by
  simp only [paddedSuffix_eq]
  ext x
  constructor
  · rintro ⟨m,A,B,ha,hb,hx⟩
    by_cases hm : m≤duration N
    · exact ⟨m,hm,A,B,ha,hb,hx⟩
    · have he := covariance_empty_suffix N m k (lt_of_not_ge hm) A B hb
      rw [he,hf] at hx
      refine ⟨0,Nat.zero_le _,∅,∅,(prefixSigma N 0).measurableSet_empty,
        (suffixSigma N (0+k)).measurableSet_empty,?_⟩
      simpa [eventProb,hf] using hx
  · rintro ⟨m,hm,A,B,ha,hb,hx⟩
    exact ⟨m,A,B,ha,hb,hx⟩

noncomputable def sourceAlpha (N k : ℕ) (absolute : Bool) : ℝ := sSup
  {x | ∃ m, ∃ A B : Set (Outcome N),
    (prefixSigma N m).MeasurableSet' A ∧
    (coordinateSigma N (Set.Ici (m+k))).MeasurableSet' B ∧
    x = if absolute then |eventProb N (A∩B)-eventProb N A*eventProb N B|
        else eventProb N (A∩B)-eventProb N A*eventProb N B}
theorem sourceAlpha_published (N k : ℕ) : sourceAlpha N k true = literalAlpha N k := by
  simp only [sourceAlpha,↓reduceIte]
  rw [source_value_set_eq N k abs (abs_zero)]
  rfl
theorem sourceAlpha_v1 (N k : ℕ) : sourceAlpha N k false = literalAlpha N k := by
  simp only [sourceAlpha,Bool.false_eq_true,↓reduceIte]
  have he := source_value_set_eq N k id rfl
  simp only [id_eq] at he
  rw [he]
  exact signedAlpha_eq N k

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

noncomputable def sourceExponent (δ : ℝ) : ℝ := δ/(4+δ)
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
  exact weightedTerm_zero hδ N k (by simp only [Finset.mem_range] at hk; omega)
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

-- Directly written with the unrestricted, infinitely padded source Eq.(7).
def DisplayedSourceClaim (absolute : Bool) : Prop :=
  ∃ δ : ℝ, 0<δ ∧ ∃ C : ℝ, 0<C ∧ ∀ N : ℕ,
    (∑' k : ℕ, ((k:ℝ)+1)^2 * (sourceAlpha N k absolute) ^ (δ/(4+δ))) < C
theorem displayedSourceClaim_iff (absolute : Bool) : DisplayedSourceClaim absolute ↔ SourceClaim := by
  cases absolute <;>
    simp only [DisplayedSourceClaim,SourceClaim,weightedSeries,weightedTerm,sourceExponent,
      sourceAlpha_v1,sourceAlpha_published]
theorem displayed_source_false (absolute : Bool) : ¬ DisplayedSourceClaim absolute :=
  fun h => publishedQuestion3_false ((displayedSourceClaim_iff absolute).mp h)
end LiteralGame
