import TreeConstruction
import Mathlib.InformationTheory.Coding.Kraft
import Mathlib.Data.List.OfFn
import Mathlib.Topology.Algebra.InfiniteSum.Real

set_option autoImplicit false
set_option warningAsError true
namespace CascadeRate
attribute [local instance] Classical.propDecidable

theorem finiteContexts_prefixFree (T : SourceContextTree) :
    InformationTheory.IsPrefixFree {w | FiniteContext T.nodes w} := by
  intro u hu v hv hp
  exact context_prefix_unique T hp (List.prefix_refl v) hu hv

theorem finiteContext_ne_nil (T : SourceContextTree) {w : Word}
    (hw : FiniteContext T.nodes w) : w ≠ [] := by
  rintro rfl
  exact hw.2 T.root_internal

def selectedContexts (T : SourceContextTree) : Set Word :=
  {w | FiniteContext T.nodes w ∧ alphaLIS T w = [true]}

theorem selectedContexts_prefixFree (T : SourceContextTree) :
    InformationTheory.IsPrefixFree (selectedContexts T) := by
  intro u hu v hv hp
  exact finiteContexts_prefixFree T u hu.1 v hv.1 hp

theorem selected_cascade (T : SourceContextTree) {w : Word}
    (hw : w ∈ selectedContexts T) :
    cascade T (fairAssignment T) w = 2 * (1/2 : ℝ)^w.length := by
  have hn := finiteContext_ne_nil T hw.1
  have hl : 1 ≤ w.length := List.length_pos_iff.mpr hn
  rw [cascade_fair_halfpower T hn, hw.2]
  simp only [List.length_singleton]
  have he : w.length = (w.length-1)+1 := by omega
  conv_rhs => rw [he, pow_succ]
  ring

noncomputable def selectedWeight (T : SourceContextTree) (w : Word) : ℝ :=
  if w ∈ selectedContexts T then 2 * (1/2 : ℝ)^w.length else 0

theorem selectedWeight_nonneg (T : SourceContextTree) (w : Word) :
    0 ≤ selectedWeight T w := by
  unfold selectedWeight
  split_ifs <;> positivity

theorem kappa_eq_sum_selectedWeight (T : SourceContextTree) (n : ℕ) :
    kappa T (fairAssignment T) [true] n =
      ∑ v : Fin n → Bool, selectedWeight T (List.ofFn v) := by
  unfold kappa
  rw [show [true].length+n-1 = n by simp]
  apply Finset.sum_congr rfl
  intro v _
  simp only [selectedWeight, selectedContexts, Set.mem_ofPred_eq]
  by_cases h : FiniteContext T.nodes (List.ofFn v) ∧ alphaLIS T (List.ofFn v) = [true]
  · simpa [h] using selected_cascade T h
  · simp [h]

theorem selectedWeight_summable (T : SourceContextTree) : Summable (selectedWeight T) := by
  have h := (selectedContexts_prefixFree T).summable_one_div_card_pow_length
  have hs : Summable (fun w : selectedContexts T => 2 * (1/2 : ℝ)^(w : Word).length) := by
    simpa using h.mul_left 2
  exact summable_subtype_iff_indicator.mp hs

theorem selectedWeight_tsum_le (T : SourceContextTree) :
    ∑' w, selectedWeight T w ≤ 2 := by
  have h := (selectedContexts_prefixFree T).tsum_one_div_card_pow_length_le_one
  have he : (∑' w, selectedWeight T w) =
      2 * ∑' w : selectedContexts T, (1/2 : ℝ)^(w : Word).length := by
    rw [← tsum_mul_left]
    exact (tsum_subtype (selectedContexts T) (fun w => 2*(1/2 : ℝ)^w.length)).symm
  rw [he]
  have hh : (∑' w : selectedContexts T, (1/2 : ℝ)^(w : Word).length) ≤ 1 := by
    simpa using h
  linarith

theorem selectedWeight_sigma_summable (T : SourceContextTree) :
    Summable (fun p : Σ n, Fin n → Bool => selectedWeight T (List.ofFn p.2)) := by
  exact List.equivSigmaTuple.symm.summable_iff.mpr (selectedWeight_summable T)

theorem kappa_fair_one_summable (T : SourceContextTree) :
    Summable (kappa T (fairAssignment T) [true]) := by
  have h := (selectedWeight_sigma_summable T).sigma
  simpa only [tsum_fintype, ← kappa_eq_sum_selectedWeight] using h

theorem kappa_fair_one_tsum_selectedWeight (T : SourceContextTree) :
    (∑' n, kappa T (fairAssignment T) [true] n) = ∑' w, selectedWeight T w := by
  have h := (selectedWeight_sigma_summable T).tsum_sigma
  have he := List.equivSigmaTuple.symm.tsum_eq (selectedWeight T)
  change (∑' p : Σ n, Fin n → Bool, selectedWeight T (List.ofFn p.2)) = _ at he
  calc
    _ = ∑' n, ∑' v : Fin n → Bool, selectedWeight T (List.ofFn v) := by
      simp only [tsum_fintype, ← kappa_eq_sum_selectedWeight]
    _ = _ := h.symm.trans he

theorem kappa_fair_one_tsum_eq (T : SourceContextTree) :
    (∑' n, kappa T (fairAssignment T) [true] n) =
      ∑' w : selectedContexts T, cascade T (fairAssignment T) w := by
  rw [kappa_fair_one_tsum_selectedWeight]
  have he : (∑' w, selectedWeight T w) =
      ∑' w : selectedContexts T, 2*(1/2 : ℝ)^(w : Word).length :=
    (tsum_subtype (selectedContexts T) (fun w => 2*(1/2 : ℝ)^w.length)).symm
  rw [he]
  apply tsum_congr
  intro w
  exact (selected_cascade T w.property).symm

theorem kappa_fair_one_tsum_le_two (T : SourceContextTree) :
    (∑' n, kappa T (fairAssignment T) [true] n) ≤ 2 := by
  rw [kappa_fair_one_tsum_selectedWeight]
  exact selectedWeight_tsum_le T
theorem word_enumerated_once (w : Word) :
    ∃! p : Σ n, Fin n → Bool, List.ofFn p.2 = w := by
  exact ⟨List.equivSigmaTuple w, List.equivSigmaTuple.symm_apply_apply w,
    fun p hp => List.equivSigmaTuple.symm.injective (hp.trans
      (List.equivSigmaTuple.symm_apply_apply w).symm)⟩

theorem kappa_fair_one_nonneg (T : SourceContextTree) (n : ℕ) :
    0 ≤ kappa T (fairAssignment T) [true] n := by
  rw [kappa_eq_sum_selectedWeight]
  exact Finset.sum_nonneg (fun v _ => selectedWeight_nonneg T (List.ofFn v))

theorem kappa_one_zero (T : SourceContextTree) (q : ProbabilityAssignment T) :
    kappa T q [true] 0 = 0 := by
  unfold kappa
  apply Finset.sum_eq_zero
  intro v _
  have he : List.ofFn v = [] := List.length_eq_zero_iff.mp (by simp)
  rw [he]
  simp only [show ¬ (FiniteContext T.nodes [] ∧ alphaLIS T [] = [true]) from
    fun h => h.1.2 T.root_internal, ite_false]

theorem fair_one_series (T : SourceContextTree) :
    Summable (kappa T (fairAssignment T) [true]) ∧
      (∑' n, kappa T (fairAssignment T) [true] n) ≤ 2 :=
  ⟨kappa_fair_one_summable T, kappa_fair_one_tsum_le_two T⟩

theorem sourceTree_fair_one_series :
    Summable (kappa sourceTree (fairAssignment sourceTree) [true]) ∧
      (∑' n, kappa sourceTree (fairAssignment sourceTree) [true] n) ≤ 2 :=
  fair_one_series sourceTree
end CascadeRate
