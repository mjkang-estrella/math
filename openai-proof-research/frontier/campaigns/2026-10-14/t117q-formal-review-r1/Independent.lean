import T117Q
import Controls

/-! Independent reviewer controls for t117q-formal-review-r1 (MIT, reviewer).
They instantiate the frozen T117Q declarations at their actual interfaces.
No declaration of the frozen packet is restated as an assumption here. -/
open scoped MatrixOrder ComplexOrder
open Matrix
namespace T117QReview

abbrev M1 : Type := Matrix (Fin 1) (Fin 1) ℂ
abbrev M2 : Type := Matrix (Fin 2) (Fin 2) ℂ

/-! ## Order semantics -/

theorem order_is_loewner {n : Type*} [Fintype n] (A B : Matrix n n ℂ) :
    A ≤ B ↔ (B - A).PosSemidef := Iff.rfl

noncomputable def swapM : M2 := !![0, 1; 1, 0]

theorem swap_entrywise_nonneg : ∀ i j, (0 : ℂ) ≤ swapM i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [swapM]

/-- Entrywise-nonnegative but not Loewner-nonnegative: the order is not entrywise. -/
theorem swap_not_loewner_nonneg : ¬ (0 : M2) ≤ swapM := by
  intro h
  have hd := (Matrix.le_iff.mp h).det_nonneg
  have hdet : (swapM - 0).det = -1 := by
    simp [swapM, Matrix.det_fin_two_of]
  rw [hdet] at hd
  have hr := (RCLike.nonneg_iff.mp hd).1
  norm_num at hr

/-! ## Genuine spectral cut at zero threshold versus the abstract control -/

theorem spectralCut_zero_at_zero {n : Type*} [Fintype n] [DecidableEq n]
    (hQ : (0 : Matrix n n ℂ) ≤ 0) : T117Q.spectralCut 0 hQ 0 = 1 := by
  have he : hQ.posSemidef.isHermitian.eigenvalues = 0 :=
    hQ.posSemidef.isHermitian.eigenvalues_eq_zero_iff.mpr rfl
  unfold T117Q.spectralCut T117Q.cutoff
  simp only [he, Pi.zero_apply, le_refl, ite_true]
  exact T117Q.model_one _

/-- The abstract `selector_coverage` interface fails at h=0 (Q=0, P=0, α=1/2). -/
theorem abstract_zero_threshold_interface :
    (∀ i ∈ (Finset.univ : Finset (Fin 1)), (0 : ℝ) • (1 - (0 : M1)) ≤ (fun _ => (0 : M1)) i) ∧
    (∑ i ∈ (Finset.univ : Finset (Fin 1)), (fun _ => (0 : M1)) i ≤
      (0 : ℝ) • ((∑ _i ∈ (Finset.univ : Finset (Fin 1)), (1 : M1)) - (1/2 : ℝ) • 1)) ∧
    ¬ ((1/2 : ℝ) • (1 : M1) ≤ ∑ i ∈ (Finset.univ : Finset (Fin 1)), (fun _ => (0 : M1)) i) := by
  refine ⟨fun _ _ => by simp, by simp, ?_⟩
  intro h
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, one_smul] at h
  have hd := (Matrix.le_iff.mp h).diag_nonneg (i := 0)
  have hr := (RCLike.nonneg_iff.mp hd).1
  norm_num [Matrix.smul_apply] at hr

/-- With the same data (Q=0, h=0, α=1/2) the genuine spectral selector covers. -/
theorem genuine_zero_threshold_covers :
    (1/2 : ℝ) • (1 : M1) ≤
      ∑ _i ∈ (Finset.univ : Finset (Fin 1)), T117Q.spectralCut (0 : M1) le_rfl 0 := by
  simp only [spectralCut_zero_at_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    one_smul]
  have h := smul_le_smul_of_nonneg_right (show (1/2 : ℝ) ≤ 1 by norm_num)
    (zero_le_one : (0 : M1) ≤ 1)
  simpa using h

/-! ## Noncommuting selectors and pairing matrix at the actual interfaces -/

open T117QControls in
theorem one_sub_proj_nonneg {P : M2} (hs : Pᴴ = P) (hi : P * P = P) : 0 ≤ 1 - P := by
  have hs' : (1 - P)ᴴ = 1 - P := by rw [conjTranspose_sub, conjTranspose_one, hs]
  have hi' : (1 - P) * (1 - P) = 1 - P := by
    rw [sub_mul, mul_sub, mul_sub, one_mul, mul_one, one_mul, hi, sub_self, sub_zero]
  have h := (Matrix.posSemidef_conjTranspose_mul_self (1 - P)).nonneg
  simpa only [hs', hi'] using h

noncomputable def Qs : Fin 4 → M2 :=
  ![1 - T117QControls.p, 1 - T117QControls.r, 0, 0]

noncomputable def Ps : Fin 4 → M2 := ![T117QControls.p, T117QControls.r, 1, 1]

theorem Ps_noncommuting : Ps 0 * Ps 1 ≠ Ps 1 * Ps 0 :=
  T117QControls.projections_need_not_commute

theorem Qs_noncommuting : Qs 0 * Qs 1 ≠ Qs 1 * Qs 0 := by
  intro h
  have he := congrArg (fun A : M2 => A 0 1) h
  norm_num [Qs, T117QControls.p, T117QControls.r, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.sub_apply, Matrix.one_apply] at he

theorem Y_noncommuting_with_selector : T117QControls.p * Ps 1 ≠ Ps 1 * T117QControls.p :=
  T117QControls.projections_need_not_commute

theorem Qs_nonneg : ∀ i, 0 ≤ Qs i := by
  intro i
  fin_cases i
  · exact one_sub_proj_nonneg T117QControls.p_selfadjoint T117QControls.p_idempotent
  · exact one_sub_proj_nonneg T117QControls.r_selfadjoint T117QControls.r_idempotent
  · exact le_rfl
  · exact le_rfl

theorem Ps_defect : ∀ i ∈ (Finset.univ : Finset (Fin 4)), (1 : ℝ) • (1 - Ps i) ≤ Qs i := by
  intro i _
  fin_cases i <;> simp [Ps, Qs]

theorem Qs_budget :
    (∑ i ∈ (Finset.univ : Finset (Fin 4)), Qs i) ≤
      (1 : ℝ) • ((∑ _i ∈ (Finset.univ : Finset (Fin 4)), (1 : M2)) - (2 : ℝ) • 1) := by
  have heq : (1 : ℝ) • ((∑ _i ∈ (Finset.univ : Finset (Fin 4)), (1 : M2)) - (2 : ℝ) • 1) =
      (∑ i ∈ (Finset.univ : Finset (Fin 4)), Qs i) + (T117QControls.p + T117QControls.r) := by
    simp only [Fin.sum_univ_four, Qs, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, one_smul]
    module
  rw [heq]
  exact le_add_of_nonneg_right (add_nonneg T117QControls.p_positive T117QControls.r_positive)

/-- `selector_coverage` with two noncommuting rank-one selectors. -/
theorem noncommuting_selector_coverage :
    (2 : ℝ) • (1 : M2) ≤ ∑ i ∈ (Finset.univ : Finset (Fin 4)), Ps i :=
  T117Q.selector_coverage _ Qs Ps one_pos Ps_defect Qs_budget

/-- `positive_trace_coverage` with Y=p, which does not commute with selector r. -/
theorem noncommuting_trace_coverage :
    2 * T117Q.realTrace T117QControls.p ≤
      ∑ i ∈ (Finset.univ : Finset (Fin 4)), T117Q.realTrace (T117QControls.p * Ps i) :=
  T117Q.positive_trace_coverage _ Ps T117QControls.p_positive noncommuting_selector_coverage

/-- The spectral endpoint lemma is jointly satisfiable with noncommuting inputs and Y. -/
theorem noncommuting_inputs_trace_budget :
    T117Q.realTrace T117QControls.p ≤ 2 * T117Q.realTrace T117QControls.p := by
  have hbud : (∑ i ∈ (Finset.univ : Finset (Fin 4)), Qs i) ≤
      ((1 : ℝ) * ((Finset.univ : Finset (Fin 4)).card : ℝ) / 2) • (1 : M2) := by
    have h := Qs_budget
    have hc : (1 : ℝ) • ((∑ _i ∈ (Finset.univ : Finset (Fin 4)), (1 : M2)) - (2 : ℝ) • 1) =
        ((1 : ℝ) * ((Finset.univ : Finset (Fin 4)).card : ℝ) / 2) • (1 : M2) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, one_smul,
        ← Nat.cast_smul_eq_nsmul ℝ]
      module
    rwa [hc] at h
  refine T117Q.trace_budget_consequence _ Finset.univ_nonempty Qs Qs_nonneg one_pos hbud
    T117QControls.p_positive ?_
  intro i _
  have h := T117Q.trace_product_mono T117QControls.p_positive
    (T117Q.spectralCut_le_one (Qs i) (Qs_nonneg i) 1)
  simpa using h

/-! ## Necessity at the actual interfaces -/

/-- `positive_trace_coverage` fails for Y=-1 although its coverage hypothesis holds. -/
theorem positivity_needed_actual_interface :
    (1 : ℝ) • (1 : M1) ≤ ∑ _i ∈ (Finset.univ : Finset (Fin 1)), (2 : ℝ) • (1 : M1) ∧
    ¬ ((1 : ℝ) * T117Q.realTrace (-1 : M1) ≤
        ∑ _i ∈ (Finset.univ : Finset (Fin 1)), T117Q.realTrace ((-1 : M1) * ((2 : ℝ) • 1))) := by
  constructor
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, one_smul]
    have h := smul_le_smul_of_nonneg_right (show (1 : ℝ) ≤ 2 by norm_num)
      (zero_le_one : (0 : M1) ≤ 1)
    rwa [one_smul] at h
  · norm_num [T117Q.realTrace, Matrix.trace, Fin.sum_univ_succ]

/-- `trace_budget_consequence` without nonemptiness: every other hypothesis holds,
the conclusion fails (s=∅, Q=0, h=1, Y=1, b=0). -/
theorem empty_family_actual_interface :
    (∑ i ∈ (∅ : Finset (Fin 1)), (fun _ => (0 : M1)) i ≤
      ((1 : ℝ) * ((∅ : Finset (Fin 1)).card : ℝ) / 2) • (1 : M1)) ∧
    (∀ i ∈ (∅ : Finset (Fin 1)),
      T117Q.realTrace ((1 : M1) * T117Q.spectralCut ((fun _ => (0 : M1)) i) le_rfl 1) ≤ 0) ∧
    (0 : M1) ≤ 1 ∧ ¬ T117Q.realTrace (1 : M1) ≤ 2 * 0 := by
  refine ⟨by simp, by simp, zero_le_one, ?_⟩
  norm_num [T117Q.realTrace, Matrix.trace]

end T117QReview

/-! ## Kernel-side enumeration of both frozen modules -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let standard : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for mod in [`T117Q, `Controls] do
    let some idx := env.getModuleIdx? mod | throwError "module missing: {mod}"
    let names := env.header.moduleData[idx.toNat]!.constNames
    let mut publicNames : Array Name := #[]
    for n in names do
      let some ci := env.find? n | throwError "constant missing: {n}"
      if ci.isUnsafe then throwError "unsafe constant: {n}"
      match ci with
      | .axiomInfo _ => throwError "axiom declared: {n}"
      | .opaqueInfo _ => logInfo m!"opaque constant: {n}"
      | _ => pure ()
      let axs ← collectAxioms n
      for a in axs do
        unless standard.contains a do throwError "nonstandard axiom {a} in {n}"
      unless n.isInternalDetail do publicNames := publicNames.push n
    logInfo m!"module {mod}: {names.size} constants total, {publicNames.size} non-internal"
    for n in publicNames do logInfo m!"  {n}"
