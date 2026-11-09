import Endpoint
import Lean.Util.FoldConsts
open SpectralExclusion SpectralSemantics
set_option autoImplicit false

-- Review-only definitional check: the root-norm supremum is precisely the
-- determinant-root supremum for the actual displayed matrix.
theorem review_radius_det (a b c d : ℝ) : radius a b c d =
    sSup {r : ℝ | ∃ z : ℂ,
      Matrix.det (z • (1 : Matrix (Fin 2) (Fin 2) ℂ) -
        !![(a:ℂ), (b:ℂ); (c:ℂ), (d:ℂ)]) = 0 ∧ ‖z‖=r} := by
  simp only [det_bridge]
  rfl

theorem review_five_nonempty :
    {n : ℕ | ∃ A : Finset ℝ, A.card=5 ∧ (∀ a ∈ A, 0<a) ∧ (sourceOmega A).card=n}.Nonempty := by
  classical
  refine ⟨(sourceOmega (castSet positiveSet)).card, castSet positiveSet, ?_, ?_, rfl⟩
  · norm_num [castSet, positiveSet]
  · intro a ha
    simp only [castSet, positiveSet, Finset.mem_image, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with ⟨n, hn, rfl⟩
    rcases hn with rfl | rfl | rfl | rfl | rfl <;> norm_num

#print axioms review_radius_det
#print axioms review_five_nonempty
#print axioms SpectralExclusion.source_conjecture_refuted

open Lean in
run_cmd do
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut todo := [``SpectralExclusion.source_conjecture_refuted]
  while !todo.isEmpty do
    let n := todo.head!
    todo := todo.tail!
    if !seen.contains n then
      seen := seen.insert n
      if let some ci := env.find? n then
        let mut deps := ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then deps := deps ++ v.getUsedConstants
        todo := deps.toList ++ todo
  for n in [``SpectralExclusion.zero_separated, ``SpectralExclusion.incompatible_sound,
      ``SpectralExclusion.canon_sound, ``SpectralExclusion.omega_source,
      ``SpectralExclusion.raw_formula, ``SpectralSemantics.radius_formula,
      ``SpectralSemantics.roots, ``SpectralSemantics.det_bridge] do
    logInfo m!"dependency {n}: {seen.contains n}"
