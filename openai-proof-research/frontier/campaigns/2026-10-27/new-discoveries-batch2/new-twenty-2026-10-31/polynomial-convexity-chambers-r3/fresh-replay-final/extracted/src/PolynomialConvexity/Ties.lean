import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod

set_option Elab.async false
namespace PolynomialConvexity
noncomputable section
open MeasureTheory Set Filter

/-- Ties concern coordinate labels, irrespective of edge coincidences. -/
theorem volume_coordinate_ne {d : ℕ} (i j : Fin d) (hij : i ≠ j) :
    ∀ᵐ t : Fin d → ℝ ∂volume, t i ≠ t j := by
  cases d with
  | zero => exact Fin.elim0 i
  | succ d =>
    obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq (Ne.symm hij)
    subst j
    have h : ∀ᵐ p : ℝ × (Fin d → ℝ) ∂(volume.prod volume), p.1 ≠ p.2 k := by
      apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun measurable_fst
        ((measurable_pi_apply k).comp measurable_snd)).compl).mpr
      exact Filter.Eventually.of_forall fun x => by
        rw [volume_pi]
        exact (Measure.ae_eval_ne (fun _ : Fin d => (volume : Measure ℝ)) k x).mono
          (fun _ ht => Ne.symm ht)
    have hp := (volume_preserving_piFinSuccAbove (fun _ : Fin (d+1) => ℝ) i).quasiMeasurePreserving.ae h
    simpa [Fin.removeNth] using hp

theorem volume_coordinates_injective (d : ℕ) :
    ∀ᵐ t : Fin d → ℝ ∂volume, Function.Injective t := by
  have h : ∀ᵐ t : Fin d → ℝ ∂volume, ∀ i j, i ≠ j → t i ≠ t j := by
    simp only [ae_all_iff]
    exact fun i j hij => volume_coordinate_ne i j hij
  exact h.mono fun _ ht i j heq => by
    by_contra hij
    exact ht i j hij heq


end
end PolynomialConvexity
