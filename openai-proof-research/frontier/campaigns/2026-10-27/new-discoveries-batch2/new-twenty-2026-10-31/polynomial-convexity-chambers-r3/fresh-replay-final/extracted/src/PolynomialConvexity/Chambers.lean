import PolynomialConvexity.Ties
import Mathlib.Data.Fin.Tuple.Sort
set_option Elab.async false
namespace PolynomialConvexity
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
/-- Strict descending labelled chamber inside the positive orthant. -/
def chamber {d : ℕ} (σ : Equiv.Perm (Fin d)) : Set (Fin d → ℝ) :=
  {t | (∀ i, 0 < t i) ∧ StrictAnti (t ∘ σ)}

theorem chamber_measurable {d : ℕ} (σ : Equiv.Perm (Fin d)) :
    MeasurableSet (chamber σ) := by
  have heq : chamber σ =
      (⋂ i, {t : Fin d → ℝ | 0 < t i}) ∩
      (⋂ i, ⋂ j, {t : Fin d → ℝ | i < j → t (σ j) < t (σ i)}) := by
    ext t
    simp only [chamber, mem_ofPred_eq, mem_inter_iff, mem_iInter, StrictAnti, Function.comp_apply]
  rw [heq]
  refine (MeasurableSet.iInter fun i => measurableSet_lt measurable_const (measurable_pi_apply i)).inter ?_
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro j
  by_cases hij : i < j
  · simpa only [hij, true_implies] using measurableSet_lt (measurable_pi_apply (σ j)) (measurable_pi_apply (σ i))
  · simp only [hij, false_implies, ofPred_true, MeasurableSet.univ]

theorem chamber_unique {d : ℕ} {t : Fin d → ℝ} {σ τ : Equiv.Perm (Fin d)}
    (hσ : t ∈ chamber σ) (hτ : t ∈ chamber τ) : σ = τ := by
  have ht : Function.Injective t := by
    have h : Function.Injective (t ∘ σ) := hσ.2.injective
    simpa [Function.comp_def] using h.comp σ.symm.injective
  have heq := Tuple.unique_antitone hσ.2.antitone hτ.2.antitone
  apply Equiv.ext
  intro i
  exact ht (congrFun heq i)

theorem chamber_cover {d : ℕ} {t : Fin d → ℝ} (ht : Function.Injective t)
    (hpos : ∀ i, 0 < t i) : ∃ σ, t ∈ chamber σ := by
  let σ := Tuple.sort (fun i => OrderDual.toDual (t i))
  have ha : Antitone (t ∘ σ) := Tuple.monotone_sort (fun i => OrderDual.toDual (t i))
  exact ⟨σ, hpos, ha.strictAnti_of_injective (ht.comp σ.injective)⟩


theorem chambers_disjoint (d : ℕ) : Pairwise (fun σ τ : Equiv.Perm (Fin d) => Disjoint (chamber σ) (chamber τ)) := by
  intro σ τ hne
  exact disjoint_left.mpr fun _ hσ hτ => hne (chamber_unique hσ hτ)

theorem chambers_cover_ae (d : ℕ) :
    (⋃ σ : Equiv.Perm (Fin d), chamber σ) =ᵐ[volume]
      Set.pi Set.univ (fun _ => Ioi (0 : ℝ)) := by
  filter_upwards [volume_coordinates_injective d] with t ht
  apply propext
  simp only [mem_iUnion, Set.mem_pi, mem_univ, forall_true_left, mem_Ioi]
  exact ⟨fun ⟨_, h⟩ => h.1, chamber_cover ht⟩

/-- Actual integral partition with all labelled permutations, also for repeated edges. -/
theorem chamber_lintegral_partition (d : ℕ) (f : (Fin d → ℝ) → ℝ≥0∞) :
    (∫⁻ t in Set.pi Set.univ (fun _ => Ioi (0 : ℝ)), f t) =
      ∑ σ : Equiv.Perm (Fin d), ∫⁻ t in chamber σ, f t := by
  rw [← setLIntegral_congr (chambers_cover_ae d),
    lintegral_iUnion (fun σ => chamber_measurable σ) (chambers_disjoint d)]
  exact tsum_fintype _

end
end PolynomialConvexity
