import ShoeConditional
import Mathlib.Probability.Independence.InfinitePi

namespace Shoe
open MeasureTheory
open scoped ENNReal

abbrev PairBlock := Fin 2 → ℕ
noncomputable def blockMeasure (p : DiscreteLaw ℕ) : Measure PairBlock :=
  Measure.infinitePi (fun _ : Fin 2 => p.toMeasure)

instance blockMeasure_probability (p : DiscreteLaw ℕ) :
    IsProbabilityMeasure (blockMeasure p) := by
  unfold blockMeasure
  infer_instance

def blocks (ω : Sample ℕ) (n : ℕ) (j : Fin 2) : ℕ := ω (2*n+j.val)

theorem blocks_law (p : DiscreteLaw ℕ) :
    (sampleMeasure p).map blocks = Measure.infinitePi (fun _ : ℕ => blockMeasure p) := by
  have hinj : Function.Injective (fun z : ℕ × Fin 2 => 2*z.1+z.2.val) := by
    intro x y h
    change 2*x.1+x.2.val = 2*y.1+y.2.val at h
    have hx := x.2.isLt
    have hy := y.2.isLt
    have h1 : x.1 = y.1 := by omega
    have h2 : x.2 = y.2 := Fin.ext (by omega)
    exact Prod.ext h1 h2
  have hmap := Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : ℕ => p.toMeasure) hinj
  have hc := Measure.infinitePi_map_curry (μ := fun (_ : ℕ) (_ : Fin 2) => p.toMeasure)
  unfold sampleMeasure blockMeasure
  rw [← hc, ← hmap, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

theorem block_zero_law (p : DiscreteLaw ℕ) :
    (sampleMeasure p).map (fun ω => blocks ω 0) = blockMeasure p := by
  have h := Measure.infinitePi_map_eval (fun _ : ℕ => blockMeasure p) 0
  rw [← blocks_law p, Measure.map_map (by fun_prop) (by unfold blocks; fun_prop)] at h
  exact h

theorem block_equality_probability (p : DiscreteLaw ℕ) :
    blockMeasure p {v | v 0 = v 1} = collisionMass p := by
  rw [← block_zero_law p, Measure.map_apply (by unfold blocks; fun_prop)
    (measurableSet_eq_fun (measurable_pi_apply 0) (measurable_pi_apply 1))]
  exact pair_equality_probability p

theorem block_inequality_probability (p : DiscreteLaw ℕ) :
    blockMeasure p {v | v 0 ≠ v 1} = 1 - collisionMass p := by
  rw [← block_equality_probability p]
  have hm : MeasurableSet {v : PairBlock | v 0 = v 1} :=
    measurableSet_eq_fun (measurable_pi_apply 0) (measurable_pi_apply 1)
  have he : {v : PairBlock | v 0 ≠ v 1} = {v : PairBlock | v 0 = v 1}ᶜ := by
    ext v
    rfl
  rw [he, measure_compl hm (measure_ne_top (blockMeasure p) _), measure_univ]

/-- Independence of all N aligned pair failures is derived from reindexing the
actual shoe product space, rather than assumed as a stopping-law hypothesis. -/
theorem diagonal_failure_probability (p : DiscreteLaw ℕ) (N : ℕ) :
    sampleMeasure p {ω | ∀ j < N, ω (2*j) ≠ ω (2*j+1)} =
      (1 - collisionMass p)^N := by
  have hset : (blocks ⁻¹' (Set.pi ((Finset.range N : Finset ℕ) : Set ℕ)
      (fun _ => {v : PairBlock | v 0 ≠ v 1}))) =
      {ω | ∀ j < N, ω (2*j) ≠ ω (2*j+1)} := by
    ext ω
    simp [blocks]
  rw [← hset, ← Measure.map_apply (by unfold blocks; fun_prop)
    (MeasurableSet.pi (Finset.countable_toSet _)
      (by intros; exact (measurableSet_eq_fun (measurable_pi_apply 0)
        (measurable_pi_apply 1)).compl)), blocks_law p,
      Measure.infinitePi_pi _ (by intros; exact (measurableSet_eq_fun
        (measurable_pi_apply 0) (measurable_pi_apply 1)).compl)]
  simp [block_inequality_probability]

theorem stopping_tail_bound (p : DiscreteLaw ℕ) (N : ℕ) :
    sampleMeasure p {ω | ¬ HasMatch ω (2*N)} ≤ (1-collisionMass p)^N := by
  rw [← diagonal_failure_probability]
  apply measure_mono
  intro ω h j hj
  exact no_match_diagonal h hj

end Shoe
