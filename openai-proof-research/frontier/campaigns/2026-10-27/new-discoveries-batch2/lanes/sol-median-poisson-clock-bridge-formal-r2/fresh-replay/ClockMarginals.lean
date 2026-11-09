import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option warningAsError true
open MeasureTheory
open scoped BigOperators ENNReal NNReal
namespace MedianClock
abbrev Vertex := Fin 10
abbrev Config := Vertex → Bool
noncomputable def weight (s : Config) : ℝ := ∏ i : Vertex, if s i then 2 else 3

noncomputable def spinPMF : PMF Bool :=
  ⟨fun b => if b then ((2/5:ℝ≥0):ℝ≥0∞) else ((3/5:ℝ≥0):ℝ≥0∞), by
    convert (hasSum_fintype (fun b : Bool => if b then ((2/5:ℝ≥0):ℝ≥0∞) else ((3/5:ℝ≥0):ℝ≥0∞))) using 1
    simp only [Fintype.sum_bool, Bool.false_eq_true, reduceIte]
    rw [← ENNReal.coe_add]
    exact congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞)) (by norm_num : (1:ℝ≥0) = 2/5+3/5)⟩
noncomputable def spinLaw : Measure Bool := spinPMF.toMeasure
noncomputable def initialLaw : Measure Config := Measure.pi (fun _ : Vertex => spinLaw)
instance : IsProbabilityMeasure spinLaw := by unfold spinLaw; infer_instance
instance : IsProbabilityMeasure initialLaw := by unfold initialLaw; infer_instance

theorem spin_mass (b : Bool) : spinLaw.real {b} = if b then 2/5 else 3/5 := by
  unfold spinLaw
  rw [measureReal_def, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  change (if b then ((2/5:ℝ≥0):ℝ≥0∞) else ((3/5:ℝ≥0):ℝ≥0∞)).toReal = _
  cases b <;> norm_num

theorem initial_rectangles (a : Vertex → Set Bool) :
    initialLaw (Set.univ.pi a) = ∏ i, spinLaw (a i) := Measure.pi_pi _ _

theorem initial_coordinate (i : Vertex) : initialLaw.map (fun s => s i) = spinLaw := by
  exact (measurePreserving_eval (fun _ : Vertex => spinLaw) i).map_eq

theorem initial_mass (s : Config) : initialLaw.real {s} = weight s / (5:ℝ)^10 := by
  change (initialLaw {s}).toReal = _
  rw [initialLaw, Measure.pi_singleton, ENNReal.toReal_prod]
  change (∏ i : Vertex, spinLaw.real {s i}) = _
  simp_rw [spin_mass]
  calc
    (∏ i : Vertex, if s i then (2:ℝ)/5 else 3/5) =
        ∏ i : Vertex, (if s i then (2:ℝ) else 3) / 5 := by
      congr 1; funext i; cases s i <;> rfl
    _ = weight s / (5:ℝ)^10 := by rw [Finset.prod_div_distrib]; simp [weight]

noncomputable def uniformMark : PMF Vertex :=
  ⟨fun _ => ((1/10:ℝ≥0):ℝ≥0∞), by
    convert (hasSum_fintype (fun _ : Vertex => ((1/10:ℝ≥0):ℝ≥0∞))) using 1
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    change (1:ℝ≥0∞) = 10 * ((1/10:ℝ≥0):ℝ≥0∞)
    rw [show (10:ℝ≥0∞) = ((10:ℝ≥0):ℝ≥0∞) from rfl, ← ENNReal.coe_mul]
    exact congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞)) (by norm_num : (1:ℝ≥0) = 10*(1/10))⟩
noncomputable def markLaw : Measure Vertex := uniformMark.toMeasure
instance : IsProbabilityMeasure markLaw := by unfold markLaw; infer_instance
noncomputable def prefixLaw (k : ℕ) : Measure (Fin k → Vertex) :=
  Measure.pi (fun _ => markLaw)
instance (k : ℕ) : IsProbabilityMeasure (prefixLaw k) := by unfold prefixLaw; infer_instance

theorem mark_mass (i : Vertex) : markLaw.real {i} = 1/10 := by
  unfold markLaw
  rw [measureReal_def, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  change (((1/10:ℝ≥0):ℝ≥0∞)).toReal = _
  norm_num

theorem prefix_rectangles (k : ℕ) (a : Fin k → Set Vertex) :
    prefixLaw k (Set.univ.pi a) = ∏ i, markLaw (a i) := Measure.pi_pi _ _

theorem prefix_mass (k : ℕ) (w : Fin k → Vertex) :
    (prefixLaw k).real {w} = (1/10:ℝ)^k := by
  change ((prefixLaw k) {w}).toReal = _
  rw [prefixLaw, Measure.pi_singleton, ENNReal.toReal_prod]
  change (∏ i : Fin k, markLaw.real {w i}) = _
  simp [mark_mass]

end MedianClock
