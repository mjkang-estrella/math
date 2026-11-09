import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Order.LocalExtr
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

open scoped BigOperators Topology
namespace MathDB368007
noncomputable def mass : Fin 3 → ℝ := ![8 / Real.sqrt 129, -1 / Real.sqrt 129, 8 / Real.sqrt 129]
def witness : Fin 3 → ℝ := ![-1, 0, 1]
noncomputable def energy (m x : Fin 3 → ℝ) : ℝ :=
  ∑ i, ∑ j, if i = j then 0 else -2 * m i * m j / |x i - x j| ^ (1 + 2 * (1/2 : ℝ))
def chamber : Set (Fin 3 → ℝ) := {x | x 0 < x 1 ∧ x 1 < x 2}
lemma sqrt_sq : (Real.sqrt (129 : ℝ)) ^ 2 = 129 := Real.sq_sqrt (by norm_num)
lemma sqrt_ne : Real.sqrt (129 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
theorem normalized : ∑ i, |mass i| ^ 2 = 1 := by
  simp [Fin.sum_univ_succ, mass, sq_abs]
  field_simp
  nlinarith [sqrt_sq]
lemma energy_formula (x : Fin 3 → ℝ) : energy mass x =
    (32 / 129 : ℝ) * (1 / (x 1 - x 0)^2 + 1 / (x 2 - x 1)^2 -
      8 / (x 2 - x 0)^2) := by
  norm_num [energy, mass, Fin.sum_univ_succ, Real.rpow_two, sq_abs]
  rw [show (x 0 - x 1)^2 = (x 1 - x 0)^2 by ring,
      show (x 0 - x 2)^2 = (x 2 - x 0)^2 by ring,
      show (x 1 - x 2)^2 = (x 2 - x 1)^2 by ring]
  field_simp [sqrt_ne]
  rw [sqrt_sq]
  ring
lemma gap_nonneg {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    0 ≤ 1/u^2 + 1/v^2 - 8/(u+v)^2 := by
  have h : 1/u^2 + 1/v^2 - 8/(u+v)^2 =
      (u-v)^2 * (u^2 + 4*u*v + v^2) / (u^2*v^2*(u+v)^2) := by
    field_simp
    ring
  rw [h]
  positivity
lemma nonneg (x : Fin 3 → ℝ) (hx : x ∈ chamber) : 0 ≤ energy mass x := by
  rw [energy_formula]
  apply mul_nonneg (by norm_num)
  have hu : 0 < x 1 - x 0 := sub_pos.2 hx.1
  have hv : 0 < x 2 - x 1 := sub_pos.2 hx.2
  convert gap_nonneg hu hv using 1
  ring
lemma at_witness : energy mass witness = 0 := by
  rw [energy_formula]
  norm_num [witness]
theorem local_minimum : IsLocalMin (energy mass) witness := by
  have ho : IsOpen chamber :=
    (isOpen_lt (continuous_apply 0) (continuous_apply 1)).inter
      (isOpen_lt (continuous_apply 1) (continuous_apply 2))
  have hw : witness ∈ chamber := by norm_num [chamber, witness]
  apply IsMinOn.isLocalMin (s := chamber) _ (ho.mem_nhds hw)
  intro x hx
  rw [at_witness]
  exact nonneg x hx
noncomputable def energyN (n d : ℕ) (s : ℝ) (m : Fin d → ℝ)
    (x : Fin d → EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ i, ∑ j, if i = j then 0 else
    -2 * m i * m j / ‖x i - x j‖ ^ ((n : ℝ) + 2 * s)
def lift (x : Fin 3 → ℝ) : Fin 3 → EuclideanSpace ℝ (Fin 1) :=
  fun i => WithLp.toLp 2 (fun _ => x i)
def coords (x : Fin 3 → EuclideanSpace ℝ (Fin 1)) : Fin 3 → ℝ := fun i => x i 0
lemma norm_one (z : EuclideanSpace ℝ (Fin 1)) : ‖z‖ = |z 0| := by
  simp [EuclideanSpace.norm_eq, Real.norm_eq_abs, Real.sqrt_sq_eq_abs]
lemma bridge (x : Fin 3 → EuclideanSpace ℝ (Fin 1)) :
    energyN 1 3 (1/2) mass x = energy mass (coords x) := by
  simp only [energyN, energy, norm_one, PiLp.sub_apply, Nat.cast_one, coords]
lemma coords_continuous : Continuous coords := by
  apply continuous_pi
  intro i
  exact (PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) 0).comp (continuous_apply i)
lemma coords_lift (x : Fin 3 → ℝ) : coords (lift x) = x := by
  rfl
theorem euclidean_local_minimum : IsLocalMin (energyN 1 3 (1/2) mass) (lift witness) := by
  have h : IsLocalMin (energy mass ∘ coords) (lift witness) := by
    apply IsLocalMin.comp_continuous (g := coords)
    · simpa only [coords_lift] using local_minimum
    · exact coords_continuous.continuousAt
  have he : energyN 1 3 (1/2) mass = energy mass ∘ coords := by
    funext x
    exact bridge x
  rw [he]
  exact h
theorem mass_nonzero (i : Fin 3) : mass i ≠ 0 := by
  fin_cases i <;> norm_num [mass, sqrt_ne]
theorem witness_injective : Function.Injective (lift witness) := by
  intro i j h
  have h0 := congrArg (fun z : EuclideanSpace ℝ (Fin 1) => z 0) h
  fin_cases i <;> fin_cases j <;> norm_num [lift, witness] at *

def NoLocalMinimumConjecture : Prop :=
  ∀ (n d : ℕ) (s : ℝ) (m : Fin d → ℝ)
    (x : Fin d → EuclideanSpace ℝ (Fin n)),
    0 < n → 2 ≤ d → 0 < s → s < 1 →
    (∑ i, |m i| ^ 2) = 1 → Function.Injective x →
    ¬ IsLocalMin (energyN n d s m) x

theorem source_refutation : ¬ NoLocalMinimumConjecture := by
  intro h
  exact h 1 3 (1/2) mass (lift witness) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) normalized witness_injective euclidean_local_minimum
end MathDB368007

