module
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Analysis.Convex.Function
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public section
noncomputable section
open Real MeasureTheory Set
namespace PendulumTimeMap
def b (z : ℝ) : ℝ := Real.arccos (1-z)/2
def a (phi : ℝ) : ℝ := 1-Real.cos (2*phi)
def sourceKernel (phi z x : ℝ) : ℝ := (Real.sqrt (z-Real.cos (2*phi)+Real.cos (2*x)))⁻¹
def sourceTime (phi z : ℝ) : ℝ :=
 (∫ x in 0..phi, sourceKernel phi z x) + (∫ x in 0..b z, sourceKernel phi z x)
def transformedKernel (a z t : ℝ) : ℝ := (Real.sqrt (t*(2-t)*(a+z-t)))⁻¹
def transformedTime (a z : ℝ) : ℝ :=
 (1/2:ℝ)*((∫ t in 0..a, transformedKernel a z t)+(∫ t in 0..z, transformedKernel a z t))
def momentKernel (n : ℕ) (a z t : ℝ) : ℝ := t^n / Real.sqrt (t*(a+z-t))
def moment (n : ℕ) (a z : ℝ) : ℝ :=
 (∫ t in 0..a, momentKernel n a z t)+(∫ t in 0..z, momentKernel n a z t)
def SourceClaim : Prop := ∀ phi : ℝ, 0<phi → phi<Real.pi/2 →
 ConvexOn ℝ (Set.Icc 0 2) (sourceTime phi)
theorem a_range {phi : ℝ} (h0 : 0<phi) (h1 : phi<Real.pi/2) : 0<a phi ∧ a phi<2 := by
 have h := Real.cos_lt_cos_of_nonneg_of_le_pi (x := 0) (y := 2*phi) (by norm_num) (by linarith) (by linarith)
 have k := Real.cos_lt_cos_of_nonneg_of_le_pi (x := 2*phi) (y := Real.pi) (by linarith) le_rfl (by linarith)
 simp only [Real.cos_zero, Real.cos_pi] at h k
 constructor <;> unfold a <;> linarith
theorem b_range {z : ℝ} (h0 : 0<z) (h1 : z<2) : 0<b z ∧ b z<Real.pi/2 := by
 have h := Real.arccos_pos.mpr (show 1-z<1 by linarith)
 have k := Real.arccos_lt_pi.mpr (show -1<1-z by linarith)
 constructor <;> unfold b <;> linarith
theorem a_b {z : ℝ} (h0 : 0≤z) (h1 : z≤2) : a (b z)=z := by
 unfold a b
 rw [show 2*(Real.arccos (1-z)/2)=Real.arccos (1-z) by ring,
 Real.cos_arccos (by linarith) (by linarith)]
 ring
end PendulumTimeMap
