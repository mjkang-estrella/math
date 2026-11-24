# Lean source appendix

Modules in dependency order. Each fenced body is byte-identical to its source.

### `ExponentialEigenvector.lean`

```lean
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic
open Matrix
open scoped BigOperators
noncomputable section
namespace Pool012
variable {n : Type*} [Fintype n] [DecidableEq n]
lemma matrix_pow_mulVec_eigen (M : Matrix n n ℂ) (v : n → ℂ) (z : ℂ)
    (h : M *ᵥ v = z • v) (k : ℕ) : (M ^ k) *ᵥ v = z ^ k • v := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, h,
      smul_smul, pow_succ]

lemma matrix_exp_mulVec_eigen (M : Matrix n n ℂ) (v : n → ℂ) (z : ℂ)
    (h : M *ᵥ v = z • v) : (NormedSpace.exp M) *ᵥ v = Complex.exp z • v := by
  let := Matrix.linftyOpNormedRing (n := n) (α := ℂ)
  let := Matrix.linftyOpNormedSpace (m := n) (n := n) (R := ℂ) (α := ℂ)
  let := Matrix.linftyOpNormedAlgebra (n := n) (R := ℂ) (α := ℂ)
  let f : Matrix n n ℂ →ₗ[ℂ] (n → ℂ) :=
    { toFun := fun A => A *ᵥ v
      map_add' := fun A B => Matrix.add_mulVec A B v
      map_smul' := fun c A => Matrix.smul_mulVec c A v }
  let fc := f.toContinuousLinearMap
  change fc (NormedSpace.exp M) = Complex.exp z • v
  rw [NormedSpace.exp_eq_tsum ℂ]
  rw [fc.map_tsum (NormedSpace.expSeries_summable' (𝕂 := ℂ) M)]
  simp_rw [ContinuousLinearMap.map_smul]
  change (∑' k : ℕ, ((k.factorial : ℂ)⁻¹) • ((M ^ k) *ᵥ v)) = _
  simp_rw [matrix_pow_mulVec_eigen M v z h, smul_smul]
  have hs : Summable (fun k : ℕ => ((k.factorial : ℂ)⁻¹) * z ^ k) := by
    simpa only [smul_eq_mul] using (NormedSpace.expSeries_summable' (𝕂 := ℂ) z)
  rw [hs.tsum_smul_const v, Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum ℂ]
  rfl
#print axioms matrix_pow_mulVec_eigen
#print axioms matrix_exp_mulVec_eigen
end Pool012
```

### `PSTGraph.lean`

```lean
import ExponentialEigenvector
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

open Matrix
open scoped BigOperators
namespace Pool012

def forwardEdge (x y : Fin 35) : Prop :=
  (x.val < 2 ∧ 2 ≤ y.val ∧ y.val < 24) ∨
  (2 ≤ x.val ∧ x.val < 24 ∧ 24 ≤ y.val ∧
    (y.val - 24 + 11 - ((x.val - 2) % 11)) % 11 < 8)

instance : DecidableRel forwardEdge := fun _ _ => by unfold forwardEdge; infer_instance

def witnessGraph : SimpleGraph (Fin 35) where
  Adj x y := forwardEdge x y ∨ forwardEdge y x
  symm := ⟨by intro x y h; exact h.symm⟩
  loopless := ⟨by decide⟩

instance : DecidableRel witnessGraph.Adj := fun _ _ => by change Decidable (_ ∨ _); infer_instance

theorem witness_connected : witnessGraph.Connected := by
  apply (witnessGraph.connected_iff_exists_forall_reachable).mpr
  refine ⟨0, ?_⟩
  intro w
  fin_cases w
  all_goals first
    | exact SimpleGraph.Reachable.rfl
    | exact (show witnessGraph.Adj 0 _ from by decide).reachable
    | exact (show witnessGraph.Adj 0 2 from by decide).reachable.trans
        (show witnessGraph.Adj 2 _ from by decide).reachable
    | exact (show witnessGraph.Adj 0 3 from by decide).reachable.trans
        (show witnessGraph.Adj 3 _ from by decide).reachable
    | exact (show witnessGraph.Adj 0 4 from by decide).reachable.trans
        (show witnessGraph.Adj 4 _ from by decide).reachable
    | exact (show witnessGraph.Adj 0 5 from by decide).reachable.trans
        (show witnessGraph.Adj 5 _ from by decide).reachable


#print axioms witness_connected
end Pool012
```

### `PSTWitness.lean`

```lean
import PSTGraph
open Matrix
open scoped BigOperators
namespace Pool012
def va : Fin 35 → ℤ := fun x => if x = 0 then 1 else if x = 1 then -1 else 0
def vj : Fin 35 → ℤ := fun _ => 1
def vx20 : Fin 35 → ℤ := fun x => if x.val < 2 then 11 else if x.val < 24 then 1 else -4
def vx28 : Fin 35 → ℤ := fun x => if x.val < 2 then -11 else if x.val < 24 then 3 else -4

def deg : Fin 35 → ℕ := fun x => if x.val < 2 then 22 else if x.val < 24 then 10 else 16
theorem witness_degree (x : Fin 35) : witnessGraph.degree x = deg x := by
  simp only [SimpleGraph.degree, SimpleGraph.neighborFinset, SimpleGraph.neighborSet]
  fin_cases x <;> decide
theorem finite_eigen_a : witnessGraph.lapMatrix ℤ *ᵥ va = (22 : ℤ) • va := by
  ext i
  rw [SimpleGraph.lapMatrix_mulVec_apply, witness_degree,
    SimpleGraph.neighborFinset_eq_filter]
  fin_cases i <;> decide
theorem finite_eigen_j : witnessGraph.lapMatrix ℤ *ᵥ vj = (0 : ℤ) • vj := by
  change witnessGraph.lapMatrix ℤ *ᵥ (1 : Fin 35 → ℤ) = (0 : ℤ) • (1 : Fin 35 → ℤ)
  rw [zero_smul]
  exact witnessGraph.lapMatrix_mulVec_one_eq_zero ℤ
theorem finite_eigen_20 : witnessGraph.lapMatrix ℤ *ᵥ vx20 = (20 : ℤ) • vx20 := by
  ext i
  rw [SimpleGraph.lapMatrix_mulVec_apply, witness_degree,
    SimpleGraph.neighborFinset_eq_filter]
  fin_cases i <;> decide
theorem finite_eigen_28 : witnessGraph.lapMatrix ℤ *ᵥ vx28 = (28 : ℤ) • vx28 := by
  ext i
  rw [SimpleGraph.lapMatrix_mulVec_apply, witness_degree,
    SimpleGraph.neighborFinset_eq_filter]
  fin_cases i <;> decide
#print axioms witness_degree
#print axioms finite_eigen_a
#print axioms finite_eigen_j
#print axioms finite_eigen_20
#print axioms finite_eigen_28
end Pool012
```

### `PSTEndpoint.lean`

```lean
import PSTWitness
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Matrix
open scoped BigOperators
noncomputable section
namespace Pool012

def cv (v : Fin 35 → ℤ) : Fin 35 → ℂ := fun x => (v x : ℂ)

lemma cast_eigen (v : Fin 35 → ℤ) (z : ℤ)
    (h : witnessGraph.lapMatrix ℤ *ᵥ v = z • v) :
    witnessGraph.lapMatrix ℂ *ᵥ cv v = (z : ℂ) • cv v := by
  ext i
  have hi := congrFun h i
  rw [SimpleGraph.lapMatrix_mulVec_apply] at hi
  have hc := congrArg (fun x : ℤ => (x : ℂ)) hi
  simpa [SimpleGraph.lapMatrix_mulVec_apply, cv, smul_eq_mul] using hc

def tau : ℂ := ((Real.pi / 2 : ℝ) : ℂ) * Complex.I
def U : Matrix (Fin 35) (Fin 35) ℂ := NormedSpace.exp (tau • witnessGraph.lapMatrix ℂ)

lemma exp_phase_zero : Complex.exp (tau * (0 : ℂ)) = 1 := by simp
lemma exp_phase_twenty : Complex.exp (tau * (20 : ℂ)) = 1 := by
  have he : tau * (20 : ℂ) = (10 : ℕ) * ((Real.pi : ℂ) * Complex.I) := by
    simp only [tau, Complex.ofReal_div, Complex.ofReal_ofNat]
    ring
  rw [he, Complex.exp_nat_mul, Complex.exp_pi_mul_I]
  norm_num
lemma exp_phase_twenty_eight : Complex.exp (tau * (28 : ℂ)) = 1 := by
  have he : tau * (28 : ℂ) = (14 : ℕ) * ((Real.pi : ℂ) * Complex.I) := by
    simp only [tau, Complex.ofReal_div, Complex.ofReal_ofNat]
    ring
  rw [he, Complex.exp_nat_mul, Complex.exp_pi_mul_I]
  norm_num
lemma exp_phase_twenty_two : Complex.exp (tau * (22 : ℂ)) = -1 := by
  have he : tau * (22 : ℂ) = (11 : ℕ) * ((Real.pi : ℂ) * Complex.I) := by
    simp only [tau, Complex.ofReal_div, Complex.ofReal_ofNat]
    ring
  rw [he, Complex.exp_nat_mul, Complex.exp_pi_mul_I]
  norm_num

lemma U_eigen (v : Fin 35 → ℤ) (z : ℤ)
    (h : witnessGraph.lapMatrix ℤ *ᵥ v = z • v) :
    U *ᵥ cv v = Complex.exp (tau * (z : ℂ)) • cv v := by
  apply matrix_exp_mulVec_eigen
  rw [Matrix.smul_mulVec, cast_eigen v z h, smul_smul]

lemma U_a : U *ᵥ cv va = -cv va := by
  simpa only [Int.cast_ofNat, exp_phase_twenty_two, neg_one_smul]
    using U_eigen va 22 finite_eigen_a
lemma U_j : U *ᵥ cv vj = cv vj := by
  simpa only [Int.cast_zero, exp_phase_zero, one_smul]
    using U_eigen vj 0 finite_eigen_j
lemma U_20 : U *ᵥ cv vx20 = cv vx20 := by
  simpa only [Int.cast_ofNat, exp_phase_twenty, one_smul]
    using U_eigen vx20 20 finite_eigen_20
lemma U_28 : U *ᵥ cv vx28 = cv vx28 := by
  simpa only [Int.cast_ofNat, exp_phase_twenty_eight, one_smul]
    using U_eigen vx28 28 finite_eigen_28

lemma decomp_u : Pi.single (0 : Fin 35) (1 : ℂ) =
    (1/2 : ℂ) • cv va + (1/35 : ℂ) • cv vj +
      (1/40 : ℂ) • cv vx20 - (1/56 : ℂ) • cv vx28 := by
  ext i
  fin_cases i <;> norm_num [cv, va, vj, vx20, vx28, Pi.single_apply]

lemma decomp_v : Pi.single (1 : Fin 35) (1 : ℂ) =
    (-1/2 : ℂ) • cv va + (1/35 : ℂ) • cv vj +
      (1/40 : ℂ) • cv vx20 - (1/56 : ℂ) • cv vx28 := by
  ext i
  fin_cases i <;> norm_num [cv, va, vj, vx20, vx28, Pi.single_apply]

theorem witness_exact_transfer :
    U *ᵥ Pi.single (0 : Fin 35) (1 : ℂ) = Pi.single (1 : Fin 35) (1 : ℂ) := by
  rw [decomp_u, decomp_v]
  simp only [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul,
    U_a, U_j, U_20, U_28, smul_neg, neg_div, neg_smul]

theorem witness_transfer_entry :
    (NormedSpace.exp ((((Real.pi / 2 : ℝ) : ℂ) * Complex.I) •
      witnessGraph.lapMatrix ℂ)) (1 : Fin 35) (0 : Fin 35) = 1 := by
  have h := congrFun witness_exact_transfer (1 : Fin 35)
  rw [Matrix.mulVec_single_one] at h
  simpa only [Matrix.col_apply, Pi.single_eq_same, U, tau] using h

def oddLaplacianClaim : Prop :=
  ∀ (n : ℕ), Odd n → ∀ (G : SimpleGraph (Fin n)),
    ∀ [DecidableRel G.Adj], G.Connected →
      ∀ u v : Fin n, u ≠ v → ∀ t : ℝ, 0 < t →
        ‖(NormedSpace.exp (((t : ℂ) * Complex.I) • G.lapMatrix ℂ)) v u‖ ≠ 1

theorem odd_order_laplacian_pst_refuted : ¬oddLaplacianClaim := by
  intro h
  have hn := h 35 (by decide) witnessGraph witness_connected
    (0 : Fin 35) (1 : Fin 35) (by decide) (Real.pi / 2) (by positivity)
  apply hn
  rw [witness_transfer_entry, norm_one]

#print axioms cast_eigen
#print axioms exp_phase_twenty_two
#print axioms witness_exact_transfer
#print oddLaplacianClaim
#print axioms odd_order_laplacian_pst_refuted
end Pool012
```

### `PSTSource.lean`

```lean
import PSTEndpoint

noncomputable section
namespace Pool012

/-- Source §2, with the entry indexed as destination, source. -/
def laplacianPST {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u v : Fin n) (t : ℝ) : Prop :=
  ‖(NormedSpace.exp (((t : ℂ) * Complex.I) • G.lapMatrix ℂ)) v u‖ = 1

/-- Conjecture 77, with positive transfer time and distinct vertices. -/
def sourceConjecture77 : Prop :=
  ∀ (n : ℕ), Odd n → ∀ (G : SimpleGraph (Fin n)),
    ∀ [DecidableRel G.Adj], G.Connected →
      ∀ u v : Fin n, u ≠ v → ∀ t : ℝ, 0 < t → ¬ laplacianPST G u v t

theorem sourceConjecture77_iff : sourceConjecture77 ↔ oddLaplacianClaim := by
  rfl

theorem source_conjecture77_refuted : ¬ sourceConjecture77 :=
  odd_order_laplacian_pst_refuted

theorem source_explicit_counterexample :
    Odd 35 ∧ witnessGraph.Connected ∧ (0 : Fin 35) ≠ 1 ∧
      0 < Real.pi / 2 ∧ laplacianPST witnessGraph 0 1 (Real.pi / 2) := by
  refine ⟨by decide, witness_connected, by decide, by positivity, ?_⟩
  unfold laplacianPST
  rw [witness_transfer_entry, norm_one]

/-- The complex Laplacian is the entrywise cast of the integer Laplacian. -/
theorem complex_laplacian_cast {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] :
    G.lapMatrix ℂ = (G.lapMatrix ℤ).map (fun z : ℤ => (z : ℂ)) := by
  ext i j
  simp [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, SimpleGraph.adjMatrix,
    Matrix.diagonal, Matrix.map_apply]

#check witness_exact_transfer
#check witness_transfer_entry
#check odd_order_laplacian_pst_refuted
#check source_conjecture77_refuted
#check source_explicit_counterexample
#print axioms witness_transfer_entry
#print laplacianPST
#print sourceConjecture77
#check @NormedSpace.exp
#print NormedSpace.exp
#check @NormedSpace.exp_eq_tsum
#print SimpleGraph.lapMatrix
set_option pp.all true in
#check (NormedSpace.exp : Matrix (Fin 35) (Fin 35) ℂ → Matrix (Fin 35) (Fin 35) ℂ)
set_option pp.all true in
#synth Algebra ℂ (Matrix (Fin 35) (Fin 35) ℂ)
set_option pp.all true in
#synth Algebra ℚ (Matrix (Fin 35) (Fin 35) ℂ)
set_option pp.all true in
#synth Ring (Matrix (Fin 35) (Fin 35) ℂ)
#print axioms sourceConjecture77_iff
#print axioms source_conjecture77_refuted
#print axioms source_explicit_counterexample
#print axioms complex_laplacian_cast
end Pool012
```

