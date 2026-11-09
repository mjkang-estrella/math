/- Copyright 2026 Myeongjin Kang. Original code licensed MIT. -/
import Mathlib

open scoped BigOperators
open Module Polynomial

namespace KnMinusEdge

section TensorKernel
variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

/-- Contraction by a functional, in finite basis coordinates. -/
def contract (φ x : ι → K) : K := ∑ i, φ i * x i

/-- Projection onto the functional kernel, using φ(e)=1. -/
def project (φ e x : ι → K) : ι → K := fun i => x i - e i * contract φ x

omit [DecidableEq ι] in
theorem contract_project (φ e x : ι → K) (he : contract φ e = 1) :
    contract φ (project φ e x) = 0 := by
  simp only [contract, project, mul_sub, Finset.sum_sub_distrib]
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul]
  change contract φ x - contract φ e * contract φ x = 0
  rw [he, one_mul, sub_self]

/-- A matrix is a tensor in a chosen finite basis. Both contractions vanish
exactly when it is a sum of rank-one tensors with both factors in ker φ.
The forward direction uses explicit projected basis vectors. -/
theorem tensor_kernel_iff (φ e : ι → K) (he : contract φ e = 1) (H : ι → ι → K) :
    ((∀ j, ∑ i, φ i * H i j = 0) ∧ (∀ i, ∑ j, φ j * H i j = 0)) ↔
    ∃ (r : ℕ) (a b : Fin r → ι → K),
      (∀ k, contract φ (a k) = 0) ∧ (∀ k, contract φ (b k) = 0) ∧
      ∀ i j, H i j = ∑ k, a k i * b k j := by
  constructor
  · rintro ⟨hl, hr⟩
    let q : ι → ι → K := fun k => project φ e (Pi.single k 1)
    have hq (k i : ι) : q k i = (if i = k then 1 else 0) - e i * φ k := by
      simp [q, project, contract, Pi.single_apply, eq_comm]
    have hdecomp (i j : ι) : H i j = ∑ k, ∑ l, H k l * q k i * q l j := by
      have row (k : ι) : (∑ l, H k l * q l j) = H k j := by
        simp_rw [hq, mul_sub, Finset.sum_sub_distrib]
        simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
          ite_true]
        have hz : (∑ l, H k l * (e j * φ l)) = 0 := by
          calc
            _ = e j * ∑ l, φ l * H k l := by
              rw [Finset.mul_sum]; congr 1; ext; ring
            _ = 0 := by rw [hr k, mul_zero]
        rw [hz, sub_zero]
      calc
        H i j = ∑ k, q k i * H k j := by
          simp_rw [hq, sub_mul, Finset.sum_sub_distrib]
          simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
            ite_true]
          have hz : (∑ k, e i * φ k * H k j) = 0 := by
            simp_rw [mul_assoc, ← Finset.mul_sum]; rw [hl j, mul_zero]
          rw [hz, sub_zero]
        _ = ∑ k, ∑ l, H k l * q k i * q l j := by
          simp_rw [← row, Finset.mul_sum]
          congr 1; ext k; congr 1; ext l; ring
    let equiv := Fintype.equivFin (ι × ι)
    refine ⟨Fintype.card (ι × ι),
      (fun k i => H (equiv.symm k).1 (equiv.symm k).2 * q (equiv.symm k).1 i),
      (fun k => q (equiv.symm k).2), ?_, ?_, ?_⟩
    · intro k
      change (∑ i, φ i * (H _ _ * q _ i)) = 0
      simp_rw [show ∀ i, φ i * (H (equiv.symm k).1 (equiv.symm k).2 *
        q (equiv.symm k).1 i) = H (equiv.symm k).1 (equiv.symm k).2 *
        (φ i * q (equiv.symm k).1 i) by intro; ring]
      rw [← Finset.mul_sum]
      change H _ _ * contract φ (project φ e _) = 0
      rw [contract_project φ e _ he, mul_zero]
    · intro k; exact contract_project φ e _ he
    · intro i j
      change H i j = ∑ k, H (equiv.symm k).1 (equiv.symm k).2 *
        q (equiv.symm k).1 i * q (equiv.symm k).2 j
      calc
        H i j = ∑ kl : ι × ι, H kl.1 kl.2 * q kl.1 i * q kl.2 j := by
          simpa only [Fintype.sum_prod_type] using hdecomp i j
        _ = _ := Fintype.sum_equiv equiv _ _ (by intro kl; simp)
  · rintro ⟨r, a, b, ha, hb, hH⟩
    constructor
    · intro j
      simp_rw [hH, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_eq_zero
      intro k _
      simp_rw [← mul_assoc, ← Finset.sum_mul]
      change contract φ (a k) * b k j = 0
      rw [ha, zero_mul]
    · intro i
      simp_rw [hH, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_eq_zero
      intro k _
      simp_rw [show ∀ j, φ j * (a k i * b k j) = a k i * (φ j * b k j) by intro; ring]
      rw [← Finset.mul_sum]
      change a k i * contract φ (b k) = 0
      rw [hb, mul_zero]
end TensorKernel

section Dimension
variable {K V A B : Type*} [Field K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup A] [Module K A] [FiniteDimensional K A]
  [AddCommGroup B] [Module K B] [FiniteDimensional K B]

omit [FiniteDimensional K A] in
/-- Surjective evaluation loses precisely the dimension of its target. -/
theorem split_kernel_dimension (ρ : V →ₗ[K] A) (hρ : Function.Surjective ρ) :
    finrank K (LinearMap.ker ρ) + finrank K A = finrank K V := by
  have h := LinearMap.finrank_range_add_finrank_ker ρ
  rw [LinearMap.range_eq_top.mpr hρ, finrank_top] at h
  omega

omit [FiniteDimensional K A] [FiniteDimensional K B] in
/-- Mixed orthogonality needs no direct-sum or self-isotropy hypothesis. -/
theorem mixed_dimension_bound (D : LinearMap.BilinForm K V) (hD : D.Nondegenerate)
    (Ea : A →ₗ[K] V) (Eb : B →ₗ[K] V)
    (ha : Function.Injective Ea) (hb : Function.Injective Eb)
    (hmix : ∀ a b, D (Ea a) (Eb b) = 0) :
    finrank K A + finrank K B ≤ finrank K V := by
  have hle : LinearMap.range Eb ≤ D.orthogonal (LinearMap.range Ea) := by
    intro x hx
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    rintro y ⟨a, rfl⟩
    rcases hx with ⟨b, rfl⟩
    exact hmix a b
  have hd := D.finrank_orthogonal hD (LinearMap.range Ea)
  have hm := Submodule.finrank_mono hle
  have hra := LinearMap.finrank_range_of_inj ha
  have hrb := LinearMap.finrank_range_of_inj hb
  have hva := Submodule.finrank_le (LinearMap.range Ea)
  omega
end Dimension

end KnMinusEdge

namespace KnMinusEdge
section PolynomialDetector
variable {K : Type*} [Field K]

/-- Separate degree rectangle, with variable 0 = u and variable 1 = v. -/
def Rectangle (a b : ℕ) (P : MvPolynomial (Fin 2) K) : Prop :=
  P.degreeOf 0 ≤ a ∧ P.degreeOf 1 ≤ b

/-- The detector pairing has arbitrary node order and weights. The upstream
nondegeneracy premise will constrain these parameters; it is not proved here. -/
def orderPair {ι : Type*} [Fintype ι] (t w : ι → K) (S : ι → ι → K)
    (A B : MvPolynomial (Fin 2) K) : K :=
  ∑ p, ∑ q, S p q * (t p - t q) * w p * w q *
    MvPolynomial.eval (fun i => if i = 0 then t p else t q) A *
    MvPolynomial.eval (fun i => if i = 0 then t p else t q) B

/-- Right nondegeneracy on the FULL two rectangles, the exact part of U4 used. -/
def RectangularNondegenerate {ι : Type*} [Fintype ι] (d : ℕ)
    (t w : ι → K) (S : ι → ι → K) : Prop :=
  ∀ Q : MvPolynomial (Fin 2) K, Rectangle d (d+1) Q →
    (∀ B, Rectangle (d+1) d B → orderPair t w S B Q = 0) → Q = 0

/-- Multiplication by v-c increases only the v degree. -/
theorem rectangle_twist (d : ℕ) (c : K) (A : MvPolynomial (Fin 2) K)
    (hA : Rectangle d d A) :
    Rectangle d (d+1) ((MvPolynomial.X 1 - MvPolynomial.C c) * A) := by
  have h0 : (MvPolynomial.X 1 - MvPolynomial.C c : MvPolynomial (Fin 2) K).degreeOf 0 ≤ 0 := by
    apply (MvPolynomial.degreeOf_sub_le _ _ _).trans
    simp [MvPolynomial.degreeOf_X]
  have h1 : (MvPolynomial.X 1 - MvPolynomial.C c : MvPolynomial (Fin 2) K).degreeOf 1 ≤ 1 := by
    apply (MvPolynomial.degreeOf_sub_le _ _ _).trans
    simp
  constructor
  · have := MvPolynomial.degreeOf_mul_le 0 (MvPolynomial.X 1 - MvPolynomial.C c) A
    dsimp [Rectangle] at hA; omega
  · have := MvPolynomial.degreeOf_mul_le 1 (MvPolynomial.X 1 - MvPolynomial.C c) A
    dsimp [Rectangle] at hA; omega

theorem twist_ne_zero (c : K) :
    (MvPolynomial.X 1 - MvPolynomial.C c : MvPolynomial (Fin 2) K) ≠ 0 := by
  intro h
  have he := congrArg (MvPolynomial.eval (fun _ : Fin 2 => c + 1)) h
  simp at he

/-- The twisted detector is a deduction from rectangular nondegeneracy, never
from the weaker square detector. No invertibility at the twist node is assumed. -/
theorem twisted_detector {ι : Type*} [Fintype ι] (d : ℕ) (t w : ι → K)
    (S : ι → ι → K) (hM : RectangularNondegenerate d t w S)
    (c : K) (A : MvPolynomial (Fin 2) K) (hA : Rectangle d d A)
    (hzero : ∀ B, Rectangle (d+1) d B →
      orderPair t w S A ((MvPolynomial.X 1 - MvPolynomial.C c) * B) = 0) :
    A = 0 := by
  have htwist : (MvPolynomial.X 1 - MvPolynomial.C c) * A = 0 := by
    apply hM _ (rectangle_twist d c A hA)
    intro B hB
    have hp : orderPair t w S B ((MvPolynomial.X 1 - MvPolynomial.C c) * A) =
        orderPair t w S A ((MvPolynomial.X 1 - MvPolynomial.C c) * B) := by
      unfold orderPair
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro q _
      simp only [map_mul]
      ring
    rw [hp]; exact hzero B hB
  exact (mul_eq_zero.mp htwist).resolve_left (twist_ne_zero c)
end PolynomialDetector
end KnMinusEdge

namespace KnMinusEdge
section Coordinates
variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

/-- First-slot evaluation in finite tensor coordinates. -/
def slotEval (φ : ι → K) : (ι → ι → K) →ₗ[K] (ι → K) where
  toFun H j := ∑ i, φ i * H i j
  map_add' H G := by ext j; simp [mul_add, Finset.sum_add_distrib]
  map_smul' c H := by
    ext j; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]; congr 1; ext; ring

omit [DecidableEq ι] in
theorem slotEval_surjective (φ e : ι → K) (he : contract φ e = 1) :
    Function.Surjective (slotEval φ) := by
  intro y
  refine ⟨fun i j => e i * y j, ?_⟩
  ext j
  change (∑ i, φ i * (e i * y j)) = y j
  simp_rw [← mul_assoc, ← Finset.sum_mul]
  change contract φ e * y j = y j
  rw [he, one_mul]

omit [DecidableEq ι] in
/-- The two split spaces each have dimension d²-d, in any basis whose
scalar evaluation functional φ has an explicitly normalized witness e. -/
theorem slot_kernel_dimension (φ e : ι → K) (he : contract φ e = 1) :
    finrank K (LinearMap.ker (slotEval φ)) =
      Fintype.card ι * Fintype.card ι - Fintype.card ι := by
  have h := split_kernel_dimension (slotEval φ) (slotEval_surjective φ e he)
  simp only [Module.finrank_pi, Module.finrank_pi_fintype,
    Finset.sum_const, Finset.card_univ, smul_eq_mul] at h
  omega

/-- Actual weighted diagonal form on the ordered edge-pair coordinate space. -/
def diagonalForm (a : ι → K) : LinearMap.BilinForm K (ι → K) :=
  LinearMap.mk₂ K (fun x y => ∑ i, a i * x i * y i)
    (by intros; simp [add_mul, mul_add, Finset.sum_add_distrib])
    (by
      intros; simp only [Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum]; congr 1; ext; ring)
    (by intros; simp [mul_add, Finset.sum_add_distrib])
    (by
      intros; simp only [Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum]; congr 1; ext; ring)

omit [DecidableEq ι] in
@[simp] theorem diagonalForm_apply (a x y : ι → K) :
    diagonalForm a x y = ∑ i, a i * x i * y i := rfl

theorem diagonal_nondegenerate (a : ι → K) (ha : ∀ i, a i ≠ 0) :
    (diagonalForm a).Nondegenerate := by
  constructor
  · intro x hx
    ext i
    have hi := hx (Pi.single i 1)
    simp [diagonalForm_apply, Pi.single_apply] at hi
    exact hi.resolve_left (ha i)
  · intro y hy
    ext i
    have hi := hy (Pi.single i 1)
    simp [diagonalForm_apply, Pi.single_apply] at hi
    exact hi.resolve_left (ha i)

/-- Both injection hypotheses are visible here. This declaration does not
prove manuscript Lemma 3.5: the two evaluation injections remain a separate gap. -/
theorem mixed_coordinate_bound {A B : Type*}
    [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
    (a : ι → K) (ha : ∀ i, a i ≠ 0)
    (Ea : A →ₗ[K] (ι → K)) (Eb : B →ₗ[K] (ι → K))
    (hEa : Function.Injective Ea) (hEb : Function.Injective Eb)
    (hmix : ∀ x y, ∑ i, a i * Ea x i * Eb y i = 0) :
    finrank K A + finrank K B ≤ Fintype.card ι := by
  simpa only [Module.finrank_pi] using
    mixed_dimension_bound (diagonalForm a) (diagonal_nondegenerate a ha)
      Ea Eb hEa hEb hmix
end Coordinates

section Localization
variable {K : Type*} [Field K]

/-- Products with degree budgets r,t span every polynomial of degree ≤r+t.
The statement is expressed by an arbitrary linear functional, not by an
opaque interpolation or injectivity assumption. -/
theorem linear_zero_of_products (r t : ℕ) (L : K[X] →ₗ[K] K)
    (hprod : ∀ U V : K[X], U.natDegree ≤ r → V.natDegree ≤ t → L (U*V) = 0)
    (P : K[X]) (hP : P.natDegree ≤ r+t) : L P = 0 := by
  have hpowers (k : ℕ) (hk : k ≤ r+t) : L (X^k) = 0 := by
    let k₁ := min k r
    let k₂ := k-k₁
    have h₁ : k₁ ≤ r := Nat.min_le_right _ _
    have h₂ : k₂ ≤ t := by dsimp [k₂, k₁]; omega
    have hsum : k₁+k₂ = k := by dsimp [k₂, k₁]; omega
    have h := hprod (X^k₁) (X^k₂) (by simpa using h₁) (by simpa using h₂)
    simpa only [← pow_add, hsum] using h
  rw [P.as_sum_support_C_mul_X_pow, map_sum]
  apply Finset.sum_eq_zero
  intro k hk
  rw [← Polynomial.smul_eq_C_mul, map_smul]
  have hkdeg : k ≤ r+t := (Polynomial.le_natDegree_of_mem_supp k hk).trans hP
  simp [hpowers k hkdeg]

/-- Lagrange isolation with the extra (t-t_a) factor. In the application
weights_i=w_i² and i₀ is outside BOTH missing endpoints. No star order is used at a. -/
theorem localize_away {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r t : ℕ) (nodes weights σ : ι → K) (hnodes : Function.Injective nodes)
    (hcard : Fintype.card ι ≤ r+t+2) (a i₀ : ι) (hi₀ : i₀ ≠ a)
    (hweights : weights i₀ ≠ 0)
    (htests : ∀ U V : K[X], U.natDegree ≤ r → V.natDegree ≤ t →
      (∑ i, weights i * U.eval (nodes i) * (nodes i-nodes a) * V.eval (nodes i) * σ i) = 0) :
    σ i₀ = 0 := by
  classical
  let ell : K[X] := Lagrange.basis Finset.univ nodes i₀
  have hinj : Set.InjOn nodes (↑(Finset.univ : Finset ι) : Set ι) := hnodes.injOn
  have hdegree : ell.natDegree = Fintype.card ι - 1 := by
    simpa [ell] using Lagrange.natDegree_basis hinj (Finset.mem_univ i₀)
  have hell : ell ≠ 0 := Lagrange.basis_ne_zero hinj (Finset.mem_univ i₀)
  have hroot : ell.eval (nodes a) = 0 :=
    Lagrange.eval_basis_of_ne hi₀ (Finset.mem_univ a)
  obtain ⟨R, hR⟩ := Polynomial.dvd_iff_isRoot.mpr hroot
  have hRne : R ≠ 0 := by intro hz; simp [hz] at hR; exact hell hR
  have hRdegree : R.natDegree ≤ r+t := by
    have hmul := Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero (nodes a)) hRne
    rw [← hR, Polynomial.natDegree_X_sub_C, hdegree] at hmul
    have hpos : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i₀⟩
    omega
  let L : K[X] →ₗ[K] K :=
    { toFun := fun P => ∑ i, weights i * (nodes i-nodes a) * P.eval (nodes i) * σ i
      map_add' := by intros; simp [mul_add, add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intros; simp only [Polynomial.eval_smul, smul_eq_mul, RingHom.id_apply]
        rw [Finset.mul_sum]; congr 1; ext; ring }
  have hLR : L R = 0 := by
    apply linear_zero_of_products r t L _ R hRdegree
    intro U V hU hV
    convert htests U V hU hV using 1
    dsimp [L]; simp only [Polynomial.eval_mul]
    congr 1; ext; ring
  have hz : (∑ i, weights i * ell.eval (nodes i) * σ i) = 0 := by
    convert hLR using 1
    dsimp [L]; rw [hR]
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    congr 1; ext; ring
  have hisolate : (∑ i, weights i * ell.eval (nodes i) * σ i) = weights i₀ * σ i₀ := by
    rw [Finset.sum_eq_single i₀]
    · simp [ell, Lagrange.eval_basis_self hinj (Finset.mem_univ i₀)]
    · intro i _ hi
      simp [ell, Lagrange.eval_basis_of_ne hi.symm (Finset.mem_univ i)]
    · simp
  rw [hisolate] at hz
  exact (mul_eq_zero.mp hz).resolve_left hweights

/-- The actual root budget after excluding both deficient stars, with
coefficients in the two remaining polynomial variables. -/
theorem diagonal_root_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ℕ) (hs : 2 ≤ s) (nodes : ι → K) (hnodes : Function.Injective nodes)
    (hcard : Fintype.card ι = 2*s+1) (a b : ι) (hab : a ≠ b)
    (P : Polynomial (MvPolynomial (Fin 2) K)) (hdegree : P.natDegree ≤ 2*s-4)
    (hvanish : ∀ i, i ≠ a → i ≠ b → P.eval (MvPolynomial.C (nodes i)) = 0) :
    P = 0 := by
  let I := (Finset.univ.erase a).erase b
  have hIcard : I.card = 2*s-1 := by
    have hb : b ∈ (Finset.univ : Finset ι).erase a := by simp [Ne.symm hab]
    dsimp [I]
    rw [Finset.card_erase_of_mem hb, Finset.card_erase_of_mem (Finset.mem_univ a),
      Finset.card_univ, hcard]
    omega
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero P
    (f := fun i : I => MvPolynomial.C (nodes i))
  · intro i j hij
    apply Subtype.ext
    exact hnodes ((MvPolynomial.C_injective (Fin 2) K) hij)
  · intro i
    have hi := i.prop
    simp only [I, Finset.mem_erase, Finset.mem_univ, and_true] at hi
    exact hvanish i hi.2 hi.1
  · rw [Fintype.card_coe, hIcard]; omega
end Localization
end KnMinusEdge

namespace KnMinusEdge
section DescentAlgebra
variable {K : Type*} [Field K]

/-- The four-variable collision factor, in order x,u,y,v. -/
noncomputable def collision : MvPolynomial (Fin 4) K :=
  (MvPolynomial.X 0 - MvPolynomial.X 2) *
  (MvPolynomial.X 0 - MvPolynomial.X 3) *
  (MvPolynomial.X 1 - MvPolynomial.X 2) *
  (MvPolynomial.X 1 - MvPolynomial.X 3)

/-- Substitute the first pair (a,b), leaving the other pair polynomial. -/
noncomputable def missingSpecialization (a b : K) :
    MvPolynomial (Fin 4) K →+* MvPolynomial (Fin 2) K :=
  MvPolynomial.eval₂Hom MvPolynomial.C ![MvPolynomial.C a, MvPolynomial.C b,
    MvPolynomial.X 0, MvPolynomial.X 1]

theorem coordinate_sub_constant_ne_zero {σ : Type*} (i : σ) (c : K) :
    (MvPolynomial.X i - MvPolynomial.C c : MvPolynomial σ K) ≠ 0 := by
  intro hz
  have he := congrArg (MvPolynomial.eval (fun _ : σ => c+1)) hz
  simp at he

/-- Nonzero as a POLYNOMIAL, with no pointwise nonvanishing assertion. -/
theorem collision_specialization_ne_zero (a b : K) :
    missingSpecialization a b (collision : MvPolynomial (Fin 4) K) ≠ 0 := by
  have h (i : Fin 2) (c : K) :
      (MvPolynomial.C c - MvPolynomial.X i : MvPolynomial (Fin 2) K) ≠ 0 := by
    intro hz
    exact coordinate_sub_constant_ne_zero i c (sub_eq_zero.mpr (sub_eq_zero.mp hz).symm)
  simp only [missingSpecialization, collision, map_mul, map_sub,
    MvPolynomial.eval₂Hom_X', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (h 0 a) (h 1 a)) (h 0 b)) (h 1 b)

/-- The missing-pair vanishing condition survives division by C. -/
theorem quotient_preserves_missing (a b : K) (P R : MvPolynomial (Fin 4) K)
    (hfactor : P = collision * R) (hmissing : missingSpecialization a b P = 0) :
    missingSpecialization a b R = 0 := by
  rw [hfactor, map_mul] at hmissing
  exact (mul_eq_zero.mp hmissing).resolve_left (collision_specialization_ne_zero a b)

/-- Cancelling a fixed invariant factor transfers a symmetry to the quotient. -/
theorem quotient_preserves_symmetry {R : Type*} [CommRing R] [IsDomain R]
    (τ : R →+* R) (C P Q : R) (hC : C ≠ 0)
    (hτC : τ C = C) (hτP : τ P = P) (hfactor : P = C*Q) : τ Q = Q := by
  have h := congrArg τ hfactor
  rw [hτP, map_mul, hτC, hfactor] at h
  exact mul_left_cancel₀ hC h.symm

/-- Cancellation at each independent coordinate preserves the evaluation kernel. -/
theorem quotient_preserves_evaluations {ι : Type*} (points : ι → Fin 4 → K)
    (P R : MvPolynomial (Fin 4) K) (hfactor : P = collision * R)
    (hC : ∀ i, MvPolynomial.eval (points i) collision ≠ 0)
    (hP : ∀ i, MvPolynomial.eval (points i) P = 0) :
    ∀ i, MvPolynomial.eval (points i) R = 0 := by
  intro i
  have hi := hP i
  rw [hfactor, map_mul] at hi
  exact (mul_eq_zero.mp hi).resolve_left (hC i)

/-- A collision specialization is divisible by its linear collision factor.
Here the coefficient ring may itself be a polynomial ring in the other variables. -/
theorem collision_divisibility {R : Type*} [CommRing R] (y : R) (P : R[X])
    (hdiag : P.eval y = 0) : X - C y ∣ P :=
  Polynomial.dvd_iff_isRoot.mpr hdiag

/-- Exact degree loss in one chosen variable once a nonzero factor is known.
The case degree P < 2 cannot contain a nonzero such factorization. -/
theorem quotient_degree_loss {σ : Type*} (i : σ) (C P Q : MvPolynomial σ K)
    (hfactor : P = C*Q) (hC : C ≠ 0) (hQ : Q ≠ 0) (hdegree : C.degreeOf i = 2) :
    Q.degreeOf i + 2 = P.degreeOf i := by
  rw [hfactor, MvPolynomial.degreeOf_mul_eq hC hQ, hdegree]
  omega

/-- Well-founded degree descent. Its explicit obligations are factorization
AND preservation of a concrete predicate, not an assumed injection. This
abstract lemma alone does not supply the four-factor theorem for S_a. -/
theorem degree_descent {σ : Type*} (i : σ) (C : MvPolynomial σ K)
    (hC : C ≠ 0) (hdegree : C.degreeOf i = 2)
    (W : MvPolynomial σ K → Prop)
    (hdivide : ∀ P, W P → P ≠ 0 → ∃ Q, P = C*Q ∧ W Q) :
    ∀ P, W P → P = 0 := by
  intro P
  induction hn : P.degreeOf i using Nat.strong_induction_on generalizing P with
  | h n ih =>
    intro hWP
    by_contra hP
    obtain ⟨Q, hfactor, hWQ⟩ := hdivide P hWP hP
    have hQ : Q ≠ 0 := by intro hz; simp [hz] at hfactor; exact hP hfactor
    have hsmall := quotient_degree_loss i C P Q hfactor hC hQ hdegree
    have hz := ih (Q.degreeOf i) (by omega) Q rfl hWQ
    exact hQ hz
end DescentAlgebra
end KnMinusEdge

namespace KnMinusEdge
section DegreeBudget
variable {K : Type*} [Field K]

/-- A genuine separate-degree predicate, not a list of asserted integers. -/
def Budget (bounds : Fin 4 → ℕ) (P : MvPolynomial (Fin 4) K) : Prop :=
  ∀ i, P.degreeOf i ≤ bounds i

theorem budget_mul {f g : Fin 4 → ℕ} {P Q : MvPolynomial (Fin 4) K}
    (hP : Budget f P) (hQ : Budget g Q) : Budget (fun i => f i + g i) (P*Q) := by
  intro i
  exact (MvPolynomial.degreeOf_mul_le i P Q).trans (Nat.add_le_add (hP i) (hQ i))

theorem budget_difference (i j : Fin 4) :
    Budget (fun k => if k=i ∨ k=j then 1 else 0)
      (MvPolynomial.X i - MvPolynomial.X j : MvPolynomial (Fin 4) K) := by
  intro k
  apply (MvPolynomial.degreeOf_sub_le _ _ _).trans
  simp only [MvPolynomial.degreeOf_X]
  split_ifs <;> simp_all

theorem budget_twist (i : Fin 4) (c : K) :
    Budget (fun k => if k=i then 1 else 0)
      (MvPolynomial.X i - MvPolynomial.C c : MvPolynomial (Fin 4) K) := by
  intro k
  apply (MvPolynomial.degreeOf_sub_le _ _ _).trans
  simp [MvPolynomial.degreeOf_X]

/-- The actual test from Lemma 3.5(a), x,u,y,v indexed 0,1,2,3.
U,V,B are polynomials constrained to their indicated variable budgets. -/
noncomputable def localTest (c : K) (P U V B : MvPolynomial (Fin 4) K) :
    MvPolynomial (Fin 4) K :=
  P * (MvPolynomial.X 1 - MvPolynomial.X 3) *
    (MvPolynomial.X 1 - MvPolynomial.X 2) *
    (MvPolynomial.X 3 - MvPolynomial.X 0) * U *
    (MvPolynomial.X 2 - MvPolynomial.C c) * V *
    (MvPolynomial.X 3 - MvPolynomial.C c) * B

/-- With d=s-2, the displayed product has degree at most 2s-1 in
EACH variable. Both extra missing-edge factors are included. -/
theorem local_test_degree (d : ℕ) (c : K) (P U V B : MvPolynomial (Fin 4) K)
    (hP : Budget (fun _ => d) P) (hU : Budget ![d+2,0,0,0] U)
    (hV : Budget ![0,0,d+1,0] V) (hB : Budget ![0,d+1,0,d] B) :
    Budget (fun _ => 2*d+3) (localTest c P U V B) := by
  have h := budget_mul
    (budget_mul (budget_mul (budget_mul (budget_mul (budget_mul
      (budget_mul (budget_mul hP (budget_difference 1 3)) (budget_difference 1 2))
        (budget_difference 3 0)) hU) (budget_twist 2 c)) hV) (budget_twist 3 c)) hB
  intro i
  have hi := h i
  fin_cases i <;> simpa [localTest, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.two_mul] using hi

/-- Substitution in the second edge slot, leaving the first pair polynomial. -/
noncomputable def secondSpecialization (a b : K) :
    MvPolynomial (Fin 4) K →+* MvPolynomial (Fin 2) K :=
  MvPolynomial.eval₂Hom MvPolynomial.C ![MvPolynomial.X 0, MvPolynomial.X 1,
    MvPolynomial.C a, MvPolynomial.C b]

/-- The two twist factors enforce BOTH second-slot missing-pair identities. -/
theorem local_test_second_missing (a b : K) (P U V B : MvPolynomial (Fin 4) K) :
    secondSpecialization a b (localTest a P U V B) = 0 ∧
    secondSpecialization b a (localTest a P U V B) = 0 := by
  simp [secondSpecialization, localTest]

/-- First-slot vanishing comes from the split space, in either endpoint order. -/
theorem local_test_first_missing (a b : K) (P U V B : MvPolynomial (Fin 4) K)
    (hPab : missingSpecialization a b P = 0)
    (hPba : missingSpecialization b a P = 0) :
    missingSpecialization a b (localTest a P U V B) = 0 ∧
    missingSpecialization b a (localTest a P U V B) = 0 := by
  simp only [localTest, map_mul, hPab, hPba, zero_mul, and_self]
end DegreeBudget
end KnMinusEdge

namespace KnMinusEdge
section MissingFunctional
variable {K : Type*} [Field K]

/-- The actual antisymmetric missing-pair evaluation functional. -/
noncomputable def missingFunctional (a b : K) : MvPolynomial (Fin 2) K →ₗ[K] K :=
  { toFun := fun P => MvPolynomial.eval ![a,b] P - MvPolynomial.eval ![b,a] P
    map_add' := by intros; simp; ring
    map_smul' := by intros; simp [mul_sub] }

theorem missingFunctional_normalized (a b : K) (hab : a ≠ b) :
    missingFunctional a b (MvPolynomial.C (a-b)⁻¹ * MvPolynomial.X 0) = 1 := by
  have h : a-b ≠ 0 := sub_ne_zero.mpr hab
  simp [missingFunctional, ← mul_sub, h]

/-- A skew matrix pairs any vector with itself to zero. This explains a
universal source of zero tests outside the admissible tensor kernel. -/
theorem skew_rank_one_zero {ι : Type*} [Fintype ι] [CharZero K]
    (J : ι → ι → K) (hJ : ∀ i j, J i j = -J j i) (x : ι → K) :
    (∑ i, ∑ j, J i j * x i * x j) = 0 := by
  let z := ∑ i, ∑ j, J i j * x i * x j
  have hz : z = -z := by
    calc
      z = ∑ i, ∑ j, J j i * x j * x i := Finset.sum_comm
      _ = ∑ i, ∑ j, -(J i j * x i * x j) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        calc
          J j i * x j * x i = (-J i j) * x j * x i := by rw [hJ j i]
          _ = -(J i j * x i * x j) := by ring
      _ = -z := by simp [z, Finset.sum_neg_distrib]
  have htwo : (2 : K) * z = 0 := by linear_combination hz
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
end MissingFunctional
end KnMinusEdge

namespace KnMinusEdge
section CollisionDegrees
variable {K : Type*} [Field K]

theorem difference_ne_zero {σ : Type*} [DecidableEq σ] (i j : σ) (hij : i ≠ j) :
    (MvPolynomial.X i - MvPolynomial.X j : MvPolynomial σ K) ≠ 0 := by
  intro hz
  have he := congrArg (MvPolynomial.eval (fun k : σ => if k=i then (1:K) else 0)) hz
  simp [Ne.symm hij] at he

theorem difference_degree {σ : Type*} [DecidableEq σ] (i j k : σ) (hij : i ≠ j) :
    (MvPolynomial.X i - MvPolynomial.X j : MvPolynomial σ K).degreeOf k =
      if k=i ∨ k=j then 1 else 0 := by
  by_cases hi : k=i
  · subst k
    rw [sub_eq_add_neg, MvPolynomial.degreeOf_add_eq_of_degreeOf_lt]
    · simp
    · simp [MvPolynomial.degreeOf_X, hij]
  · by_cases hj : k=j
    · subst k
      have heq : (MvPolynomial.X i - MvPolynomial.X j : MvPolynomial σ K) =
          -(MvPolynomial.X j - MvPolynomial.X i) := by ring
      rw [heq, MvPolynomial.degreeOf_neg, sub_eq_add_neg,
        MvPolynomial.degreeOf_add_eq_of_degreeOf_lt]
      · simp
      · simp [MvPolynomial.degreeOf_X, Ne.symm hij]
    · have hz := MvPolynomial.degreeOf_sub_le k
        (MvPolynomial.X i : MvPolynomial σ K) (MvPolynomial.X j)
      simp only [MvPolynomial.degreeOf_X, hi, hj, ite_false, max_self] at hz
      simp [hi, hj, Nat.eq_zero_of_le_zero hz]

theorem collision_ne_zero : (collision : MvPolynomial (Fin 4) K) ≠ 0 := by
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero
    (difference_ne_zero 0 2 (by decide)) (difference_ne_zero 0 3 (by decide)))
    (difference_ne_zero 1 2 (by decide))) (difference_ne_zero 1 3 (by decide))

theorem collision_degree (i : Fin 4) :
    (collision : MvPolynomial (Fin 4) K).degreeOf i = 2 := by
  have h02 := difference_ne_zero (K:=K) (0:Fin 4) 2 (by decide)
  have h03 := difference_ne_zero (K:=K) (0:Fin 4) 3 (by decide)
  have h12 := difference_ne_zero (K:=K) (1:Fin 4) 2 (by decide)
  have h13 := difference_ne_zero (K:=K) (1:Fin 4) 3 (by decide)
  unfold collision
  rw [MvPolynomial.degreeOf_mul_eq (mul_ne_zero (mul_ne_zero h02 h03) h12) h13,
    MvPolynomial.degreeOf_mul_eq (mul_ne_zero h02 h03) h12,
    MvPolynomial.degreeOf_mul_eq h02 h03]
  rw [difference_degree 0 2 i (by decide), difference_degree 0 3 i (by decide),
    difference_degree 1 2 i (by decide), difference_degree 1 3 i (by decide)]
  fin_cases i <;> decide

/-- Handles d=0 and d=1 (s=2,3) without any negative degree spaces. -/
theorem small_degree_collision_zero (d : ℕ) (hd : d < 2)
    (P : MvPolynomial (Fin 4) K) (hP : Budget (fun _ => d) P)
    (hdiv : collision ∣ P) : P = 0 := by
  obtain ⟨Q, hQ⟩ := hdiv
  by_contra hp
  have hq : Q ≠ 0 := by intro hz; simp [hz] at hQ; exact hp hQ
  have hdegree := quotient_degree_loss 0 collision P Q hQ collision_ne_zero hq (collision_degree 0)
  have hdP : P.degreeOf 0 ≤ d := hP 0
  omega
end CollisionDegrees
end KnMinusEdge

namespace KnMinusEdge
section ActualCollisionSupport
variable {K : Type*} [Field K]

theorem collision_swap_first :
    MvPolynomial.rename (Equiv.swap (0:Fin 4) 1) (collision : MvPolynomial (Fin 4) K) =
      collision := by
  simp [collision, Equiv.swap_apply_def]; ring

theorem collision_swap_second :
    MvPolynomial.rename (Equiv.swap (2:Fin 4) 3) (collision : MvPolynomial (Fin 4) K) =
      collision := by
  simp [collision, Equiv.swap_apply_def]; ring

theorem collision_nonzero_on_independent (point : Fin 4 → K)
    (hpoint : Function.Injective point) :
    MvPolynomial.eval point (collision : MvPolynomial (Fin 4) K) ≠ 0 := by
  simp only [collision, map_mul, map_sub, MvPolynomial.eval_X]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero
    (sub_ne_zero.mpr (hpoint.ne (by decide)))
    (sub_ne_zero.mpr (hpoint.ne (by decide))))
    (sub_ne_zero.mpr (hpoint.ne (by decide))))
    (sub_ne_zero.mpr (hpoint.ne (by decide)))
end ActualCollisionSupport

/-- Exact interpolation weights appearing in U3/U4; no property is postulated
by this definition. -/
noncomputable def baryWeights {ι : Type*} [Fintype ι] (t : ι → ℝ) : ι → ℝ :=
  fun i => (Polynomial.eval (t i) (Polynomial.derivative
    (∏ j, (Polynomial.X - Polynomial.C (t j)))))⁻¹

/-- Any prescribed order is represented by an arbitrary permutation of labels. -/
noncomputable def orderSigns {n : ℕ} (order : Fin n ≃ Fin n) (i j : Fin n) : ℝ :=
  if order i < order j then 1/2 else if order j < order i then -1/2 else 0

/-- The ONLY unformalized upstream mathematical premise used by the detector
wrapper: distinct real nodes and full rectangular right nondegeneracy of
exactly the U4 pairing at 2s nodes, s=d+2. This is a proposition, not a new
constant asserting it. -/
def UpstreamDetectorPremise (d : ℕ) (t : Fin (2*(d+2)) → ℝ)
    (order : Fin (2*(d+2)) ≃ Fin (2*(d+2))) : Prop :=
  Function.Injective t ∧ RectangularNondegenerate d t (baryWeights t) (orderSigns order)

/-- The twist is one of the 2s detector nodes, as in Lemma 3.4. -/
theorem twisted_detector_from_U4 (d : ℕ) (t : Fin (2*(d+2)) → ℝ)
    (order : Fin (2*(d+2)) ≃ Fin (2*(d+2)))
    (hU4 : UpstreamDetectorPremise d t order) (c : Fin (2*(d+2)))
    (A : MvPolynomial (Fin 2) ℝ) (hA : Rectangle d d A)
    (hzero : ∀ B, Rectangle (d+1) d B →
      orderPair t (baryWeights t) (orderSigns order) A
        ((MvPolynomial.X 1 - MvPolynomial.C (t c)) * B) = 0) : A = 0 :=
  twisted_detector d t (baryWeights t) (orderSigns order) hU4.2 (t c) A hA hzero
end KnMinusEdge

namespace KnMinusEdge
/-- Assembly of the genuinely changed localization/detector step. The summed
test identity and its identification with each complete-star order pairing
are EXPLICIT obligations; neither is called an upstream theorem here.
No order-pairing information is required at either missing endpoint. -/
theorem localized_twisted_vanishing {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (s : ℕ) (hs : 2 ≤ s) (nodes weights : ι → K)
    (hnodes : Function.Injective nodes) (hcard : Fintype.card ι = 2*s+1)
    (a b : ι) (hweights : ∀ i, weights i ≠ 0)
    (localNodes localWeights : ι → Fin (2*s) → K)
    (localSigns : ι → Fin (2*s) → Fin (2*s) → K)
    (A : ι → MvPolynomial (Fin 2) K)
    (hA : ∀ i, Rectangle (s-2) (s-2) (A i))
    (hM : ∀ i, i ≠ a → i ≠ b →
      RectangularNondegenerate (s-2) (localNodes i) (localWeights i) (localSigns i))
    (sigma : MvPolynomial (Fin 2) K → ι → K)
    (hidentify : ∀ B, Rectangle (s-2+1) (s-2) B → ∀ i, i ≠ a → i ≠ b →
      sigma B i = orderPair (localNodes i) (localWeights i) (localSigns i)
        (A i) ((MvPolynomial.X 1 - MvPolynomial.C (nodes a))*B))
    (htests : ∀ B, Rectangle (s-2+1) (s-2) B → ∀ U V : Polynomial K,
      U.natDegree ≤ s → V.natDegree ≤ s-1 →
      (∑ i, weights i * U.eval (nodes i) * (nodes i - nodes a) *
        V.eval (nodes i) * sigma B i) = 0) :
    ∀ i, i ≠ a → i ≠ b → A i = 0 := by
  intro i hia hib
  apply twisted_detector (s-2) (localNodes i) (localWeights i) (localSigns i)
    (hM i hia hib) (nodes a) (A i) (hA i)
  intro B hB
  rw [← hidentify B hB i hia hib]
  exact localize_away s (s-1) nodes weights (sigma B) hnodes (by omega)
    a i hia (hweights i) (htests B hB)
end KnMinusEdge

namespace KnMinusEdge
section MixedTest
variable {K : Type*} [Field K]

/-- Vandermonde factor in the exact x,u,y,v orientation of Lemma 3.3. -/
noncomputable def delta : MvPolynomial (Fin 4) K :=
  (MvPolynomial.X 0 - MvPolynomial.X 1) *
    (MvPolynomial.X 2 - MvPolynomial.X 3) * collision

theorem delta_budget : Budget (fun _ => 3) (delta : MvPolynomial (Fin 4) K) := by
  have hC : Budget (fun _ => 2) (collision : MvPolynomial (Fin 4) K) :=
    fun i => le_of_eq (collision_degree i)
  have h := budget_mul (budget_mul (budget_difference (K:=K) 0 1)
    (budget_difference 2 3)) hC
  intro i
  have hi := h i
  fin_cases i <;> simpa [delta] using hi

theorem mixed_test_degree (d : ℕ) (P Q : MvPolynomial (Fin 4) K)
    (hP : Budget (fun _ => d) P) (hQ : Budget (fun _ => d) Q) :
    Budget (fun _ => 2*d+3) (P*Q*delta) := by
  have h := budget_mul (budget_mul hP hQ) delta_budget
  intro i
  simpa only [Nat.two_mul] using h i

/-- Mixed admissibility uses the FIRST split condition on P and the SECOND
on Q. There is no self-isotropy or intersection-space hypothesis. -/
theorem mixed_test_missing (a b : K) (P Q : MvPolynomial (Fin 4) K)
    (hPab : missingSpecialization a b P = 0)
    (hPba : missingSpecialization b a P = 0)
    (hQab : secondSpecialization a b Q = 0)
    (hQba : secondSpecialization b a Q = 0) :
    missingSpecialization a b (P*Q*delta) = 0 ∧
    missingSpecialization b a (P*Q*delta) = 0 ∧
    secondSpecialization a b (P*Q*delta) = 0 ∧
    secondSpecialization b a (P*Q*delta) = 0 := by
  simp only [map_mul, hPab, hPba, hQab, hQba, zero_mul, mul_zero, and_self]

theorem delta_reverse_first :
    MvPolynomial.rename (Equiv.swap (0:Fin 4) 1) (delta : MvPolynomial (Fin 4) K) =
      -delta := by
  simp only [delta, map_mul, map_sub, MvPolynomial.rename_X, collision_swap_first]
  simp [Equiv.swap_apply_def]; ring

theorem delta_reverse_second :
    MvPolynomial.rename (Equiv.swap (2:Fin 4) 3) (delta : MvPolynomial (Fin 4) K) =
      -delta := by
  simp only [delta, map_mul, map_sub, MvPolynomial.rename_X, collision_swap_second]
  simp [Equiv.swap_apply_def]; ring

theorem delta_nonzero_on_independent (point : Fin 4 → K)
    (hpoint : Function.Injective point) :
    MvPolynomial.eval point (delta : MvPolynomial (Fin 4) K) ≠ 0 := by
  simp only [delta, map_mul, map_sub, MvPolynomial.eval_X]
  exact mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr (hpoint.ne (by decide)))
    (sub_ne_zero.mpr (hpoint.ne (by decide)))) (collision_nonzero_on_independent point hpoint)
end MixedTest
end KnMinusEdge
