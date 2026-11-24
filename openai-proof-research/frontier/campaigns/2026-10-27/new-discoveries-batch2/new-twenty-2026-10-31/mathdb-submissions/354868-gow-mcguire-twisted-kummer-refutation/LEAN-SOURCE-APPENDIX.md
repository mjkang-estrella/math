# Complete Lean source appendix

Modules are in import order. Code blocks are byte-identical to `src/`.

### `GowStatement.lean`

```lean
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.SplittingField.IsSplittingField
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.LinearIndependent.Defs

noncomputable section
namespace Gow
open Polynomial

/-- Source §1: the only nonzero exponents are powers of q. -/
def IsQPoly {A : Type*} [Semiring A] (q : ℕ) (L : A[X]) : Prop :=
  ∀ k ∈ L.support, ∃ i : ℕ, k = q ^ i

/-- Source §2: the only nonzero exponents are powers q^(s*i). -/
def IsQsPoly {A : Type*} [Semiring A] (q s : ℕ) (L : A[X]) : Prop :=
  ∀ k ∈ L.support, ∃ i : ℕ, k = q ^ (s * i)

abbrev H (n r : ℕ) := MvPolynomial.homogeneousSubmodule (Fin n) (ZMod 3) r

/-- Source §4: evaluation of homogeneous forms on a root-space basis. -/
def eps {E : Type*} [CommRing E] [Algebra (ZMod 3) E]
    {n : ℕ} (v : Fin n → E) (r : ℕ) : H n r →ₗ[ZMod 3] E :=
  (MvPolynomial.aeval v).toLinearMap.comp (H n r).subtype

/-- The printed universal conjecture specialized only to q=p=3.
The field, polynomial, splitting field, root-space basis, and r stay universal. -/
def Conjecture : Prop :=
  ∀ (F E : Type) [Field F] [Field E] [CharP F 3]
    [Algebra (ZMod 3) F] [Algebra F E] [Algebra (ZMod 3) E]
    [IsScalarTower (ZMod 3) F E]
    (n r : ℕ) (L : F[X]) (v : Fin n → E),
    IsQPoly 3 L → L.natDegree = 3 ^ n →
    (∀ s, 1 < s → ¬ IsQsPoly 3 s L) →
    Irreducible L.divX → IsSplittingField F E L →
    LinearIndependent (ZMod 3) v →
    (∀ x : E, aeval x L = 0 ↔ x ∈ Submodule.span (ZMod 3) (Set.range v)) →
    1 ≤ r → r ≤ 3 - 1 → Function.Injective (eps v r)

#print Conjecture
#print axioms eps
end Gow
```

### `GowIdentities.lean`

```lean
import GowStatement
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

set_option maxRecDepth 2048

noncomputable section
namespace Gow
open Polynomial

/-- The counterexample polynomial, with its parameter left symbolic. -/
def poly {A : Type*} [CommRing A] (t : A) : A[X] :=
  X^81 + C (t+t^2)*X^27 - C (t+t^2)*X^9 + C (t+t^2)*X^3
    - C (t*(t^2+t+1))*X

section PolynomialFacts
variable {A : Type*} [CommRing A] [Nontrivial A] (t : A)

omit [Nontrivial A] in
theorem poly_monic : (poly t).Monic := by unfold poly; monicity <;> norm_num
theorem poly_natDegree : (poly t).natDegree = 81 := by unfold poly; compute_degree <;> norm_num
omit [Nontrivial A] in
theorem poly_coeff_three : (poly t).coeff 3 = t+t^2 := by simp only [poly, coeff_add, coeff_sub, coeff_C_mul, coeff_X_pow, coeff_X]; norm_num
omit [Nontrivial A] in
theorem poly_coeff_one : (poly t).coeff 1 = -(t*(t^2+t+1)) := by simp only [poly, coeff_add, coeff_sub, coeff_C_mul, coeff_X_pow, coeff_X]; norm_num

omit [Nontrivial A] in
theorem poly_isQPoly : IsQPoly 3 (poly t) := by
  classical
  intro k hk
  have hc : (poly t).coeff k ≠ 0 := mem_support_iff.mp hk
  have he : k = 81 ∨ k = 27 ∨ k = 9 ∨ k = 3 ∨ k = 1 := by
    by_contra hn
    push Not at hn
    apply hc
    simp only [poly, coeff_add, coeff_sub, coeff_C_mul, coeff_X_pow, coeff_X]
    simp_all only [ne_eq, ite_false, mul_zero, add_zero,
      sub_zero, eq_comm]
  rcases he with rfl | rfl | rfl | rfl | rfl
  · exact ⟨4, rfl⟩
  · exact ⟨3, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨0, rfl⟩
end PolynomialFacts

section CharacteristicThree
variable {A : Type*} [CommRing A] [CharP A 3]

lemma cube_add (x y : A) : (x+y)^3 = x^3+y^3 := by
  exact add_pow_char x y 3

lemma pow9_add (x y : A) : (x+y)^9 = x^9+y^9 := by
  calc (x+y)^9 = ((x+y)^3)^3 := by ring
       _ = (x^3+y^3)^3 := by rw [cube_add]
       _ = x^9+y^9 := by rw [cube_add]; ring

lemma pow27_add (x y : A) : (x+y)^27 = x^27+y^27 := by
  calc (x+y)^27 = ((x+y)^9)^3 := by ring
       _ = (x^9+y^9)^3 := by rw [pow9_add]
       _ = x^27+y^27 := by rw [cube_add]; ring

lemma pow81_add (x y : A) : (x+y)^81 = x^81+y^81 := by
  calc (x+y)^81 = ((x+y)^27)^3 := by ring
       _ = (x^27+y^27)^3 := by rw [pow27_add]
       _ = x^81+y^81 := by rw [cube_add]; ring

/-- The additive twist, in an arbitrary characteristic-three ring. -/
def w (a u : A) : A := a*u+a^3*u^3

theorem twist_telescoping (a u : A) (ha : a^81 = a) :
    w a u - (w a u)^3 + (w a u)^9 - (w a u)^27 =
      (1-u^80)*(a*u) := by
  simp only [w, cube_add, pow9_add, pow27_add, mul_pow, ← pow_mul]
  rw [show 3*27 = 81 by rfl, ha]
  ring

theorem twist_pow81 (a u : A) (ha : a^81 = a) :
    (w a u)^81 = (u^80)^3 * w a u + (u^80-(u^80)^3)*(a*u) := by
  simp only [w, pow81_add, mul_pow, ← pow_mul]
  rw [ha, show 3*81 = 81*3 by rfl, pow_mul, ha]
  ring

theorem twist_root (a u : A) (ha : a^81 = a) :
    (poly (u^80)).eval (w a u) = 0 := by
  have hS := twist_telescoping a u ha
  have hP := twist_pow81 a u ha
  simp only [poly, eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C]
  linear_combination hP - (u^80+(u^80)^2)*hS
end CharacteristicThree

#print axioms poly_isQPoly
#print axioms twist_telescoping
#print axioms twist_root
end Gow
```

### `GowFiniteField.lean`

```lean
import GowIdentities
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FinCases
import Mathlib.FieldTheory.Finiteness

set_option linter.unusedSimpArgs false

noncomputable section
namespace Gow
open Polynomial Module
abbrev k := ZMod 3

def modulus : k[X] := X^4 + X + 2

theorem modulus_monic : modulus.Monic := by unfold modulus; monicity; norm_num
theorem modulus_natDegree : modulus.natDegree = 4 := by
  unfold modulus; compute_degree; norm_num

private theorem no_linear_factor (a : k) : ¬ (X + C a) ∣ modulus := by
  intro hd
  have he := Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero hd (show (X+C a : k[X]).eval (-a) = 0 by simp)
  fin_cases a <;> norm_num only [modulus, eval_add, eval_pow, eval_X, eval_ofNat] at he <;> revert he <;> decide

private theorem quadratic_coprime (a b : k) :
    IsCoprime (X^2 + C a*X + C b) modulus := by
  have h3 : (3 : k[X]) = 0 := CharP.ofNat_eq_zero _ 3
  have h4 : (4 : k[X]) = 1 := by linear_combination h3
  have h6 : (6 : k[X]) = 0 := by linear_combination 2*h3
  fin_cases a <;> fin_cases b
  · change IsCoprime (X^2 + C (0 : k)*X + C (0 : k)) modulus
    refine ⟨1 + X^2 + X^3, 2 + 2*X, ?_⟩
    norm_num only [modulus, C_0, C_1, C_ofNat]
    ring_nf
    simp only [h3, h4, h6, mul_zero, add_zero, sub_zero, zero_add]
  · change IsCoprime (X^2 + C (0 : k)*X + C (1 : k)) modulus
    refine ⟨1 + 2*X + X^3, 2*X, ?_⟩
    norm_num only [modulus, C_0, C_1, C_ofNat]
    ring_nf
    simp only [h3, h4, h6, mul_zero, add_zero, sub_zero, zero_add]
  · change IsCoprime (X^2 + C (0 : k)*X + C (2 : k)) modulus
    refine ⟨2 + 2*X + 2*X^3, X, ?_⟩
    norm_num only [modulus, C_0, C_1, C_ofNat]
    ring_nf
    simp only [h3, h4, h6, mul_zero, add_zero, sub_zero, zero_add]
  · change IsCoprime (X^2 + C (1 : k)*X + C (0 : k)) modulus
    refine ⟨1 + 2*X + X^2, 2, ?_⟩
    norm_num only [modulus, C_0, C_1, C_ofNat]
    ring_nf
    simp only [h3, h4, h6, mul_zero, add_zero, sub_zero, zero_add]
  · change IsCoprime (X^2 + C (1 : k)*X + C (1 : k)) modulus
    refine ⟨1 + X^2 + 2*X^3, X, ?_⟩
    norm_num only [modulus, C_0, C_1, C_ofNat]
    ring_nf
    simp only [h3, h4, h6, mul_zero, add_zero, sub_zero, zero_add]
  · change IsCoprime (X^2 + C (1 : k)*X + C (2 : k)) modulus
    refine ⟨2 + X + X^2 + 2*X^3, X, ?_⟩
    norm_num only [modulus, C_0, C_1, C_ofNat]
    ring_nf
    simp only [h3, h4, h6, mul_zero, add_zero, sub_zero, zero_add]
  · change IsCoprime (X^2 + C (2 : k)*X + C (0 : k)) modulus
    refine ⟨2*X + 2*X^2 + X^3, 2 + 2*X, ?_⟩
    norm_num only [modulus, C_0, C_1, C_ofNat]
    ring_nf
    simp only [h3, h4, h6, mul_zero, add_zero, sub_zero, zero_add]
  · change IsCoprime (X^2 + C (2 : k)*X + C (1 : k)) modulus
    refine ⟨X + X^2, 2, ?_⟩
    norm_num only [modulus, C_0, C_1, C_ofNat]
    ring_nf
    simp only [h3, h4, h6, mul_zero, add_zero, sub_zero, zero_add]
  · change IsCoprime (X^2 + C (2 : k)*X + C (2 : k)) modulus
    refine ⟨2*X^2 + X^3, 2 + 2*X, ?_⟩
    norm_num only [modulus, C_0, C_1, C_ofNat]
    ring_nf
    simp only [h3, h4, h6, mul_zero, add_zero, sub_zero, zero_add]

private theorem no_quadratic_factor (a b : k) :
    ¬ (X^2 + C a*X + C b) ∣ modulus := by
  intro hd
  have hu := (quadratic_coprime a b).isUnit_of_dvd hd
  have hn := Polynomial.natDegree_eq_zero_of_isUnit hu
  have ht : (X^2 + C a*X + C b : k[X]).natDegree = 2 := by
    compute_degree <;> norm_num
  omega

theorem modulus_irreducible : Irreducible modulus := by
  apply (modulus_monic.irreducible_iff_lt_natDegree_lt ?_).mpr
  · intro q hq hd hdvd
    rw [modulus_natDegree] at hd
    have hn : q.natDegree = 1 ∨ q.natDegree = 2 := by
      simp only [Finset.mem_Ioc] at hd
      omega
    rcases hn with hn | hn
    · rw [hq.eq_X_add_C hn] at hdvd
      exact no_linear_factor _ hdvd
    · have he : q = X^2 + C (q.coeff 1)*X + C (q.coeff 0) := by
        conv_lhs => rw [q.as_sum_range_C_mul_X_pow]
        rw [hn]
        simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero,
          mul_one, pow_one]
        rw [show q.coeff 2 = 1 from hn ▸ hq.coeff_natDegree]
        simp only [C_1]
        ring
      rw [he] at hdvd
      exact no_quadratic_factor _ _ hdvd
  · intro he
    have := modulus_natDegree
    rw [he, natDegree_one] at this
    contradiction

instance : Fact (Irreducible modulus) := ⟨modulus_irreducible⟩
abbrev K := AdjoinRoot modulus
def z : K := AdjoinRoot.root modulus

theorem z_relation : z^4+z+2 = 0 := by
  have h := AdjoinRoot.eval₂_root modulus
  change (X^4+X+2 : k[X]).eval₂ (AdjoinRoot.of modulus) z = 0 at h
  simpa only [eval₂_add, eval₂_pow, eval₂_X, eval₂_ofNat] using h

def K_basis : Basis (Fin 4) k K :=
  ((AdjoinRoot.powerBasis modulus_monic.ne_zero).basis).reindex
    (finCongr modulus_natDegree)

theorem K_basis_apply (i : Fin 4) : K_basis i = z^i.val := by
  rw [K_basis, Basis.reindex_apply, PowerBasis.basis_eq_pow]
  rfl

instance : Module.Finite k K := Module.Finite.of_basis K_basis

instance : Finite K := Module.finite_of_finite k

theorem K_card : Nat.card K = 81 := by
  rw [Module.natCard_eq_pow_finrank (K := k)]
  have hd : Module.finrank k K = 4 := Module.finrank_eq_card_basis K_basis
  rw [hd]
  norm_num [Nat.card_zmod]

theorem K_pow81 (a : K) : a^81 = a := by
  let := Fintype.ofFinite K
  have hc : Fintype.card K = 81 := by simpa [Nat.card_eq_fintype_card] using K_card
  simpa [hc] using FiniteField.pow_card a

#print axioms modulus_irreducible
#print axioms K_pow81
end Gow
```

### `GowQuadratic.lean`

```lean
import GowIdentities

noncomputable section
namespace Gow
open MvPolynomial

/-- The source-compatible homogeneous form, with coefficients in F₃. -/
def Q : MvPolynomial (Fin 4) (ZMod 3) :=
  -(X 0)^2 + X 0*X 1 - X 0*X 2 - X 0*X 3 - X 1*X 2 + (X 2)^2 + (X 3)^2

theorem Q_homogeneous : Q.IsHomogeneous 2 := by
  have hp (i j : Fin 4) : IsHomogeneous (X i * X j : MvPolynomial (Fin 4) (ZMod 3)) 2 :=
    (isHomogeneous_X (ZMod 3) i).mul (isHomogeneous_X (ZMod 3) j)
  have hs (i : Fin 4) : IsHomogeneous ((X i)^2 : MvPolynomial (Fin 4) (ZMod 3)) 2 :=
    (isHomogeneous_X (ZMod 3) i).pow 2
  exact ((((((hs 0).neg.add (hp 0 1)).sub (hp 0 2)).sub (hp 0 3)).sub
    (hp 1 2)).add (hs 2)).add (hs 3)

theorem Q_ne_zero : Q ≠ 0 := by
  intro h
  have he := congrArg (MvPolynomial.eval (fun i : Fin 4 => if i = 3 then (1 : ZMod 3) else 0)) h
  norm_num [Q] at he

section Generic
variable {A : Type*} [CommRing A] [CharP A 3]

theorem quadratic_identity (z u : A) (hz : z^4+z+2 = 0) :
    -(w 1 u)^2 + w 1 u*w z u - w 1 u*w (z^2) u - w 1 u*w (z^3) u
      - w z u*w (z^2) u + (w (z^2) u)^2 + (w (z^3) u)^2 = 0 := by
  have h3 : (3 : A) = 0 := CharP.ofNat_eq_zero A 3
  unfold w
  linear_combination (norm := (ring_nf; simp only [h3, mul_zero, sub_zero, add_zero, neg_zero]))
    (u^2 - u^4 + u^6 + z*u^4 + z*u^6 + z^2*u^2 - z^2*u^4 + z^2*u^6
      - z^3*u^4 + z^4*u^4 + z^4*u^6 - z^5*u^6 + z^6*u^6 + z^7*u^6
      - z^8*u^4 - z^8*u^6 + z^10*u^6 - z^11*u^6 + z^14*u^6) * hz

variable [Algebra (ZMod 3) A]

theorem Q_eval_eq_zero (z u : A) (hz : z^4+z+2 = 0) :
    MvPolynomial.aeval (fun i : Fin 4 => w (z^i.val) u) Q = 0 := by
  simp only [Q, map_add, map_sub, map_neg, map_pow, map_mul, aeval_X]
  simpa using quadratic_identity z u hz

theorem eps_not_injective_of_quartic (z u : A) (hz : z^4+z+2 = 0) :
    ¬ Function.Injective (eps (fun i : Fin 4 => w (z^i.val) u) 2) := by
  intro hi
  have he : eps (fun i : Fin 4 => w (z^i.val) u) 2 ⟨Q, Q_homogeneous⟩ =
      eps (fun i : Fin 4 => w (z^i.val) u) 2 0 := by
    simpa [eps] using Q_eval_eq_zero z u hz
  have hh := congrArg Subtype.val (hi he)
  exact Q_ne_zero hh
end Generic

#print axioms Q_homogeneous
#print axioms Q_ne_zero
#print axioms quadratic_identity
#print axioms eps_not_injective_of_quartic
end Gow
```

### `GowWitness.lean`

```lean
import GowFiniteField
import GowQuadratic
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic

noncomputable section
namespace Gow
open Polynomial Module

abbrev E := RatFunc K
instance : CharP E 3 := charP_of_injective_algebraMap (algebraMap k E).injective 3

def u : E := RatFunc.X
def tE : E := u^80

def F : IntermediateField k E := IntermediateField.adjoin k {tE}
def t : F := ⟨tE, IntermediateField.subset_adjoin k {tE} (Set.mem_singleton tE)⟩
def L : F[X] := poly t

def twist (a : K) : E := w (RatFunc.C a) u
def v (i : Fin 4) : E := twist (z^i.val)

lemma twist_as_polynomial (a : K) : twist a =
    algebraMap K[X] E (C a*X + C (a^3)*X^3) := by
  simp only [twist, w, map_add, map_mul, map_pow, RatFunc.algebraMap_C,
    RatFunc.algebraMap_X, map_pow, u]

theorem twist_injective : Function.Injective twist := by
  intro a b hab
  rw [twist_as_polynomial, twist_as_polynomial] at hab
  have hp := RatFunc.algebraMap_injective K hab
  have hc := congrArg (fun P : K[X] => P.coeff 1) hp
  norm_num only [coeff_add, coeff_C_mul, coeff_X, coeff_X_pow] at hc
  simpa using hc

lemma C_pow81 (a : K) : (RatFunc.C a : E)^81 = RatFunc.C a := by
  rw [← map_pow, K_pow81]

theorem aeval_L (x : E) : aeval x L = (poly tE).eval x := by
  simp only [L, poly, map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C,
    eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C]
  rfl

theorem all_explicit_roots (a : K) : aeval (twist a) L = 0 := by
  rw [aeval_L]
  exact twist_root (RatFunc.C a) u (C_pow81 a)

theorem Q_twist_vanishes : MvPolynomial.aeval v Q = 0 := by
  have hz : (RatFunc.C z : E)^4+RatFunc.C z+2 = 0 := by
    simpa only [map_add, map_pow, map_ofNat, map_zero] using congrArg RatFunc.C z_relation
  have he := Q_eval_eq_zero (RatFunc.C z) u hz
  change MvPolynomial.aeval (fun i : Fin 4 => twist (z^i.val)) Q = 0
  simpa only [twist, map_pow] using he

theorem eps_not_injective : ¬ Function.Injective (eps v 2) := by
  intro hi
  have he : eps v 2 ⟨Q, Q_homogeneous⟩ = eps v 2 0 := by
    simpa [eps] using Q_twist_vanishes
  exact Q_ne_zero (congrArg Subtype.val (hi he))

#print axioms all_explicit_roots
#print axioms twist_injective
#print axioms eps_not_injective
end Gow
```

### `GowRootSpace.lean`

```lean
import GowWitness

noncomputable section
namespace Gow
open Polynomial Module

local instance : DecidableEq E := Classical.decEq E

/-- The additive Frobenius twist is linear over the coefficient field F₃. -/
def twistLinear : K →ₗ[k] E where
  toFun := twist
  map_add' a b := by
    simp only [twist, w, map_add, cube_add]
    ring
  map_smul' c a := by
    have hc : (algebraMap k E c)^3 = algebraMap k E c := by
      rw [← map_pow]
      congr 1
      exact FiniteField.pow_card c
    have hm : RatFunc.C (algebraMap k K c) = algebraMap k E c :=
      (IsScalarTower.algebraMap_apply k K E c).symm
    simp only [Algebra.smul_def, twist, w, map_mul, mul_pow, hm, hc, RingHom.id_apply]
    ring

theorem root_basis_independent : LinearIndependent k v := by
  have hev : v = twistLinear ∘ K_basis := by
    funext i
    change twist (z^i.val) = twist (K_basis i)
    rw [K_basis_apply]
  rw [hev]
  exact K_basis.linearIndependent.map' twistLinear
    (LinearMap.ker_eq_bot.mpr twist_injective)

theorem span_v : Submodule.span k (Set.range v) = LinearMap.range twistLinear := by
  have he := Submodule.map_span twistLinear (Set.range K_basis)
  rw [K_basis.span_eq, Submodule.map_top] at he
  rw [he]
  congr 1
  rw [← Set.range_comp]
  congr 1
  funext i
  change twist (z^i.val) = twist (K_basis i)
  rw [K_basis_apply]

instance : Fintype K := Fintype.ofFinite K

theorem explicit_roots : (poly tE).roots = (Finset.univ.image twist).val := by
  have hc : (Finset.univ.image twist).card = 81 := by
    rw [Finset.card_image_of_injective _ twist_injective, Finset.card_univ,
      ← Nat.card_eq_fintype_card, K_card]
  apply roots_eq_of_natDegree_le_card_of_ne_zero
  · intro x hx
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hx
    exact twist_root (RatFunc.C a) u (C_pow81 a)
  · rw [poly_natDegree, hc]
  · exact (poly_monic tE).ne_zero

theorem root_exhaustive (x : E) : aeval x L = 0 ↔ ∃ a : K, x = twist a := by
  rw [aeval_L]
  change (poly tE).IsRoot x ↔ _
  rw [← Polynomial.mem_roots (poly_monic tE).ne_zero, explicit_roots]
  simp only [Finset.mem_val, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨fun ⟨a, h⟩ => ⟨a, h.symm⟩, fun ⟨a, h⟩ => ⟨a, h.symm⟩⟩

theorem root_span (x : E) :
    aeval x L = 0 ↔ x ∈ Submodule.span k (Set.range v) := by
  rw [root_exhaustive, span_v]
  exact ⟨fun ⟨a, h⟩ => ⟨a, h.symm⟩, fun ⟨a, h⟩ => ⟨a, h.symm⟩⟩

#print axioms root_basis_independent
#print axioms root_exhaustive
#print axioms root_span
end Gow
```

### `GowHypotheses.lean`

```lean
import GowWitness

set_option maxRecDepth 2048

noncomputable section
namespace Gow
open Polynomial

theorem t_ne_one : tE ≠ 1 := by
  intro h
  have he : algebraMap K[X] E (X^80) = algebraMap K[X] E 1 := by
    simpa only [map_pow, RatFunc.algebraMap_X, map_one, tE, u] using h
  have hp := RatFunc.algebraMap_injective K he
  have hc := congrArg (fun P : K[X] => P.coeff 0) hp
  norm_num at hc

theorem t_add_sq_ne_zero : t+t^2 ≠ 0 := by
  intro h
  have he : u^80+u^160 = 0 := by
    have hc := congrArg (fun x : F => (x : E)) h
    simpa only [map_add, map_pow, t, tE, IntermediateField.coe_add,
      IntermediateField.coe_pow, Subtype.coe_mk, ZeroMemClass.coe_zero, ← pow_mul] using hc
  have hm : algebraMap K[X] E (X^80+X^160) = algebraMap K[X] E 0 := by
    simpa only [map_add, map_pow, RatFunc.algebraMap_X, map_zero, u] using he
  have hp := RatFunc.algebraMap_injective K hm
  have hc := congrArg (fun P : K[X] => P.coeff 80) hp
  norm_num at hc

theorem L_isQPoly : IsQPoly 3 L := poly_isQPoly t
theorem L_natDegree : L.natDegree = 3^4 := poly_natDegree t

theorem L_notQs : ∀ s : ℕ, 1 < s → ¬ IsQsPoly 3 s L := by
  intro s hs hq
  have hc : L.coeff 3 ≠ 0 := by
    rw [L, poly_coeff_three]
    exact t_add_sq_ne_zero
  obtain ⟨i, hi⟩ := hq 3 (Polynomial.mem_support_iff.mpr hc)
  have hp : 3^1 = 3^(s*i) := by simpa only [pow_one] using hi
  have he := Nat.pow_right_injective (by decide : 2 ≤ 3) hp
  have hsi : s ∣ 1 := he ▸ Nat.dvd_mul_right s i
  have hle : s ≤ 1 := Nat.le_of_dvd (by decide) hsi
  omega

theorem r_admissible : 1 ≤ (2 : ℕ) ∧ 2 ≤ 3-1 := by decide

#print axioms t_ne_one
#print axioms L_notQs
end Gow
```

### `GowScaling.lean`

```lean
import GowRootSpace
import GowHypotheses

noncomputable section
namespace Gow
open Polynomial

/-- Scaling X by a nonzero constant, first on the polynomial ring. -/
def scalePoly (c : Kˣ) : K[X] ≃ₐ[K] K[X] :=
  Polynomial.algEquivOfCompEqX (C (c : K)*X) (C ((c⁻¹ : Kˣ) : K)*X)
    (by simp only [mul_comp, C_comp, X_comp, ← mul_assoc, ← C_mul]; simp)
    (by simp only [mul_comp, C_comp, X_comp, ← mul_assoc, ← C_mul]; simp)

/-- The genuine field automorphism of RatFunc K. -/
def scaleK (c : Kˣ) : E ≃ₐ[K] E := IsFractionRing.algEquivOfAlgEquiv (scalePoly c)

lemma scaleK_C (c : Kˣ) (a : K) : scaleK c (RatFunc.C a) = RatFunc.C a :=
  (scaleK c).commutes a

lemma scaleK_u (c : Kˣ) : scaleK c u = RatFunc.C (c : K)*u := by
  change scaleK c (algebraMap K[X] E X) = _
  rw [scaleK, IsFractionRing.algEquivOfAlgEquiv_algebraMap]
  simp only [scalePoly, Polynomial.algEquivOfCompEqX_apply, aeval_X,
    map_mul, RatFunc.algebraMap_C, RatFunc.algebraMap_X, u]

lemma unit_pow80 (c : Kˣ) : (c : K)^80 = 1 := by
  have hc : Fintype.card K = 81 := by simpa only [Nat.card_eq_fintype_card] using K_card
  simpa only [hc] using FiniteField.pow_card_sub_one_eq_one (c : K) c.ne_zero

lemma scaleK_t (c : Kˣ) : scaleK c tE = tE := by
  rw [tE, map_pow, scaleK_u, mul_pow, ← map_pow, unit_pow80, map_one, one_mul]

lemma scaleK_fixes_F (c : Kˣ) (a : F) : scaleK c (a : E) = a := by
  have hp (x : E) (hx : x ∈ F) : scaleK c x = x := by
    apply IntermediateField.adjoin_induction k (s := {tE}) (p := fun x _ => scaleK c x = x)
    · intro y hy
      obtain rfl := Set.mem_singleton_iff.mp hy
      exact scaleK_t c
    · intro b
      rw [IsScalarTower.algebraMap_apply k K E]
      exact (scaleK c).commutes ((algebraMap k K) b)
    · intro x y _ _ hx hy
      rw [map_add, hx, hy]
    · intro x _ hx
      rw [map_inv₀, hx]
    · intro x y _ _ hx hy
      rw [map_mul, hx, hy]
    · exact hx
  exact hp a a.property

/-- The same automorphism, now certified to fix the actual base field F. -/
def scale (c : Kˣ) : E ≃ₐ[F] E :=
  { (scaleK c).toRingEquiv with commutes' := scaleK_fixes_F c }

lemma scale_twist (c : Kˣ) : scale c (twist 1) = twist (c : K) := by
  change scaleK c (w (RatFunc.C 1) u) = w (RatFunc.C (c : K)) u
  simp only [w, map_add, map_mul, map_pow, map_one, scaleK_u]
  ring

#print axioms scale
#print axioms scale_twist
end Gow
```

### `GowSplitting.lean`

```lean
import GowRootSpace
import GowHypotheses

noncomputable section
namespace Gow
open Polynomial

local instance splittingDecEqE : DecidableEq E := Classical.decEq E

theorem recover_au (a : K) :
    (twist a - (twist a)^3 + (twist a)^9 - (twist a)^27)/(1-tE) = RatFunc.C a*u := by
  have hd : 1-tE ≠ 0 := sub_ne_zero.mpr (Ne.symm t_ne_one)
  apply (div_eq_iff hd).mpr
  simpa only [mul_comm, twist, tE] using twist_telescoping (RatFunc.C a) u (C_pow81 a)

theorem map_L : L.map (algebraMap F E) = poly tE := by
  simp only [L, poly, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
  rfl

theorem L_splits : (L.map (algebraMap F E)).Splits := by
  rw [map_L, Polynomial.splits_iff_card_roots, explicit_roots]
  rw [Finset.card_val, Finset.card_image_of_injective _ twist_injective,
    Finset.card_univ, ← Nat.card_eq_fintype_card, K_card, poly_natDegree]

theorem roots_generate : IntermediateField.adjoin F (L.rootSet E) = ⊤ := by
  let S := IntermediateField.adjoin F (L.rootSet E)
  have hw (a : K) : twist a ∈ S :=
    IntermediateField.subset_adjoin F (L.rootSet E)
      ((poly_monic t).mem_rootSet.mpr (all_explicit_roots a))
  have ht : tE ∈ S := S.algebraMap_mem t
  have hd : 1-tE ∈ S := S.sub_mem S.one_mem ht
  have hau (a : K) : RatFunc.C a*u ∈ S := by
    rw [← recover_au a]
    exact S.div_mem (S.sub_mem (S.add_mem (S.sub_mem (hw a) (S.pow_mem (hw a) 3))
      (S.pow_mem (hw a) 9)) (S.pow_mem (hw a) 27)) hd
  have hu : u ∈ S := by simpa only [map_one, one_mul] using hau 1
  have hune : u ≠ 0 := RatFunc.X_ne_zero
  have hconst (a : K) : RatFunc.C a ∈ S := by
    have hh := S.div_mem (hau a) hu
    simpa only [mul_div_cancel_right₀ _ hune] using hh
  have hpoly (p : K[X]) : algebraMap K[X] E p ∈ S := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simpa only [map_add] using S.add_mem hp hq
    | monomial n a =>
        simpa only [RatFunc.algebraMap_monomial, u] using
          S.mul_mem (hconst a) (pow_mem hu n)
  apply top_unique
  intro x _
  exact RatFunc.induction_on x (fun p q _ => S.div_mem (hpoly p) (hpoly q))

theorem L_splittingField : Polynomial.IsSplittingField F E L :=
  isSplittingField_iff_intermediateField.mpr ⟨L_splits, roots_generate⟩

#print axioms roots_generate
#print axioms L_splittingField
end Gow
```

### `GowIrreducible.lean`

```lean
import GowScaling
import Mathlib.FieldTheory.Minpoly.Field

noncomputable section
namespace Gow
open Polynomial

local instance irreducibleDecEqE : DecidableEq E := Classical.decEq E

theorem L_constant : L.coeff 0 = 0 := by
  norm_num only [L, poly, coeff_add, coeff_sub, coeff_C_mul, coeff_X_pow, coeff_X]
  simp

theorem L_eq_X_mul_divX : X*L.divX = L := by
  simpa only [L_constant, C_0, add_zero] using Polynomial.X_mul_divX_add L

theorem L_divX_monic : L.divX.Monic := by
  apply monic_X.of_mul_monic_left
  rw [L_eq_X_mul_divX]
  exact poly_monic t

theorem L_divX_degree : L.divX.natDegree = 80 := by
  rw [natDegree_divX_eq_natDegree_tsub_one, L_natDegree]
  norm_num

theorem twist_one_ne_zero : twist 1 ≠ 0 := by
  have h0 : twist 0 = 0 := by simp [twist, w]
  intro he
  have hh : (1 : K) = 0 := twist_injective (he.trans h0.symm)
  exact one_ne_zero hh

theorem divX_root : aeval (twist 1) L.divX = 0 := by
  have hh : aeval (twist 1) (X*L.divX) = 0 := by
    rw [L_eq_X_mul_divX]
    exact all_explicit_roots 1
  rw [map_mul, aeval_X] at hh
  exact (mul_eq_zero.mp hh).resolve_left twist_one_ne_zero

lemma twist_one_integral : IsIntegral F (twist 1) :=
  ⟨L, poly_monic t, all_explicit_roots 1⟩

lemma conjugate_root (c : Kˣ) : aeval (twist (c : K)) (minpoly F (twist 1)) = 0 := by
  rw [← scale_twist c]
  exact minpoly.aeval_algHom F (scale c).toAlgHom (twist 1)

lemma minpoly_degree_lower : 80 ≤ (minpoly F (twist 1)).natDegree := by
  let P := (minpoly F (twist 1)).map (algebraMap F E)
  let S := Finset.univ.image (fun c : Kˣ => twist (c : K))
  have hinj : Function.Injective (fun c : Kˣ => twist (c : K)) :=
    twist_injective.comp Units.val_injective
  have hc : S.card = 80 := by
    dsimp [S]
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_units]
    have hh : Fintype.card K = 81 := by simpa only [Nat.card_eq_fintype_card] using K_card
    rw [hh]
  have hP : P ≠ 0 := ((minpoly.monic twist_one_integral).map (algebraMap F E)).ne_zero
  have hS : S.val ⊆ P.roots := by
    intro x hx
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hx
    apply (Polynomial.mem_roots hP).mpr
    exact (Polynomial.eval_map_algebraMap _ _).trans (conjugate_root c)
  have hd := Polynomial.card_le_degree_of_subset_roots hS
  rw [hc] at hd
  exact hd.trans Polynomial.natDegree_map_le

theorem L_divX_irreducible : Irreducible L.divX := by
  have he : L.divX = minpoly F (twist 1) := by
    apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le
      (minpoly.monic twist_one_integral) L_divX_monic (minpoly.dvd F (twist 1) divX_root)
    rw [L_divX_degree]
    exact minpoly_degree_lower
  rw [he]
  exact minpoly.irreducible twist_one_integral

#print axioms L_divX_irreducible
end Gow
```

### `GowEndpoint.lean`

```lean
import GowIrreducible
import GowSplitting

set_option maxRecDepth 2048

noncomputable section
namespace Gow
open Polynomial

/-- The linear coefficient is genuinely nonzero in the specified base field. -/
theorem L_coeff_one_ne_zero : L.coeff 1 ≠ 0 := by
  rw [L, poly_coeff_one]
  intro h
  have hc := congrArg (fun x : F => (x : E)) h
  change -(u^80*((u^80)^2+u^80+1)) = 0 at hc
  have hm : algebraMap K[X] E (-(X^240+X^160+X^80)) = 0 := by
    simp only [map_neg, map_add, map_pow, RatFunc.algebraMap_X]
    change -(u^240+u^160+u^80) = 0
    linear_combination hc
  have hp : (-(X^240+X^160+X^80) : K[X]) = 0 :=
    RatFunc.algebraMap_injective K (by simpa only [map_zero] using hm)
  have hh := congrArg (fun P : K[X] => P.coeff 240) hp
  norm_num at hh

/-- Every source hypothesis and the negated conclusion, for the actual witness. -/
theorem concrete_counterexample :
    IsQPoly 3 L ∧ L.natDegree = 3^4 ∧
    (∀ s : ℕ, 1 < s → ¬ IsQsPoly 3 s L) ∧
    Irreducible L.divX ∧ Polynomial.IsSplittingField F E L ∧
    LinearIndependent k v ∧
    (∀ x : E, aeval x L = 0 ↔ x ∈ Submodule.span k (Set.range v)) ∧
    ¬ Function.Injective (eps v 2) :=
  ⟨L_isQPoly, L_natDegree, L_notQs, L_divX_irreducible, L_splittingField,
    root_basis_independent, root_span, eps_not_injective⟩

/-- Literal negation of the universal q=3 specialization of Conjecture 1. -/
theorem mathdb_354868_false : ¬ Conjecture := by
  intro hc
  exact eps_not_injective
    (hc F E 4 2 L v L_isQPoly L_natDegree L_notQs L_divX_irreducible
      L_splittingField root_basis_independent root_span (by decide) (by decide))

#print Conjecture
#check concrete_counterexample
#check mathdb_354868_false
#print axioms concrete_counterexample
#print axioms mathdb_354868_false
#print axioms L_coeff_one_ne_zero
#eval Lean.versionString
end Gow
```

