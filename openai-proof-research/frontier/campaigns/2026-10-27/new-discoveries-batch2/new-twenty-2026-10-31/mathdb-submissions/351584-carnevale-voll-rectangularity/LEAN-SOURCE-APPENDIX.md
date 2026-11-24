# Lean source appendix

Stage 4; E2. All 49 stage-3 modules are retained unchanged. Blueprint contains proposition specifications, not assumed facts. Optional M5, R1, S2–S4 are unused and unproved; the final proof bypasses them. Historical comments in retained modules describe earlier stages, not this completed endpoint. All module blocks are byte-identical to src/.

### `SourceDefinitions.lean`

```lean
import Mathlib.Data.List.Permutation
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic.NormNum

namespace Carnevale
noncomputable section

abbrev Bivar := MvPolynomial (Fin 2) ℤ

def x : Bivar := MvPolynomial.X 0
def y : Bivar := MvPolynomial.X 1

/-- The source's trivial word, with letters starting at 1. -/
def baseFrom (letter : ℕ) : List ℕ → List ℕ
  | [] => []
  | m :: ms => List.replicate m letter ++ baseFrom (letter + 1) ms

def baseWord (η : List ℕ) : List ℕ := baseFrom 1 η

def multisetPerms (η : List ℕ) : Finset (List ℕ) :=
  (baseWord η).permutations'.toFinset

/-- Stored indices start at 0; the statistic `den` adds 1 to each index. -/
def excPositions (η w : List ℕ) : Finset ℕ :=
  (Finset.range w.length).filter (fun i => (baseWord η)[i]?.getD 0 < w[i]?.getD 0)

def exc (η w : List ℕ) : ℕ := (excPositions η w).card

def exceedingWord (η w : List ℕ) : List ℕ :=
  ((w.zipIdx).filter (fun p => (baseWord η)[p.2]?.getD 0 < p.1)).map Prod.fst

def nonExceedingWord (η w : List ℕ) : List ℕ :=
  ((w.zipIdx).filter (fun p => ¬ (baseWord η)[p.2]?.getD 0 < p.1)).map Prod.fst

/-- Strict inversions: i<j and w_i>w_j. -/
def inv (w : List ℕ) : ℕ :=
  (((Finset.range w.length) ×ˢ (Finset.range w.length)).filter
    (fun p => p.1 < p.2 ∧ w[p.2]?.getD 0 < w[p.1]?.getD 0)).card

/-- Weak inversions: i<j and w_i≥w_j. -/
def imv (w : List ℕ) : ℕ :=
  (((Finset.range w.length) ×ˢ (Finset.range w.length)).filter
    (fun p => p.1 < p.2 ∧ w[p.2]?.getD 0 ≤ w[p.1]?.getD 0)).card

def den (η w : List ℕ) : ℕ :=
  (∑ i ∈ excPositions η w, (i + 1)) + imv (exceedingWord η w) +
    inv (nonExceedingWord η w)

def denertPoly (η : List ℕ) : Bivar :=
  ∑ w ∈ multisetPerms η, x ^ den η w * y ^ exc η w

/-- Nonconstancy is part of the printed source's definition. -/
def IsUnitary (f : Bivar) : Prop :=
  (¬ ∃ c : ℤ, f = MvPolynomial.C c) ∧
  ∃ (F : Polynomial ℤ) (a b : ℕ),
    f = Polynomial.eval₂ (Int.castRingHom Bivar) (x ^ a * y ^ b) F ∧
    ∀ z : ℂ, Polynomial.eval₂ (Int.castRingHom ℂ) z F = 0 → ‖z‖ = 1

def HasUnitaryFactor (P : Bivar) : Prop := ∃ f : Bivar, IsUnitary f ∧ f ∣ P

def rectangleFactor (N : ℕ) : Bivar := 1 + x ^ (N / 2) * y

def Conjecture23 : Prop :=
  ∀ η : List ℕ, η ≠ [] → (∀ m ∈ η, 0 < m) →
    (HasUnitaryFactor (denertPoly η) ↔
      ∃ m r : ℕ, 0 < m ∧ 0 < r ∧ η = List.replicate r m ∧ Odd m ∧ Even r) ∧
    (∀ m r : ℕ, 0 < m → 0 < r → η = List.replicate r m → Odd m → Even r →
      ∃ f0 : Bivar, denertPoly η = rectangleFactor η.sum * f0 ∧
        ¬ HasUnitaryFactor f0)

end
end Carnevale
```

### `SourceStatement.lean`

```lean
import SourceDefinitions
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.WellKnown

namespace Carnevale

abbrev Series := PowerSeries (Polynomial ℤ)

noncomputable def seriesOfBivar : Bivar →+* Series :=
  MvPolynomial.eval₂Hom (Int.castRingHom Series)
    (fun i => if i = 0 then PowerSeries.C Polynomial.X else PowerSeries.X)

noncomputable def denominator (m : ℕ) : Series :=
  ∏ j ∈ Finset.range (m + 1),
    (1 - PowerSeries.C (Polynomial.X ^ j) * PowerSeries.X)

noncomputable def inverseDenominator (m : ℕ) : Series :=
  PowerSeries.invOfUnit (denominator m) 1

/-- Empty coefficientwise product has every coefficient equal to 1. -/
noncomputable def hadamard (ss : List Series) : Series :=
  PowerSeries.mk (fun k => (ss.map (fun s => PowerSeries.coeff k s)).prod)

/-- The numerator form of the published formula (10), combined with Theorems 3/10. -/
def SourceFormula10At (η : List ℕ) : Prop :=
  seriesOfBivar (denertPoly η) = denominator η.sum * hadamard (η.map inverseDenominator)

/-- The sole external theorem allowed as a hypothesis of the E2 endpoint. -/
def SourceFormula10 : Prop :=
  ∀ η : List ℕ, η ≠ [] → (∀ m ∈ η, 0 < m) → SourceFormula10At η

/-- This records the requested endpoint's TYPE; it is not its proof. -/
def E2Endpoint : Prop := SourceFormula10 → Conjecture23

end Carnevale
```

### `SourceTests.lean`

```lean
import SourceStatement

namespace Carnevale

noncomputable section

theorem den_source_example : den [3,2,2,3] [4,2,3,2,3,1,4,1,4,1] = 27 := by decide

theorem source_example_subwords :
    exceedingWord [3,2,2,3] [4,2,3,2,3,1,4,1,4,1] = [4,2,3,3,4] ∧
    nonExceedingWord [3,2,2,3] [4,2,3,2,3,1,4,1,4,1] = [2,1,1,4,1] := by decide

theorem polynomial_singleton_one : denertPoly [1] = 1 := by
  have hw : multisetPerms [1] = {[1]} := by decide
  have hd : den [1] [1] = 0 := by decide
  have he : exc [1] [1] = 0 := by decide
  simp [denertPoly, hw, hd, he]

theorem polynomial_singleton_two : denertPoly [2] = 1 := by
  have hw : multisetPerms [2] = {[1,1]} := by decide
  have hd : den [2] [1,1] = 0 := by decide
  have he : exc [2] [1,1] = 0 := by decide
  simp [denertPoly, hw, hd, he]

theorem polynomial_two_letters : denertPoly [1,1] = 1 + x * y := by
  have hw : multisetPerms [1,1] = {[1,2], [2,1]} := by decide
  have hd : den [1,1] [1,2] = 0 := by decide
  have he : exc [1,1] [1,2] = 0 := by decide
  have hd' : den [1,1] [2,1] = 1 := by decide
  have he' : exc [1,1] [2,1] = 1 := by decide
  simp [denertPoly, hw, hd, he, hd', he']

theorem denominator_constant (m : ℕ) :
    PowerSeries.constantCoeff (denominator m) = 1 := by
  simp [denominator]

theorem denominator_inverse (m : ℕ) : denominator m * inverseDenominator m = 1 := by
  exact PowerSeries.mul_invOfUnit _ 1 (by simpa using denominator_constant m)

theorem hadamard_singleton (s : Series) : hadamard [s] = s := by
  ext k
  simp [hadamard]

theorem formula_singleton_one : SourceFormula10At [1] := by
  unfold SourceFormula10At
  rw [polynomial_singleton_one, map_one]
  simp only [List.sum_cons, List.sum_nil, add_zero, List.map_cons, List.map_nil,
    hadamard_singleton]
  exact (denominator_inverse 1).symm

theorem formula_singleton_two : SourceFormula10At [2] := by
  unfold SourceFormula10At
  rw [polynomial_singleton_two, map_one]
  simp only [List.sum_cons, List.sum_nil, add_zero, List.map_cons, List.map_nil,
    hadamard_singleton]
  exact (denominator_inverse 2).symm

#print axioms den_source_example
#print axioms source_example_subwords
#print axioms polynomial_two_letters
#print axioms formula_singleton_one
#print axioms formula_singleton_two
end
end Carnevale
```

### `LiteralFoundation.lean`

```lean
import SourceTests

namespace Carnevale

/-- The enumerator contains precisely all rearrangements of the trivial word. -/
theorem mem_multisetPerms (η w : List ℕ) :
    w ∈ multisetPerms η ↔ w.Perm (baseWord η) := by
  simp only [multisetPerms, List.mem_toFinset, List.mem_permutations']

theorem baseFrom_length (letter : ℕ) (η : List ℕ) :
    (baseFrom letter η).length = η.sum := by
  induction η generalizing letter with
  | nil => rfl
  | cons m ms ih => simp [baseFrom, ih]

theorem baseWord_length (η : List ℕ) : (baseWord η).length = η.sum :=
  baseFrom_length 1 η

theorem word_length {η w : List ℕ} (hw : w ∈ multisetPerms η) : w.length=η.sum := by
  exact ((mem_multisetPerms η w).mp hw).length_eq.trans (baseWord_length η)

theorem baseWord_mem (η : List ℕ) : baseWord η ∈ multisetPerms η :=
  (mem_multisetPerms η (baseWord η)).mpr (List.Perm.refl _)

#print axioms mem_multisetPerms
#print axioms baseWord_length
#print axioms word_length
#print axioms baseWord_mem
#print Carnevale.Conjecture23
#print Carnevale.SourceFormula10At
#print Carnevale.SourceFormula10
#print Carnevale.E2Endpoint
#print axioms Carnevale.denertPoly
#print axioms Carnevale.SourceFormula10
#print axioms Carnevale.Conjecture23
end Carnevale
```

### `AlgebraicModel.lean`

```lean
import SourceStatement
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Algebra.Squarefree.Basic

namespace Carnevale
noncomputable section

abbrev K := RatFunc ℚ

def q : K := RatFunc.X

def bivarToK : Bivar →+* Polynomial K :=
  MvPolynomial.eval₂Hom (Int.castRingHom (Polynomial K))
    (fun i => if i = 0 then Polynomial.C q else Polynomial.X)

def A (η : List ℕ) : Polynomial K := bivarToK (denertPoly η)

def AInverseQ (η : List ℕ) : Polynomial K :=
  MvPolynomial.eval₂ (Int.castRingHom (Polynomial K))
    (fun i => if i = 0 then Polynomial.C q⁻¹ else Polynomial.X) (denertPoly η)

def block (η : List ℕ) : Polynomial K :=
  (η.map (fun m => ∏ s ∈ Finset.range m,
    (1 - Polynomial.C (q ^ (s+1)) * Polynomial.X))).prod

def c (η : List ℕ) (j : ℕ) : K := (block η).coeff j

def E (η : List ℕ) : K := (block η).eval 1

def R (η : List ℕ) (t : K) : K :=
  ∑ j ∈ Finset.range (η.sum+1), c η j / (1-t*q^j)

def L (η : List ℕ) (a : ℕ) : K :=
  ∑ j ∈ Finset.range (η.sum+1), c η j / (1+q^((j:ℤ)-(a:ℤ)))

def weight (η : List ℕ) : ℕ := (η.map (fun m => m*(m+1)/2)).sum

def levelSum {F : Type*} [Semiring F] (η : List ℕ) (z : F) : F :=
  (η.map (fun m => ∑ s ∈ Finset.range m, z^(s+1))).sum

def qGaussian : ℕ → ℕ → Polynomial ℤ
  | 0, 0 => 1
  | 0, _+1 => 0
  | _+1, 0 => 1
  | n+1, k+1 => qGaussian n (k+1) + Polynomial.X^(n-k) * qGaussian n k

def specializeYZero (P : Bivar) : Polynomial ℤ :=
  MvPolynomial.eval₂ (Int.castRingHom (Polynomial ℤ))
    (fun i => if i=0 then Polynomial.X else 0) P

def specializeXZero (P : Bivar) : Polynomial ℤ :=
  MvPolynomial.eval₂ (Int.castRingHom (Polynomial ℤ))
    (fun i => if i=0 then 0 else Polynomial.X) P

def specializeXOneReal (P : Bivar) : Polynomial ℝ :=
  MvPolynomial.eval₂ (Int.castRingHom (Polynomial ℝ))
    (fun i => if i=0 then 1 else Polynomial.X) P

def T (d : ℕ) (cc : ℝ) (W : Polynomial ℝ) : Polynomial ℝ :=
  (Polynomial.C cc + Polynomial.C ((d+1:ℝ)-cc)*Polynomial.X)*W +
    Polynomial.X*(1-Polynomial.X)*W.derivative

def SimpleNegative (W : Polynomial ℝ) : Prop :=
  W ≠ 0 ∧ Squarefree W ∧
    ∀ z : ℂ, (W.map (algebraMap ℝ ℂ)).IsRoot z → z.im=0 ∧ z.re<0

/-- Ambient degree d is the exponent d+1 in the Euler transform denominator. -/
def eulerSeries (d : ℕ) (P : Polynomial ℝ) : PowerSeries ℝ :=
  (1-PowerSeries.X)^(d+1) * PowerSeries.mk (fun k => P.eval (k:ℝ))

def rectangleReciprocity (η : List ℕ) (N d : ℕ) : Prop :=
  ∀ t : K, t ≠ 0 →
    (AInverseQ η).eval t⁻¹ = t^(-(d:ℤ))*q^(-((N*d/2:ℕ):ℤ))*(A η).eval t

end
end Carnevale
```

### `PolePrototype.lean`

```lean
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

namespace Carnevale

/-- Valid even when j<a: no natural subtraction is used in the exponent. -/
theorem negative_exponent_denominator {K : Type*} [Field K] (q : K)
    (hq : q ≠ 0) (j a : ℕ) :
    1 + q ^ ((j : ℤ) - (a : ℤ)) = (q ^ a + q ^ j) / q ^ a := by
  rw [zpow_sub₀ hq, zpow_natCast, zpow_natCast]
  field_simp

/-- Laurent evaluation reduces to polynomial evaluation at every nonzero point. -/
theorem negative_exponent_zero_iff {K : Type*} [Field K] (ζ : K)
    (hζ : ζ ≠ 0) (j a : ℕ) :
    1 + ζ ^ ((j : ℤ) - (a : ℤ)) = 0 ↔ ζ ^ a + ζ ^ j = 0 := by
  rw [negative_exponent_denominator ζ hζ j a, div_eq_zero_iff]
  simp [pow_ne_zero _ hζ]

/-- At a zero of v, all regular terms disappear after polynomial clearing.
The numerator n may represent one singular term or a combined singular pair. -/
theorem cleared_pole_numerator {K : Type*} [Field K] {ι : Type*}
    (s : Finset ι) (d : ι → Polynomial K) (n v b : Polynomial K) (ζ : K)
    (hd : ∀ i ∈ s, (d i).eval ζ ≠ 0) (hv : v.eval ζ = 0)
    (h : n * (∏ i ∈ s, d i) + v * b = 0) : n.eval ζ = 0 := by
  have he := congrArg (Polynomial.eval ζ) h
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_zero, hv,
    zero_mul, add_zero, Polynomial.eval_prod] at he
  have hprod : (∏ i ∈ s, (d i).eval ζ) ≠ 0 := Finset.prod_ne_zero_iff.mpr hd
  exact (mul_eq_zero.mp he).resolve_right hprod

/-- In particular, a single pole with nonzero numerator cannot cancel. -/
theorem isolated_pole_impossible {K : Type*} [Field K] {ι : Type*}
    (s : Finset ι) (d : ι → Polynomial K) (n v b : Polynomial K) (ζ : K)
    (hd : ∀ i ∈ s, (d i).eval ζ ≠ 0) (hv : v.eval ζ = 0)
    (hn : n.eval ζ ≠ 0) : n * (∏ i ∈ s, d i) + v * b ≠ 0 := by
  intro h
  exact hn (cleared_pole_numerator s d n v b ζ hd hv h)

/-- One may clear in a fraction field and then return to polynomials.
This is the injectivity step needed before evaluating at a pole. -/
theorem fraction_identity_clears {K F : Type*} [Field K] [Field F]
    (f : Polynomial K →+* F) (hf : Function.Injective f)
    (n v b D : Polynomial K) (hv : f v ≠ 0) (hD : f D ≠ 0)
    (h : f n / f v + f b / f D = 0) : n*D+v*b=0 := by
  apply hf
  simp only [map_add, map_mul, map_zero]
  have hh := (div_add_div (f n) (f b) hv hD).symm.trans h
  have hh' := (div_eq_zero_iff.mp hh).resolve_right (mul_ne_zero hv hD)
  simpa only [mul_comm (f b) (f v)] using hh'

/-- First-pole isolation for the smallest nontrivial even N. -/
theorem primitive_four_denominators (j : ℕ) (hj : j≤4) :
    1 + Complex.I ^ ((j:ℤ)-2) = 0 ↔ j=0 ∨ j=4 := by
  have h := negative_exponent_zero_iff Complex.I Complex.I_ne_zero j 2
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  interval_cases j <;> norm_num [pow_succ, Complex.I_mul_I, Complex.ext_iff]

/-- The second pole when N=4 has exactly indices 1 and 3. -/
theorem second_pole_four_denominators (j : ℕ) (hj : j≤4) :
    1 + (-1:ℂ) ^ ((j:ℤ)-2) = 0 ↔ j=1 ∨ j=3 := by
  have h := negative_exponent_zero_iff (-1:ℂ) (by norm_num) j 2
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  interval_cases j <;> norm_num

#print axioms negative_exponent_denominator
#print axioms negative_exponent_zero_iff
#print axioms cleared_pole_numerator
#print axioms isolated_pole_impossible
#print axioms fraction_identity_clears
#print axioms primitive_four_denominators
#print axioms second_pole_four_denominators
end Carnevale
```

### `ModelFoundation.lean`

```lean
import AlgebraicModel
import PolePrototype

namespace Carnevale

/-- q is transcendental, hence nonzero. -/
theorem q_ne_zero : q ≠ 0 := RatFunc.X_ne_zero

/-- A positive binomial of powers is nonzero as a rational function.
Polynomial evaluation at 1 proves this without any order on RatFunc. -/
theorem power_add_power_ne_zero (a j : ℕ) : q^a+q^j ≠ 0 := by
  intro hh
  have he : (Polynomial.X^a+Polynomial.X^j : Polynomial ℚ)=0 := by
    apply RatFunc.algebraMap_injective ℚ
    simpa [q] using hh
  have h1 := congrArg (Polynomial.eval 1) he
  norm_num at h1

theorem slope_denominator_ne_zero (j a : ℕ) :
    1+q^((j:ℤ)-(a:ℤ)) ≠ 0 := by
  rw [negative_exponent_denominator q q_ne_zero j a]
  exact div_ne_zero (power_add_power_ne_zero a j) (pow_ne_zero _ q_ne_zero)

theorem one_sub_q_power_ne_zero (s : ℕ) (hs : 0<s) : 1-q^s ≠ 0 := by
  intro hh
  have he : (1-Polynomial.X^s : Polynomial ℚ)=0 := by
    apply RatFunc.algebraMap_injective ℚ
    simpa [q] using hh
  have h0 := congrArg (Polynomial.eval 0) he
  norm_num [ne_of_gt hs] at h0

theorem E_ne_zero (η : List ℕ) : E η ≠ 0 := by
  induction η with
  | nil => simp [E,block]
  | cons m ms ih =>
    change ((∏ s ∈ Finset.range m,
      (1-Polynomial.C (q^(s+1))*Polynomial.X)) * block ms).eval 1 ≠ 0
    rw [Polynomial.eval_mul]
    apply mul_ne_zero _ ih
    rw [Polynomial.eval_prod]
    apply Finset.prod_ne_zero_iff.mpr
    intro s _
    simpa using one_sub_q_power_ne_zero (s+1) (Nat.succ_pos _)

#print axioms q_ne_zero
#print axioms power_add_power_ne_zero
#print axioms slope_denominator_ne_zero
#print axioms one_sub_q_power_ne_zero
#print axioms E_ne_zero
end Carnevale
```

### `SincPrototype.lean`

```lean
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace Carnevale

/-- Derivative numerator for sinc; proved on the closed interval to include 0. -/
theorem sin_sub_mul_cos_pos {u : ℝ} (hu : 0 < u) (hp : u < Real.pi) :
    0 < Real.sin u - u * Real.cos u := by
  have hd (t : ℝ) : HasDerivAt (fun s : ℝ => Real.sin s - s * Real.cos s)
      (t * Real.sin t) t := by
    convert (Real.hasDerivAt_sin t).sub
      ((hasDerivAt_id t).mul (Real.hasDerivAt_cos t)) using 1 <;> first | (funext s; rfl) | (dsimp; ring)
  have hm : StrictMonoOn (fun s : ℝ => Real.sin s - s * Real.cos s)
      (Set.Icc 0 Real.pi) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    · fun_prop
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hd t).deriv]
      exact mul_pos ht.1 (Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2)
  have hh := hm (by simp [Real.pi_pos.le]) ⟨hu.le, hp.le⟩ hu
  simpa using hh

/-- The closed interval includes sinc(0)=1 and sinc(pi)=0. -/
theorem strictAntiOn_sinc : StrictAntiOn Real.sinc (Set.Icc 0 Real.pi) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _) Real.continuous_sinc.continuousOn
  intro t ht
  rw [interior_Icc] at ht
  have hn : t ≠ 0 := ne_of_gt ht.1
  have hd : HasDerivAt (fun s : ℝ => Real.sin s / s)
      ((Real.cos t * t - Real.sin t) / t ^ 2) t :=
    by
      convert (Real.hasDerivAt_sin t).div (hasDerivAt_id t) hn using 1 <;> first | (funext s; rfl) | (dsimp; ring)
  have he : Real.sinc =ᶠ[nhds t] (fun s : ℝ => Real.sin s / s) := by
    filter_upwards [eventually_ne_nhds hn] with s hs
    exact Real.sinc_of_ne_zero hs
  rw [(hd.congr_of_eventuallyEq he).deriv]
  exact div_neg_of_neg_of_pos (by nlinarith [sin_sub_mul_cos_pos ht.1 ht.2])
    (sq_pos_of_ne_zero hn)

theorem sinc_mul_gt {u v : ℝ} (hu : 0 < u) (hv : 0 < v)
    (hp : u + v < Real.pi) : Real.sinc (u + v) < Real.sinc u * Real.sinc v := by
  have hup : u < Real.pi := by linarith
  have hvp : v < Real.pi := by linarith
  have su := Real.sin_pos_of_pos_of_lt_pi hu hup
  have sv := Real.sin_pos_of_pos_of_lt_pi hv hvp
  have gu := sin_sub_mul_cos_pos hu hup
  have gv := sin_sub_mul_cos_pos hv hvp
  rw [Real.sinc_of_ne_zero (ne_of_gt (add_pos hu hv)),
    Real.sinc_of_ne_zero (ne_of_gt hu), Real.sinc_of_ne_zero (ne_of_gt hv)]
  rw [Real.sin_add]
  apply (div_lt_iff₀ (add_pos hu hv)).2
  field_simp
  nlinarith [mul_pos (mul_pos hu su) gv, mul_pos (mul_pos hv sv) gu]

#print axioms sin_sub_mul_cos_pos
#print axioms strictAntiOn_sinc
#print axioms sinc_mul_gt
end Carnevale
```

### `SineSum.lean`

```lean
import SincPrototype
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

namespace Carnevale

/-- Finite sine sum, with the endpoint m=0 included. -/
theorem finite_sine_sum (m : ℕ) (z M : ℝ) (hz : Real.sin z ≠ 0) :
    (∑ s ∈ Finset.range m, Real.sin (2*z*((s+1 : ℝ)-(M+1)/2))) =
      Real.sin (m*z)*Real.sin ((m-M)*z)/Real.sin z := by
  apply (eq_div_iff hz).2
  have h := Real.sin_mul_sum_sin m (2*z) (z*(1-M))
  have hsum : (∑ s ∈ Finset.range m, Real.sin (2*z*((s+1:ℝ)-(M+1)/2))) =
      ∑ s ∈ Finset.range m, Real.sin (2*z*s+z*(1-M)) := by
    apply Finset.sum_congr rfl
    intro s _
    congr 1
    ring
  rw [show 2*z/2=z by ring,
    show (m:ℝ)*(2*z)/2=m*z by ring,
    show ((m:ℝ)-1)*(2*z)/2+z*(1-M)=(m-M)*z by ring] at h
  rw [hsum, mul_comm]
  exact h

/-- Pointwise strict comparison. This includes m*z=pi and m<M. -/
theorem sine_product_lt {m M z : ℝ} (hm : 0<m) (hM : 0<M)
    (hz : 0<z) (hangle : m*z≤Real.pi) (hmean : M*z<Real.pi)
    (hne : m ≠ M) :
    Real.sin (m*z)*Real.sin ((m-M)*z) <
      z^2*Real.sinc (M*z)*m*(m-M) := by
  have hmp : 0 < m*z := mul_pos hm hz
  have hMp : 0 < M*z := mul_pos hM hz
  have sinc_id (t : ℝ) : Real.sin t = t*Real.sinc t := by
    by_cases ht : t=0
    · simp [ht]
    · rw [Real.sinc_of_ne_zero ht]
      field_simp
  rw [sinc_id (m*z), sinc_id ((m-M)*z)]
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hv : 0 < (M-m)*z := mul_pos (sub_pos.mpr hlt) hz
    have hcomp := sinc_mul_gt hmp hv (by nlinarith)
    have he : m*z+(M-m)*z=M*z := by ring
    rw [he] at hcomp
    have he' : (m-M)*z = -((M-m)*z) := by ring
    rw [he', Real.sinc_neg]
    have hw : z^2*m*(m-M) < 0 :=
      mul_neg_of_pos_of_neg (mul_pos (sq_pos_of_pos hz) hm) (sub_neg.mpr hlt)
    have h := mul_lt_mul_of_neg_left hcomp hw
    nlinarith [h]
  · have hd : 0 < (m-M)*z := mul_pos (sub_pos.mpr hgt) hz
    have hcmp : Real.sinc (m*z) < Real.sinc (M*z) :=
      strictAntiOn_sinc ⟨hMp.le, hmean.le⟩ ⟨hmp.le,hangle⟩ (by nlinarith)
    have hsin : 0 ≤ Real.sinc (m*z) := by
      rw [Real.sinc_of_ne_zero (ne_of_gt hmp)]
      exact div_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hmp.le hangle) hmp.le
    have hprod : Real.sinc (m*z)*Real.sinc ((m-M)*z) < Real.sinc (M*z) := by
      calc
        _ ≤ Real.sinc (m*z)*1 := mul_le_mul_of_nonneg_left (Real.sinc_le_one _) hsin
        _ < _ := by simpa using hcmp
    have hw : 0 < z^2*m*(m-M) :=
      mul_pos (mul_pos (sq_pos_of_pos hz) hm) (sub_pos.mpr hgt)
    have h := mul_lt_mul_of_pos_left hprod hw
    nlinarith [h]

/-- Balanced weighted sums are strictly negative unless every m_i=M. -/
theorem weighted_sine_sum {ι : Type*} (s : Finset ι) (m : ι → ℝ)
    (M z : ℝ) (hp : ∀ i∈s, 0<m i) (hM : 0<M) (hz : 0<z)
    (hangle : ∀ i∈s, m i*z≤Real.pi) (hmean : M*z<Real.pi)
    (hbalance : ∑ i∈s, m i*(m i-M)=0) (hvar : ∃ i∈s, m i ≠ M) :
    (∑ i∈s, Real.sin (m i*z)*Real.sin ((m i-M)*z)) < 0 := by
  have hle (i) (hi : i∈s) :
      Real.sin (m i*z)*Real.sin ((m i-M)*z) ≤
        (z^2*Real.sinc (M*z))*(m i*(m i-M)) := by
    by_cases he : m i=M
    · simp [he]
    · have h := sine_product_lt (hp i hi) hM hz (hangle i hi) hmean he
      nlinarith [h]
  obtain ⟨i,hi,hne⟩ := hvar
  have hstrict : Real.sin (m i*z)*Real.sin ((m i-M)*z) <
      (z^2*Real.sinc (M*z))*(m i*(m i-M)) := by
    have h := sine_product_lt (hp i hi) hM hz (hangle i hi) hmean hne
    nlinarith [h]
  have hh := Finset.sum_lt_sum hle ⟨i,hi,hstrict⟩
  rw [← Finset.mul_sum, hbalance, mul_zero] at hh
  exact hh

#print axioms finite_sine_sum
#print axioms sine_product_lt
#print axioms weighted_sine_sum
end Carnevale
```

### `StrictSineList.lean`

```lean
import SineSum
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.Positivity

namespace Carnevale

/-- Uniform finite-index version of the new strict sine-sum lemma. -/
theorem strict_sine_sum_finset {ι : Type*} (s : Finset ι) (m : ι → ℕ)
    (hne : s.Nonempty) (hp : ∀ i∈s, 0<m i)
    (hvar : ¬∃ n : ℕ, ∀ i∈s, m i=n) (z : ℝ) (hz : 0<z)
    (hangle : ∀ i∈s, (m i:ℝ)*z≤Real.pi) :
    let M := (∑ i∈s, (m i:ℝ)^2)/(∑ i∈s, (m i:ℝ));
    (∑ i∈s, ∑ k ∈ Finset.range (m i),
      Real.sin (2*z*((k+1:ℝ)-(M+1)/2))) < 0 := by
  classical
  let M := (∑ i∈s, (m i:ℝ)^2)/(∑ i∈s, (m i:ℝ))
  change (∑ i∈s, ∑ k ∈ Finset.range (m i),
    Real.sin (2*z*((k+1:ℝ)-(M+1)/2))) < 0
  obtain ⟨i,hi⟩ := hne
  have hpos (j) (hj : j∈s) : (0:ℝ)<m j := by exact_mod_cast hp j hj
  have hN : 0 < ∑ j∈s, (m j:ℝ) :=
    Finset.sum_pos' (fun j hj => (hpos j hj).le) ⟨i,hi,hpos i hi⟩
  have hS : 0 < ∑ j∈s, (m j:ℝ)^2 :=
    Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨i,hi,sq_pos_of_pos (hpos i hi)⟩
  have hM : 0<M := div_pos hS hN
  have hbalance : ∑ j∈s, (m j:ℝ)*((m j:ℝ)-M)=0 := by
    simp_rw [mul_sub, ← sq]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
    dsimp [M]
    field_simp
    ring
  have hmvar : ∃ j∈s, (m j:ℝ) ≠ M := by
    by_contra! hh
    apply hvar
    refine ⟨m i, fun j hj => ?_⟩
    exact_mod_cast (hh j hj).trans (hh i hi).symm
  have hmean : M*z<Real.pi := by
    by_contra! hh
    have hle (j) (hj : j∈s) : (m j:ℝ)≤M := by
      nlinarith [hangle j hj]
    have hnonpos (j) (hj : j∈s) : (m j:ℝ)*((m j:ℝ)-M)≤0 :=
      mul_nonpos_of_nonneg_of_nonpos (hpos j hj).le (sub_nonpos.mpr (hle j hj))
    obtain ⟨j,hj,hjM⟩ := hmvar
    have hstrict : (m j:ℝ)*((m j:ℝ)-M)<0 :=
      mul_neg_of_pos_of_neg (hpos j hj) (sub_neg.mpr (lt_of_le_of_ne (hle j hj) hjM))
    have hh' := Finset.sum_lt_sum hnonpos ⟨j,hj,hstrict⟩
    simp [hbalance] at hh'
  have hex : ∃ j∈s, 2≤m j := by
    by_contra! hh
    apply hvar
    exact ⟨1, fun j hj => by have := hp j hj; have := hh j hj; omega⟩
  obtain ⟨j,hj,hj2⟩ := hex
  have h2 : (2:ℝ)≤m j := by exact_mod_cast hj2
  have hzpi : z<Real.pi := by nlinarith [hangle j hj, Real.pi_pos]
  have hsin : 0<Real.sin z := Real.sin_pos_of_pos_of_lt_pi hz hzpi
  simp_rw [finite_sine_sum _ z M (ne_of_gt hsin)]
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  rw [← div_eq_mul_inv]
  apply div_neg_of_neg_of_pos _ hsin
  exact weighted_sine_sum s (fun i => (m i:ℝ)) M z hpos hM hz hangle hmean hbalance hmvar

/-- Literal list form, including a part attaining the angle bound. -/
theorem strict_sine_sum (ms : List ℕ) (hp : ∀ m∈ms, 0<m)
    (hne : ms ≠ []) (hvar : ¬∃m : ℕ, ∀n∈ms, n=m)
    (z : ℝ) (hz : 0<z) (hangle : ∀m∈ms, (m:ℝ)*z≤Real.pi) :
    let M := ((ms.map (fun m : ℕ => (m:ℝ)^2)).sum)/(ms.sum:ℝ);
    (ms.map (fun m => ∑ s ∈ Finset.range m,
      Real.sin (2*z*((s+1:ℝ)-(M+1)/2)))).sum < 0 := by
  have hlen : 0<ms.length := List.length_pos_iff.mpr hne
  have hn : (Finset.univ : Finset (Fin ms.length)).Nonempty :=
    ⟨⟨0,hlen⟩, Finset.mem_univ _⟩
  have hv : ¬∃n : ℕ, ∀i ∈ (Finset.univ : Finset (Fin ms.length)), ms.get i=n := by
    rintro ⟨n,hh⟩
    apply hvar
    exact ⟨n, List.forall_mem_iff_get.mpr (fun i => hh i (Finset.mem_univ _))⟩
  have h := strict_sine_sum_finset Finset.univ ms.get hn
    (fun i _ => hp _ (List.get_mem ms i)) hv z hz
    (fun i _ => hangle _ (List.get_mem ms i))
  have hs (f : ℕ → ℝ) : (∑ i : Fin ms.length, f (ms.get i)) = (ms.map f).sum := by
    simpa only [List.sum_ofFn, List.get_eq_getElem] using congrArg List.sum (List.ofFn_getElem_eq_map ms f)
  have hN : (∑ i : Fin ms.length, (ms.get i:ℝ)) = (ms.sum:ℝ) := by
    rw [hs]
    simp
  dsimp only at h ⊢
  rw [hN, hs (fun m : ℕ => (m:ℝ)^2)] at h
  rw [hs (fun m => ∑ k ∈ Finset.range m,
    Real.sin (2*z*((k+1:ℝ)-(((ms.map (fun m : ℕ => (m:ℝ)^2)).sum)/(ms.sum:ℝ)+1)/2)))] at h
  simpa only [List.map_map, Function.comp_def] using h

#print axioms strict_sine_sum_finset
#print axioms strict_sine_sum
end Carnevale
```

### `BinomialUnitary.lean`

```lean
import SourceDefinitions

namespace Carnevale

/-- Every printed candidate factor satisfies the literal complex-root predicate. -/
theorem binomial_isUnitary (a : ℕ) : IsUnitary (1+x^a*y) := by
  refine ⟨?_, 1+Polynomial.X, a, 1, ?_, ?_⟩
  · rintro ⟨cc,hc⟩
    have h0 := congrArg (MvPolynomial.eval (fun _ : Fin 2 => (0:ℤ))) hc
    have h1 := congrArg (MvPolynomial.eval (fun _ : Fin 2 => (1:ℤ))) hc
    simp [x,y] at h0 h1
    omega
  · simp
  · intro z hz
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_one, Polynomial.eval₂_X] at hz
    have he : z=(-1:ℂ) := (eq_neg_iff_add_eq_zero).mpr (by simpa [add_comm] using hz)
    simp [he]

#print axioms binomial_isUnitary
end Carnevale
```

### `Blueprint.lean`

```lean
import ModelFoundation
import StrictSineList
import BinomialUnitary
import PolePrototype

/-! Typed open proof obligations. Every declaration here is a proposition
DEFINITION, not a theorem asserting the proposition. None is assumed by E2. -/
namespace Carnevale.Blueprint
noncomputable section
open Carnevale

-- Group 2

def M0 : Prop := q ≠ 0 ∧ ∀ η : List ℕ, E η ≠ 0 ∧
  ∀ j a : ℕ, 1+q^((j:ℤ)-(a:ℤ)) ≠ 0

def M1 : Prop := ∀ m k : ℕ, PowerSeries.coeff k (inverseDenominator m) = qGaussian (k+m) m

def M2 : Prop := SourceFormula10 → ∀ η : List ℕ, η ≠ [] → (∀ m∈η, 0<m) →
  ∀ t : K, (∀ j ∈ Finset.range (η.sum+1), 1-t*q^j ≠ 0) →
    (A η).eval t / (∏ j ∈ Finset.range (η.sum+1), (1-t*q^j)) = R η t / E η

def M3 : Prop := SourceFormula10 → ∀ η : List ℕ, η ≠ [] → (∀ m∈η, 0<m) →
  ∀ a : ℕ, (A η).eval (-q^(-(a:ℤ))) = 0 ↔ L η a = 0

def M4 : Prop := ∀ η : List ℕ, 2≤η.sum → Even η.sum →
  c η 0=1 ∧ c η η.sum=q^(weight η) ∧ c η 1= -levelSum η q ∧
    c η (η.sum-1)= -q^(weight η)*levelSum η q⁻¹

def M5 : Prop := SourceFormula10 → ∀ η : List ℕ, η ≠ [] → (∀ m∈η, 0<m) →
  ∀ t : K, (A η).eval t = (AInverseQ η).eval (t*q^η.sum)

def M6 : Prop := SourceFormula10 → ∀ η : List ℕ, η ≠ [] → (∀ m∈η, 0<m) →
  specializeYZero (denertPoly η)=1 ∧ specializeXZero (denertPoly η)=1

-- Group 3 (depends on group 6)

def U1 : Prop := SourceFormula10 → ∀ η : List ℕ, η ≠ [] → (∀ m∈η, 0<m) →
  ∀ f : Bivar, IsUnitary f → f ∣ denertPoly η →
    ∃ a : ℕ, 0<a ∧ (f=1+x^a*y ∨ f= -(1+x^a*y))

def U2 : Prop := SourceFormula10 → ∀ η : List ℕ, η ≠ [] → (∀ m∈η, 0<m) →
  ∀ a b : ℕ, (1+x^a*y) ∣ denertPoly η → (1+x^b*y) ∣ denertPoly η → a=b

def U3 : Prop := SourceFormula10 → ∀ η : List ℕ, η ≠ [] → (∀ m∈η, 0<m) →
  ∀ a : ℕ, ¬ (1+x^a*y)^2 ∣ denertPoly η

-- Group 4; P1 is the four actual theorems in PolePrototype.

def P2 : Prop := SourceFormula10 → ∀ η : List ℕ, η ≠ [] → (∀ m∈η, 0<m) →
  ∀ a : ℕ, 0<a → L η a=0 → η.sum=2*a

def P3 : Prop := ∀ (η : List ℕ) (a : ℕ), 0<a → η.sum=2*a →
  L η a=0 → η.sum ∣ weight η

def P4 : Prop := ∀ (η : List ℕ) (a : ℕ), 2≤a → η.sum=2*a → L η a=0 →
  let ξ : ℂ := Complex.exp (2*Real.pi*Complex.I/(η.sum-2 : ℕ));
  levelSum η ξ = ξ^(weight η)*levelSum η ξ⁻¹

-- P5 needs evenness explicitly; hL at floor(N/2) is insufficient for odd N.
def P5 : Prop := ∀ η : List ℕ, 4≤η.sum → Even η.sum → η.sum ∣ weight η →
  L η (η.sum/2)=0 →
  (η.map (fun m => ∑ s ∈ Finset.range m,
    Real.sin (2*Real.pi*((s+1:ℝ)-(weight η:ℝ)/(η.sum:ℝ))/((η.sum:ℝ)-2)))).sum=0

-- Group 5; T1--T4 are already theorems. T5 is the list form of weighted_sine_sum.
def T5 : Prop := ∀ ms : List ℕ, (∀ m∈ms, 0<m) → ms ≠ [] →
  (¬∃m : ℕ, ∀n∈ms, n=m) → ∀ z : ℝ, 0<z →
  (∀m∈ms, (m:ℝ)*z≤Real.pi) →
  let M := ((ms.map (fun m : ℕ => (m:ℝ)^2)).sum)/(ms.sum:ℝ);
  (ms.map (fun m => ∑ s ∈ Finset.range m,
    Real.sin (2*z*((s+1:ℝ)-(M+1)/2)))).sum < 0

def T6 : Prop := SourceFormula10 → ∀ η : List ℕ, η ≠ [] → (∀ m∈η, 0<m) →
  ∀ a : ℕ, 0<a → L η a=0 →
  ∃m r : ℕ, 0<m ∧ 0<r ∧ η=List.replicate r m ∧ Odd m ∧ Even r

-- Group 6

def S2 : Prop := ∀ (W : Polynomial ℝ) (d : ℕ) (cc : ℝ),
  SimpleNegative W → 0<W.coeff 0 → 0<cc → W.natDegree≤d →
  cc≤(d+1:ℝ)-W.natDegree → SimpleNegative (T d cc W) ∧ 0<(T d cc W).coeff 0

def S3 : Prop := ∀ (d : ℕ) (cc : ℝ) (P W : Polynomial ℝ),
  eulerSeries d P=(W : PowerSeries ℝ) →
  eulerSeries (d+1) ((Polynomial.X+Polynomial.C cc)*P) = (T d cc W : PowerSeries ℝ)

def S4 : Prop := SourceFormula10 → ∀ η : List ℕ, η ≠ [] → (∀ m∈η, 0<m) →
  SimpleNegative (specializeXOneReal (denertPoly η)) ∧
    0<(specializeXOneReal (denertPoly η)).coeff 0

-- Group 7

def R1 : Prop := SourceFormula10 → ∀ m r : ℕ, 0<m → 0<r →
  rectangleReciprocity (List.replicate r m) (m*r) (m*(r-1))

def R2 : Prop := SourceFormula10 → ∀ m r : ℕ, 0<m → 0<r → Odd m → Even r →
  (A (List.replicate r m)).eval (-q^(-((m*r/2:ℕ):ℤ)))=0

def R3 : Prop := ∀ (P : Bivar) (a : ℕ),
  (bivarToK P).eval (-q^(-(a:ℤ)))=0 → (1+x^a*y) ∣ P

def R4 : Prop := SourceFormula10 → ∀ m r : ℕ, 0<m → 0<r → Odd m → Even r →
  ∃f0 : Bivar, denertPoly (List.replicate r m)=rectangleFactor (m*r)*f0 ∧
    ¬HasUnitaryFactor f0

def R5 : Prop := ∀ a : ℕ, IsUnitary (1+x^a*y)

-- Group 8. No proof of this proposition is present.
def F1 : Prop := SourceFormula10 → Conjecture23

/-- Completed obligations, not assumptions. -/
theorem M0_proved : M0 :=
  ⟨q_ne_zero, fun η => ⟨E_ne_zero η, slope_denominator_ne_zero⟩⟩
theorem T5_proved : T5 := strict_sine_sum
theorem R5_proved : R5 := binomial_isUnitary

end
end Carnevale.Blueprint
```

### `Audit.lean`

```lean
import LiteralFoundation
import Blueprint
import ModelFoundation

#eval Lean.versionString

#check Carnevale.den_source_example
#print axioms Carnevale.den_source_example
#check Carnevale.source_example_subwords
#print axioms Carnevale.source_example_subwords
#check Carnevale.polynomial_singleton_one
#print axioms Carnevale.polynomial_singleton_one
#check Carnevale.polynomial_singleton_two
#print axioms Carnevale.polynomial_singleton_two
#check Carnevale.polynomial_two_letters
#print axioms Carnevale.polynomial_two_letters
#check Carnevale.denominator_constant
#print axioms Carnevale.denominator_constant
#check Carnevale.denominator_inverse
#print axioms Carnevale.denominator_inverse
#check Carnevale.hadamard_singleton
#print axioms Carnevale.hadamard_singleton
#check Carnevale.formula_singleton_one
#print axioms Carnevale.formula_singleton_one
#check Carnevale.formula_singleton_two
#print axioms Carnevale.formula_singleton_two
#check Carnevale.mem_multisetPerms
#print axioms Carnevale.mem_multisetPerms
#check Carnevale.baseFrom_length
#print axioms Carnevale.baseFrom_length
#check Carnevale.baseWord_length
#print axioms Carnevale.baseWord_length
#check Carnevale.word_length
#print axioms Carnevale.word_length
#check Carnevale.baseWord_mem
#print axioms Carnevale.baseWord_mem
#check Carnevale.negative_exponent_denominator
#print axioms Carnevale.negative_exponent_denominator
#check Carnevale.negative_exponent_zero_iff
#print axioms Carnevale.negative_exponent_zero_iff
#check Carnevale.cleared_pole_numerator
#print axioms Carnevale.cleared_pole_numerator
#check Carnevale.isolated_pole_impossible
#print axioms Carnevale.isolated_pole_impossible
#check Carnevale.fraction_identity_clears
#print axioms Carnevale.fraction_identity_clears
#check Carnevale.primitive_four_denominators
#print axioms Carnevale.primitive_four_denominators
#check Carnevale.second_pole_four_denominators
#print axioms Carnevale.second_pole_four_denominators
#check Carnevale.q_ne_zero
#print axioms Carnevale.q_ne_zero
#check Carnevale.power_add_power_ne_zero
#print axioms Carnevale.power_add_power_ne_zero
#check Carnevale.slope_denominator_ne_zero
#print axioms Carnevale.slope_denominator_ne_zero
#check Carnevale.one_sub_q_power_ne_zero
#print axioms Carnevale.one_sub_q_power_ne_zero
#check Carnevale.E_ne_zero
#print axioms Carnevale.E_ne_zero
#check Carnevale.sin_sub_mul_cos_pos
#print axioms Carnevale.sin_sub_mul_cos_pos
#check Carnevale.strictAntiOn_sinc
#print axioms Carnevale.strictAntiOn_sinc
#check Carnevale.sinc_mul_gt
#print axioms Carnevale.sinc_mul_gt
#check Carnevale.finite_sine_sum
#print axioms Carnevale.finite_sine_sum
#check Carnevale.sine_product_lt
#print axioms Carnevale.sine_product_lt
#check Carnevale.weighted_sine_sum
#print axioms Carnevale.weighted_sine_sum
#check Carnevale.strict_sine_sum_finset
#print axioms Carnevale.strict_sine_sum_finset
#check Carnevale.strict_sine_sum
#print axioms Carnevale.strict_sine_sum
#check Carnevale.binomial_isUnitary
#print axioms Carnevale.binomial_isUnitary
#check Carnevale.Blueprint.M0_proved
#print axioms Carnevale.Blueprint.M0_proved
#check Carnevale.Blueprint.T5_proved
#print axioms Carnevale.Blueprint.T5_proved
#check Carnevale.Blueprint.R5_proved
#print axioms Carnevale.Blueprint.R5_proved

#print Carnevale.E2Endpoint
#print Carnevale.Conjecture23
#print Carnevale.SourceFormula10
#print Carnevale.SourceFormula10At
#print axioms Carnevale.denertPoly
#print axioms Carnevale.IsUnitary
```

### `GaussianProducts.lean`

```lean
import ModelFoundation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace Carnevale
noncomputable section
open Finset

/-- The numerator and denominator of the Gaussian product in the field ℚ(q). -/
def gaussianNumerator (m k : ℕ) : K :=
  ∏ s ∈ range m, (1-q^(k+s+1))
def gaussianDenominator (m : ℕ) : K := gaussianNumerator m 0
def gaussianProduct (m k : ℕ) : K := gaussianNumerator m k / gaussianDenominator m

theorem gaussianDenominator_ne_zero (m : ℕ) : gaussianDenominator m ≠ 0 := by
  unfold gaussianDenominator gaussianNumerator
  apply Finset.prod_ne_zero_iff.mpr
  intro s _
  exact one_sub_q_power_ne_zero (0+s+1) (by omega)

theorem gaussianNumerator_succ (m k : ℕ) :
    gaussianNumerator (m+1) k = gaussianNumerator m k * (1-q^(k+m+1)) := by
  exact prod_range_succ _ _

theorem gaussianNumerator_shift (m k : ℕ) :
    gaussianNumerator (m+1) k = (1-q^(k+1))*gaussianNumerator m (k+1) := by
  unfold gaussianNumerator
  rw [prod_range_succ']
  simp only [Nat.add_zero]
  rw [mul_comm]
  congr 1
  apply prod_congr rfl
  intro s _
  congr 2
  omega

theorem gaussianProduct_zero (m : ℕ) : gaussianProduct m 0 = 1 := by
  exact div_self (gaussianDenominator_ne_zero m)

theorem gaussianProduct_zero_left (k : ℕ) : gaussianProduct 0 k = 1 := by
  simp [gaussianProduct, gaussianNumerator, gaussianDenominator]

/-- Pascal recursion in the variables (block size, series coefficient). -/
theorem gaussianProduct_pascal (m k : ℕ) :
    gaussianProduct (m+1) (k+1) =
      gaussianProduct m (k+1) + q^(m+1)*gaussianProduct (m+1) k := by
  have hd := gaussianDenominator_ne_zero m
  have hq := one_sub_q_power_ne_zero (m+1) (by omega)
  unfold gaussianProduct
  rw [show gaussianDenominator (m+1) = gaussianDenominator m * (1-q^(m+1)) by
    simpa [gaussianDenominator] using gaussianNumerator_succ m 0]
  rw [gaussianNumerator_succ m (k+1), gaussianNumerator_shift m k]
  field_simp
  rw [show k+1+m+1 = (m+1)+(k+1) by omega, pow_add]
  ring

end
end Carnevale
```

### `FieldSeries.lean`

```lean
import GaussianProducts
import SourceTests

namespace Carnevale
noncomputable section
open Finset

def qCoeffHom : Polynomial ℤ →+* K := Polynomial.eval₂RingHom (Int.castRingHom K) q
def fieldSeries : Series →+* PowerSeries K := PowerSeries.map qCoeffHom
def fieldDenominator (m : ℕ) : PowerSeries K := fieldSeries (denominator m)
def fieldInverse (m : ℕ) : PowerSeries K := fieldSeries (inverseDenominator m)

@[simp] theorem qCoeffHom_X : qCoeffHom Polynomial.X = q := by simp [qCoeffHom]

 theorem fieldDenominator_eq (m : ℕ) : fieldDenominator m =
    ∏ j ∈ range (m+1), (1-PowerSeries.C (q^j)*PowerSeries.X) := by
  simp [fieldDenominator, denominator, fieldSeries, PowerSeries.map_C,
    PowerSeries.map_X]

 theorem fieldDenominator_inverse (m : ℕ) : fieldDenominator m * fieldInverse m = 1 := by
  rw [fieldDenominator, fieldInverse, ← map_mul, denominator_inverse, map_one]

 theorem fieldDenominator_succ (m : ℕ) : fieldDenominator (m+1) =
    fieldDenominator m * (1-PowerSeries.C (q^(m+1))*PowerSeries.X) := by
  simp only [fieldDenominator_eq, prod_range_succ]

 theorem fieldInverse_step (m : ℕ) :
    (1-PowerSeries.C (q^(m+1))*PowerSeries.X)*fieldInverse (m+1) = fieldInverse m := by
  have h := fieldDenominator_inverse (m+1)
  rw [fieldDenominator_succ] at h
  calc
    _ = (fieldDenominator m * fieldInverse m) *
      ((1-PowerSeries.C (q^(m+1))*PowerSeries.X)*fieldInverse (m+1)) := by
        rw [fieldDenominator_inverse, one_mul]
    _ = fieldInverse m * (fieldDenominator m *
      (1-PowerSeries.C (q^(m+1))*PowerSeries.X)*fieldInverse (m+1)) := by ring
    _ = fieldInverse m := by rw [h, mul_one]

 theorem coeff_linear_mul_succ (r : K) (S : PowerSeries K) (k : ℕ) :
    PowerSeries.coeff (k+1) ((1-PowerSeries.C r*PowerSeries.X)*S) =
      PowerSeries.coeff (k+1) S - r*PowerSeries.coeff k S := by
  rw [sub_mul, one_mul, mul_assoc, map_sub, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_succ_X_mul]

 theorem fieldInverse_constant (m : ℕ) : PowerSeries.coeff 0 (fieldInverse m) = 1 := by
  have h := congrArg PowerSeries.constantCoeff (fieldDenominator_inverse m)
  simpa [fieldDenominator_eq] using h

 theorem fieldInverse_coeff (m k : ℕ) :
    PowerSeries.coeff k (fieldInverse m) = gaussianProduct m k := by
  induction m generalizing k with
  | zero =>
    have h := fieldDenominator_inverse 0
    simp [fieldDenominator_eq] at h
    induction k with
    | zero => rw [fieldInverse_constant, gaussianProduct_zero_left]
    | succ k ih =>
      have he := congrArg (PowerSeries.coeff (k+1)) h
      simp only [sub_mul, one_mul, map_sub, PowerSeries.coeff_succ_X_mul] at he
      simp only [PowerSeries.coeff_one, Nat.add_eq_zero_iff, one_ne_zero, and_false,
        ↓reduceIte] at he
      rw [gaussianProduct_zero_left] at ih ⊢
      exact (sub_eq_zero.mp he).trans ih
  | succ m ih =>
    induction k with
    | zero => rw [fieldInverse_constant, gaussianProduct_zero]
    | succ k ikh =>
      have he := congrArg (PowerSeries.coeff (k+1)) (fieldInverse_step m)
      rw [coeff_linear_mul_succ, ih, ikh] at he
      rw [gaussianProduct_pascal]
      exact sub_eq_iff_eq_add.mp he

end
end Carnevale
```

### `IntegralGaussian.lean`

```lean
import FieldSeries

namespace Carnevale
noncomputable section

 theorem qGaussian_above (n k : ℕ) (h : n<k) : qGaussian n k = 0 := by
  induction n generalizing k with
  | zero => cases k with
    | zero => omega
    | succ k => rfl
  | succ n ih => cases k with
    | zero => omega
    | succ k => simp [qGaussian, ih (k+1) (by omega), ih k (by omega)]

 theorem qGaussian_diagonal (m : ℕ) : qGaussian m m = 1 := by
  induction m with
  | zero => rfl
  | succ m ih => simp [qGaussian, qGaussian_above m (m+1) (by omega), ih]

 theorem gaussianProduct_pascal_alt (m k : ℕ) :
    gaussianProduct (m+1) (k+1) =
      gaussianProduct (m+1) k + q^(k+1)*gaussianProduct m (k+1) := by
  have hd := gaussianDenominator_ne_zero m
  have hq := one_sub_q_power_ne_zero (m+1) (by omega)
  unfold gaussianProduct
  rw [show gaussianDenominator (m+1) = gaussianDenominator m * (1-q^(m+1)) by
    simpa [gaussianDenominator] using gaussianNumerator_succ m 0]
  rw [gaussianNumerator_succ m (k+1), gaussianNumerator_shift m k]
  field_simp
  rw [show k+1+m+1 = (k+1)+(m+1) by omega, pow_add]
  ring

 theorem qGaussian_product (m k : ℕ) :
    qCoeffHom (qGaussian (k+m) m) = gaussianProduct m k := by
  induction m generalizing k with
  | zero => cases k <;> simp [qGaussian, gaussianProduct_zero_left]
  | succ m ih =>
    induction k with
    | zero => simp [qGaussian_diagonal, gaussianProduct_zero]
    | succ k ikh =>
      rw [show k+1+(m+1) = (k+(m+1))+1 by omega, qGaussian]
      simp only [map_add, map_mul, map_pow, qCoeffHom_X]
      rw [show k+(m+1)-m = k+1 by omega, show k+(m+1) = (k+1)+m by omega,
        ih, ← show k+(m+1) = (k+1)+m by omega, ikh, gaussianProduct_pascal_alt]

 theorem qCoeffHom_injective : Function.Injective qCoeffHom := by
  have he : qCoeffHom = (algebraMap (Polynomial ℚ) K).comp
      (Polynomial.mapRingHom (Int.castRingHom ℚ)) := by
    ext <;> simp [qCoeffHom, q, RatFunc.algebraMap_X]
  rw [he]
  exact (RatFunc.algebraMap_injective ℚ).comp
    (Polynomial.map_injective (Int.castRingHom ℚ) (Int.cast_injective (α := ℚ)))

 theorem inverseDenominator_coeff (m k : ℕ) :
    PowerSeries.coeff k (inverseDenominator m) = qGaussian (k+m) m := by
  apply qCoeffHom_injective
  exact (fieldInverse_coeff m k).trans (qGaussian_product m k).symm

end
end Carnevale
```

### `BlockProducts.lean`

```lean
import FieldSeries
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Tactic.FinCases

namespace Carnevale
noncomputable section
open Finset

def denominatorPoly (n : ℕ) : Polynomial K :=
  ∏ j ∈ range (n+1), (1-Polynomial.C (q^j)*Polynomial.X)
def puncturedDenominator (n j : ℕ) : Polynomial K :=
  ∏ i ∈ (range (n+1)).erase j, (1-Polynomial.C (q^i)*Polynomial.X)

theorem denominatorPoly_series (n : ℕ) :
    (denominatorPoly n : PowerSeries K) = fieldDenominator n := by
  rw [fieldDenominator_eq]
  change Polynomial.coeToPowerSeries.ringHom (denominatorPoly n) = _
  simp only [denominatorPoly, map_prod, map_sub, map_one, map_mul,
    Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C, Polynomial.coe_X]

theorem denominatorPoly_erase (n j : ℕ) (hj : j ∈ range (n+1)) :
    (1-Polynomial.C (q^j)*Polynomial.X)*puncturedDenominator n j = denominatorPoly n := by
  exact Finset.mul_prod_erase (range (n+1))
    (fun i : ℕ => (1-Polynomial.C (q^i)*Polynomial.X : Polynomial K)) hj

theorem block_degree (η : List ℕ) : (block η).natDegree ≤ η.sum := by
  have hpart (m : ℕ) : (∏ s ∈ range m,
      (1-Polynomial.C (q^(s+1))*Polynomial.X)).natDegree ≤ m := by
    apply (Polynomial.natDegree_prod_le _ _).trans
    calc
      _ ≤ ∑ _s ∈ range m, 1 := by
        apply sum_le_sum
        intro s _
        exact (Polynomial.natDegree_sub_le _ _).trans
          (max_le (by simp) (by
            apply Polynomial.natDegree_mul_le |>.trans
            simp))
      _ = m := by simp
  induction η with
  | nil => simp [block]
  | cons m ms ih =>
    simp only [block, List.map_cons, List.prod_cons, List.sum_cons] at *
    exact (Polynomial.natDegree_mul_le).trans (Nat.add_le_add (hpart m) ih)

theorem block_eval (η : List ℕ) (k : ℕ) :
    (block η).eval (q^k) = (η.map (fun m => gaussianNumerator m k)).prod := by
  induction η with
  | nil => simp [block]
  | cons m ms ih =>
    simp only [block, List.map_cons, List.prod_cons, Polynomial.eval_mul] at *
    rw [Polynomial.eval_prod, ih]
    congr 1
    apply prod_congr rfl
    intro s _
    simp only [Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X, pow_add]
    ring

theorem E_product (η : List ℕ) : E η = (η.map gaussianDenominator).prod := by
  change (block η).eval 1 = (η.map (fun m => gaussianNumerator m 0)).prod
  simpa only [pow_zero] using block_eval η 0

theorem gaussian_product_list (η : List ℕ) (k : ℕ) :
    (η.map (fun m => gaussianProduct m k)).prod = (block η).eval (q^k) / E η := by
  rw [block_eval, E_product]
  induction η with
  | nil => simp
  | cons m ms ih =>
    simpa only [List.map_cons, List.prod_cons, gaussianProduct, mul_div_mul_comm] using
      congrArg (fun z => gaussianProduct m k * z) ih

theorem field_hadamard_coeff (η : List ℕ) (k : ℕ) :
    PowerSeries.coeff k (fieldSeries (hadamard (η.map inverseDenominator))) =
      (block η).eval (q^k) / E η := by
  rw [← gaussian_product_list]
  change qCoeffHom (PowerSeries.coeff k (hadamard (η.map inverseDenominator))) = _
  simp only [hadamard, PowerSeries.coeff_mk, List.map_map]
  induction η with
  | nil => simp
  | cons m ms ih =>
    simp only [List.map_cons, List.prod_cons, map_mul, Function.comp_apply]
    rw [show qCoeffHom (PowerSeries.coeff k (inverseDenominator m)) =
      gaussianProduct m k by exact fieldInverse_coeff m k, ih]

end
end Carnevale
```

### `RationalNumerator.lean`

```lean
import BlockProducts

namespace Carnevale
noncomputable section
open Finset

theorem bivar_series_compat (P : Bivar) :
    (bivarToK P : PowerSeries K) = fieldSeries (seriesOfBivar P) := by
  have hh : Polynomial.coeToPowerSeries.ringHom.comp bivarToK =
      fieldSeries.comp seriesOfBivar := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [bivarToK, seriesOfBivar, fieldSeries]
    · intro i
      fin_cases i <;> simp [bivarToK, seriesOfBivar, fieldSeries,
        PowerSeries.map_C, PowerSeries.map_X]
  exact DFunLike.congr_fun hh P

/-- Geometric series are used only formally. -/
def geometric (z : K) : PowerSeries K := PowerSeries.mk (fun k => z^k)

theorem geometric_inverse (z : K) :
    (1-PowerSeries.C z*PowerSeries.X)*geometric z = 1 := by
  ext k
  cases k with
  | zero => simp [geometric]
  | succ k =>
    rw [coeff_linear_mul_succ]
    simp [geometric, pow_succ, mul_comm]

theorem denominator_geometric (n j : ℕ) (hj : j ∈ range (n+1)) :
    (denominatorPoly n : PowerSeries K)*geometric (q^j) =
      (puncturedDenominator n j : PowerSeries K) := by
  rw [← denominatorPoly_erase n j hj, Polynomial.coe_mul]
  simp only [Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_mul,
    Polynomial.coe_C, Polynomial.coe_X]
  calc
    _ = (puncturedDenominator n j : PowerSeries K)*
      ((1-PowerSeries.C (q^j)*PowerSeries.X)*geometric (q^j)) := by ring
    _ = _ := by rw [geometric_inverse, mul_one]

/-- The numerator obtained after putting the finite partial fractions over a common denominator. -/
def rationalNumerator (η : List ℕ) : Polynomial K :=
  ∑ j ∈ range (η.sum+1), Polynomial.C (c η j / E η)*puncturedDenominator η.sum j

 theorem field_hadamard_eq (η : List ℕ) :
    fieldSeries (hadamard (η.map inverseDenominator)) =
      ∑ j ∈ range (η.sum+1), PowerSeries.C (c η j / E η)*geometric (q^j) := by
  ext k
  rw [field_hadamard_coeff]
  simp only [map_sum, PowerSeries.coeff_C_mul, geometric, PowerSeries.coeff_mk]
  rw [Polynomial.eval_eq_sum_range' (n := η.sum+1) (Nat.lt_succ_of_le (block_degree η)), sum_div]
  apply sum_congr rfl
  intro j _
  rw [c, ← pow_mul, ← pow_mul, Nat.mul_comm k j]
  ring

/-- The source formula determines the cleared rational numerator. -/
theorem formula_to_rational_cleared (H : SourceFormula10) (η : List ℕ)
    (hne : η ≠ []) (hp : ∀ m∈η, 0<m) : A η = rationalNumerator η := by
  apply Polynomial.coe_injective K
  have hh := congrArg fieldSeries (H η hne hp)
  change fieldSeries (seriesOfBivar (denertPoly η)) = _ at hh
  rw [← bivar_series_compat, map_mul, ← fieldDenominator, ← denominatorPoly_series, field_hadamard_eq,
    mul_sum] at hh
  rw [show (A η : PowerSeries K) =
      (bivarToK (denertPoly η) : PowerSeries K) from rfl, hh]
  change _ = Polynomial.coeToPowerSeries.ringHom (rationalNumerator η)
  rw [rationalNumerator, map_sum]
  simp only [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_mul, Polynomial.coe_C]
  apply sum_congr rfl
  intro j hj
  calc
    _ = PowerSeries.C (c η j / E η)*
        ((denominatorPoly η.sum : PowerSeries K)*geometric (q^j)) := by ring
    _ = _ := by rw [denominator_geometric _ _ hj]

/-- Finite partial fractions, derived from the literal published formal-series hypothesis. -/
theorem formula_to_rational (H : SourceFormula10) (η : List ℕ)
    (hne : η ≠ []) (hp : ∀ m∈η, 0<m) (t : K)
    (ht : ∀ j ∈ range (η.sum+1), 1-t*q^j ≠ 0) :
    (A η).eval t / (∏ j ∈ range (η.sum+1), (1-t*q^j)) = R η t / E η := by
  have hD : (∏ j ∈ range (η.sum+1), (1-t*q^j)) ≠ 0 := prod_ne_zero_iff.mpr ht
  apply (div_eq_div_iff hD (E_ne_zero η)).mpr
  rw [formula_to_rational_cleared H η hne hp]
  simp only [rationalNumerator, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, R, sum_mul]
  apply sum_congr rfl
  intro j hj
  have he := congrArg (Polynomial.eval t) (denominatorPoly_erase η.sum j hj)
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_one,
    Polynomial.eval_C, Polynomial.eval_X, denominatorPoly, Polynomial.eval_prod] at he
  simp_rw [mul_comm _ t] at he
  rw [← he]
  field_simp [E_ne_zero η, ht j hj]

 theorem slope_zero_iff (H : SourceFormula10) (η : List ℕ)
    (hne : η ≠ []) (hp : ∀ m∈η, 0<m) (a : ℕ) :
    (A η).eval (-q^(-(a:ℤ))) = 0 ↔ L η a = 0 := by
  have hd (j : ℕ) : 1-(-q^(-(a:ℤ)))*q^j = 1+q^((j:ℤ)-(a:ℤ)) := by
    rw [zpow_sub₀ q_ne_zero, zpow_natCast, zpow_natCast, zpow_neg, zpow_natCast]
    ring
  have hh := formula_to_rational H η hne hp (-q^(-(a:ℤ)))
    (fun j _ => by rw [hd]; exact slope_denominator_ne_zero j a)
  have hD : (∏ j ∈ range (η.sum+1), (1-(-q^(-(a:ℤ)))*q^j)) ≠ 0 := by
    apply prod_ne_zero_iff.mpr
    intro j _
    rw [hd]
    exact slope_denominator_ne_zero j a
  have hRL : R η (-q^(-(a:ℤ))) = L η a := by simp only [R, L, hd]
  rw [hRL] at hh
  have he := congrArg (fun z : K => z=0) hh
  simpa only [div_eq_zero_iff, hD, E_ne_zero η, or_false] using (eq_iff_iff.mp he)

end
end Carnevale
```

### `AxisSpecializations.lean`

```lean
import FieldSeries
import Mathlib.Tactic.FinCases

namespace Carnevale
noncomputable section

 theorem specializeYZero_series (P : Bivar) :
    specializeYZero P = PowerSeries.constantCoeff (seriesOfBivar P) := by
  have hh : MvPolynomial.eval₂Hom (Int.castRingHom (Polynomial ℤ))
      (fun i : Fin 2 => if i=0 then Polynomial.X else 0) =
      PowerSeries.constantCoeff.comp seriesOfBivar := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [seriesOfBivar]
    · intro i
      fin_cases i <;> simp [seriesOfBivar]
  exact DFunLike.congr_fun hh P

 theorem inverseDenominator_constant (m : ℕ) :
    PowerSeries.constantCoeff (inverseDenominator m) = 1 := by
  simp [inverseDenominator, PowerSeries.constantCoeff_invOfUnit]

 theorem y_axis_one (H : SourceFormula10) (η : List ℕ)
    (hne : η ≠ []) (hp : ∀ m∈η, 0<m) : specializeYZero (denertPoly η) = 1 := by
  rw [specializeYZero_series, H η hne hp, map_mul, denominator_constant, one_mul]
  simp [hadamard, PowerSeries.constantCoeff_mk, List.map_map,
    PowerSeries.coeff_zero_eq_constantCoeff, Function.comp_def, inverseDenominator_constant]

 def atZeroSeries : Series →+* PowerSeries ℤ := PowerSeries.map (Polynomial.evalRingHom 0)

 theorem denominator_at_zero (m : ℕ) : atZeroSeries (denominator m) = 1-PowerSeries.X := by
  simp only [atZeroSeries, denominator, map_prod, map_sub, map_one, map_mul,
    PowerSeries.map_C, PowerSeries.map_X]
  rw [Finset.prod_range_succ']
  simp

 theorem inverse_at_zero (m : ℕ) :
    atZeroSeries (inverseDenominator m) = PowerSeries.mk (fun _ => (1:ℤ)) := by
  have h := congrArg atZeroSeries (denominator_inverse m)
  rw [map_mul, map_one, denominator_at_zero] at h
  have hg : (1-PowerSeries.X)*PowerSeries.mk (fun _ => (1:ℤ)) = 1 := by
    rw [mul_comm]
    exact PowerSeries.mk_one_mul_one_sub_eq_one ℤ
  have hn : (1-PowerSeries.X : PowerSeries ℤ) ≠ 0 := by
    intro he
    have := congrArg PowerSeries.constantCoeff he
    simp at this
  exact mul_left_cancel₀ hn (h.trans hg.symm)

 theorem hadamard_at_zero (η : List ℕ) :
    atZeroSeries (hadamard (η.map inverseDenominator)) =
      PowerSeries.mk (fun _ => (1:ℤ)) := by
  ext k
  simp only [atZeroSeries, PowerSeries.coeff_map, hadamard, PowerSeries.coeff_mk,
    List.map_map]
  have he (m : ℕ) : Polynomial.eval 0 (PowerSeries.coeff k (inverseDenominator m)) = 1 := by
    have h := congrArg (PowerSeries.coeff k) (inverse_at_zero m)
    simpa [atZeroSeries] using h
  induction η with
  | nil => simp
  | cons m ms ih =>
    simp only [List.map_cons, List.prod_cons, map_mul, Function.comp_apply, ih]
    exact mul_one _ |>.trans (he m)

 theorem specializeXZero_series (P : Bivar) :
    (specializeXZero P : PowerSeries ℤ) = atZeroSeries (seriesOfBivar P) := by
  have hh : Polynomial.coeToPowerSeries.ringHom.comp
      (MvPolynomial.eval₂Hom (Int.castRingHom (Polynomial ℤ))
        (fun i : Fin 2 => if i=0 then 0 else Polynomial.X)) =
      atZeroSeries.comp seriesOfBivar := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [seriesOfBivar, atZeroSeries]
    · intro i
      fin_cases i <;> simp [seriesOfBivar, atZeroSeries]
  exact DFunLike.congr_fun hh P

 theorem x_axis_one (H : SourceFormula10) (η : List ℕ)
    (hne : η ≠ []) (hp : ∀ m∈η, 0<m) : specializeXZero (denertPoly η) = 1 := by
  apply Polynomial.coe_injective ℤ
  rw [specializeXZero_series, H η hne hp, map_mul, denominator_at_zero,
    hadamard_at_zero, mul_comm]
  rw [Polynomial.coe_one]
  exact PowerSeries.mk_one_mul_one_sub_eq_one ℤ

 theorem axes_one (H : SourceFormula10) (η : List ℕ)
    (hne : η ≠ []) (hp : ∀ m∈η, 0<m) :
    specializeYZero (denertPoly η)=1 ∧ specializeXZero (denertPoly η)=1 :=
  ⟨y_axis_one H η hne hp, x_axis_one H η hne hp⟩

end
end Carnevale
```

### `UnitReductionAxes.lean`

```lean
import AxisSpecializations
import Mathlib.Algebra.MvPolynomial.Nilpotent

namespace Carnevale
noncomputable section

 def killY : Bivar →+* Bivar :=
  MvPolynomial.eval₂Hom (Int.castRingHom Bivar) (fun i => if i=0 then x else 0)
 def killX : Bivar →+* Bivar :=
  MvPolynomial.eval₂Hom (Int.castRingHom Bivar) (fun i => if i=0 then 0 else y)

 theorem killY_eq (P : Bivar) : killY P =
    Polynomial.eval₂ (Int.castRingHom Bivar) x (specializeYZero P) := by
  have hh : killY = (Polynomial.eval₂RingHom (Int.castRingHom Bivar) x).comp
      (MvPolynomial.eval₂Hom (Int.castRingHom (Polynomial ℤ))
        (fun i : Fin 2 => if i=0 then Polynomial.X else 0)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [killY]
    · intro i
      fin_cases i <;> simp [killY, x]
  exact DFunLike.congr_fun hh P

 theorem killX_eq (P : Bivar) : killX P =
    Polynomial.eval₂ (Int.castRingHom Bivar) y (specializeXZero P) := by
  have hh : killX = (Polynomial.eval₂RingHom (Int.castRingHom Bivar) y).comp
      (MvPolynomial.eval₂Hom (Int.castRingHom (Polynomial ℤ))
        (fun i : Fin 2 => if i=0 then 0 else Polynomial.X)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [killX]
    · intro i
      fin_cases i <;> simp [killX, y]
  exact DFunLike.congr_fun hh P

 theorem map_int_eval₂ (f : Bivar →+* Bivar) (F : Polynomial ℤ) (z : Bivar) :
    f (F.eval₂ (Int.castRingHom Bivar) z) = F.eval₂ (Int.castRingHom Bivar) (f z) := by
  simp [Polynomial.eval₂_eq_sum_range]

 theorem nonconstant_not_isUnit {f : Bivar} (h : ¬∃ n : ℤ, f=MvPolynomial.C n) :
    ¬IsUnit f := by
  rintro hh
  obtain ⟨n, _, hn⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hh
  exact h ⟨n, hn⟩

/-- The two axis identities already force both monomial exponents to be positive.
No real-rootedness assertion is used in this step. -/
theorem unitary_exponents_pos (H : SourceFormula10) (η : List ℕ)
    (hne : η ≠ []) (hp : ∀ m∈η, 0<m) (f : Bivar)
    (hu : IsUnitary f) (hd : f ∣ denertPoly η) :
    ∃ (F : Polynomial ℤ) (a b : ℕ), 0<a ∧ 0<b ∧
      f=F.eval₂ (Int.castRingHom Bivar) (x^a*y^b) ∧
      ∀ z : ℂ, F.eval₂ (Int.castRingHom ℂ) z=0 → ‖z‖=1 := by
  obtain ⟨hconst, F, a, b, he, hroots⟩ := hu
  have hn := nonconstant_not_isUnit hconst
  have ha : 0<a := by
    by_contra ha
    have ha0 : a=0 := by omega
    have hfix : killX f = f := by
      rw [he, map_int_eval₂]
      simp [ha0, killX, y]
    have hP : killX (denertPoly η)=1 := by
      rw [killX_eq, x_axis_one H η hne hp, Polynomial.eval₂_one]
    exact hn (isUnit_iff_dvd_one.mpr (by simpa only [hfix, hP] using map_dvd killX hd))
  have hb : 0<b := by
    by_contra hb
    have hb0 : b=0 := by omega
    have hfix : killY f = f := by
      rw [he, map_int_eval₂]
      simp [hb0, killY, x]
    have hP : killY (denertPoly η)=1 := by
      rw [killY_eq, y_axis_one H η hne hp, Polynomial.eval₂_one]
    exact hn (isUnit_iff_dvd_one.mpr (by simpa only [hfix, hP] using map_dvd killY hd))
  exact ⟨F,a,b,ha,hb,he,hroots⟩

end
end Carnevale
```

### `PolynomialClearing.lean`

```lean
import PolePrototype
import Mathlib.Algebra.Polynomial.BigOperators

namespace Carnevale
noncomputable section
open Finset

/-- Denominator clearing is performed before any evaluation at a pole. -/
theorem polynomial_sum_div_clears {B F : Type*} [Field B] [Field F]
    (f : Polynomial B →+* F) (hf : Function.Injective f) {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (p d : ι → Polynomial B) (hd : ∀ i∈s, f (d i) ≠ 0)
    (h : ∑ i∈s, f (p i) / f (d i) = 0) :
    ∑ i∈s, p i * ∏ j ∈ s.erase i, d j = 0 := by
  apply hf
  rw [map_zero, map_sum]
  have hh := congrArg (fun z : F => z * ∏ j∈s, f (d j)) h
  rw [zero_mul, sum_mul] at hh
  convert hh using 1
  apply sum_congr rfl
  intro i hi
  simp only [map_mul, map_prod]
  rw [← Finset.mul_prod_erase s (fun j => f (d j)) hi]
  field_simp [hd i hi]

/-- Evaluation of a cleared sum with exactly one singular denominator. -/
theorem polynomial_sum_isolated {B : Type*} [Field B] {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (p d : ι → Polynomial B) (i : ι) (hi : i∈s) (z : B)
    (hz : (d i).eval z = 0) (hd : ∀ j∈s, j≠i → (d j).eval z ≠ 0)
    (h : ∑ j∈s, p j * ∏ k ∈ s.erase j, d k = 0) : (p i).eval z = 0 := by
  have he := congrArg (Polynomial.eval z) h
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_prod,
    Polynomial.eval_zero] at he
  have hs : (∑ j∈s, (p j).eval z * ∏ k∈s.erase j, (d k).eval z) =
      (p i).eval z * ∏ k∈s.erase i, (d k).eval z := by
    apply sum_eq_single i
    · intro j hj hji
      have hm : i∈s.erase j := mem_erase.mpr ⟨Ne.symm hji, hi⟩
      rw [prod_eq_zero hm hz, mul_zero]
    · exact fun hn => False.elim (hn hi)
  rw [hs] at he
  apply (mul_eq_zero.mp he).resolve_right
  apply prod_ne_zero_iff.mpr
  intro j hj
  exact hd j (mem_of_mem_erase hj) (ne_of_mem_erase hj)

end
end Carnevale
```

### `PoleEncoding.lean`

```lean
import RationalNumerator
import PolynomialClearing

namespace Carnevale
noncomputable section
open Finset

/-- The block before embedding its coefficients into ℚ(q). -/
def blockPolynomial (η : List ℕ) : Polynomial (Polynomial ℚ) :=
  (η.map (fun m => ∏ s∈range m,
    (1-Polynomial.C (Polynomial.X^(s+1))*Polynomial.X))).prod

def coefficientPolynomial (η : List ℕ) (j : ℕ) : Polynomial ℚ :=
  (blockPolynomial η).coeff j

def poleDenominator (a j : ℕ) : Polynomial ℚ := Polynomial.X^a+Polynomial.X^j

def poleNumerator (η : List ℕ) (a j : ℕ) : Polynomial ℚ :=
  Polynomial.X^a * coefficientPolynomial η j

 theorem blockPolynomial_map (η : List ℕ) :
    (blockPolynomial η).map (algebraMap (Polynomial ℚ) K) = block η := by
  simp [blockPolynomial, block, Polynomial.map_list_prod, Polynomial.map_prod,
    RatFunc.algebraMap_X, q, Function.comp_def]

 theorem coefficientPolynomial_map (η : List ℕ) (j : ℕ) :
    algebraMap (Polynomial ℚ) K (coefficientPolynomial η j) = c η j := by
  rw [coefficientPolynomial, ← Polynomial.coeff_map, blockPolynomial_map]
  rfl

 theorem coefficientPolynomial_zero (η : List ℕ) : coefficientPolynomial η 0 = 1 := by
  change Polynomial.constantCoeff (blockPolynomial η) = 1
  simp [blockPolynomial, map_list_prod, map_prod, Function.comp_def]

 theorem pole_sum (η : List ℕ) (a : ℕ) : L η a =
    ∑ j∈range (η.sum+1),
      algebraMap (Polynomial ℚ) K (poleNumerator η a j) /
        algebraMap (Polynomial ℚ) K (poleDenominator a j) := by
  unfold L
  apply sum_congr rfl
  intro j _
  simp only [poleNumerator, poleDenominator, map_mul, map_add, map_pow,
    RatFunc.algebraMap_X, show RatFunc.X = q from rfl, coefficientPolynomial_map]
  rw [negative_exponent_denominator q q_ne_zero j a]
  field_simp

 theorem slope_cleared (η : List ℕ) (a : ℕ) (h : L η a = 0) :
    ∑ j∈range (η.sum+1), poleNumerator η a j *
      ∏ k∈(range (η.sum+1)).erase j, poleDenominator a k = 0 := by
  apply polynomial_sum_div_clears (algebraMap (Polynomial ℚ) K)
    (RatFunc.algebraMap_injective ℚ) (range (η.sum+1)) (poleNumerator η a)
    (poleDenominator a)
  · intro j _
    simpa [poleDenominator, q] using power_add_power_ne_zero a j
  · rw [← pole_sum]
    exact h

end
end Carnevale
```

### `TopCoefficient.lean`

```lean
import PoleEncoding

namespace Carnevale
noncomputable section
open Finset

 theorem linear_part_degree {B : Type*} [CommRing B] (z : ℕ→B) (n : ℕ) :
    (∏ s∈range n, (1-Polynomial.C (z s)*Polynomial.X)).natDegree ≤ n := by
  apply (Polynomial.natDegree_prod_le _ _).trans
  calc
    _ ≤ ∑ _s∈range n, 1 := by
      apply sum_le_sum
      intro s _
      exact (Polynomial.natDegree_sub_le _ _).trans (max_le (by simp) (by
        apply Polynomial.natDegree_mul_le |>.trans
        simpa using (Polynomial.natDegree_X_le (R := B))))
    _ = n := by simp

 theorem linear_part_top {B : Type*} [CommRing B] (z : ℕ→B) (n : ℕ) :
    (∏ s∈range n, (1-Polynomial.C (z s)*Polynomial.X)).coeff n =
      ∏ s∈range n, -z s := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hlin : (1-Polynomial.C (z n)*Polynomial.X).natDegree ≤ 1 := by
      simpa using linear_part_degree (fun _ => z n) 1
    rw [prod_range_succ, prod_range_succ,
      Polynomial.coeff_mul_add_eq_of_natDegree_le (linear_part_degree z n) hlin]
    simpa [Polynomial.coeff_one] using congrArg (fun v => v * -z n) ih

 theorem blockPolynomial_degree (η : List ℕ) : (blockPolynomial η).natDegree ≤ η.sum := by
  induction η with
  | nil => simp [blockPolynomial]
  | cons m ms ih =>
    simp only [blockPolynomial, List.map_cons, List.prod_cons, List.sum_cons] at *
    exact Polynomial.natDegree_mul_le.trans
      (Nat.add_le_add (linear_part_degree (fun s => (Polynomial.X : Polynomial ℚ)^(s+1)) m) ih)

 theorem coefficientPolynomial_top (η : List ℕ) : coefficientPolynomial η η.sum =
    (η.map (fun m => ∏ s∈range m, -(Polynomial.X : Polynomial ℚ)^(s+1))).prod := by
  induction η with
  | nil => simp [coefficientPolynomial, blockPolynomial]
  | cons m ms ih =>
    change ((∏ s∈range m, (1-Polynomial.C ((Polynomial.X : Polynomial ℚ)^(s+1))*Polynomial.X)) *
      blockPolynomial ms).coeff (m+ms.sum) = _
    rw [Polynomial.coeff_mul_add_eq_of_natDegree_le
      (linear_part_degree (fun s => (Polynomial.X : Polynomial ℚ)^(s+1)) m)
      (blockPolynomial_degree ms), linear_part_top]
    simpa only [List.map_cons, List.prod_cons, coefficientPolynomial] using
      congrArg (fun v => (∏ s∈range m, -(Polynomial.X : Polynomial ℚ)^(s+1))*v) ih

 theorem coefficientPolynomial_top_eval_ne_zero (η : List ℕ) {ζ : ℂ} (hζ : ζ≠0) :
    Polynomial.eval₂ (Rat.castHom ℂ) ζ (coefficientPolynomial η η.sum) ≠ 0 := by
  rw [coefficientPolynomial_top]
  induction η with
  | nil => simp
  | cons m ms ih =>
    simp only [List.map_cons, List.prod_cons, Polynomial.eval₂_mul]
    apply mul_ne_zero _ ih
    rw [Polynomial.eval₂_finsetProd]
    apply prod_ne_zero_iff.mpr
    intro s _
    simpa using neg_ne_zero.mpr (pow_ne_zero (s+1) hζ)

end
end Carnevale
```

### `ExtremeTopFormula.lean`

```lean
import TopCoefficient
import Mathlib.Algebra.BigOperators.Intervals

namespace Carnevale
noncomputable section
open Finset

 theorem triangle_sum (m : ℕ) : (∑ s∈range m, (s+1)) = m*(m+1)/2 := by
  have h := sum_range_id (m+1)
  rw [sum_range_succ'] at h
  simpa only [add_zero, Nat.add_sub_cancel, Nat.mul_comm (m+1) m] using h

 theorem signed_power_product {B : Type*} [CommRing B] (z : B) (m : ℕ) :
    (∏ s∈range m, -z^(s+1)) = (-1)^m*z^(m*(m+1)/2) := by
  rw [← triangle_sum]
  induction m with
  | zero => simp
  | succ m ih =>
    rw [prod_range_succ, sum_range_succ, pow_succ, pow_add, ih]
    ring

 theorem coefficientPolynomial_top_formula (η : List ℕ) :
    coefficientPolynomial η η.sum = (-1)^η.sum*(Polynomial.X : Polynomial ℚ)^(weight η) := by
  rw [coefficientPolynomial_top]
  induction η with
  | nil => simp [weight]
  | cons m ms ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons, signed_power_product, weight] at *
    rw [ih, pow_add, pow_add]
    ring

 theorem coefficient_zero (η : List ℕ) : c η 0=1 := by
  rw [← coefficientPolynomial_map, coefficientPolynomial_zero, map_one]

 theorem coefficient_top (η : List ℕ) : c η η.sum = (-1)^η.sum*q^(weight η) := by
  rw [← coefficientPolynomial_map, coefficientPolynomial_top_formula]
  simp [q]

end
end Carnevale
```

### `SlopePoleBound.lean`

```lean
import PoleEncoding
import Mathlib.RingTheory.RootsOfUnity.Complex

namespace Carnevale
noncomputable section
open Finset

/-- A cleared sum can be specialized by any homomorphism, including at roots of unity. -/
theorem cleared_sum_isolated {B F : Type*} [CommRing B] [CommRing F] [IsDomain F]
    (f : B →+* F) {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (p d : ι → B) (i : ι) (hi : i∈s)
    (hz : f (d i)=0) (hd : ∀ j∈s, j≠i → f (d j) ≠ 0)
    (h : ∑ j∈s, p j * ∏ k∈s.erase j, d k = 0) : f (p i)=0 := by
  have he := congrArg f h
  simp only [map_sum, map_mul, map_prod, map_zero] at he
  have hs : (∑ j∈s, f (p j) * ∏ k∈s.erase j, f (d k)) =
      f (p i) * ∏ k∈s.erase i, f (d k) := by
    apply sum_eq_single i
    · intro j _ hji
      have hm : i∈s.erase j := mem_erase.mpr ⟨Ne.symm hji, hi⟩
      rw [prod_eq_zero hm hz, mul_zero]
    · exact fun hn => False.elim (hn hi)
  rw [hs] at he
  apply (mul_eq_zero.mp he).resolve_right
  apply prod_ne_zero_iff.mpr
  intro j hj
  exact hd j (mem_of_mem_erase hj) (ne_of_mem_erase hj)

 theorem primitive_even_half {a : ℕ} (ha : 0<a) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (2*a)) : ζ^a = -1 := by
  have hs : (ζ^a)^2 = 1 := by
    rw [← pow_mul, Nat.mul_comm a 2]
    exact hζ.pow_eq_one
  exact (sq_eq_one_iff.mp hs).resolve_left
    (hζ.pow_ne_one_of_pos_of_lt (Nat.ne_of_gt ha) (by omega))

/-- The general isolated first pole: every root slope is at most half the total.
This statement needs neither positivity of the parts nor the source formula. -/
theorem slope_pole_bound (η : List ℕ) (a : ℕ) (ha : 0<a) (hL : L η a=0) :
    2*a ≤ η.sum := by
  by_contra hn
  have hN : η.sum < 2*a := by omega
  let ζ : ℂ := Complex.exp (2*Real.pi*Complex.I/(2*a : ℕ))
  have hζ : IsPrimitiveRoot ζ (2*a) := Complex.isPrimitiveRoot_exp _ (by omega)
  have hh := primitive_even_half ha hζ
  let ev : Polynomial ℚ →+* ℂ := Polynomial.eval₂RingHom (Rat.castHom ℂ) ζ
  have hpole : ev (poleNumerator η a 0) = 0 := by
    apply cleared_sum_isolated ev (range (η.sum+1)) (poleNumerator η a)
      (poleDenominator a) 0 (by simp)
    · simp [ev, poleDenominator, hh]
    · intro j hj hj0
      have hjpos : 0<j := by omega
      have hjlt : j<2*a := by have := mem_range.mp hj; omega
      have hpow := hζ.pow_ne_one_of_pos_of_lt (Nat.ne_of_gt hjpos) hjlt
      intro he
      apply hpow
      have he' : ζ^a+ζ^j=0 := by simpa [ev, poleDenominator] using he
      rw [hh] at he'
      linear_combination he'
    · exact slope_cleared η a hL
  simp [ev, poleNumerator, coefficientPolynomial_zero, hh] at hpole

end
end Carnevale
```

### `SlopeMidpoint.lean`

```lean
import SlopePoleBound
import TopCoefficient

namespace Carnevale
noncomputable section
open Finset

/-- The opposite isolated pole uses the top coefficient, so inversion symmetry
is unnecessary for the midpoint reduction. -/
theorem slope_pole_bound_opposite (η : List ℕ) (a : ℕ) (hL : L η a=0) :
    η.sum ≤ 2*a := by
  by_contra hn
  have hN : 2*a < η.sum := by omega
  have hd : 0<η.sum-a := by omega
  let ζ : ℂ := Complex.exp (2*Real.pi*Complex.I/(2*(η.sum-a) : ℕ))
  have hζ : IsPrimitiveRoot ζ (2*(η.sum-a)) := Complex.isPrimitiveRoot_exp _ (by omega)
  have hh := primitive_even_half hd hζ
  have htop : ζ^η.sum = -(ζ^a) := by
    rw [show η.sum = a+(η.sum-a) by omega, pow_add, hh, mul_neg_one]
  let ev : Polynomial ℚ →+* ℂ := Polynomial.eval₂RingHom (Rat.castHom ℂ) ζ
  have hpole : ev (poleNumerator η a η.sum) = 0 := by
    apply cleared_sum_isolated ev (range (η.sum+1)) (poleNumerator η a)
      (poleDenominator a) η.sum (by simp)
    · simp [ev, poleDenominator, htop]
    · intro j hj hjN
      have hjlt : j<2*(η.sum-a) := by have := mem_range.mp hj; omega
      have hNlt : η.sum<2*(η.sum-a) := by omega
      intro he
      apply hjN
      apply hζ.pow_inj hjlt hNlt
      have he' : ζ^a+ζ^j=0 := by simpa [ev, poleDenominator] using he
      rw [htop]
      linear_combination he'
    · exact slope_cleared η a hL
  have hz : ζ≠0 := Complex.exp_ne_zero _
  apply (mul_ne_zero (pow_ne_zero a hz) (coefficientPolynomial_top_eval_ne_zero η hz))
  simpa [ev, poleNumerator] using hpole

 theorem slope_midpoint_unconditional (η : List ℕ) (a : ℕ) (ha : 0<a)
    (hL : L η a=0) : η.sum=2*a :=
  Nat.le_antisymm (slope_pole_bound_opposite η a hL) (slope_pole_bound η a ha hL)

/-- Discharges the original P2 specification, with unused source assumptions omitted above. -/
theorem slope_midpoint (_H : SourceFormula10) (η : List ℕ)
    (_hne : η ≠ []) (_hp : ∀ m∈η, 0<m) (a : ℕ) (ha : 0<a)
    (hL : L η a=0) : η.sum=2*a := slope_midpoint_unconditional η a ha hL

end
end Carnevale
```

### `FirstPole.lean`

```lean
import SlopeMidpoint
import ExtremeTopFormula

namespace Carnevale
noncomputable section
open Finset

 def firstPairNumerator (η : List ℕ) (a j : ℕ) : Polynomial ℚ :=
  if j=0 then Polynomial.X^a+coefficientPolynomial η η.sum else poleNumerator η a j
 def firstPairDenominator (a j : ℕ) : Polynomial ℚ :=
  if j=0 then Polynomial.X^a+1 else poleDenominator a j

 theorem first_pair_sum (η : List ℕ) (a : ℕ) (ha : 0<a)
    (hN : η.sum=2*a) (hL : L η a=0) :
    ∑ j∈range η.sum, algebraMap (Polynomial ℚ) K (firstPairNumerator η a j) /
      algebraMap (Polynomial ℚ) K (firstPairDenominator a j) = 0 := by
  let f (j : ℕ) : K := algebraMap (Polynomial ℚ) K (poleNumerator η a j) /
      algebraMap (Polynomial ℚ) K (poleDenominator a j)
  let g (j : ℕ) : K := algebraMap (Polynomial ℚ) K (firstPairNumerator η a j) /
      algebraMap (Polynomial ℚ) K (firstPairDenominator a j)
  have h0 : 0∈range η.sum := by simp; omega
  have hs : (∑ j∈range η.sum, f j)+f η.sum=0 := by
    rw [← sum_range_succ, ← pole_sum]
    exact hL
  have hpair : g 0 = f 0 + f η.sum := by
    simp only [g, f, firstPairNumerator, firstPairDenominator, ↓reduceIte,
      poleNumerator, poleDenominator, map_add, map_mul, map_pow, map_one,
      RatFunc.algebraMap_X, coefficientPolynomial_map, coefficient_zero, pow_zero, mul_one]
    change (q^a+c η η.sum)/(q^a+1) = q^a/(q^a+1)+
      q^a*c η η.sum/(q^a+q^η.sum)
    rw [hN, show 2*a = a+a by omega, pow_add]
    field_simp [q_ne_zero, power_add_power_ne_zero a 0]
    ring
  have hreg : (∑ j∈(range η.sum).erase 0, g j) =
      ∑ j∈(range η.sum).erase 0, f j := by
    apply sum_congr rfl
    intro j hj
    simp only [g, f, firstPairNumerator, firstPairDenominator,
      ite_eq_right (ne_of_mem_erase hj)]
  change (∑ j∈range η.sum, g j)=0
  rw [← sum_erase_add (range η.sum) g h0, hreg, hpair, ← add_assoc,
    sum_erase_add (range η.sum) f h0]
  exact hs

 theorem first_pair_cleared (η : List ℕ) (a : ℕ) (ha : 0<a)
    (hN : η.sum=2*a) (hL : L η a=0) :
    ∑ j∈range η.sum, firstPairNumerator η a j *
      ∏ k∈(range η.sum).erase j, firstPairDenominator a k=0 := by
  apply polynomial_sum_div_clears (algebraMap (Polynomial ℚ) K)
    (RatFunc.algebraMap_injective ℚ) (range η.sum) (firstPairNumerator η a)
    (firstPairDenominator a)
  · intro j _
    by_cases hj : j=0
    · simpa [firstPairDenominator, hj, q] using power_add_power_ne_zero a 0
    · simpa [firstPairDenominator, hj, poleDenominator, q] using power_add_power_ne_zero a j
  · exact first_pair_sum η a ha hN hL

 theorem first_pole (η : List ℕ) (a : ℕ) (ha : 0<a)
    (hN : η.sum=2*a) (hL : L η a=0) : η.sum ∣ weight η := by
  let ζ : ℂ := Complex.exp (2*Real.pi*Complex.I/η.sum)
  have hpos : 0<η.sum := by omega
  have hζ : IsPrimitiveRoot ζ η.sum := Complex.isPrimitiveRoot_exp _ (Nat.ne_of_gt hpos)
  have hh : ζ^a = -1 := primitive_even_half ha (hN ▸ hζ)
  let ev : Polynomial ℚ →+* ℂ := Polynomial.eval₂RingHom (Rat.castHom ℂ) ζ
  have hpole : ev (firstPairNumerator η a 0) = 0 := by
    apply cleared_sum_isolated ev (range η.sum) (firstPairNumerator η a)
      (firstPairDenominator a) 0 (by simpa using hpos)
    · simp [ev, firstPairDenominator, hh]
    · intro j hj hj0
      have hpow := hζ.pow_ne_one_of_pos_of_lt hj0 (mem_range.mp hj)
      intro he
      apply hpow
      have he' : ζ^a+ζ^j=0 := by simpa [ev, firstPairDenominator, hj0, poleDenominator] using he
      rw [hh] at he'
      linear_combination he'
    · exact first_pair_cleared η a ha hN hL
  apply (hζ.pow_eq_one_iff_dvd _).mp
  have he : ζ^a+(-1:ℂ)^η.sum*ζ^(weight η)=0 := by
    simpa [ev, firstPairNumerator, coefficientPolynomial_top_formula, Polynomial.eval₂_pow, Polynomial.eval₂_neg] using hpole
  rw [hh, hN, pow_mul] at he
  norm_num at he
  linear_combination he

end
end Carnevale
```

### `BinomialReduction.lean`

```lean
import SlopeMidpoint
import UnitReductionAxes

namespace Carnevale
noncomputable section

 theorem bivarToK_binomial (a : ℕ) :
    bivarToK (1+x^a*y) = 1+Polynomial.C (q^a)*Polynomial.X := by
  simp [bivarToK, x, y]

 theorem binomial_root (P : Bivar) (a : ℕ) (hd : (1+x^a*y) ∣ P) :
    (bivarToK P).eval (-q^(-(a:ℤ)))=0 := by
  obtain ⟨g, hg⟩ := map_dvd bivarToK hd
  rw [hg, Polynomial.eval_mul]
  have he : (bivarToK (1+x^a*y)).eval (-q^(-(a:ℤ)))=0 := by
    rw [bivarToK_binomial]
    simp only [Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X, zpow_neg, zpow_natCast]
    field_simp [q_ne_zero]
    ring
  rw [he, zero_mul]

 theorem binomial_slope_pos (H : SourceFormula10) (η : List ℕ)
    (hne : η≠[]) (hp : ∀ m∈η, 0<m) (a : ℕ)
    (hd : (1+x^a*y) ∣ denertPoly η) : 0<a := by
  by_contra hn
  have ha : a=0 := by omega
  let pr : Bivar →+* Polynomial ℤ := MvPolynomial.eval₂Hom
    (Int.castRingHom (Polynomial ℤ)) (fun i => if i=0 then 0 else Polynomial.X)
  have hs : pr (denertPoly η)=1 := x_axis_one H η hne hp
  obtain ⟨g,hg⟩ := map_dvd pr hd
  rw [hs] at hg
  have he := congrArg (Polynomial.eval (-1)) hg
  norm_num [pr, ha, x, y] at he

 theorem binomial_slope_midpoint (H : SourceFormula10) (η : List ℕ)
    (hne : η≠[]) (hp : ∀ m∈η, 0<m) (a : ℕ)
    (hd : (1+x^a*y) ∣ denertPoly η) : η.sum=2*a := by
  have hroot := binomial_root (denertPoly η) a hd
  exact slope_midpoint_unconditional η a (binomial_slope_pos H η hne hp a hd)
    ((slope_zero_iff H η hne hp a).mp hroot)

 theorem at_most_one (H : SourceFormula10) (η : List ℕ)
    (hne : η≠[]) (hp : ∀ m∈η, 0<m) (a b : ℕ)
    (ha : (1+x^a*y) ∣ denertPoly η) (hb : (1+x^b*y) ∣ denertPoly η) : a=b := by
  have h1 := binomial_slope_midpoint H η hne hp a ha
  have h2 := binomial_slope_midpoint H η hne hp b hb
  omega

end
end Carnevale
```

### `BlockReflection.lean`

```lean
import ExtremeTopFormula
import Mathlib.Algebra.Polynomial.Reverse

namespace Carnevale
noncomputable section
open Finset

 def blockAt {B : Type*} [CommRing B] (η : List ℕ) (z : B) : Polynomial B :=
  (η.map (fun m => ∏ s∈range m, (1-Polynomial.C (z^(s+1))*Polynomial.X))).prod

 theorem blockAt_degree {B : Type*} [CommRing B] (η : List ℕ) (z : B) :
    (blockAt η z).natDegree ≤ η.sum := by
  induction η with
  | nil => simp [blockAt]
  | cons m ms ih =>
    exact Polynomial.natDegree_mul_le.trans
      (Nat.add_le_add (linear_part_degree (fun s => z^(s+1)) m) ih)

 theorem linear_reflect {B : Type*} [Field B] (z : B) (hz : z≠0) :
    Polynomial.reflect 1 (1-Polynomial.C z*Polynomial.X) =
      Polynomial.C (-z)*(1-Polynomial.C z⁻¹*Polynomial.X) := by
  simp only [Polynomial.reflect_sub, Polynomial.reflect_one, Polynomial.reflect_C_mul,
    Polynomial.reflect_one_X, pow_one, mul_one]
  rw [mul_sub, mul_one, ← mul_assoc, ← Polynomial.C_mul]
  simp only [neg_mul, mul_inv_cancel₀ hz, Polynomial.C_neg, Polynomial.C_1, neg_mul, one_mul]
  ring

 theorem part_reflect {B : Type*} [Field B] (z : B) (hz : z≠0) (m : ℕ) :
    Polynomial.reflect m (∏ s∈range m, (1-Polynomial.C (z^(s+1))*Polynomial.X)) =
      Polynomial.C (∏ s∈range m, -z^(s+1)) *
        (∏ s∈range m, (1-Polynomial.C ((z⁻¹)^(s+1))*Polynomial.X)) := by
  induction m with
  | zero => simp [Polynomial.reflect_one]
  | succ m ih =>
    have hlin : (1-Polynomial.C (z^(m+1))*Polynomial.X).natDegree ≤ 1 := by
      simpa using linear_part_degree (fun _ => z^(m+1)) 1
    rw [prod_range_succ, Polynomial.reflect_mul _ _ (linear_part_degree _ m) hlin,
      ih, linear_reflect _ (pow_ne_zero _ hz), ← inv_pow, prod_range_succ, prod_range_succ, map_mul]
    ring

 theorem blockAt_reflect {B : Type*} [Field B] (η : List ℕ) (z : B) (hz : z≠0) :
    Polynomial.reflect η.sum (blockAt η z) =
      Polynomial.C ((-1)^η.sum*z^(weight η))*blockAt η z⁻¹ := by
  induction η with
  | nil => simp [blockAt, weight, Polynomial.reflect_one]
  | cons m ms ih =>
    change Polynomial.reflect (m+ms.sum)
      ((∏ s∈range m, (1-Polynomial.C (z^(s+1))*Polynomial.X))*blockAt ms z) = _
    rw [Polynomial.reflect_mul _ _ (linear_part_degree _ m) (blockAt_degree ms z),
      part_reflect z hz m, ih, signed_power_product]
    simp only [blockAt, List.map_cons, List.prod_cons, List.sum_cons, weight,
      pow_add, map_mul] at *
    ring

 theorem part_coeff_one {B : Type*} [CommRing B] (z : B) (m : ℕ) :
    (∏ s∈range m, (1-Polynomial.C (z^(s+1))*Polynomial.X)).coeff 1 =
      -(∑ s∈range m, z^(s+1)) := by
  induction m with
  | zero => simp [Polynomial.coeff_one]
  | succ m ih =>
    rw [prod_range_succ, Polynomial.mul_coeff_one, ih, sum_range_succ]
    have h0 : (∏ s∈range m, (1-Polynomial.C (z^(s+1))*Polynomial.X)).coeff 0 = 1 := by
      change Polynomial.constantCoeff _ = 1
      simp [map_prod]
    rw [h0]
    simp only [Polynomial.coeff_sub, Polynomial.coeff_one, Polynomial.coeff_C_mul_X,
      one_ne_zero, zero_ne_one, ↓reduceIte, one_mul, zero_sub, mul_neg]
    ring

 theorem blockAt_coeff_one {B : Type*} [CommRing B] (η : List ℕ) (z : B) :
    (blockAt η z).coeff 1 = -levelSum η z := by
  have h0 (ms : List ℕ) : (blockAt ms z).coeff 0 = 1 := by
    change Polynomial.constantCoeff _ = 1
    simp [blockAt, map_list_prod, map_prod, Function.comp_def]
  induction η with
  | nil => simp [blockAt, levelSum, Polynomial.coeff_one]
  | cons m ms ih =>
    change ((∏ s∈range m, (1-Polynomial.C (z^(s+1))*Polynomial.X))*blockAt ms z).coeff 1 = _
    rw [Polynomial.mul_coeff_one, ih, part_coeff_one, h0]
    have hp0 : (∏ s∈range m, (1-Polynomial.C (z^(s+1))*Polynomial.X)).coeff 0 = 1 := by
      change Polynomial.constantCoeff _ = 1
      simp [map_prod]
    rw [hp0]
    simp [levelSum]

 theorem blockAt_penultimate {B : Type*} [Field B] (η : List ℕ) (z : B) (hz : z≠0)
    (hN : 1≤η.sum) :
    (blockAt η z).coeff (η.sum-1) =
      -((-1)^η.sum*z^(weight η))*levelSum η z⁻¹ := by
  have h := congrArg (fun p : Polynomial B => p.coeff 1) (blockAt_reflect η z hz)
  rw [Polynomial.coeff_reflect, Polynomial.revAt_le hN, Polynomial.coeff_C_mul,
    blockAt_coeff_one] at h
  exact h.trans (by ring)

end
end Carnevale
```

### `ExtremeCoefficients.lean`

```lean
import BlockReflection

namespace Carnevale
noncomputable section

 theorem coefficientPolynomial_eval (η : List ℕ) (j : ℕ) (ζ : ℂ) :
    Polynomial.eval₂ (Rat.castHom ℂ) ζ (coefficientPolynomial η j) =
      (blockAt η ζ).coeff j := by
  change (Polynomial.eval₂RingHom (Rat.castHom ℂ) ζ) ((blockPolynomial η).coeff j) = _
  rw [← Polynomial.coeff_map]
  congr 1
  simp [blockPolynomial, blockAt, Polynomial.map_list_prod, Polynomial.map_prod,
    Function.comp_def]

 theorem extreme_coefficients (η : List ℕ) (hN : 2≤η.sum) (he : Even η.sum) :
    c η 0=1 ∧ c η η.sum=q^(weight η) ∧ c η 1= -levelSum η q ∧
      c η (η.sum-1)= -q^(weight η)*levelSum η q⁻¹ := by
  have hs : (-1:K)^η.sum=1 := he.neg_one_pow
  refine ⟨coefficient_zero η, ?_, ?_, ?_⟩
  · rw [coefficient_top, hs, one_mul]
  · exact blockAt_coeff_one η q
  · simpa only [hs, one_mul, c, blockAt, block] using blockAt_penultimate η q q_ne_zero (by omega)

 theorem complex_extreme_coefficients (η : List ℕ) (hN : 2≤η.sum) (he : Even η.sum)
    (ζ : ℂ) (hz : ζ≠0) :
    Polynomial.eval₂ (Rat.castHom ℂ) ζ (coefficientPolynomial η 1) = -levelSum η ζ ∧
    Polynomial.eval₂ (Rat.castHom ℂ) ζ (coefficientPolynomial η (η.sum-1)) =
      -ζ^(weight η)*levelSum η ζ⁻¹ := by
  have hs : (-1:ℂ)^η.sum=1 := he.neg_one_pow
  constructor
  · rw [coefficientPolynomial_eval, blockAt_coeff_one]
  · rw [coefficientPolynomial_eval, blockAt_penultimate η ζ hz (by omega), hs, one_mul]

end
end Carnevale
```

### `SecondPole.lean`

```lean
import FirstPole
import ExtremeCoefficients

namespace Carnevale
noncomputable section
open Finset

 theorem sum_pair_merge {ι F : Type*} [DecidableEq ι] [AddCommGroup F]
    (s : Finset ι) (f g : ι→F) (i j : ι) (hi : i∈s) (hj : j∈s) (hij : i≠j)
    (hpair : g i=f i+f j) (hreg : ∀ k∈s.erase j, k≠i → g k=f k) :
    (∑ k∈s.erase j, g k)=∑ k∈s, f k := by
  have hii : i∈s.erase j := mem_erase.mpr ⟨hij,hi⟩
  rw [← sum_erase_add (s.erase j) g hii, ← sum_erase_add s f hj,
    ← sum_erase_add (s.erase j) f hii]
  have hr : (∑ k∈(s.erase j).erase i, g k)=∑ k∈(s.erase j).erase i, f k := by
    apply sum_congr rfl
    intro k hk
    exact hreg k (mem_of_mem_erase hk) (ne_of_mem_erase hk)
  rw [hr,hpair]
  abel

 def secondPairNumerator (η : List ℕ) (a j : ℕ) : Polynomial ℚ :=
  if j=1 then Polynomial.X^(a-1)*coefficientPolynomial η 1+
    coefficientPolynomial η (η.sum-1) else poleNumerator η a j
 def secondPairDenominator (a j : ℕ) : Polynomial ℚ :=
  if j=1 then 1+Polynomial.X^(a-1) else poleDenominator a j

 theorem second_pair_sum (η : List ℕ) (a : ℕ) (ha : 2≤a)
    (hN : η.sum=2*a) (hL : L η a=0) :
    ∑ j∈(range (η.sum+1)).erase (η.sum-1),
      algebraMap (Polynomial ℚ) K (secondPairNumerator η a j) /
        algebraMap (Polynomial ℚ) K (secondPairDenominator a j)=0 := by
  let f (j : ℕ) : K := algebraMap (Polynomial ℚ) K (poleNumerator η a j) /
      algebraMap (Polynomial ℚ) K (poleDenominator a j)
  let g (j : ℕ) : K := algebraMap (Polynomial ℚ) K (secondPairNumerator η a j) /
      algebraMap (Polynomial ℚ) K (secondPairDenominator a j)
  have hpair : g 1=f 1+f (η.sum-1) := by
    simp only [g,f,secondPairNumerator,secondPairDenominator, ↓reduceIte,
      poleNumerator,poleDenominator,map_add,map_mul,map_pow,map_one,
      RatFunc.algebraMap_X,coefficientPolynomial_map,pow_one]
    change (q^(a-1)*c η 1+c η (η.sum-1))/(1+q^(a-1)) =
      q^a*c η 1/(q^a+q)+q^a*c η (η.sum-1)/(q^a+q^(η.sum-1))
    have heA : q^a=q*q^(a-1) := by
      rw [← pow_succ', Nat.sub_add_cancel (by omega : 1≤a)]
    have heN : q^(η.sum-1)=q^a*q^(a-1) := by
      rw [← pow_add]
      congr 1
      omega
    have hqa : 1+q^(a-1)≠0 := by simpa using power_add_power_ne_zero 0 (a-1)
    have ht1 : q^a*c η 1/(q^a+q)=q^(a-1)*c η 1/(1+q^(a-1)) := by
      rw [heA, show q*q^(a-1)+q=q*(1+q^(a-1)) by ring]
      field_simp [q_ne_zero,hqa]
    have htN : q^a*c η (η.sum-1)/(q^a+q^(η.sum-1)) =
        c η (η.sum-1)/(1+q^(a-1)) := by
      rw [heN, show q^a+q^a*q^(a-1)=q^a*(1+q^(a-1)) by ring]
      field_simp [q_ne_zero,hqa]
    rw [ht1,htN,add_div]

  change (∑ j∈(range (η.sum+1)).erase (η.sum-1), g j)=0
  rw [sum_pair_merge (range (η.sum+1)) f g 1 (η.sum-1)
    (by simp only [mem_range]; omega) (by simp only [mem_range]; omega) (by omega) hpair]
  · rw [← pole_sum]
    exact hL
  · intro j _ hj
    simp only [g,f,secondPairNumerator,secondPairDenominator,ite_eq_right hj]

 theorem second_pair_cleared (η : List ℕ) (a : ℕ) (ha : 2≤a)
    (hN : η.sum=2*a) (hL : L η a=0) :
    let s := (range (η.sum+1)).erase (η.sum-1)
    ∑ j∈s, secondPairNumerator η a j * ∏ k∈s.erase j, secondPairDenominator a k=0 := by
  apply polynomial_sum_div_clears (algebraMap (Polynomial ℚ) K)
    (RatFunc.algebraMap_injective ℚ) _ (secondPairNumerator η a) (secondPairDenominator a)
  · intro j _
    by_cases hj : j=1
    · simpa [secondPairDenominator,hj,q] using power_add_power_ne_zero 0 (a-1)
    · simpa [secondPairDenominator,hj,poleDenominator,q] using power_add_power_ne_zero a j
  · exact second_pair_sum η a ha hN hL

 theorem primitive_second_denominators (a : ℕ) (ha : 2≤a) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (2*(a-1))) (j : ℕ) (hj : j≤2*a) :
    ζ^a+ζ^j=0 ↔ j=1 ∨ j=2*a-1 := by
  have hh := primitive_even_half (by omega : 0<a-1) hζ
  have hz : ζ≠0 := (hζ.isUnit (by omega)).ne_zero
  have hza : ζ^a = -ζ := by
    rw [show a=(a-1)+1 by omega, pow_succ, hh, neg_one_mul]
  constructor
  · intro he
    have heq : ζ^j=ζ := by rw [hza] at he; linear_combination he
    have hj0 : j≠0 := by
      intro h
      rw [h,pow_zero] at heq
      exact hζ.ne_one (by omega) heq.symm
    have hpow : ζ^(j-1)=1 := by
      apply mul_right_cancel₀ hz
      rw [← pow_succ, Nat.sub_add_cancel (by omega : 1≤j), one_mul]
      exact heq
    have hd := (hζ.pow_eq_one_iff_dvd (j-1)).mp hpow
    by_cases hsmall : j-1=0
    · left; omega
    · have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hsmall) hd
      by_cases htop : j=2*a-1
      · exact Or.inr htop
      · have hjN : j=2*a := by omega
        have hd' : 2*(a-1) ∣ 2*(a-1)+1 := by convert hd using 1; omega
        have hbad : 2*(a-1) ∣ 1 := (Nat.dvd_add_iff_right (dvd_refl _)).mpr hd'
        have := Nat.le_of_dvd (by omega : 0<1) hbad
        omega
  · rintro (rfl|rfl)
    · rw [hza,pow_one,neg_add_cancel]
    · rw [show 2*a-1=(2*(a-1))+1 by omega, pow_succ,hζ.pow_eq_one,one_mul,hza,
        neg_add_cancel]

 theorem second_pole (η : List ℕ) (a : ℕ) (ha : 2≤a)
    (hN : η.sum=2*a) (hL : L η a=0) :
    let ξ : ℂ := Complex.exp (2*Real.pi*Complex.I/(η.sum-2 : ℕ))
    levelSum η ξ=ξ^(weight η)*levelSum η ξ⁻¹ := by
  dsimp only
  let ξ : ℂ := Complex.exp (2*Real.pi*Complex.I/(η.sum-2 : ℕ))
  have hpos : 0<η.sum-2 := by omega
  have hξ : IsPrimitiveRoot ξ (2*(a-1)) := by
    rw [show 2*(a-1)=η.sum-2 by omega]
    exact Complex.isPrimitiveRoot_exp _ (Nat.ne_of_gt hpos)
  have hh := primitive_even_half (by omega : 0<a-1) hξ
  have hz : ξ≠0 := Complex.exp_ne_zero _
  let ev : Polynomial ℚ →+* ℂ := Polynomial.eval₂RingHom (Rat.castHom ℂ) ξ
  have hpole : ev (secondPairNumerator η a 1)=0 := by
    apply cleared_sum_isolated ev ((range (η.sum+1)).erase (η.sum-1))
      (secondPairNumerator η a) (secondPairDenominator a) 1 (by simp; omega)
    · simp [ev,secondPairDenominator,hh]
    · intro j hj hj1
      have hjN := ne_of_mem_erase hj
      have hjle : j≤2*a := by have := mem_range.mp (mem_of_mem_erase hj); omega
      intro he
      have he' : ξ^a+ξ^j=0 := by simpa [ev,secondPairDenominator,hj1,poleDenominator] using he
      rcases (primitive_second_denominators a ha hξ j hjle).mp he' with h|h
      · exact hj1 h
      · exact hjN (by omega)
    · exact second_pair_cleared η a ha hN hL
  have hEven : Even η.sum := ⟨a, by omega⟩
  obtain ⟨hc1,hcN⟩ := complex_extreme_coefficients η (by omega) hEven ξ hz
  have he : ξ^(a-1)*(-levelSum η ξ)-ξ^(weight η)*levelSum η ξ⁻¹=0 := by
    simpa [ev,secondPairNumerator,hc1,hcN,sub_eq_add_neg] using hpole
  rw [hh] at he
  dsimp only [ξ] at he
  linear_combination he

end
end Carnevale
```

### `ComplexSineBridge.lean`

```lean
import SlopePoleBound
import StrictSineList
import Mathlib.Basic.Complex.BigOperators

namespace Carnevale
noncomputable section
open Finset
open scoped ComplexConjugate

 theorem centered_power_im (θ : ℝ) (n l : ℕ) :
    (((Complex.exp ((θ:ℂ)*Complex.I))^l)⁻¹ *
      (Complex.exp ((θ:ℂ)*Complex.I))^n).im = Real.sin (θ*((n:ℝ)-(l:ℝ))) := by
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_neg, ← Complex.exp_add]
  have he : -((l:ℂ)*(θ:ℂ)*Complex.I)+(n:ℂ)*(θ:ℂ)*Complex.I =
      (θ*((n:ℝ)-(l:ℝ)) : ℝ)*Complex.I := by push_cast; ring
  rw [← mul_assoc, ← mul_assoc, he]
  simp [Complex.exp_im]

 theorem centered_level_im (η : List ℕ) (θ : ℝ) (l : ℕ) :
    (((Complex.exp ((θ:ℂ)*Complex.I))^l)⁻¹ *
      levelSum η (Complex.exp ((θ:ℂ)*Complex.I))).im =
    (η.map (fun m => ∑ s∈range m, Real.sin (θ*((s+1:ℝ)-(l:ℝ))))).sum := by
  induction η with
  | nil => simp [levelSum]
  | cons m ms ih =>
    simp only [levelSum, List.map_cons, List.sum_cons] at *
    rw [mul_add, Complex.add_im, ih]
    congr 1
    rw [mul_sum, Complex.im_sum]
    apply sum_congr rfl
    intro s _
    simpa only [Nat.cast_add, Nat.cast_one] using centered_power_im θ (s+1) l

 theorem centered_level_zero (η : List ℕ) (θ : ℝ) (l : ℕ)
    (h : levelSum η (Complex.exp ((θ:ℂ)*Complex.I)) =
      Complex.exp ((θ:ℂ)*Complex.I)^(2*l)*
        levelSum η (Complex.exp ((θ:ℂ)*Complex.I))⁻¹) :
    (η.map (fun m => ∑ s∈range m, Real.sin (θ*((s+1:ℝ)-(l:ℝ))))).sum=0 := by
  let z : ℂ := Complex.exp ((θ:ℂ)*Complex.I)
  have hz : z≠0 := Complex.exp_ne_zero _
  have hc : conj z=z⁻¹ := by
    change conj (Complex.exp ((θ:ℂ)*Complex.I)) = _
    rw [← Complex.exp_conj]
    simp [z, Complex.exp_neg]
  have hsum : conj (levelSum η z)=levelSum η z⁻¹ := by
    simp [levelSum, map_list_sum, map_sum, map_pow, Function.comp_def, hc]
  have hself : conj ((z^l)⁻¹*levelSum η z) = (z^l)⁻¹*levelSum η z := by
    simp only [map_mul, map_inv₀, map_pow, hc, inv_pow, inv_inv, hsum]
    change z^l*levelSum η z⁻¹ = (z^l)⁻¹*levelSum η z
    change levelSum η z=z^(2*l)*levelSum η z⁻¹ at h
    rw [h, show z^(2*l)=(z^l)^2 by rw [mul_comm 2 l, pow_mul]]
    field_simp [hz]
  have hzero := Complex.conj_eq_iff_im.mp hself
  rw [← centered_level_im η θ l]
  exact hzero

end
end Carnevale
```

### `SecondPoleSine.lean`

```lean
import SecondPole
import ComplexSineBridge

namespace Carnevale
noncomputable section
open Finset

 theorem second_pole_sine (η : List ℕ) (hN : 4≤η.sum) (he : Even η.sum)
    (hd : η.sum ∣ weight η) (hL : L η (η.sum/2)=0) :
    (η.map (fun m => ∑ s∈range m,
      Real.sin (2*Real.pi*((s+1:ℝ)-(weight η:ℝ)/(η.sum:ℝ))/((η.sum:ℝ)-2)))).sum=0 := by
  have hmid : η.sum=2*(η.sum/2) := by obtain ⟨k,hk⟩ := he; omega
  have ha : 2≤η.sum/2 := by omega
  obtain ⟨l,hl⟩ := hd
  let θ : ℝ := 2*Real.pi/(η.sum-2:ℕ)
  let ξ : ℂ := Complex.exp (2*Real.pi*Complex.I/(η.sum-2:ℕ))
  have hξang : ξ=Complex.exp ((θ:ℂ)*Complex.I) := by
    dsimp only [ξ]
    congr 1
    dsimp only [θ]
    push_cast
    ring
  have hξ : IsPrimitiveRoot ξ (η.sum-2) := Complex.isPrimitiveRoot_exp _ (by omega)
  have hp := second_pole η (η.sum/2) ha hmid hL
  change levelSum η ξ=ξ^(weight η)*levelSum η ξ⁻¹ at hp
  have hexp : ξ^(weight η)=ξ^(2*l) := by
    rw [hl, show η.sum*l=(η.sum-2)*l+2*l by nlinarith [Nat.sub_add_cancel (by omega : 2≤η.sum)],
      pow_add, pow_mul, hξ.pow_eq_one, one_pow, one_mul]
  rw [hexp,hξang] at hp
  have hs := centered_level_zero η θ l hp
  have hpos : (η.sum:ℝ)≠0 := Nat.cast_ne_zero.mpr (by omega)
  have hmean : (weight η:ℝ)/(η.sum:ℝ)=(l:ℝ) := by
    rw [hl,Nat.cast_mul]
    field_simp
  have hcast : ((η.sum-2:ℕ):ℝ)=(η.sum:ℝ)-2 := by
    rw [Nat.cast_sub (by omega : 2≤η.sum)]
    norm_num
  calc
    _ = (η.map (fun m => ∑ s∈range m, Real.sin (θ*((s+1:ℝ)-(l:ℝ))))).sum := by
      congr 1
      apply List.map_congr_left
      intro m _
      apply sum_congr rfl
      intro s _
      congr 1
      rw [hmean]
      dsimp only [θ]
      rw [hcast]
      ring
    _ = 0 := hs

end
end Carnevale
```

### `NonrectangleCore.lean`

```lean
import SecondPoleSine

namespace Carnevale
noncomputable section
open Finset

 theorem triangular_double (m : ℕ) : 2*(m*(m+1)/2)=m*(m+1) := by
  rw [← triangle_sum]
  induction m with
  | zero => simp
  | succ m ih => rw [sum_range_succ]; nlinarith

 theorem weight_balance_real (η : List ℕ) :
    2*(weight η:ℝ) = (η.map (fun m : ℕ => (m:ℝ)^2)).sum+(η.sum:ℝ) := by
  induction η with
  | nil => simp [weight]
  | cons m ms ih =>
    have ht : (2:ℝ)*(m*(m+1)/2:ℕ)=(m:ℝ)*((m:ℝ)+1) := by
      exact_mod_cast triangular_double m
    simp only [weight, List.map_cons, List.sum_cons, Nat.cast_add] at *
    nlinarith

/-- This is the nonrectangular exclusion under the geometric range condition.
The remaining classification work is the exceptional large-part casework. -/
theorem bounded_parts_equal (η : List ℕ) (hp : ∀ m∈η,0<m) (hne : η≠[])
    (hN : 4≤η.sum) (he : Even η.sum) (hd : η.sum ∣ weight η)
    (hL : L η (η.sum/2)=0) (hmax : ∀m∈η, m≤η.sum-2) :
    ∃ m : ℕ, ∀ n∈η,n=m := by
  by_contra hvar
  let z : ℝ := Real.pi/((η.sum:ℝ)-2)
  have hdpos : 0<(η.sum:ℝ)-2 := by
    have hh : (4:ℝ)≤(η.sum:ℝ) := by exact_mod_cast hN
    linarith
  have hz : 0<z := div_pos Real.pi_pos hdpos
  have hangle : ∀m∈η,(m:ℝ)*z≤Real.pi := by
    intro m hm
    have hle : (m:ℝ)≤(η.sum:ℝ)-2 := by
      have hh := hmax m hm
      have hh' : (m:ℝ)+2≤(η.sum:ℝ) := by exact_mod_cast (show m+2≤η.sum by omega)
      linarith
    dsimp only [z]
    rw [← mul_div_assoc, div_le_iff₀ hdpos]
    nlinarith [Real.pi_pos]
  have hn : (η.sum:ℝ)≠0 := Nat.cast_ne_zero.mpr (by omega)
  have hmean : (((η.map (fun m : ℕ => (m:ℝ)^2)).sum)/(η.sum:ℝ)+1)/2 =
      (weight η:ℝ)/(η.sum:ℝ) := by
    have hb := weight_balance_real η
    field_simp
    nlinarith
  have hs := strict_sine_sum η hp hne hvar z hz hangle
  dsimp only at hs
  have hzero : (η.map (fun m => ∑ s∈range m,
      Real.sin (2*z*((s+1:ℝ)-
        (((η.map (fun m : ℕ => (m:ℝ)^2)).sum)/(η.sum:ℝ)+1)/2)))).sum=0 := by
    convert second_pole_sine η hN he hd hL using 1
    congr 1
    apply List.map_congr_left
    intro m _
    apply sum_congr rfl
    intro s _
    congr 1
    rw [hmean]
    dsimp only [z]
    ring
  linarith

end
end Carnevale
```

### `CompositionArithmetic.lean`

```lean
import NonrectangleCore
import Mathlib.Algebra.Order.BigOperators.Group.List

namespace Carnevale
noncomputable section

 theorem weight_append (xs ys : List ℕ) : weight (xs++ys)=weight xs+weight ys := by
  simp [weight]

 theorem weight_small_sum (ms : List ℕ) (h : ms.sum≤1) : weight ms=ms.sum := by
  induction ms with
  | nil => simp [weight]
  | cons m ms ih =>
    have hm : m≤1 := by simp only [List.sum_cons] at h; omega
    have hs : ms.sum≤1 := by simp only [List.sum_cons] at h; omega
    change m*(m+1)/2+weight ms=m+ms.sum
    rw [ih hs]
    interval_cases m <;> norm_num

 theorem part_le_sum {η : List ℕ} {m : ℕ} (hm : m∈η) : m≤η.sum := by
  exact List.le_sum_of_mem hm

 theorem large_part_weight (η : List ℕ) (m : ℕ) (hm : m∈η) (hbig : η.sum≤m+1) :
    weight η=m*(m+1)/2+(η.sum-m) := by
  obtain ⟨xs,ys,rfl⟩ := List.mem_iff_append.mp hm
  have hs : (xs++ys).sum≤1 := by simp only [List.sum_append, List.sum_cons] at *; omega
  have hw := weight_small_sum (xs++ys) hs
  simp only [weight, List.map_append, List.sum_append, List.map_cons, List.sum_cons] at *
  omega

 theorem large_parts_excluded (η : List ℕ) (hN : 4≤η.sum) (he : Even η.sum)
    (hd : η.sum∣weight η) (m : ℕ) (hm : m∈η) : m≤η.sum-2 := by
  by_contra hn
  have hmle := part_le_sum hm
  have hbig : η.sum≤m+1 := by omega
  have hw := large_part_weight η m hm hbig
  have ht := triangular_double m
  obtain ⟨l,hl⟩ := hd
  by_cases htop : m=η.sum
  · rw [htop] at hw ht
    simp only [Nat.sub_self, add_zero] at hw
    have heq : η.sum*(2*l)=η.sum*(η.sum+1) := by nlinarith
    have heq' := Nat.eq_of_mul_eq_mul_left (by omega : 0<η.sum) heq
    obtain ⟨k,hk⟩ := he
    omega
  · have hmN : m=η.sum-1 := by omega
    have hrem : η.sum-m=1 := by omega
    rw [hrem] at hw
    have h2 : 2*weight η=η.sum*(η.sum-1)+2 := by
      calc
        _ = m*(m+1)+2 := by nlinarith
        _ = _ := by rw [show m+1=η.sum by omega, hmN]; ring
    have hdiv : η.sum∣2*weight η := dvd_mul_of_dvd_right ⟨l,hl⟩ 2
    rw [h2] at hdiv
    have hd2 : η.sum∣2 :=
      (Nat.dvd_add_iff_right (dvd_mul_right η.sum (η.sum-1))).mpr hdiv
    have := Nat.le_of_dvd (by omega : 0<2) hd2
    omega

 theorem sum_two_parts_equal (η : List ℕ) (hp : ∀m∈η,0<m) (hN : η.sum=2)
    (hd : η.sum∣weight η) : ∀m∈η,m=1 := by
  intro m hm
  have hmle := part_le_sum hm
  have hmpos := hp m hm
  by_contra hn
  have hm2 : m=2 := by omega
  have hw := large_part_weight η m hm (by omega)
  rw [hm2,hN] at hw
  norm_num at hw
  rw [hN,hw] at hd
  norm_num at hd

 theorem uniform_rectangle (η : List ℕ) (hne : η≠[]) (hp : ∀m∈η,0<m)
    (he : Even η.sum) (hd : η.sum∣weight η) (hu : ∃m,∀n∈η,n=m) :
    ∃m r : ℕ, 0<m ∧ 0<r ∧ η=List.replicate r m ∧ Odd m ∧ Even r := by
  obtain ⟨m,hm⟩ := hu
  have hrep : η=List.replicate η.length m := List.eq_replicate_of_mem hm
  have hr : 0<η.length := List.length_pos_iff.mpr hne
  have hmem : m∈η := by rw [hrep]; exact List.mem_replicate.mpr ⟨by omega,rfl⟩
  have hmpos := hp m hmem
  have hsum : η.sum=η.length*m := by conv_lhs => rw [hrep]; simp
  have hw : weight η=η.length*(m*(m+1)/2) := by
    conv_lhs => rw [hrep]
    simp [weight]
  obtain ⟨l,hl⟩ := hd
  have ht := triangular_double m
  have heq : η.length*m*(m+1)=η.length*m*(2*l) := by nlinarith [hw,hsum]
  have hcancel := Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hr hmpos) heq
  have hom : Odd m := by
    refine ⟨l-1, ?_⟩
    omega
  have hnot : ¬Even m := by
    rintro ⟨k,hk⟩
    obtain ⟨j,hj⟩ := hom
    omega
  have her : Even η.length :=
    (Nat.even_mul.mp (hsum ▸ he)).resolve_right hnot
  exact ⟨m,η.length,hmpos,hr,hrep,hom,her⟩

end
end Carnevale
```

### `NonrectangleClassification.lean`

```lean
import CompositionArithmetic

namespace Carnevale
noncomputable section

/-- All nonrectangles are excluded by the two pole conditions and the strict
sine sum. This classification itself does not need the source formula. -/
theorem zero_slope_classification (η : List ℕ) (hne : η≠[]) (hp : ∀m∈η,0<m)
    (a : ℕ) (ha : 0<a) (hL : L η a=0) :
    ∃m r : ℕ,0<m ∧ 0<r ∧ η=List.replicate r m ∧ Odd m ∧ Even r := by
  have hmid := slope_midpoint_unconditional η a ha hL
  have hEven : Even η.sum := ⟨a,by omega⟩
  have hd := first_pole η a ha hmid hL
  apply uniform_rectangle η hne hp hEven hd
  by_cases htwo : η.sum=2
  · exact ⟨1,sum_two_parts_equal η hp htwo hd⟩
  · have hN : 4≤η.sum := by omega
    have hhalf : η.sum/2=a := by omega
    apply bounded_parts_equal η hp hne hN hEven hd
    · simpa only [hhalf] using hL
    · exact large_parts_excluded η hN hEven hd

 theorem nonrectangle_excluded (_H : SourceFormula10) (η : List ℕ)
    (hne : η≠[]) (hp : ∀m∈η,0<m) (a : ℕ) (ha : 0<a) (hL : L η a=0) :
    ∃m r : ℕ,0<m ∧ 0<r ∧ η=List.replicate r m ∧ Odd m ∧ Even r :=
  zero_slope_classification η hne hp a ha hL

end
end Carnevale
```

### `BinomialNecessity.lean`

```lean
import NonrectangleClassification
import BinomialReduction

namespace Carnevale
noncomputable section

/-- The entire necessity direction for literal binomial divisors, including
its unique exponent. The sole external input is the published source formula. -/
theorem binomial_divisor_necessity (H : SourceFormula10) (η : List ℕ)
    (hne : η≠[]) (hp : ∀m∈η,0<m) (a : ℕ)
    (hd : (1+x^a*y) ∣ denertPoly η) :
    (∃m r : ℕ,0<m ∧ 0<r ∧ η=List.replicate r m ∧ Odd m ∧ Even r) ∧
      η.sum=2*a := by
  have ha := binomial_slope_pos H η hne hp a hd
  have hroot := binomial_root (denertPoly η) a hd
  have hL := (slope_zero_iff H η hne hp a).mp hroot
  exact ⟨zero_slope_classification η hne hp a ha hL,
    slope_midpoint_unconditional η a ha hL⟩

end
end Carnevale
```

### `Stage2Audit.lean`

```lean
import Blueprint
import IntegralGaussian
import BinomialReduction
import NonrectangleClassification
import BinomialNecessity

namespace Carnevale.Stage2
noncomputable section

theorem M1_proved : Carnevale.Blueprint.M1 := Carnevale.inverseDenominator_coeff
theorem M2_proved : Carnevale.Blueprint.M2 := Carnevale.formula_to_rational
theorem M3_proved : Carnevale.Blueprint.M3 := Carnevale.slope_zero_iff
theorem M4_proved : Carnevale.Blueprint.M4 := Carnevale.extreme_coefficients
theorem M6_proved : Carnevale.Blueprint.M6 := Carnevale.axes_one
theorem U2_proved : Carnevale.Blueprint.U2 := Carnevale.at_most_one
theorem P2_proved : Carnevale.Blueprint.P2 := Carnevale.slope_midpoint
theorem P3_proved : Carnevale.Blueprint.P3 := Carnevale.first_pole
theorem P4_proved : Carnevale.Blueprint.P4 := Carnevale.second_pole
theorem P5_proved : Carnevale.Blueprint.P5 := Carnevale.second_pole_sine
theorem T6_proved : Carnevale.Blueprint.T6 := Carnevale.nonrectangle_excluded

end
end Carnevale.Stage2

#eval Lean.versionString
#check Carnevale.Stage2.M1_proved
#print axioms Carnevale.Stage2.M1_proved
#check Carnevale.Stage2.M2_proved
#print axioms Carnevale.Stage2.M2_proved
#check Carnevale.Stage2.M3_proved
#print axioms Carnevale.Stage2.M3_proved
#check Carnevale.Stage2.M4_proved
#print axioms Carnevale.Stage2.M4_proved
#check Carnevale.Stage2.M6_proved
#print axioms Carnevale.Stage2.M6_proved
#check Carnevale.Stage2.U2_proved
#print axioms Carnevale.Stage2.U2_proved
#check Carnevale.Stage2.P2_proved
#print axioms Carnevale.Stage2.P2_proved
#check Carnevale.Stage2.P3_proved
#print axioms Carnevale.Stage2.P3_proved
#check Carnevale.Stage2.P4_proved
#print axioms Carnevale.Stage2.P4_proved
#check Carnevale.Stage2.P5_proved
#print axioms Carnevale.Stage2.P5_proved
#check Carnevale.Stage2.T6_proved
#print axioms Carnevale.Stage2.T6_proved
#check Carnevale.fieldInverse_coeff
#print axioms Carnevale.fieldInverse_coeff
#check Carnevale.qGaussian_product
#print axioms Carnevale.qGaussian_product
#check Carnevale.qCoeffHom_injective
#print axioms Carnevale.qCoeffHom_injective
#check Carnevale.bivar_series_compat
#print axioms Carnevale.bivar_series_compat
#check Carnevale.formula_to_rational_cleared
#print axioms Carnevale.formula_to_rational_cleared
#check Carnevale.formula_to_rational
#print axioms Carnevale.formula_to_rational
#check Carnevale.slope_zero_iff
#print axioms Carnevale.slope_zero_iff
#check Carnevale.axes_one
#print axioms Carnevale.axes_one
#check Carnevale.unitary_exponents_pos
#print axioms Carnevale.unitary_exponents_pos
#check Carnevale.binomial_root
#print axioms Carnevale.binomial_root
#check Carnevale.at_most_one
#print axioms Carnevale.at_most_one
#check Carnevale.polynomial_sum_div_clears
#print axioms Carnevale.polynomial_sum_div_clears
#check Carnevale.cleared_sum_isolated
#print axioms Carnevale.cleared_sum_isolated
#check Carnevale.slope_midpoint_unconditional
#print axioms Carnevale.slope_midpoint_unconditional
#check Carnevale.first_pole
#print axioms Carnevale.first_pole
#check Carnevale.extreme_coefficients
#print axioms Carnevale.extreme_coefficients
#check Carnevale.primitive_second_denominators
#print axioms Carnevale.primitive_second_denominators
#check Carnevale.second_pole
#print axioms Carnevale.second_pole
#check Carnevale.centered_level_zero
#print axioms Carnevale.centered_level_zero
#check Carnevale.second_pole_sine
#print axioms Carnevale.second_pole_sine
#check Carnevale.bounded_parts_equal
#print axioms Carnevale.bounded_parts_equal
#check Carnevale.large_parts_excluded
#print axioms Carnevale.large_parts_excluded
#check Carnevale.zero_slope_classification
#print axioms Carnevale.zero_slope_classification

#check Carnevale.binomial_divisor_necessity
#print axioms Carnevale.binomial_divisor_necessity
```

### `UnitaryRootConstraints.lean`

```lean
import UnitReductionAxes
import LiteralFoundation

namespace Carnevale
noncomputable section

 def origin : Bivar →+* ℤ := MvPolynomial.eval₂Hom (RingHom.id ℤ) (fun _ => 0)
 def allOne : Bivar →+* ℤ := MvPolynomial.eval₂Hom (RingHom.id ℤ) (fun _ => 1)

 theorem origin_eq (P : Bivar) : origin P=(specializeYZero P).eval 0 := by
  have hh : origin = (Polynomial.evalRingHom 0).comp
      (MvPolynomial.eval₂Hom (Int.castRingHom (Polynomial ℤ))
        (fun i : Fin 2 => if i=0 then Polynomial.X else 0)) := by
    apply MvPolynomial.ringHom_ext
    · intro n; simp [origin]
    · intro i; fin_cases i <;> simp [origin]
  exact DFunLike.congr_fun hh P

 theorem denert_allOne_ne_zero (η : List ℕ) : allOne (denertPoly η)≠0 := by
  have hh : allOne (denertPoly η)=((multisetPerms η).card:ℤ) := by
    simp [allOne, denertPoly, x, y]
  rw [hh]
  exact_mod_cast Nat.ne_of_gt (Finset.card_pos.mpr ⟨baseWord η, baseWord_mem η⟩)

/-- Necessary root/content constraints for the remaining full unitary reduction. -/
theorem unitary_polynomial_constraints (H : SourceFormula10) (η : List ℕ)
    (hne : η≠[]) (hp : ∀ m∈η, 0<m) (f : Bivar)
    (hu : IsUnitary f) (hd : f ∣ denertPoly η) :
    ∃ (F : Polynomial ℤ) (a b : ℕ), 0<a ∧ 0<b ∧
      f=F.eval₂ (Int.castRingHom Bivar) (x^a*y^b) ∧
      (F.eval 0=1 ∨ F.eval 0= -1) ∧ F.eval 1≠0 ∧
      ∀ z : ℂ, F.eval₂ (Int.castRingHom ℂ) z=0 → ‖z‖=1 := by
  obtain ⟨F,a,b,ha,hb,he,hroots⟩ := unitary_exponents_pos H η hne hp f hu hd
  have hO : origin (denertPoly η)=1 := by
    rw [origin_eq, (axes_one H η hne hp).1, Polynomial.eval_one]
  have hF0 : origin f=F.eval 0 := by
    simp [he, Polynomial.eval₂_eq_sum_range, Polynomial.eval_eq_sum_range, origin, x, y, Nat.ne_of_gt ha]
  have hF1 : allOne f=F.eval 1 := by
    simp [he, Polynomial.eval₂_eq_sum_range, Polynomial.eval_eq_sum_range, allOne, x, y]
  have hc : IsUnit (F.eval 0) := by
    apply isUnit_iff_dvd_one.mpr
    simpa only [hO, hF0] using map_dvd origin hd
  have hc' : F.eval 0=1 ∨ F.eval 0= -1 := Int.isUnit_iff.mp hc
  have h1 : F.eval 1≠0 := by
    intro hz
    obtain ⟨g,hg⟩ := map_dvd allOne hd
    rw [hF1, hz, zero_mul] at hg
    exact denert_allOne_ne_zero η hg
  exact ⟨F,a,b,ha,hb,he,hc',h1,hroots⟩

end
end Carnevale
```

### `DoubleRootBridge.lean`

```lean
import BinomialReduction
import Mathlib.Algebra.Polynomial.Derivative

namespace Carnevale
noncomputable section
open Finset Polynomial

/-- A polynomial Wronskian identity, before any specialization. -/
theorem punctured_wronskian (n j : ℕ) (hj : j∈range (n+1)) :
    denominatorPoly n * (puncturedDenominator n j).derivative -
      (denominatorPoly n).derivative * puncturedDenominator n j =
    C (q^j) * (puncturedDenominator n j)^2 := by
  rw [← denominatorPoly_erase n j hj, derivative_mul]
  simp only [derivative_sub, derivative_one, derivative_C_mul, derivative_X,
    mul_one, zero_sub]
  ring

/-- Both zero values force the derivative partial-fraction sum to vanish.
All denominators are required nonzero at the specialization. -/
theorem double_root_partial_fractions (H : SourceFormula10) (η : List ℕ)
    (hne : η≠[]) (hp : ∀ m∈η, 0<m) (t : K)
    (ht : ∀ j∈range (η.sum+1), 1-t*q^j≠0)
    (h0 : (A η).eval t=0) (h1 : (A η).derivative.eval t=0) :
    ∑ j∈range (η.sum+1), c η j*q^j/(1-t*q^j)^2 = 0 := by
  have hD : (denominatorPoly η.sum).eval t≠0 := by
    simpa only [denominatorPoly, eval_prod, eval_sub, eval_one, eval_mul, eval_C,
      eval_X, mul_comm (q^_) t] using prod_ne_zero_iff.mpr ht
  have hw : denominatorPoly η.sum * (A η).derivative -
      (denominatorPoly η.sum).derivative * A η =
      ∑ j∈range (η.sum+1), C (c η j/E η)*C (q^j)*
        (puncturedDenominator η.sum j)^2 := by
    rw [formula_to_rational_cleared H η hne hp]
    simp only [rationalNumerator, derivative_sum, derivative_C_mul,
      mul_sum]
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro j hj
    calc
      _ = C (c η j/E η)*(denominatorPoly η.sum * (puncturedDenominator η.sum j).derivative -
          (denominatorPoly η.sum).derivative*puncturedDenominator η.sum j) := by ring
      _ = _ := by rw [punctured_wronskian _ _ hj]; ring
  have he := congrArg (eval t) hw
  simp only [eval_sub, eval_mul, h0, h1, mul_zero, sub_self, eval_finsetSum,
    eval_C, eval_pow] at he
  have he' := congrArg (fun z : K => z * E η / ((denominatorPoly η.sum).eval t)^2) he.symm
  rw [sum_mul, sum_div, zero_mul, zero_div] at he'
  convert he' using 1
  apply sum_congr rfl
  intro j hj
  have hd := congrArg (eval t) (denominatorPoly_erase η.sum j hj)
  simp only [eval_mul, eval_sub, eval_one, eval_C, eval_X] at hd
  have hP : (puncturedDenominator η.sum j).eval t ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hd
    exact hD hd.symm
  rw [← hd]
  field_simp [hP, E_ne_zero η, ht j hj, mul_comm (q^j) t]

 theorem binomial_square_double_root (P : Bivar) (a : ℕ)
    (hd : (1+x^a*y)^2 ∣ P) :
    (bivarToK P).eval (-q^(-(a:ℤ)))=0 ∧
      (bivarToK P).derivative.eval (-q^(-(a:ℤ)))=0 := by
  have hlin : (bivarToK (1+x^a*y)).eval (-q^(-(a:ℤ)))=0 :=
    binomial_root (1+x^a*y) a (dvd_refl _)
  obtain ⟨g,hg⟩ := map_dvd bivarToK hd
  rw [map_pow] at hg
  constructor
  · rw [hg, eval_mul, eval_pow, hlin, zero_pow (by decide : 2≠0), zero_mul]
  · rw [hg, derivative_mul, derivative_pow]
    simp only [eval_add, eval_mul, eval_pow, hlin]
    ring

 theorem squared_slope_sum_zero (H : SourceFormula10) (η : List ℕ)
    (hne : η≠[]) (hp : ∀ m∈η, 0<m) (a : ℕ)
    (hd : (1+x^a*y)^2 ∣ denertPoly η) :
    ∑ j∈range (η.sum+1), c η j*q^j/(1+q^((j:ℤ)-(a:ℤ)))^2=0 := by
  obtain ⟨h0,h1⟩ := binomial_square_double_root (denertPoly η) a hd
  have hden (j : ℕ) : 1-(-q^(-(a:ℤ)))*q^j = 1+q^((j:ℤ)-(a:ℤ)) := by
    rw [zpow_sub₀ q_ne_zero, zpow_natCast, zpow_natCast, zpow_neg, zpow_natCast]
    ring
  simpa only [hden] using double_root_partial_fractions H η hne hp
    (-q^(-(a:ℤ))) (fun j _ => by rw [hden]; exact slope_denominator_ne_zero j a) h0 h1

end
end Carnevale
```

### `DoublePoleEncoding.lean`

```lean
import DoubleRootBridge
import FirstPole

namespace Carnevale
noncomputable section
open Finset Polynomial

 def doublePoleNumerator (η : List ℕ) (a j : ℕ) : Polynomial ℚ :=
  X^(j+2*a)*coefficientPolynomial η j
 def doublePoleDenominator (a j : ℕ) : Polynomial ℚ := (poleDenominator a j)^2
 def doublePairNumerator (η : List ℕ) (a j : ℕ) : Polynomial ℚ :=
  if j=0 then X^(2*a)*(1+coefficientPolynomial η η.sum) else doublePoleNumerator η a j
 def doublePairDenominator (a j : ℕ) : Polynomial ℚ :=
  if j=0 then (X^a+1)^2 else doublePoleDenominator a j

 theorem double_pole_sum (η : List ℕ) (a : ℕ) :
    (∑ j∈range (η.sum+1), c η j*q^j/(1+q^((j:ℤ)-(a:ℤ)))^2) =
    ∑ j∈range (η.sum+1),
      algebraMap (Polynomial ℚ) K (doublePoleNumerator η a j) /
        algebraMap (Polynomial ℚ) K (doublePoleDenominator a j) := by
  apply sum_congr rfl
  intro j _
  simp only [doublePoleNumerator, doublePoleDenominator, poleDenominator, map_pow,
    map_mul, map_add, RatFunc.algebraMap_X, show RatFunc.X=q from rfl,
    coefficientPolynomial_map]
  rw [negative_exponent_denominator q q_ne_zero j a]
  field_simp
  ring

 theorem double_pair_sum (η : List ℕ) (a : ℕ) (ha : 0<a)
    (hN : η.sum=2*a)
    (hL : (∑ j∈range (η.sum+1), c η j*q^j/(1+q^((j:ℤ)-(a:ℤ)))^2)=0) :
    ∑ j∈range η.sum, algebraMap (Polynomial ℚ) K (doublePairNumerator η a j) /
      algebraMap (Polynomial ℚ) K (doublePairDenominator a j)=0 := by
  let f (j : ℕ) : K := algebraMap (Polynomial ℚ) K (doublePoleNumerator η a j) /
    algebraMap (Polynomial ℚ) K (doublePoleDenominator a j)
  let g (j : ℕ) : K := algebraMap (Polynomial ℚ) K (doublePairNumerator η a j) /
    algebraMap (Polynomial ℚ) K (doublePairDenominator a j)
  have h0 : 0∈range η.sum := by simp; omega
  have hs : (∑ j∈range η.sum, f j)+f η.sum=0 := by
    rw [← sum_range_succ, ← double_pole_sum]
    exact hL
  have hpair : g 0 = f 0+f η.sum := by
    simp only [g, f, doublePairNumerator, doublePairDenominator, ↓reduceIte,
      doublePoleNumerator, doublePoleDenominator, poleDenominator, map_add, map_mul,
      map_pow, map_one, RatFunc.algebraMap_X, coefficientPolynomial_map, coefficient_zero,
      zero_add, pow_zero, mul_one]
    change q^(2*a)*(1+c η η.sum)/(q^a+1)^2 =
      q^(2*a)/(q^a+1)^2+q^(η.sum+2*a)*c η η.sum/(q^a+q^η.sum)^2
    rw [hN, show 2*a=a+a by omega, pow_add, pow_add]
    field_simp [q_ne_zero, power_add_power_ne_zero a 0]
    ring
  have hreg : (∑ j∈(range η.sum).erase 0, g j)=
      ∑ j∈(range η.sum).erase 0, f j := by
    apply sum_congr rfl
    intro j hj
    simp only [g, f, doublePairNumerator, doublePairDenominator,
      ite_eq_right (ne_of_mem_erase hj)]
  change (∑ j∈range η.sum, g j)=0
  rw [← sum_erase_add (range η.sum) g h0, hreg, hpair, ← add_assoc,
    sum_erase_add (range η.sum) f h0]
  exact hs

 theorem double_pair_cleared (η : List ℕ) (a : ℕ) (ha : 0<a)
    (hN : η.sum=2*a)
    (hL : (∑ j∈range (η.sum+1), c η j*q^j/(1+q^((j:ℤ)-(a:ℤ)))^2)=0) :
    ∑ j∈range η.sum, doublePairNumerator η a j *
      ∏ k∈(range η.sum).erase j, doublePairDenominator a k = 0 := by
  apply polynomial_sum_div_clears (algebraMap (Polynomial ℚ) K)
    (RatFunc.algebraMap_injective ℚ) (range η.sum) (doublePairNumerator η a)
    (doublePairDenominator a)
  · intro j _
    by_cases hj : j=0
    · simpa [doublePairDenominator, hj, q] using pow_ne_zero 2 (power_add_power_ne_zero a 0)
    · simpa [doublePairDenominator, hj, doublePoleDenominator, poleDenominator, q] using
        pow_ne_zero 2 (power_add_power_ne_zero a j)
  · exact double_pair_sum η a ha hN hL

end
end Carnevale
```

### `NoSquare.lean`

```lean
import DoublePoleEncoding

namespace Carnevale
noncomputable section
open Finset Polynomial

/-- Multiplicity is excluded using a double pole, independently of Simion. -/
theorem no_square (H : SourceFormula10) (η : List ℕ)
    (hne : η≠[]) (hp : ∀ m∈η, 0<m) (a : ℕ) :
    ¬ (1+x^a*y)^2 ∣ denertPoly η := by
  intro hd
  have hdiv : 1+x^a*y ∣ denertPoly η := (dvd_pow_self _ (by decide : 2≠0)).trans hd
  have ha := binomial_slope_pos H η hne hp a hdiv
  have hN := binomial_slope_midpoint H η hne hp a hdiv
  have hL := (slope_zero_iff H η hne hp a).mp (binomial_root _ a hdiv)
  have hS := first_pole η a ha hN hL
  let ζ : ℂ := Complex.exp (2*Real.pi*Complex.I/η.sum)
  have hpos : 0<η.sum := by omega
  have hζ : IsPrimitiveRoot ζ η.sum := Complex.isPrimitiveRoot_exp _ (Nat.ne_of_gt hpos)
  have hhalf : ζ^a = -1 := primitive_even_half ha (hN ▸ hζ)
  let ev : Polynomial ℚ →+* ℂ := eval₂RingHom (Rat.castHom ℂ) ζ
  have hevX : ev X=ζ := eval₂_X _ _
  have hz : ev (doublePairNumerator η a 0)=0 := by
    apply cleared_sum_isolated ev (range η.sum) (doublePairNumerator η a)
      (doublePairDenominator a) 0 (by simpa using hpos)
    · simp only [doublePairDenominator, ↓reduceIte, map_pow, map_add, map_one, hevX,
        hhalf, neg_add_cancel, zero_pow (by decide : 2≠0)]
    · intro j hj hj0
      simp only [doublePairDenominator, ite_eq_right hj0, doublePoleDenominator, map_pow,
        poleDenominator, map_add, hevX]
      apply pow_ne_zero 2
      have hpow := hζ.pow_ne_one_of_pos_of_lt hj0 (mem_range.mp hj)
      intro he
      apply hpow
      rw [hhalf] at he
      linear_combination he
    · exact double_pair_cleared η a ha hN (squared_slope_sum_zero H η hne hp a hd)
  have htop : ev (coefficientPolynomial η η.sum)=1 := by
    have he : Even η.sum := ⟨a, by omega⟩
    simp [ev, coefficientPolynomial_top_formula, he.neg_one_pow,
      (hζ.pow_eq_one_iff_dvd _).mpr hS]
  have hz' : ζ^(2*a)*(1+(1:ℂ))=0 := by
    simpa only [doublePairNumerator, ↓reduceIte, map_mul, map_pow, hevX,
      map_add, map_one, htop] using hz
  rw [← hN, hζ.pow_eq_one] at hz'
  norm_num at hz'

end
end Carnevale
```

### `IntegralBinomial.lean`

```lean
import IntegralGaussian
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Div

namespace Carnevale
noncomputable section
open Polynomial

/-- A constant-one linear factor descends through an injective coefficient map.
Reversal turns it into a monic factor, so no fraction-field assumption is needed. -/
theorem integral_linear_factor {R F : Type*} [CommRing R] [IsDomain R] [Field F]
    (f : R →+* F) (hf : Function.Injective f) (u : R) (hu : f u≠0) (P : Polynomial R)
    (hroot : P.eval₂ f (-(f u)⁻¹)=0) : 1+C u*X ∣ P := by
  let z : F := -(f u)⁻¹
  have hz : z≠0 := neg_ne_zero.mpr (inv_ne_zero hu)
  let : Invertible z := invertibleOfNonzero hz
  have hrev : (reflect P.natDegree P).eval₂ f (-(f u))=0 := by
    have hh := (eval₂_reflect_eq_zero_iff f z P.natDegree P le_rfl).mpr hroot
    simpa [z, invOf_eq_inv] using hh
  have hR : (reflect P.natDegree P).eval (-u)=0 := by
    apply hf
    rw [map_zero]
    simpa only [← eval₂_at_apply, map_neg] using hrev
  have hd : X+C u ∣ reflect P.natDegree P := by
    simpa only [sub_neg_eq_add, C_neg, sub_neg_eq_add] using
      (dvd_iff_isRoot.mpr hR : X-C (-u) ∣ reflect P.natDegree P)
  obtain ⟨Q,hQ⟩ := hd
  by_cases hP : P=0
  · simp [hP]
  have hQ0 : Q≠0 := by
    intro hz
    rw [hz, mul_zero] at hQ
    have hh := congrArg (reflect P.natDegree) hQ
    exact hP (by simpa only [reflect_reflect, reflect_zero] using hh)
  have hdeg : 1+Q.natDegree≤P.natDegree := by
    have hh := natDegree_reflect_le (p := P) (N := P.natDegree)
    rw [hQ, natDegree_mul (monic_X_add_C u).ne_zero hQ0, natDegree_X_add_C] at hh
    simpa only [max_self] using hh
  have hN : P.natDegree=1+(P.natDegree-1) := by omega
  have hQr : Q.natDegree≤P.natDegree-1 := by omega
  have he := congrArg (reflect P.natDegree) hQ
  rw [reflect_reflect, hN, reflect_mul _ _ (by simp) hQr] at he
  have hlin : reflect 1 (X+C u)=1+C u*X := by
    simp [reflect_add, reflect_one_X, reflect_C]
  rw [hlin] at he
  exact ⟨reflect (P.natDegree-1) Q, he⟩

/-- Literal integer bivariate polynomials, viewed as polynomials in y over ℤ[x]. -/
def bivarIntegral : Bivar →+* Polynomial (Polynomial ℤ) :=
  MvPolynomial.eval₂Hom (Int.castRingHom (Polynomial (Polynomial ℤ)))
    (fun i => if i=0 then C X else X)

def integralToBivar : Polynomial (Polynomial ℤ) →+* Bivar :=
  eval₂RingHom (eval₂RingHom (Int.castRingHom Bivar) x) y

theorem integral_retraction (P : Bivar) : integralToBivar (bivarIntegral P)=P := by
  have hh : integralToBivar.comp bivarIntegral = RingHom.id Bivar := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [integralToBivar, bivarIntegral]
    · intro i
      fin_cases i <;> simp [integralToBivar, bivarIntegral, x, y]
  exact DFunLike.congr_fun hh P

theorem bivarIntegral_map (P : Bivar) : (bivarIntegral P).map qCoeffHom=bivarToK P := by
  have hh : (Polynomial.mapRingHom qCoeffHom).comp bivarIntegral = bivarToK := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [bivarIntegral, bivarToK, qCoeffHom]
    · intro i
      fin_cases i <;> simp [bivarIntegral, bivarToK]
  exact DFunLike.congr_fun hh P

/-- The root in ℚ(q) yields divisibility in the literal ring ℤ[x,y]. -/
theorem integral_factor (P : Bivar) (a : ℕ)
    (h : (bivarToK P).eval (-q^(-(a:ℤ)))=0) : (1+x^a*y) ∣ P := by
  have hh : (bivarIntegral P).eval₂ qCoeffHom (-(qCoeffHom (X^a))⁻¹)=0 := by
    rw [← eval_map, bivarIntegral_map]
    simpa [zpow_neg, zpow_natCast] using h
  have hd := integral_linear_factor qCoeffHom qCoeffHom_injective (X^a)
    (by simpa using pow_ne_zero a q_ne_zero) (bivarIntegral P) hh
  have hm := map_dvd integralToBivar hd
  rw [integral_retraction] at hm
  have hc : integralToBivar (C (X^a))=x^a := by
    change (C (X^a)).eval₂ (eval₂RingHom (Int.castRingHom Bivar) x) y=x^a
    rw [eval₂_C]
    simp
  have hx : integralToBivar X=y := by simp [integralToBivar]
  simpa only [map_add, map_one, map_mul, hc, hx] using hm

end
end Carnevale
```

### `RectangleReflection.lean`

```lean
import BlockReflection

namespace Carnevale
noncomputable section
open Finset Polynomial

 theorem rectangle_inverse_comp (m r : ℕ) :
    blockAt (List.replicate r m) q⁻¹ =
      (blockAt (List.replicate r m) q).comp (C (q^(-((m+1:ℕ):ℤ)))*X) := by
  have hpart : (∏ s∈range m, (1-C ((q⁻¹)^(s+1))*X)) =
      (∏ s∈range m, (1-C (q^(s+1))*X)).comp (C (q^(-((m+1:ℕ):ℤ)))*X) := by
    rw [Polynomial.prod_comp]
    trans ∏ s∈range m, (1-C (q^(m-1-s+1))*X).comp (C (q^(-((m+1:ℕ):ℤ)))*X)
    swap
    · exact prod_range_reflect (fun s : ℕ => (1-C (q^(s+1))*X).comp
        (C (q^(-((m+1:ℕ):ℤ)))*X)) m
    apply prod_congr rfl
    intro s hs
    have hpow : q^(m-1-s+1)*q^(-((m+1:ℕ):ℤ)) = (q⁻¹)^(s+1) := by
      rw [← zpow_natCast q, ← zpow_add₀ q_ne_zero]
      have hexp : ((m-1-s+1:ℕ):ℤ)+ -((m+1:ℕ):ℤ) = -((s+1:ℕ):ℤ) := by
        have := mem_range.mp hs
        omega
      rw [hexp]
      simp only [zpow_neg, zpow_natCast, inv_pow]
    simp only [sub_comp, one_comp, mul_comp, C_comp, X_comp]
    rw [← mul_assoc, ← C_mul, hpow]
  simp only [blockAt, List.map_replicate, List.prod_replicate, pow_comp, ← hpart]

 theorem rectangle_coeff_reflection (m r j : ℕ) (he : Even (m*r)) (hj : j≤m*r) :
    c (List.replicate r m) (m*r-j) =
      q^(weight (List.replicate r m))*c (List.replicate r m) j*
        (q^(-((m+1:ℕ):ℤ)))^j := by
  have hh := congrArg (fun p : Polynomial K => p.coeff j)
    (blockAt_reflect (List.replicate r m) q q_ne_zero)
  rw [rectangle_inverse_comp] at hh
  have hsum : (List.replicate r m).sum=m*r := by simp [Nat.mul_comm]
  rw [hsum, coeff_reflect, revAt_le hj, coeff_C_mul, comp_C_mul_X_coeff,
    he.neg_one_pow, one_mul] at hh
  change _ = q^(weight (List.replicate r m))*(c (List.replicate r m) j*_) at hh
  exact hh.trans (by ring)

 theorem rectangle_block_root (m r s : ℕ) (hr : 0<r) (hs : 0<s) (hsm : s≤m) :
    (block (List.replicate r m)).eval (q^(-(s:ℤ)))=0 := by
  simp only [block, List.map_replicate, List.prod_replicate, eval_pow]
  have hz : (∏ i∈range m, (1-C (q^(i+1))*X)).eval (q^(-(s:ℤ)))=0 := by
    rw [eval_prod]
    apply prod_eq_zero (mem_range.mpr (by omega : s-1<m))
    have hi : s-1+1=s := by omega
    simp only [eval_sub, eval_one, eval_mul, eval_C, eval_X, hi, zpow_neg, zpow_natCast]
    rw [mul_inv_cancel₀ (pow_ne_zero s q_ne_zero), sub_self]
  rw [hz, zero_pow (by omega : r≠0)]

end
end Carnevale
```

### `ShiftedSlope.lean`

```lean
import RectangleReflection

namespace Carnevale
noncomputable section
open Finset Polynomial

 def shiftedSlope (η : List ℕ) (a s : ℕ) : K :=
  ∑ j∈range (η.sum+1), c η j*((q^j)⁻¹)^s/(1+q^((j:ℤ)-(a:ℤ)))

 theorem shiftedSlope_zero (η : List ℕ) (a : ℕ) : shiftedSlope η a 0=L η a := by
  simp [shiftedSlope, L]

 theorem shiftedSlope_step (η : List ℕ) (a s : ℕ) :
    shiftedSlope η a (s+1)+(q^a)⁻¹*shiftedSlope η a s =
      (block η).eval (q^(-((s+1:ℕ):ℤ))) := by
  rw [eval_eq_sum_range' (n := η.sum+1) (Nat.lt_succ_of_le (block_degree η))]
  simp only [shiftedSlope, mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro j _
  have hd := slope_denominator_ne_zero j a
  rw [negative_exponent_denominator q q_ne_zero j a] at hd ⊢
  change c η j*((q^j)⁻¹)^(s+1)/((q^a+q^j)/q^a)+
    (q^a)⁻¹*(c η j*((q^j)⁻¹)^s/((q^a+q^j)/q^a)) =
      c η j*(q^(-((s+1:ℕ):ℤ)))^j
  have hpow : (q^(-((s+1:ℕ):ℤ)))^j = ((q^j)⁻¹)^(s+1) := by
    simp only [zpow_neg, zpow_natCast, inv_pow]
    rw [← pow_mul, ← pow_mul, Nat.mul_comm (s+1) j]
  rw [hpow, pow_succ]
  field_simp [q_ne_zero, power_add_power_ne_zero a j]

 theorem rectangle_shiftedSlope (m r a s : ℕ) (hr : 0<r) (hs : s≤m) :
    shiftedSlope (List.replicate r m) a s = (-(q^a)⁻¹)^s*L (List.replicate r m) a := by
  induction s with
  | zero => simp [shiftedSlope_zero]
  | succ s ih =>
    have hh := shiftedSlope_step (List.replicate r m) a s
    rw [rectangle_block_root m r (s+1) hr (by omega) hs, ih (by omega)] at hh
    rw [pow_succ]
    linear_combination hh

end
end Carnevale
```

### `RectangleRoot.lean`

```lean
import ShiftedSlope
import IntegralBinomial
import BinomialUnitary

namespace Carnevale
noncomputable section
open Finset Polynomial

 theorem rectangle_weight_center (m r a : ℕ) (hN : m*r=2*a) :
    weight (List.replicate r m)=a*(m+1) := by
  have hd : 2∣m*(m+1) := Nat.two_dvd_mul_add_one m
  have hh : 2*(m*(m+1)/2)=m*(m+1) := Nat.mul_div_cancel' hd
  have hw : weight (List.replicate r m)=r*(m*(m+1)/2) := by simp [weight]
  rw [hw]
  nlinarith [congrArg (fun x : ℕ => x*(m+1)) hN]

 theorem rectangle_slope_reflection (m r a : ℕ) (hN : m*r=2*a) :
    L (List.replicate r m) a = (q^a)^m*shiftedSlope (List.replicate r m) a m := by
  let η := List.replicate r m
  have hsum : η.sum=m*r := by simp [η, Nat.mul_comm]
  have he : Even (m*r) := ⟨a, by omega⟩
  have hw := rectangle_weight_center m r a hN
  have hreindex : L η a =
      ∑ j∈range (m*r+1), c η (m*r-j)/(1+q^(((m*r-j:ℕ):ℤ)-(a:ℤ))) := by
    unfold L
    rw [hsum]
    simpa only [Nat.add_sub_cancel] using (sum_range_reflect
      (fun j => c η j/(1+q^((j:ℤ)-(a:ℤ)))) (m*r+1)).symm
  rw [hreindex, shiftedSlope, mul_sum, hsum]
  apply sum_congr rfl
  intro j hj
  have hj' : j≤m*r := by have := mem_range.mp hj; omega
  rw [rectangle_coeff_reflection m r j he hj', hw]
  have hexp : (((m*r-j:ℕ):ℤ)-(a:ℤ))=(a:ℤ)-(j:ℤ) := by omega
  rw [hexp, zpow_sub₀ q_ne_zero, zpow_natCast, zpow_natCast,
    negative_exponent_denominator q q_ne_zero j a]
  have hpow : (q^(-((m+1:ℕ):ℤ)))^j = ((q^j)^(m+1))⁻¹ := by
    simp only [zpow_neg, zpow_natCast, inv_pow]
    rw [← pow_mul, Nat.mul_comm (m+1) j, pow_mul]
  rw [hpow, pow_mul]
  simp only [pow_succ, inv_pow]
  field_simp [q_ne_zero, power_add_power_ne_zero a j]
  ring_nf
  field_simp [power_add_power_ne_zero a j]

 theorem rectangle_L_zero (m r : ℕ) (hr : 0<r) (ho : Odd m) (he : Even r) :
    L (List.replicate r m) (m*r/2)=0 := by
  have hNe : Even (m*r) := he.mul_left m
  have hN : m*r=2*(m*r/2) := (Nat.mul_div_cancel' hNe.two_dvd).symm
  have hh := rectangle_slope_reflection m r (m*r/2) hN
  have hcancel : (q^(m*r/2))^m*(-(q^(m*r/2))⁻¹)^m = -1 := by
    rw [← mul_pow, mul_neg, mul_inv_cancel₀ (pow_ne_zero _ q_ne_zero), ho.neg_one_pow]
  rw [rectangle_shiftedSlope m r _ m hr le_rfl, ← mul_assoc, hcancel] at hh
  linear_combination (1/2:K)*hh

 theorem rectangle_root (H : SourceFormula10) (m r : ℕ)
    (hm : 0<m) (hr : 0<r) (ho : Odd m) (he : Even r) :
    (A (List.replicate r m)).eval (-q^(-((m*r/2:ℕ):ℤ)))=0 := by
  apply (slope_zero_iff H (List.replicate r m) (by simpa using Nat.ne_of_gt hr)
    (by intro n hn; rcases List.mem_replicate.mp hn with ⟨_, rfl⟩; exact hm) _).mpr
  exact rectangle_L_zero m r hr ho he

 theorem rectangle_factor_divides (H : SourceFormula10) (m r : ℕ)
    (hm : 0<m) (hr : 0<r) (ho : Odd m) (he : Even r) :
    rectangleFactor (m*r) ∣ denertPoly (List.replicate r m) :=
  integral_factor _ _ (rectangle_root H m r hm hr ho he)

 theorem rectangle_hasUnitaryFactor (H : SourceFormula10) (m r : ℕ)
    (hm : 0<m) (hr : 0<r) (ho : Odd m) (he : Even r) :
    HasUnitaryFactor (denertPoly (List.replicate r m)) := by
  exact ⟨rectangleFactor (m*r), binomial_isUnitary (m*r/2),
    rectangle_factor_divides H m r hm hr ho he⟩

end
end Carnevale
```

### `BinomialQuotient.lean`

```lean
import RectangleRoot
import NoSquare
import BinomialNecessity

namespace Carnevale
noncomputable section

/-- Removing an existing binomial leaves no further binomial divisor, of any slope. -/
theorem binomial_cofactor_free (H : SourceFormula10) (η : List ℕ)
    (hne : η≠[]) (hp : ∀ m∈η, 0<m) (a : ℕ) (f0 : Bivar)
    (hfac : denertPoly η=(1+x^a*y)*f0) :
    ∀ b : ℕ, ¬ (1+x^b*y) ∣ f0 := by
  intro b hb
  have ha : (1+x^a*y) ∣ denertPoly η := ⟨f0,hfac⟩
  have hbP : (1+x^b*y) ∣ denertPoly η := by rw [hfac]; exact hb.trans (dvd_mul_left _ _)
  have hab := at_most_one H η hne hp a b ha hbP
  subst b
  apply no_square H η hne hp a
  obtain ⟨g,hg⟩ := hb
  refine ⟨g, ?_⟩
  rw [hfac, hg]
  ring

 theorem rectangle_binomial_quotient (H : SourceFormula10) (m r : ℕ)
    (hm : 0<m) (hr : 0<r) (ho : Odd m) (he : Even r) :
    ∃ f0 : Bivar, denertPoly (List.replicate r m)=rectangleFactor (m*r)*f0 ∧
      ∀ b : ℕ, ¬ (1+x^b*y) ∣ f0 := by
  obtain ⟨f0,hf0⟩ := rectangle_factor_divides H m r hm hr ho he
  exact ⟨f0,hf0,binomial_cofactor_free H _ (by simpa using Nat.ne_of_gt hr)
    (by intro n hn; rcases List.mem_replicate.mp hn with ⟨_, rfl⟩; exact hm) _ f0 hf0⟩

 theorem binomial_divisor_iff (H : SourceFormula10) (η : List ℕ)
    (hne : η≠[]) (hp : ∀ m∈η, 0<m) (a : ℕ) :
    (1+x^a*y) ∣ denertPoly η ↔
      (∃ m r : ℕ, 0<m ∧ 0<r ∧ η=List.replicate r m ∧ Odd m ∧ Even r) ∧ η.sum=2*a := by
  constructor
  · exact binomial_divisor_necessity H η hne hp a
  · rintro ⟨⟨m,r,hm,hr,hη,ho,he⟩,hN⟩
    have hd := rectangle_factor_divides H m r hm hr ho he
    have hsum : η.sum=m*r := by simp [hη, Nat.mul_comm]
    have ha : m*r/2=a := by omega
    simpa only [← hη, rectangleFactor, ha] using hd

end
end Carnevale
```

### `ConditionalAssembly.lean`

```lean
import BinomialQuotient
import Blueprint

/-! This is a conditional assembly lemma, NOT the required E2 endpoint.
Blueprint.U1 is an explicit unproved antecedent, not an axiom or an instance.
The declaration `source_conjecture_351584` is deliberately absent. -/
namespace Carnevale
noncomputable section

 theorem assembly_requires_U1 (hU : Blueprint.U1)
    (H_published_CarnevaleTielker_formula10 : SourceFormula10) : Conjecture23 := by
  let H := H_published_CarnevaleTielker_formula10
  intro η hne hp
  constructor
  · constructor
    · rintro ⟨f,hu,hd⟩
      obtain ⟨a,_ha,he⟩ := hU H η hne hp f hu hd
      have hb : (1+x^a*y) ∣ denertPoly η := by
        rcases he with he|he
        · simpa only [he] using hd
        · simpa only [he, neg_dvd] using hd
      exact (binomial_divisor_necessity H η hne hp a hb).1
    · rintro ⟨m,r,hm,hr,hη,ho,he⟩
      rw [hη]
      exact rectangle_hasUnitaryFactor H m r hm hr ho he
  · intro m r hm hr hη ho he
    obtain ⟨f0,hfac,hfree⟩ := rectangle_binomial_quotient H m r hm hr ho he
    have hsum : η.sum=m*r := by simp [hη,Nat.mul_comm]
    refine ⟨f0, ?_, ?_⟩
    · simpa only [← hη, ← hsum] using hfac
    · rintro ⟨f,hu,hd⟩
      have hf0 : f0 ∣ denertPoly η := by rw [hη,hfac]; exact dvd_mul_left _ _
      obtain ⟨a,_ha,he⟩ := hU H η hne hp f hu (hd.trans hf0)
      apply hfree a
      rcases he with he|he
      · simpa only [he] using hd
      · simpa only [he, neg_dvd] using hd

end
end Carnevale
```

### `Stage3Audit.lean`

```lean
import Stage2Audit
import UnitaryRootConstraints
import ConditionalAssembly

namespace Carnevale.Stage3
noncomputable section

theorem U3_proved : Blueprint.U3 := no_square
theorem R2_proved : Blueprint.R2 := rectangle_root
theorem R3_proved : Blueprint.R3 := integral_factor

#eval Lean.versionString
#check U3_proved
#print axioms U3_proved
#check R2_proved
#print axioms R2_proved
#check R3_proved
#print axioms R3_proved
#check Carnevale.unitary_polynomial_constraints
#print axioms Carnevale.unitary_polynomial_constraints
#check Carnevale.double_root_partial_fractions
#print axioms Carnevale.double_root_partial_fractions
#check Carnevale.no_square
#print axioms Carnevale.no_square
#check Carnevale.integral_factor
#print axioms Carnevale.integral_factor
#check Carnevale.rectangle_root
#print axioms Carnevale.rectangle_root
#check Carnevale.rectangle_factor_divides
#print axioms Carnevale.rectangle_factor_divides
#check Carnevale.rectangle_hasUnitaryFactor
#print axioms Carnevale.rectangle_hasUnitaryFactor
#check Carnevale.binomial_divisor_iff
#print axioms Carnevale.binomial_divisor_iff
#check Carnevale.binomial_cofactor_free
#print axioms Carnevale.binomial_cofactor_free
#check Carnevale.rectangle_binomial_quotient
#print axioms Carnevale.rectangle_binomial_quotient
#check Carnevale.assembly_requires_U1
#print axioms Carnevale.assembly_requires_U1
#print Carnevale.Blueprint.U1
#print Carnevale.Conjecture23
#print Carnevale.SourceFormula10

end
end Carnevale.Stage3
```

### `ComplexPoleIdentity.lean`

```lean
import TopCoefficient
import SlopePoleBound

namespace Carnevale
noncomputable section
set_option linter.unusedSimpArgs false
open Polynomial Finset

def bivarQ : Bivar →+* Polynomial (Polynomial ℚ) :=
  MvPolynomial.eval₂Hom (Int.castRingHom _) (fun i => if i=0 then C X else X)

def puncturedQ (N j : ℕ) : Polynomial (Polynomial ℚ) :=
  ∏ k ∈ (range (N+1)).erase j, (1-C (X^k)*X)

theorem bivarQ_map (P : Bivar) :
    (bivarQ P).map (algebraMap (Polynomial ℚ) K)=bivarToK P := by
  have hh : (mapRingHom (algebraMap (Polynomial ℚ) K)).comp bivarQ=bivarToK := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [bivarQ, bivarToK]
    · intro i; fin_cases i <;> simp [bivarQ, bivarToK, RatFunc.algebraMap_X, q]
  exact DFunLike.congr_fun hh P

theorem formula_polynomial_cleared (H : SourceFormula10) (η : List ℕ)
    (hne : η≠[]) (hp : ∀ m∈η, 0<m) :
    C ((blockPolynomial η).eval 1)*bivarQ (denertPoly η) =
      ∑ j ∈ range (η.sum+1), C (coefficientPolynomial η j)*puncturedQ η.sum j := by
  apply Polynomial.map_injective (algebraMap (Polynomial ℚ) K) (RatFunc.algebraMap_injective ℚ)
  rw [Polynomial.map_mul, bivarQ_map, Polynomial.map_C]
  rw [show algebraMap (Polynomial ℚ) K ((blockPolynomial η).eval 1) = E η by
    rw [← eval₂_at_apply, ← eval_map, blockPolynomial_map, map_one]; rfl]
  change C (E η)*A η = _
  rw [formula_to_rational_cleared H η hne hp, rationalNumerator, mul_sum]
  simp only [Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C, coefficientPolynomial_map]
  apply sum_congr rfl
  intro j _
  have hc : C (E η)*C (c η j / E η)=C (c η j) := by
    rw [← C_mul]; congr 1; field_simp [E_ne_zero η]
  rw [← mul_assoc, hc]
  congr 1
  simp [puncturedQ, puncturedDenominator, Polynomial.map_prod, Polynomial.map_sub,
    Polynomial.map_mul, Polynomial.map_one, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_C, RatFunc.algebraMap_X, q]

def complexBivar (Q T : ℂ) : Bivar →+* ℂ :=
  MvPolynomial.eval₂Hom (Int.castRingHom ℂ) (fun i => if i=0 then Q else T)

theorem complexBivar_eq (P : Bivar) (Q T : ℂ) :
    complexBivar Q T P = (bivarQ P).eval₂ (eval₂RingHom (Rat.castHom ℂ) Q) T := by
  have hh : complexBivar Q T =
      (eval₂RingHom (eval₂RingHom (Rat.castHom ℂ) Q) T).comp bivarQ := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [complexBivar, bivarQ]
    · intro i; fin_cases i <;> simp [complexBivar, bivarQ]
  exact DFunLike.congr_fun hh P

theorem complex_pole_sum (H : SourceFormula10) (η : List ℕ)
    (hne : η≠[]) (hp : ∀ m∈η, 0<m) (Q T : ℂ)
    (hz : complexBivar Q T (denertPoly η)=0) :
    ∑ j ∈ range (η.sum+1),
      (coefficientPolynomial η j).eval₂ (Rat.castHom ℂ) Q *
      ∏ k ∈ (range (η.sum+1)).erase j, (1-T*Q^k) = 0 := by
  have hh := congrArg (eval₂RingHom (eval₂RingHom (Rat.castHom ℂ) Q) T)
    (formula_polynomial_cleared H η hne hp)
  rw [map_mul] at hh
  have hz' : (eval₂RingHom (eval₂RingHom (Rat.castHom ℂ) Q) T) (bivarQ (denertPoly η))=0 :=
    (complexBivar_eq _ Q T).symm.trans hz
  rw [hz', mul_zero] at hh
  simpa only [coe_eval₂RingHom, eval₂_finsetSum, eval₂_mul, eval₂_C, puncturedQ,
    eval₂_finsetProd, eval₂_sub, eval₂_one, eval₂_pow, eval₂_X, mul_comm] using hh.symm

theorem complex_endpoint_pole (H : SourceFormula10) (η : List ℕ)
    (hne : η≠[]) (hp : ∀ m∈η, 0<m) (Q T : ℂ) (hQ : Q≠0)
    (hz : complexBivar Q T (denertPoly η)=0) (i : ℕ)
    (hi : i=0 ∨ i=η.sum) (hden : 1-T*Q^i=0)
    (hother : ∀ j∈range (η.sum+1), j≠i → 1-T*Q^j≠0) : False := by
  have him : i∈range (η.sum+1) := by rcases hi with rfl|rfl <;> simp
  have hh := cleared_sum_isolated (RingHom.id ℂ) (range (η.sum+1))
    (fun j => (coefficientPolynomial η j).eval₂ (Rat.castHom ℂ) Q)
    (fun j => 1-T*Q^j) i him hden hother (complex_pole_sum H η hne hp Q T hz)
  change (coefficientPolynomial η i).eval₂ (Rat.castHom ℂ) Q=0 at hh
  rcases hi with rfl|rfl
  · simp [coefficientPolynomial_zero] at hh
  · exact coefficientPolynomial_top_eval_ne_zero η hQ hh

end
end Carnevale
```

### `UnitCircleArc.lean`

```lean
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

namespace Carnevale
noncomputable section
set_option linter.unusedSimpArgs false

/-- A short-arc root: its first possible positive period is at least 2d. -/
theorem unitCircle_short_root {ρ : ℂ} (hρ : ‖ρ‖=1) (h1 : ρ≠1)
    (d : ℕ) (hd : 0<d) :
    ∃ Q : ℂ, Q≠0 ∧ Q^d=ρ ∧ ∀ j : ℕ, 0<j → j<2*d → Q^j≠1 := by
  let θ : ℝ := ρ.arg
  have hexp : Complex.exp ((θ:ℂ)*Complex.I)=ρ := by
    have hh := Complex.norm_mul_exp_arg_mul_I ρ
    simpa [hρ, θ] using hh
  have hθ : θ≠0 := by
    intro hz
    apply h1
    rw [← hexp, hz]
    simp
  have hθlo : -Real.pi<θ := Complex.neg_pi_lt_arg ρ
  have hθhi : θ≤Real.pi := Complex.arg_le_pi ρ
  have hdR : (0:ℝ)<d := by exact_mod_cast hd
  let Q : ℂ := Complex.exp (((θ/(d:ℝ):ℝ):ℂ)*Complex.I)
  have hp (j : ℕ) : Q^j=Complex.exp (((θ*(j:ℝ)/(d:ℝ):ℝ):ℂ)*Complex.I) := by
    dsimp [Q]
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  refine ⟨Q, Complex.exp_ne_zero _, ?_, ?_⟩
  · rw [hp]
    convert hexp using 2; field_simp
  · intro j hj hjd he
    have hjR : (0:ℝ)<j := by exact_mod_cast hj
    have hjdR : (j:ℝ)<2*d := by exact_mod_cast hjd
    rw [hp] at he
    obtain ⟨k,hk⟩ := Complex.exp_eq_one_iff.mp he
    have hi := congrArg Complex.im hk
    have hi' : θ*(j:ℝ)/(d:ℝ)=(k:ℝ)*(2*Real.pi) := by simpa using hi
    have hlo : -(2*Real.pi)<θ*j/d := by
      apply (lt_div_iff₀ hdR).mpr
      nlinarith [Real.pi_pos]
    have hhi : θ*j/d<2*Real.pi := by
      apply (div_lt_iff₀ hdR).mpr
      nlinarith [Real.pi_pos]
    have hklo : (-1:ℝ)<k := by nlinarith [Real.pi_pos]
    have hkhi : (k:ℝ)<1 := by nlinarith [Real.pi_pos]
    have hkloZ : (-1:ℤ)<k := by exact_mod_cast hklo
    have hkhiZ : k<1 := by exact_mod_cast hkhi
    have hk0 : k=0 := by omega
    rw [hk0] at hi'
    simp only [Int.cast_zero, zero_mul] at hi'
    exact hθ ((mul_eq_zero.mp ((div_eq_zero_iff.mp hi').resolve_right (ne_of_gt hdR))).resolve_right (ne_of_gt hjR))

end
end Carnevale
```

### `UnitaryEndpointBounds.lean`

```lean
import ComplexPoleIdentity
import UnitCircleArc

namespace Carnevale
noncomputable section
open Polynomial Finset
set_option linter.unusedSimpArgs false

theorem complex_factor_root (η : List ℕ) (f : Bivar) (F : Polynomial ℤ)
    (a b : ℕ) (hf : f=F.eval₂ (Int.castRingHom Bivar) (x^a*y^b))
    (hd : f ∣ denertPoly η) (Q T ρ : ℂ)
    (hr : F.eval₂ (Int.castRingHom ℂ) ρ=0) (he : Q^a*T^b=ρ) :
    complexBivar Q T (denertPoly η)=0 := by
  have hfz : complexBivar Q T f=0 := by
    rw [hf]
    have hm (n : ℤ) : complexBivar Q T ((Int.castRingHom Bivar) n)=(Int.castRingHom ℂ) n := by simp
    simpa only [Polynomial.eval₂_eq_sum_range, map_sum, map_mul, map_pow, hm,
      show complexBivar Q T x=Q by simp [complexBivar, x],
      show complexBivar Q T y=T by simp [complexBivar, y], he] using hr
  obtain ⟨g,hg⟩ := hd
  rw [hg, map_mul, hfz, zero_mul]

/-- Both endpoint poles constrain the monomial exponents and every unit-circle root. -/
theorem unitary_endpoint_bounds (H : SourceFormula10) (η : List ℕ)
    (hne : η≠[]) (hp : ∀ m∈η, 0<m) (f : Bivar) (F : Polynomial ℤ)
    (a b : ℕ) (ha : 0<a) (hb : 0<b)
    (hf : f=F.eval₂ (Int.castRingHom Bivar) (x^a*y^b))
    (hd : f ∣ denertPoly η) (ρ : ℂ)
    (hr : F.eval₂ (Int.castRingHom ℂ) ρ=0) (hnorm : ‖ρ‖=1) (h1 : ρ≠1) :
    b=1 ∧ η.sum=2*a ∧ ρ= -1 := by
  have hρ0 : ρ≠0 := by intro hz; simp [hz] at hnorm
  have hlow : 2*a≤η.sum := by
    by_contra hgt
    obtain ⟨Q,hQ,hQa,hshort⟩ := unitCircle_short_root hnorm h1 a ha
    apply complex_endpoint_pole H η hne hp Q 1 hQ
      (complex_factor_root η f F a b hf hd Q 1 ρ hr (by simpa using hQa)) 0 (Or.inl rfl)
    · simp
    · intro j hj hji hz
      have hjN : j≤η.sum := by simpa using hj
      apply hshort j (by omega) (by omega)
      simpa using (sub_eq_zero.mp hz).symm
  have hN : 0<η.sum := by omega
  have hNb : η.sum≤b*η.sum := by nlinarith
  let d := b*η.sum-a
  have hda : a+d=b*η.sum := by dsimp [d]; omega
  have hdpos : 0<d := by omega
  have hupp : 2*d≤η.sum := by
    by_contra hgt
    obtain ⟨Q,hQ,hQd,hshort⟩ := unitCircle_short_root
      (by simpa using hnorm : ‖ρ⁻¹‖=1) (by simpa using h1 : ρ⁻¹≠1) d hdpos
    have hmon : Q^a*((Q^η.sum)⁻¹)^b=ρ := by
      have hpow : Q^(b*η.sum)=Q^a*ρ⁻¹ := by rw [← hda, pow_add, hQd]
      have hTI : ((Q^η.sum)⁻¹)^b=(Q^(b*η.sum))⁻¹ := by
        simp [← pow_mul, Nat.mul_comm]
      rw [hTI, hpow]
      field_simp [hQ, hρ0]
    apply complex_endpoint_pole H η hne hp Q ((Q^η.sum)⁻¹) hQ
      (complex_factor_root η f F a b hf hd Q _ ρ hr hmon) η.sum (Or.inr rfl)
    · simp [pow_ne_zero _ hQ]
    · intro j hj hji hz
      have hjN : j<η.sum := by have := mem_range.mp hj; omega
      have he : Q^j=Q^η.sum := by
        have he := sub_eq_zero.mp hz
        exact ((inv_mul_eq_one₀ (pow_ne_zero η.sum hQ)).mp he.symm).symm
      have hperiod : Q^(η.sum-j)=1 := by
        apply mul_right_cancel₀ (pow_ne_zero j hQ)
        rw [one_mul, ← pow_add, Nat.sub_add_cancel hjN.le, he]
      exact hshort (η.sum-j) (by omega) (by omega) hperiod
  have hb1 : b=1 := by
    have hmul : b*η.sum≤η.sum := by omega
    nlinarith
  have hmid : η.sum=2*a := by rw [hb1, one_mul] at hda; omega
  refine ⟨hb1,hmid,?_⟩
  by_contra hneg
  obtain ⟨Q,hQ,hQa,hshort⟩ := unitCircle_short_root hnorm h1 a ha
  apply complex_endpoint_pole H η hne hp Q 1 hQ
    (complex_factor_root η f F a b hf hd Q 1 ρ hr (by simpa using hQa)) 0 (Or.inl rfl)
  · simp
  · intro j hj hji hz
    have he : Q^j=1 := by simpa using (sub_eq_zero.mp hz).symm
    have hjN : j≤η.sum := by simpa using hj
    by_cases hjlt : j<2*a
    · exact hshort j (by omega) hjlt he
    · have hjEq : j=2*a := by omega
      have hr2 : ρ^2=1 := by rw [← hQa, ← pow_mul, Nat.mul_comm a 2, ← hjEq, he]
      have hh : (ρ-1)*(ρ+1)=0 := by linear_combination hr2
      rcases mul_eq_zero.mp hh with hh|hh
      · exact h1 (sub_eq_zero.mp hh)
      · exact hneg (eq_neg_iff_add_eq_zero.mpr hh)

end
end Carnevale
```

### `OneRootPolynomial.lean`

```lean
import Mathlib.Analysis.Complex.Polynomial.Basic

namespace Carnevale
noncomputable section
open Polynomial

/-- FTA with all roots fixed at -1, followed by injective descent to Z. -/
theorem integer_polynomial_one_root (F : Polynomial ℤ)
    (hroots : ∀ z : ℂ, F.eval₂ (Int.castRingHom ℂ) z=0 → z= -1) :
    ∃ n : ℕ, F=C (F.eval 0)*(1+X)^n := by
  let P := F.map (Int.castRingHom ℂ)
  have hprod : (P.roots.map (fun z => X-C z)).prod=(1+X)^(P.roots.card) := by
    have hh : P.roots.map (fun z => X-C z) = P.roots.map (fun _ => (1+X:Polynomial ℂ)) := by
      apply Multiset.map_congr rfl
      intro z hz
      have hP : P≠0 := by intro hzero; simp [hzero] at hz
      have he : z= -1 := hroots z (by simpa [P, eval_map] using (mem_roots hP).mp hz)
      simp [he, add_comm]
    rw [hh]
    simp
  have he := (IsAlgClosed.splits P).eq_prod_roots
  rw [hprod] at he
  have hc : P.leadingCoeff=P.eval 0 := by
    have hh := congrArg (eval 0) he
    simpa using hh.symm
  refine ⟨P.roots.card, ?_⟩
  apply Polynomial.map_injective (Int.castRingHom ℂ) (Int.cast_injective)
  simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
    Polynomial.map_add, Polynomial.map_one, Polynomial.map_X]
  have heval : (Int.castRingHom ℂ) (F.eval 0)=P.eval 0 := by
    simp [P, eval_map, ← coeff_zero_eq_eval_zero]
  rw [heval, ← hc]
  exact he

end
end Carnevale
```

### `UnitaryBinomial.lean`

```lean
import UnitaryEndpointBounds
import UnitaryRootConstraints
import OneRootPolynomial
import NoSquare

namespace Carnevale
noncomputable section
open Polynomial
set_option linter.unusedSimpArgs false

theorem unitary_binomial (H : SourceFormula10) (η : List ℕ)
    (hne : η≠[]) (hp : ∀ m∈η, 0<m) (f : Bivar)
    (hu : IsUnitary f) (hd : f ∣ denertPoly η) :
    ∃ a : ℕ, 0<a ∧ (f=1+x^a*y ∨ f= -(1+x^a*y)) := by
  obtain ⟨F,a,b,ha,hb,hf,hF0,hF1,hnorm⟩ := unitary_polynomial_constraints H η hne hp f hu hd
  have hclass (z : ℂ) (hz : F.eval₂ (Int.castRingHom ℂ) z=0) :
      b=1 ∧ η.sum=2*a ∧ z= -1 := by
    apply unitary_endpoint_bounds H η hne hp f F a b ha hb hf hd z hz (hnorm z hz)
    intro he
    subst z
    apply hF1
    apply Int.cast_injective (α := ℂ)
    simpa [← eval₂_at_apply] using hz
  have hdeg : F.natDegree≠0 := by
    intro hz
    have hFC := eq_C_of_natDegree_eq_zero hz
    apply hu.1
    refine ⟨F.coeff 0, ?_⟩
    rw [hf]
    conv_lhs => rw [hFC, eval₂_C]
    simp
  obtain ⟨z,hz⟩ := IsAlgClosed.exists_root (F.map (Int.castRingHom ℂ))
    (by rw [degree_map_eq_of_injective Int.cast_injective]; exact degree_ne_of_natDegree_ne hdeg)
  have hz' : F.eval₂ (Int.castRingHom ℂ) z=0 := by simpa [IsRoot, eval_map] using hz
  have hb1 := (hclass z hz').1
  obtain ⟨n,hn⟩ := integer_polynomial_one_root F (fun z hz => (hclass z hz).2.2)
  have hfe : f=MvPolynomial.C (F.eval 0)*(1+x^a*y)^n := by
    rw [hf]
    conv_lhs => rw [hn, eval₂_mul, eval₂_C, eval₂_pow, eval₂_add, eval₂_one, eval₂_X]
    simp only [hb1, pow_one]
    congr 1
  have hn0 : n≠0 := by
    intro hz
    apply hu.1
    exact ⟨F.eval 0, by simpa [hz] using hfe⟩
  have hn2 : ¬2≤n := by
    intro hnn
    apply no_square H η hne hp a
    apply dvd_trans (show (1+x^a*y)^2 ∣ f from ?_) hd
    rw [hfe]
    exact dvd_mul_of_dvd_right (pow_dvd_pow _ hnn) _
  have hn1 : n=1 := by omega
  refine ⟨a,ha,?_⟩
  rcases hF0 with hc|hc
  · left; simpa [hn1, hc] using hfe
  · right; simpa [hn1, hc] using hfe

end
end Carnevale
```

### `SourceConjecture.lean`

```lean
import UnitaryBinomial
import ConditionalAssembly

namespace Carnevale
noncomputable section

theorem rectangle_quotient (H : SourceFormula10) (m r : ℕ)
    (hm : 0<m) (hr : 0<r) (ho : Odd m) (he : Even r) :
    ∃ f0 : Bivar, denertPoly (List.replicate r m)=rectangleFactor (m*r)*f0 ∧
      ¬HasUnitaryFactor f0 := by
  obtain ⟨f0,hfac,hfree⟩ := rectangle_binomial_quotient H m r hm hr ho he
  refine ⟨f0,hfac,?_⟩
  rintro ⟨f,hu,hd⟩
  have hf0 : f0 ∣ denertPoly (List.replicate r m) := by rw [hfac]; exact dvd_mul_left _ _
  obtain ⟨a,_ha,he⟩ := unitary_binomial H _ (by simpa using Nat.ne_of_gt hr)
    (by intro n hn; rcases List.mem_replicate.mp hn with ⟨_,rfl⟩; exact hm) f hu (hd.trans hf0)
  apply hfree a
  rcases he with he|he
  · simpa only [he] using hd
  · simpa only [he, neg_dvd] using hd

/-- MathDB 351584, E2: the literal conjecture, conditional only on the source formula. -/
theorem source_conjecture_351584
    (H_published_CarnevaleTielker_formula10 : SourceFormula10) : Conjecture23 :=
  assembly_requires_U1 unitary_binomial H_published_CarnevaleTielker_formula10

end
end Carnevale
```

### `Stage4Audit.lean`

```lean
import SourceConjecture
import Stage3Audit

namespace Carnevale.Stage4

theorem U1_proved : Blueprint.U1 := unitary_binomial
theorem R4_proved : Blueprint.R4 := rectangle_quotient
theorem F1_proved : Blueprint.F1 := source_conjecture_351584

#check Carnevale.unitary_binomial
#print axioms Carnevale.unitary_binomial
#check Carnevale.unitary_endpoint_bounds
#print axioms Carnevale.unitary_endpoint_bounds
#check Carnevale.rectangle_quotient
#print axioms Carnevale.rectangle_quotient
#check Carnevale.source_conjecture_351584
#print axioms Carnevale.source_conjecture_351584
#print Carnevale.Conjecture23
#print Carnevale.IsUnitary
#print Carnevale.SourceFormula10
#print Carnevale.SourceFormula10At
#print Carnevale.denertPoly
#print Carnevale.den
#print Carnevale.rectangleFactor
#print axioms U1_proved
#print axioms R4_proved
#print axioms F1_proved
end Carnevale.Stage4
```

