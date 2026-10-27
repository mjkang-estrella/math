import SourceLiteral
import UniversalExpansion

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace PeakonCoefficients

open Matrix
open scoped Nat

theorem source_trace_partition_universal_ordered {n : Type*} [Fintype n] [DecidableEq n]
    [LinearOrder n] (r : n → ℂ) (q : n → ℝ) (nu lam xi gamma : ℂ)
    (hq : Antitone q) (hcurve : xi ^ 2 = lam ^ 2 + gamma * lam + 1) (m : ℕ) (hm : 0 < m) :
    Matrix.trace (sourceLax r q nu lam xi ^ m) =
      ∑ j ∈ Finset.range m, ∑ k ∈ (Finset.Icc 1 m).sym (j + 1),
        if k.val.sum = m then coefficientWeight (K := ℂ) m k.val * lam ^ (j + 1) *
          (k.val.map (sourceHamiltonian r q nu gamma)).prod else 0 := by
  rw [sourceLax_ordered r q nu lam xi hq]
  simpa only [sourceHamiltonian_ordered r q nu gamma hq] using
    trace_partition_universal (sourceU r q nu) (sourceV r q nu) lam xi gamma hcurve m hm

theorem source_trace_partition_universal {N : ℕ} (r : Fin N → ℂ) (q : Fin N → ℝ)
    (nu lam xi gamma : ℂ) (hcurve : xi ^ 2 = lam ^ 2 + gamma * lam + 1) (m : ℕ) (hm : 0 < m) :
    Matrix.trace (sourceLax r q nu lam xi ^ m) =
      ∑ j ∈ Finset.range m, ∑ k ∈ (Finset.Icc 1 m).sym (j + 1),
        if k.val.sum = m then coefficientWeight (K := ℂ) m k.val * lam ^ (j + 1) *
          (k.val.map (sourceHamiltonian r q nu gamma)).prod else 0 := by
  have h := source_trace_partition_universal_ordered (r ∘ descendingPositionPermutation q)
    (q ∘ descendingPositionPermutation q) nu lam xi gamma (positions_sorted q) hcurve m hm
  rw [sourceTrace_permutation] at h
  simpa only [sourceHamiltonian_permutation] using h

def universalCoefficient (p : Multiset ℕ) : ℂ := coefficientWeight p.sum p

theorem universalCoefficient_formula (p : Multiset ℕ) (hp : 0 < p.card) :
    universalCoefficient p = (p.sum : ℂ) * ((p.card - 1)! : ℂ) /
      ((p.map (fun k : ℕ => (k : ℂ))).prod * (multiplicityDenominator p : ℂ)) :=
  coefficientWeight_formula p.sum p hp

def ConjecturedCoefficientFamilies (a : Multiset ℕ → ℂ) : Prop :=
  (∀ m : ℕ, 0 < m → a {m} = 1) ∧
  (∀ m : ℕ, 0 < m → a (Multiset.replicate m 1) = 1) ∧
  (∀ m j : ℕ, j < m - 1 → a ((m - j) ::ₘ Multiset.replicate j 1) =
    (m : ℂ) / (m - j : ℕ))

theorem universalCoefficient_families : ConjecturedCoefficientFamilies universalCoefficient := by
  refine ⟨?_, ?_, ?_⟩
  · intro m hm
    simpa only [universalCoefficient, Multiset.sum_singleton] using
      coefficientWeight_singleton (K := ℂ) m hm
  · intro m hm
    simpa only [universalCoefficient, Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_id, mul_one] using
      coefficientWeight_all_ones (K := ℂ) m hm
  · intro m j hj
    have hsum : ((m - j) ::ₘ Multiset.replicate j 1).sum = m := by
      simp only [Multiset.sum_cons, Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_id, mul_one]
      omega
    simpa only [universalCoefficient, hsum] using coefficientWeight_one_big (K := ℂ) m j hj

theorem coherent_source_expansion {N : ℕ} (r : Fin N → ℂ) (q : Fin N → ℝ)
    (nu z gamma : ℂ) (hz : 2 * z + gamma ≠ 0) (m : ℕ) (hm : 0 < m) :
    Matrix.trace (sourceLax r q nu (spectralLambda z gamma) (spectralXi z gamma) ^ m) =
      ∑ j ∈ Finset.range m, ∑ k ∈ (Finset.Icc 1 m).sym (j + 1),
        if k.val.sum = m then universalCoefficient k.val *
          spectralLambda z gamma ^ (j + 1) *
            (k.val.map (sourceHamiltonian r q nu gamma)).prod else 0 := by
  rw [source_trace_partition_universal r q nu (spectralLambda z gamma)
    (spectralXi z gamma) gamma (spectral_curve z gamma hz) m hm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hkm : k.val.sum = m
  · simp only [universalCoefficient, hkm]
  · simp only [ite_eq_right hkm]

theorem nonnegative_source_expansion {N : ℕ} (p q : Fin N → ℝ) (nu z gamma : ℂ)
    (hp : ∀ i, 0 ≤ p i) (hz : 2 * z + gamma ≠ 0) (m : ℕ) (hm : 0 < m) :
    Matrix.trace (literalLax p q nu z gamma ^ m) =
      ∑ j ∈ Finset.range m, ∑ k ∈ (Finset.Icc 1 m).sym (j + 1),
        if k.val.sum = m then universalCoefficient k.val *
          spectralLambda z gamma ^ (j + 1) *
            (k.val.map (literalHamiltonian p q nu gamma)).prod else 0 := by
  rw [literalLax_eq_source p q nu z gamma hp]
  simpa only [literalHamiltonian_eq_source p q nu gamma hp] using
    coherent_source_expansion (particleRoots p) q nu z gamma hz m hm

def NonnegativeSourceConjecture372008 : Prop :=
  ∃ a : Multiset ℕ → ℂ, ConjecturedCoefficientFamilies a ∧
    ∀ (N : ℕ) (p q : Fin N → ℝ) (nu z gamma : ℂ),
      (∀ i, 0 ≤ p i) → 2 * z + gamma ≠ 0 → ∀ m : ℕ, 0 < m →
      Matrix.trace (literalLax p q nu z gamma ^ m) =
        ∑ j ∈ Finset.range m, ∑ k ∈ (Finset.Icc 1 m).sym (j + 1),
          if k.val.sum = m then a k.val * spectralLambda z gamma ^ (j + 1) *
            (k.val.map (literalHamiltonian p q nu gamma)).prod else 0

theorem nonnegative_source_conjecture_372008 : NonnegativeSourceConjecture372008 :=
  ⟨universalCoefficient, universalCoefficient_families, fun _ p q nu z gamma hp hz m hm =>
    nonnegative_source_expansion p q nu z gamma hp hz m hm⟩


def SourceConjecture372008 : Prop :=
  ∃ a : Multiset ℕ → ℂ, ConjecturedCoefficientFamilies a ∧
    ∀ (N : ℕ) (r : Fin N → ℂ) (q : Fin N → ℝ) (nu z gamma : ℂ),
      2 * z + gamma ≠ 0 → ∀ m : ℕ, 0 < m →
      Matrix.trace (sourceLax r q nu (spectralLambda z gamma) (spectralXi z gamma) ^ m) =
        ∑ j ∈ Finset.range m, ∑ k ∈ (Finset.Icc 1 m).sym (j + 1),
          if k.val.sum = m then a k.val * spectralLambda z gamma ^ (j + 1) *
            (k.val.map (sourceHamiltonian r q nu gamma)).prod else 0

theorem source_conjecture_372008 : SourceConjecture372008 :=
  ⟨universalCoefficient, universalCoefficient_families, fun _ r q nu z gamma hz m hm =>
    coherent_source_expansion r q nu z gamma hz m hm⟩

end PeakonCoefficients
