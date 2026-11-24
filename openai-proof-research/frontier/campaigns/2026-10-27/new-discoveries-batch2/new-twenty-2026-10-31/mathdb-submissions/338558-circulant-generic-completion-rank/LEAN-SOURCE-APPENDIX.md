# Lean source appendix — MathDB 338558

Complete literal endpoint; modules in dependency order. All eight stage-1 modules are preserved byte-for-byte.

### `CirculantStatement.lean`

```lean
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Nat.Sqrt

/-! Literal complex completion-rank objects. No tangent-space surrogate. -/
noncomputable section
open Matrix
namespace Circulant
open Classical

def Unknown (n l : ℕ) : Set (Fin n × Fin n) :=
  {ij | ∃ s : ℕ, s < n - l ∧ ij.2.val = (ij.1.val + s) % n}

def Observed (n l : ℕ) : Set (Fin n × Fin n) := (Unknown n l)ᶜ

def Agrees {n : ℕ} (E : Set (Fin n × Fin n))
    (x : E → ℂ) (M : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ e : E, M e.val.1 e.val.2 = x e

def zeroFill {n : ℕ} (E : Set (Fin n × Fin n)) (x : E → ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun i j => if h : (i, j) ∈ E then x ⟨(i, j), h⟩ else 0

theorem zeroFill_agrees {n : ℕ} (E : Set (Fin n × Fin n)) (x : E → ℂ) :
    Agrees E x (zeroFill E x) := by
  intro e
  simp only [zeroFill, dite_eq_left e.property]

theorem completion_exists {n : ℕ} (E : Set (Fin n × Fin n)) (x : E → ℂ) :
    ∃ t : ℕ, ∃ M : Matrix (Fin n) (Fin n) ℂ, Agrees E x M ∧ M.rank = t :=
  ⟨_, zeroFill E x, zeroFill_agrees E x, rfl⟩

def CompletionRank {n : ℕ} (E : Set (Fin n × Fin n)) (x : E → ℂ) : ℕ :=
  Nat.find (completion_exists E x)

theorem completionRank_attained {n : ℕ} (E : Set (Fin n × Fin n)) (x : E → ℂ) :
    ∃ M : Matrix (Fin n) (Fin n) ℂ,
      Agrees E x M ∧ M.rank = CompletionRank E x :=
  Nat.find_spec (completion_exists E x)

theorem completionRank_le {n : ℕ} {E : Set (Fin n × Fin n)} {x : E → ℂ}
    {M : Matrix (Fin n) (Fin n) ℂ} (hM : Agrees E x M) :
    CompletionRank E x ≤ M.rank :=
  Nat.find_min' (completion_exists E x) ⟨M, hM, rfl⟩

theorem completionRank_le_iff {n t : ℕ} (E : Set (Fin n × Fin n)) (x : E → ℂ) :
    CompletionRank E x ≤ t ↔
      ∃ M : Matrix (Fin n) (Fin n) ℂ, Agrees E x M ∧ M.rank ≤ t := by
  constructor
  · intro h
    obtain ⟨M, hM, hr⟩ := completionRank_attained E x
    exact ⟨M, hM, hr ▸ h⟩
  · rintro ⟨M, hM, ht⟩
    exact (completionRank_le hM).trans ht

def ZeroLocus {I : Type*} (S : Set (MvPolynomial I ℂ)) : Set (I → ℂ) :=
  {x | ∀ p ∈ S, MvPolynomial.eval x p = 0}

def ZOpen {I : Type*} (U : Set (I → ℂ)) : Prop :=
  ∃ S : Set (MvPolynomial I ℂ), U = (ZeroLocus S)ᶜ

def PrincipalOpen {I : Type*} (p : MvPolynomial I ℂ) : Set (I → ℂ) :=
  {x | MvPolynomial.eval x p ≠ 0}

theorem principalOpen_zopen {I : Type*} (p : MvPolynomial I ℂ) :
    ZOpen (PrincipalOpen p) := by
  refine ⟨{p}, ?_⟩
  ext x
  simp [PrincipalOpen, ZeroLocus]

theorem nonzero_has_eval {I : Type*} {p : MvPolynomial I ℂ} (hp : p ≠ 0) :
    ∃ x : I → ℂ, MvPolynomial.eval x p ≠ 0 := by
  by_contra h
  push Not at h
  apply hp
  apply MvPolynomial.funext
  intro x
  simpa using h x

theorem nonempty_principalOpen {I : Type*} {p : MvPolynomial I ℂ} (hp : p ≠ 0) :
    (PrincipalOpen p).Nonempty := nonzero_has_eval hp

theorem principalOpen_inside {I : Type*} {U : Set (I → ℂ)}
    (hU : ZOpen U) (hne : U.Nonempty) :
    ∃ p : MvPolynomial I ℂ, p ≠ 0 ∧ PrincipalOpen p ⊆ U := by
  obtain ⟨S, rfl⟩ := hU
  obtain ⟨x, hx⟩ := hne
  change ¬ ∀ p ∈ S, MvPolynomial.eval x p = 0 at hx
  push Not at hx
  obtain ⟨p, hpS, hpx⟩ := hx
  refine ⟨p, ?_, ?_⟩
  · intro hp
    simp [hp] at hpx
  · intro y hy hz
    exact hy (hz p hpS)

theorem zopen_inter_nonempty {I : Type*} {U V : Set (I → ℂ)}
    (hU : ZOpen U) (hneU : U.Nonempty) (hV : ZOpen V) (hneV : V.Nonempty) :
    (U ∩ V).Nonempty := by
  obtain ⟨p, hp, hpU⟩ := principalOpen_inside hU hneU
  obtain ⟨q, hq, hqV⟩ := principalOpen_inside hV hneV
  obtain ⟨x, hx⟩ := nonzero_has_eval (mul_ne_zero hp hq)
  rw [map_mul] at hx
  exact ⟨x, hpU (mul_ne_zero_iff.mp hx).1, hqV (mul_ne_zero_iff.mp hx).2⟩

def GCR {n : ℕ} (E : Set (Fin n × Fin n)) (r : ℕ) : Prop :=
  ∃ U : Set (E → ℂ), ZOpen U ∧ U.Nonempty ∧
    ∀ x ∈ U, CompletionRank E x = r

theorem gcr_unique {n r s : ℕ} {E : Set (Fin n × Fin n)}
    (hr : GCR E r) (hs : GCR E s) : r = s := by
  obtain ⟨U, hU, hneU, hUr⟩ := hr
  obtain ⟨V, hV, hneV, hVs⟩ := hs
  obtain ⟨x, hxU, hxV⟩ := zopen_inter_nonempty hU hneU hV hneV
  exact (hUr x hxU).symm.trans (hVs x hxV)

def LiteralConjecture : Prop :=
  ∀ n l : ℕ, 0 < n → l ≤ n →
    GCR (Observed n l) (n - Nat.sqrt (n * (n - l)))

/-- This assembly bridge assumes two explicit polynomial certificates, not a
Jacobian criterion or a redefinition of generic completion rank. -/
theorem gcr_of_polynomial_certificates {n r : ℕ} {E : Set (Fin n × Fin n)}
    (p q : MvPolynomial E ℂ) (hp : p ≠ 0) (hq : q ≠ 0)
    (upper : ∀ x, MvPolynomial.eval x p ≠ 0 →
      ∃ M : Matrix (Fin n) (Fin n) ℂ, Agrees E x M ∧ M.rank ≤ r)
    (lower : ∀ M : Matrix (Fin n) (Fin n) ℂ, M.rank < r →
      MvPolynomial.eval (fun e : E => M e.val.1 e.val.2) q = 0) :
    GCR E r := by
  refine ⟨PrincipalOpen (p * q), principalOpen_zopen _, nonempty_principalOpen
    (mul_ne_zero hp hq), ?_⟩
  intro x hx
  change MvPolynomial.eval x (p * q) ≠ 0 at hx
  rw [map_mul] at hx
  obtain ⟨hpx, hqx⟩ := mul_ne_zero_iff.mp hx
  obtain ⟨M, hM, hMr⟩ := upper x hpx
  apply Nat.le_antisymm ((completionRank_le hM).trans hMr)
  by_contra h
  have hlt : CompletionRank E x < r := Nat.lt_of_not_ge h
  obtain ⟨N, hN, hNr⟩ := completionRank_attained E x
  have hz := lower N (hNr ▸ hlt)
  have he : (fun e : E => N e.val.1 e.val.2) = x := funext hN
  exact hqx (he ▸ hz)

end Circulant

#print axioms Circulant.completionRank_attained
#print axioms Circulant.completionRank_le_iff
#print axioms Circulant.zopen_inter_nonempty
#print axioms Circulant.gcr_unique
#print axioms Circulant.gcr_of_polynomial_certificates
```

### `BalancedWindow.lean`

```lean
import Mathlib.Data.Int.DivMod
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Data.Nat.Sqrt

/-! Integer mechanical words; the starting point may be negative. -/
namespace Circulant
open Finset

def step (n k : ℕ) (j : ℤ) : ℤ :=
  ((j + 1) * (k : ℤ)) / (n : ℤ) - (j * (k : ℤ)) / (n : ℤ)

theorem step_nonneg {n k : ℕ} (hn : 0 < n) (j : ℤ) :
    0 ≤ step n k j := by
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  have hk : (0 : ℤ) ≤ k := by exact_mod_cast (Nat.zero_le k)
  have hm : j * (k : ℤ) ≤ (j + 1) * k := by nlinarith
  exact sub_nonneg.mpr (Int.ediv_le_ediv hn' hm)

theorem step_le_one {n k : ℕ} (hn : 0 < n) (hk : k ≤ n) (j : ℤ) :
    step n k j ≤ 1 := by
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  have hk' : (k : ℤ) ≤ n := by exact_mod_cast hk
  have hm : (j + 1) * (k : ℤ) ≤ j * k + n := by nlinarith
  have h := Int.ediv_le_ediv hn' hm
  have he : (j * (k : ℤ) + n) / n = (j * k) / n + 1 := by
    simpa using Int.add_mul_ediv_right (j * (k : ℤ)) 1 (ne_of_gt hn')
  unfold step
  omega

theorem step_binary {n k : ℕ} (hn : 0 < n) (hk : k ≤ n) (j : ℤ) :
    step n k j = 0 ∨ step n k j = 1 := by
  have := step_nonneg (k := k) hn j
  have := step_le_one hn hk j
  omega

theorem step_periodic {n k : ℕ} (hn : 0 < n) (j : ℤ) :
    step n k (j + n) = step n k j := by
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  have h1 : (j + (n : ℤ) + 1) * k = (j + 1) * k + k * n := by ring
  have h2 : (j + (n : ℤ)) * k = j * k + k * n := by ring
  simp only [step, h1, h2, Int.add_mul_ediv_right _ _ hn']
  omega

theorem window_sum (n k m : ℕ) (L : ℤ) :
    (∑ t ∈ range m, step n k (L + t)) =
      ((L + m) * (k : ℤ)) / n - (L * (k : ℤ)) / n := by
  convert sum_range_sub (fun t : ℕ => ((L + t) * (k : ℤ)) / n) m using 1
  · apply sum_congr rfl
    intro t _
    simp only [step, Nat.cast_add, Nat.cast_one]
    congr 2
    ring
  · simp

theorem period_sum {n k : ℕ} (hn : 0 < n) (L : ℤ) :
    (∑ t ∈ range n, step n k (L + t)) = k := by
  rw [window_sum]
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  have he : (L + (n : ℤ)) * k = L * k + k * n := by ring
  rw [he, Int.add_mul_ediv_right _ _ hn']
  omega

/-- The all-parameter cyclic window bound, including wraparound and negative starts. -/
theorem balanced_window_bound {n k d : ℕ} (hn : 0 < n)
    (hkd : k * k ≤ n * d) (L : ℤ) :
    (∑ t ∈ range k, step n k (L + t)) ≤ d := by
  rw [window_sum]
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  have hkd' : (k : ℤ) * k ≤ (n : ℤ) * d := by exact_mod_cast hkd
  have hm : (L + (k : ℤ)) * k ≤ L * k + d * n := by nlinarith
  have h := Int.ediv_le_ediv hn' hm
  rw [Int.add_mul_ediv_right _ _ (ne_of_gt hn')] at h
  omega

/-- Count ones rather than their integer weights. -/
theorem balanced_window_card {n k d : ℕ} (hn : 0 < n)
    (hk : k ≤ n) (hkd : k * k ≤ n * d) (L : ℤ) :
    ((range k).filter (fun t : ℕ => step n k (L + t) = 1)).card ≤ d := by
  have he :
      (∑ t ∈ range k, step n k (L + t)) =
        (((range k).filter (fun t : ℕ => step n k (L + t) = 1)).card : ℤ) := by
    calc
      _ = ∑ t ∈ range k, if step n k (L + t) = 1 then (1 : ℤ) else 0 := by
        apply sum_congr rfl
        intro t _
        rcases step_binary hn hk (L + t) with h | h <;> simp [h]
      _ = _ := by simp only [sum_boole]
  have h := balanced_window_bound hn hkd L
  rw [he] at h
  exact_mod_cast h

theorem period_card {n k : ℕ} (hn : 0 < n) (hk : k ≤ n) (L : ℤ) :
    ((range n).filter (fun t : ℕ => step n k (L + t) = 1)).card = k := by
  have he :
      (∑ t ∈ range n, step n k (L + t)) =
        (((range n).filter (fun t : ℕ => step n k (L + t) = 1)).card : ℤ) := by
    calc
      _ = ∑ t ∈ range n, if step n k (L + t) = 1 then (1 : ℤ) else 0 := by
        apply sum_congr rfl
        intro t _
        rcases step_binary hn hk (L + t) with h | h <;> simp [h]
      _ = _ := by simp only [sum_boole]
  have h := period_sum (k := k) hn L
  rw [he] at h
  exact_mod_cast h

#print axioms step_binary
#print axioms step_periodic
#print axioms balanced_window_bound
#print axioms balanced_window_card
#print axioms period_card
end Circulant
```

### `BalancedFrequencies.lean`

```lean
import BalancedWindow
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.ModEq

noncomputable section
namespace Circulant
open Finset

theorem step_shift {n k : ℕ} (hn : 0 < n) (j q : ℤ) :
    step n k (j + q * n) = step n k j := by
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  have h1 : (j + q * (n : ℤ) + 1) * k = (j + 1) * k + (q * k) * n := by ring
  have h2 : (j + q * (n : ℤ)) * k = j * k + (q * k) * n := by ring
  simp only [step, h1, h2, Int.add_mul_ediv_right _ _ hn']
  omega

abbrev BalancedSet (n k : ℕ) := {a : Fin n // step n k a.val = 1}
theorem balancedSet_card {n k : ℕ} (hn : 0 < n) (hk : k ≤ n) :
    Fintype.card (BalancedSet n k) = k := by
  classical
  let S := (range n).filter (fun t : ℕ => step n k (0 + t) = 1)
  let e : BalancedSet n k ≃ S :=
    { toFun := fun a => ⟨a.val.val, mem_filter.mpr
        ⟨mem_range.mpr a.val.isLt, by simpa using a.property⟩⟩
      invFun := fun a => ⟨⟨a.val, mem_range.mp (mem_filter.mp a.property).1⟩,
        by simpa using (mem_filter.mp a.property).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  calc
    Fintype.card (BalancedSet n k) = Fintype.card S := Fintype.card_congr e
    _ = S.card := Fintype.card_coe S
    _ = k := period_card hn hk 0

abbrev FrequencyPair (n k : ℕ) := BalancedSet n k × Fin k

def pairFrequency {n k : ℕ} (hn : 0 < n) (p : FrequencyPair n k) : Fin n :=
  ⟨(p.1.val.val + p.2.val) % n, Nat.mod_lt _ hn⟩

theorem pairFrequency_second_injective {n k : ℕ} (hn : 0 < n) (f : Fin n) :
    Function.Injective
      (fun p : {p : FrequencyPair n k // pairFrequency hn p = f} => p.val.2) := by
  intro p q he
  change p.val.2 = q.val.2 at he
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    apply Fin.ext
    have hp := congr_arg Fin.val p.property
    have hq := congr_arg Fin.val q.property
    change (p.val.1.val.val + p.val.2.val) % n = f.val at hp
    change (q.val.1.val.val + q.val.2.val) % n = f.val at hq
    have hb : p.val.2.val = q.val.2.val := congr_arg Fin.val he
    have ha := p.val.1.val.isLt
    have hq' := q.val.1.val.isLt
    rw [hb] at hp
    have hm : Nat.ModEq n (p.val.1.val.val + q.val.2.val)
        (q.val.1.val.val + q.val.2.val) := hp.trans hq.symm
    have hmod := Nat.ModEq.add_right_cancel' q.val.2.val hm
    change p.val.1.val.val % n = q.val.1.val.val % n at hmod
    simpa only [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hq'] using hmod
  · exact he

theorem pairFrequency_step {n k : ℕ} (hn : 0 < n) (f : Fin n)
    (p : {p : FrequencyPair n k // pairFrequency hn p = f}) :
    step n k ((f.val : ℤ) - p.val.2.val) = 1 := by
  have hp := congr_arg Fin.val p.property
  change (p.val.1.val.val + p.val.2.val) % n = f.val at hp
  have hnat := Nat.mod_add_div (p.val.1.val.val + p.val.2.val) n
  rw [hp] at hnat
  have hz : (f.val : ℤ) + n * ((p.val.1.val.val + p.val.2.val) / n : ℕ) =
      (p.val.1.val.val : ℤ) + p.val.2.val := by exact_mod_cast hnat
  have he : (f.val : ℤ) - p.val.2.val =
      (p.val.1.val.val : ℤ) + (-((p.val.1.val.val + p.val.2.val) / n : ℕ) : ℤ) * n := by
    nlinarith [hz]
  rw [he, step_shift hn]
  exact p.val.1.property

/-- Actual cardinal bound on the modular collision classes of the balanced set. -/
theorem balanced_fiber_card {n k d : ℕ} (hn : 0 < n)
    (hk : k ≤ n) (hkd : k * k ≤ n * d) (f : Fin n) :
    Fintype.card {p : FrequencyPair n k // pairFrequency hn p = f} ≤ d := by
  classical
  let S := (range k).filter
    (fun t : ℕ => step n k ((f.val : ℤ) - k + 1 + t) = 1)
  let g : {p : FrequencyPair n k // pairFrequency hn p = f} → S := fun p =>
    ⟨k - 1 - p.val.2.val, by
      apply mem_filter.mpr
      have hb := p.val.2.isLt
      refine ⟨mem_range.mpr (by omega), ?_⟩
      have he : (f.val : ℤ) - k + 1 + (k - 1 - p.val.2.val : ℕ) =
          (f.val : ℤ) - p.val.2.val := by omega
      rw [he]
      exact pairFrequency_step hn f p⟩
  have hg : Function.Injective g := by
    intro p q he
    apply pairFrequency_second_injective hn f
    apply Fin.ext
    have ht := congr_arg Subtype.val he
    change k - 1 - p.val.2.val = k - 1 - q.val.2.val at ht
    have hp := p.val.2.isLt
    have hq := q.val.2.isLt
    change p.val.2.val = q.val.2.val
    omega
  have hcard := Fintype.card_le_of_injective g hg
  have hS : S.card ≤ d :=
    balanced_window_card hn hk hkd ((f.val : ℤ) - k + 1)
  exact hcard.trans (by simpa using hS)

#print axioms balancedSet_card
#print axioms step_shift
#print axioms pairFrequency_second_injective
#print axioms balanced_fiber_card
end Circulant
```

### `FourierBlocks.lean`

```lean
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-! A finite Fourier/Vandermonde certificate. Frequency fiber loads are explicit hypotheses. -/
noncomputable section
namespace Circulant
open Finset

/-- Interpolation on any finite set of distinct nodes. -/
theorem moments_zero {P : Type*} [Fintype P] {d : ℕ}
    (z c : P → ℂ) (hz : Function.Injective z) (hd : Fintype.card P ≤ d)
    (h : ∀ s : Fin d, ∑ p, c p * z p ^ s.val = 0) : c = 0 := by
  let e := (Fintype.equivFin P).symm
  have he : Function.Injective (fun j : Fin (Fintype.card P) => z (e j)) :=
    hz.comp e.injective
  have hc : (fun j => c (e j)) = 0 := by
    apply Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero he
    intro i
    have hi := h ⟨i.val, lt_of_lt_of_le i.isLt hd⟩
    rw [← e.sum_comp (fun p => c p * z p ^ i.val)] at hi
    exact hi
  funext p
  have hp := congr_fun hc (e.symm p)
  simpa [e] using hp

theorem root_nodes_injective {n : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n) :
    Function.Injective (fun f : Fin n => ζ ^ f.val) := by
  intro f g h
  exact Fin.ext (hζ.pow_inj f.isLt g.isLt h)

theorem root_vandermonde_det_ne_zero {n : ℕ} {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ n) :
    (Matrix.vandermonde (fun f : Fin n => ζ ^ f.val)).det ≠ 0 :=
  Matrix.det_vandermonde_ne_zero_iff.mpr (root_nodes_injective hζ)

def blockRestriction {P : Type*} [Fintype P] {n d : ℕ} (ζ : ℂ)
    (freq : P → Fin n) (node : P → ℂ) (c : P → ℂ) (i : Fin n) (s : Fin d) : ℂ :=
  ∑ p, c p * node p ^ s.val * (ζ ^ (freq p).val) ^ i.val

/-- Each collision class has at most d nodes. Fourier isolation followed by
Vandermonde interpolation kills every coefficient. -/
theorem fourier_blocks_kernel {P : Type*} [Fintype P] {n d : ℕ}
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n) (freq : P → Fin n) (node : P → ℂ)
    (loads : ∀ f : Fin n, Fintype.card {p : P // freq p = f} ≤ d)
    (distinct : ∀ f : Fin n, Function.Injective
      (fun p : {p : P // freq p = f} => node p.val))
    (c : P → ℂ)
    (h : ∀ (i : Fin n) (s : Fin d), blockRestriction ζ freq node c i s = 0) :
    c = 0 := by
  classical
  have hf (s : Fin d) :
      (fun f : Fin n => ∑ p : {p : P // freq p = f}, c p.val * node p.val ^ s.val) = 0 := by
    apply moments_zero (d := n) (fun f : Fin n => ζ ^ f.val) _
      (root_nodes_injective hζ) (by simp)
    intro i
    have hi := h i s
    unfold blockRestriction at hi
    rw [← Fintype.sum_fiberwise freq
      (fun p => c p * node p ^ s.val * (ζ ^ (freq p).val) ^ i.val)] at hi
    convert hi using 1
    apply sum_congr rfl
    intro f _
    rw [sum_mul]
    apply sum_congr rfl
    intro p _
    rw [p.property]
  have hc (f : Fin n) :
      (fun p : {p : P // freq p = f} => c p.val) = 0 := by
    apply moments_zero _ _ (distinct f) (loads f)
    intro s
    exact congr_fun (hf s) f
  funext p
  exact congr_fun (hc (freq p)) ⟨p, rfl⟩

theorem fourier_blocks_injective {P : Type*} [Fintype P] {n d : ℕ}
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n) (freq : P → Fin n) (node : P → ℂ)
    (loads : ∀ f : Fin n, Fintype.card {p : P // freq p = f} ≤ d)
    (distinct : ∀ f : Fin n, Function.Injective
      (fun p : {p : P // freq p = f} => node p.val)) :
    Function.Injective (fun c : P → ℂ =>
      fun i : Fin n => fun s : Fin d => blockRestriction ζ freq node c i s) := by
  intro c c' he
  have hzero : c - c' = 0 := by
    apply fourier_blocks_kernel hζ freq node loads distinct
    intro i s
    have hi := congr_fun (congr_fun he i) s
    change (∑ p, (c p - c' p) * node p ^ s.val * (ζ ^ (freq p).val) ^ i.val) = 0
    simp_rw [sub_mul, sum_sub_distrib]
    exact sub_eq_zero.mpr hi
  exact sub_eq_zero.mp hzero

#print axioms moments_zero
#print axioms root_vandermonde_det_ne_zero
#print axioms fourier_blocks_kernel
#print axioms fourier_blocks_injective
end Circulant
```

### `CirculantFourier.lean`

```lean
import BalancedFrequencies
import FourierBlocks
import Mathlib.LinearAlgebra.Matrix.Rank

noncomputable section
namespace Circulant
set_option backward.isDefEq.respectTransparency false
open Finset Matrix

def fourierU (n k : ℕ) (ζ : ℂ) : Matrix (Fin n) (BalancedSet n k) ℂ :=
  fun i a => (ζ ^ a.val.val) ^ i.val

def fourierV (n k : ℕ) (ζ : ℂ) : Matrix (Fin n) (Fin k) ℂ :=
  fun j b => (ζ ^ b.val) ^ j.val

def bandRestriction {n k d : ℕ} (hn : 0 < n) (ζ : ℂ)
    (C : Matrix (BalancedSet n k) (Fin k) ℂ) (i : Fin n) (s : Fin d) : ℂ :=
  (fourierU n k ζ * C * (fourierV n k ζ).transpose)
    i ⟨(i.val + s.val) % n, Nat.mod_lt _ hn⟩

theorem root_power_period {n : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n)
    (b t : ℕ) : (ζ ^ b) ^ (t % n) = (ζ ^ b) ^ t := by
  have hb : (ζ ^ b) ^ n = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  exact (pow_eq_pow_mod t hb).symm

theorem bandRestriction_eq_blocks {n k d : ℕ} (hn : 0 < n)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n)
    (C : Matrix (BalancedSet n k) (Fin k) ℂ) (i : Fin n) (s : Fin d) :
    bandRestriction hn ζ C i s =
      blockRestriction ζ (pairFrequency hn) (fun p : FrequencyPair n k => ζ ^ p.2.val)
        (fun p => C p.1 p.2) i s := by
  classical
  unfold bandRestriction blockRestriction
  simp only [Matrix.mul_apply, Matrix.transpose_apply, fourierU, fourierV]
  simp_rw [sum_mul]
  rw [sum_comm]
  rw [Fintype.sum_prod_type]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  dsimp [pairFrequency]
  rw [root_power_period hζ, pow_add]
  have hf : ζ ^ ((a.val.val + b.val) % n) =
      ζ ^ a.val.val * ζ ^ b.val := by
    rw [← pow_eq_pow_mod _ hζ.pow_eq_one, pow_add]
  rw [hf, mul_pow]
  ring

theorem balanced_fourier_restriction_injective {n k d : ℕ} (hn : 0 < n)
    (hk : k ≤ n) (hkd : k * k ≤ n * d)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n) :
    Function.Injective (fun C : Matrix (BalancedSet n k) (Fin k) ℂ =>
      fun i : Fin n => fun s : Fin d => bandRestriction hn ζ C i s) := by
  classical
  intro C D h
  have he := fourier_blocks_injective hζ (pairFrequency hn)
    (fun p : FrequencyPair n k => ζ ^ p.2.val)
    (balanced_fiber_card hn hk hkd) (fun f => ?_) (a₁ := fun p => C p.1 p.2)
    (a₂ := fun p => D p.1 p.2) ?_
  · ext a b
    exact congr_fun he (a, b)
  · intro p q hpq
    apply pairFrequency_second_injective hn f
    apply Fin.ext
    exact hζ.pow_inj (lt_of_lt_of_le p.val.2.isLt hk)
      (lt_of_lt_of_le q.val.2.isLt hk) hpq
  · funext i s
    exact (bandRestriction_eq_blocks hn hζ C i s).symm.trans
      ((congr_fun (congr_fun h i) s).trans (bandRestriction_eq_blocks hn hζ D i s))

#print axioms bandRestriction_eq_blocks
#print axioms balanced_fourier_restriction_injective
end Circulant
```

### `PolynomialObstruction.lean`

```lean
import CirculantStatement
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

noncomputable section
namespace Circulant
open MvPolynomial

/-- Polynomial maps from fewer affine parameters satisfy a nonzero relation.
This is a genuine pointwise polynomial certificate, but does not itself supply
the rational charts for the determinantal variety. -/
theorem polynomial_map_obstruction {a b : ℕ}
    (f : Fin b → MvPolynomial (Fin a) ℂ) (hab : a < b) :
    ∃ p : MvPolynomial (Fin b) ℂ, p ≠ 0 ∧
      ∀ x : Fin a → ℂ, eval (fun i => eval x (f i)) p = 0 := by
  have hdep : ¬ AlgebraicIndependent ℂ f := by
    intro hi
    have h := hi.cardinalMk_le_trdeg
    simp only [MvPolynomial.trdeg_of_isDomain, Cardinal.mk_fintype,
      Fintype.card_fin, Cardinal.lift_natCast] at h
    have hba : b ≤ a := by exact_mod_cast h
    omega
  rw [algebraicIndependent_iff] at hdep
  push Not at hdep
  obtain ⟨p, hp, hpne⟩ := hdep
  refine ⟨p, hpne, ?_⟩
  intro x
  have he : eval x (aeval f p) = eval (fun i => eval x (f i)) p := by
    have hh : (aeval x).comp (aeval f) = aeval (fun i => eval x (f i)) := by
      ext i
      simp
    exact congr_arg (fun g : MvPolynomial (Fin b) ℂ →ₐ[ℂ] ℂ => g p) hh
  rw [hp, map_zero] at he
  exact he.symm

#print axioms polynomial_map_obstruction
end Circulant
```

### `CirculantCertificate.lean`

```lean
import CirculantFourier
import CirculantStatement

noncomputable section
namespace Circulant
set_option backward.isDefEq.respectTransparency false
open Matrix Finset

theorem powers_columns_independent {P : Type*} [Fintype P] {n : ℕ}
    (z : P → ℂ) (hz : Function.Injective z) (hn : Fintype.card P ≤ n) :
    LinearIndependent ℂ (fun p : P => fun i : Fin n => z p ^ i.val) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc p
  have hcz : c = 0 := by
    apply moments_zero z c hz hn
    intro i
    have hi := congr_fun hc i
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using hi
  exact congr_fun hcz p

theorem fourierU_rank {n k : ℕ} (hn : 0 < n) (hk : k ≤ n)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n) :
    (fourierU n k ζ).rank = k := by
  classical
  have hz : Function.Injective (fun a : BalancedSet n k => ζ ^ a.val.val) := by
    intro a b he
    apply Subtype.ext
    exact Fin.ext (hζ.pow_inj a.val.isLt b.val.isLt he)
  have hcard : Fintype.card (BalancedSet n k) ≤ n := by
    rw [balancedSet_card hn hk]
    exact hk
  have hi := powers_columns_independent _ hz hcard
  have hr := LinearIndependent.rank_matrix
    (M := (fourierU n k ζ).transpose) hi
  rw [Matrix.rank_transpose, balancedSet_card hn hk] at hr
  exact hr

theorem fourierV_rank {n k : ℕ} (hk : k ≤ n)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n) :
    (fourierV n k ζ).rank = k := by
  have hz : Function.Injective (fun b : Fin k => ζ ^ b.val) := by
    intro a b he
    exact Fin.ext (hζ.pow_inj (lt_of_lt_of_le a.isLt hk)
      (lt_of_lt_of_le b.isLt hk) he)
  have hi := powers_columns_independent _ hz (n := n) (by simpa)
  have hr := LinearIndependent.rank_matrix
    (M := (fourierV n k ζ).transpose) hi
  simpa only [Matrix.rank_transpose, Fintype.card_fin] using hr

/-- Every square collision block has a nonzero actual complex Vandermonde determinant. -/
theorem fiber_vandermonde_det_ne_zero {n k : ℕ} (hn : 0 < n) (hk : k ≤ n)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n) (f : Fin n) :
    let F := {p : FrequencyPair n k // pairFrequency hn p = f}
    let e := (Fintype.equivFin F).symm
    (Matrix.vandermonde (fun j : Fin (Fintype.card F) => ζ ^ (e j).val.2.val)).det ≠ 0 := by
  classical
  dsimp only
  apply Matrix.det_vandermonde_ne_zero_iff.mpr
  intro a b he
  apply (Fintype.equivFin {p : FrequencyPair n k // pairFrequency hn p = f}).symm.injective
  apply pairFrequency_second_injective hn f
  apply Fin.ext
  exact hζ.pow_inj (lt_of_lt_of_le ((Fintype.equivFin _).symm a).val.2.isLt hk)
    (lt_of_lt_of_le ((Fintype.equivFin _).symm b).val.2.isLt hk) he

/-- Uniform finite core: an actual primitive root, actual full-rank Fourier
matrices, and injective restriction of UCVᵀ to the missing cyclic band.
This theorem does NOT assert generic completion rank. -/
theorem uniform_fourier_certificate {n k d : ℕ} (hn : 0 < n) (hk : k ≤ n)
    (hkd : k * k ≤ n * d) :
    ∃ ζ : ℂ, IsPrimitiveRoot ζ n ∧
      (fourierU n k ζ).rank = k ∧ (fourierV n k ζ).rank = k ∧
      Function.Injective (fun C : Matrix (BalancedSet n k) (Fin k) ℂ =>
        fun i : Fin n => fun s : Fin d => bandRestriction hn ζ C i s) := by
  let ζ := Complex.exp (2 * Real.pi * Complex.I / n)
  have hζ : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp n (ne_of_gt hn)
  exact ⟨ζ, hζ, fourierU_rank hn hk hζ, fourierV_rank hk hζ,
    balanced_fourier_restriction_injective hn hk hkd hζ⟩

/-- The finite certificate specialized to the exact missing pattern and integer
corank in Conjecture 5.6. The conclusion is still a finite tensor statement. -/
theorem circulant_fourier_certificate {n : ℕ} (l : ℕ) (hn : 0 < n) :
    let k := Nat.sqrt (n * (n - l))
    ∃ ζ : ℂ, IsPrimitiveRoot ζ n ∧
      (fourierU n k ζ).rank = k ∧ (fourierV n k ζ).rank = k ∧
      Function.Injective (fun C : Matrix (BalancedSet n k) (Fin k) ℂ =>
        fun e : Unknown n l =>
          (fourierU n k ζ * C * (fourierV n k ζ).transpose) e.val.1 e.val.2) := by
  classical
  dsimp only
  let k := Nat.sqrt (n * (n - l))
  have hk : k ≤ n := by
    have hs := Nat.sqrt_le_sqrt (Nat.mul_le_mul_left n (Nat.sub_le n l))
    simpa only [Nat.sqrt_eq] using hs
  obtain ⟨ζ, hζ, hU, hV, hi⟩ :=
    uniform_fourier_certificate hn hk (Nat.sqrt_le (n * (n - l)))
  refine ⟨ζ, hζ, hU, hV, ?_⟩
  intro C D he
  apply hi
  funext i s
  exact congr_fun he
    ⟨(i, ⟨(i.val + s.val) % n, Nat.mod_lt _ hn⟩), ⟨s.val, s.isLt, rfl⟩⟩

#print axioms circulant_fourier_certificate
#print axioms fourierU_rank
#print axioms fourierV_rank
#print axioms fiber_vandermonde_det_ne_zero
#print axioms uniform_fourier_certificate
end Circulant
```

### `CirculantAudit.lean`

```lean
import CirculantCertificate
import PolynomialObstruction

#eval Lean.versionString
#print Circulant.Unknown
#print Circulant.Observed
#print Circulant.Agrees
#print Circulant.CompletionRank
#print Circulant.ZeroLocus
#print Circulant.ZOpen
#print Circulant.GCR
#print Circulant.LiteralConjecture

#check Circulant.completionRank_attained
#check Circulant.completionRank_le_iff
#check Circulant.gcr_unique
#check Circulant.gcr_of_polynomial_certificates
#check Circulant.balanced_window_bound
#check Circulant.balanced_window_card
#check Circulant.balancedSet_card
#check Circulant.balanced_fiber_card
#check Circulant.polynomial_map_obstruction
#check Circulant.fourierU_rank
#check Circulant.fourierV_rank
#check Circulant.fiber_vandermonde_det_ne_zero
#check Circulant.uniform_fourier_certificate
#check Circulant.circulant_fourier_certificate

#print axioms Circulant.completionRank_attained
#print axioms Circulant.completionRank_le_iff
#print axioms Circulant.gcr_unique
#print axioms Circulant.gcr_of_polynomial_certificates
#print axioms Circulant.balanced_window_bound
#print axioms Circulant.balanced_window_card
#print axioms Circulant.balancedSet_card
#print axioms Circulant.balanced_fiber_card
#print axioms Circulant.polynomial_map_obstruction
#print axioms Circulant.fourierU_rank
#print axioms Circulant.fourierV_rank
#print axioms Circulant.fiber_vandermonde_det_ne_zero
#print axioms Circulant.uniform_fourier_certificate
#print axioms Circulant.circulant_fourier_certificate
```

### `GenericImage.lean`

```lean
import Mathlib.RingTheory.Spectrum.Prime.Chevalley
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.AlgebraicIndependent.Defs
import Mathlib.RingTheory.MvPolynomial.Basic

/-! Actual affine-point generic lifting, using Chevalley and Nullstellensatz. -/
noncomputable section
namespace Circulant
open MvPolynomial

/-- A constructible spectrum image containing the zero prime contains D(p), p ≠ 0. -/
theorem spectrum_principal_open_of_injective
    {R S : Type*} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    (f : R →+* S) (hf : Function.Injective f) (hfp : f.FinitePresentation) :
    ∃ p : R, p ≠ 0 ∧ ∀ q : PrimeSpectrum R,
      p ∉ q.asIdeal → ∃ Q : PrimeSpectrum S, PrimeSpectrum.comap f Q = q := by
  classical
  let ηR : PrimeSpectrum R := ⟨⊥, inferInstance⟩
  let ηS : PrimeSpectrum S := ⟨⊥, inferInstance⟩
  have hη : PrimeSpectrum.comap f ηS = ηR := by
    apply PrimeSpectrum.ext
    exact (RingHom.injective_iff_ker_eq_bot f).mp hf
  obtain ⟨T, hT⟩ := PrimeSpectrum.exists_constructibleSetData_iff.mpr
    (PrimeSpectrum.isConstructible_range_comap hfp)
  have hmem : ηR ∈ T.toSet := hT ▸ ⟨ηS, hη⟩
  simp only [PrimeSpectrum.ConstructibleSetData.toSet, Set.mem_iUnion] at hmem
  obtain ⟨C, hCT, hC⟩ := hmem
  have hg : ∀ i, C.g i = 0 := by
    intro i
    exact hC.1 (Set.mem_range_self i)
  have hp : C.f ≠ 0 := by
    intro hz
    apply hC.2
    intro r hr
    rcases Set.mem_singleton_iff.mp hr with rfl
    exact hz
  refine ⟨C.f, hp, ?_⟩
  intro q hq
  have hqT : q ∈ T.toSet := by
    apply Set.mem_iUnion.mpr ⟨C, ?_⟩
    apply Set.mem_iUnion.mpr ⟨hCT, ?_⟩
    constructor
    · rintro r ⟨i, rfl⟩
      rw [hg i]
      exact q.asIdeal.zero_mem
    · intro h
      exact hq (h (Set.mem_singleton _))
  rw [hT] at hqT
  exact hqT

/-- A spectrum preimage of an evaluation ideal gives a genuine complex preimage. -/
theorem polynomial_point_lift {I J : Type*} [Finite I]
    (f : J → MvPolynomial I ℂ) (y : J → ℂ)
    (Q : PrimeSpectrum (MvPolynomial I ℂ))
    (hQ : PrimeSpectrum.comap (MvPolynomial.aeval f).toRingHom Q =
      MvPolynomial.pointToPoint (k := ℂ) y) :
    ∃ x : I → ℂ, ∀ j, MvPolynomial.eval x (f j) = y j := by
  obtain ⟨N, hN, hQN⟩ := Ideal.exists_le_maximal Q.asIdeal Q.isPrime.ne_top
  obtain ⟨x, hx⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal ℂ hN
  refine ⟨x, ?_⟩
  intro j
  have hrel : X j - C (y j) ∈ (PrimeSpectrum.comap (aeval (R := ℂ) f).toRingHom Q).asIdeal := by
    rw [hQ]
    change X j - C (y j) ∈ MvPolynomial.vanishingIdeal ℂ {y}
    rw [MvPolynomial.mem_vanishingIdeal_singleton_iff]
    simp
  have hrel' : f j - C (y j) ∈ Q.asIdeal := by
    simpa only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, map_sub, aeval_X, aeval_C, algebraMap_eq] using hrel
  have hv : f j - C (y j) ∈ MvPolynomial.vanishingIdeal ℂ {x} := hx ▸ hQN hrel'
  rw [MvPolynomial.mem_vanishingIdeal_singleton_iff] at hv
  simpa [sub_eq_zero] using hv

/-- Algebraically independent polynomial coordinates attain every complex point
of a nonempty principal open. No rational inverse is asserted. -/
theorem algebraicIndependent_open_image {I J : Type*} [Finite I] [Finite J]
    (f : J → MvPolynomial I ℂ) (hf : AlgebraicIndependent ℂ f) :
    ∃ p : MvPolynomial J ℂ, p ≠ 0 ∧
      ∀ y : J → ℂ, MvPolynomial.eval y p ≠ 0 →
        ∃ x : I → ℂ, ∀ j, MvPolynomial.eval x (f j) = y j := by
  have hft : (aeval (R := ℂ) f).toRingHom.FiniteType := by
    apply RingHom.FiniteType.of_comp_finiteType (f := MvPolynomial.C)
    have he : (aeval (R := ℂ) f).toRingHom.comp MvPolynomial.C =
        (algebraMap ℂ (MvPolynomial I ℂ)) := by ext; simp
    rw [he, RingHom.finiteType_algebraMap]
    infer_instance
  have hfp : (aeval (R := ℂ) f).toRingHom.FinitePresentation :=
    RingHom.FinitePresentation.of_finiteType.mp hft
  obtain ⟨p, hp, h⟩ := spectrum_principal_open_of_injective
    (aeval (R := ℂ) f).toRingHom hf hfp
  refine ⟨p, hp, ?_⟩
  intro y hy
  have hpy : p ∉ (MvPolynomial.pointToPoint (k := ℂ) y).asIdeal := by
    simpa only [MvPolynomial.pointToPoint, MvPolynomial.mem_vanishingIdeal_singleton_iff,
      MvPolynomial.aeval_eq_eval] using hy
  obtain ⟨Q, hQ⟩ := h _ hpy
  exact polynomial_point_lift f y Q hQ

end Circulant
#print axioms Circulant.spectrum_principal_open_of_injective
#print axioms Circulant.polynomial_point_lift
#print axioms Circulant.algebraicIndependent_open_image
```

### `JacobianCriterion.lean`

```lean
import GenericImage
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-! The characteristic-zero Jacobian criterion and actual generic lifting. -/
noncomputable section
namespace Circulant
set_option backward.isDefEq.respectTransparency false
open MvPolynomial Matrix
open scoped BigOperators

/-- Formal polynomial chain rule, before evaluating at any point. -/
theorem pderiv_aeval {I J : Type*} [Fintype J]
    (f : J → MvPolynomial I ℂ) (p : MvPolynomial J ℂ) (i : I) :
    pderiv i (aeval f p) =
      ∑ j, aeval f (pderiv j p) * pderiv i (f j) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq =>
    simp only [map_add, hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p j hp =>
    simp only [map_mul, aeval_X, pderiv_mul, hp, map_add]
    simp only [Finset.sum_add_distrib, add_mul, mul_assoc]
    congr 1
    · rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      ring
    · simp [pderiv_X, Pi.single_apply, mul_comm]

/-- A nonzero partial derivative strictly lowers total degree. -/
theorem pderiv_totalDegree_lt {J : Type*} (p : MvPolynomial J ℂ) (j : J)
    (h : pderiv j p ≠ 0) : (pderiv j p).totalDegree < p.totalDegree := by
  classical
  have hm : ∀ m ∈ (pderiv j p).support,
      m.sum (fun _ e => e) < p.totalDegree := by
    intro m hm
    have hc : p.coeff (m + Finsupp.single j (1 : ℕ)) ≠ 0 := by
      have hc := (MvPolynomial.mem_support_iff.mp hm)
      rw [coeff_pderiv] at hc
      exact (mul_ne_zero_iff.mp hc).1
    have hd := MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hc)
    have hs : (m + Finsupp.single j (1 : ℕ)).sum (fun _ e => e) =
        m.sum (fun _ e => e) + 1 := by
      rw [Finsupp.sum_add_index'] <;> simp
    rw [hs] at hd
    omega
  have hpos : 0 < p.totalDegree := by
    obtain ⟨m, hm'⟩ := (MvPolynomial.support_nonempty.mpr h)
    exact lt_of_le_of_lt (Nat.zero_le _) (hm m hm')
  exact Finset.sup_lt_iff hpos |>.mpr hm

/-- In characteristic zero, vanishing of all partial derivatives means constant. -/
theorem eq_C_of_pderiv_eq_zero {J : Type*} (p : MvPolynomial J ℂ)
    (h : ∀ j, pderiv j p = 0) : p = C (p.coeff 0) := by
  classical
  ext m
  by_cases hm : m = 0
  · subst m; simp
  · rw [coeff_C, ite_eq_right (Ne.symm hm)]
    obtain ⟨j, hj⟩ := Finsupp.support_nonempty_iff.mpr hm
    have hj' : m j ≠ 0 := Finsupp.mem_support_iff.mp hj
    have he : m - Finsupp.single j (1 : ℕ) + Finsupp.single j (1 : ℕ) = m :=
      tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hj'))
    have hc := congr_arg (fun q : MvPolynomial J ℂ =>
      q.coeff (m - Finsupp.single j (1 : ℕ))) (h j)
    rw [coeff_pderiv, he] at hc
    simp only [AddMonoidAlgebra.coeff_zero] at hc
    have hjval : (m - Finsupp.single j (1 : ℕ) : J →₀ ℕ) j + 1 = m j := by
      simpa using congr_fun (congr_arg (fun s : J →₀ ℕ => (s : J → ℕ)) he) j
    have hcast : (((m - Finsupp.single j (1 : ℕ) : J →₀ ℕ) j : ℕ) : ℂ) + 1 = (m j : ℂ) := by
      exact_mod_cast hjval
    rw [hcast] at hc
    change p.coeff m * (m j : ℂ) = 0 at hc
    exact (mul_eq_zero.mp hc).resolve_right (by exact_mod_cast hj')

/-- A nonzero square Jacobian minor forbids all nonzero polynomial relations. -/
theorem algebraicIndependent_of_jacobian_minor {I J : Type*} [Fintype J] [DecidableEq J]
    (f : J → MvPolynomial I ℂ) (cols : J → I)
    (hJ : Matrix.det (fun i j : J => pderiv (cols j) (f i)) ≠ 0) :
    AlgebraicIndependent ℂ f := by
  classical
  rw [algebraicIndependent_iff]
  by_contra hdep
  push Not at hdep
  obtain ⟨p, hp, hpne⟩ := hdep
  have hex : ∃ d : ℕ, ∃ p : MvPolynomial J ℂ,
      p ≠ 0 ∧ aeval f p = 0 ∧ p.totalDegree = d := ⟨_, p, hpne, hp, rfl⟩
  obtain ⟨p, hpne, hp, hdeg⟩ := Nat.find_spec hex
  have hpartials : ∀ j, aeval f (pderiv j p) = 0 := by
    let v : J → MvPolynomial I ℂ := fun j => aeval f (pderiv j p)
    let A : Matrix J J (MvPolynomial I ℂ) := fun i j => pderiv (cols j) (f i)
    have hvA : v ᵥ* A = 0 := by
      funext j
      have hchain := pderiv_aeval f p (cols j)
      rw [hp, map_zero] at hchain
      exact hchain.symm
    have hv : v = 0 := by
      by_contra hv
      exact hJ (Matrix.exists_vecMul_eq_zero_iff.mp ⟨v, hv, hvA⟩)
    exact fun j => congr_fun hv j
  have hzero : ∀ j, pderiv j p = 0 := by
    intro j
    by_contra hne
    have hlt : (pderiv j p).totalDegree < Nat.find hex := by
      rw [← hdeg]
      exact pderiv_totalDegree_lt p j hne
    exact Nat.find_min hex hlt ⟨pderiv j p, hne, hpartials j, rfl⟩
  have hc := eq_C_of_pderiv_eq_zero p hzero
  have hz : p.coeff 0 = 0 := by
    rw [hc] at hp
    simpa using hp
  exact hpne (by rw [hc, hz, C_0])

/-- A nonzero Jacobian minor at one point gives a nonempty principal open in
its actual complex point image. This is the abstract generic upper-bound bridge. -/
theorem jacobian_minor_open_image {I J : Type*} [Finite I] [Fintype J] [DecidableEq J]
    (f : J → MvPolynomial I ℂ) (cols : J → I) (z : I → ℂ)
    (hJ : Matrix.det (fun i j : J =>
      eval z (pderiv (cols j) (f i))) ≠ 0) :
    ∃ p : MvPolynomial J ℂ, p ≠ 0 ∧
      ∀ y : J → ℂ, eval y p ≠ 0 →
        ∃ x : I → ℂ, ∀ j, eval x (f j) = y j := by
  apply algebraicIndependent_open_image f
  apply algebraicIndependent_of_jacobian_minor f cols
  intro hz
  apply hJ
  have he := congr_arg (eval z) hz
  have he' := (RingHom.map_det (eval z) _).symm.trans he
  have hmap : (eval z).mapMatrix (fun i j : J => pderiv (cols j) (f i)) =
      (fun i j : J => eval z (pderiv (cols j) (f i))) := by
    ext i j
    rfl
  rw [hmap, map_zero] at he'
  exact he'

end Circulant
#print axioms Circulant.pderiv_aeval
#print axioms Circulant.pderiv_totalDegree_lt
#print axioms Circulant.eq_C_of_pderiv_eq_zero
#print axioms Circulant.algebraicIndependent_of_jacobian_minor
#print axioms Circulant.jacobian_minor_open_image
```

### `MatrixKernel.lean`

```lean
import CirculantStatement
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Ordinary bilinear kernel complements, with no Hermitian orthogonality. -/
noncomputable section
namespace Circulant
set_option backward.isDefEq.respectTransparency false
open Matrix Module

/-- A rank-k column space is the kernel of the transpose of an n×(n−k)
matrix. The quotient construction handles k=0 and k=n as well. -/
theorem exists_transpose_kernel {n k : ℕ} {A : Type*} [Fintype A]
    (U : Matrix (Fin n) A ℂ) (hU : U.rank = k) :
    ∃ P : Matrix (Fin n) (Fin (n-k)) ℂ,
      LinearMap.ker P.transpose.mulVecLin = LinearMap.range U.mulVecLin := by
  classical
  let W := LinearMap.range U.mulVecLin
  have hW : Module.finrank ℂ W = k := hU
  have hdim : Module.finrank ℂ ((Fin n → ℂ) ⧸ W) = n-k := by
    have h := W.finrank_quotient_add_finrank
    rw [Module.finrank_fin_fun, hW] at h
    omega
  let e := (Module.finBasisOfFinrankEq ℂ ((Fin n → ℂ) ⧸ W) hdim).equivFun
  let L := e.toLinearMap.comp W.mkQ
  let P := (LinearMap.toMatrix' L).transpose
  refine ⟨P, ?_⟩
  have hL : P.transpose.mulVecLin = L := by
    apply LinearMap.ext
    intro x
    funext i
    exact congr_fun (LinearMap.toMatrix'_mulVec L x) i
  rw [hL, LinearEquiv.ker_comp, Submodule.ker_mkQ]

/-- Matrix factorization from column-space containment; no choice of basis in
the containing space is required. -/
theorem exists_matrix_factor_of_range_le {m n a : Type*}
    [Fintype n] [Fintype a] (U : Matrix m a ℂ) (N : Matrix m n ℂ)
    (h : LinearMap.range N.mulVecLin ≤ LinearMap.range U.mulVecLin) :
    ∃ D : Matrix a n ℂ, U * D = N := by
  classical
  have hc : ∀ j : n, ∃ c : a → ℂ, U *ᵥ c = N.col j := by
    intro j
    have hNj : N.col j ∈ LinearMap.range N.mulVecLin := by
      refine ⟨Pi.single j 1, ?_⟩
      ext i
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    exact h hNj
  choose c hc using hc
  refine ⟨fun a j => c j a, ?_⟩
  ext i j
  exact congr_fun (hc j) i

/-- Factor through a column space while preserving a right-kernel equation.
A linear splitting of the range removes any need to assume U injective. -/
theorem exists_matrix_factor_preserving_zero {m n a b : Type*}
    [Fintype m] [Fintype n] [Fintype a] [Fintype b]
    (U : Matrix m a ℂ) (N : Matrix m n ℂ) (Q : Matrix n b ℂ)
    (h : LinearMap.range N.mulVecLin ≤ LinearMap.range U.mulVecLin)
    (hNQ : N * Q = 0) :
    ∃ D : Matrix a n ℂ, U * D = N ∧ D * Q = 0 := by
  classical
  obtain ⟨g, hg⟩ := U.mulVecLin.rangeRestrict.exists_rightInverse_of_surjective
    U.mulVecLin.range_rangeRestrict
  obtain ⟨L, hL⟩ := g.exists_extend
  let W := LinearMap.toMatrix' L
  have hUL (x : m → ℂ) (hx : x ∈ LinearMap.range U.mulVecLin) :
      U *ᵥ (L x) = x := by
    have h1 := LinearMap.congr_fun hL ⟨x, hx⟩
    have h2 := congr_arg Subtype.val (LinearMap.congr_fun hg ⟨x, hx⟩)
    change L x = g ⟨x, hx⟩ at h1
    rw [h1]
    exact h2
  refine ⟨W * N, ?_, ?_⟩
  · ext i j
    have hc : N.col j ∈ LinearMap.range N.mulVecLin := by
      refine ⟨Pi.single j 1, ?_⟩
      ext i
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    have he := hUL (N.col j) (h hc)
    have hw : (W * N).col j = L (N.col j) := by
      exact LinearMap.toMatrix'_mulVec L (N.col j)
    change (U *ᵥ (W * N).col j) i = N.col j i
    rw [hw]
    exact congr_fun he i
  · rw [Matrix.mul_assoc, hNQ, Matrix.mul_zero]

end Circulant
#print axioms Circulant.exists_transpose_kernel
#print axioms Circulant.exists_matrix_factor_of_range_le

#print axioms Circulant.exists_matrix_factor_preserving_zero
```

### `TensorAnnihilator.lean`

```lean
import MatrixKernel

/-! The matrix annihilator in the proof's differential argument. -/
noncomputable section
namespace Circulant
set_option backward.isDefEq.respectTransparency false
open Matrix

theorem range_le_kernel_of_mul_zero {m n a : Type*}
    [Fintype m] [Fintype n] (A : Matrix a m ℂ) (N : Matrix m n ℂ)
    (h : A * N = 0) : LinearMap.range N.mulVecLin ≤ LinearMap.ker A.mulVecLin := by
  rintro _ ⟨x, rfl⟩
  change A *ᵥ (N *ᵥ x) = 0
  rw [Matrix.mulVec_mulVec, h, Matrix.zero_mulVec]

/-- Every matrix annihilating the factorization differential belongs to U⊗V.
All transposes are ordinary transposes over ℂ. -/
theorem annihilator_tensor_factor {n r : ℕ} {A B : Type*} [Fintype A] [Fintype B]
    (U : Matrix (Fin n) A ℂ) (V : Matrix (Fin n) B ℂ)
    (P Q : Matrix (Fin n) (Fin r) ℂ)
    (hP : LinearMap.ker P.transpose.mulVecLin = LinearMap.range U.mulVecLin)
    (hQ : LinearMap.ker Q.transpose.mulVecLin = LinearMap.range V.mulVecLin)
    (N : Matrix (Fin n) (Fin n) ℂ) (hNQ : N * Q = 0)
    (hNP : N.transpose * P = 0) :
    ∃ C : Matrix A B ℂ, U * C * V.transpose = N := by
  have hPN : P.transpose * N = 0 := by
    have ht := congr_arg Matrix.transpose hNP
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero] using ht
  have hrange : LinearMap.range N.mulVecLin ≤ LinearMap.range U.mulVecLin := by
    rw [← hP]
    exact range_le_kernel_of_mul_zero _ _ hPN
  obtain ⟨D, hUD, hDQ⟩ := exists_matrix_factor_preserving_zero U N Q hrange hNQ
  have hQD : Q.transpose * D.transpose = 0 := by
    have ht := congr_arg Matrix.transpose hDQ
    simpa only [Matrix.transpose_mul, Matrix.transpose_zero] using ht
  have hrangeD : LinearMap.range D.transpose.mulVecLin ≤ LinearMap.range V.mulVecLin := by
    rw [← hQ]
    exact range_le_kernel_of_mul_zero _ _ hQD
  obtain ⟨C, hVC⟩ := exists_matrix_factor_of_range_le V D.transpose hrangeD
  refine ⟨C.transpose, ?_⟩
  have hCV : C.transpose * V.transpose = D := by
    have ht := congr_arg Matrix.transpose hVC
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose] using ht
  rw [Matrix.mul_assoc, hCV, hUD]

/-- Injectivity on the missing mask kills an annihilator supported on the
observed mask. This is the finite duality core of differential surjectivity. -/
theorem tensor_annihilator_zero {n r : ℕ} {A B : Type*} [Fintype A] [Fintype B]
    (E : Set (Fin n × Fin n))
    (U : Matrix (Fin n) A ℂ) (V : Matrix (Fin n) B ℂ)
    (P Q : Matrix (Fin n) (Fin r) ℂ)
    (hP : LinearMap.ker P.transpose.mulVecLin = LinearMap.range U.mulVecLin)
    (hQ : LinearMap.ker Q.transpose.mulVecLin = LinearMap.range V.mulVecLin)
    (hinj : Function.Injective (fun C : Matrix A B ℂ =>
      fun e : ↥(Eᶜ) => (U * C * V.transpose) e.val.1 e.val.2))
    (N : Matrix (Fin n) (Fin n) ℂ) (hNQ : N * Q = 0)
    (hNP : N.transpose * P = 0) (hNH : ∀ e : ↥(Eᶜ), N e.val.1 e.val.2 = 0) : N = 0 := by
  obtain ⟨C, hC⟩ := annihilator_tensor_factor U V P Q hP hQ N hNQ hNP
  have hC0 : C = 0 := by
    apply hinj
    funext e
    change (U * C * V.transpose) e.val.1 e.val.2 =
      (U * (0 : Matrix A B ℂ) * V.transpose) e.val.1 e.val.2
    simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_apply]
    rw [hC]
    exact hNH e
  rw [hC0, Matrix.mul_zero, Matrix.zero_mul] at hC
  exact hC.symm

end Circulant
#print axioms Circulant.range_le_kernel_of_mul_zero
#print axioms Circulant.annihilator_tensor_factor
#print axioms Circulant.tensor_annihilator_zero
```

### `SquareMinor.lean`

```lean
import MatrixKernel

noncomputable section
namespace Circulant
set_option backward.isDefEq.respectTransparency false
open Matrix

/-- Select an actual square nonsingular column minor from independent rows. -/
theorem exists_nonsingular_minor {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq J] (A : Matrix J I ℂ) (hA : LinearIndependent ℂ A.row) :
    ∃ cols : J → I, Matrix.det (fun i j => A i (cols j)) ≠ 0 := by
  classical
  have hrank : A.rank = Fintype.card J := LinearIndependent.rank_matrix hA
  have hspan : Submodule.span ℂ (Set.range A.col) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← Matrix.rank_eq_finrank_span_cols, hrank]
    simp
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' ℂ A.col
  let : Finite κ := Finite.of_injective a ha
  let : Fintype κ := Fintype.ofFinite κ
  let b : Module.Basis κ ℂ (J → ℂ) := Module.Basis.mk hli (by rw [hsp, hspan])
  have hcard : Fintype.card J = Fintype.card κ := by
    rw [← Module.finrank_eq_card_basis b]
    simp
  let e : J ≃ κ := Fintype.equivOfCardEq hcard
  refine ⟨a ∘ e, ?_⟩
  have hi : LinearIndependent ℂ (fun j : J => (fun i => A i (a (e j)))) :=
    hli.comp e e.injective
  have hu : IsUnit (show Matrix J J ℂ from fun i j => A i (a (e j))) :=
    Matrix.linearIndependent_cols_iff_isUnit.mp hi
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero

end Circulant
#print axioms Circulant.exists_nonsingular_minor
```

### `FactorJacobian.lean`

```lean
import TensorAnnihilator
import SquareMinor
import Mathlib.Algebra.MvPolynomial.PDeriv

noncomputable section
namespace Circulant
set_option backward.isDefEq.respectTransparency false
open Matrix MvPolynomial
open scoped BigOperators

abbrev FactorVars (n r : ℕ) := (Fin n × Fin r) ⊕ (Fin n × Fin r)

def factorPolynomial {n r : ℕ} (ij : Fin n × Fin n) : MvPolynomial (FactorVars n r) ℂ :=
  ∑ k : Fin r, X (Sum.inl (ij.1,k)) * X (Sum.inr (ij.2,k))

def factorPoint {n r : ℕ} (P Q : Matrix (Fin n) (Fin r) ℂ) : FactorVars n r → ℂ :=
  Sum.elim (fun ik => P ik.1 ik.2) (fun jk => Q jk.1 jk.2)

theorem factorPolynomial_eval {n r : ℕ} (x : FactorVars n r → ℂ) (ij : Fin n × Fin n) :
    eval x (factorPolynomial ij) =
      ((show Matrix (Fin n) (Fin r) ℂ from fun i k => x (Sum.inl (i,k))) *
        Matrix.transpose (show Matrix (Fin n) (Fin r) ℂ from fun j k => x (Sum.inr (j,k)))) ij.1 ij.2 := by
  simp [factorPolynomial, Matrix.mul_apply, Matrix.transpose_apply]

theorem factorPolynomial_pderiv_left {n r : ℕ} (ij : Fin n × Fin n) (i : Fin n) (a : Fin r) :
    pderiv (Sum.inl (i,a)) (factorPolynomial ij) =
      if ij.1 = i then X (Sum.inr (ij.2,a)) else 0 := by
  classical
  by_cases hi : ij.1 = i
  · simp [factorPolynomial, pderiv_X, Pi.single_apply, hi, eq_comm]
  · simp [factorPolynomial, pderiv_X, hi]

theorem factorPolynomial_pderiv_right {n r : ℕ} (ij : Fin n × Fin n) (j : Fin n) (a : Fin r) :
    pderiv (Sum.inr (j,a)) (factorPolynomial ij) =
      if ij.2 = j then X (Sum.inl (ij.1,a)) else 0 := by
  classical
  by_cases hj : ij.2 = j
  · simp [factorPolynomial, pderiv_X, Pi.single_apply, hj, eq_comm]
  · simp [factorPolynomial, pderiv_X, hj]

/-- Coefficients on E extended by zero, paired with arbitrary ambient entries. -/
theorem zeroFill_sum {n : ℕ} (E : Set (Fin n × Fin n)) [Fintype E]
    (c : E → ℂ) (g : Fin n × Fin n → ℂ) :
    (∑ e : E, c e * g e.val) = ∑ ij : Fin n × Fin n, zeroFill E c ij.1 ij.2 * g ij := by
  classical
  rw [← Fintype.sum_subtype_add_sum_subtype (fun ij => ij ∈ E)]
  have hE : ∀ e : E, zeroFill E c e.val.1 e.val.2 = c e := zeroFill_agrees E c
  simp only [hE]
  have hH : ∀ e : ↥(Eᶜ), zeroFill E c e.val.1 e.val.2 = 0 := by
    intro e
    have he : e.val ∉ E := e.property
    simp [zeroFill, he]
  simp only [hH, zero_mul, Finset.sum_const_zero, add_zero]
  apply Finset.sum_congr (by ext; simp)
  intro e _
  rfl

/-- The rows of the observed factorization Jacobian are independent when the
missing-coordinate tensor restriction is injective. -/
theorem factor_jacobian_rows_independent {n r : ℕ} {A B : Type*}
    [Fintype A] [Fintype B] (E : Set (Fin n × Fin n)) [Fintype E]
    (U : Matrix (Fin n) A ℂ) (V : Matrix (Fin n) B ℂ)
    (P Q : Matrix (Fin n) (Fin r) ℂ)
    (hP : LinearMap.ker P.transpose.mulVecLin = LinearMap.range U.mulVecLin)
    (hQ : LinearMap.ker Q.transpose.mulVecLin = LinearMap.range V.mulVecLin)
    (hinj : Function.Injective (fun C : Matrix A B ℂ =>
      fun e : ↥(Eᶜ) => (U * C * V.transpose) e.val.1 e.val.2)) :
    LinearIndependent ℂ (fun e : E => fun v : FactorVars n r =>
      eval (factorPoint P Q) (pderiv v (factorPolynomial e.val))) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc e
  let N := zeroFill E c
  have heq (v : FactorVars n r) :
      (∑ e : E, c e * eval (factorPoint P Q) (pderiv v (factorPolynomial e.val))) = 0 := by
    have h := congr_fun hc v
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using h
  have hNQ : N * Q = 0 := by
    ext i a
    have hv := heq (Sum.inl (i,a))
    simp only [factorPolynomial_pderiv_left, apply_ite, eval_X, map_zero,
      factorPoint, Sum.elim_inr] at hv
    simp only [← mul_ite] at hv
    rw [zeroFill_sum E c (fun ij => if ij.1 = i then Q ij.2 a else 0)] at hv
    simpa [Fintype.sum_prod_type, mul_ite, Matrix.mul_apply, N, eq_comm] using hv
  have hNP : N.transpose * P = 0 := by
    ext j a
    have hv := heq (Sum.inr (j,a))
    simp only [factorPolynomial_pderiv_right, apply_ite, eval_X, map_zero,
      factorPoint, Sum.elim_inl] at hv
    simp only [← mul_ite] at hv
    rw [zeroFill_sum E c (fun ij => if ij.2 = j then P ij.1 a else 0)] at hv
    rw [Fintype.sum_prod_type] at hv
    simp only [mul_ite, mul_zero] at hv
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_eq_left] at hv
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.zero_apply] using hv
  have hNH : ∀ e : ↥(Eᶜ), N e.val.1 e.val.2 = 0 := by
    intro e
    have he : e.val ∉ E := e.property
    simp [N, zeroFill, he]
  have hN := tensor_annihilator_zero E U V P Q hP hQ hinj N hNQ hNP hNH
  have hc0 := zeroFill_agrees E c e
  rw [show zeroFill E c = N from rfl, hN] at hc0
  exact hc0.symm

/-- Choose the kernel-complement base point and a nonsingular observed
Jacobian minor, directly in the two matrix-factor coordinate types. -/
theorem tensor_factor_jacobian {n k : ℕ} {A B : Type*}
    [Fintype A] [Fintype B] (E : Set (Fin n × Fin n)) [Fintype E] [DecidableEq E]
    (U : Matrix (Fin n) A ℂ) (V : Matrix (Fin n) B ℂ)
    (hU : U.rank = k) (hV : V.rank = k)
    (hinj : Function.Injective (fun C : Matrix A B ℂ =>
      fun e : ↥(Eᶜ) => (U * C * V.transpose) e.val.1 e.val.2)) :
    ∃ (P Q : Matrix (Fin n) (Fin (n-k)) ℂ) (cols : E → FactorVars n (n-k)),
      Matrix.det (fun i j : E => eval (factorPoint P Q)
        (pderiv (cols j) (factorPolynomial i.val))) ≠ 0 := by
  obtain ⟨P, hP⟩ := exists_transpose_kernel U hU
  obtain ⟨Q, hQ⟩ := exists_transpose_kernel V hV
  obtain ⟨cols, hcols⟩ := exists_nonsingular_minor
    (show Matrix E (FactorVars n (n-k)) ℂ from fun e v =>
      eval (factorPoint P Q) (pderiv v (factorPolynomial e.val)))
    (factor_jacobian_rows_independent E U V P Q hP hQ hinj)
  exact ⟨P, Q, cols, hcols⟩

end Circulant

#print axioms Circulant.factorPolynomial_eval
#print axioms Circulant.factorPolynomial_pderiv_left
#print axioms Circulant.factorPolynomial_pderiv_right
#print axioms Circulant.zeroFill_sum
#print axioms Circulant.factor_jacobian_rows_independent
#print axioms Circulant.tensor_factor_jacobian
```

### `CirculantUpper.lean`

```lean
import FactorJacobian
import JacobianCriterion
import CirculantCertificate

/-! Generic rank-at-most certificate on the literal observed-coordinate space. -/
noncomputable section
namespace Circulant
set_option backward.isDefEq.respectTransparency false
open Matrix MvPolynomial

/-- Injective restriction on the missing mask implies actual rank-at-most-n−k
completions on a nonempty complex principal open. -/
theorem tensor_upper_polynomial {n k : ℕ} {A B : Type*}
    [Fintype A] [Fintype B] (E : Set (Fin n × Fin n))
    (U : Matrix (Fin n) A ℂ) (V : Matrix (Fin n) B ℂ)
    (hU : U.rank = k) (hV : V.rank = k)
    (hinj : Function.Injective (fun C : Matrix A B ℂ =>
      fun e : ↥(Eᶜ) => (U * C * V.transpose) e.val.1 e.val.2)) :
    ∃ p : MvPolynomial E ℂ, p ≠ 0 ∧
      ∀ x : E → ℂ, eval x p ≠ 0 →
        ∃ M : Matrix (Fin n) (Fin n) ℂ, Agrees E x M ∧ M.rank ≤ n-k := by
  classical
  let : Fintype E := Fintype.ofFinite E
  obtain ⟨P, Q, cols, hJ⟩ := tensor_factor_jacobian E U V hU hV hinj
  obtain ⟨p, hp, hlift⟩ := jacobian_minor_open_image
    (fun e : E => factorPolynomial (r := n-k) e.val) cols (factorPoint P Q) hJ
  refine ⟨p, hp, ?_⟩
  intro y hy
  obtain ⟨x, hx⟩ := hlift y hy
  let L : Matrix (Fin n) (Fin (n-k)) ℂ := fun i a => x (Sum.inl (i,a))
  let R : Matrix (Fin n) (Fin (n-k)) ℂ := fun j a => x (Sum.inr (j,a))
  refine ⟨L * R.transpose, ?_, ?_⟩
  · intro e
    exact (factorPolynomial_eval x e.val).symm.trans (hx e)
  · exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_width L)

/-- Uniform upper certificate for every n>0 and every l, with the original
Unknown/Observed masks and actual Matrix.rank. -/
theorem circulant_upper_polynomial {n : ℕ} (l : ℕ) (hn : 0 < n) :
    ∃ p : MvPolynomial (Observed n l) ℂ, p ≠ 0 ∧
      ∀ x : Observed n l → ℂ, eval x p ≠ 0 →
        ∃ M : Matrix (Fin n) (Fin n) ℂ, Agrees (Observed n l) x M ∧
          M.rank ≤ n - Nat.sqrt (n*(n-l)) := by
  obtain ⟨ζ, _, hU, hV, hinj⟩ := circulant_fourier_certificate l hn
  apply tensor_upper_polynomial (Observed n l) _ _ hU hV
  intro C D h
  apply hinj
  funext e
  exact congr_fun h ⟨e.val, by
    change ¬ ¬ e.val ∈ Unknown n l
    exact not_not.mpr e.property⟩

end Circulant
#print axioms Circulant.tensor_upper_polynomial
#print axioms Circulant.circulant_upper_polynomial
```

### `RankFactorization.lean`

```lean
import MatrixKernel

/-! Rank-exactly-t matrices have a factorization normalized on t selected rows. -/
noncomputable section
namespace Circulant
set_option backward.isDefEq.respectTransparency false
open Matrix

theorem normalized_rank_factorization {n t : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    (hr : M.rank = t) :
    ∃ (s : Fin t ↪ Fin n) (P : Matrix (Fin n) (Fin t) ℂ)
      (Q : Matrix (Fin t) (Fin n) ℂ), M = P * Q ∧
        ∀ a b, P (s a) b = if a = b then 1 else 0 := by
  classical
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' ℂ M.row
  let : Finite κ := Finite.of_injective a ha
  let : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = t := by
    rw [← Module.finrank_eq_card_basis (Module.Basis.span hli), hsp]
    rw [← Matrix.rank_eq_finrank_span_row, hr]
  let e : Fin t ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
  let s : Fin t ↪ Fin n := ⟨a ∘ e, ha.comp e.injective⟩
  have hi : LinearIndependent ℂ (fun j : Fin t => M.row (s j)) := hli.comp e e.injective
  have hs : Submodule.span ℂ (Set.range (fun j : Fin t => M.row (s j))) =
      Submodule.span ℂ (Set.range M.row) := by
    rw [show Set.range (fun j : Fin t => M.row (s j)) = Set.range (M.row ∘ a) by
      simpa only [s, Function.comp_def, Function.Embedding.coeFn_mk] using
        e.surjective.range_comp (M.row ∘ a)]
    exact hsp
  let b := Module.Basis.span hi
  let row (i : Fin n) : Submodule.span ℂ (Set.range (fun j : Fin t => M.row (s j))) :=
    ⟨M.row i, hs ▸ Submodule.subset_span (Set.mem_range_self i)⟩
  let P : Matrix (Fin n) (Fin t) ℂ := fun i j => b.repr (row i) j
  let Q : Matrix (Fin t) (Fin n) ℂ := fun j i => M (s j) i
  refine ⟨s, P, Q, ?_, ?_⟩
  · ext i j
    have h := congr_arg (fun v : Submodule.span ℂ (Set.range (fun j : Fin t => M.row (s j))) =>
      (v : Fin n → ℂ) j) (b.sum_repr (row i))
    simpa [Matrix.mul_apply, P, Q, b, row] using h.symm
  · intro i j
    have he : row (s i) = b i := by
      apply Subtype.ext
      simp [row, b]
    simp [P, he, Finsupp.single_apply]

end Circulant
#print axioms Circulant.normalized_rank_factorization
```

### `FinitePolynomialObstruction.lean`

```lean
import PolynomialObstruction

noncomputable section
namespace Circulant
open MvPolynomial

/-- The dimension obstruction with arbitrary finite coordinate types. -/
theorem finite_polynomial_map_obstruction {I J : Type} [Finite I] [Finite J]
    (f : J → MvPolynomial I ℂ) (hab : Nat.card I < Nat.card J) :
    ∃ p : MvPolynomial J ℂ, p ≠ 0 ∧
      ∀ x : I → ℂ, eval (fun j => eval x (f j)) p = 0 := by
  classical
  let : Fintype I := Fintype.ofFinite I
  let : Fintype J := Fintype.ofFinite J
  have hdep : ¬ AlgebraicIndependent ℂ f := by
    intro hi
    have h := hi.cardinalMk_le_trdeg
    simp only [MvPolynomial.trdeg_of_isDomain, Cardinal.mk_fintype,
      Cardinal.lift_natCast] at h
    have hba : Fintype.card J ≤ Fintype.card I := by exact_mod_cast h
    simp only [Nat.card_eq_fintype_card] at hab
    omega
  rw [algebraicIndependent_iff] at hdep
  push Not at hdep
  obtain ⟨p, hp, hpne⟩ := hdep
  refine ⟨p, hpne, ?_⟩
  intro x
  have he : eval x (aeval f p) = eval (fun j => eval x (f j)) p := by
    have hh : (aeval x).comp (aeval f) = aeval (fun j => eval x (f j)) := by
      ext j
      simp
    exact congr_arg (fun g : MvPolynomial J ℂ →ₐ[ℂ] ℂ => g p) hh
  rw [hp, map_zero] at he
  exact he.symm

end Circulant
#print axioms Circulant.finite_polynomial_map_obstruction
```

### `RankCharts.lean`

```lean
import RankFactorization
import FinitePolynomialObstruction

/-! Polynomial normalized-row charts with the exact determinantal dimension. -/
noncomputable section
namespace Circulant
set_option backward.isDefEq.respectTransparency false
open Matrix MvPolynomial
open scoped BigOperators

def ChartVars {n t : ℕ} (s : Fin t ↪ Fin n) :=
  ({i : Fin n // i ∉ Set.range s} × Fin t) ⊕ (Fin t × Fin n)

instance {n t : ℕ} (s : Fin t ↪ Fin n) : Finite (ChartVars s) := by
  unfold ChartVars
  infer_instance

def chartP {n t : ℕ} (s : Fin t ↪ Fin n) (i : Fin n) (a : Fin t) :
    MvPolynomial (ChartVars s) ℂ := by
  classical
  exact if hi : i ∈ Set.range s then C (if i = s a then 1 else 0)
    else X (Sum.inl (⟨i, hi⟩,a))

def chartPolynomial {n t : ℕ} (s : Fin t ↪ Fin n) (ij : Fin n × Fin n) :
    MvPolynomial (ChartVars s) ℂ :=
  ∑ a : Fin t, chartP s ij.1 a * X (Sum.inr (a,ij.2))

def chartPoint {n t : ℕ} (s : Fin t ↪ Fin n)
    (P : Matrix (Fin n) (Fin t) ℂ) (Q : Matrix (Fin t) (Fin n) ℂ) : ChartVars s → ℂ :=
  Sum.elim (fun ia => P ia.1.val ia.2) (fun aj => Q aj.1 aj.2)

theorem chartP_eval {n t : ℕ} (s : Fin t ↪ Fin n)
    (P : Matrix (Fin n) (Fin t) ℂ) (Q : Matrix (Fin t) (Fin n) ℂ)
    (hP : ∀ a b, P (s a) b = if a = b then 1 else 0) (i : Fin n) (a : Fin t) :
    eval (chartPoint s P Q) (chartP s i a) = P i a := by
  classical
  by_cases hi : i ∈ Set.range s
  · obtain ⟨b, rfl⟩ := hi
    simp [chartP, chartPoint, hP, s.injective.eq_iff]
  · simp [chartP, hi, chartPoint]

theorem chartPolynomial_eval {n t : ℕ} (s : Fin t ↪ Fin n)
    (P : Matrix (Fin n) (Fin t) ℂ) (Q : Matrix (Fin t) (Fin n) ℂ)
    (hP : ∀ a b, P (s a) b = if a = b then 1 else 0) (ij : Fin n × Fin n) :
    eval (chartPoint s P Q) (chartPolynomial s ij) = (P * Q) ij.1 ij.2 := by
  simp only [chartPolynomial, map_sum, map_mul]
  simp only [chartP_eval s P Q hP]
  simp [chartPoint, Matrix.mul_apply]

theorem chartVars_card {n t : ℕ} (s : Fin t ↪ Fin n) :
    Nat.card (ChartVars s) = t*(2*n-t) := by
  classical
  have ht : t ≤ n := by simpa using Fintype.card_le_of_injective s s.injective
  have hs : Fintype.card {i : Fin n // i ∈ Set.range s} = t := by
    exact (Fintype.card_congr (Equiv.ofInjective s s.injective)).symm.trans
      (Fintype.card_fin t)
  have hc : Nat.card {i : Fin n // i ∉ Set.range s} = n-t := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_fin, hs]
  simp only [ChartVars, Nat.card_sum, Nat.card_prod, Nat.card_fin, hc]
  calc (n-t)*t + t*n = t*((n-t)+n) := by ring
    _ = t*(2*n-t) := by congr 1; omega

/-- Every rank-t matrix is in one of the finitely many normalized polynomial charts. -/
theorem rank_chart_coverage {n t : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (hr : M.rank = t) :
    ∃ (s : Fin t ↪ Fin n) (x : ChartVars s → ℂ),
      ∀ i j, eval x (chartPolynomial s (i,j)) = M i j := by
  obtain ⟨s, P, Q, hM, hP⟩ := normalized_rank_factorization M hr
  refine ⟨s, chartPoint s P Q, ?_⟩
  intro i j
  rw [chartPolynomial_eval s P Q hP, hM]

end Circulant
#print axioms Circulant.chartP_eval
#print axioms Circulant.chartPolynomial_eval
#print axioms Circulant.chartVars_card
#print axioms Circulant.rank_chart_coverage
```

### `LowRankPolynomial.lean`

```lean
import RankCharts

noncomputable section
namespace Circulant
set_option backward.isDefEq.respectTransparency false
open MvPolynomial
open scoped BigOperators

/-- A single nonzero polynomial excludes every projected rank-t matrix. -/
theorem rank_projection_polynomial {n t : ℕ}
    (E : Set (Fin n × Fin n))
    (hdim : t*(2*n-t) < Nat.card E) :
    ∃ q : MvPolynomial E ℂ, q ≠ 0 ∧
      ∀ M : Matrix (Fin n) (Fin n) ℂ, M.rank = t →
        eval (fun e : E => M e.val.1 e.val.2) q = 0 := by
  classical
  let : Fintype (Fin t ↪ Fin n) := Fintype.ofFinite _
  have hex (s : Fin t ↪ Fin n) : ∃ q : MvPolynomial E ℂ, q ≠ 0 ∧
      ∀ x : ChartVars s → ℂ, eval (fun e : E => eval x (chartPolynomial s e.val)) q = 0 := by
    apply finite_polynomial_map_obstruction
    rw [chartVars_card]
    exact hdim
  choose q hq hqeval using hex
  refine ⟨∏ s, q s, Finset.prod_ne_zero_iff.mpr (fun s _ => hq s), ?_⟩
  intro M hr
  obtain ⟨s, x, hx⟩ := rank_chart_coverage M hr
  rw [map_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ s)
  have he : (fun e : E => eval x (chartPolynomial s e.val)) =
      (fun e : E => M e.val.1 e.val.2) := by
    funext e
    exact hx e.val.1 e.val.2
  rw [← he]
  exact hqeval s x

/-- Product over all lower ranks, including the empty product when r=0. -/
theorem low_rank_projection_polynomial {n r : ℕ}
    (E : Set (Fin n × Fin n))
    (hdim : ∀ t < r, t*(2*n-t) < Nat.card E) :
    ∃ q : MvPolynomial E ℂ, q ≠ 0 ∧
      ∀ M : Matrix (Fin n) (Fin n) ℂ, M.rank < r →
        eval (fun e : E => M e.val.1 e.val.2) q = 0 := by
  classical
  have hex (t : Fin r) := rank_projection_polynomial E (hdim t.val t.isLt)
  choose q hq hqeval using hex
  refine ⟨∏ t, q t, Finset.prod_ne_zero_iff.mpr (fun t _ => hq t), ?_⟩
  intro M hr
  rw [map_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ (⟨M.rank, hr⟩ : Fin r))
  exact hqeval ⟨M.rank, hr⟩ M rfl

end Circulant
#print axioms Circulant.rank_projection_polynomial
#print axioms Circulant.low_rank_projection_polynomial
```

### `CirculantLower.lean`

```lean
import LowRankPolynomial
import Mathlib.Data.Nat.ModEq

noncomputable section
namespace Circulant
set_option backward.isDefEq.respectTransparency false
open MvPolynomial

theorem unknown_card {n l : ℕ} (hn : 0 < n) :
    Nat.card (Unknown n l) = n*(n-l) := by
  let f : Fin n × Fin (n-l) → Unknown n l := fun p =>
    ⟨(p.1, ⟨(p.1.val+p.2.val)%n, Nat.mod_lt _ hn⟩), ⟨p.2.val, p.2.isLt, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨i,s⟩ ⟨j,t⟩ he
      have hi : i = j := congr_arg (fun e : Unknown n l => e.val.1) he
      subst j
      apply Prod.ext
      · rfl
      · apply Fin.ext
        have he2 := congr_arg (fun e : Unknown n l => e.val.2.val) he
        have hm : Nat.ModEq n (i.val+s.val) (i.val+t.val) := he2
        have hs := Nat.ModEq.add_left_cancel' i.val hm
        change s.val % n = t.val % n at hs
        simpa only [Nat.mod_eq_of_lt (lt_of_lt_of_le s.isLt (Nat.sub_le n l)),
          Nat.mod_eq_of_lt (lt_of_lt_of_le t.isLt (Nat.sub_le n l))] using hs
    · intro e
      obtain ⟨s, hs, he⟩ := e.property
      refine ⟨(e.val.1, ⟨s, hs⟩), ?_⟩
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · apply Fin.ext
        exact he.symm
  have hc := Nat.card_congr (Equiv.ofBijective f hf)
  rw [Nat.card_prod, Nat.card_fin, Nat.card_fin] at hc
  exact hc.symm

theorem observed_card {n l : ℕ} (hn : 0 < n) (hl : l ≤ n) :
    Nat.card (Observed n l) = n*l := by
  classical
  have hu := unknown_card (l := l) hn
  have hc : Nat.card (Observed n l) = n*n - Nat.card (Unknown n l) := by
    have h := Nat.card_congr (Equiv.Set.sumCompl (Unknown n l))
    simp only [Nat.card_sum, Nat.card_prod, Nat.card_fin] at h
    change Nat.card (Unknown n l) + Nat.card (Observed n l) = n*n at h
    omega
  rw [hc, hu]
  have hs : n*(n-l) + n*l = n*n := by
    have hsub := Nat.sub_add_cancel hl
    nlinarith
  omega

theorem circulant_dimension_bound {n l t : ℕ} (hl : l ≤ n)
    (ht : t < n - Nat.sqrt (n*(n-l))) : t*(2*n-t) < n*l := by
  have htn : t ≤ n := by omega
  have hs : Nat.sqrt (n*(n-l)) < n-t := by omega
  have hsq : n*(n-l) < (n-t)*(n-t) := Nat.sqrt_lt.mp hs
  have hsub : n-l+l=n := Nat.sub_add_cancel hl
  have hnt : n-t+t=n := Nat.sub_add_cancel htn
  have htt : t ≤ 2*n := by omega
  have h2 : 2*n-t+t=2*n := Nat.sub_add_cancel htt
  nlinarith

/-- Polynomial vanishing on every actual matrix below the predicted rank. -/
theorem circulant_lower_polynomial {n l : ℕ} (hn : 0 < n) (hl : l ≤ n) :
    ∃ q : MvPolynomial (Observed n l) ℂ, q ≠ 0 ∧
      ∀ M : Matrix (Fin n) (Fin n) ℂ, M.rank < n-Nat.sqrt (n*(n-l)) →
        eval (fun e : Observed n l => M e.val.1 e.val.2) q = 0 := by
  apply low_rank_projection_polynomial
  intro t ht
  rw [observed_card hn hl]
  exact circulant_dimension_bound hl ht

end Circulant
#print axioms Circulant.unknown_card
#print axioms Circulant.observed_card
#print axioms Circulant.circulant_dimension_bound
#print axioms Circulant.circulant_lower_polynomial
```

### `CirculantConjecture.lean`

```lean
import CirculantUpper
import CirculantLower

/-! The unchanged literal MathDB 338558 endpoint, with both polynomial certificates. -/
noncomputable section
namespace Circulant

/-- Conjecture 5.6 of Bernstein–Blekherman–Sinn, in the literal complex
completion-rank definitions of CirculantStatement. -/
theorem mathdb338558 : ∀ n l : ℕ, 0 < n → l ≤ n →
    GCR (Observed n l) (n - Nat.sqrt (n*(n-l))) := by
  intro n l hn hl
  obtain ⟨p, hp, hupper⟩ := circulant_upper_polynomial l hn
  obtain ⟨q, hq, hlower⟩ := circulant_lower_polynomial hn hl
  exact gcr_of_polynomial_certificates p q hp hq hupper hlower

theorem literalConjecture_proved : LiteralConjecture := mathdb338558

end Circulant
#print axioms Circulant.mathdb338558
#print axioms Circulant.literalConjecture_proved
```

### `CirculantFinalAudit.lean`

```lean
import CirculantConjecture
import CirculantAudit

#eval Lean.versionString
#print Circulant.LiteralConjecture
#check Circulant.spectrum_principal_open_of_injective
#print axioms Circulant.spectrum_principal_open_of_injective
#check Circulant.polynomial_point_lift
#print axioms Circulant.polynomial_point_lift
#check Circulant.algebraicIndependent_open_image
#print axioms Circulant.algebraicIndependent_open_image
#check Circulant.pderiv_aeval
#print axioms Circulant.pderiv_aeval
#check Circulant.pderiv_totalDegree_lt
#print axioms Circulant.pderiv_totalDegree_lt
#check Circulant.eq_C_of_pderiv_eq_zero
#print axioms Circulant.eq_C_of_pderiv_eq_zero
#check Circulant.algebraicIndependent_of_jacobian_minor
#print axioms Circulant.algebraicIndependent_of_jacobian_minor
#check Circulant.jacobian_minor_open_image
#print axioms Circulant.jacobian_minor_open_image
#check Circulant.exists_transpose_kernel
#print axioms Circulant.exists_transpose_kernel
#check Circulant.exists_matrix_factor_of_range_le
#print axioms Circulant.exists_matrix_factor_of_range_le
#check Circulant.exists_matrix_factor_preserving_zero
#print axioms Circulant.exists_matrix_factor_preserving_zero
#check Circulant.range_le_kernel_of_mul_zero
#print axioms Circulant.range_le_kernel_of_mul_zero
#check Circulant.annihilator_tensor_factor
#print axioms Circulant.annihilator_tensor_factor
#check Circulant.tensor_annihilator_zero
#print axioms Circulant.tensor_annihilator_zero
#check Circulant.exists_nonsingular_minor
#print axioms Circulant.exists_nonsingular_minor
#check Circulant.factorPolynomial_eval
#print axioms Circulant.factorPolynomial_eval
#check Circulant.factorPolynomial_pderiv_left
#print axioms Circulant.factorPolynomial_pderiv_left
#check Circulant.factorPolynomial_pderiv_right
#print axioms Circulant.factorPolynomial_pderiv_right
#check Circulant.zeroFill_sum
#print axioms Circulant.zeroFill_sum
#check Circulant.factor_jacobian_rows_independent
#print axioms Circulant.factor_jacobian_rows_independent
#check Circulant.tensor_factor_jacobian
#print axioms Circulant.tensor_factor_jacobian
#check Circulant.tensor_upper_polynomial
#print axioms Circulant.tensor_upper_polynomial
#check Circulant.circulant_upper_polynomial
#print axioms Circulant.circulant_upper_polynomial
#check Circulant.normalized_rank_factorization
#print axioms Circulant.normalized_rank_factorization
#check Circulant.finite_polynomial_map_obstruction
#print axioms Circulant.finite_polynomial_map_obstruction
#check Circulant.chartP_eval
#print axioms Circulant.chartP_eval
#check Circulant.chartPolynomial_eval
#print axioms Circulant.chartPolynomial_eval
#check Circulant.chartVars_card
#print axioms Circulant.chartVars_card
#check Circulant.rank_chart_coverage
#print axioms Circulant.rank_chart_coverage
#check Circulant.rank_projection_polynomial
#print axioms Circulant.rank_projection_polynomial
#check Circulant.low_rank_projection_polynomial
#print axioms Circulant.low_rank_projection_polynomial
#check Circulant.unknown_card
#print axioms Circulant.unknown_card
#check Circulant.observed_card
#print axioms Circulant.observed_card
#check Circulant.circulant_dimension_bound
#print axioms Circulant.circulant_dimension_bound
#check Circulant.circulant_lower_polynomial
#print axioms Circulant.circulant_lower_polynomial
#check Circulant.mathdb338558
#print axioms Circulant.mathdb338558
#check Circulant.literalConjecture_proved
#print axioms Circulant.literalConjecture_proved
```

