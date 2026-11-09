import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Tactic

namespace AK350721
open Finset MvPolynomial

/-- Positions and values are shifted down by one from the paper. Since this
shift preserves strict order, it preserves inversions, excedances and minima. -/
def invCount {n : ℕ} (pi : Equiv.Perm (Fin n)) : ℕ :=
  (univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ pi p.2 < pi p.1).card

def excv {n : ℕ} (pi : Equiv.Perm (Fin n)) : Finset (Fin n) :=
  univ.filter fun v => pi.symm v < v

def rlmv {n : ℕ} (pi : Equiv.Perm (Fin n)) : Finset (Fin n) :=
  univ.filter fun v => ∀ j, pi.symm v < j → v < pi j

/-- `partition` includes fixed points as parts equal to one. -/
def cycleGe {n : ℕ} (k : ℕ) (pi : Equiv.Perm (Fin n)) : Prop :=
  ∀ a ∈ pi.partition.parts, k ≤ a

noncomputable def term {n : ℕ} (pi : Equiv.Perm (Fin n)) :
    MvPolynomial (Fin n ⊕ Fin n) ℤ :=
  (∏ i ∈ rlmv pi, X (Sum.inl i)) * (∏ i ∈ excv pi, X (Sum.inr i))

noncomputable def rawSum (n k : ℕ) : MvPolynomial (Fin n ⊕ Fin n) ℤ := by
  classical
  exact ∑ pi ∈ univ.filter (cycleGe k), C ((-1 : ℤ) ^ invCount pi) * term pi

noncomputable def F (n k : ℕ) : MvPolynomial (Fin n ⊕ Fin n) ℤ :=
  C ((-1 : ℤ) ^ (n - 1)) * rawSum n k

def InNat {n : ℕ} (f : MvPolynomial (Fin n ⊕ Fin n) ℤ) : Prop :=
  ∃ p : MvPolynomial (Fin n ⊕ Fin n) ℕ, map (Nat.castRingHom ℤ) p = f

def VoRConj : Prop := ∀ n k, 2 ≤ k → k ≤ n → InNat (F n k)
def MathDBConj : Prop := ∀ n k, 1 ≤ k → k ≤ n → InNat (rawSum n k)

theorem InNat.coeff_nonneg {n : ℕ} {f : MvPolynomial (Fin n ⊕ Fin n) ℤ}
    (h : InNat f) (m : (Fin n ⊕ Fin n) →₀ ℕ) : 0 ≤ f.coeff m := by
  obtain ⟨p, rfl⟩ := h
  simp only [coeff_map]
  exact Nat.cast_nonneg _

end AK350721
