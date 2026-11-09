import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity.Basic

namespace Sepperm362890
open Classical

/-- The literal classical avoidance class; the source excludes the empty permutation. -/
def Separable {n : ℕ} (p : Equiv.Perm (Fin n)) : Prop :=
  0 < n ∧ ∀ a b c d : Fin n, a < b → b < c → c < d →
    ¬ (p c < p a ∧ p a < p d ∧ p d < p b) ∧
    ¬ (p b < p d ∧ p d < p a ∧ p a < p c)

noncomputable def separablePermutations (n : ℕ) : Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter Separable

noncomputable def lmax {n : ℕ} (p : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter fun i => ∀ j, j < i → p j < p i).card
noncomputable def rmax {n : ℕ} (p : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter fun i => ∀ j, i < j → p j < p i).card
noncomputable def lmin {n : ℕ} (p : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter fun i => ∀ j, j < i → p i < p j).card
noncomputable def rmin {n : ℕ} (p : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter fun i => ∀ j, i < j → p i < p j).card

noncomputable def count (n k : ℕ) (stat : Equiv.Perm (Fin n) → ℕ) : ℕ :=
  ((separablePermutations n).filter fun p => stat p = k).card

def PeakTwo (a : ℕ → ℕ) : Prop :=
  (∀ k, k < 2 → a k ≤ a (k+1)) ∧ (∀ k, 2 ≤ k → a (k+1) ≤ a k)

def LiteralEndpoint : Prop := ∀ n : ℕ, 3 ≤ n →
  PeakTwo (fun k => count n k lmax) ∧ PeakTwo (fun k => count n k rmax) ∧
  PeakTwo (fun k => count n k lmin) ∧ PeakTwo (fun k => count n k rmin)

/-- The algebra underlying the adjacent Newton-kernel pairing. -/
theorem newton_pair {R : Type*} [CommRing R] (q u v w : R) :
    (1+q)*((1+q)*u-q*(1-q)*(u+v) +
      ((1+q)*v-q*(1-q)*(v+w))) =
      (1+q)^2*(u+v)-q*(1-q)*(1+q)*(u+2*v+w) := by ring

def A (m : ℚ) : ℚ :=
  1282*m^4-21003*m^3+135851*m^2-412770*m+496440
def B (m : ℚ) : ℚ :=
  -220*m^4+3933*m^3-27227*m^2+88074*m-113400

theorem A_shift (x : ℚ) : A (20+x) =
    83677440+20841670*x+1952471*x^2+81557*x^3+1282*x^4 := by unfold A; ring

theorem AB_shift (x : ℚ) : 5*A (20+x)+B (20+x) =
    405408480+100886944*x+9443108*x^2+394118*x^3+6190*x^4 := by
  unfold A B; ring

theorem A_nonnegative (m : ℚ) (hm : 20 ≤ m) : 0 ≤ A m := by
  have hx : 0 ≤ m-20 := sub_nonneg.mpr hm
  have h := A_shift (m-20)
  rw [show 20+(m-20)=m by ring] at h
  rw [h]
  repeat first | apply add_nonneg | apply mul_nonneg | exact pow_nonneg hx _ | exact hx | decide

theorem AB_nonnegative (m : ℚ) (hm : 20 ≤ m) : 0 ≤ 5*A m+B m := by
  have hx : 0 ≤ m-20 := sub_nonneg.mpr hm
  have h := AB_shift (m-20)
  rw [show 20+(m-20)=m by ring] at h
  rw [h]
  repeat first | apply add_nonneg | apply mul_nonneg | exact pow_nonneg hx _ | exact hx | decide

#print axioms newton_pair
#print axioms A_nonnegative
#print axioms AB_nonnegative
end Sepperm362890
