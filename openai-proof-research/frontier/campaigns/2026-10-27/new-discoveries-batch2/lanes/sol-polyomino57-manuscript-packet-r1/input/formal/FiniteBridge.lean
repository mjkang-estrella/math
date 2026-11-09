import CanonicalCoverage
import Bridge
import Mathlib.Data.Finset.Powerset
set_option autoImplicit false
namespace Polyomino57.Diagonal.FiniteProof
open Polyomino57

noncomputable def liftPotential {V I : Type*} (p : V → GridPoint)
    (L : Finset I → V → ℕ) (A : Finset I) (z : GridPoint) : ℕ := by
  classical
  exact if h : ∃ i, p i = z then L A (Classical.choose h) else 0

theorem lift_at {V I : Type*} (p : V → GridPoint) (hinj : Function.Injective p)
    (L : Finset I → V → ℕ) (A : Finset I) (i : V) :
    liftPotential p L A (p i) = L A i := by
  unfold liftPotential
  rw [dite_eq_left ⟨i,rfl⟩]
  congr 1
  exact hinj (Classical.choose_spec (show ∃ j, p j = p i from ⟨i,rfl⟩))

theorem lift_certificate {V I : Type*} [DecidableEq V] [DecidableEq I]
    (p : V → GridPoint) (hinj : Function.Injective p)
    (D : Finset V) (M : Finset I) (g : I → Finset GridPoint)
    (L : Finset I → V → ℕ)
    (c : GraphPotential.Certificate (fun i j => Adj (p i) (p j)) D M
      (fun i j => p j ∈ g i) L) :
    GraphPotential.Certificate Adj (D.image p) M (fun i z => z ∈ g i)
      (liftPotential p L) := by
  constructor
  · intro A hA hAM z hz hhit
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
    rw [lift_at p hinj]
    exact c.base A hA hAM i hi hhit
  · intro A hA hAM z hz w hw hadj
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hw
    rw [lift_at p hinj, lift_at p hinj]
    exact c.edge A hA hAM i hi j hj hadj
  · intro A B hA hB hAM hBM hd z hz
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
    rw [lift_at p hinj, lift_at p hinj, lift_at p hinj]
    exact c.merge A B hA hB hAM hBM hd i hi

/-- A finite certificate closes a literal original-group assertion. -/
theorem excludes {V I : Type*} [DecidableEq V] [DecidableEq I]
    (a b e : ℤ) (p : V → GridPoint) (hinj : Function.Injective p)
    (D : Finset V) (M : Finset I) (g : I → Finset GridPoint)
    (L : Finset I → V → ℕ)
    (hdom : domain a b e = D.image p)
    (hgroups : ∀ i ∈ M, g i ∈ groups a b e)
    (c : GraphPotential.Certificate (fun i j => Adj (p i) (p j)) D M
      (fun i j => p j ∈ g i) L)
    (hne : M.Nonempty) (hfull : ∀ i ∈ D, 12 ≤ L M i) :
    ∀ Q : Finset GridPoint, Q ⊆ domain a b e → EdgeConnected Q → Q.card = 11 →
      ¬ HitsAll Q (groups a b e) := by
  intro Q hQ hc hn hh
  have cert := lift_certificate p hinj D M g L c
  have hlow : ∀ z ∈ D.image p, 12 ≤ liftPotential p L M z := by
    intro z hz
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
    rw [lift_at p hinj]
    exact hfull i hi
  have hit : GraphPotential.Hits (fun i z => z ∈ g i) M Q := by
    intro i hi
    exact hh (g i) (hgroups i hi)
  have bad := potential_excludes_eleven cert hne hlow hc (hdom ▸ hQ) hit
  exact bad (by omega)

/-- All subset quantification is bounded by a powerset, enabling kernel checking. -/
theorem checked_certificate {V I : Type*} [DecidableEq V] [DecidableEq I]
    (E : V → V → Prop) (D : Finset V) (M : Finset I)
    (H : I → V → Prop) (L : Finset I → V → ℕ)
    (hb : ∀ A ∈ M.powerset, A.Nonempty → ∀ z ∈ D,
      (∀ i ∈ A, H i z) → L A z ≤ 1)
    (he : ∀ A ∈ M.powerset, A.Nonempty → ∀ z ∈ D, ∀ w ∈ D,
      E z w → L A z ≤ L A w + 1)
    (hm : ∀ A ∈ M.powerset, ∀ B ∈ M.powerset, A.Nonempty → B.Nonempty →
      Disjoint A B → ∀ z ∈ D, L (A ∪ B) z + 1 ≤ L A z + L B z) :
    GraphPotential.Certificate E D M H L := by
  constructor
  · intro A hs ha; exact hb A (Finset.mem_powerset.mpr hs) ha
  · intro A hs ha; exact he A (Finset.mem_powerset.mpr hs) ha
  · intro A B hs ht ha hb'; exact hm A (Finset.mem_powerset.mpr hs)
      B (Finset.mem_powerset.mpr ht) ha hb'
end Polyomino57.Diagonal.FiniteProof
