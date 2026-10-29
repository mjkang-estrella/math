import Grid
import Potential
set_option autoImplicit false
namespace Polyomino57

/-- The frozen grid definition has exactly the restricted-path semantics used here. -/
theorem edgeConnected_iff_graphPotential (P : Finset GridPoint) :
    EdgeConnected P ↔ GraphPotential.Connected Adj P := Iff.rfl

/-- Closed transfer from literal grid connectedness; all inequalities live on D. -/
theorem potential_soundness {I : Type*} [DecidableEq I]
    {D P : Finset GridPoint} {M : Finset I} {H : I → GridPoint → Prop}
    {L : Finset I → GridPoint → ℕ}
    (c : GraphPotential.Certificate Adj D M H L)
    (hP : EdgeConnected P) (hPD : P ⊆ D) {z : GridPoint} (hz : z ∈ P)
    (hM : M.Nonempty) (hh : GraphPotential.Hits H M P) : L M z ≤ P.card :=
  GraphPotential.soundness c hP hPD hz hM hh

/-- A full-mask lower bound of twelve rules out connected hitting sets of size eleven. -/
theorem potential_excludes_eleven {I : Type*} [DecidableEq I]
    {D P : Finset GridPoint} {M : Finset I} {H : I → GridPoint → Prop}
    {L : Finset I → GridPoint → ℕ}
    (c : GraphPotential.Certificate Adj D M H L)
    (hM : M.Nonempty) (hl : ∀ z ∈ D, 12 ≤ L M z)
    (hP : EdgeConnected P) (hPD : P ⊆ D) (hh : GraphPotential.Hits H M P) :
    ¬ P.card ≤ 11 := GraphPotential.excludes_small c hM hl hP hPD hh
end Polyomino57

namespace GraphPotential
-- Singleton masks and singleton connected sets are included in the interface.
example {V I : Type*} [DecidableEq V] [DecidableEq I]
    {E : V → V → Prop} {D : Finset V} {i : I} {z : V}
    {H : I → V → Prop} {L : Finset I → V → ℕ}
    (c : Certificate E D {i} H L) (hz : z ∈ D) (hi : H i z) :
    L {i} z ≤ ({z} : Finset V).card := by
  apply rooted_bound c (Rooted.single z) (Finset.singleton_subset_iff.mpr hz)
    {i} (Finset.Subset.refl _) (Finset.singleton_nonempty _)
  intro j hj
  exact ⟨z, by simp, (Finset.mem_singleton.mp hj) ▸ hi⟩
end GraphPotential
