import CrownVCut
import CrownVClass

/-!
Full-side ideal equalities for the crown binomial edge ideal
 lane crown-fullside-ideal-formal-pi-r13.

Both full-side cuts have side-pure complements, and the crown graph has no
edge between two vertices of the same side (`CrownVGraph.cadj` demands
opposite `isX` tags).  Hence every path inside `Finset.univ \ Xside n`
(resp. `Finset.univ \ Yside n`) is trivial, so each completed-component
minor of the original `CrownVAlg.Pc` has equal endpoints, and `minor v v = 0`
by the defining subtraction.  Consequently, for every `n : ℕ` and every
`CommRing K`, as ideal equalities in `MvPolynomial (V n × Bool) K`:

* `Pc (Xside n) = Ideal.span (coordGens (Xside n))`,
* `Pc (Yside n) = Ideal.span (coordGens (Yside n))`.

The `Pc` definition of `CrownVAlg` is used unchanged; both ideal inclusions
are proved (coordinates into the small span; minors via component triviality
and the zero self-minor).
-/

namespace CrownV

/-- No crown edge lies inside `Finset.univ \ Xside n`: an edge inside the
complement would join two `Y`-side vertices, but `cadj` needs opposite `isX`
tags. -/
theorem not_sEdge_univDiffX {n : ℕ} {u z : V n}
    (hS : SEdge (Finset.univ \ Xside n) u z) : False := by
  obtain ⟨huS, hzS, hcadj⟩ := hS
  obtain ⟨_, hor⟩ := hcadj
  rcases hor with ⟨e1, _⟩ | ⟨_, e2⟩
  · have h1 : isX u = true := e1
    exact absurd (mem_Xside.2 h1) (Finset.mem_sdiff.1 huS).2
  · have h2 : isX z = true := e2
    exact absurd (mem_Xside.2 h2) (Finset.mem_sdiff.1 hzS).2

/-- No crown edge lies inside `Finset.univ \ Yside n`: same-side tags. -/
theorem not_sEdge_univDiffY {n : ℕ} {u z : V n}
    (hS : SEdge (Finset.univ \ Yside n) u z) : False := by
  obtain ⟨huS, hzS, hcadj⟩ := hS
  obtain ⟨_, hor⟩ := hcadj
  rcases hor with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · have h1 : isX z = false := e2
    exact absurd (mem_Yside.2 h1) (Finset.mem_sdiff.1 hzS).2
  · have h2 : isX u = false := e1
    exact absurd (mem_Yside.2 h2) (Finset.mem_sdiff.1 huS).2

/-- Full-`X` cut: the source prime of the all-`X` family is spanned by the
coordinate variables of `Xside n` alone; every completed-component minor has
equal endpoints, hence is the zero self-minor. -/
theorem pcXside_eq_span (n : ℕ) (K : Type*) [CommRing K] :
    Pc (n := n) (K := K) (Xside n) =
      Ideal.span (coordGens (n := n) (K := K) (Xside n)) := by
  refine le_antisymm ?_ (Ideal.span_mono
    fun _ hx => Set.mem_union_left (compMinors (n := n) (K := K) (Xside n)) hx)
  refine Ideal.span_le.2 ?_
  rintro p (⟨v, hv, hpx⟩ | ⟨u, w, hu, hw, hconn, hpx⟩)
  · rcases hpx with h | h <;> subst h
    · exact Submodule.mem_span_of_mem ⟨v, hv, Or.inl rfl⟩
    · exact Submodule.mem_span_of_mem ⟨v, hv, Or.inr rfl⟩
  · have hno : ∀ z : V n, ¬ SEdge (Finset.univ \ Xside n) u z := fun _ hS =>
      not_sEdge_univDiffX hS
    have huv : u = w := sameC_eq_of_forall_not_sEdge hno hconn
    have hzero : (minor u u : PolyRing n K) = 0 := by
      show xx u * yy u - xx u * yy u = 0
      exact sub_self _
    rw [hpx, ← huv, hzero]
    exact Submodule.zero_mem _

/-- Full-`Y` cut: mirrored equality. -/
theorem pcYside_eq_span (n : ℕ) (K : Type*) [CommRing K] :
    Pc (n := n) (K := K) (Yside n) =
      Ideal.span (coordGens (n := n) (K := K) (Yside n)) := by
  refine le_antisymm ?_ (Ideal.span_mono
    fun _ hx => Set.mem_union_left (compMinors (n := n) (K := K) (Yside n)) hx)
  refine Ideal.span_le.2 ?_
  rintro p (⟨v, hv, hpx⟩ | ⟨u, w, hu, hw, hconn, hpx⟩)
  · rcases hpx with h | h <;> subst h
    · exact Submodule.mem_span_of_mem ⟨v, hv, Or.inl rfl⟩
    · exact Submodule.mem_span_of_mem ⟨v, hv, Or.inr rfl⟩
  · have hno : ∀ z : V n, ¬ SEdge (Finset.univ \ Yside n) u z := fun _ hS =>
      not_sEdge_univDiffY hS
    have huv : u = w := sameC_eq_of_forall_not_sEdge hno hconn
    have hzero : (minor u u : PolyRing n K) = 0 := by
      show xx u * yy u - xx u * yy u = 0
      exact sub_self _
    rw [hpx, ← huv, hzero]
    exact Submodule.zero_mem _

end CrownV
