import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Basic

/-!
Crown graphs: vertices, side markers, adjacency, and path-connectivity inside
finite vertex sets.

Vertex type `CrownV.V n = Fin n ⊕ Fin n`; `Sum.inl i` is the X-vertex `a i`,
`Sum.inr j` the Y-vertex `b j`.  Crown edges join `a i` and `b j` iff `i ≠ j`.

The index function and side test live here so that `cadj` is defined without a
two-argument pattern match; its recognizing equalities are `Iff`s proved by
`vidx`/`isX` computation.
-/

open Classical

namespace CrownV

/-- Vertices of the crown `C_{n,n}`. -/
abbrev V (n : ℕ) := Fin n ⊕ Fin n

/-- The index of a vertex, on either side. -/
def vidx : V n → Fin n
  | Sum.inl i => i
  | Sum.inr i => i

/-- Whether the vertex lies on the X side (`a i`). -/
def isX : V n → Bool
  | Sum.inl _ => true
  | Sum.inr _ => false

/-- X-side predicate. -/
def sideX (v : V n) : Prop := isX v = true

/-- Y-side predicate. -/
def sideY (v : V n) : Prop := isX v = false

/-- The X-side vertex `a i`. -/
abbrev vx {n : ℕ} (i : Fin n) : V n := Sum.inl i

/-- The Y-side vertex `b j`. -/
abbrev vy {n : ℕ} (j : Fin n) : V n := Sum.inr j

/-- Crown adjacency: opposite sides with unequal indices. -/
def cadj (u v : V n) : Prop :=
  vidx u ≠ vidx v ∧ ((sideX u ∧ sideY v) ∨ (sideY u ∧ sideX v))

theorem vidx_inl {i : Fin n} : vidx (Sum.inl i) = i := rfl

theorem vidx_inr {i : Fin n} : vidx (Sum.inr i) = i := rfl

theorem isX_inl {i : Fin n} : isX (Sum.inl i) = true := rfl

theorem isX_inr {i : Fin n} : isX (Sum.inr i) = false := rfl

theorem sideX_inl {i : Fin n} : sideX (Sum.inl i) := rfl

theorem sideY_inr {i : Fin n} : sideY (Sum.inr i) := rfl

theorem sideX_of_inl {y : V n} (h : ∃ k : Fin n, y = Sum.inl k) : sideX y := by
  obtain ⟨k, rfl⟩ := h; exact rfl

theorem sideY_of_inr {y : V n} (h : ∃ k : Fin n, y = Sum.inr k) : sideY y := by
  obtain ⟨k, rfl⟩ := h; exact rfl

theorem inl_of_sideX {y : V n} (h : sideX y) : ∃ k : Fin n, y = Sum.inl k := by
  cases y with
  | inl k => exact ⟨k, rfl⟩
  | inr k =>
    have h' : isX (Sum.inr k) = true := h
    rw [isX_inr] at h'
    exact absurd h' (by decide)

theorem inr_of_sideY {y : V n} (h : sideY y) : ∃ k : Fin n, y = Sum.inr k := by
  cases y with
  | inl k =>
    have h' : isX (Sum.inl k) = false := h
    rw [isX_inl] at h'
    exact absurd h' (by decide)
  | inr k => exact ⟨k, rfl⟩

/-- Recognizing lemma, X to Y. -/
theorem cadj_inl_inr {i j : Fin n} : cadj (Sum.inl i) (Sum.inr j) ↔ i ≠ j :=
  ⟨fun h => h.1, fun h => ⟨h, Or.inl ⟨rfl, rfl⟩⟩⟩

/-- Recognizing lemma, Y to X. -/
theorem cadj_inr_inl {i j : Fin n} : cadj (Sum.inr j) (Sum.inl i) ↔ i ≠ j :=
  ⟨fun h => Ne.symm h.1, fun h => ⟨Ne.symm h, Or.inr ⟨rfl, rfl⟩⟩⟩

theorem cadj_symm {n : ℕ} {u v : V n} (h : cadj u v) : cadj v u := by
  obtain ⟨hne, hcases⟩ := h
  refine ⟨Ne.symm hne, ?_⟩
  rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inr ⟨h2, h1⟩
  · exact Or.inl ⟨h2, h1⟩

/-- The single-edge relation inside `s`. -/
def SEdge (s : Finset (V n)) (x y : V n) : Prop := x ∈ s ∧ y ∈ s ∧ cadj x y

/-- Path-connectivity of `a`, `b` through vertices of `s`. -/
abbrev SameC (s : Finset (V n)) (a b : V n) : Prop := Relation.ReflTransGen (SEdge s) a b

theorem sEdge_symm {s : Finset (V n)} {x y : V n} (h : SEdge s x y) : SEdge s y x :=
  ⟨h.2.1, h.1, cadj_symm h.2.2⟩

theorem SameC.symm {s : Finset (V n)} {a b : V n} (h : SameC s a b) : SameC s b a := by
  induction h with
  | refl => exact .refl
  | tail h₁ h₂ ih => exact ih.head (sEdge_symm h₂)

theorem SameC.trans' {s : Finset (V n)} {a b c : V n}
    (h₁ : SameC s a b) (h₂ : SameC s b c) : SameC s a c :=
  Relation.ReflTransGen.trans h₁ h₂

theorem SameC.single {s : Finset (V n)} {x y : V n} (h : SEdge s x y) : SameC s x y :=
  .tail .refl h

/-- The connected component of `a` inside `s`. -/
noncomputable def comp (s : Finset (V n)) (a : V n) : Finset (V n) :=
  s.filter fun b => SameC s a b

/-- The family of components of `s`. -/
noncomputable def comps (s : Finset (V n)) : Finset (Finset (V n)) :=
  s.image (comp s)

/-- Number of connected components of the graph induced on `s`. -/
noncomputable abbrev ccnt (s : Finset (V n)) : ℕ := (comps s).card

theorem comp_self {s : Finset (V n)} {a : V n} (ha : a ∈ s) : a ∈ comp s a :=
  Finset.mem_filter.2 ⟨ha, (Relation.ReflTransGen.refl : SameC s a a)⟩

theorem comp_subset (s : Finset (V n)) (a : V n) : comp s a ⊆ s := Finset.filter_subset _ _

theorem comp_mem_comps {s : Finset (V n)} {a : V n} (ha : a ∈ s) : comp s a ∈ comps s :=
  Finset.mem_image.2 ⟨a, ha, rfl⟩

theorem comp_eq_of_sameC {s : Finset (V n)} {a b : V n} (hab : SameC s a b) :
    comp s b ⊆ comp s a := by
  intro x hx
  obtain ⟨hxS, hxSame⟩ := Finset.mem_filter.1 hx
  exact Finset.mem_filter.2 ⟨hxS, Relation.ReflTransGen.trans hab hxSame⟩

end CrownV
