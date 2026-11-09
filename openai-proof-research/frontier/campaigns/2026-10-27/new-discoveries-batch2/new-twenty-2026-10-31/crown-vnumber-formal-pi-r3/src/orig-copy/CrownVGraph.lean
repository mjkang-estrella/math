import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Basic

/-!
Crown graphs: vertices, adjacency, and path-connectivity inside finite vertex sets.

Vertex type `CrownV.V n = Fin n ⊕ Fin n`; `Sum.inl i` is the X-vertex `a i`,
`Sum.inr j` the Y-vertex `b j`.  Crown edges join `a i` and `b j` iff `i ≠ j`.
-/

open Classical

namespace CrownV

/-- Vertices of the crown `C_{n,n}`. -/
abbrev V (n : ℕ) := Fin n ⊕ Fin n

/-- The X-side vertex `a i`. -/
abbrev vx {n : ℕ} (i : Fin n) : V n := Sum.inl i

/-- The Y-side vertex `b j`. -/
abbrev vy {n : ℕ} (j : Fin n) : V n := Sum.inr j

/-- Crown adjacency: `a i ~ b j` iff `i ≠ j`. -/
def cadj {n : ℕ} : V n → V n → Prop
  | Sum.inl i, Sum.inr j => i ≠ j
  | Sum.inr j, Sum.inl i => i ≠ j
  | _, _ => False

theorem cadj_symm {n : ℕ} {u v : V n} (h : cadj u v) : cadj v u := by
  cases u <;> cases v <;> simp only [cadj, ne_eq] at h ⊢ <;> tauto

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
