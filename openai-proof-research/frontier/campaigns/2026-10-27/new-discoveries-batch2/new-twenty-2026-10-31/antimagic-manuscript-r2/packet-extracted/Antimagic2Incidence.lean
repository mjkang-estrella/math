import Antimagic2LowerBound
namespace Antimagic
open Finset

/-- The child contribution, still indexed by incoming endpoints. -/
theorem weight_split {t n : ℕ} (ht : 0 < t) (f : Labeling (tree t n))
    (v : Vertex t n) :
    weight (tree t n) f v =
      (∑ a : Nonroot t n, if v = a.val then (f (incomingEdge ht a)).val + 1 else 0) +
      ∑ a : Nonroot t n, if Child v a.val then (f (incomingEdge ht a)).val + 1 else 0 := by
  rw [weight_incoming ht, ← sum_add_distrib]
  apply sum_congr rfl
  intro a _
  have hp : v = parent ht a ↔ Child v a.val :=
    ⟨fun h => h ▸ parent_child ht a, fun h => child_parent_unique h ht⟩
  have hn : ¬ (v = a.val ∧ Child v a.val) := by
    rintro ⟨rfl, h⟩
    have := h.1
    omega
  simp only [hp]
  by_cases h₁ : v = a.val <;> by_cases h₂ : Child v a.val <;> simp_all

theorem incoming_contribution {t n : ℕ} (ht : 0 < t) (f : Labeling (tree t n))
    (v : Vertex t n) :
    (∑ a : Nonroot t n, if v = a.val then (f (incomingEdge ht a)).val + 1 else 0) =
    if hv : 0 < depth v then (f (incomingEdge ht ⟨v, hv⟩)).val + 1 else 0 := by
  split_ifs with hv
  · rw [sum_eq_single (⟨v, hv⟩ : Nonroot t n)]
    · simp only [ite_true]
    · intro b _ hb
      have he : v ≠ b.val := by intro h; exact hb (Subtype.ext h.symm)
      simp only [he, ite_false]
    · simp
  · apply sum_eq_zero
    intro a _
    have he : v ≠ a.val := by intro h; exact hv (h ▸ a.property)
    simp only [he, ite_false]

/-- The incidence identity with a child set, valid also at the root and bottom. -/
theorem weight_children {t n : ℕ} (ht : 0 < t) (f : Labeling (tree t n))
    (v : Vertex t n) :
    weight (tree t n) f v =
      (if hv : 0 < depth v then (f (incomingEdge ht ⟨v, hv⟩)).val + 1 else 0) +
      (∑ w : {w : Vertex t n // Child v w},
        ((f (incomingEdge ht ⟨w.val, by have := w.property.1; unfold depth; omega⟩)).val + 1)) := by
  rw [weight_split ht, incoming_contribution ht]
  apply congrArg (fun k : ℕ => (if hd : 0 < depth v then (f (incomingEdge ht ⟨v, hd⟩)).val + 1 else 0) + k)
  rw [← sum_filter]
  apply sum_bij (fun a ha => (⟨a.val, (mem_filter.mp ha).2⟩ : {w // Child v w}))
  · intro a ha; exact mem_univ _
  · intro a ha b hb h
    exact Subtype.ext (congrArg (fun w : {w : Vertex t n // Child v w} => w.val) h)
  · intro w _
    exact ⟨⟨w.val, by have := w.property.1; unfold depth; omega⟩,
      mem_filter.mpr ⟨mem_univ _, w.property⟩, rfl⟩
  · intro a ha; rfl

/-- Literal weights as an incoming label plus the `Fin t` child labels. -/
theorem weight_row {t n : ℕ} (ht : 0 < t) (f : Labeling (tree t n))
    (v : Vertex t n) (hv : depth v < n) :
    weight (tree t n) f v =
      (if hd : 0 < depth v then (f (incomingEdge ht ⟨v, hd⟩)).val + 1 else 0) +
      (∑ j : Fin t, ((f (incomingEdge ht ⟨childAt v hv j, by
        have := (childAt_child ht v hv j).1; unfold depth; omega⟩)).val + 1)) := by
  rw [weight_children ht, ← (childrenEquiv ht v hv).sum_comp]
  rfl

#print axioms weight_row
end Antimagic
