import Mathlib

namespace SigmaFusion

/-- A signed subset: its positive and negative coordinates are disjoint. -/
def Space (α : Type*) := {p : Set α × Set α // Disjoint p.1 p.2}

variable {α : Type*}

def positive (x : Space α) : Set α := x.val.1

def negative (x : Space α) : Set α := x.val.2

theorem no_collision (x : Space α) (a : α) : ¬ (a ∈ positive x ∧ a ∈ negative x) := by
  exact fun h => Set.disjoint_left.mp x.property h.1 h.2

theorem ext_coordinates {x y : Space α}
    (hp : positive x = positive y) (hn : negative x = negative y) : x = y := by
  apply Subtype.ext
  exact Prod.ext hp hn

def empty : Space α := ⟨(∅, ∅), by simp⟩

def inverse (x : Space α) : Space α := ⟨(negative x, positive x), x.property.symm⟩

/-- The fusion definition from source Definition 1.12, in signed coordinates. -/
def fusion (x y : Space α) : Space α :=
  ⟨((positive x \ negative y) ∪ (positive y \ negative x),
     (negative x \ positive y) ∪ (negative y \ positive x)), by
    apply Set.disjoint_left.mpr
    intro a hp hn
    have hx := no_collision x a
    have hy := no_collision y a
    simp only [Set.mem_union, Set.mem_sdiff] at hp hn
    tauto⟩

/-- The result of fusing a positive subset P with a negative subset Q. -/
def generated (P Q : Set α) : Space α :=
  ⟨(P \ Q, Q \ P), by
    apply Set.disjoint_left.mpr
    intro a hp hn
    exact hp.2 hn.1⟩

def purePositive (P : Set α) : Space α := ⟨(P, ∅), by simp⟩

def pureNegative (Q : Set α) : Space α := ⟨(∅, Q), by simp⟩

theorem generated_is_fusion (P Q : Set α) :
    generated P Q = fusion (purePositive P) (pureNegative Q) := by
  apply ext_coordinates <;>
    simp [generated, fusion, purePositive, pureNegative, positive, negative]

theorem generated_covers (x : Space α) : generated (positive x) (negative x) = x := by
  apply ext_coordinates
  · ext a
    have hx := no_collision x a
    simp only [positive, generated, Set.mem_sdiff]
    change (a ∈ positive x ∧ a ∉ negative x) ↔ a ∈ positive x
    tauto
  · ext a
    have hx := no_collision x a
    simp only [negative, generated, Set.mem_sdiff]
    change (a ∈ negative x ∧ a ∉ positive x) ↔ a ∈ negative x
    tauto

theorem generated_space_exact :
    ∀ x : Space α, ∃ P Q : Set α, fusion (purePositive P) (pureNegative Q) = x := by
  intro x
  exact ⟨positive x, negative x, (generated_is_fusion _ _).symm.trans (generated_covers x)⟩

theorem fusion_comm (x y : Space α) : fusion x y = fusion y x := by
  apply ext_coordinates <;> exact Set.union_comm _ _

theorem fusion_empty (x : Space α) : fusion x empty = x := by
  apply ext_coordinates <;> simp [fusion, positive, negative, empty]

theorem empty_fusion (x : Space α) : fusion empty x = x := by
  rw [fusion_comm, fusion_empty]

theorem identity_unique : ∃! e : Space α, ∀ x, fusion x e = x ∧ fusion e x = x := by
  refine ⟨empty, fun x => ⟨fusion_empty x, empty_fusion x⟩, ?_⟩
  intro e he
  have h := (he empty).2
  simpa only [fusion_empty] using h

theorem fusion_inverse (x : Space α) : fusion x (inverse x) = empty := by
  apply ext_coordinates <;> simp [fusion, inverse, positive, negative, empty]

theorem annihilator_eq_inverse (x y : Space α) (h : fusion x y = empty) : y = inverse x := by
  have hp : (positive x \ negative y) ∪ (positive y \ negative x) = ∅ :=
    congrArg positive h
  have hn : (negative x \ positive y) ∪ (negative y \ positive x) = ∅ :=
    congrArg negative h
  apply ext_coordinates
  · ext a
    have hpp := Set.ext_iff.mp hp a
    have hnn := Set.ext_iff.mp hn a
    simp only [Set.mem_union, Set.mem_sdiff, Set.mem_empty_iff_false] at hpp hnn
    change a ∈ positive y ↔ a ∈ negative x
    tauto
  · ext a
    have hpp := Set.ext_iff.mp hp a
    have hnn := Set.ext_iff.mp hn a
    simp only [Set.mem_union, Set.mem_sdiff, Set.mem_empty_iff_false] at hpp hnn
    change a ∈ negative y ↔ a ∈ positive x
    tauto

theorem inverse_unique (x : Space α) :
    ∃! y : Space α, fusion x y = empty ∧ fusion y x = empty := by
  refine ⟨inverse x, ⟨fusion_inverse x, ?_⟩, ?_⟩
  · rw [fusion_comm, fusion_inverse]
  · intro y hy
    exact annihilator_eq_inverse x y hy.1

/-- Exactly the four properties in source Conjecture 3.2. Closure is supplied
by the total typed operation; the first conjunct makes it explicit. -/
theorem conjecture_3_2 (α : Type*) :
    (∀ x y : Space α, ∃ z : Space α, fusion x y = z) ∧
    (∃! e : Space α, ∀ x, fusion x e = x ∧ fusion e x = x) ∧
    (∀ x : Space α, ∃! y : Space α, fusion x y = empty ∧ fusion y x = empty) ∧
    (∀ x y : Space α, fusion x y = fusion y x) := by
  exact ⟨fun x y => ⟨fusion x y, rfl⟩, identity_unique, inverse_unique, fusion_comm⟩

theorem fusion_idempotent (x : Space α) : fusion x x = x := by
  apply ext_coordinates
  · ext a
    have hx := no_collision x a
    change ((a ∈ positive x ∧ a ∉ negative x) ∨
      (a ∈ positive x ∧ a ∉ negative x)) ↔ a ∈ positive x
    tauto
  · ext a
    have hx := no_collision x a
    change ((a ∈ negative x ∧ a ∉ positive x) ∨
      (a ∈ negative x ∧ a ∉ positive x)) ↔ a ∈ negative x
    tauto

/-- Failure of division uniqueness: the four stated properties do not imply
that this is a loop in the usual quasigroup sense. -/
theorem translation_not_injective {x : Space α} (hx : x ≠ empty) :
    ¬ Function.Injective (fun y => fusion x y) := by
  intro h
  apply hx
  apply h
  change fusion x x = fusion x empty
  rw [fusion_idempotent, fusion_empty]

theorem nonassociative_at_nonempty {x : Space α} (hx : x ≠ empty) :
    fusion (fusion (inverse x) x) x ≠ fusion (inverse x) (fusion x x) := by
  rw [fusion_comm (inverse x) x, fusion_inverse, empty_fusion,
      fusion_idempotent, fusion_comm (inverse x) x, fusion_inverse]
  exact hx

end SigmaFusion
