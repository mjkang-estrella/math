import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Lattice.Nat

open Finset
namespace Antimagic
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

abbrev Labeling := G.edgeSet ≃ Fin (Fintype.card G.edgeSet)

def weight (f : Labeling G) (v : V) : ℕ :=
  ∑ e : G.edgeSet, if v ∈ (e.val : Sym2 V) then (f e).val + 1 else 0

def IsLocal (f : Labeling G) : Prop :=
  ∀ u v, G.Adj u v → weight G f u ≠ weight G f v

noncomputable def colorCount (f : Labeling G) : ℕ := by
  classical
  exact (univ.image (weight G f)).card

def spectrum : Set ℕ := {k | ∃ f : Labeling G, IsLocal G f ∧ colorCount G f = k}

noncomputable def chiLA : ℕ := sInf (spectrum G)

noncomputable def numLeaves : ℕ := (univ.filter fun v => G.degree v = 1).card

/-- Source standing exclusion, expressed without connected-component machinery. -/
def NoK2Component : Prop := ∀ u v, G.Adj u v → ¬ (G.degree u = 1 ∧ G.degree v = 1)

theorem least_of_bounds (k : ℕ)
    (upper : ∃ f : Labeling G, IsLocal G f ∧ colorCount G f = k)
    (lower : ∀ f : Labeling G, IsLocal G f → k ≤ colorCount G f) :
    IsLeast (spectrum G) k := by
  refine ⟨upper, ?_⟩
  rintro j ⟨f, hf, rfl⟩
  exact lower f hf

theorem chiLA_eq_of_least {k : ℕ} (h : IsLeast (spectrum G) k) : chiLA G = k := by
  exact h.csInf_eq

omit [DecidableEq V] in
/-- Finite colour-counting form of the leaf argument: distinct bounded leaf
colours and one colour above the bound force an additional colour. -/
theorem leaf_color_bound {L : Type} [Fintype L] (w : V → ℕ)
    (leaf : L → V) (bound : ℕ)
    (inj : Function.Injective (w ∘ leaf))
    (small : ∀ x, w (leaf x) ≤ bound)
    (large : ∃ v, bound < w v) :
    Fintype.card L + 1 ≤ (univ.image w).card := by
  classical
  obtain ⟨v, hv⟩ := large
  let s := univ.image (w ∘ leaf)
  have hs : s.card = Fintype.card L := card_image_of_injective _ inj
  have hn : w v ∉ s := by
    simp only [s, mem_image, mem_univ, true_and, Function.comp_apply]
    rintro ⟨x, hx⟩
    have := small x
    omega
  have hsub : insert (w v) s ⊆ univ.image w := by
    intro a ha
    rcases mem_insert.mp ha with rfl | ha
    · exact mem_image.mpr ⟨v, mem_univ _, rfl⟩
    · obtain ⟨x, _, rfl⟩ := mem_image.mp ha
      exact mem_image.mpr ⟨leaf x, mem_univ _, rfl⟩
  have := card_le_card hsub
  rw [card_insert_of_notMem hn, hs] at this
  exact this
end Antimagic
