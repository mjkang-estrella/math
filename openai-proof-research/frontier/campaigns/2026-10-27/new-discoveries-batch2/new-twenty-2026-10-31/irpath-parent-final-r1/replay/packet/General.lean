import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Lattice.Fold
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.NormNum

open Finset
set_option linter.unusedSectionVars false

namespace IR350452

section General

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Closed neighbourhood of a vertex, as a predicate on vertices. -/
def ClosedNbr (G : SimpleGraph V) (v w : V) : Prop := w = v ∨ G.Adj v w

/-- Closed neighbourhood of a vertex set. -/
def ClosedNbrSet (G : SimpleGraph V) (D : Finset V) (w : V) : Prop :=
  ∃ v ∈ D, ClosedNbr G v w

/-- `w` is a `D`-private neighbour of `v`. -/
def IsPrivateNbr (G : SimpleGraph V) (D : Finset V) (v w : V) : Prop :=
  (w = v ∨ G.Adj v w) ∧ ∀ u ∈ D, u ≠ v → ¬ (w = u ∨ G.Adj u w)

lemma privateNbr_closed (G : SimpleGraph V) (D : Finset V) (v w : V) :
    IsPrivateNbr G D v w ↔ ClosedNbr G v w ∧ ¬ ClosedNbrSet G (D.erase v) w := by
  simp only [IsPrivateNbr, ClosedNbr, ClosedNbrSet, Finset.mem_erase]
  constructor
  · rintro ⟨h, hn⟩
    exact ⟨h, fun ⟨u, ⟨hne, hu⟩, hw⟩ => hn u hu hne hw⟩
  · rintro ⟨h, hn⟩
    exact ⟨h, fun u hu hne hw => hn ⟨u, ⟨hne, hu⟩, hw⟩⟩

/-- `D` is irredundant: every vertex of `D` has a `D`-private neighbour. -/
def Irredundant (G : SimpleGraph V) (D : Finset V) : Prop :=
  ∀ v ∈ D, ∃ w, IsPrivateNbr G D v w

noncomputable def IR (G : SimpleGraph V) : ℕ := by
  classical
  exact (Finset.univ.filter (Irredundant G)).sup Finset.card

lemma ir_upper {G : SimpleGraph V} {D : Finset V} (h : Irredundant G D) :
    D.card ≤ IR G := by
  classical
  exact Finset.le_sup (f := Finset.card) (Finset.mem_filter.mpr ⟨Finset.mem_univ D, h⟩)

lemma ir_attained (G : SimpleGraph V) : ∃ D, Irredundant G D ∧ D.card = IR G := by
  classical
  have hempty : Irredundant G ∅ := by simp [Irredundant]
  have hn : (Finset.univ.filter (Irredundant G)).Nonempty :=
    ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hempty⟩⟩
  obtain ⟨D, hD, heq⟩ := Finset.exists_mem_eq_sup _ hn Finset.card
  exact ⟨D, (Finset.mem_filter.mp hD).2, heq.symm⟩

def IRSet (G : SimpleGraph V) (D : Finset V) : Prop :=
  Irredundant G D ∧ D.card = IR G

abbrev IsIRSet := @IRSet

lemma irSet_iff_max (G : SimpleGraph V) (D : Finset V) :
    IRSet G D ↔ Irredundant G D ∧ ∀ E, Irredundant G E → E.card ≤ D.card := by
  constructor
  · rintro ⟨h, hc⟩
    exact ⟨h, fun E he => hc ▸ ir_upper he⟩
  · rintro ⟨h, hm⟩
    obtain ⟨E, he, hc⟩ := ir_attained G
    exact ⟨h, le_antisymm (ir_upper h) (hc ▸ hm E he)⟩

/-- The swap relation `D ~ D'`: `D' = (D \ {u}) ∪ {v}` with `u ∈ D`, `v ∈ D'`, `uv ∈ E(G)`. -/
def Swap (G : SimpleGraph V) (A B : Finset V) : Prop :=
  ∃ u ∈ A, ∃ v ∈ B, G.Adj u v ∧ B = insert v (A.erase u)

lemma IsIRSet.card_eq {G : SimpleGraph V} {A B : Finset V}
    (hA : IsIRSet G A) (hB : IsIRSet G B) : A.card = B.card :=
  hA.2.trans hB.2.symm

/-- On sets of equal cardinality the swap relation is symmetric. -/
lemma swap_symm {G : SimpleGraph V} {A B : Finset V} (hc : A.card = B.card)
    (h : Swap G A B) : Swap G B A := by
  obtain ⟨u, hu, v, -, huv, rfl⟩ := h
  have hvA : v ∉ A.erase u := by
    intro hv'
    have h1 : (insert v (A.erase u)).card = (A.erase u).card := Finset.card_insert_of_mem hv'
    have h2 : (A.erase u).card = A.card - 1 := Finset.card_erase_of_mem hu
    have h3 : 0 < A.card := Finset.card_pos.mpr ⟨u, hu⟩
    omega
  refine ⟨v, Finset.mem_insert_self _ _, u, hu, huv.symm, ?_⟩
  rw [Finset.erase_insert hvA, Finset.insert_erase hu]

/-- The swap relation is irreflexive. -/
lemma swap_irrefl {G : SimpleGraph V} (A : Finset V) : ¬ Swap G A A := by
  rintro ⟨u, hu, v, -, huv, hA⟩
  have hne : u ≠ v := G.ne_of_adj huv
  have : u ∈ insert v (A.erase u) := hA ▸ hu
  rcases Finset.mem_insert.mp this with h | h
  · exact hne h
  · exact (Finset.notMem_erase u A) h

/-- The IR-graph `G(IR)` of `G`, with adjacency exactly the source's swap relation. -/
def IRGraph (G : SimpleGraph V) : SimpleGraph {D : Finset V // IsIRSet G D} where
  Adj A B := Swap G A.1 B.1
  symm := ⟨fun A B h => swap_symm (IsIRSet.card_eq A.2 B.2) h⟩
  loopless := ⟨fun A h => swap_irrefl A.1 h⟩

/-- Irredundance is hereditary. -/
lemma Irredundant.mono {G : SimpleGraph V} {D D' : Finset V} (h : Irredundant G D)
    (hsub : D' ⊆ D) : Irredundant G D' := by
  intro v hv
  obtain ⟨w, hw1, hw2⟩ := h v (hsub hv)
  exact ⟨w, hw1, fun u hu huv => hw2 u (hsub hu) huv⟩

end General

/-- `H` is an IR-graph: it is isomorphic to the IR-graph of some finite simple graph. -/
def IsIRGraph {W : Type} (H : SimpleGraph W) : Prop :=
  ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V),
    Nonempty (H ≃g IRGraph G)


end IR350452
