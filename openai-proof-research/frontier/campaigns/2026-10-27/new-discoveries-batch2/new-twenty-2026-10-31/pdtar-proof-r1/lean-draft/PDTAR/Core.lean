/-
DRAFT — NOT COMPILED, NOT A CERTIFICATE.  Statement skeleton of PROOF.md §2–§6 (the new part).
Works on a general finite vertex type `V` with a bipartition given by `A B : Finset V`
(disjoint, covering), which makes the A/B mirror symmetry a one-line instantiation.
-/
import PDTAR.Defs

open Finset

namespace PDTAR

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- K_{A,B} on V for a partition A ⊔ B = univ. -/
def KAB (A B : Finset V) : SimpleGraph V where
  Adj x y := (x ∈ A ∧ y ∈ B) ∨ (x ∈ B ∧ y ∈ A)
  symm := by
    intro x y h
    rcases h with h | h
    exacts [Or.inr ⟨h.2, h.1⟩, Or.inl ⟨h.2, h.1⟩]
  loopless := by sorry  -- uses Disjoint A B

/-- Lemma 0 (fort duality).  General graphs; the main finite-combinatorics engine. -/
theorem isPD_iff_forall_fort (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    IsPD G S ↔ ∀ F, IsFort G F → (F ∩ cnbhd G S).Nonempty := by
  sorry

section core
variable (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V)
  (hAB : Disjoint A B) (hcov : A ∪ B = univ)
  (hs : 3 ≤ A.card) (ht : 3 ≤ B.card)
  (hfam : ∀ S, IsPD G S ↔ IsPD (KAB A B) S)

-- Lemma 1(a): blocker form of the hypothesis
theorem fort_nbhd (F : Finset V) (hF : IsFort G F) :
    (A ⊆ cnbhd G F ∧ 2 ≤ (cnbhd G F ∩ B).card) ∨ (B ⊆ cnbhd G F ∧ 2 ≤ (cnbhd G F ∩ A).card) := by
  sorry
-- Lemma 1(b)
theorem noIsolated : ∀ v, ∃ w, G.Adj v w := by sorry
-- Lemma 2 (pair forts), A-side; B-side by symmetry (swap A B, use hcov.symm, hAB.symm)
theorem pair_fort {x y : V} (hx : x ∈ A) (hy : y ∈ A) (hxy : x ≠ y) :
    ∃ F, IsFort G F ∧ cnbhd G F = B ∪ {x, y} := by sorry
-- Lemma 3
theorem cross_nonempty {a : V} (ha : a ∈ A) : (G.neighborFinset a ∩ B).Nonempty := by sorry
-- Lemma 4
theorem no_cross_leaf {a c : V} (ha : a ∈ A) (hc : c ∈ B) : G.neighborFinset a ≠ {c} := by sorry
-- Lemma 5
theorem cross_deg_one {a : V} (ha : a ∈ A) (h1 : (G.neighborFinset a ∩ B).card = 1) :
    A.card = 3 ∧ B.card = 3 := by sorry
-- Lemma 6 (stated with 4 ≤ B.card; the 4 ≤ A.card case is the mirror instance)
theorem cross_complete (h4 : 4 ≤ B.card) (h4' : ¬ (A.card = 3 ∧ B.card = 3)) {a b : V}
    (ha : a ∈ A) (hb : b ∈ B) : G.Adj a b := by sorry
-- Lemma 7 + assembly: the Core Theorem
theorem core (hne : ¬ (A.card = 3 ∧ B.card = 3)) : G = KAB A B := by sorry
end core

/-- Theorem R (Bong–Carlson–Curtis–Haas–Hogben 2023 / survey t:main), specialised to power domination:
a TAR isomorphism between graphs without isolated vertices is induced by a vertex bijection carrying
PD sets to PD sets.  This is the heavy general part of the formalization (see LEAN-PLAN.md §3). -/
theorem tar_iso_relabel {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W) [DecidableRel H.Adj]
    (hG : NoIsolated G) (hH : NoIsolated H) (e : tar H ≃g tar G) :
    ∃ ψ : W ≃ V, ∀ S : Finset W, IsPD H S ↔ IsPD G (S.map ψ.toEmbedding) := by
  sorry

end PDTAR
