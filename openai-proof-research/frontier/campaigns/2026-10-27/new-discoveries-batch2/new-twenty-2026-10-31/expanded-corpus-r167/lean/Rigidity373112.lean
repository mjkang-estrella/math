/-
  UNCOMPILED DRAFT (Claude lane r167; Lean was NOT run). Explicit `sorry`s mark the proof
  obligations; this file is a statement-correspondence plan, not a certificate.
  Intended dependency: CombinatorialRigidity.CountMatroid (bryangingechen/CombinatorialRigidity
  @ 021c2284bc387efee3c3b20a18eb5f769638b578), ported to the campaign pin or replayed in its own pin.

  Target: negation of MathDB 373112 = Tyomkyn arXiv:2602.11892 Conjecture 6.1.
-/
import Mathlib
import CombinatorialRigidity.CountMatroid

open SimpleGraph

namespace R373112

variable {n : ℕ}

/-- Generic plane rigidity matroid R_n (source Definition 1.2): the (2,3)-count matroid. -/
noncomputable abbrev R (n : ℕ) : Matroid (Sym2 (Fin n)) := countMatroid (Fin n) 2 3 (by omega)

/-- edge set of the copy of K_m on the image of an embedding. -/
def copyEdges {m : ℕ} (f : Fin m ↪ Fin n) : Set (Sym2 (Fin n)) :=
  {e | ∃ a b : Fin m, a ≠ b ∧ e = s(f a, f b)}

def K33Edges (f : Fin 6 ↪ Fin n) : Set (Sym2 (Fin n)) :=
  {e | ∃ a b : Fin 6, a.val < 3 ∧ 3 ≤ b.val ∧ e = s(f a, f b)}

/-- Source Definition 1.1 (Nguyen): abstract 2-rigidity matroid on E(K_n). -/
structure IsAbstract2Rigidity (M : Matroid (Sym2 (Fin n))) : Prop where
  ground : M.E = (⊤ : SimpleGraph (Fin n)).edgeSet
  rank : M.eRank = 2 * n - 3
  k4 : ∀ f : Fin 4 ↪ Fin n, M.IsCircuit (copyEdges f)

/-- Source Definition 1.4: symmetric graph matroid. -/
def IsSymmetric (M : Matroid (Sym2 (Fin n))) : Prop :=
  ∀ σ : Equiv.Perm (Fin n), ∀ I, M.Indep I → M.Indep (Sym2.map σ '' I)

def K33Indep (M : Matroid (Sym2 (Fin n))) : Prop := ∀ f : Fin 6 ↪ Fin n, M.Indep (K33Edges f)

/-- The set of n for which the conjectured-rare object exists. -/
def Exceptional : Set ℕ :=
  {n | ∃ M : Matroid (Sym2 (Fin n)), IsAbstract2Rigidity M ∧ IsSymmetric M ∧ M ≠ R n ∧ K33Indep M}

/-! ## Combinatorial core (Lemmas A, C, D of CANDIDATE-373112.md) -/

/-- edges of `B` inside `X` -/
def eIn (B : SimpleGraph (Fin n)) [DecidableRel B.Adj] (X : Finset (Fin n)) : ℕ :=
  ((X ×ˢ X).filter (fun p => p.1 < p.2 ∧ B.Adj p.1 p.2)).card

/-- free Laman basis: Laman and no tight set with 4 ≤ |X| ≤ n-1 -/
def FreeLaman (B : SimpleGraph (Fin n)) [DecidableRel B.Adj] : Prop :=
  B.IsLaman ∧ ∀ X : Finset (Fin n), 4 ≤ X.card → X.card ≤ n - 1 → eIn B X + 4 ≤ 2 * X.card

/-- Lemma A: a free Laman basis stays a basis of R_n after any single exchange. -/
theorem exchange_indep_of_freeLaman (B : SimpleGraph (Fin n)) [DecidableRel B.Adj]
    (hB : FreeLaman B) (a b : Sym2 (Fin n)) (ha : a ∈ B.edgeSet) (hb : b ∈ (⊤ : SimpleGraph (Fin n)).edgeSet)
    (hb' : b ∉ B.edgeSet) : (R n).IsBase (insert b (B.edgeSet \ {a})) := by
  sorry -- counting argument of Lemma A (cases on whether both ends of b lie in X)

/-- Lemma C: degree-3 split with z non-adjacent to u, v preserves FreeLaman (statement on Fin (n+1)). -/
theorem split_freeLaman : True := by
  trivial -- placeholder: formal statement to be phrased via an embedding Fin n ↪ Fin (n+1)

/-- Lemma D: no two consecutive degrees ⇒ no single exchange gives an isomorphic copy. -/
theorem no_adjacent_copy : True := by
  trivial -- placeholder: degree multiset argument

/-- Base graph B₈ (graph6 GCR`vo): edges 03 05 07 14 15 17 25 26 27 36 37 46 47. -/
def B8 : SimpleGraph (Fin 8) := SimpleGraph.fromEdgeSet
  {s(0,3), s(0,5), s(0,7), s(1,4), s(1,5), s(1,7), s(2,5), s(2,6), s(2,7), s(3,6), s(3,7), s(4,6), s(4,7)}

/-! ## Matroid assembly (Lemma B) -/

/-- Main theorem: for every even n ≥ 8, n is exceptional. -/
theorem even_mem_exceptional (k : ℕ) (hk : 4 ≤ k) : 2 * k ∈ Exceptional := by
  sorry -- build B_{2k} (free, degrees in {3,5}); M := IndepMatroid.ofFinite with
        -- Indep I := (R n).Indep I ∧ I ∉ orbit(B_{2k}); augmentation as after Lemma B; then the fields.

/-- Literal negation of MathDB 373112 / Tyomkyn Conjecture 6.1. -/
theorem conjecture_6_1_false : ¬ Exceptional.Finite := by
  intro hfin
  obtain ⟨N, hN⟩ := hfin.bddAbove
  have h := even_mem_exceptional (N + 4) (by omega)
  have := hN h
  omega

end R373112
