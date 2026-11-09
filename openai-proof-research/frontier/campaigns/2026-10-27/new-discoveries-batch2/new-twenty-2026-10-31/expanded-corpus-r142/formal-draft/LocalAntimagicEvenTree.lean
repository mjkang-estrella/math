/-
  UNCOMPILED DRAFT (r142 lane). This lane did not run Lean, lake or leanchecker; per the
  Claude lane restriction, root and a Sol worker compile. The `sorry`s mark proof obligations
  that are still TO DO. They are NOT acceptable in a final certificate.
  Target: MathDB 354228. For every even t ≥ 2 and every n, the complete full t-ary tree
  with n levels has local antimagic chromatic number (#leaves + 1).
  Ordinary proof: outputs/antimagic/proof.md. Labelling: scripts/antimagic/construct.py.
-/
import Mathlib

open Finset

namespace LocalAntimagicTree

/-- Vertices: words over `Fin t` of length at most `n`. The empty word is the root;
    the children of `w` are `w ++ [i]`. -/
abbrev TVert (t n : ℕ) := {w : List (Fin t) // w.length ≤ n}

/-- The complete full t-ary tree with n levels (every nonleaf has exactly t children,
    and all leaves have depth n). -/
def tree (t n : ℕ) : SimpleGraph (TVert t n) where
  Adj u v := (∃ i : Fin t, v.1 = u.1 ++ [i]) ∨ (∃ i : Fin t, u.1 = v.1 ++ [i])
  symm := by intro u v h; rcases h with h | h <;> [exact Or.inr h; exact Or.inl h]
  loopless := by
    intro u h
    rcases h with ⟨i, hi⟩ | ⟨i, hi⟩ <;>
      · have := congrArg List.length hi; simp at this

instance (t n : ℕ) : Fintype (TVert t n) := sorry -- TODO: finite (bounded-length lists over Fin t)
instance (t n : ℕ) : DecidableRel (tree t n).Adj := sorry -- TODO: decidable

/-- Vertex sum: the sum of the labels (shifted to 1..m) of the edges incident to v. -/
noncomputable def wsum {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (f : G.edgeSet ≃ Fin (Fintype.card G.edgeSet)) (v : V) : ℕ :=
  ∑ e ∈ (Finset.univ.filter fun e : G.edgeSet => v ∈ (e : Sym2 V)), ((f e : ℕ) + 1)

/-- Literal source definition: a bijection E → {1,…,|E|} with w(u) ≠ w(v) on every edge. -/
def IsLocalAntimagic {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (f : G.edgeSet ≃ Fin (Fintype.card G.edgeSet)) : Prop :=
  ∀ u v, G.Adj u v → wsum G f u ≠ wsum G f v

/-- χ_la: the least number of colours over all local antimagic labelings. -/
noncomputable def chiLA {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : ℕ :=
  sInf {k | ∃ f, IsLocalAntimagic G f ∧ (Finset.univ.image (wsum G f)).card = k}

/-- Leaves are degree-one vertices (source convention). -/
noncomputable def numLeaves {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : ℕ :=
  (Finset.univ.filter fun v => G.degree v = 1).card

/-! ### Construction (proof.md §2), stated on words.
    Row index `h = w.length`, position `pos w` = base-t value of w (0 ≤ pos < t^h).
    The label of the edge to a child `w` (with `w ≠ []`) is `lab t n w`, defined by cases
    following proof.md §2.1–2.4. Rows 1..n−2 take labels Z ± d with d in the shell D_h;
    leaf edges take labels from the tuples T_a given by σ. -/

def pos {t : ℕ} : List (Fin t) → ℕ
  | [] => 0
  | w => w.foldl (fun acc i => acc * t + i.val) 0

def sigma (k a : ℕ) : ℕ := if a ≤ k then 2 * a else 2 * (a - k) - 1

/-- TODO: closed-form label function (mirror of `construct.py`). -/
noncomputable def lab (t n : ℕ) (w : List (Fin t)) : ℕ := sorry

/-! ### Proof obligations (each a separate lemma in the final development)
  L1 `lab_bij`: `lab` restricted to nonempty words is a bijection onto [1, m]; it induces
     the edge equivalence `edgeEquiv : (tree t n).edgeSet ≃ Fin m`.
  L2 `wsum_formula`: for `w ∈ V_h`, wsum = lab(w) + Σ_i lab(w ++ [i]); the root has no parent term.
  L3 `row_sums` (n ≥ 3): Σ_i lab(w ++ [i]) = t·Z for |w| ≤ n−2, and lab w + Σ_i lab(w++[i]) = c for |w| = n−1.
  L4 `range`: every non-leaf colour except c lies in [N+1, m] (= the leaf labels).
  L5 `proper`: adjacent colours differ (band disjointness, plus the root and t = 2 special checks).
  L6 `lower_bound`: every local antimagic labeling uses ≥ numLeaves + 1 colours (proof.md §1).
  L7 `numLeaves_tree`: numLeaves (tree t n) = t^n for t ≥ 2, n ≥ 1.
  n = 1 and n = 2 are handled by explicit small definitions (§2.1–2.3).
-/

theorem lower_bound (t n : ℕ) (ht : 2 ≤ t) (hn : 1 ≤ n)
    (f : (tree t n).edgeSet ≃ Fin (Fintype.card (tree t n).edgeSet))
    (hf : IsLocalAntimagic (tree t n) f) :
    numLeaves (tree t n) + 1 ≤ (Finset.univ.image (wsum (tree t n) f)).card := sorry

theorem upper_bound (t n : ℕ) (ht : 2 ≤ t) (he : Even t) (hn : 1 ≤ n) :
    ∃ f, IsLocalAntimagic (tree t n) f ∧
      (Finset.univ.image (wsum (tree t n) f)).card = numLeaves (tree t n) + 1 := sorry

/-- MathDB 354228 (source Conjecture 6, even case), literal endpoint. -/
theorem mathdb_354228 (t n : ℕ) (ht : 2 ≤ t) (he : Even t) (hn : 1 ≤ n) :
    chiLA (tree t n) = numLeaves (tree t n) + 1 := by
  apply le_antisymm
  · obtain ⟨f, hf, hc⟩ := upper_bound t n ht he hn
    exact Nat.sInf_le ⟨f, hf, hc⟩
  · obtain ⟨f, hf, hc⟩ := upper_bound t n ht he hn
    apply le_csInf ⟨_, f, hf, hc⟩
    rintro k ⟨g, hg, rfl⟩
    exact lower_bound t n ht hn g hg

end LocalAntimagicTree
