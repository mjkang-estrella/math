/-
  DRAFT — UNCOMPILED — NOT A CERTIFICATE.
  Written in the Claude lane expanded-corpus-r175. That lane may not run Lean, lake or leanchecker.
  The `sorry`s below are explicit proof obligations for the root/Sol formalization stage.
  This file must not be counted as a proof.

  Target: MathDB 362785 = Conjecture con:path of Goedgebeur–Jooken–Okrasa–Rzążewski–Schaudt,
  arXiv:2404.11704v2: for odd q ≥ 3 and every p ≥ 1, G_{q,p} is P_{3q-2}-free.
  The ordinary proof is in ../CANDIDATE-362785.md (Steps 0–2, Lemmas A–C and the case analysis).
-/
import Mathlib

open SimpleGraph

namespace InducedPathGqp

/-- Number of vertices of `G_{q,p}`. -/
def nV (q p : ℕ) : ℕ := q * p - 2

/-- Connection set of the circulant: `±1` and `q*k - 1` for `1 ≤ k ≤ p - 1`. The printed
neighbourhood `N(i) = {i-1, i+1} ∪ {i + qk - 1}` is already symmetric, because
`(qk-1) + (q(p-k)-1) = qp - 2`. -/
def conn (q p : ℕ) (d : ZMod (nV q p)) : Prop :=
  d = 1 ∨ d = -1 ∨ ∃ k ∈ Finset.Icc 1 (p - 1), d = ((q * k - 1 : ℕ) : ZMod (nV q p))

/-- The graph `G_{q,p}` of arXiv:2404.11704, Section 6.1, on vertex set `ZMod (q*p-2)`. -/
def Gqp (q p : ℕ) : SimpleGraph (ZMod (nV q p)) where
  Adj i j := i ≠ j ∧ (conn q p (j - i) ∨ conn q p (i - j))
  symm := by
    intro i j h
    exact ⟨h.1.symm, h.2.symm⟩
  loopless := by
    intro i h
    exact h.1 rfl

/-- `G` is `P_t`-free: there is no induced copy of the path on `t` vertices.
Mathlib's `↪g` (`SimpleGraph.Embedding`) is an induced embedding, preserving adjacency in both directions. -/
def PFree {V : Type*} (G : SimpleGraph V) (t : ℕ) : Prop :=
  IsEmpty (pathGraph t ↪g G)

/-- Literal MathDB 362785 statement (Conjecture con:path). -/
theorem induced_path_conjecture (q p : ℕ) (hq : Odd q) (hq3 : 3 ≤ q) (hp : 1 ≤ p) :
    PFree (Gqp q p) (3 * q - 2) := by
  sorry -- assembled from the lemmas below

/-! ## Proof skeleton (statements only; obligations for the formalization stage) -/

/-- Step 1 (linear model): for `0 ≤ i < j ≤ n-2`, the vertices `i` and `j` are adjacent iff
`j - i = 1` or `j - i ≡ -1 (mod q)`. Requires `p ≥ 4`, so that `n > 3q - 2`. -/
lemma adj_linear (q p : ℕ) (hq3 : 3 ≤ q) (hp : 4 ≤ p) (i j : ℕ) (hij : i < j) (hj : j ≤ nV q p - 2) :
    (Gqp q p).Adj (i : ZMod (nV q p)) (j : ZMod (nV q p)) ↔ (j - i = 1 ∨ (j - i) % q = q - 1) := by
  sorry

/-- Linear-model adjacency on naturals (Step 1). -/
def linAdj (q a b : ℕ) : Prop :=
  (a < b ∧ (b - a = 1 ∨ (b - a) % q = q - 1)) ∨ (b < a ∧ (a - b = 1 ∨ (a - b) % q = q - 1))

/-- (★), Step 2(b): if `ρ u = ρ w + 1` (mod `q`) and `u, w` are non-adjacent in the linear model, then `w < u`. -/
lemma star (q : ℕ) (hq3 : 3 ≤ q) (u w : ℕ) (hres : u % q = (w + 1) % q) (hna : ¬ linAdj q u w) :
    w < u := by
  sorry -- u < w would give (w - u) % q = q - 1, i.e. adjacency

/-- Lemma A: in the linear model, no independent set meets all residue classes mod `q`. -/
lemma no_independent_transversal (q : ℕ) (hq3 : 3 ≤ q) (v : ZMod q → ℕ)
    (hres : ∀ s : ZMod q, ((v s : ℕ) : ZMod q) = s)
    (hind : ∀ s : ZMod q, ¬ linAdj q (v (s + 1)) (v s)) : False := by
  sorry -- by `star`, v s < v (s+1) for all s; iterate q times around the cycle

/-- Lemma B and Lemma C and the case analysis, phrased on the residue walk `r : Fin L → ZMod q` of an
induced path. `classOf i = {r (i-1), r i}`. The final combinatorial statement: every ±1 walk of
length `3q-2` satisfying Lemma B has an independent transversal. -/
lemma walk_has_transversal (q : ℕ) (hq : Odd q) (hq3 : 3 ≤ q) (r : Fin (3 * q - 2) → ZMod q)
    (hstep : ∀ i : Fin (3 * q - 2), ∀ h : i.val + 1 < 3 * q - 2,
      r ⟨i.val + 1, h⟩ - r i = 1 ∨ r ⟨i.val + 1, h⟩ - r i = -1)
    (hB : ∀ i j : ℕ, ∀ (hi : 1 ≤ i) (hij : i + 3 ≤ j) (hj : j < 3 * q - 2),
      ({r ⟨i - 1, by omega⟩, r ⟨i, by omega⟩} : Finset (ZMod q)) ≠
      {r ⟨j - 1, by omega⟩, r ⟨j, by omega⟩}) :
    ∃ c : ZMod q → Fin (3 * q - 2), (∀ s, r (c s) = s) ∧
      ∀ s t, s ≠ t → (c s).val + 1 ≠ (c t).val := by
  sorry -- runs (Lemma C), deficit cases t ≤ q-1, (I.a), (I.b), (II.a), (II.b)

end InducedPathGqp
