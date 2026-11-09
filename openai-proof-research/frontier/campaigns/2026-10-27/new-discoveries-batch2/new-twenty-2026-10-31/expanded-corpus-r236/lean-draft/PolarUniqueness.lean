/-
  UNCOMPILED DRAFT — MathDB 350432 (Contreras-Mendoza & Hernández-Cruz, arXiv:2104.07852, Conjecture 1).
  Written in the Claude lane expanded-corpus-r236, which may NOT run Lean. This file is a statement and
  proof PLAN: every `sorry` below is a placeholder to be discharged by the formalization worker, so this
  file is NOT a certificate. Target toolchain: Lean 4.34.1, mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.
  The ordinary proof is in ../CANDIDATE.md §3 (Lemma numbers below refer to it).
-/
import Mathlib

open SimpleGraph Finset

namespace Polar350432

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Induced P₄-freeness (cograph). -/
def IsP4Free (G : SimpleGraph V) : Prop :=
  ∀ a b c d : V, G.Adj a b → G.Adj b c → G.Adj c d →
    a ≠ c → b ≠ d → a ≠ d → ¬ G.Adj a c → ¬ G.Adj b d → G.Adj a d

/-- `S` induces a complete multipartite graph: non-adjacency is transitive on distinct vertices of `S`
(no induced `K₁ + K₂`). The empty set and edgeless sets qualify. -/
def IsCMSet (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x ≠ y → y ≠ z → x ≠ z → ¬ G.Adj x y → ¬ G.Adj y z → ¬ G.Adj x z

/-- `S` is edgeless (the `s = 1` case of a complete multipartite side). -/
def IsIndepSet (G : SimpleGraph V) (S : Finset V) : Prop := ∀ x ∈ S, ∀ y ∈ S, ¬ G.Adj x y

/-- `S` induces a cluster (no induced P₃). -/
def IsClusterSet (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, G.Adj x y → G.Adj y z → x ≠ z → G.Adj x z

/-- Number of cliques of a cluster side = number of connected components of the induced subgraph. -/
noncomputable def numCliques (G : SimpleGraph V) (S : Finset V) : ℕ :=
  Nat.card (G.induce (S : Set V)).ConnectedComponent

/-- `(∞,k)`-polar: some partition (A, Aᶜ) with A complete multipartite and Aᶜ a cluster with ≤ k cliques. -/
def IsInfPolar (k : ℕ) (G : SimpleGraph V) : Prop :=
  ∃ A : Finset V, IsCMSet G A ∧ IsClusterSet G Aᶜ ∧ numCliques G Aᶜ ≤ k

/-- `(1,k)`-polar. -/
def IsOnePolar (k : ℕ) (G : SimpleGraph V) : Prop :=
  ∃ A : Finset V, IsIndepSet G A ∧ IsClusterSet G Aᶜ ∧ numCliques G Aᶜ ≤ k

/-- Cograph minimal `(∞,k)`-polar obstruction, phrased literally over proper induced subgraphs. -/
def IsMinObs (k : ℕ) (G : SimpleGraph V) : Prop :=
  IsP4Free G ∧ ¬ IsInfPolar k G ∧
    ∀ S : Finset V, S ≠ univ → IsInfPolar k (G.induce (S : Set V))

/-- Type `(c,i)`: `c` connected components, `i` isolated vertices. -/
def HasType (G : SimpleGraph V) (c i : ℕ) : Prop :=
  Nat.card G.ConnectedComponent = c ∧ (univ.filter fun v => G.degree v = 0).card = i

/-- Literal endpoint (MathDB 350432): for `1 ≤ i ≤ c - 2 ≤ k` there is exactly one obstruction up to isomorphism. -/
theorem conjecture_350432 (k c i : ℕ) (hi : 1 ≤ i) (hic : i + 2 ≤ c) (hck : c ≤ k + 2) :
    (∃ n : ℕ, ∃ G : SimpleGraph (Fin n), IsMinObs k G ∧ HasType G c i) ∧
    (∀ (n m : ℕ) (G : SimpleGraph (Fin n)) (H : SimpleGraph (Fin m)),
        IsMinObs k G → HasType G c i → IsMinObs k H → HasType H c i → Nonempty (G ≃g H)) := by
  /- PLAN (CANDIDATE.md §3):
     * heredity: polarity passes to induced subgraphs; minimality ⇔ all one-vertex deletions polar.
     * F1–F3 (CM/cluster/join facts), F4 Seinsche (Lean Pool `IsP4Free.not_preconnected_or_compl`).
     * Lemma 1 (clusters), Lemma 2 (≤ 1 non-complete component), Lemma 3 (criterion), Lemma 4 (K₂ components),
       Lemma 5 (structure coK_a ⊕ cluster), Lemma 6 (polarity calculus), final case analysis.
     * normal form `P k c i` on `Fin`, explicit isomorphism from any obstruction to it. -/
  sorry

end Polar350432
