/-
  UNCOMPILED DRAFT (expanded-corpus-r199, Claude lane: Lean was NOT run here).
  MathDB 337062 / Newman–Miranda–Flórez–Narayan, EJGTA 8(2) (2020), Conjecture 2.1
  (arXiv:1709.04773).  Goal: the conjecture is false, witnessed by Class 4 at n = 1,
  G = C_32(1,7,9), which is not edge-betweenness-uniform:
      B'({0,1}) = 15169/615  ≠  15172/615 = B'({0,9}).
  Definitions follow the source's Definition 1.1 literally (ordered pairs of distinct vertices,
  shortest paths = walks of length `G.dist x y`).
  Root/Sol: compile under the pinned toolchain; no sorry / native_decide in the final endpoint.
-/
import Mathlib

open SimpleGraph Finset

namespace EBC337062

variable {V : Type} [Fintype V] [DecidableEq V]

/-- σ_xy: number of shortest x–y paths (walks of length dist x y; these are exactly the
shortest paths). -/
noncomputable def sigma (G : SimpleGraph V) [DecidableRel G.Adj] [G.LocallyFinite]
    (x y : V) : ℕ :=
  (G.finsetWalkLength (G.dist x y) x y).card

/-- σ_xy(e): number of shortest x–y paths containing the edge e. -/
noncomputable def sigmaEdge (G : SimpleGraph V) [DecidableRel G.Adj] [G.LocallyFinite]
    (x y : V) (e : Sym2 V) : ℕ :=
  ((G.finsetWalkLength (G.dist x y) x y).filter (fun w => e ∈ w.edges)).card

/-- Edge betweenness centrality B'_G(e) (Definition 1.1), summed over ordered pairs x ≠ y. -/
noncomputable def edgeBetweenness (G : SimpleGraph V) [DecidableRel G.Adj] [G.LocallyFinite]
    (e : Sym2 V) : ℚ :=
  ∑ x : V, ∑ y ∈ (univ.filter (fun y => y ≠ x)),
    (sigmaEdge G x y e : ℚ) / (sigma G x y : ℚ)

/-- Definition 1.2: uniform edge betweenness centrality. -/
def EdgeBetweennessUniform (G : SimpleGraph V) [DecidableRel G.Adj] [G.LocallyFinite] : Prop :=
  ∀ e ∈ G.edgeSet, ∀ e' ∈ G.edgeSet, edgeBetweenness G e = edgeBetweenness G e'

/-- Edge-transitivity: the automorphism group acts transitively on edges. -/
def EdgeTransitive (G : SimpleGraph V) : Prop :=
  ∀ e ∈ G.edgeSet, ∀ e' ∈ G.edgeSet, ∃ φ : G ≃g G, Sym2.map φ e = e'

/-- The circulant C_m(a₁,a₂,a₃) on ZMod m (Mathlib's `circulantGraph` with jump set
{a₁,a₂,a₃}; Mathlib symmetrizes jumps, matching the source's undirected circulants). -/
def circ (m a₁ a₂ a₃ : ℕ) : SimpleGraph (ZMod m) :=
  circulantGraph ({(a₁ : ZMod m), (a₂ : ZMod m), (a₃ : ZMod m)} : Set (ZMod m))

/-- The seven classes of Conjecture 2.1, as (order, jumps) for class c and n ≥ 1. -/
def classData : ℕ → ℕ → ℕ × ℕ × ℕ × ℕ
  | 3, n => (20 + 8 * (n - 1), 1, 2 * n + 2, 2 * n + 4)
  | 4, n => (32 + 8 * (n - 1), 1, 2 * n + 5, 2 * n + 7)
  | 5, n => (20 + 16 * (n - 1), 1, 4 * n, 8 * n + 1)
  | 6, n => (28 + 16 * (n - 1), 1, 4 * n + 4, 8 * n + 5)
  | 7, n => (32 + 8 * (n - 1), 1, 2 * n + 5, 4 * n + 11)
  | 8, n => (32 + 8 * (n - 1), 1, 2 * n + 7, 4 * n + 11)
  | 9, n => (49 + 14 * (n - 1), 1, 2 * n + 6, 4 * n + 9)
  | _, _ => (1, 0, 0, 0)

/-- Conjecture 2.1 (literal): every member of Classes 3–9 is edge-betweenness-uniform and not
edge-transitive.  (Instances `Fintype`, `DecidableRel`, `LocallyFinite` for `circ` are
inferred / to be supplied; m ≥ 1 in all classes.) -/
def Conjecture : Prop :=
  ∀ c ∈ ({3, 4, 5, 6, 7, 8, 9} : Finset ℕ), ∀ n ≥ 1,
    let d := classData c n
    haveI : NeZero d.1 := sorry -- DRAFT: replace by a proof that d.1 ≥ 20 for c ∈ 3..9
    EdgeBetweennessUniform (circ d.1 d.2.1 d.2.2.1 d.2.2.2) ∧
      ¬ EdgeTransitive (circ d.1 d.2.1 d.2.2.1 d.2.2.2)

/-- G = C_32(1,7,9) = Class 4, n = 1. -/
abbrev G32 : SimpleGraph (ZMod 32) := circ 32 1 7 9

/-- The key computation.  Planned proof:
  (1) `adjMatrix_pow_apply_eq_card_walk` turns walk counts into entries of A^ℓ;
  (2) the distance table d(0,y) (diameter 4) from explicit walks plus vanishing of lower powers;
  (3) splitting lemma: for a shortest x–y walk, s(uv) ∈ edges ↔ it factors through u→v or v→u,
      giving σ_xy(uv) = σ_xu σ_vy [d(x,u)+1+d(v,y)=d(x,y)] + σ_xv σ_uy [...];
  (4) evaluate the two 992-term rational sums (`decide` on ℕ numerators over the common
      denominator 615·k, or `norm_num [Finset.sum_fin_eq_sum_range]`).
  Alternatively (heavier kernel, no new lemma): `decide` directly on `finsetWalkLength`
  (≤ 41 walks per pair, walk length ≤ 4). -/
theorem bprime_01 : edgeBetweenness G32 s(0, 1) = 15169 / 615 := by
  sorry -- DRAFT

theorem bprime_09 : edgeBetweenness G32 s(0, 9) = 15172 / 615 := by
  sorry -- DRAFT

theorem not_uniform : ¬ EdgeBetweennessUniform G32 := by
  intro h
  have h01 : s((0 : ZMod 32), 1) ∈ G32.edgeSet := by sorry -- DRAFT: 1 - 0 ∈ jumps
  have h09 : s((0 : ZMod 32), 9) ∈ G32.edgeSet := by sorry -- DRAFT: 9 - 0 ∈ jumps
  have := h _ h01 _ h09
  rw [bprime_01, bprime_09] at this
  norm_num at this

/-- MathDB 337062 is refuted: Class 4 at n = 1 is not edge-betweenness-uniform. -/
theorem conjecture_false : ¬ Conjecture := by
  intro h
  have h4 := h 4 (by decide) 1 le_rfl
  -- classData 4 1 = (32, 1, 7, 9) by `rfl`/`decide`; then h4.1 contradicts `not_uniform`
  sorry -- DRAFT

end EBC337062
