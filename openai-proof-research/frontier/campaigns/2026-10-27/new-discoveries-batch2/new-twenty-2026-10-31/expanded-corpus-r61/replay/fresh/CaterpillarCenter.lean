import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# A counterexample to the caterpillar maximum-centre conjecture (MathDB 366834)

Source: G. Hurlbert, *A Survey of the Holroyd–Talbot Conjecture*, arXiv:2501.16144v4,
Conjecture 39 (attributed to Zhang, Ran and Huang, Discrete Appl. Math. 344 (2024)):

> If `T` is a caterpillar, `r ≥ 1`, and `z` is a maximum `r`-center, then the neighbor of `z`
> has maximum degree.

Here `𝓘^r_v(G)` is the family of independent `r`-sets of `G` containing `v` (the star at `v`),
and `v` is a maximum `r`-center when `|𝓘^r_v(G)|` is maximum over all vertices.

We exhibit a caterpillar on 11 vertices for which, at `r = 6`, the maximum `6`-centers are
exactly two leaves, each adjacent only to a vertex of degree `3`, while the maximum degree is `4`.
This refutes the conjecture both in its universal form (every neighbour of every maximum
center has maximum degree) and in the weaker existential form (some maximum center has a
neighbour of maximum degree).
-/

open SimpleGraph Finset

namespace Caterpillar366834

section Definitions

variable {V : Type} [Fintype V] [DecidableEq V]

/-- A caterpillar is a tree containing a path such that every vertex lies on the path or is
adjacent to a vertex of the path (equivalently, deleting all leaves leaves a path). -/
def IsCaterpillar (T : SimpleGraph V) : Prop :=
  T.IsTree ∧ ∃ (u v : V) (p : T.Walk u v), p.IsPath ∧
    ∀ x : V, x ∈ p.support ∨ ∃ y ∈ p.support, T.Adj x y

/-- The size `|𝓘^r_v(G)|` of the star at `v` in the family of independent `r`-sets of `G`. -/
def starSize (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (v : V) : ℕ :=
  (univ.filter fun s : Finset V => G.IsNIndepSet r s ∧ v ∈ s).card

/-- `z` is a maximum `r`-center: its star in `𝓘^r(G)` has maximum size. -/
def IsMaxCenter (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (z : V) : Prop :=
  ∀ v : V, starSize G r v ≤ starSize G r z

end Definitions

/-- Literal (universal) reading of Conjecture 39. -/
def CaterpillarCenterConjecture : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (T : SimpleGraph V) [DecidableRel T.Adj],
    IsCaterpillar T → ∀ r : ℕ, 1 ≤ r → ∀ z : V, IsMaxCenter T r z →
      ∀ w : V, T.Adj z w → T.degree w = T.maxDegree

/-- Weaker existential reading: for every `r ≥ 1` some maximum `r`-center has a neighbour of
maximum degree. -/
def CaterpillarCenterConjectureWeak : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (T : SimpleGraph V) [DecidableRel T.Adj],
    IsCaterpillar T → ∀ r : ℕ, 1 ≤ r → ∃ z : V, IsMaxCenter T r z ∧
      ∃ w : V, T.Adj z w ∧ T.degree w = T.maxDegree

/-! ### The witness

Spine `0 - 1 - 2 - 3 - 4`; pendant leaves `5` at `0`, `6, 7` at `1`, `8` at `2`, `9, 10` at `4`. -/

/-- Edge list of the witness caterpillar. -/
def edges : List (Fin 11 × Fin 11) :=
  [(0, 1), (1, 2), (2, 3), (3, 4), (0, 5), (1, 6), (1, 7), (2, 8), (4, 9), (4, 10)]

/-- The witness caterpillar on 11 vertices. -/
def W : SimpleGraph (Fin 11) where
  Adj a b := (a, b) ∈ edges ∨ (b, a) ∈ edges
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by decide⟩

instance : DecidableRel W.Adj := fun a b =>
  inferInstanceAs (Decidable ((a, b) ∈ edges ∨ (b, a) ∈ edges))

theorem degrees :
    (List.finRange 11).map (fun v => W.degree v) = [2, 4, 3, 2, 3, 1, 1, 1, 1, 1, 1] := by
  decide +kernel

theorem degree_eq (v : Fin 11) :
    W.degree v = [2, 4, 3, 2, 3, 1, 1, 1, 1, 1, 1].getD v.val 0 := by
  revert v; decide +kernel

theorem maxDegree_W : W.maxDegree = 4 := by
  apply le_antisymm
  · exact W.maxDegree_le_of_forall_degree_le 4 (by decide +kernel)
  · have h : W.degree 1 = 4 := by decide +kernel
    exact h ▸ W.degree_le_maxDegree 1

/-! #### `W` is a tree -/

theorem card_edgeFinset_W : W.edgeFinset.card = 10 := by
  have h := W.sum_degrees_eq_twice_card_edges
  have hs : ∑ v, W.degree v = 20 := by decide +kernel
  omega

theorem reachable_zero (v : Fin 11) : W.Reachable 0 v := by
  have a01 : W.Adj 0 1 := by decide
  have a12 : W.Adj 1 2 := by decide
  have a23 : W.Adj 2 3 := by decide
  have a34 : W.Adj 3 4 := by decide
  have a05 : W.Adj 0 5 := by decide
  have a16 : W.Adj 1 6 := by decide
  have a17 : W.Adj 1 7 := by decide
  have a28 : W.Adj 2 8 := by decide
  have a49 : W.Adj 4 9 := by decide
  have a410 : W.Adj 4 10 := by decide
  have r1 := a01.reachable
  have r2 := r1.trans a12.reachable
  have r3 := r2.trans a23.reachable
  have r4 := r3.trans a34.reachable
  fin_cases v
  · exact Reachable.refl _
  · exact r1
  · exact r2
  · exact r3
  · exact r4
  · exact a05.reachable
  · exact r1.trans a16.reachable
  · exact r1.trans a17.reachable
  · exact r2.trans a28.reachable
  · exact r4.trans a49.reachable
  · exact r4.trans a410.reachable

theorem connected_W : W.Connected :=
  { preconnected := fun u v => (reachable_zero u).symm.trans (reachable_zero v)
    nonempty := ⟨0⟩ }

theorem isTree_W : W.IsTree := by
  rw [isTree_iff_connected_and_card]
  refine ⟨connected_W, ?_⟩
  rw [Nat.card_eq_fintype_card, ← edgeFinset_card, card_edgeFinset_W]
  simp

/-! #### `W` is a caterpillar -/

/-- The spine `0 - 1 - 2 - 3 - 4`. -/
def spine : W.Walk 0 4 :=
  Walk.cons (by decide : W.Adj 0 1) <| Walk.cons (by decide : W.Adj 1 2) <|
    Walk.cons (by decide : W.Adj 2 3) <| Walk.cons (by decide : W.Adj 3 4) Walk.nil

theorem spine_support : spine.support = [0, 1, 2, 3, 4] := rfl

theorem spine_isPath : spine.IsPath := by
  rw [Walk.isPath_def, spine_support]; decide

theorem isCaterpillar_W : IsCaterpillar W := by
  refine ⟨isTree_W, 0, 4, spine, spine_isPath, ?_⟩
  rw [spine_support]
  decide

/-- Bridge to the leaf-deletion definition: the non-leaf vertices of `W` are exactly the spine,
and two non-leaf vertices are adjacent exactly when they are consecutive on the spine. -/
theorem spine_eq_nonleaves :
    (∀ x : Fin 11, x ∈ spine.support ↔ 2 ≤ W.degree x) ∧
    (∀ x y : Fin 11, 2 ≤ W.degree x → 2 ≤ W.degree y → (W.Adj x y ↔ s(x, y) ∈ spine.edges)) := by
  have he : spine.edges = [s(0, 1), s(1, 2), s(2, 3), s(3, 4)] := rfl
  rw [spine_support, he]
  constructor
  · intro x; rw [degree_eq x]; revert x; decide
  · intro x y hx hy
    rw [degree_eq x] at hx; rw [degree_eq y] at hy
    revert x y; decide

/-! #### Star sizes at `r = 6` -/

theorem starSize_eq {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (r : ℕ) (v : V) :
    starSize G r v =
      ((powersetCard r univ).filter fun s : Finset V => G.IsIndepSet (s : Set V) ∧ v ∈ s).card := by
  unfold starSize
  congr 1
  ext s
  simp [isNIndepSet_iff, mem_powersetCard, and_comm, and_left_comm]

theorem starSizes_six :
    (List.finRange 11).map (fun v => starSize W 6 v) = [7, 1, 2, 12, 0, 8, 13, 13, 12, 14, 14] := by
  simp only [starSize_eq]
  decide +kernel

theorem starSize_six (v : Fin 11) :
    starSize W 6 v = [7, 1, 2, 12, 0, 8, 13, 13, 12, 14, 14].getD v.val 0 := by
  rw [starSize_eq]
  revert v
  decide +kernel

/-- At `r = 6` the maximum centers of `W` are exactly the two leaves `9` and `10`. -/
theorem isMaxCenter_six_iff (z : Fin 11) : IsMaxCenter W 6 z ↔ z = 9 ∨ z = 10 := by
  unfold IsMaxCenter
  simp only [starSize_six]
  revert z; decide

/-- Every neighbour of every maximum `6`-center of `W` has degree strictly below the maximum. -/
theorem maxCenter_neighbours_not_max (z : Fin 11) (hz : IsMaxCenter W 6 z) (w : Fin 11)
    (hw : W.Adj z w) : W.degree w < W.maxDegree := by
  rw [maxDegree_W, degree_eq w]
  rcases (isMaxCenter_six_iff z).1 hz with rfl | rfl <;> revert w <;> decide

/-! ### Main results -/

/-- The witness: a caterpillar, `r = 6`, a maximum `6`-center (`9`), and its neighbour `4` of
degree `3 < 4 = Δ`. -/
theorem witness :
    IsCaterpillar W ∧ IsMaxCenter W 6 9 ∧ W.Adj 9 4 ∧ W.degree 4 = 3 ∧ W.maxDegree = 4 :=
  ⟨isCaterpillar_W, (isMaxCenter_six_iff 9).2 (Or.inl rfl), by decide, by decide +kernel,
    maxDegree_W⟩

/-- Conjecture 39 of arXiv:2501.16144 (universal reading) is false. -/
theorem not_caterpillarCenterConjecture : ¬ CaterpillarCenterConjecture := by
  intro h
  have := h (Fin 11) W isCaterpillar_W 6 (by decide) 9
    ((isMaxCenter_six_iff 9).2 (Or.inl rfl)) 4 (by decide)
  have h4 : W.degree 4 = 3 := by decide +kernel
  rw [h4, maxDegree_W] at this
  exact absurd this (by decide)

/-- Even the weaker existential reading is false. -/
theorem not_caterpillarCenterConjectureWeak : ¬ CaterpillarCenterConjectureWeak := by
  intro h
  obtain ⟨z, hz, w, hw, hdeg⟩ := h (Fin 11) W isCaterpillar_W 6 (by decide)
  have := maxCenter_neighbours_not_max z hz w hw
  omega

end Caterpillar366834
