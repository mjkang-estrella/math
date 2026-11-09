import TreeModelsR3
namespace EdgePattern.TreeModelsR4
universe u
variable {W : Type u} [Fintype W] (T : Rooted W)

noncomputable def children (x p : W) : Finset W := by
  classical exact (Finset.univ.filter (T.graph.Adj x)).erase p

@[simp] theorem mem_children (x p y : W) :
    y ∈ children T x p ↔ T.graph.Adj x y ∧ y ≠ p := by
  classical
  simp [children, and_comm]

theorem root_degrees (hT : TreeFamily T 3 2) :
    (T.graph.neighborSet T.left).ncard = 3 ∧
    (T.graph.neighborSet T.right).ncard = 3 := by
  constructor
  · apply (hT.1.2 T.left).2
    simp [rootDistance]
  · apply (hT.1.2 T.right).2
    simp [rootDistance]

theorem children_card (x p : W) (hp : T.graph.Adj x p) :
    (children T x p).card + 1 = (T.graph.neighborSet x).ncard := by
  classical
  let s := Finset.univ.filter (T.graph.Adj x)
  have hm : p ∈ s := by simp [s, hp]
  have he : (T.graph.neighborSet x).ncard = s.card := by
    rw [← Set.ncard_coe_finset s]
    congr 1
    ext y
    simp [s]
  rw [he]
  exact Finset.card_erase_add_one hm

theorem root_children_card (hT : TreeFamily T 3 2) :
    (children T T.left T.right).card = 2 ∧
    (children T T.right T.left).card = 2 := by
  have h := root_degrees T hT
  have h1 := children_card T T.left T.right T.root_edge
  have h2 := children_card T T.right T.left T.root_edge.symm
  omega

theorem children_card_le (hT : TreeFamily T 3 2) (x p : W)
    (hp : T.graph.Adj x p) : (children T x p).card ≤ 2 := by
  have h := children_card T x p hp
  have := (hT.1.2 x).1
  omega

-- Every vertex is reached from one root by a walk of length at most two.
-- This is the exhaustive coverage fact, without assuming a chosen enumeration.
theorem depth_coverage (hT : TreeFamily T 3 2) (x : W) :
    x = T.left ∨ x = T.right ∨ T.graph.Adj x T.left ∨ T.graph.Adj x T.right ∨
    (∃ p, T.graph.Adj x p ∧ T.graph.Adj p T.left) ∨
    (∃ p, T.graph.Adj x p ∧ T.graph.Adj p T.right) := by
  have hd := hT.1.1.1 x
  change min (T.graph.edist x T.left) (T.graph.edist x T.right) ≤ 2 at hd
  have aux (r : W) (hr : T.graph.edist x r ≤ 2) :
      x = r ∨ T.graph.Adj x r ∨ ∃ p, T.graph.Adj x p ∧ T.graph.Adj p r := by
    by_cases h : T.graph.edist x r ≤ 1
    · rcases SimpleGraph.edist_le_one_iff_adj_or_eq.mp h with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
    · have he : T.graph.edist x r = 2 := by
        exact le_antisymm hr ((ENat.natCast_add_one_le_iff (m := 1)).mpr (lt_of_not_ge h))
      obtain ⟨_, _, p, hp⟩ := SimpleGraph.edist_eq_two_iff.mp he
      exact Or.inr (Or.inr ⟨p, hp.1, hp.2.symm⟩)
  rcases (min_le_iff.mp hd) with h | h
  · rcases aux T.left h with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · rcases aux T.right h with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

-- A two-edge path cannot have an additional edge joining its endpoints.
omit [Fintype W] in
theorem no_triangle (ha : T.graph.IsAcyclic) {x y z : W}
    (hxy : T.graph.Adj x y) (hyz : T.graph.Adj y z) : ¬ T.graph.Adj x z := by
  intro hxz
  let p : T.graph.Walk x z := .cons hxy (.cons hyz .nil)
  have hp : p.IsPath := by
    simp [p, SimpleGraph.Walk.cons_isPath_iff, hxy.ne, hxz.ne, hyz.ne]
  have he := ha.eq_snd_of_adj_start hp hxz p.end_mem_support
  change z = y at he
  exact hyz.ne he.symm

theorem root_children_disjoint (hT : TreeFamily T 3 2) :
    Disjoint (children T T.left T.right) (children T T.right T.left) := by
  classical
  apply Finset.disjoint_left.mpr
  intro x hx hy
  exact no_triangle T hT.2 T.root_edge (mem_children T _ _ _ |>.mp hy).1
    (mem_children T _ _ _ |>.mp hx).1

-- Acyclicity makes the parent of a two-edge path unique.
omit [Fintype W] in
theorem common_neighbor_unique (ha : T.graph.IsAcyclic) {x y a b : W}
    (hxy : x ≠ y) (hxa : T.graph.Adj x a) (hay : T.graph.Adj a y)
    (hxb : T.graph.Adj x b) (hby : T.graph.Adj b y) : a = b := by
  let p : T.graph.Walk x y := .cons hxa (.cons hay .nil)
  let q : T.graph.Walk x y := .cons hxb (.cons hby .nil)
  have hp : p.IsPath := by
    simp [p, SimpleGraph.Walk.cons_isPath_iff, hxa.ne, hxy, hay.ne]
  have hq : q.IsPath := by
    simp [q, SimpleGraph.Walk.cons_isPath_iff, hxb.ne, hxy, hby.ne]
  have he : p = q := congrArg Subtype.val ((ha.subsingleton_path x y).elim ⟨p,hp⟩ ⟨q,hq⟩)
  exact congrArg SimpleGraph.Walk.snd he
end EdgePattern.TreeModelsR4

