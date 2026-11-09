import StructureR4
set_option linter.unusedSimpArgs false
namespace EdgePattern.TreeModelsR5
open TreeModelsR4
universe u v
variable {W : Type u} {V : Type v}

theorem edge_in_every_walk {G : SimpleGraph W} (ha : G.IsAcyclic)
    {x y : W} (hxy : G.Adj x y) (p : G.Walk x y) : s(x,y) ∈ p.edges :=
  SimpleGraph.isBridge_iff_forall_walk_mem_edges.mp
    (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp ha hxy) p

theorem cycle_exclusion {G : SimpleGraph W} (ha : G.IsAcyclic)
    {x y : W} (hxy : G.Adj x y) (p : G.Walk x y)
    (hp : s(x,y) ∉ p.edges) : False := hp (edge_in_every_walk ha hxy p)

-- An injective homomorphism with connected source into a forest reflects edges.
-- Surjectivity is unnecessary for this step.
theorem reflects_adjacency {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G →g H) (hi : Function.Injective f) (hc : G.Connected)
    (ha : H.IsAcyclic) {x y : V} (h : H.Adj (f x) (f y)) : G.Adj x y := by
  obtain ⟨p⟩ := hc.preconnected x y
  have hm := edge_in_every_walk ha h (p.map f)
  rw [SimpleGraph.Walk.edges_map] at hm
  obtain ⟨e, he, eq⟩ := List.mem_map.mp hm
  have einj : Function.Injective (Sym2.map f) := Sym2.map.injective hi
  have ee : e = s(x,y) := einj eq
  exact p.adj_of_mem_edges (ee ▸ he)

variable [Fintype W] (T : Rooted W)

theorem connected (hT : TreeFamily T 3 2) : T.graph.Connected := by
  have hr (x : W) : T.graph.Reachable x T.left := by
    rcases depth_coverage T hT x with h | h | h | h | ⟨p,hp,hq⟩ | ⟨p,hp,hq⟩
    · subst x; exact SimpleGraph.Reachable.refl _
    · subst x; exact T.root_edge.symm.reachable
    · exact h.reachable
    · exact h.reachable.trans T.root_edge.symm.reachable
    · exact hp.reachable.trans hq.reachable
    · exact (hp.reachable.trans hq.reachable).trans T.root_edge.symm.reachable
  let : Nonempty W := ⟨T.left⟩
  exact ⟨fun x y => (hr x).trans (hr y).symm⟩

theorem isTree (hT : TreeFamily T 3 2) : T.graph.IsTree :=
  ⟨connected T hT, hT.2⟩

-- Every rooted tree in question is partitioned into its roots, branches,
-- and grandchildren, independently of an ordering of W.
theorem branch_coverage (hT : TreeFamily T 3 2) (x : W) :
    x = T.left ∨ x = T.right ∨ x ∈ children T T.left T.right ∨
      x ∈ children T T.right T.left ∨
      (∃ a ∈ children T T.left T.right, x ∈ children T a T.left) ∨
      (∃ b ∈ children T T.right T.left, x ∈ children T b T.right) := by
  classical
  by_cases hl : x = T.left
  · exact Or.inl hl
  by_cases hr : x = T.right
  · exact Or.inr (Or.inl hr)
  have left_adj (h : T.graph.Adj x T.left) : x ∈ children T T.left T.right :=
    (mem_children T _ _ _).mpr ⟨h.symm, hr⟩
  have right_adj (h : T.graph.Adj x T.right) : x ∈ children T T.right T.left :=
    (mem_children T _ _ _).mpr ⟨h.symm, hl⟩
  rcases depth_coverage T hT x with h | h | h | h | ⟨p,hp,hq⟩ | ⟨p,hp,hq⟩
  · exact (hl h).elim
  · exact (hr h).elim
  · exact Or.inr (Or.inr (Or.inl (left_adj h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (right_adj h))))
  · by_cases he : p = T.right
    · exact Or.inr (Or.inr (Or.inr (Or.inl (right_adj (he ▸ hp)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨p,(mem_children T _ _ _).mpr ⟨hq.symm,he⟩,
          (mem_children T _ _ _).mpr ⟨hp.symm,hl⟩⟩))))
  · by_cases he : p = T.left
    · exact Or.inr (Or.inr (Or.inl (left_adj (he ▸ hp))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨p,(mem_children T _ _ _).mpr ⟨hq.symm,he⟩,
          (mem_children T _ _ _).mpr ⟨hp.symm,hr⟩⟩))))
end EdgePattern.TreeModelsR5

namespace EdgePattern.TreeModelsR5
open TreeModelsR4
universe u
variable {W : Type u} [Fintype W] (T : Rooted W)

-- These statements apply symmetrically to either end of the root edge.
omit [Fintype W] in
theorem grandchild_ne_other_root (ha : T.graph.IsAcyclic) {p q a z : W}
    (hpq : T.graph.Adj p q) (hpa : T.graph.Adj p a)
    (haz : T.graph.Adj a z) : z ≠ q := by
  intro hz
  subst z
  exact no_triangle T ha hpq haz.symm hpa

omit [Fintype W] in
theorem grandchild_not_sibling (ha : T.graph.IsAcyclic) {p a z b : W}
    (hpa : T.graph.Adj p a) (haz : T.graph.Adj a z)
    (hpb : T.graph.Adj p b) : z ≠ b := by
  intro hz
  subst z
  exact no_triangle T ha hpa haz hpb

omit [Fintype W] in
theorem cross_branch_ne (ha : T.graph.IsAcyclic) {p q a b : W}
    (hpq : T.graph.Adj p q) (hpa : T.graph.Adj p a)
    (hqb : T.graph.Adj q b) : a ≠ b := by
  intro he
  subst b
  exact no_triangle T ha hpq hqb hpa

omit [Fintype W] in
theorem grandchild_not_cross_branch (ha : T.graph.IsAcyclic) {p q a b z : W}
    (hpq : T.graph.Adj p q) (hpa : T.graph.Adj p a) (haq : a ≠ q)
    (hqb : T.graph.Adj q b) (hbp : b ≠ p) (haz : T.graph.Adj a z) : z ≠ b := by
  intro hz
  subst z
  have hab := cross_branch_ne T ha hpq hpa hqb
  apply cycle_exclusion ha haz (.cons hpa.symm (.cons hpq (.cons hqb .nil)))
  simp [SimpleGraph.Walk.edges_cons, Sym2.eq_iff, hpa.ne, hpq.ne, hqb.ne,
    haq, hbp, hab, hpa.ne.symm, Ne.symm haq, Ne.symm hbp, Ne.symm hab]

theorem sibling_grandchildren_disjoint (ha : T.graph.IsAcyclic) {p a b : W}
    (hab : a ≠ b) (hpa : T.graph.Adj p a) (hpb : T.graph.Adj p b) :
    Disjoint (children T a p) (children T b p) := by
  classical
  apply Finset.disjoint_left.mpr
  intro z hz hw
  obtain ⟨haz,hzp⟩ := (mem_children T _ _ _).mp hz
  obtain ⟨hbz,_⟩ := (mem_children T _ _ _).mp hw
  have he := common_neighbor_unique T ha hab hpa.symm hpb haz hbz.symm
  exact hzp he.symm

theorem cross_grandchildren_disjoint (ha : T.graph.IsAcyclic) {p q a b : W}
    (hpq : T.graph.Adj p q) (hpa : T.graph.Adj p a) (haq : a ≠ q)
    (hqb : T.graph.Adj q b) (_hbp : b ≠ p) :
    Disjoint (children T a p) (children T b q) := by
  classical
  apply Finset.disjoint_left.mpr
  intro z hz hw
  obtain ⟨haz,hzp⟩ := (mem_children T _ _ _).mp hz
  obtain ⟨hbz,hzq⟩ := (mem_children T _ _ _).mp hw
  have hab := cross_branch_ne T ha hpq hpa hqb
  have hza := haz.ne.symm
  have hzb := hbz.ne.symm
  apply cycle_exclusion ha haz (.cons hpa.symm (.cons hpq (.cons hqb (.cons hbz .nil))))
  simp [SimpleGraph.Walk.edges_cons, Sym2.eq_iff, hpa.ne, hpq.ne, hqb.ne,
    haq, _hbp, hab, hzp, hzq, hza, hzb,
    Ne.symm haq, Ne.symm _hbp, Ne.symm hab, Ne.symm hzp, Ne.symm hzq]
end EdgePattern.TreeModelsR5
