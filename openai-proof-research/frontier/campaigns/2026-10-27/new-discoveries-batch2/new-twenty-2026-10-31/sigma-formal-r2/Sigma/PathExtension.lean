import Sigma.Basic

namespace Sigma365710

def OneEdgeTriple {V : Type*} (G : SimpleGraph V) (x y z : V) : Prop :=
  x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
    ((G.Adj x y ∧ ¬ G.Adj x z ∧ ¬ G.Adj y z) ∨
     (¬ G.Adj x y ∧ G.Adj x z ∧ ¬ G.Adj y z) ∨
     (¬ G.Adj x y ∧ ¬ G.Adj x z ∧ G.Adj y z))

theorem no_triangle {V : Type*} (G : SimpleGraph V) (hG : G.CliqueFree 3)
    {x y z : V} (hxy : G.Adj x y) (hxz : G.Adj x z) (hyz : G.Adj y z) : False := by
  classical
  exact hG {x, y, z} (SimpleGraph.is3Clique_triple_iff.mpr ⟨hxy, hxz, hyz⟩)

/-- The local witness step: one vertex outside an induced P4 contributes a
one-edge triple containing it and two path vertices. This does not yet count triples. -/
theorem path_extension_witness {V : Type*} (G : SimpleGraph V) (hG : G.CliqueFree 3)
    {a b c d x : V} (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d)
    (had : ¬ G.Adj a d) (hne : a ≠ d)
    (hxa : x ≠ a) (hxb : x ≠ b) (hxc : x ≠ c) (hxd : x ≠ d) :
    OneEdgeTriple G x a b ∨ OneEdgeTriple G x b c ∨
      OneEdgeTriple G x c d ∨ OneEdgeTriple G x a d := by
  have h1 : ¬ (G.Adj x a ∧ G.Adj x b) := fun h => no_triangle G hG h.1 h.2 hab
  have h2 : ¬ (G.Adj x b ∧ G.Adj x c) := fun h => no_triangle G hG h.1 h.2 hbc
  have h3 : ¬ (G.Adj x c ∧ G.Adj x d) := fun h => no_triangle G hG h.1 h.2 hcd
  have habne := hab.ne
  have hbcne := hbc.ne
  have hcdne := hcd.ne
  by_cases ha : G.Adj x a <;> by_cases hb : G.Adj x b <;>
    by_cases hc : G.Adj x c <;> by_cases hd : G.Adj x d <;>
    simp_all [OneEdgeTriple]

end Sigma365710
