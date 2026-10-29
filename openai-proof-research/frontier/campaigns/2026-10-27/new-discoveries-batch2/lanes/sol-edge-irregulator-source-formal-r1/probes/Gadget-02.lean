import Source
import Boundary
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option warningAsError true
namespace EdgeIrregulator
abbrev Vertex (t : ℕ) := Unit ⊕ (Fin t × Fin 6)
def hub (t : ℕ) : Vertex t := Sum.inl ()
def node {t : ℕ} (i : Fin t) (v : Fin 6) : Vertex t := Sum.inr (i,v)
-- a,b,c,d,x,y are respectively 0,1,2,3,4,5.
def localAdj (u v : Fin 6) : Prop :=
  (u=0 ∧ v=1) ∨ (u=0 ∧ v=2) ∨ (u=0 ∧ v=3) ∨
  (u=1 ∧ v=2) ∨ (u=1 ∧ v=3) ∨ (u=2 ∧ v=4) ∨ (u=4 ∧ v=5) ∨
  (v=0 ∧ u=1) ∨ (v=0 ∧ u=2) ∨ (v=0 ∧ u=3) ∨
  (v=1 ∧ u=2) ∨ (v=1 ∧ u=3) ∨ (v=2 ∧ u=4) ∨ (v=4 ∧ u=5)
theorem localAdj_symm : ∀ u v, localAdj u v → localAdj v u := by
  unfold localAdj
  decide +kernel
theorem localAdj_irrefl : ∀ u, ¬localAdj u u := by
  unfold localAdj
  decide +kernel
def graphAdj {t : ℕ} : Vertex t → Vertex t → Prop
  | Sum.inl _, Sum.inl _ => False
  | Sum.inl _, Sum.inr (_,v) => v=5
  | Sum.inr (_,v), Sum.inl _ => v=5
  | Sum.inr (i,u), Sum.inr (j,v) => i=j ∧ localAdj u v
def graph (t : ℕ) : SimpleGraph (Vertex t) where
  Adj := graphAdj
  symm := by
    constructor
    intro u v h
    cases u with
    | inl a => cases v <;> simpa [graphAdj] using h
    | inr a =>
      cases v with
      | inl b => exact h
      | inr b => exact ⟨h.1.symm,localAdj_symm _ _ h.2⟩
  loopless := by
    constructor
    intro u h
    cases u with
    | inl a => exact h
    | inr a => exact localAdj_irrefl _ h.2
theorem vertex_card (t : ℕ) : Fintype.card (Vertex t) = 6*t+1 := by
  simp [Vertex, Nat.mul_comm, Nat.add_comm]
theorem node_reaches_hub {t : ℕ} (i : Fin t) (v : Fin 6) :
    (graph t).Reachable (node i v) (hub t) := by
  have hy : (graph t).Adj (node i 5) (hub t) := rfl
  have hxy : (graph t).Adj (node i 4) (node i 5) := by simp [graph, graphAdj, node, localAdj]
  have hcx : (graph t).Adj (node i 2) (node i 4) := by simp [graph, graphAdj, node, localAdj]
  have hac : (graph t).Adj (node i 0) (node i 2) := by simp [graph, graphAdj, node, localAdj]
  have hbc : (graph t).Adj (node i 1) (node i 2) := by simp [graph, graphAdj, node, localAdj]
  have hda : (graph t).Adj (node i 3) (node i 0) := by simp [graph, graphAdj, node, localAdj]
  have ry := hy.reachable
  have rx := hxy.reachable.trans ry
  have rc := hcx.reachable.trans rx
  fin_cases v
  · exact hac.reachable.trans rc
  · exact hbc.reachable.trans rc
  · exact rc
  · exact hda.reachable.trans (hac.reachable.trans rc)
  · exact rx
  · exact ry
theorem graph_connected (t : ℕ) : (graph t).Connected := by
  have rh : ∀ v, (graph t).Reachable v (hub t) := by
    intro v
    cases v with
    | inl a => cases a; exact SimpleGraph.Reachable.refl _
    | inr a => exact node_reaches_hub a.1 a.2
  exact { preconnected := fun u v => (rh u).trans (rh v).symm, nonempty := ⟨hub t⟩ }
end EdgeIrregulator
