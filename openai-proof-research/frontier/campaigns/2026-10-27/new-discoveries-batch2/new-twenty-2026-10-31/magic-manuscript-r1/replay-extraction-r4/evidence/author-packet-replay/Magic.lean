import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fin.VecNotation
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
namespace Magic381805
abbrev V := Fin 11
def edges : Finset (Sym2 V) :=
 {s(0,1),s(1,2),s(2,3),s(3,4),s(4,5),s(5,6),s(6,0),s(6,7),s(6,8),s(6,9),s(6,10)}
def G : SimpleGraph V := SimpleGraph.fromEdgeSet (↑edges)
instance : DecidableRel G.Adj := by unfold G; infer_instance
def vertexLabel : V → ℕ := ![3,2,4,5,8,6,1,7,9,10,11]
def endpointSum : Sym2 V → ℕ := Sym2.lift ⟨fun u v => vertexLabel u + vertexLabel v, fun _ _ => Nat.add_comm _ _⟩
def edgeLabel (e : Sym2 V) : ℕ := 26 - endpointSum e
def rawLabel : V ⊕ G.edgeSet → ℕ := Sum.elim vertexLabel (fun e => edgeLabel e.val)
instance : Fintype G.edgeSet := inferInstanceAs (Fintype {e : Sym2 V // e ∈ G.edgeSet})
theorem raw_bounds : ∀ x, 1 ≤ rawLabel x ∧ rawLabel x ≤ 22 := by decide
def labeling (x : V ⊕ G.edgeSet) : Fin 22 := ⟨rawLabel x - 1, by have h := raw_bounds x; omega⟩
theorem labeling_bijective : Function.Bijective labeling := by decide
noncomputable def labelEquiv : (V ⊕ G.edgeSet) ≃ Fin 22 := Equiv.ofBijective labeling labeling_bijective
/-- The literal bijection on vertices and unordered edges, with vertex labels 1..p. -/
def IsSuperEdgeMagic {W : Type} (H : SimpleGraph W) (p q c : ℕ)
    (f : (W ⊕ H.edgeSet) ≃ Fin (p+q)) : Prop :=
 (∀ v, (f (.inl v)).val < p) ∧
 (∀ j : Fin p, ∃ v, (f (.inl v)).val = j.val) ∧
 ∀ u v (h : H.Adj u v),
   (f (.inl u)).val + 1 + ((f (.inl v)).val + 1) +
     ((f (.inr ⟨s(u,v),h⟩)).val + 1) = c

theorem certificate : IsSuperEdgeMagic G 11 11 26 labelEquiv := by unfold IsSuperEdgeMagic; decide
/-- Exact source family: the displayed seven-cycle with four leaves at its last vertex. -/
def cycleVertex (i : Fin 7) : V := ⟨i.val, by omega⟩
theorem family_edges : ∀ u v : V, G.Adj u v ↔
 (∃ i : Fin 7, (u = cycleVertex i ∧ v = cycleVertex ⟨(i.val+1)%7, Nat.mod_lt _ (by decide)⟩) ∨
   (v = cycleVertex i ∧ u = cycleVertex ⟨(i.val+1)%7, Nat.mod_lt _ (by decide)⟩)) ∨
 (u = 6 ∧ 7 ≤ v.val) ∨ (v = 6 ∧ 7 ≤ u.val) := by decide

theorem vertex_count : Fintype.card V = 11 := by decide
theorem edge_count : Fintype.card G.edgeSet = 11 := by decide
/-- Minimized over all source super edge-magic total labelings. -/
noncomputable def strength {W : Type} (H : SimpleGraph W) (p q : ℕ) : ℕ :=
 sInf {c | ∃ f : (W ⊕ H.edgeSet) ≃ Fin (p+q), IsSuperEdgeMagic H p q c f}
theorem strength_le : strength G 11 11 ≤ 26 := by
 apply Nat.sInf_le
 exact ⟨labelEquiv, certificate⟩
theorem wrong_predicted_value : strength G 11 11 ≠ 2 * 11 + (7+3)/2 := by
 have := strength_le
 norm_num at *
 omega
end Magic381805
namespace Magic381805
/-- Cycle vertices are listed cyclically. All other vertices are leaves, with precisely
`k i` leaves at the i-th cycle vertex; these clauses also exclude chords and leaf-leaf edges. -/
def IsFamily {N : ℕ} (H : SimpleGraph (Fin N)) (n : ℕ) (k : Fin n → ℕ) : Prop :=
 ∃ a : Fin n → Fin N, Function.Injective a ∧
 (∀ i j, H.Adj (a i) (a j) ↔
     ((i.val+1)%n = j.val ∨ (j.val+1)%n = i.val)) ∧
 (∀ v, (¬∃ i, a i = v) → ∃ i, ∀ w, H.Adj v w ↔ w = a i) ∧
 (∀ i, Nat.card {v : Fin N // (¬∃ j, a j = v) ∧ H.Adj (a i) v} = k i)
def leafCounts : Fin 7 → ℕ := ![0,0,0,0,0,0,4]
theorem family : IsFamily G 7 leafCounts := by
 refine ⟨cycleVertex, ?_, ?_, ?_, ?_⟩
 · decide
 · decide
 · decide
 · intro i
   rw [Nat.card_eq_fintype_card]
   revert i
   decide
/-- Literal universal strength assertion for odd cycles with arbitrarily many leaves
at each cycle vertex, restricted to graphs admitting the source labelings. -/
def SourceConjecture : Prop := ∀ (N n : ℕ) (k : Fin n → ℕ)
 (H : SimpleGraph (Fin N)) [DecidableRel H.Adj],
 3 ≤ n → Odd n → IsFamily H n k →
 (∃ (c : ℕ) (f : (Fin N ⊕ H.edgeSet) ≃ Fin (N + Fintype.card H.edgeSet)),
    IsSuperEdgeMagic H N (Fintype.card H.edgeSet) c f) →
 strength H N (Fintype.card H.edgeSet) = 2 * Fintype.card H.edgeSet + (n+3)/2

theorem source_refutation : ¬SourceConjecture := by
 intro h
 have hodd : Odd 7 := by decide
 have hex : ∃ (c : ℕ) (f : (V ⊕ G.edgeSet) ≃ Fin (11 + Fintype.card G.edgeSet)),
    IsSuperEdgeMagic G 11 (Fintype.card G.edgeSet) c f := by
  rw [edge_count]
  exact ⟨26, labelEquiv, certificate⟩
 have he := h 11 7 leafCounts G (by decide) hodd family hex
 rw [edge_count] at he
 exact wrong_predicted_value he
end Magic381805
