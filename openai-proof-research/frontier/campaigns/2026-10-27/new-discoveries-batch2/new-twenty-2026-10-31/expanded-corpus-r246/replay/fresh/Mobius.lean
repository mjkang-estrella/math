import Init
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace Mobius
/-- Cycle C_(2n), followed by its n antipodal edges. -/
def edge (n i : Nat) : Nat × Nat :=
  if i < 2*n then (i, (i+1) % (2*n)) else (i-2*n, i-n)
def edgeIndices (n : Nat) : List Nat := List.range (3*n)
def vertexSum (n : Nat) (labels : List Nat) (v : Nat) : Nat :=
  ((edgeIndices n).filter (fun i => (edge n i).1 == v || (edge n i).2 == v)).foldl
    (fun s i => s + labels[i]!) 0
def colorCount (n : Nat) (labels : List Nat) : Nat :=
  (((List.range (2*n)).map (vertexSum n labels)).eraseDups).length
/-- Permutation of 1,...,3n, with unequal sums at every adjacent pair. -/
def LocalAntimagic (n : Nat) (labels : List Nat) : Prop :=
  labels.Perm (List.range' 1 (3*n)) ∧
  ∀ i ∈ edgeIndices n, vertexSum n labels (edge n i).1 ≠ vertexSum n labels (edge n i).2
instance localDecidable (n : Nat) (l : List Nat) : Decidable (LocalAntimagic n l) := inferInstanceAs
  (Decidable (l.Perm (List.range' 1 (3*n)) ∧ ∀ i ∈ edgeIndices n,
    vertexSum n l (edge n i).1 ≠ vertexSum n l (edge n i).2))
/-- Equality to k for the minimum over all local antimagic edge labelings. -/
def LocalAntimagicChromaticNumberEq (n k : Nat) : Prop :=
  (∃ l, LocalAntimagic n l ∧ colorCount n l = k) ∧
  ∀ l, LocalAntimagic n l → k ≤ colorCount n l
def witness : List Nat := [17,13,7,8,3,15,6,18,4,5,12,2,10,1,9,16,14,11]
theorem witness_valid : LocalAntimagic 6 witness := by decide
theorem witness_colors : colorCount 6 witness = 3 := by decide
theorem witness_sums : (List.range 12).map (vertexSum 6 witness) =
  [29,31,29,31,25,29,31,25,31,25,31,25] := by decide
theorem number_not_four : ¬ LocalAntimagicChromaticNumberEq 6 4 := by
  intro h
  have hle := h.2 witness witness_valid
  rw [witness_colors] at hle
  exact (by decide : ¬ (4 ≤ 3)) hle
/-- Exact negation of Conjecture 3.2, including even n >= 4. -/
theorem conjecture_false : ¬ (∀ n : Nat, 4 ≤ n → n % 2 = 0 →
    LocalAntimagicChromaticNumberEq n 4) := by
  intro h
  exact number_not_four (h 6 (by decide) (by decide))
/-- Simple undirected edges: no repetition and no loops for the witness graph. -/
def simpleEdges (n : Nat) : List (Nat × Nat) :=
  (edgeIndices n).map (fun i => let (u,v) := edge n i; (min u v, max u v))
theorem simple_edges_nodup : (simpleEdges 6).Nodup := by decide
theorem no_loops_and_in_range : ∀ i ∈ edgeIndices 6,
  (edge 6 i).1 < 12 ∧ (edge 6 i).2 < 12 ∧ (edge 6 i).1 ≠ (edge 6 i).2 := by decide
/-- Each cycle or antipodal pair, and only those pairs, occurs in the enumeration. -/
theorem adjacency_literal : ∀ u : Fin 12, ∀ v : Fin 12,
  ((min u.val v.val, max u.val v.val) ∈ simpleEdges 6) ↔
  (v.val = (u.val+1)%12 ∨ u.val = (v.val+1)%12 ∨
   (u.val < 6 ∧ v.val = u.val+6) ∨ (v.val < 6 ∧ u.val = v.val+6)) := by decide
#print axioms edge
#print axioms edgeIndices
#print axioms vertexSum
#print axioms colorCount
#print axioms LocalAntimagic
#print axioms localDecidable
#print axioms LocalAntimagicChromaticNumberEq
#print axioms witness
#print axioms witness_sums
#print axioms simpleEdges
#print axioms witness_valid
#print axioms witness_colors
#print axioms number_not_four
#print axioms conjecture_false
#print axioms simple_edges_nodup
#print axioms no_loops_and_in_range
#print axioms adjacency_literal
end Mobius
