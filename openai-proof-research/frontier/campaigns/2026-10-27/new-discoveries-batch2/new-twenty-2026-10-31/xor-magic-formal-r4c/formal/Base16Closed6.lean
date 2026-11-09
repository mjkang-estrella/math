import Certificates
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace XorMagic.Base16Closed6
def masks : Fin 16 → ℕ := ![9448,51552,15440,46209,21284,33171,2695,17001,21554,57552,37133,45126,3356,18957,9106,3626]
theorem symmetry : ∀ u v, (masks u).testBit v.val = (masks v).testBit u.val := by decide
theorem noLoop : ∀ u, (masks u).testBit u.val = false := by decide
def graph := maskGraph masks symmetry noLoop
instance : DecidableRel graph.Adj := maskGraphDecidable masks symmetry noLoop
def parents : Fin 16 → Fin 16 := ![0,5,6,0,5,0,0,0,5,6,0,6,3,0,7,3]
def ranks : Fin 16 → ℕ := ![0,2,2,1,2,1,1,1,2,2,1,2,2,1,2,2]
theorem descent : ∀ v, v ≠ 0 → graph.Adj v (parents v) ∧ ranks (parents v) < ranks v := by decide
theorem connected : graph.Connected := connected_of_descent graph 0 parents ranks descent
theorem regular : graph.IsRegularOfDegree 6 := by
  change ∀ v, graph.degree v = 6
  decide
theorem label_bijective : Function.Bijective (binaryLabel 4) := by decide
noncomputable def labels : Fin 16 ≃ Bits 4 := Equiv.ofBijective (binaryLabel 4) label_bijective
theorem zero_sum : ∀ v, labels v + (∑ u ∈ graph.neighborFinset v, labels u) = 0 := by decide
theorem magic : ClosedMagic graph 4 := ⟨connected, labels, zero_sum⟩
theorem exists_literal : ClosedExists 4 6 :=
  ⟨Fin 16, inferInstance, inferInstance, graph, inferInstance, regular, magic⟩
end XorMagic.Base16Closed6
