import Certificates
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace XorMagic.Base16Closed10
def masks : Fin 16 → ℕ := ![36286,6013,53723,47895,10159,60243,48550,32341,19583,60602,29651,54249,60622,55032,49060,31341]
theorem symmetry : ∀ u v, (masks u).testBit v.val = (masks v).testBit u.val := by decide
theorem noLoop : ∀ u, (masks u).testBit u.val = false := by decide
def graph := maskGraph masks symmetry noLoop
instance : DecidableRel graph.Adj := maskGraphDecidable masks symmetry noLoop
def parents : Fin 16 → Fin 16 := ![0,0,0,0,0,0,1,0,0,1,0,0,1,3,2,0]
def ranks : Fin 16 → ℕ := ![0,1,1,1,1,1,2,1,1,2,1,1,2,2,2,1]
theorem descent : ∀ v, v ≠ 0 → graph.Adj v (parents v) ∧ ranks (parents v) < ranks v := by decide
theorem connected : graph.Connected := connected_of_descent graph 0 parents ranks descent
theorem regular : graph.IsRegularOfDegree 10 := by
  change ∀ v, graph.degree v = 10
  decide
theorem label_bijective : Function.Bijective (binaryLabel 4) := by decide
noncomputable def labels : Fin 16 ≃ Bits 4 := Equiv.ofBijective (binaryLabel 4) label_bijective
theorem zero_sum : ∀ v, labels v + (∑ u ∈ graph.neighborFinset v, labels u) = 0 := by decide
theorem magic : ClosedMagic graph 4 := ⟨connected, labels, zero_sum⟩
theorem exists_literal : ClosedExists 4 10 :=
  ⟨Fin 16, inferInstance, inferInstance, graph, inferInstance, regular, magic⟩
end XorMagic.Base16Closed10
