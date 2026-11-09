import Certificates
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace XorMagic.Base32Closed8
def masks : Fin 32 → ℕ := ![545298632,136995456,475072576,3323461697,342426880,812797952,21628941,2181099523,1292633104,2686627842,159469840,1091702853,671092385,2753593986,13894818,2198086273,362808340,9701986,1245888768,79692122,285362220,805380658,269238388,3221963777,269585728,3422847112,34152732,570692870,24182836,1210069537,2726562056,1115726472]
theorem symmetry : ∀ u v, (masks u).testBit v.val = (masks v).testBit u.val := by decide
theorem noLoop : ∀ u, (masks u).testBit u.val = false := by decide
def graph := maskGraph masks symmetry noLoop
instance : DecidableRel graph.Adj := maskGraphDecidable masks symmetry noLoop
def parents : Fin 32 → Fin 32 := ![0,7,6,0,19,12,0,0,19,12,12,0,0,7,7,0,23,6,15,3,3,29,6,0,6,3,3,12,20,0,3,3]
def ranks : Fin 32 → ℕ := ![0,2,2,1,3,2,1,1,3,2,2,1,1,2,2,1,2,2,2,2,2,2,2,1,2,2,2,2,3,1,2,2]
theorem descent : ∀ v, v ≠ 0 → graph.Adj v (parents v) ∧ ranks (parents v) < ranks v := by decide
theorem connected : graph.Connected := connected_of_descent graph 0 parents ranks descent
theorem regular : graph.IsRegularOfDegree 8 := by
  change ∀ v, graph.degree v = 8
  decide
theorem label_bijective : Function.Bijective (binaryLabel 5) := by decide
noncomputable def labels : Fin 32 ≃ Bits 5 := Equiv.ofBijective (binaryLabel 5) label_bijective
theorem zero_sum : ∀ v, labels v + (∑ u ∈ graph.neighborFinset v, labels u) = 0 := by decide
theorem magic : ClosedMagic graph 5 := ⟨connected, labels, zero_sum⟩
theorem exists_literal : ClosedExists 5 8 :=
  ⟨Fin 32, inferInstance, inferInstance, graph, inferInstance, regular, magic⟩
end XorMagic.Base32Closed8
