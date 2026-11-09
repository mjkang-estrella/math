import Certificates
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace XorMagic.Base32Closed6
def masks : Fin 32 → ℕ := ![31457552,2684403872,1610653792,3221250240,283119617,3825205254,3892314124,3791650826,1171457,73203712,144375808,37158912,1171472,33689868,67375370,134746374,268443392,318778368,352340480,419464704,16785152,146802705,44040721,73401361,270401537,2151819392,545538592,1076397120,17760272,67109094,134217964,33554666]
theorem symmetry : ∀ u v, (masks u).testBit v.val = (masks v).testBit u.val := by decide
theorem noLoop : ∀ u, (masks u).testBit u.val = false := by decide
def graph := maskGraph masks symmetry noLoop
instance : DecidableRel graph.Adj := maskGraphDecidable masks symmetry noLoop
def parents : Fin 32 → Fin 32 := ![0,14,13,13,0,26,27,25,0,22,23,21,4,8,8,8,8,24,24,24,8,0,0,0,0,22,23,21,4,26,27,25]
def ranks : Fin 32 → ℕ := ![0,3,3,3,1,3,3,3,1,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,2,2,2,2,3,3,3]
theorem descent : ∀ v, v ≠ 0 → graph.Adj v (parents v) ∧ ranks (parents v) < ranks v := by decide
theorem connected : graph.Connected := connected_of_descent graph 0 parents ranks descent
theorem regular : graph.IsRegularOfDegree 6 := by
  change ∀ v, graph.degree v = 6
  decide
theorem label_bijective : Function.Bijective (binaryLabel 5) := by decide
noncomputable def labels : Fin 32 ≃ Bits 5 := Equiv.ofBijective (binaryLabel 5) label_bijective
theorem zero_sum : ∀ v, labels v + (∑ u ∈ graph.neighborFinset v, labels u) = 0 := by decide
theorem magic : ClosedMagic graph 5 := ⟨connected, labels, zero_sum⟩
theorem exists_literal : ClosedExists 5 6 :=
  ⟨Fin 32, inferInstance, inferInstance, graph, inferInstance, regular, magic⟩
end XorMagic.Base32Closed6
