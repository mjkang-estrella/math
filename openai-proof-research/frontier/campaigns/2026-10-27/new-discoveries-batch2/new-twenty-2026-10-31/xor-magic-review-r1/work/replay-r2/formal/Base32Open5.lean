import Certificates
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace XorMagic.Base32Open5
def masks : Fin 32 → ℕ := ![306446338,61,2232834,329986,75498562,2684356098,2415952144,2954889216,33693768,134357028,67176496,20972680,1143472132,37765888,278142976,813760576,1090552840,150995716,138428425,3240103936,1749041152,67637380,1320961,2214641680,34277376,553656577,10490896,1075184128,49345,34635936,135860224,8913120]
theorem symmetry : ∀ u v, (masks u).testBit v.val = (masks v).testBit u.val := by decide
theorem noLoop : ∀ u, (masks u).testBit u.val = false := by decide
def graph := maskGraph masks symmetry noLoop
instance : DecidableRel graph.Adj := maskGraphDecidable masks symmetry noLoop
def parents : Fin 32 → Fin 32 := ![0,0,1,1,1,1,28,28,25,2,4,22,2,22,18,28,3,2,0,24,22,2,0,4,25,0,4,18,0,25,27,5]
def ranks : Fin 32 → ℕ := ![0,1,2,2,2,2,2,2,2,3,3,2,3,2,2,2,3,3,1,3,2,3,1,3,2,1,3,2,1,2,3,3]
theorem descent : ∀ v, v ≠ 0 → graph.Adj v (parents v) ∧ ranks (parents v) < ranks v := by decide
theorem connected : graph.Connected := connected_of_descent graph 0 parents ranks descent
theorem regular : graph.IsRegularOfDegree 5 := by
  change ∀ v, graph.degree v = 5
  decide
theorem label_bijective : Function.Bijective (binaryLabel 5) := by decide
noncomputable def labels : Fin 32 ≃ Bits 5 := Equiv.ofBijective (binaryLabel 5) label_bijective
theorem zero_sum : ∀ v, (∑ u ∈ graph.neighborFinset v, labels u) = 0 := by decide
theorem magic : OpenMagic graph 5 := ⟨connected, labels, zero_sum⟩
theorem exists_literal : OpenExists 5 5 :=
  ⟨Fin 32, inferInstance, inferInstance, graph, inferInstance, regular, magic⟩
end XorMagic.Base32Open5
