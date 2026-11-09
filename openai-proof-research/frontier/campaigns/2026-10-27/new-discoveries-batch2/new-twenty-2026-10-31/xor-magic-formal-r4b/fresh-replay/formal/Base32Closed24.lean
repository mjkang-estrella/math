import Certificates
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace XorMagic.Base32Closed24
def masks : Fin 32 → ℕ := ![3730832574,4252360509,2136833947,1061149559,4110349551,2667044699,4009745336,4285661013,4025138926,4025138670,3757941687,3688608751,3352161279,4025982869,2147193087,3034021883,2010053871,4289588089,4194022527,4281818973,4151110911,4225656826,2595618807,4285005680,3200221070,1710981101,865859583,4058935279,1845480639,2680153054,2596241367,1778302963]
theorem symmetry : ∀ u v, (masks u).testBit v.val = (masks v).testBit u.val := by decide
theorem noLoop : ∀ u, (masks u).testBit u.val = false := by decide
def graph := maskGraph masks symmetry noLoop
instance : DecidableRel graph.Adj := maskGraphDecidable masks symmetry noLoop
def parents : Fin 32 → Fin 32 := ![0,0,0,0,0,0,3,0,1,1,0,0,0,0,0,0,0,0,0,0,0,1,0,4,1,0,0,0,0,1,0,0]
def ranks : Fin 32 → ℕ := ![0,1,1,1,1,1,2,1,2,2,1,1,1,1,1,1,1,1,1,1,1,2,1,2,2,1,1,1,1,2,1,1]
theorem descent : ∀ v, v ≠ 0 → graph.Adj v (parents v) ∧ ranks (parents v) < ranks v := by decide
theorem connected : graph.Connected := connected_of_descent graph 0 parents ranks descent
theorem regular : graph.IsRegularOfDegree 24 := by
  change ∀ v, graph.degree v = 24
  decide
theorem label_bijective : Function.Bijective (binaryLabel 5) := by decide
noncomputable def labels : Fin 32 ≃ Bits 5 := Equiv.ofBijective (binaryLabel 5) label_bijective
theorem zero_sum : ∀ v, labels v + (∑ u ∈ graph.neighborFinset v, labels u) = 0 := by decide
theorem magic : ClosedMagic graph 5 := ⟨connected, labels, zero_sum⟩
theorem exists_literal : ClosedExists 5 24 :=
  ⟨Fin 32, inferInstance, inferInstance, graph, inferInstance, regular, magic⟩
end XorMagic.Base32Closed24
