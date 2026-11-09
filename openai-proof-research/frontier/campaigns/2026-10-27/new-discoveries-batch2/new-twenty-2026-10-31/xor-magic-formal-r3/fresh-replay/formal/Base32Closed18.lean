import Certificates
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace XorMagic.Base32Closed18
def masks : Fin 32 → ℕ := ![2354932598,2006372761,3989240849,3379226546,3442062671,3212480841,3547178801,268381706,2918324347,1991875785,2334055132,2002401157,1968295734,1859553501,3756200975,1832007294,3215610577,1354100142,4092208327,2607091449,2049097635,2430583800,749500909,3479659398,76406270,3097325282,297925559,584705469,3862911586,3663051558,2962684510,1923958141]
theorem symmetry : ∀ u v, (masks u).testBit v.val = (masks v).testBit u.val := by decide
theorem noLoop : ∀ u, (masks u).testBit u.val = false := by decide
def graph := maskGraph masks symmetry noLoop
instance : DecidableRel graph.Adj := maskGraphDecidable masks symmetry noLoop
def parents : Fin 32 → Fin 32 := ![0,0,0,1,0,0,0,1,0,0,2,0,1,0,0,1,0,1,0,0,0,4,0,1,1,1,0,0,1,1,1,0]
def ranks : Fin 32 → ℕ := ![0,1,1,2,1,1,1,2,1,1,2,1,2,1,1,2,1,2,1,1,1,2,1,2,2,2,1,1,2,2,2,1]
theorem descent : ∀ v, v ≠ 0 → graph.Adj v (parents v) ∧ ranks (parents v) < ranks v := by decide
theorem connected : graph.Connected := connected_of_descent graph 0 parents ranks descent
theorem regular : graph.IsRegularOfDegree 18 := by
  change ∀ v, graph.degree v = 18
  decide
theorem label_bijective : Function.Bijective (binaryLabel 5) := by decide
noncomputable def labels : Fin 32 ≃ Bits 5 := Equiv.ofBijective (binaryLabel 5) label_bijective
theorem zero_sum : ∀ v, labels v + (∑ u ∈ graph.neighborFinset v, labels u) = 0 := by decide
theorem magic : ClosedMagic graph 5 := ⟨connected, labels, zero_sum⟩
theorem exists_literal : ClosedExists 5 18 :=
  ⟨Fin 32, inferInstance, inferInstance, graph, inferInstance, regular, magic⟩
end XorMagic.Base32Closed18
