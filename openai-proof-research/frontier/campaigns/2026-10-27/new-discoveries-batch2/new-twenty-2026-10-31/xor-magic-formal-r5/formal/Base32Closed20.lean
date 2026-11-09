import Certificates
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace XorMagic.Base32Closed20
def masks : Fin 32 → ℕ := ![4198162040,4276477700,1465350874,2902396837,3351243045,2641596377,3487249317,3435066988,666622586,2936715759,2013216939,4274533183,4113460167,4260666068,2947487127,4291961779,1339966846,3309950973,1608086686,2993119193,988128765,2933421499,868199534,2574642650,2026370932,1887293271,271056894,1907747563,3487349799,3413704459,3137846487,1890253563]
theorem symmetry : ∀ u v, (masks u).testBit v.val = (masks v).testBit u.val := by decide
theorem noLoop : ∀ u, (masks u).testBit u.val = false := by decide
def graph := maskGraph masks symmetry noLoop
instance : DecidableRel graph.Adj := maskGraphDecidable masks symmetry noLoop
def parents : Fin 32 → Fin 32 := ![0,9,3,0,0,0,0,3,3,0,0,0,0,4,0,0,3,0,3,0,0,0,3,3,4,0,3,0,0,0,0,0]
def ranks : Fin 32 → ℕ := ![0,2,2,1,1,1,1,2,2,1,1,1,1,2,1,1,2,1,2,1,1,1,2,2,2,1,2,1,1,1,1,1]
theorem descent : ∀ v, v ≠ 0 → graph.Adj v (parents v) ∧ ranks (parents v) < ranks v := by decide
theorem connected : graph.Connected := connected_of_descent graph 0 parents ranks descent
theorem regular : graph.IsRegularOfDegree 20 := by
  change ∀ v, graph.degree v = 20
  decide
theorem label_bijective : Function.Bijective (binaryLabel 5) := by decide
noncomputable def labels : Fin 32 ≃ Bits 5 := Equiv.ofBijective (binaryLabel 5) label_bijective
theorem zero_sum : ∀ v, labels v + (∑ u ∈ graph.neighborFinset v, labels u) = 0 := by decide
theorem magic : ClosedMagic graph 5 := ⟨connected, labels, zero_sum⟩
theorem exists_literal : ClosedExists 5 20 :=
  ⟨Fin 32, inferInstance, inferInstance, graph, inferInstance, regular, magic⟩
end XorMagic.Base32Closed20
