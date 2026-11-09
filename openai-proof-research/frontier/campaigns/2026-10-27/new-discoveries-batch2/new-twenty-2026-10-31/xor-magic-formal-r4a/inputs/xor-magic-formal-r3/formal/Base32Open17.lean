import Certificates
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace XorMagic.Base32Open17
def masks : Fin 32 → ℕ := ![1583676752,3477812620,3498704298,1144692598,3569275273,3958389900,4043082633,2121369718,2762235487,4254812488,160168239,1237407725,1045957951,4072326183,3680546581,1163355357,2115931782,1558029850,4124803409,387397214,567259896,3208667641,2587285731,2400595828,2931609122,2917757091,61838235,602103459,2691658453,3677696992,537389823,870605686]
theorem symmetry : ∀ u v, (masks u).testBit v.val = (masks v).testBit u.val := by decide
theorem noLoop : ∀ u, (masks u).testBit u.val = false := by decide
def graph := maskGraph masks symmetry noLoop
instance : DecidableRel graph.Adj := maskGraphDecidable masks symmetry noLoop
def parents : Fin 32 → Fin 32 := ![0,8,8,4,0,10,0,4,0,6,0,0,0,0,0,0,10,4,0,4,4,0,0,4,10,0,0,0,0,6,0,4]
def ranks : Fin 32 → ℕ := ![0,2,2,2,1,2,1,2,1,2,1,1,1,1,1,1,2,2,1,2,2,1,1,2,2,1,1,1,1,2,1,2]
theorem descent : ∀ v, v ≠ 0 → graph.Adj v (parents v) ∧ ranks (parents v) < ranks v := by decide
theorem connected : graph.Connected := connected_of_descent graph 0 parents ranks descent
theorem regular : graph.IsRegularOfDegree 17 := by
  change ∀ v, graph.degree v = 17
  decide
theorem label_bijective : Function.Bijective (binaryLabel 5) := by decide
noncomputable def labels : Fin 32 ≃ Bits 5 := Equiv.ofBijective (binaryLabel 5) label_bijective
theorem zero_sum : ∀ v, (∑ u ∈ graph.neighborFinset v, labels u) = 0 := by decide
theorem magic : OpenMagic graph 5 := ⟨connected, labels, zero_sum⟩
theorem exists_literal : OpenExists 5 17 :=
  ⟨Fin 32, inferInstance, inferInstance, graph, inferInstance, regular, magic⟩
end XorMagic.Base32Open17
