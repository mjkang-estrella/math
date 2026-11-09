import Certificates
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace XorMagic.Base32Open7
def masks : Fin 32 → ℕ := ![564134720,42606784,2158133344,3233817728,184617728,1627922564,285221895,9306154,269828113,269828113,537024584,606356496,942801920,268976234,2147757824,1260912644,2284847888,5248134,100682624,12624034,142807808,67213317,1695154184,1573007,1077969009,2550431762,3361998848,101814288,2181051200,1077943329,624984104,369180684]
theorem symmetry : ∀ u v, (masks u).testBit v.val = (masks v).testBit u.val := by decide
theorem noLoop : ∀ u, (masks u).testBit u.val = false := by decide
def graph := maskGraph masks symmetry noLoop
instance : DecidableRel graph.Adj := maskGraphDecidable masks symmetry noLoop
def parents : Fin 32 → Fin 32 := ![0,6,6,23,8,24,0,23,0,0,6,21,21,6,8,21,8,1,8,23,8,0,24,0,0,1,21,4,6,0,24,2]
def ranks : Fin 32 → ℕ := ![0,2,2,2,2,2,1,2,1,1,2,2,2,2,2,2,2,3,2,2,2,1,2,1,1,3,2,3,2,1,2,3]
theorem descent : ∀ v, v ≠ 0 → graph.Adj v (parents v) ∧ ranks (parents v) < ranks v := by decide
theorem connected : graph.Connected := connected_of_descent graph 0 parents ranks descent
theorem regular : graph.IsRegularOfDegree 7 := by
  change ∀ v, graph.degree v = 7
  decide
theorem label_bijective : Function.Bijective (binaryLabel 5) := by decide
noncomputable def labels : Fin 32 ≃ Bits 5 := Equiv.ofBijective (binaryLabel 5) label_bijective
theorem zero_sum : ∀ v, (∑ u ∈ graph.neighborFinset v, labels u) = 0 := by decide
theorem magic : OpenMagic graph 5 := ⟨connected, labels, zero_sum⟩
theorem exists_literal : OpenExists 5 7 :=
  ⟨Fin 32, inferInstance, inferInstance, graph, inferInstance, regular, magic⟩
end XorMagic.Base32Open7
