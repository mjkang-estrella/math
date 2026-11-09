import Certificates
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace XorMagic.Base16Open9
def masks : Fin 16 → ℕ := ![56086,13981,50091,19318,44235,32332,62776,48406,43725,7471,27378,18361,58083,38386,40045,29141]
theorem symmetry : ∀ u v, (masks u).testBit v.val = (masks v).testBit u.val := by decide
theorem noLoop : ∀ u, (masks u).testBit u.val = false := by decide
def graph := maskGraph masks symmetry noLoop
instance : DecidableRel graph.Adj := maskGraphDecidable masks symmetry noLoop
def parents : Fin 16 → Fin 16 := ![0,0,0,1,0,2,4,1,0,0,1,0,0,1,0,0]
def ranks : Fin 16 → ℕ := ![0,1,1,2,1,2,2,2,1,1,2,1,1,2,1,1]
theorem descent : ∀ v, v ≠ 0 → graph.Adj v (parents v) ∧ ranks (parents v) < ranks v := by decide
theorem connected : graph.Connected := connected_of_descent graph 0 parents ranks descent
theorem regular : graph.IsRegularOfDegree 9 := by
  change ∀ v, graph.degree v = 9
  decide
theorem label_bijective : Function.Bijective (binaryLabel 4) := by decide
noncomputable def labels : Fin 16 ≃ Bits 4 := Equiv.ofBijective (binaryLabel 4) label_bijective
theorem zero_sum : ∀ v, (∑ u ∈ graph.neighborFinset v, labels u) = 0 := by decide
theorem magic : OpenMagic graph 4 := ⟨connected, labels, zero_sum⟩
theorem exists_literal : OpenExists 4 9 :=
  ⟨Fin 16, inferInstance, inferInstance, graph, inferInstance, regular, magic⟩
end XorMagic.Base16Open9
