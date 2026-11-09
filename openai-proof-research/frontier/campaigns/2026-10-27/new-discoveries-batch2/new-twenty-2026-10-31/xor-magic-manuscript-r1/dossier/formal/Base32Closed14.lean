import Certificates
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace XorMagic.Base32Closed14
def masks : Fin 32 → ℕ := ![2711290542,817154673,796262993,3150274689,725692006,336577363,251884598,2173597449,1532731552,40154295,4134798032,3057557522,3249005248,222632920,614404330,3131579170,2178969977,2736806373,169901742,3907045793,3726658823,1084202502,1703487260,1885982859,1346580957,1343655772,4166020196,3558646108,1334873386,80399391,2683835648,1276877961]
theorem symmetry : ∀ u v, (masks u).testBit v.val = (masks v).testBit u.val := by decide
theorem noLoop : ∀ u, (masks u).testBit u.val = false := by decide
def graph := maskGraph masks symmetry noLoop
instance : DecidableRel graph.Adj := maskGraphDecidable masks symmetry noLoop
def parents : Fin 32 → Fin 32 := ![0,0,0,0,1,0,1,0,5,0,7,1,7,3,1,1,0,0,1,0,0,1,2,0,0,2,2,2,1,0,19,0]
def ranks : Fin 32 → ℕ := ![0,1,1,1,2,1,2,1,2,1,2,2,2,2,2,2,1,1,2,1,1,2,2,1,1,2,2,2,2,1,2,1]
theorem descent : ∀ v, v ≠ 0 → graph.Adj v (parents v) ∧ ranks (parents v) < ranks v := by decide
theorem connected : graph.Connected := connected_of_descent graph 0 parents ranks descent
theorem regular : graph.IsRegularOfDegree 14 := by
  change ∀ v, graph.degree v = 14
  decide
theorem label_bijective : Function.Bijective (binaryLabel 5) := by decide
noncomputable def labels : Fin 32 ≃ Bits 5 := Equiv.ofBijective (binaryLabel 5) label_bijective
theorem zero_sum : ∀ v, labels v + (∑ u ∈ graph.neighborFinset v, labels u) = 0 := by decide
theorem magic : ClosedMagic graph 5 := ⟨connected, labels, zero_sum⟩
theorem exists_literal : ClosedExists 5 14 :=
  ⟨Fin 32, inferInstance, inferInstance, graph, inferInstance, regular, magic⟩
end XorMagic.Base32Closed14
