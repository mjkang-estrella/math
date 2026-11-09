import Certificates
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace XorMagic.Base32Open9
def masks : Fin 32 → ℕ := ![2751596652,2499819016,1080590425,1074047047,316772356,2316902529,614469901,3027744,2298953920,447758466,457293826,2953359369,319031506,137496746,1881343744,554437660,68568368,587293057,1086427528,610306212,2374050336,1074291412,3364619284,877920848,303207682,620893744,1117323331,3226478368,25189906,42649665,2355380236,1213204771]
theorem symmetry : ∀ u v, (masks u).testBit v.val = (masks v).testBit u.val := by decide
theorem noLoop : ∀ u, (masks u).testBit u.val = false := by decide
def graph := maskGraph masks symmetry noLoop
instance : DecidableRel graph.Adj := maskGraphDecidable masks symmetry noLoop
def parents : Fin 32 → Fin 32 := ![0,3,0,0,2,0,0,5,6,21,15,0,6,3,17,2,5,0,3,2,5,2,2,6,17,5,0,5,11,0,2,0]
def ranks : Fin 32 → ℕ := ![0,2,1,1,2,1,1,2,2,3,3,1,2,2,2,2,2,1,2,2,2,2,2,2,2,2,1,2,2,1,2,1]
theorem descent : ∀ v, v ≠ 0 → graph.Adj v (parents v) ∧ ranks (parents v) < ranks v := by decide
theorem connected : graph.Connected := connected_of_descent graph 0 parents ranks descent
theorem regular : graph.IsRegularOfDegree 9 := by
  change ∀ v, graph.degree v = 9
  decide
theorem label_bijective : Function.Bijective (binaryLabel 5) := by decide
noncomputable def labels : Fin 32 ≃ Bits 5 := Equiv.ofBijective (binaryLabel 5) label_bijective
theorem zero_sum : ∀ v, (∑ u ∈ graph.neighborFinset v, labels u) = 0 := by decide
theorem magic : OpenMagic graph 5 := ⟨connected, labels, zero_sum⟩
theorem exists_literal : OpenExists 5 9 :=
  ⟨Fin 32, inferInstance, inferInstance, graph, inferInstance, regular, magic⟩
end XorMagic.Base32Open9
