import Certificates
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace XorMagic.Base32Open11
def masks : Fin 32 → ℕ := ![96805254,18489593,2829616417,1392570450,943724234,1653370886,807717914,859900179,3628344453,1358251024,2281749332,20432064,181503032,34293035,1347463784,2972748,2954934913,984885250,2686618465,1301323814,3305789954,1359448644,3422573457,1711936037,2251819147,2374119592,3956801537,2253002004,539182040,344391924,83378984,257230084]
theorem symmetry : ∀ u v, (masks u).testBit v.val = (masks v).testBit u.val := by decide
theorem noLoop : ∀ u, (masks u).testBit u.val = false := by decide
def graph := maskGraph masks symmetry noLoop
instance : DecidableRel graph.Adj := maskGraphDecidable masks symmetry noLoop
def parents : Fin 32 → Fin 32 := ![0,0,0,1,1,1,1,0,0,16,2,7,16,0,13,2,0,1,0,1,1,2,0,0,0,7,0,2,7,2,8,2]
def ranks : Fin 32 → ℕ := ![0,1,1,2,2,2,2,1,1,2,2,2,2,1,2,2,1,2,1,2,2,2,1,1,1,2,1,2,2,2,2,2]
theorem descent : ∀ v, v ≠ 0 → graph.Adj v (parents v) ∧ ranks (parents v) < ranks v := by decide
theorem connected : graph.Connected := connected_of_descent graph 0 parents ranks descent
theorem regular : graph.IsRegularOfDegree 11 := by
  change ∀ v, graph.degree v = 11
  decide
theorem label_bijective : Function.Bijective (binaryLabel 5) := by decide
noncomputable def labels : Fin 32 ≃ Bits 5 := Equiv.ofBijective (binaryLabel 5) label_bijective
theorem zero_sum : ∀ v, (∑ u ∈ graph.neighborFinset v, labels u) = 0 := by decide
theorem magic : OpenMagic graph 5 := ⟨connected, labels, zero_sum⟩
theorem exists_literal : OpenExists 5 11 :=
  ⟨Fin 32, inferInstance, inferInstance, graph, inferInstance, regular, magic⟩
end XorMagic.Base32Open11
