import Certificates
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace XorMagic.Base32Open15
def masks : Fin 32 → ℕ := ![2100357890,2088995981,1050767570,4260904994,4042322084,1693211928,4219508612,3265589846,1012677729,971720897,2370283874,214927139,3275874804,1373836693,48009917,2221694163,1027096070,3881577986,2922565024,2659437352,1927758105,3356861117,1108541240,2182638334,3187881545,3789443268,152014127,86839119,3239650143,51839871,309473531,330208472]
theorem symmetry : ∀ u v, (masks u).testBit v.val = (masks v).testBit u.val := by decide
theorem noLoop : ∀ u, (masks u).testBit u.val = false := by decide
def graph := maskGraph masks symmetry noLoop
instance : DecidableRel graph.Adj := maskGraphDecidable masks symmetry noLoop
def parents : Fin 32 → Fin 32 := ![0,0,1,1,13,8,8,1,0,0,1,0,8,0,0,0,1,1,8,8,0,0,8,1,0,14,0,0,0,0,0,15]
def ranks : Fin 32 → ℕ := ![0,1,2,2,2,2,2,2,1,1,2,1,2,1,1,1,2,2,2,2,1,1,2,2,1,2,1,1,1,1,1,2]
theorem descent : ∀ v, v ≠ 0 → graph.Adj v (parents v) ∧ ranks (parents v) < ranks v := by decide
theorem connected : graph.Connected := connected_of_descent graph 0 parents ranks descent
theorem regular : graph.IsRegularOfDegree 15 := by
  change ∀ v, graph.degree v = 15
  decide
theorem label_bijective : Function.Bijective (binaryLabel 5) := by decide
noncomputable def labels : Fin 32 ≃ Bits 5 := Equiv.ofBijective (binaryLabel 5) label_bijective
theorem zero_sum : ∀ v, (∑ u ∈ graph.neighborFinset v, labels u) = 0 := by decide
theorem magic : OpenMagic graph 5 := ⟨connected, labels, zero_sum⟩
theorem exists_literal : OpenExists 5 15 :=
  ⟨Fin 32, inferInstance, inferInstance, graph, inferInstance, regular, magic⟩
end XorMagic.Base32Open15
