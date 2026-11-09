import Certificates
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace XorMagic.Base32Open19
def masks : Fin 32 → ℕ := ![4130791916,1374623484,3925366907,1025457543,4207246886,3555892503,3219934343,2048229195,3595517609,2675880338,717744634,2365109756,846441406,2648252313,2684126421,3210173985,1471853978,1743361835,3912812507,1336372046,1768290989,1818188391,112394102,4115360886,3097485934,1816909809,3807112009,3275550428,3783390203,2545325277,2663317943,2105863029]
theorem symmetry : ∀ u v, (masks u).testBit v.val = (masks v).testBit u.val := by decide
theorem noLoop : ∀ u, (masks u).testBit u.val = false := by decide
def graph := maskGraph masks symmetry noLoop
instance : DecidableRel graph.Adj := maskGraphDecidable masks symmetry noLoop
def parents : Fin 32 → Fin 32 := ![0,2,0,0,2,0,0,0,0,7,3,2,2,0,0,0,3,0,0,2,0,0,2,2,2,0,0,2,0,0,0,0]
def ranks : Fin 32 → ℕ := ![0,2,1,1,2,1,1,1,1,2,2,2,2,1,1,1,2,1,1,2,1,1,2,2,2,1,1,2,1,1,1,1]
theorem descent : ∀ v, v ≠ 0 → graph.Adj v (parents v) ∧ ranks (parents v) < ranks v := by decide
theorem connected : graph.Connected := connected_of_descent graph 0 parents ranks descent
theorem regular : graph.IsRegularOfDegree 19 := by
  change ∀ v, graph.degree v = 19
  decide
theorem label_bijective : Function.Bijective (binaryLabel 5) := by decide
noncomputable def labels : Fin 32 ≃ Bits 5 := Equiv.ofBijective (binaryLabel 5) label_bijective
theorem zero_sum : ∀ v, (∑ u ∈ graph.neighborFinset v, labels u) = 0 := by decide
theorem magic : OpenMagic graph 5 := ⟨connected, labels, zero_sum⟩
theorem exists_literal : OpenExists 5 19 :=
  ⟨Fin 32, inferInstance, inferInstance, graph, inferInstance, regular, magic⟩
end XorMagic.Base32Open19
