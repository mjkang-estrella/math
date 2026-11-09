import Certificates
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace XorMagic.Base32Closed12
def masks : Fin 32 → ℕ := ![164175378,2920343809,369600384,3269509744,87720393,739074760,1075032888,2246737972,699449430,1619086445,3577221637,1929855491,3448521793,1646706790,1610824490,1084760542,2823047781,2551474388,381892644,2958070961,2525627730,2474681752,4178378889,171217801,1180704145,2444503054,420746422,885199139,243141636,1212771106,557907528,41620618]
theorem symmetry : ∀ u v, (masks u).testBit v.val = (masks v).testBit u.val := by decide
theorem noLoop : ∀ u, (masks u).testBit u.val = false := by decide
def graph := maskGraph masks symmetry noLoop
instance : DecidableRel graph.Adj := maskGraphDecidable masks symmetry noLoop
def parents : Fin 32 → Fin 32 := ![0,0,9,4,0,9,4,4,1,0,0,0,0,1,1,1,0,4,11,0,1,4,0,0,0,1,1,0,10,1,9,1]
def ranks : Fin 32 → ℕ := ![0,1,2,2,1,2,2,2,2,1,1,1,1,2,2,2,1,2,2,1,2,2,1,1,1,2,2,1,2,2,2,2]
theorem descent : ∀ v, v ≠ 0 → graph.Adj v (parents v) ∧ ranks (parents v) < ranks v := by decide
theorem connected : graph.Connected := connected_of_descent graph 0 parents ranks descent
theorem regular : graph.IsRegularOfDegree 12 := by
  change ∀ v, graph.degree v = 12
  decide
theorem label_bijective : Function.Bijective (binaryLabel 5) := by decide
noncomputable def labels : Fin 32 ≃ Bits 5 := Equiv.ofBijective (binaryLabel 5) label_bijective
theorem zero_sum : ∀ v, labels v + (∑ u ∈ graph.neighborFinset v, labels u) = 0 := by decide
theorem magic : ClosedMagic graph 5 := ⟨connected, labels, zero_sum⟩
theorem exists_literal : ClosedExists 5 12 :=
  ⟨Fin 32, inferInstance, inferInstance, graph, inferInstance, regular, magic⟩
end XorMagic.Base32Closed12
