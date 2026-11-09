import Certificates
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace XorMagic.Base32Closed4
def masks : Fin 32 → ℕ := ![5140,268567072,603979809,2281707520,268501249,1310726,2164310016,58851328,12591120,2415921154,4751361,3146248,25165833,1074823424,4358208,25664,335806480,33570946,1107361824,2818573312,8398880,687867904,67126528,1053056,2101440,537264256,1078001668,1076363272,66066,36175876,201596928,524872]
theorem symmetry : ∀ u v, (masks u).testBit v.val = (masks v).testBit u.val := by decide
theorem noLoop : ∀ u, (masks u).testBit u.val = false := by decide
def graph := maskGraph masks symmetry noLoop
instance : DecidableRel graph.Adj := maskGraphDecidable masks symmetry noLoop
def parents : Fin 32 → Fin 32 := ![0,5,0,12,0,2,15,23,4,28,0,3,0,8,15,10,4,1,5,10,5,29,10,12,12,29,2,19,4,2,26,19]
def ranks : Fin 32 → ℕ := ![0,3,1,2,1,2,3,3,2,3,1,3,1,3,3,2,2,4,3,2,3,3,2,2,2,3,2,3,2,2,3,3]
theorem descent : ∀ v, v ≠ 0 → graph.Adj v (parents v) ∧ ranks (parents v) < ranks v := by decide
theorem connected : graph.Connected := connected_of_descent graph 0 parents ranks descent
theorem regular : graph.IsRegularOfDegree 4 := by
  change ∀ v, graph.degree v = 4
  decide
theorem label_bijective : Function.Bijective (binaryLabel 5) := by decide
noncomputable def labels : Fin 32 ≃ Bits 5 := Equiv.ofBijective (binaryLabel 5) label_bijective
theorem zero_sum : ∀ v, labels v + (∑ u ∈ graph.neighborFinset v, labels u) = 0 := by decide
theorem magic : ClosedMagic graph 5 := ⟨connected, labels, zero_sum⟩
theorem exists_literal : ClosedExists 5 4 :=
  ⟨Fin 32, inferInstance, inferInstance, graph, inferInstance, regular, magic⟩
end XorMagic.Base32Closed4
