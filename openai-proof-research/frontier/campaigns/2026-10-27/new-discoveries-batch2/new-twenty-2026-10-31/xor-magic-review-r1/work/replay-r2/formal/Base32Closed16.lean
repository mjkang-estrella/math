import Certificates
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace XorMagic.Base32Closed16
def masks : Fin 32 → ℕ := ![2194609404,2205971312,3244199721,34062293,252645195,2601755335,75458619,1029377321,3282289310,3323245886,1924682397,4080038108,1019088395,2921122410,4246940994,2073240364,3267805689,413258237,1372140127,1635005655,2366160614,936009026,3182231751,2103940353,1090308534,471969595,4075844304,4073910448,786881696,3706256512,2911751940,1817275175]
theorem symmetry : ∀ u v, (masks u).testBit v.val = (masks v).testBit u.val := by decide
theorem noLoop : ∀ u, (masks u).testBit u.val = false := by decide
def graph := maskGraph masks symmetry noLoop
instance : DecidableRel graph.Adj := maskGraphDecidable masks symmetry noLoop
def parents : Fin 32 → Fin 32 := ![0,4,0,0,0,0,0,0,2,2,0,2,0,3,6,2,0,0,0,0,2,6,0,0,2,0,4,4,5,7,2,0]
def ranks : Fin 32 → ℕ := ![0,2,1,1,1,1,1,1,2,2,1,2,1,2,2,2,1,1,1,1,2,2,1,1,2,1,2,2,2,2,2,1]
theorem descent : ∀ v, v ≠ 0 → graph.Adj v (parents v) ∧ ranks (parents v) < ranks v := by decide
theorem connected : graph.Connected := connected_of_descent graph 0 parents ranks descent
theorem regular : graph.IsRegularOfDegree 16 := by
  change ∀ v, graph.degree v = 16
  decide
theorem label_bijective : Function.Bijective (binaryLabel 5) := by decide
noncomputable def labels : Fin 32 ≃ Bits 5 := Equiv.ofBijective (binaryLabel 5) label_bijective
theorem zero_sum : ∀ v, labels v + (∑ u ∈ graph.neighborFinset v, labels u) = 0 := by decide
theorem magic : ClosedMagic graph 5 := ⟨connected, labels, zero_sum⟩
theorem exists_literal : ClosedExists 5 16 :=
  ⟨Fin 32, inferInstance, inferInstance, graph, inferInstance, regular, magic⟩
end XorMagic.Base32Closed16
