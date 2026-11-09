import Certificates
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace XorMagic.Base32Open21
def masks : Fin 32 → ℕ := ![2948053922,3714678445,4258965426,2146424338,3853238220,3941384007,4007521200,4288900183,3199778421,2677615999,3351186366,3547944947,4238321979,1926714359,4160596170,1568625021,3765370587,4289836189,3756651625,1256578942,4280483653,2833239483,4281198702,858683389,1993789087,2849927145,961992671,1451135983,2916547470,401830397,157285630,309813239]
theorem symmetry : ∀ u v, (masks u).testBit v.val = (masks v).testBit u.val := by decide
theorem noLoop : ∀ u, (masks u).testBit u.val = false := by decide
def graph := maskGraph masks symmetry noLoop
instance : DecidableRel graph.Adj := maskGraphDecidable masks symmetry noLoop
def parents : Fin 32 → Fin 32 := ![0,0,1,1,7,0,5,0,0,0,1,0,0,0,1,0,0,0,0,1,0,0,1,0,0,0,0,0,1,0,1,0]
def ranks : Fin 32 → ℕ := ![0,1,2,2,2,1,2,1,1,1,2,1,1,1,2,1,1,1,1,2,1,1,2,1,1,1,1,1,2,1,2,1]
theorem descent : ∀ v, v ≠ 0 → graph.Adj v (parents v) ∧ ranks (parents v) < ranks v := by decide
theorem connected : graph.Connected := connected_of_descent graph 0 parents ranks descent
theorem regular : graph.IsRegularOfDegree 21 := by
  change ∀ v, graph.degree v = 21
  decide
theorem label_bijective : Function.Bijective (binaryLabel 5) := by decide
noncomputable def labels : Fin 32 ≃ Bits 5 := Equiv.ofBijective (binaryLabel 5) label_bijective
theorem zero_sum : ∀ v, (∑ u ∈ graph.neighborFinset v, labels u) = 0 := by decide
theorem magic : OpenMagic graph 5 := ⟨connected, labels, zero_sum⟩
theorem exists_literal : OpenExists 5 21 :=
  ⟨Fin 32, inferInstance, inferInstance, graph, inferInstance, regular, magic⟩
end XorMagic.Base32Open21
