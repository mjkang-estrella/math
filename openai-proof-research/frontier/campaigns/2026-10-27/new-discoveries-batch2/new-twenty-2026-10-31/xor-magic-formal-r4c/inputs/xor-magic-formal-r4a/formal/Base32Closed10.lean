import Certificates
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace XorMagic.Base32Closed10
def masks : Fin 32 → ℕ := ![1346913372,580288848,36001865,2148542949,441729059,353583256,287446031,6066984,1095188618,1617350784,943779905,747020300,56641220,2368244744,134354741,2726309506,529531172,5000034,538053526,3037864065,13435066,1459630660,9574289,3427895298,2284400992,1411485718,3265865760,2709613584,1109984369,3356265986,3063939841,1837670408]
theorem symmetry : ∀ u v, (masks u).testBit v.val = (masks v).testBit u.val := by decide
theorem noLoop : ∀ u, (masks u).testBit u.val = false := by decide
def graph := maskGraph masks symmetry noLoop
instance : DecidableRel graph.Adj := maskGraphDecidable masks symmetry noLoop
def parents : Fin 32 → Fin 32 := ![0,4,0,0,0,3,0,3,3,14,0,2,2,3,0,10,2,6,2,0,3,2,0,22,6,2,19,4,0,10,0,3]
def ranks : Fin 32 → ℕ := ![0,2,1,1,1,2,1,2,2,2,1,2,2,2,1,2,2,2,2,1,2,2,1,2,2,2,2,2,1,2,1,2]
theorem descent : ∀ v, v ≠ 0 → graph.Adj v (parents v) ∧ ranks (parents v) < ranks v := by decide
theorem connected : graph.Connected := connected_of_descent graph 0 parents ranks descent
theorem regular : graph.IsRegularOfDegree 10 := by
  change ∀ v, graph.degree v = 10
  decide
theorem label_bijective : Function.Bijective (binaryLabel 5) := by decide
noncomputable def labels : Fin 32 ≃ Bits 5 := Equiv.ofBijective (binaryLabel 5) label_bijective
theorem zero_sum : ∀ v, labels v + (∑ u ∈ graph.neighborFinset v, labels u) = 0 := by decide
theorem magic : ClosedMagic graph 5 := ⟨connected, labels, zero_sum⟩
theorem exists_literal : ClosedExists 5 10 :=
  ⟨Fin 32, inferInstance, inferInstance, graph, inferInstance, regular, magic⟩
end XorMagic.Base32Closed10
