import Certificates
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace XorMagic.Base32Open13
def masks : Fin 32 → ℕ := ![1940034696,2288594532,305726442,915740741,852904608,1082486422,747788430,4026585461,1376642692,2303090998,1960911139,2292564090,2326667465,2435405602,538749936,2462927233,1079291182,2940736081,202496824,1687351558,2244821084,1862286343,3541272082,806919289,4201783809,1164087581,3929932872,3576044098,163620253,95044825,258540961,223525506]
theorem symmetry : ∀ u v, (masks u).testBit v.val = (masks v).testBit u.val := by decide
theorem noLoop : ∀ u, (masks u).testBit u.val = false := by decide
def graph := maskGraph masks symmetry noLoop
instance : DecidableRel graph.Adj := maskGraphDecidable masks symmetry noLoop
def parents : Fin 32 → Fin 32 := ![0,10,3,0,7,7,3,0,7,17,0,3,0,10,7,0,3,0,3,12,3,0,10,0,0,0,3,12,0,0,0,7]
def ranks : Fin 32 → ℕ := ![0,2,2,1,2,2,2,1,2,2,1,2,1,2,2,1,2,1,2,2,2,1,2,1,1,1,2,2,1,1,1,2]
theorem descent : ∀ v, v ≠ 0 → graph.Adj v (parents v) ∧ ranks (parents v) < ranks v := by decide
theorem connected : graph.Connected := connected_of_descent graph 0 parents ranks descent
theorem regular : graph.IsRegularOfDegree 13 := by
  change ∀ v, graph.degree v = 13
  decide
theorem label_bijective : Function.Bijective (binaryLabel 5) := by decide
noncomputable def labels : Fin 32 ≃ Bits 5 := Equiv.ofBijective (binaryLabel 5) label_bijective
theorem zero_sum : ∀ v, (∑ u ∈ graph.neighborFinset v, labels u) = 0 := by decide
theorem magic : OpenMagic graph 5 := ⟨connected, labels, zero_sum⟩
theorem exists_literal : OpenExists 5 13 :=
  ⟨Fin 32, inferInstance, inferInstance, graph, inferInstance, regular, magic⟩
end XorMagic.Base32Open13
