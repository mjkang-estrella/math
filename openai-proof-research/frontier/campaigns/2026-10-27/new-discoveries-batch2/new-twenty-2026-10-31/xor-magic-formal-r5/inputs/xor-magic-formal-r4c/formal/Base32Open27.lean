import Certificates
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace XorMagic.Base32Open27
def masks : Fin 32 → ℕ := ![4294962154,4026400221,3690987482,2013259767,4026466030,4293656537,2130657215,4236115839,4282375919,1879045629,4290214910,4291818999,4269797366,3220135679,4290592703,4294908863,3959095279,4261265277,3187343327,1475869695,4285519839,3605002239,4223646463,4285525631,4276088639,3724148607,3149856763,3084386295,4026465773,3721920507,3019628543,2146958775]
theorem symmetry : ∀ u v, (masks u).testBit v.val = (masks v).testBit u.val := by decide
theorem noLoop : ∀ u, (masks u).testBit u.val = false := by decide
def graph := maskGraph masks symmetry noLoop
instance : DecidableRel graph.Adj := maskGraphDecidable masks symmetry noLoop
def parents : Fin 32 → Fin 32 := ![0,0,1,0,1,0,0,0,0,0,1,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def ranks : Fin 32 → ℕ := ![0,1,2,1,2,1,1,1,1,1,2,1,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
theorem descent : ∀ v, v ≠ 0 → graph.Adj v (parents v) ∧ ranks (parents v) < ranks v := by decide
theorem connected : graph.Connected := connected_of_descent graph 0 parents ranks descent
theorem regular : graph.IsRegularOfDegree 27 := by
  change ∀ v, graph.degree v = 27
  decide
theorem label_bijective : Function.Bijective (binaryLabel 5) := by decide
noncomputable def labels : Fin 32 ≃ Bits 5 := Equiv.ofBijective (binaryLabel 5) label_bijective
theorem zero_sum : ∀ v, (∑ u ∈ graph.neighborFinset v, labels u) = 0 := by decide
theorem magic : OpenMagic graph 5 := ⟨connected, labels, zero_sum⟩
theorem exists_literal : OpenExists 5 27 :=
  ⟨Fin 32, inferInstance, inferInstance, graph, inferInstance, regular, magic⟩
end XorMagic.Base32Open27
