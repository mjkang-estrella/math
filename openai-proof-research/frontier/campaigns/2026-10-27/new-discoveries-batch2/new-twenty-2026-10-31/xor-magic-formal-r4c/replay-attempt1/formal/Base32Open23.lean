import Certificates
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace XorMagic.Base32Open23
def masks : Fin 32 → ℕ := ![3749668662,4157971837,3819894715,971505590,3952540399,3482169311,4273338290,2113867644,3002333935,1608338941,4135496431,3203262394,3623870814,1541365117,4281056093,2096848254,3932093419,4285134237,3048816383,4214750885,4008556499,3487489485,4021534603,1064614910,4008604351,838565751,4193705699,3590056697,4002349003,2548026846,494663415,1031757175]
theorem symmetry : ∀ u v, (masks u).testBit v.val = (masks v).testBit u.val := by decide
theorem noLoop : ∀ u, (masks u).testBit u.val = false := by decide
def graph := maskGraph masks symmetry noLoop
instance : DecidableRel graph.Adj := maskGraphDecidable masks symmetry noLoop
def parents : Fin 32 → Fin 32 := ![0,0,0,1,0,0,1,2,0,0,0,1,1,0,0,1,0,0,0,0,0,0,0,1,0,0,0,0,0,1,0,0]
def ranks : Fin 32 → ℕ := ![0,1,1,2,1,1,2,2,1,1,1,2,2,1,1,2,1,1,1,1,1,1,1,2,1,1,1,1,1,2,1,1]
theorem descent : ∀ v, v ≠ 0 → graph.Adj v (parents v) ∧ ranks (parents v) < ranks v := by decide
theorem connected : graph.Connected := connected_of_descent graph 0 parents ranks descent
theorem regular : graph.IsRegularOfDegree 23 := by
  change ∀ v, graph.degree v = 23
  decide
theorem label_bijective : Function.Bijective (binaryLabel 5) := by decide
noncomputable def labels : Fin 32 ≃ Bits 5 := Equiv.ofBijective (binaryLabel 5) label_bijective
theorem zero_sum : ∀ v, (∑ u ∈ graph.neighborFinset v, labels u) = 0 := by decide
theorem magic : OpenMagic graph 5 := ⟨connected, labels, zero_sum⟩
theorem exists_literal : OpenExists 5 23 :=
  ⟨Fin 32, inferInstance, inferInstance, graph, inferInstance, regular, magic⟩
end XorMagic.Base32Open23
