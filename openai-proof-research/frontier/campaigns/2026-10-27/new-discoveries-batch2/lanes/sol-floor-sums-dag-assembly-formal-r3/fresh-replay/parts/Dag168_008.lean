import parts.Dag168_007
import generated.th_lemma_16
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n17271 (_v : Vars) (_q : Query _v) (h6571 : (e6571 _v)) : (e2697 _v) := by
  have p11373 := n11373 _v _q 
  have p14141 := n14141 _v _q h6571
  simp only [e2697, e2746, e6758, e11372] at *
  tauto
end
end Assembly
