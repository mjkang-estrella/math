import parts.Dag168_023
import generated.th_lemma_16
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n17287 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) : (e4314 _v) := by
  have p14704 := n14704 _v _q 
  have p17049 := n17049 _v _q h51
  simp only [e2585, e4306, e4307, e4311, e4312, e4313, e4314, e6676, e7836] at *
  tauto
end
end Assembly
