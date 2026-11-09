import parts.Dag168_014
import generated.th_lemma_16
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n17278 (_v : Vars) (_q : Query _v) (h2781 : (e2781 _v)) : (e4398 _v) := by
  have p14976 := n14976 _v _q 
  have p16022 := n16022 _v _q h2781
  simp only [e4397, e4398, e4402, e4403, e4404, e4405, e4962] at *
  tauto
end
end Assembly
