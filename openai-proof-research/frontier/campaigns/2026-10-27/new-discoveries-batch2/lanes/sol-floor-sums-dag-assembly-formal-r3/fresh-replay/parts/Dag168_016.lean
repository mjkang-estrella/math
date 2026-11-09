import parts.Dag168_015
import generated.th_lemma_16
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n17279 (_v : Vars) (_q : Query _v) (h2781 : (e2781 _v)) : (e51 _v) := by
  have p14962 := n14962 _v _q 
  have p16024 := n16024 _v _q h2781
  simp only [e51, e52, e57, e58, e59, e60, e77] at *
  tauto
end
end Assembly
