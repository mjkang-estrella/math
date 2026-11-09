import parts.Dag168_000
import generated.th_lemma_16
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n17264 (_v : Vars) (_q : Query _v) (h2781 : (e2781 _v)) (h6423 : (e6423 _v)) : (e51 _v) := by
  have p14962 := n14962 _v _q 
  have p15999 := n15999 _v _q h2781 h6423
  simp only [e51, e52, e57, e58, e59, e60, e77] at *
  tauto
end
end Assembly
