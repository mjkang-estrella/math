import parts.Dag168_001
import generated.th_lemma_16
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n17265 (_v : Vars) (_q : Query _v) (h2781 : (e2781 _v)) (h6423 : (e6423 _v)) : (e5237 _v) := by
  have p8682 := n8682 _v _q 
  have p16001 := n16001 _v _q h2781 h6423
  simp only [e5237, e5240, e5247, e5248, e5249, e5250, e5252] at *
  tauto
end
end Assembly
