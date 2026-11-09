import Dag167
import generated.th_lemma_16
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n17263 (_v : Vars) (_q : Query _v) (h2781 : (e2781 _v)) (h6423 : (e6423 _v)) : (e5145 _v) := by
  have p15925 := n15925 _v _q 
  have p15997 := n15997 _v _q h2781 h6423
  simp only [e5143, e5145, e5147, e5148, e5149, e5150, e5152] at *
  tauto
end
end Assembly
