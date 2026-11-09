import parts.Dag168_004
import generated.th_lemma_16
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n17268 (_v : Vars) (_q : Query _v) (h2781 : (e2781 _v)) (h6423 : (e6423 _v)) : (e4101 _v) := by
  have p14929 := n14929 _v _q 
  have p16005 := n16005 _v _q h2781 h6423
  simp only [e4101, e4102, e4106, e4107, e4108, e4109, e4952] at *
  tauto
end
end Assembly
