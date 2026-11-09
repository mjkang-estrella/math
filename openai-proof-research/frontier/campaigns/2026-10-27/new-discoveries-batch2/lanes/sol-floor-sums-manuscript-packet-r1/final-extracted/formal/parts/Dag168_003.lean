import parts.Dag168_002
import generated.th_lemma_16
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n17266 (_v : Vars) (_q : Query _v) (h6571 : (e6571 _v)) : (e4731 _v) := by
  have p14698 := n14698 _v _q 
  have p14727 := n14727 _v _q h6571
  simp only [e2254, e4723, e4724, e4728, e4729, e4730, e4731, e6531, e8220] at *
  tauto
end
end Assembly
