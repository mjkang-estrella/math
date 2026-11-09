import parts.Dag168_017
import generated.th_lemma_16
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n17281 (_v : Vars) (_q : Query _v) (h196 : (e196 _v)) (h2781 : (e2781 _v)) : (e4567 _v) := by
  have p8485 := n8485 _v _q 
  have p16038 := n16038 _v _q h196 h2781
  simp only [e4567, e4568, e4572, e4573, e4574, e4575, e4956] at *
  tauto
end
end Assembly
