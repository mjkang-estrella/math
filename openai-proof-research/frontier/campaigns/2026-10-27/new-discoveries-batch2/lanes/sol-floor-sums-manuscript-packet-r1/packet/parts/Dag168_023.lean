import parts.Dag168_022
import generated.th_lemma_16
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n17286 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) : (e4653 _v) := by
  have p15168 := n15168 _v _q 
  have p17285 := n17285 _v _q h51
  simp only [e4653, e4654, e4658, e4659, e4660, e4661, e4939] at *
  tauto
end
end Assembly
