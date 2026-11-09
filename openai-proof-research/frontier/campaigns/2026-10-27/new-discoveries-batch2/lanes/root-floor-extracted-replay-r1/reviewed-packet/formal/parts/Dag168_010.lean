import parts.Dag168_009
import generated.th_lemma_16
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n17273 (_v : Vars) (_q : Query _v) (h6571 : (e6571 _v)) : (e4491 _v) := by
  have p14969 := n14969 _v _q 
  have p17272 := n17272 _v _q h6571
  simp only [e4491, e4492, e4496, e4497, e4498, e4499, e4960] at *
  tauto
end
end Assembly
