import parts.Dag168_008
import generated.th_lemma_16
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n17272 (_v : Vars) (_q : Query _v) (h6571 : (e6571 _v)) : (e4499 _v) := by
  have p14700 := n14700 _v _q 
  have p17271 := n17271 _v _q h6571
  simp only [e2697, e4491, e4492, e4496, e4497, e4498, e4499, e6732, e7998] at *
  tauto
end
end Assembly
