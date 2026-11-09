import parts.Dag168_003
import generated.th_lemma_16
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n17267 (_v : Vars) (_q : Query _v) (h6571 : (e6571 _v)) : (e4724 _v) := by
  have p15518 := n15518 _v _q 
  have p17266 := n17266 _v _q h6571
  simp only [e4723, e4724, e4728, e4729, e4730, e4731, e4958] at *
  tauto
end
end Assembly
