import parts.Dag168_006
import generated.th_lemma_16
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n17270 (_v : Vars) (_q : Query _v) (h6571 : (e6571 _v)) : (e4903 _v) := by
  have p14973 := n14973 _v _q 
  have p17269 := n17269 _v _q h6571
  simp only [e4902, e4903, e4907, e4908, e4909, e4910, e4961] at *
  tauto
end
end Assembly
