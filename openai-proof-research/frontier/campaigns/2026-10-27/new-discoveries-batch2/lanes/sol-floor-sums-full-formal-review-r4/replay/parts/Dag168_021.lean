import parts.Dag168_020
import generated.th_lemma_16
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n17284 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) : (e2364 _v) := by
  have p11343 := n11343 _v _q 
  have p17049 := n17049 _v _q h51
  simp only [e2364, e2585, e6676, e11342] at *
  tauto
end
end Assembly
