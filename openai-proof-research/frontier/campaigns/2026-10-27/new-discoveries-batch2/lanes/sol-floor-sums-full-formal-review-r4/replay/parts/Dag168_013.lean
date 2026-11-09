import parts.Dag168_012
import generated.th_lemma_16
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n17276 (_v : Vars) (_q : Query _v) (h5195 : (e5195 _v)) : (e8317 _v) := by
  have p11541 := n11541 _v _q 
  have p15935 := n15935 _v _q h5195
  simp only [e8315, e8317, e8319, e8320, e8321, e8322, e8491] at *
  tauto
end
end Assembly
