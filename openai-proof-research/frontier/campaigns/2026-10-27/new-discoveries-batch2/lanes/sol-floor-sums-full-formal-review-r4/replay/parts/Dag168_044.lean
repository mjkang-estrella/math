import parts.Dag168_043
import generated.th_lemma_16
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n17320 (_v : Vars) (_q : Query _v) (h2740 : (e2740 _v)) (h6423 : (e6423 _v)) : (e2787 _v) := by
  have p8663 := n8663 _v _q 
  have p11426 := n11426 _v _q h2740
  have p8452 := n8452 _v _q h6423
  exact FloorCertificate.node_17320 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8663 p11426 p8452
end
end Assembly
