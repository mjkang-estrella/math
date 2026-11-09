import parts.Dag168_027
import generated.th_lemma_16
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n17292 (_v : Vars) (_q : Query _v)  : (e2805 _v) := by
  by_contra hc
  change ¬ (e2805 _v) at hc
  have h6792 : (e6792 _v) := by
    change (¬ (e2805 _v))
    tauto
  have p17152 := n17152 _v _q h6792
  exact p17152
end
end Assembly
