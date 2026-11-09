import parts.Dag168_038
import generated.th_lemma_16
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n17312 (_v : Vars) (_q : Query _v)  : (e17311 _v) := by
  by_contra hc
  change ¬ ((e2585 _v) ∨ (¬ (e4838 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e4369 _v)) ∨ (e2475 _v) ∨ (¬ (e7606 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4477 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e4903 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e3976 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e3169 _v)) ∨ (¬ (e4567 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e4608 _v)) ∨ (e2358 _v) ∨ (¬ (e2536 _v))) at hc
  have h70 : (e70 _v) := by
    tauto
  have h91 : (e91 _v) := by
    tauto
  have h191 : (e191 _v) := by
    tauto
  have h225 : (e225 _v) := by
    tauto
  have h442 : (e442 _v) := by
    tauto
  have h488 : (e488 _v) := by
    tauto
  have h2536 : (e2536 _v) := by
    tauto
  have h3069 : (e3069 _v) := by
    tauto
  have h3105 : (e3105 _v) := by
    tauto
  have h3152 : (e3152 _v) := by
    tauto
  have h3169 : (e3169 _v) := by
    tauto
  have h3937 : (e3937 _v) := by
    tauto
  have h3976 : (e3976 _v) := by
    tauto
  have h4096 : (e4096 _v) := by
    tauto
  have h4156 : (e4156 _v) := by
    tauto
  have h4199 : (e4199 _v) := by
    tauto
  have h4260 : (e4260 _v) := by
    tauto
  have h4369 : (e4369 _v) := by
    tauto
  have h4434 : (e4434 _v) := by
    tauto
  have h4477 : (e4477 _v) := by
    tauto
  have h4567 : (e4567 _v) := by
    tauto
  have h4608 : (e4608 _v) := by
    tauto
  have h4675 : (e4675 _v) := by
    tauto
  have h4787 : (e4787 _v) := by
    tauto
  have h4813 : (e4813 _v) := by
    tauto
  have h4838 : (e4838 _v) := by
    tauto
  have h4872 : (e4872 _v) := by
    tauto
  have h4903 : (e4903 _v) := by
    tauto
  have h6571 : (e6571 _v) := by
    change (¬ (e2358 _v))
    tauto
  have h6676 : (e6676 _v) := by
    change (¬ (e2585 _v))
    tauto
  have h7606 : (e7606 _v) := by
    tauto
  have h8038 : (e8038 _v) := by
    change (¬ (e2475 _v))
    tauto
  have p17190 := n17190 _v _q h70 h91 h191 h225 h442 h488 h2536 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4434 h4477 h4567 h4608 h4675 h4787 h4813 h4838 h4872 h4903 h6571 h6676 h7606 h8038
  exact p17190
end
end Assembly
