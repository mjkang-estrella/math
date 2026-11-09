import parts.Dag168_032
import generated.th_lemma_16
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n17300 (_v : Vars) (_q : Query _v)  : (e17299 _v) := by
  by_contra hc
  change ¬ ((¬ (e2787 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e4434 _v)) ∨ (e2740 _v) ∨ (¬ (e4306 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e3271 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4477 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e3566 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e4903 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e3976 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e3169 _v)) ∨ (¬ (e4567 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4156 _v)) ∨ (e2475 _v)) at hc
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
  have h2787 : (e2787 _v) := by
    tauto
  have h3069 : (e3069 _v) := by
    tauto
  have h3105 : (e3105 _v) := by
    tauto
  have h3152 : (e3152 _v) := by
    tauto
  have h3169 : (e3169 _v) := by
    tauto
  have h3271 : (e3271 _v) := by
    tauto
  have h3566 : (e3566 _v) := by
    tauto
  have h3937 : (e3937 _v) := by
    tauto
  have h3976 : (e3976 _v) := by
    tauto
  have h4096 : (e4096 _v) := by
    tauto
  have h4139 : (e4139 _v) := by
    tauto
  have h4156 : (e4156 _v) := by
    tauto
  have h4199 : (e4199 _v) := by
    tauto
  have h4260 : (e4260 _v) := by
    tauto
  have h4306 : (e4306 _v) := by
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
  have h4653 : (e4653 _v) := by
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
  have h6746 : (e6746 _v) := by
    change (¬ (e2740 _v))
    tauto
  have h8038 : (e8038 _v) := by
    change (¬ (e2475 _v))
    tauto
  have p17171 := n17171 _v _q h70 h91 h191 h225 h442 h488 h2787 h3069 h3105 h3152 h3169 h3271 h3566 h3937 h3976 h4096 h4139 h4156 h4199 h4260 h4306 h4369 h4434 h4477 h4567 h4608 h4653 h4675 h4787 h4813 h4838 h4872 h4903 h6746 h8038
  exact p17171
end
end Assembly
