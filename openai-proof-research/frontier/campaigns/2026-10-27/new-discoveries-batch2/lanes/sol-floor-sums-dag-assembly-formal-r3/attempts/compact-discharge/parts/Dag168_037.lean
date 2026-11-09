import parts.Dag168_036
import generated.th_lemma_16
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n17308 (_v : Vars) (_q : Query _v)  : (e17307 _v) := by
  by_contra hc
  change ¬ ((e2529 _v) ∨ (¬ (e196 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e4459 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e7493 _v)) ∨ (¬ (e4096 _v)) ∨ (e2634 _v) ∨ (¬ (e3946 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e5100 _v)) ∨ (¬ (e4903 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e3976 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e3169 _v)) ∨ (¬ (e4567 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e8045 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4724 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e4398 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e3855 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e4491 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e2125 _v))) at hc
  have h70 : (e70 _v) := by
    tauto
  have h91 : (e91 _v) := by
    tauto
  have h191 : (e191 _v) := by
    tauto
  have h196 : (e196 _v) := by
    tauto
  have h225 : (e225 _v) := by
    tauto
  have h442 : (e442 _v) := by
    tauto
  have h488 : (e488 _v) := by
    tauto
  have h2125 : (e2125 _v) := by
    tauto
  have h3069 : (e3069 _v) := by
    tauto
  have h3105 : (e3105 _v) := by
    tauto
  have h3152 : (e3152 _v) := by
    tauto
  have h3169 : (e3169 _v) := by
    tauto
  have h3855 : (e3855 _v) := by
    tauto
  have h3937 : (e3937 _v) := by
    tauto
  have h3946 : (e3946 _v) := by
    tauto
  have h3976 : (e3976 _v) := by
    tauto
  have h4059 : (e4059 _v) := by
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
  have h4369 : (e4369 _v) := by
    tauto
  have h4398 : (e4398 _v) := by
    tauto
  have h4459 : (e4459 _v) := by
    tauto
  have h4491 : (e4491 _v) := by
    tauto
  have h4567 : (e4567 _v) := by
    tauto
  have h4608 : (e4608 _v) := by
    tauto
  have h4675 : (e4675 _v) := by
    tauto
  have h4724 : (e4724 _v) := by
    tauto
  have h4747 : (e4747 _v) := by
    tauto
  have h4787 : (e4787 _v) := by
    tauto
  have h4813 : (e4813 _v) := by
    tauto
  have h4872 : (e4872 _v) := by
    tauto
  have h4903 : (e4903 _v) := by
    tauto
  have h5100 : (e5100 _v) := by
    tauto
  have h6700 : (e6700 _v) := by
    change (¬ (e2634 _v))
    tauto
  have h7493 : (e7493 _v) := by
    tauto
  have h8045 : (e8045 _v) := by
    tauto
  have h8310 : (e8310 _v) := by
    change (¬ (e2529 _v))
    tauto
  have p17186 := n17186 _v _q h70 h91 h191 h196 h225 h442 h488 h2125 h3069 h3105 h3152 h3169 h3855 h3937 h3946 h3976 h4059 h4096 h4139 h4156 h4199 h4260 h4369 h4398 h4459 h4491 h4567 h4608 h4675 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h6700 h7493 h8045 h8310
  exact p17186
end
end Assembly
