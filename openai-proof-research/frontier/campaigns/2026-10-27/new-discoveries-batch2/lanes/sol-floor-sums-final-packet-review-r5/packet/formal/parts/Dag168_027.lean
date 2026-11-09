import parts.Dag168_026
import generated.th_lemma_16
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n17291 (_v : Vars) (_q : Query _v)  : (e17290 _v) := by
  by_contra hc
  change ¬ ((¬ (e4439 _v)) ∨ (¬ (e4459 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e4791 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e3133 _v)) ∨ (¬ (e4101 _v)) ∨ (¬ (e3158 _v)) ∨ (¬ (e4679 _v)) ∨ (¬ (e3976 _v)) ∨ (¬ (e3919 _v)) ∨ (¬ (e4161 _v)) ∨ (¬ (e467 _v)) ∨ (¬ (e4373 _v)) ∨ (¬ (e4817 _v)) ∨ (¬ (e4724 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4264 _v)) ∨ (¬ (e3051 _v)) ∨ (¬ (e4491 _v)) ∨ (¬ (e4903 _v)) ∨ (¬ (e4398 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4877 _v)) ∨ (¬ (e3109 _v)) ∨ (¬ (e4567 _v))) at hc
  have h51 : (e51 _v) := by
    tauto
  have h467 : (e467 _v) := by
    tauto
  have h3051 : (e3051 _v) := by
    tauto
  have h3109 : (e3109 _v) := by
    tauto
  have h3133 : (e3133 _v) := by
    tauto
  have h3158 : (e3158 _v) := by
    tauto
  have h3919 : (e3919 _v) := by
    tauto
  have h3946 : (e3946 _v) := by
    tauto
  have h3976 : (e3976 _v) := by
    tauto
  have h4059 : (e4059 _v) := by
    tauto
  have h4101 : (e4101 _v) := by
    tauto
  have h4161 : (e4161 _v) := by
    tauto
  have h4264 : (e4264 _v) := by
    tauto
  have h4306 : (e4306 _v) := by
    tauto
  have h4373 : (e4373 _v) := by
    tauto
  have h4398 : (e4398 _v) := by
    tauto
  have h4439 : (e4439 _v) := by
    tauto
  have h4459 : (e4459 _v) := by
    tauto
  have h4491 : (e4491 _v) := by
    tauto
  have h4567 : (e4567 _v) := by
    tauto
  have h4653 : (e4653 _v) := by
    tauto
  have h4679 : (e4679 _v) := by
    tauto
  have h4724 : (e4724 _v) := by
    tauto
  have h4747 : (e4747 _v) := by
    tauto
  have h4791 : (e4791 _v) := by
    tauto
  have h4817 : (e4817 _v) := by
    tauto
  have h4877 : (e4877 _v) := by
    tauto
  have h4903 : (e4903 _v) := by
    tauto
  have p17144 := n17144 _v _q h51 h467 h3051 h3109 h3133 h3158 h3919 h3946 h3976 h4059 h4101 h4161 h4264 h4306 h4373 h4398 h4439 h4459 h4491 h4567 h4653 h4679 h4724 h4747 h4791 h4817 h4877 h4903
  exact p17144
end
end Assembly
