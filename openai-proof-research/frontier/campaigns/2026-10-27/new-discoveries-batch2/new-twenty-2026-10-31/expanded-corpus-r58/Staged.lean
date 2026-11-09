import Defs
set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option warningAsError true
set_option synthInstance.maxSize 100000
namespace Palette
theorem staged :
  ∀ a : C, 
  ∀ b : C, 
  ∀ c : C, 
  ∀ d : C, 
  ∀ e : C, 
  ∀ f : C, (pal a b e) ≠ (pal a c f) → 
  ∀ g : C, (pal a b e) ≠ (pal a d g) ∧ (pal a c f) ≠ (pal a d g) → 
  ∀ h : C, (pal a b e) ≠ (pal b c h) ∧ (pal a b e) ≠ (pal e f h) ∧ (pal a c f) ≠ (pal b c h) ∧ (pal a c f) ≠ (pal e f h) ∧ (pal a d g) ≠ (pal b c h) ∧ (pal a d g) ≠ (pal e f h) ∧ (pal b c h) ≠ (pal e f h) → 
  ∀ i : C, (pal a b e) ≠ (pal b d i) ∧ (pal a b e) ≠ (pal e g i) ∧ (pal a c f) ≠ (pal b d i) ∧ (pal a c f) ≠ (pal e g i) ∧ (pal a d g) ≠ (pal b d i) ∧ (pal a d g) ≠ (pal e g i) ∧ (pal b c h) ≠ (pal b d i) ∧ (pal b c h) ≠ (pal e g i) ∧ (pal b d i) ≠ (pal e f h) ∧ (pal b d i) ≠ (pal e g i) ∧ (pal e f h) ≠ (pal e g i) → 
  ∀ j : C, (pal a b e) ≠ (pal c d j) ∧ (pal a b e) ≠ (pal f g j) ∧ (pal a b e) ≠ (pal h i j) ∧ (pal a c f) ≠ (pal c d j) ∧ (pal a c f) ≠ (pal f g j) ∧ (pal a c f) ≠ (pal h i j) ∧ (pal a d g) ≠ (pal c d j) ∧ (pal a d g) ≠ (pal f g j) ∧ (pal a d g) ≠ (pal h i j) ∧ (pal b c h) ≠ (pal c d j) ∧ (pal b c h) ≠ (pal f g j) ∧ (pal b c h) ≠ (pal h i j) ∧ (pal b d i) ≠ (pal c d j) ∧ (pal b d i) ≠ (pal f g j) ∧ (pal b d i) ≠ (pal h i j) ∧ (pal c d j) ≠ (pal e f h) ∧ (pal c d j) ≠ (pal e g i) ∧ (pal c d j) ≠ (pal f g j) ∧ (pal c d j) ≠ (pal h i j) ∧ (pal e f h) ≠ (pal f g j) ∧ (pal e f h) ≠ (pal h i j) ∧ (pal e g i) ≠ (pal f g j) ∧ (pal e g i) ≠ (pal h i j) ∧ (pal f g j) ≠ (pal h i j) → False := by decide
end Palette
