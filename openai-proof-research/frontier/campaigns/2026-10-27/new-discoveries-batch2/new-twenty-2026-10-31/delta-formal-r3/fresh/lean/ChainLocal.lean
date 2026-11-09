import ChainBool
namespace ChainPrefix
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
theorem fits_attachments (a b c l m : V) (hf : Fits (first a b c l m)) :
    Fits (dbl a l ++ dbl a m) := by
  intro i j
  have h := hf i j
  simp only [first, pairCount_append] at h
  rw [pairCount_append]
  omega
 theorem attachments3 : ∀ l m : V, Fits (dbl 3 l ++ dbl 3 m) →
    (l = 2 ∧ m = 6) ∨ (l = 6 ∧ m = 2) := by decide +kernel
 theorem attachments6 : ∀ l m : V, Fits (dbl 6 l ++ dbl 6 m) →
    (l = 3 ∧ m = 4) ∨ (l = 4 ∧ m = 3) := by decide +kernel
end ChainPrefix
