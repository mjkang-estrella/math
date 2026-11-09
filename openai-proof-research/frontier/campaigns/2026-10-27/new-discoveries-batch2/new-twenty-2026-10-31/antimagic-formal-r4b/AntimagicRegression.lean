import AntimagicFinal
namespace Antimagic
open Finset
/-- Direct row-incidence weights. Agreement with `weight` is still required. -/
def rowWeight (t n h i : ℕ) : ℕ :=
  (if h = 0 then 0 else label t n h i) +
  if h < n then ∑ j ∈ range t, label t n (h + 1) (t * i + j) else 0

def allLabels (t n : ℕ) : List ℕ :=
  (List.range n).flatMap fun h => (List.range (t ^ (h + 1))).map (label t n (h + 1))

def allWeights (t n : ℕ) : List ℕ :=
  (List.range (n + 1)).flatMap fun h => (List.range (t ^ h)).map (rowWeight t n h)

def rowCheck (t n : ℕ) : Prop :=
  let m := (allLabels t n).length
  (allLabels t n).Nodup ∧
  (∀ x ∈ allLabels t n, 1 ≤ x ∧ x ≤ m) ∧
  (∀ h ∈ range n, ∀ i ∈ range (t ^ (h + 1)),
    rowWeight t n h (i / t) ≠ rowWeight t n (h + 1) i) ∧
  (allWeights t n).toFinset.card = t ^ n + 1

instance (t n : ℕ) : Decidable (rowCheck t n) := by unfold rowCheck; infer_instance

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
example : rowCheck 2 1 ∧ rowCheck 2 2 ∧ rowCheck 2 3 ∧
    rowCheck 4 1 ∧ rowCheck 4 2 ∧ rowCheck 4 3 := by decide

example : ¬ Even 3 := by decide
example : ¬ ([1, 1] : List ℕ).Nodup := by decide
example : (allWeights 2 2).toFinset.card ≠ 2 ^ 2 := by decide
end Antimagic
