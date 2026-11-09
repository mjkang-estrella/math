/-
# Bunkbed start-state support (r14)

Pure base-state fact for the exact start state of `BunState`: for every `n j k`,
every window assignment `w : Asg n j` and every layer bit `sigma`, any index in
`k ∈ sval sigma (startST n j w)` must equal `j`.  The first component is the
singleton `{j}`; the second is `{j}` or empty according to the vertical bit
when `j < n`, and empty otherwise.  No recursive machinery here.
-/
import BunState

namespace Bun

/-- All indices appearing in either layer of `startST n j w` are `j`. -/
theorem startST_support (n j k : Nat) (w : Asg n j) (σ : Bool)
    (h : k ∈ sval σ (startST n j w)) : k = j := by
  cases σ with
  | false => simpa [sval, startST] using h
  | true =>
    simp only [sval, startST, reduceIte] at h
    split at h
    · split at h
      · simpa using h
      · exact absurd h (Finset.notMem_empty _)
    · exact absurd h (Finset.notMem_empty _)

end Bun
