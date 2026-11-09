import Clow371639.LexPower
import Mathlib.Data.Fin.VecNotation

/-! Positive companion facts for the rejected mutations run by the replay script. -/

namespace Clow371639

/-- Decidability of lexicographic adjacency (kernel-evaluable recursor term, no compiled code),
used only for the sanity evaluations below. -/
noncomputable instance instDecidableLexAdj (k : ℕ) : DecidableRel (lexAdj k) :=
  Nat.rec (motive := fun k => DecidableRel (lexAdj k)) (fun _ _ => instDecidableFalse)
    (fun k ih u v =>
      haveI := ih
      inferInstanceAs
        (Decidable (c5Adj (u 0) (v 0) ∨ (u 0 = v 0 ∧ lexAdj k (Fin.tail u) (Fin.tail v))))) k

example : ¬ c5Adj 0 0 := by decide
example : lexAdj 1 ![0] ![1] := by decide
example : ¬ lexAdj 1 ![0] ![2] := by decide
example : lexAdj 2 ![0, 0] ![1, 3] := by decide
example : lexAdj 2 ![0, 0] ![0, 4] := by decide
example : ¬ lexAdj 2 ![0, 0] ![2, 1] := by decide

end Clow371639
