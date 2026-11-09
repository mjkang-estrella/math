import CountR7TCyclic
import CountR7TSum
noncomputable section
open scoped BigOperators
namespace ChanLevine.Round7T
open Round3 Round6 Polynomial

theorem orderedProduct_congr_prefix {M : Type*} [Monoid M]
    (a b : ℕ → M) (r : ℕ) (h : ∀ k < r, a k = b k) :
    orderedProduct a r = orderedProduct b r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [orderedProduct_succ, orderedProduct_succ,
      ih (fun k hk => h k (by omega)), h r (by omega)]

theorem trace_matchingNumerator {F : Type*} [Field F]
    (n : ℕ) [NeZero n] (z : F) :
    (transferProduct z n).trace = matchingNumerator n z := by
  obtain ⟨r,hr⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  subst n
  let B : ZMod (r+1) → Matrix (Fin 2) (Fin 2) (Polynomial F) :=
    fun k => dominoMatrix (Polynomial.C z) (1-X*Polynomial.C (z^k.val))
  have hp : transferProduct z (r+1) =
      orderedProduct (fun k : ℕ => B (k : ZMod (r+1))) (r+1) := by
    apply orderedProduct_congr_prefix
    intro k hk
    simp only [B, transferFactor, ZMod.val_natCast_of_lt hk]
  rw [hp, trace_zmod_words]
  exact sum_words_numerator z

/-- The assigned round-7t target, without residual hypotheses. -/
theorem matchingTraceExpansion : MatchingTraceExpansion := by
  intro n inst hn k
  exact trace_matchingNumerator n (frequencyRoot n k)
end ChanLevine.Round7T
