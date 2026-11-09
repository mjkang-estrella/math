/-
# BunFinalModel — token/outcome counts and the uniform probability form

* `Bun.card_token : Fintype.card (Bun.Token n) = n * n` — the model has `n(n-1)`
  horizontal tokens (two layers per transitive arc) plus `n` bidirectional vertical
  tokens, i.e. the source's `n(n-1) + n` tokens.
* `Bun.card_out : Fintype.card (Bun.Out n) = 2 ^ (n * n)` — the outcome space is the
  uniform Boolean cube on those tokens.
* `Bun.prob_layer_true_le_false` — the probability form of the bunkbed inequality:
  both layer counts divided by `2 ^ (n * n)` satisfy the inequality.
-/
import BunFinalEndpoint
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.GroupWithZero.Basic

namespace Bun

open Classical

/-- Strict ordered pairs of indices are the sigma of lower indices. -/
noncomputable def pairLtEquiv (n : Nat) :
    {p : Fin n × Fin n // (p.1 : Nat) < (p.2 : Nat)} ≃ Σ j : Fin n, Fin (j : Nat) where
  toFun p := ⟨p.1.2, ⟨p.1.1, p.2⟩⟩
  invFun s := ⟨(⟨s.2.val, s.2.isLt.trans s.1.isLt⟩, s.1), s.2.isLt⟩
  left_inv p := by
    obtain ⟨⟨i, j⟩, h⟩ := p
    rfl
  right_inv s := by
    obtain ⟨j, i⟩ := s
    rfl

/-- The number of ordered pairs `i < j` is `∑_{i<n} i`. -/
theorem card_pairLt (n : Nat) :
    Fintype.card {p : Fin n × Fin n // (p.1 : Nat) < (p.2 : Nat)} =
      ∑ i ∈ Finset.range n, i := by
  rw [Fintype.card_congr (pairLtEquiv n), Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) n]

/-- Two layers per transitive arc: `n(n-1)` horizontal tokens. -/
theorem card_htoken (n : Nat) : Fintype.card (HToken n) = n * (n - 1) := by
  rw [Fintype.card_congr (htokenEquiv n), Fintype.card_prod, Fintype.card_bool,
    card_pairLt, Finset.sum_range_id_mul_two]

/-- **Token count.**  `n(n-1)` horizontal tokens plus `n` vertical tokens. -/
theorem card_token (n : Nat) : Fintype.card (Token n) = n * n := by
  change Fintype.card (HToken n ⊕ Fin n) = n * n
  rw [Fintype.card_sum, card_htoken, Fintype.card_fin]
  cases n with
  | zero => simp
  | succ m =>
      rw [Nat.succ_sub_one, Nat.mul_succ]

/-- **Outcome count.**  The uniform Boolean cube on `n * n` tokens. -/
theorem card_out (n : Nat) : Fintype.card (Out n) = 2 ^ (n * n) := by
  classical
  change Fintype.card (Token n → Bool) = 2 ^ (n * n)
  rw [Fintype.card_fun, Fintype.card_bool, card_token]

/-- **Probability form** of the bunkbed inequality in the uniform model:
the true-layer probability is at most the false-layer probability. -/
theorem prob_layer_true_le_false (n : Nat) (u v : Fin n) :
    ((Fintype.card {ω : Out n // Reach n ω (u, false) (v, true)} : ℚ) / 2 ^ (n * n)) ≤
    ((Fintype.card {ω : Out n // Reach n ω (u, false) (v, false)} : ℚ) / 2 ^ (n * n)) := by
  classical
  have h := bunkbed_E7_transitive n u v
  have hq : ((Fintype.card {ω : Out n // Reach n ω (u, false) (v, true)} : ℚ)) ≤
      ((Fintype.card {ω : Out n // Reach n ω (u, false) (v, false)} : ℚ)) := by
    exact_mod_cast h
  have hpos : (0 : ℚ) < 2 ^ (n * n) := by positivity
  exact (div_le_div_iff_of_pos_right hpos).mpr hq

end Bun
