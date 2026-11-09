import Mathlib.Tactic
namespace AK350721
theorem tail_arithmetic (a b c d e : ℕ)
    (ha : 3 ≤ a ∧ a ≤ 7)
    (hb : 3 ≤ b ∧ b ≤ 7)
    (hc : 3 ≤ c ∧ c ≤ 7)
    (hd : 3 ≤ d ∧ d ≤ 7)
    (he : 3 ≤ e ∧ e ≤ 7)
    (hab : a ≠ b)
    (hac : a ≠ c)
    (had : a ≠ d)
    (hae : a ≠ e)
    (hbc : b ≠ c)
    (hbd : b ≠ d)
    (hbe : b ≠ e)
    (hcd : c ≠ d)
    (hce : c ≠ e)
    (hde : d ≠ e)
    (hab : a < b) (hbd : b < d) (hb4 : 4 ≤ b) (hd6 : 6 ≤ d) (hc4 : c ≤ 4) :
    (a = 3 ∧ b = 5 ∧ c = 4 ∧ d = 6 ∧ e = 7) ∨
    (a = 3 ∧ b = 5 ∧ c = 4 ∧ d = 7 ∧ e = 6) ∨
    (a = 3 ∧ b = 6 ∧ c = 4 ∧ d = 7 ∧ e = 5) ∨
    (a = 4 ∧ b = 5 ∧ c = 3 ∧ d = 6 ∧ e = 7) ∨
    (a = 4 ∧ b = 5 ∧ c = 3 ∧ d = 7 ∧ e = 6) ∨
    (a = 4 ∧ b = 6 ∧ c = 3 ∧ d = 7 ∧ e = 5) ∨
    (a = 5 ∧ b = 6 ∧ c = 3 ∧ d = 7 ∧ e = 4) ∨
    (a = 5 ∧ b = 6 ∧ c = 4 ∧ d = 7 ∧ e = 3) := by
  rcases ha with ⟨ha1, ha2⟩
  rcases hb with ⟨hb1, hb2⟩
  rcases hc with ⟨hc1, hc2⟩
  rcases hd with ⟨hd1, hd2⟩
  rcases he with ⟨he1, he2⟩
  interval_cases a <;> interval_cases b <;> norm_num at *
  all_goals interval_cases c <;> norm_num at *
  all_goals interval_cases d <;> norm_num at *
  all_goals interval_cases e <;> norm_num at *
end AK350721
