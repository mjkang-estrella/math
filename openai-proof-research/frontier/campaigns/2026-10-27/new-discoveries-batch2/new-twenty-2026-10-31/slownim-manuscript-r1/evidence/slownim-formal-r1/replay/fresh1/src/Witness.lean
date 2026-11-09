import Play
namespace SlowNim360653
def x0 : Pos 3 := ![4,4,5]
def baseline : Profile 3 3 := GMProfile (by decide) 3
def deviation : Strategy 3 where
  choose x := if x = x0 then 1 else gm (by decide) 3 x
  valid x h := by
    split
    · rename_i he
      subst x
      intro j hj
      fin_cases j <;> norm_num [x0]
    · exact gm_legal (by decide) 3 x h
def deviated : Profile 3 3 := replace baseline 0 deviation

theorem baseline_length : length (by decide) baseline x0 = 6 := by decide
theorem deviated_length : length (by decide) deviated x0 = 5 := by decide

theorem witness_payoffs : payoff (by decide) baseline x0 7 0 = -1 ∧
    payoff (by decide) deviated x0 7 0 = 1 := by
  norm_num [payoff, loser, baseline_length, deviated_length]
theorem seven_admissible : Admissible (l := 3) (by decide) x0 7 := by
  intro s
  have h := length_bound (by decide : 2 ≤ 3) (by decide : 2 ≤ 3) s x0
  have hm : mass x0 = 13 := by decide
  rw [hm] at h
  norm_num at h
  exact_mod_cast (show length (by decide) s x0 < 7 by omega)
-- This is a legal positional deviation, hence also an admissible deviation
-- in any strategy class permitting dependence on the entire history.
theorem witness_not_nash : ¬ IsNash (by decide) x0 7 baseline := by
  intro h
  have hp := h 0 deviation
  change payoff (by decide) deviated x0 7 0 ≤ payoff (by decide) baseline x0 7 0 at hp
  rw [witness_payoffs.1, witness_payoffs.2] at hp
  norm_num at hp
theorem conjecture1_false : ¬ Conjecture := by
  intro h
  exact witness_not_nash (h 3 (by decide) 3 (by decide) x0 7 seven_admissible)
end SlowNim360653
