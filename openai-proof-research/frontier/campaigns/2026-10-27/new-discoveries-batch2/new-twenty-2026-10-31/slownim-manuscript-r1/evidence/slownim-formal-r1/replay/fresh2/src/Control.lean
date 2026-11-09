import Play
namespace SlowNim360653
lemma two_terminal_mass (x : Pos 2) (h : Terminal x) : mass x = 0 := by
  obtain ⟨i,j,he,hi,hj⟩ := h
  fin_cases i <;> fin_cases j <;> simp_all [mass, Fin.sum_univ_succ]
lemma two_run {l} (hl : 2 ≤ l) (s : Profile 2 l) (k) (x : Pos 2) (t)
    (hk : mass x < k) : run hl s k x t = mass x := by
  induction k generalizing x t with
  | zero => omega
  | succ k ih =>
    rw [run_succ]
    split
    · rename_i h; exact (two_terminal_mass x h).symm
    · rename_i h
      have hm := mass_move x ((s ⟨t % l, Nat.mod_lt _ (by omega)⟩).choose x) ((s _).valid x h)
      have hm' : mass (move x ((s ⟨t % l, Nat.mod_lt _ (by omega)⟩).choose x)) + 1 = mass x := by simpa using hm
      rw [ih _ _ (by omega)]
      omega
theorem two_length {l} (hl : 2 ≤ l) (s : Profile 2 l) (x : Pos 2) :
    length hl s x = mass x := two_run hl s _ x 0 (by omega)
theorem two_every_profile_nash {l} (hl : 2 ≤ l) (s : Profile 2 l) (x : Pos 2) (C : ℚ) :
    IsNash hl x C s := by
  intro p d
  simp only [payoff, loser, two_length]
  exact le_rfl
end SlowNim360653
