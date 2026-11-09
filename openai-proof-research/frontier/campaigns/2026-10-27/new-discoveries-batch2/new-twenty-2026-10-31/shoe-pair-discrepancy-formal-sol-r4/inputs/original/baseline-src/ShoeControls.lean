import ShoeTermination

namespace Shoe

/-- Nonvacuity: a constant sample really stops and returns its sole color. -/
theorem constant_sample_wins (i : ℕ) : winner (fun _ => i) = i :=
  winner_first_pair rfl

/-- An odd chronological arrival can win. A simultaneous-pair replacement
would not report the match at this prefix of length three. -/
theorem odd_arrival_control (ω : Sample ℕ) (h01 : ω 0 ≠ ω 1)
    (h21 : ω 2 = ω 1) : FirstMatch ω 2 ∧ winner ω = ω 2 := by
  have hf : FirstMatch ω 2 := by
    constructor
    · exact ⟨1,0,by omega,by omega,h21⟩
    · rintro ⟨a,b,ha,hb,he⟩
      have hA : a = 0 := by omega
      have hB : b = 0 := by omega
      subst a
      subst b
      exact h01 he
  exact ⟨hf,winner_at_first hf⟩

end Shoe
