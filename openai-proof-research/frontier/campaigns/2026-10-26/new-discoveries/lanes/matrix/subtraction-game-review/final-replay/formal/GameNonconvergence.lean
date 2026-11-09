import GameLimits
import GameDefinition

open Finset Filter
open scoped Topology

namespace OddSubtraction

theorem model_positive_invariant {S : Finset ℕ} {a : ℕ → ℝ}
    (hm : Model S a) (hodd : ∀ k∈S,k%2=1) {D : ℕ}
    (hD : ∀ k∈S,k≤D) (n : ℕ) :
    (S.card:ℝ)≤window S (centered a) (n+D) := by
  have hrec := centered_balance hm hodd
  have hf : ∀ m, (S.card:ℝ)*centered a (m+D)=∑ k∈S,centered a (m+D-k) := by
    intro m
    have h := hrec (m+D)
    rw [eligible_full (by intro k hk; have := hD k hk; omega)] at h
    exact h
  rw [window_constant hD hf n, initial_window hD hrec]
  have h := Finset.sum_le_sum (fun k hk => odd_prefix_positive hm hodd k (hodd k hk))
  simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using h

/-- The actual uniformly randomized source game never converges for an all-odd move set. -/
theorem all_odd_game_nonconvergence (S : Finset ℕ) (hne : S.Nonempty)
    (hodd : ∀ k∈S,k%2=1) : ¬∃ L : ℝ, Tendsto (gameWin S) atTop (𝓝 L) := by
  have hpos : ∀ k∈S,0<k := by intro k hk; have := hodd k hk; omega
  rintro ⟨L,hL⟩
  exact model_not_tendsto (gameWin_model S hpos) hne hodd L hL

theorem all_odd_game_positive_invariant (S : Finset ℕ) (hodd : ∀ k∈S,k%2=1) (n : ℕ) :
    (S.card:ℝ)≤window S (centered (gameWin S)) (n+S.sup id) := by
  have hpos : ∀ k∈S,0<k := by intro k hk; have := hodd k hk; omega
  exact model_positive_invariant (gameWin_model S hpos) hodd
    (by intro k hk; exact Finset.le_sup (f := id) hk) n

end OddSubtraction
