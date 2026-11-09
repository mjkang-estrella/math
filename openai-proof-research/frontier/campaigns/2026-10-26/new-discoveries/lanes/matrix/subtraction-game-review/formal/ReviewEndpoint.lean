import GameDefinition
import GameLimits

open Filter
open scoped Topology
namespace OddSubtractionReview

theorem actual_game_not_tendsto (S : Finset ℕ) (hne : S.Nonempty)
    (hodd : ∀ k ∈ S, k % 2 = 1) (L : ℝ) :
    ¬ Tendsto (OddSubtraction.gameWin S) atTop (𝓝 L) := by
  apply OddSubtraction.model_not_tendsto
    (OddSubtraction.gameWin_model S (by intro k hk; have := hodd k hk; omega))
    hne hodd L

end OddSubtractionReview
