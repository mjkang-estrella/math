import ChecksR3_0222_0
import ChecksR3_0222_1
import ChecksR3_0222_2
import ChecksR3_0222_3
namespace EdgePattern.TreeModelsR3
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem best_0222 : MaskR3.best (graph ⟨0,2,2,2⟩) = {4038} := by
  apply MaskR3.best_of_checks (graph ⟨0,2,2,2⟩) 8 {4038} (by decide) (by decide)
  have hall : ∀ b : Fin 16, MaskR3.blockCheck (graph ⟨0,2,2,2⟩) 8 {4038} (b.val * 256) 256 := by
    intro b
    fin_cases b
    · exact check_0222_0
    · exact check_0222_1
    · exact check_0222_2
    · exact check_0222_3
    · exact check_0222_4
    · exact check_0222_5
    · exact check_0222_6
    · exact check_0222_7
    · exact check_0222_8
    · exact check_0222_9
    · exact check_0222_10
    · exact check_0222_11
    · exact check_0222_12
    · exact check_0222_13
    · exact check_0222_14
    · exact check_0222_15
  intro m hm ho
  change m < 4096 at hm
  let b : Fin 16 := ⟨m / 256, by omega⟩
  let i : Fin 256 := ⟨m % 256, by omega⟩
  have he : b.val * 256 + i.val = m := by dsimp [b,i]; omega
  have h := hall b i
  rw [he] at h
  exact h ho

theorem totals_0222 : totals ⟨0,2,2,2⟩ 0 = 1 ∧ totals ⟨0,2,2,2⟩ 1 = 1 ∧ totals ⟨0,2,2,2⟩ 2 = 6 := by
  unfold totals
  rw [best_0222]
  decide
theorem count_0222 : count ⟨0,2,2,2⟩ = 1 := by
  unfold count
  rw [best_0222]
  decide
theorem bound_0222 : 1 ≤ ∑ i : Fin 3, Concrete.alpha i * occupancy ⟨0,2,2,2⟩ i := by
  simp only [Fin.sum_univ_succ]
  norm_num [Concrete.alpha, occupancy, totals_0222.1, totals_0222.2.1, totals_0222.2.2, count_0222]
end EdgePattern.TreeModelsR3
