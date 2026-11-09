import ChecksR3_0020_0
namespace EdgePattern.TreeModelsR3
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem best_0020 : MaskR3.best (graph ⟨0,0,2,0⟩) = {206,236} := by
  apply MaskR3.best_of_checks (graph ⟨0,0,2,0⟩) 5 {206,236} (by decide) (by decide)
  have hall : ∀ b : Fin 1, MaskR3.blockCheck (graph ⟨0,0,2,0⟩) 5 {206,236} (b.val * 256) 256 := by
    intro b
    fin_cases b
    · exact check_0020_0
  intro m hm ho
  change m < 256 at hm
  let b : Fin 1 := ⟨m / 256, by omega⟩
  let i : Fin 256 := ⟨m % 256, by omega⟩
  have he : b.val * 256 + i.val = m := by dsimp [b,i]; omega
  have h := hall b i
  rw [he] at h
  exact h ho

theorem totals_0020 : totals ⟨0,0,2,0⟩ 0 = 1 ∧ totals ⟨0,0,2,0⟩ 1 = 5 ∧ totals ⟨0,0,2,0⟩ 2 = 4 := by
  unfold totals
  rw [best_0020]
  decide
theorem count_0020 : count ⟨0,0,2,0⟩ = 2 := by
  unfold count
  rw [best_0020]
  decide
theorem bound_0020 : 1 ≤ ∑ i : Fin 3, Concrete.alpha i * occupancy ⟨0,0,2,0⟩ i := by
  simp only [Fin.sum_univ_succ]
  norm_num [Concrete.alpha, occupancy, totals_0020.1, totals_0020.2.1, totals_0020.2.2, count_0020]
end EdgePattern.TreeModelsR3
