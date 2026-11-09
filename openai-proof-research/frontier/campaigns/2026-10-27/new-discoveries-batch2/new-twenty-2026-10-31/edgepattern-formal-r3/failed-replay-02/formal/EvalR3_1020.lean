import ChecksR3_1020_0
namespace EdgePattern.TreeModelsR3
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem best_1020 : MaskR3.best (graph ⟨1,0,2,0⟩) = {398,428,458,481,488} := by
  apply MaskR3.best_of_checks (graph ⟨1,0,2,0⟩) 5 {398,428,458,481,488} (by decide) (by decide)
  have hall : ∀ b : Fin 2, MaskR3.blockCheck (graph ⟨1,0,2,0⟩) 5 {398,428,458,481,488} (b.val * 256) 256 := by
    intro b
    fin_cases b
    · exact check_1020_0
    · exact check_1020_1
  intro m hm ho
  change m < 512 at hm
  let b : Fin 2 := ⟨m / 256, by omega⟩
  let i : Fin 256 := ⟨m % 256, by omega⟩
  have he : b.val * 256 + i.val = m := by dsimp [b,i]; omega
  have h := hall b i
  rw [he] at h
  exact h ho

theorem totals_1020 : totals ⟨1,0,2,0⟩ 0 = 3 ∧ totals ⟨1,0,2,0⟩ 1 = 9 ∧ totals ⟨1,0,2,0⟩ 2 = 13 := by
  unfold totals
  rw [best_1020]
  decide
theorem count_1020 : count ⟨1,0,2,0⟩ = 5 := by
  unfold count
  rw [best_1020]
  decide
theorem bound_1020 : 1 ≤ ∑ i : Fin 3, Concrete.alpha i * occupancy ⟨1,0,2,0⟩ i := by
  simp only [Fin.sum_univ_succ]
  norm_num [Concrete.alpha, occupancy, totals_1020.1, totals_1020.2.1, totals_1020.2.2, count_1020]
end EdgePattern.TreeModelsR3
