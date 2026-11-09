import ChecksR3_2000_0
namespace EdgePattern.TreeModelsR3
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem best_2000 : MaskR3.best (graph ⟨2,0,0,0⟩) = {241,248} := by
  apply MaskR3.best_of_checks (graph ⟨2,0,0,0⟩) 5 {241,248} (by decide) (by decide)
  have hall : ∀ b : Fin 1, MaskR3.blockCheck (graph ⟨2,0,0,0⟩) 5 {241,248} (b.val * 256) 256 := by
    intro b
    fin_cases b
    · exact check_2000_0
  intro m hm ho
  change m < 256 at hm
  let b : Fin 1 := ⟨m / 256, by omega⟩
  let i : Fin 256 := ⟨m % 256, by omega⟩
  have he : b.val * 256 + i.val = m := by dsimp [b,i]; omega
  have h := hall b i
  rw [he] at h
  exact h ho

theorem totals_2000 : totals ⟨2,0,0,0⟩ 0 = 1 ∧ totals ⟨2,0,0,0⟩ 1 = 5 ∧ totals ⟨2,0,0,0⟩ 2 = 4 := by
  unfold totals
  rw [best_2000]
  decide
theorem count_2000 : count ⟨2,0,0,0⟩ = 2 := by
  unfold count
  rw [best_2000]
  decide
theorem bound_2000 : 1 ≤ ∑ i : Fin 3, Concrete.alpha i * occupancy ⟨2,0,0,0⟩ i := by
  simp only [Fin.sum_univ_succ]
  norm_num [Concrete.alpha, occupancy, totals_2000.1, totals_2000.2.1, totals_2000.2.2, count_2000]
end EdgePattern.TreeModelsR3
