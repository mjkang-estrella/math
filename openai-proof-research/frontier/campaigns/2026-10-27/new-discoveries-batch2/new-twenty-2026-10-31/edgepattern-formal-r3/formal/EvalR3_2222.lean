import ChecksR3_2222_0
import ChecksR3_2222_1
import ChecksR3_2222_2
import ChecksR3_2222_3
import ChecksR3_2222_4
import ChecksR3_2222_5
import ChecksR3_2222_6
import ChecksR3_2222_7
import ChecksR3_2222_8
import ChecksR3_2222_9
import ChecksR3_2222_10
import ChecksR3_2222_11
import ChecksR3_2222_12
import ChecksR3_2222_13
import ChecksR3_2222_14
import ChecksR3_2222_15
namespace EdgePattern.TreeModelsR3
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem best_2222 : MaskR3.best (graph ⟨2,2,2,2⟩) = {16321,16322} := by
  apply MaskR3.best_of_checks (graph ⟨2,2,2,2⟩) 9 {16321,16322} (by decide) (by decide)
  have hall : ∀ b : Fin 64, MaskR3.blockCheck (graph ⟨2,2,2,2⟩) 9 {16321,16322} (b.val * 256) 256 := by
    intro b
    fin_cases b
    · exact check_2222_0
    · exact check_2222_1
    · exact check_2222_2
    · exact check_2222_3
    · exact check_2222_4
    · exact check_2222_5
    · exact check_2222_6
    · exact check_2222_7
    · exact check_2222_8
    · exact check_2222_9
    · exact check_2222_10
    · exact check_2222_11
    · exact check_2222_12
    · exact check_2222_13
    · exact check_2222_14
    · exact check_2222_15
    · exact check_2222_16
    · exact check_2222_17
    · exact check_2222_18
    · exact check_2222_19
    · exact check_2222_20
    · exact check_2222_21
    · exact check_2222_22
    · exact check_2222_23
    · exact check_2222_24
    · exact check_2222_25
    · exact check_2222_26
    · exact check_2222_27
    · exact check_2222_28
    · exact check_2222_29
    · exact check_2222_30
    · exact check_2222_31
    · exact check_2222_32
    · exact check_2222_33
    · exact check_2222_34
    · exact check_2222_35
    · exact check_2222_36
    · exact check_2222_37
    · exact check_2222_38
    · exact check_2222_39
    · exact check_2222_40
    · exact check_2222_41
    · exact check_2222_42
    · exact check_2222_43
    · exact check_2222_44
    · exact check_2222_45
    · exact check_2222_46
    · exact check_2222_47
    · exact check_2222_48
    · exact check_2222_49
    · exact check_2222_50
    · exact check_2222_51
    · exact check_2222_52
    · exact check_2222_53
    · exact check_2222_54
    · exact check_2222_55
    · exact check_2222_56
    · exact check_2222_57
    · exact check_2222_58
    · exact check_2222_59
    · exact check_2222_60
    · exact check_2222_61
    · exact check_2222_62
    · exact check_2222_63
  intro m hm ho
  change m < 16384 at hm
  let b : Fin 64 := ⟨m / 256, by omega⟩
  let i : Fin 256 := ⟨m % 256, by omega⟩
  have he : b.val * 256 + i.val = m := by dsimp [b,i]; omega
  have h := hall b i
  rw [he] at h
  exact h ho

theorem totals_2222 : totals ⟨2,2,2,2⟩ 0 = 2 ∧ totals ⟨2,2,2,2⟩ 1 = 0 ∧ totals ⟨2,2,2,2⟩ 2 = 16 := by
  unfold totals
  rw [best_2222]
  decide
theorem count_2222 : count ⟨2,2,2,2⟩ = 2 := by
  unfold count
  rw [best_2222]
  decide
theorem bound_2222 : 1 ≤ ∑ i : Fin 3, Concrete.alpha i * occupancy ⟨2,2,2,2⟩ i := by
  simp only [Fin.sum_univ_succ]
  norm_num [Concrete.alpha, occupancy, totals_2222.1, totals_2222.2.1, totals_2222.2.2, count_2222]
end EdgePattern.TreeModelsR3
