import Cases0
import Cases1
import Cases2
import Cases3
import Cases4
import Cases5
import Cases6
import Cases7
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace CommonBasis332371
theorem exchange_checked : ∀ a ∈ bases, ∀ b ∈ bases,
    ∀ e ∈ a \ b, ∃ f ∈ b \ a, insert f (a.erase e) ∈ bases := by
  intro a ha
  simp only [bases, List.mem_toFinset, baseList, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · intro b hb
    exact of_decide_eq_true ((List.all_eq_true.mp check_0) b (by simpa [bases] using hb))
  · intro b hb
    exact of_decide_eq_true ((List.all_eq_true.mp check_1) b (by simpa [bases] using hb))
  · intro b hb
    exact of_decide_eq_true ((List.all_eq_true.mp check_2) b (by simpa [bases] using hb))
  · intro b hb
    exact of_decide_eq_true ((List.all_eq_true.mp check_3) b (by simpa [bases] using hb))
  · intro b hb
    exact of_decide_eq_true ((List.all_eq_true.mp check_4) b (by simpa [bases] using hb))
  · intro b hb
    exact of_decide_eq_true ((List.all_eq_true.mp check_5) b (by simpa [bases] using hb))
  · intro b hb
    exact of_decide_eq_true ((List.all_eq_true.mp check_6) b (by simpa [bases] using hb))
  · intro b hb
    exact of_decide_eq_true ((List.all_eq_true.mp check_7) b (by simpa [bases] using hb))
  · intro b hb
    exact of_decide_eq_true ((List.all_eq_true.mp check_8) b (by simpa [bases] using hb))
  · intro b hb
    exact of_decide_eq_true ((List.all_eq_true.mp check_9) b (by simpa [bases] using hb))
  · intro b hb
    exact of_decide_eq_true ((List.all_eq_true.mp check_10) b (by simpa [bases] using hb))
  · intro b hb
    exact of_decide_eq_true ((List.all_eq_true.mp check_11) b (by simpa [bases] using hb))
  · intro b hb
    exact of_decide_eq_true ((List.all_eq_true.mp check_12) b (by simpa [bases] using hb))
  · intro b hb
    exact of_decide_eq_true ((List.all_eq_true.mp check_13) b (by simpa [bases] using hb))
  · intro b hb
    exact of_decide_eq_true ((List.all_eq_true.mp check_14) b (by simpa [bases] using hb))
  · intro b hb
    exact of_decide_eq_true ((List.all_eq_true.mp check_15) b (by simpa [bases] using hb))
  · intro b hb
    exact of_decide_eq_true ((List.all_eq_true.mp check_16) b (by simpa [bases] using hb))
  · intro b hb
    exact of_decide_eq_true ((List.all_eq_true.mp check_17) b (by simpa [bases] using hb))
  · intro b hb
    exact of_decide_eq_true ((List.all_eq_true.mp check_18) b (by simpa [bases] using hb))
  · intro b hb
    exact of_decide_eq_true ((List.all_eq_true.mp check_19) b (by simpa [bases] using hb))
  · intro b hb
    exact of_decide_eq_true ((List.all_eq_true.mp check_20) b (by simpa [bases] using hb))
  · intro b hb
    exact of_decide_eq_true ((List.all_eq_true.mp check_21) b (by simpa [bases] using hb))
  · intro b hb
    exact of_decide_eq_true ((List.all_eq_true.mp check_22) b (by simpa [bases] using hb))
  · intro b hb
    exact of_decide_eq_true ((List.all_eq_true.mp check_23) b (by simpa [bases] using hb))
  · intro b hb
    exact of_decide_eq_true ((List.all_eq_true.mp check_24) b (by simpa [bases] using hb))
  · intro b hb
    exact of_decide_eq_true ((List.all_eq_true.mp check_25) b (by simpa [bases] using hb))
  · intro b hb
    exact of_decide_eq_true ((List.all_eq_true.mp check_26) b (by simpa [bases] using hb))
  · intro b hb
    exact of_decide_eq_true ((List.all_eq_true.mp check_27) b (by simpa [bases] using hb))
  · intro b hb
    exact of_decide_eq_true ((List.all_eq_true.mp check_28) b (by simpa [bases] using hb))
  · intro b hb
    exact of_decide_eq_true ((List.all_eq_true.mp check_29) b (by simpa [bases] using hb))
  · intro b hb
    exact of_decide_eq_true ((List.all_eq_true.mp check_30) b (by simpa [bases] using hb))
  · intro b hb
    exact of_decide_eq_true ((List.all_eq_true.mp check_31) b (by simpa [bases] using hb))
  · intro b hb
    exact of_decide_eq_true ((List.all_eq_true.mp check_32) b (by simpa [bases] using hb))
  · intro b hb
    exact of_decide_eq_true ((List.all_eq_true.mp check_33) b (by simpa [bases] using hb))
  · intro b hb
    exact of_decide_eq_true ((List.all_eq_true.mp check_34) b (by simpa [bases] using hb))
  · intro b hb
    exact of_decide_eq_true ((List.all_eq_true.mp check_35) b (by simpa [bases] using hb))
  · intro b hb
    exact of_decide_eq_true ((List.all_eq_true.mp check_36) b (by simpa [bases] using hb))
  · intro b hb
    exact of_decide_eq_true ((List.all_eq_true.mp check_37) b (by simpa [bases] using hb))
  · intro b hb
    exact of_decide_eq_true ((List.all_eq_true.mp check_38) b (by simpa [bases] using hb))
  · intro b hb
    exact of_decide_eq_true ((List.all_eq_true.mp check_39) b (by simpa [bases] using hb))
  · intro b hb
    exact of_decide_eq_true ((List.all_eq_true.mp check_40) b (by simpa [bases] using hb))
  · intro b hb
    exact of_decide_eq_true ((List.all_eq_true.mp check_41) b (by simpa [bases] using hb))
  · intro b hb
    exact of_decide_eq_true ((List.all_eq_true.mp check_42) b (by simpa [bases] using hb))
  · intro b hb
    exact of_decide_eq_true ((List.all_eq_true.mp check_43) b (by simpa [bases] using hb))
  · intro b hb
    exact of_decide_eq_true ((List.all_eq_true.mp check_44) b (by simpa [bases] using hb))
  · intro b hb
    exact of_decide_eq_true ((List.all_eq_true.mp check_45) b (by simpa [bases] using hb))
  · intro b hb
    exact of_decide_eq_true ((List.all_eq_true.mp check_46) b (by simpa [bases] using hb))
  · intro b hb
    exact of_decide_eq_true ((List.all_eq_true.mp check_47) b (by simpa [bases] using hb))
  · intro b hb
    exact of_decide_eq_true ((List.all_eq_true.mp check_48) b (by simpa [bases] using hb))
  · intro b hb
    exact of_decide_eq_true ((List.all_eq_true.mp check_49) b (by simpa [bases] using hb))
  · intro b hb
    exact of_decide_eq_true ((List.all_eq_true.mp check_50) b (by simpa [bases] using hb))
  · intro b hb
    exact of_decide_eq_true ((List.all_eq_true.mp check_51) b (by simpa [bases] using hb))
  · intro b hb
    exact of_decide_eq_true ((List.all_eq_true.mp check_52) b (by simpa [bases] using hb))
  · intro b hb
    exact of_decide_eq_true ((List.all_eq_true.mp check_53) b (by simpa [bases] using hb))
  · intro b hb
    exact of_decide_eq_true ((List.all_eq_true.mp check_54) b (by simpa [bases] using hb))
  · intro b hb
    exact of_decide_eq_true ((List.all_eq_true.mp check_55) b (by simpa [bases] using hb))
  · intro b hb
    exact of_decide_eq_true ((List.all_eq_true.mp check_56) b (by simpa [bases] using hb))
  · intro b hb
    exact of_decide_eq_true ((List.all_eq_true.mp check_57) b (by simpa [bases] using hb))
  · intro b hb
    exact of_decide_eq_true ((List.all_eq_true.mp check_58) b (by simpa [bases] using hb))
  · intro b hb
    exact of_decide_eq_true ((List.all_eq_true.mp check_59) b (by simpa [bases] using hb))
  · intro b hb
    exact of_decide_eq_true ((List.all_eq_true.mp check_60) b (by simpa [bases] using hb))
  · intro b hb
    exact of_decide_eq_true ((List.all_eq_true.mp check_61) b (by simpa [bases] using hb))
  · intro b hb
    exact of_decide_eq_true ((List.all_eq_true.mp check_62) b (by simpa [bases] using hb))
  · intro b hb
    exact of_decide_eq_true ((List.all_eq_true.mp check_63) b (by simpa [bases] using hb))
  · intro b hb
    exact of_decide_eq_true ((List.all_eq_true.mp check_64) b (by simpa [bases] using hb))
  · intro b hb
    exact of_decide_eq_true ((List.all_eq_true.mp check_65) b (by simpa [bases] using hb))
  · intro b hb
    exact of_decide_eq_true ((List.all_eq_true.mp check_66) b (by simpa [bases] using hb))
  · intro b hb
    exact of_decide_eq_true ((List.all_eq_true.mp check_67) b (by simpa [bases] using hb))
  · intro b hb
    exact of_decide_eq_true ((List.all_eq_true.mp check_68) b (by simpa [bases] using hb))
  · intro b hb
    exact of_decide_eq_true ((List.all_eq_true.mp check_69) b (by simpa [bases] using hb))
  · intro b hb
    exact of_decide_eq_true ((List.all_eq_true.mp check_70) b (by simpa [bases] using hb))
  · intro b hb
    exact of_decide_eq_true ((List.all_eq_true.mp check_71) b (by simpa [bases] using hb))
  · intro b hb
    exact of_decide_eq_true ((List.all_eq_true.mp check_72) b (by simpa [bases] using hb))
  · intro b hb
    exact of_decide_eq_true ((List.all_eq_true.mp check_73) b (by simpa [bases] using hb))
  · intro b hb
    exact of_decide_eq_true ((List.all_eq_true.mp check_74) b (by simpa [bases] using hb))
  · intro b hb
    exact of_decide_eq_true ((List.all_eq_true.mp check_75) b (by simpa [bases] using hb))

theorem exchange : Matroid.ExchangeProperty BP := by
  rintro A B ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩ e he
  obtain ⟨f, hf, h⟩ := exchange_checked a ha b hb e (by simpa using he)
  refine ⟨f, by simpa using hf, insert f (a.erase e), h, ?_⟩
  ext x
  simp

noncomputable def M : Matroid V := Matroid.ofIsBaseOfFinite
  (Set.finite_univ) BP
  ⟨({0,2,3,5} : Finset V), by exact ⟨{0,2,3,5}, by decide, rfl⟩⟩
  exchange (by intro B _; exact Set.subset_univ B)

end CommonBasis332371
