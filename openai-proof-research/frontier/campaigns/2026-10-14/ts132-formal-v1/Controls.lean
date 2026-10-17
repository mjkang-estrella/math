import TSLocal

/- Copyright 2026 Myeongjin Kang. MIT. Concrete nonvacuity and boundary controls. -/
namespace TSControls
open TSLocal

theorem empty_tournament :
    (∅ : Finset ℕ).card ≤ 3 := by
  exact tournament_card_le_three _ (fun _ _ => False)
    (by simp) (by simp) (by simp)

theorem three_cycle_bound : (Finset.univ : Finset (Fin 3)).card ≤ 3 := by
  let R : Fin 3 → Fin 3 → Prop := fun a b => (a.val+1)%3 = b.val
  apply tournament_card_le_three _ R
  · decide
  · decide
  · decide

def triple : Finset ((ZMod 3) × PUnit) :=
  {(0,PUnit.unit), (1,PUnit.unit), (2,PUnit.unit)}

theorem triple_head_constant : HeadConstant (fun a b : ZMod 3 => b-a=1) 1 triple := by
  refine ⟨fun _ => 1, ?_⟩
  intro u _ v _ c hc
  simp only [edgeLabel] at hc
  split_ifs at hc with he hR
  exact (Option.some.inj hc).symm.trans hR

theorem triple_card : triple.card = 3 := by decide

theorem bound_two_false : ¬ triple.card ≤ 2 := by rw [triple_card]; omega

theorem zero_depth_singleton :
    ({PUnit.unit} : Finset (Word ℤ 0)).card = 1 := by decide

theorem zero_scalar_collapses :
    affineVector (0:ℚ) (fun _ : Fin 1 => 3) (fun _ => 1) =
    affineVector (0:ℚ) (fun _ : Fin 1 => 3) (fun _ => 2) := by
  funext i
  norm_num [affineVector]

theorem row_only_preserves_label {K ι : Type*} [Field K] (H : Subgroup Kˣ)
    (b : ι → K) (x : (ι → K) × H) : (rowPositionMap H 1 b x).2 = x.2 := by
  simp [rowPositionMap]

theorem row_only_cannot_change_label {K ι : Type*} [Field K] (H : Subgroup Kˣ)
    (b : ι → K) (x y : (ι → K) × H) (h : x.2 ≠ y.2) :
    rowPositionMap H 1 b x ≠ y := by
  intro he
  have hh := congrArg Prod.snd he
  rw [row_only_preserves_label] at hh
  exact h hh

theorem zero_epsilon_profiles :
    ∀ n ≤ 20, (5:ℝ) ≤ profileEnvelope 5 0 n ∧
      (0:ℝ) ≤ 0*5*(3^n-1) ∧ (5:ℝ) ≤ 2*5 := by
  exact coupled_profiles (fun _ => 5) (fun _ => 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by intro n _; norm_num) (by intro n _; norm_num)

theorem positive_epsilon_depth_one :
    (7/3:ℝ) ≤ profileEnvelope 2 (1/6) 1 ∧
      (1/3:ℝ) ≤ (1/6:ℝ)*2*(3^1-1) ∧ (7/3:ℝ) ≤ 2*2 := by
  have hh := coupled_profiles (d := 1)
    (fun n => if n = 0 then 2 else 7/3) (fun n => if n = 0 then 0 else 1/3)
    (by norm_num : (0:ℝ) ≤ 2) (by norm_num : (0:ℝ) ≤ 1/6)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro n hn
      have hn0 : n = 0 := by omega
      subst n
      norm_num)
    (by
      intro n hn
      have hn0 : n = 0 := by omega
      subst n
      norm_num)
  simpa using hh 1 (by omega)

theorem seed_at_integer_parameters :
    (44*(2:ℝ)^21)^2 < (2:ℝ)^2*6^20 :=
  strict_seed_parameters (by norm_num) (by norm_num)

theorem depth_eighteen_not_seed :
    ¬ (1:ℝ) < (3/2:ℝ)^18 / (4*(18+2)^2) := by norm_num

end TSControls
