import ShoeBlockProbability
import ShoePair

namespace Shoe
open MeasureTheory
open scoped ENNReal

theorem four_coordinates_probability (p : DiscreteLaw ℕ) (x y z t i j : ℕ)
    (hxy : x ≠ y) (hxz : x ≠ z) (hxt : x ≠ t)
    (hyz : y ≠ z) (hyt : y ≠ t) (hzt : z ≠ t) :
    sampleMeasure p {ω | ω x = i ∧ ω y = i ∧ ω z = j ∧ ω t = j} =
      p i * p i * (p j * p j) := by
  classical
  let r : ℕ → Set ℕ := fun k => if k = x ∨ k = y then {i} else {j}
  have hs : {ω : Sample ℕ | ω x = i ∧ ω y = i ∧ ω z = j ∧ ω t = j} =
      Set.pi (({x,y,z,t} : Finset ℕ) : Set ℕ) r := by
    ext ω
    simp [r, Ne.symm hxz, Ne.symm hyz, Ne.symm hxt, Ne.symm hyt]
  rw [hs, cylinder_probability p {x,y,z,t} r (by
    intro k _; unfold r; split <;> exact measurableSet_singleton _)]
  simp [r, hxy, hxz, hxt, hyz, hyt, hzt,
    Ne.symm hxz, Ne.symm hyz, Ne.symm hxt, Ne.symm hyt,
    p.toMeasure_apply_singleton i (measurableSet_singleton i),
    p.toMeasure_apply_singleton j (measurableSet_singleton j), mul_assoc]

/-- No independence of different competing-pair events is asserted. -/
theorem isolated_other_collision_le (p : DiscreteLaw ℕ) {K a b c d i : ℕ}
    (hca : c ≠ a) (hdb : d ≠ b) :
    sampleMeasure p {ω | Isolated ω K a b i ∧ ω (2*c) = ω (2*d+1)} ≤
      p i * p i * collisionMass p := by
  have hs : {ω : Sample ℕ | Isolated ω K a b i ∧ ω (2*c) = ω (2*d+1)} ⊆
      ⋃ j : ℕ, {ω | ω (2*a) = i ∧ ω (2*b+1) = i ∧
        ω (2*c) = j ∧ ω (2*d+1) = j} := by
    intro ω h
    apply Set.mem_iUnion.mpr
    exact ⟨ω (2*c),h.1.2.2.1,h.1.2.2.2.1,rfl,h.2.symm⟩
  calc
    _ ≤ sampleMeasure p (⋃ j : ℕ, {ω | ω (2*a) = i ∧ ω (2*b+1) = i ∧
        ω (2*c) = j ∧ ω (2*d+1) = j}) := measure_mono hs
    _ ≤ ∑' j : ℕ, sampleMeasure p {ω | ω (2*a) = i ∧ ω (2*b+1) = i ∧
        ω (2*c) = j ∧ ω (2*d+1) = j} := measure_iUnion_le _
    _ = ∑' j : ℕ, p i * p i * (p j * p j) := by
      congr 1
      funext j
      exact four_coordinates_probability p _ _ _ _ i j
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    _ = _ := by rw [ENNReal.tsum_mul_left]; rfl


def OtherBad (K a b i c d : ℕ) : Set (Sample ℕ) :=
  {ω | Isolated ω K a b i ∧ c ≠ a ∧ d ≠ b ∧ ω (2*c) = ω (2*d+1)}

theorem otherBad_probability_le (p : DiscreteLaw ℕ) (K a b i c d : ℕ) :
    sampleMeasure p (OtherBad K a b i c d) ≤ p i * p i * collisionMass p := by
  by_cases hc : c = a
  · simp [OtherBad, hc]
  by_cases hd : d = b
  · simp [OtherBad, hd]
  calc
    _ ≤ sampleMeasure p {ω | Isolated ω K a b i ∧ ω (2*c) = ω (2*d+1)} :=
      measure_mono (fun _ h => ⟨h.1,h.2.2.2⟩)
    _ ≤ _ := isolated_other_collision_le p hc hd

/-- Unconditional finite union bound; overlapping competing pairs are allowed. -/
theorem isolated_le_good_add_collisions (p : DiscreteLaw ℕ) (K a b i : ℕ) :
    sampleMeasure p {ω | Isolated ω K a b i} ≤
      sampleMeasure p {ω | GoodBlock ω K a b i} +
        (K : ℝ≥0∞) * K * (p i * p i * collisionMass p) := by
  classical
  let B := ⋃ c ∈ Finset.range K, ⋃ d ∈ Finset.range K, OtherBad K a b i c d
  have hcover : {ω : Sample ℕ | Isolated ω K a b i} ⊆
      {ω | GoodBlock ω K a b i} ∪ B := by
    intro ω hω
    by_cases hg : GoodBlock ω K a b i
    · exact Or.inl hg
    · right
      have hn : ¬ (∀ c < K, ∀ d < K, c ≠ a → d ≠ b →
          ω (2*c) ≠ ω (2*d+1)) := fun h => hg ⟨hω,h⟩
      push Not at hn
      obtain ⟨c,hc,d,hd,hca,hdb,he⟩ := hn
      simp only [B, Set.mem_iUnion]
      exact ⟨c,Finset.mem_range.mpr hc,d,Finset.mem_range.mpr hd,hω,hca,hdb,he⟩
  have hB : sampleMeasure p B ≤ (K : ℝ≥0∞) * K * (p i * p i * collisionMass p) := by
    calc
      _ ≤ ∑ c ∈ Finset.range K, sampleMeasure p
          (⋃ d ∈ Finset.range K, OtherBad K a b i c d) :=
        measure_biUnion_finset_le _ _
      _ ≤ ∑ c ∈ Finset.range K, ∑ d ∈ Finset.range K,
          sampleMeasure p (OtherBad K a b i c d) := by
        apply Finset.sum_le_sum
        intro c _
        exact measure_biUnion_finset_le _ _
      _ ≤ ∑ _c ∈ Finset.range K, ∑ _d ∈ Finset.range K,
          (p i * p i * collisionMass p) := by
        apply Finset.sum_le_sum
        intro c _
        apply Finset.sum_le_sum
        intro d _
        exact otherBad_probability_le p K a b i c d
      _ = _ := by simp [nsmul_eq_mul, mul_assoc]
  exact (measure_mono hcover).trans ((measure_union_le _ _).trans
    (add_le_add le_rfl hB))

end Shoe
