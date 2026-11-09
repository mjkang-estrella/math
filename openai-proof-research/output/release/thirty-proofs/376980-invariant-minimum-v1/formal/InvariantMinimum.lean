import Mathlib

namespace InvariantMinimum

/-- The binary minimum, restricted to positive inputs in the source statements. -/
def m (a b : ℝ) : ℝ := min a b

/-- The ternary minimum. -/
def M (a b c : ℝ) : ℝ := min a (min b c)

/-- Horwitz's continuous internal binary mean, with no strictness condition. -/
def IsMean2 (f : ℝ → ℝ → ℝ) : Prop :=
  ContinuousOn (fun v : Fin 2 → ℝ => f (v 0) (v 1)) {v | ∀ i, 0 < v i} ∧
  ∀ a b : ℝ, 0 < a → 0 < b → min a b ≤ f a b ∧ f a b ≤ max a b

/-- The same source definition for three variables. -/
def IsMean3 (f : ℝ → ℝ → ℝ → ℝ) : Prop :=
  ContinuousOn (fun v : Fin 3 → ℝ => f (v 0) (v 1) (v 2)) {v | ∀ i, 0 < v i} ∧
  ∀ a b c : ℝ, 0 < a → 0 < b → 0 < c →
    min a (min b c) ≤ f a b c ∧ f a b c ≤ max a (max b c)

def Symmetric2 (f : ℝ → ℝ → ℝ) : Prop :=
  ∀ v : Fin 2 → ℝ, (∀ i, 0 < v i) → ∀ σ : Equiv.Perm (Fin 2),
    f (v (σ 0)) (v (σ 1)) = f (v 0) (v 1)

def Symmetric3 (f : ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ v : Fin 3 → ℝ, (∀ i, 0 < v i) → ∀ σ : Equiv.Perm (Fin 3),
    f (v (σ 0)) (v (σ 1)) (v (σ 2)) = f (v 0) (v 1) (v 2)

/-- The actual source type 1 identity, in its stated argument order. -/
def Type1 (f : ℝ → ℝ → ℝ) (g : ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ a b c : ℝ, 0 < a → 0 < b → 0 < c →
    g (f a c) (f a b) (f b c) = g a b c

/-- The actual source type 2 identity. -/
def Type2 (f : ℝ → ℝ → ℝ) (g : ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ a b : ℝ, 0 < a → 0 < b → g a b (f a b) = f a b

/-- Necessary conjugacy equations for the binary and ternary arithmetic means. -/
def ArithmeticGenerator (f : ℝ → ℝ → ℝ) (g : ℝ → ℝ → ℝ → ℝ)
    (h : ℝ → ℝ) : Prop :=
  Set.InjOn h (Set.Ioi 0) ∧
  (∀ a b : ℝ, 0 < a → 0 < b → h (f a b) = (h a + h b)/2) ∧
  (∀ a b c : ℝ, 0 < a → 0 < b → 0 < c →
    h (g a b c) = (h a + h b + h c)/3)

/-- A precise inverse-transform representation. The averages must lie in the
range of the generator, where its inverse is defined. No monotonicity is imposed:
excluding this larger class also excludes every genuine monotone transform. -/
def InverseArithmeticPair (f : ℝ → ℝ → ℝ) (g : ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∃ h inv : ℝ → ℝ,
    (∀ a : ℝ, 0 < a → inv (h a) = a) ∧
    (∀ a b : ℝ, 0 < a → 0 < b → (h a + h b)/2 ∈ h '' Set.Ioi 0) ∧
    (∀ a b c : ℝ, 0 < a → 0 < b → 0 < c →
      (h a + h b + h c)/3 ∈ h '' Set.Ioi 0) ∧
    (∀ a b : ℝ, 0 < a → 0 < b → f a b = inv ((h a + h b)/2)) ∧
    (∀ a b c : ℝ, 0 < a → 0 < b → 0 < c →
      g a b c = inv ((h a + h b + h c)/3))

theorem m_isMean : IsMean2 m := by
  constructor
  · exact ((continuous_apply 0).min (continuous_apply 1)).continuousOn
  · intro a b _ _
    exact ⟨le_rfl, min_le_max⟩

theorem M_isMean : IsMean3 M := by
  constructor
  · exact ((continuous_apply 0).min ((continuous_apply 1).min (continuous_apply 2))).continuousOn
  · intro a b c _ _ _
    exact ⟨le_rfl, (min_le_left _ _).trans (le_max_left _ _)⟩

theorem min2_le (v : Fin 2 → ℝ) (i : Fin 2) : m (v 0) (v 1) ≤ v i := by
  fin_cases i
  · exact min_le_left _ _
  · exact min_le_right _ _

theorem min3_le (v : Fin 3 → ℝ) (i : Fin 3) : M (v 0) (v 1) (v 2) ≤ v i := by
  fin_cases i
  · exact min_le_left _ _
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact (min_le_right _ _).trans (min_le_right _ _)

theorem m_symmetric : Symmetric2 m := by
  intro v _ σ
  apply le_antisymm
  · apply le_min
    · simpa only [Equiv.apply_symm_apply] using min2_le (fun i => v (σ i)) (σ.symm 0)
    · simpa only [Equiv.apply_symm_apply] using min2_le (fun i => v (σ i)) (σ.symm 1)
  · exact le_min (min2_le v (σ 0)) (min2_le v (σ 1))

theorem M_symmetric : Symmetric3 M := by
  intro v _ σ
  apply le_antisymm
  · apply le_min
    · simpa only [Equiv.apply_symm_apply] using min3_le (fun i => v (σ i)) (σ.symm 0)
    · apply le_min
      · simpa only [Equiv.apply_symm_apply] using min3_le (fun i => v (σ i)) (σ.symm 1)
      · simpa only [Equiv.apply_symm_apply] using min3_le (fun i => v (σ i)) (σ.symm 2)
  · exact le_min (min3_le v (σ 0)) (le_min (min3_le v (σ 1)) (min3_le v (σ 2)))

theorem type1 : Type1 m M := by
  intro a b c _ _ _
  simp [m, M, min_left_comm, min_comm]

theorem type2 : Type2 m M := by
  intro a b _ _
  simp [m, M]

/-- The positive orthant is closed under both witness means. -/
theorem witness_positive (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    0 < m a b ∧ 0 < M a b c := by
  exact ⟨lt_min ha hb, lt_min ha (lt_min hb hc)⟩

/-- Genuine inverse formulas imply the generator equations, with both arity denominators. -/
theorem inverse_pair_implies_generator (f : ℝ → ℝ → ℝ) (g : ℝ → ℝ → ℝ → ℝ)
    (hrep : InverseArithmeticPair f g) : ∃ h, ArithmeticGenerator f g h := by
  obtain ⟨h, inv, hi, h2range, h3range, h2, h3⟩ := hrep
  refine ⟨h, ?_, ?_, ?_⟩
  · intro a ha b hb he
    have he' := congrArg inv he
    rw [hi a ha, hi b hb] at he'
    exact he'
  · intro a b ha hb
    obtain ⟨c, hc, he⟩ := h2range a b ha hb
    rw [h2 a b ha hb, ← he, hi c hc]
  · intro a b c ha hb hc
    obtain ⟨d, hd, he⟩ := h3range a b c ha hb hc
    rw [h3 a b c ha hb hc, ← he, hi d hd]

/-- The binary minimum alone obstructs every injective arithmetic generator. -/
theorem no_arithmetic_generator : ¬ ∃ h, ArithmeticGenerator m M h := by
  rintro ⟨h, hinj, h2, _⟩
  have he := h2 1 2 (by norm_num) (by norm_num)
  norm_num [m] at he
  have hh : h 1 = h 2 := by linarith
  have h12 := hinj (by norm_num : (1:ℝ) ∈ Set.Ioi 0)
    (by norm_num : (2:ℝ) ∈ Set.Ioi 0) hh
  norm_num at h12

theorem no_inverse_arithmetic_pair : ¬ InverseArithmeticPair m M := by
  intro h
  exact no_arithmetic_generator (inverse_pair_implies_generator m M h)

/-- The witness is not strict in the source's separate sense. -/
theorem witness_not_strict : m 1 2 = (1:ℝ) ∧ (1:ℝ) ≠ 2 := by norm_num [m]

/-- MathDB376980 / Horwitz's literal both-types classification is false for
continuous symmetric means when no strictness assumption is added. -/
theorem source_counterexample :
    IsMean2 m ∧ IsMean3 M ∧ Symmetric2 m ∧ Symmetric3 M ∧
    Type1 m M ∧ Type2 m M ∧ ¬ InverseArithmeticPair m M := by
  exact ⟨m_isMean, M_isMean, m_symmetric, M_symmetric, type1, type2, no_inverse_arithmetic_pair⟩

end InvariantMinimum
