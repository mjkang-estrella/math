import Mathlib

namespace AdditiveMonotonicity

-- Arithmetic functions take natural arguments and real values here.
def identityFn : ℕ → ℝ := fun n => n

def exceptionalFn : ℕ → ℝ := fun n => if n = 2 then 0 else n

def KAdditive (E : Set ℕ) (k : ℕ) (f : ℕ → ℝ) : Prop :=
  ∀ a : Fin k → ℕ, (∀ i, a i ∈ E) →
    f (∑ i, a i) = ∑ i, f (a i)

noncomputable def count (E : Set ℕ) (S : Finset (ℕ → ℝ)) (k : ℕ) : ℕ := by
  classical
  exact (S.filter (KAdditive E k)).card

theorem identity_additive (E : Set ℕ) (k : ℕ) : KAdditive E k identityFn := by
  intro a _
  simp [identityFn]

theorem exceptional_not_two : ¬ KAdditive {1} 2 exceptionalFn := by
  intro h
  have hx := h (fun _ => 1) (by simp)
  norm_num [exceptionalFn, Fin.sum_univ_two] at hx

theorem exceptional_three : KAdditive {1} 3 exceptionalFn := by
  intro a ha
  have he : a = fun _ => 1 := by
    funext i
    simpa only [Set.mem_singleton_iff] using ha i
  subst a
  norm_num [exceptionalFn, Fin.sum_univ_succ]

theorem identity_ne_exceptional : identityFn ≠ exceptionalFn := by
  intro h
  have hx := congrFun h 2
  norm_num [identityFn, exceptionalFn] at hx

noncomputable def family : Finset (ℕ → ℝ) := by
  classical
  exact {identityFn, exceptionalFn}

theorem count_two : count {1} family 2 = 1 := by
  classical
  simp [count, family, Finset.filter_insert, Finset.filter_singleton, identity_additive,
    exceptional_not_two]

theorem count_three : count {1} family 3 = 2 := by
  classical
  simp [count, family, Finset.filter_insert, Finset.filter_singleton, identity_additive,
    exceptional_three, identity_ne_exceptional]

theorem monotonicity_counterexample :
    2 ≤ (3 : ℕ) ∧ count {1} family 2 < count {1} family 3 := by
  rw [count_two, count_three]
  norm_num

end AdditiveMonotonicity
