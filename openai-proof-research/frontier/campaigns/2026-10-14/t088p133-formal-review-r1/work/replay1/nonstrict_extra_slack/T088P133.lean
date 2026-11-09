/- Copyright (c) 2026 Myeongjin Kang. Released under the MIT license.
   Scoped deterministic support for original Proposition B; not the geometric theorem. -/
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace T088P133

noncomputable def firstBracket (α β p q d A B : ℝ) : ℝ :=
  p*A*β + q*B*α - d*α*β

noncomputable def secondBracket (α β p q d A B : ℝ) : ℝ :=
  A*B - d*(p*α*B + q*β*A)

noncomputable def mixture (α β p q d A B : ℝ) : ℝ :=
  (1+d)*(p*α/(α+A) + q*β/(β+B))

theorem firstBracket_decomposition (α β p q d A B : ℝ)
    (hs : α+β=2) (hq : q=1-p) :
    firstBracket α β p q d A B =
      p*β*(A-2*d*p) + q*α*(B-2*d*q) + d*(2*p-α)^2 := by
  dsimp [firstBracket]
  subst q
  have hb : β=2-α := by linarith
  rw [hb]
  ring

theorem secondBracket_decomposition (α β p q d A B : ℝ)
    (hs : α+β=2) :
    secondBracket α β p q d A B =
      (α*B*(A-2*d*p) + β*A*(B-2*d*q))/2 := by
  dsimp [secondBracket]
  have hb : β=2-α := by linarith
  rw [hb]
  ring

theorem cleared_slack (α β p q d A B : ℝ) (hq : q=1-p) :
    (α+A)*(β+B) - (1+d)*(p*α*(β+B)+q*β*(α+A)) =
      firstBracket α β p q d A B + secondBracket α β p q d A B := by
  subst q
  dsimp [firstBracket, secondBracket]
  ring

theorem slack_identity (α β p q d A B : ℝ) (hq : q=1-p)
    (hdenA : α+A ≠ 0) (hdenB : β+B ≠ 0) :
    1-mixture α β p q d A B =
      (firstBracket α β p q d A B + secondBracket α β p q d A B) /
        ((α+A)*(β+B)) := by
  dsimp [mixture, firstBracket, secondBracket]
  subst q
  field_simp
  ring

theorem firstBracket_nonneg (α β p q d A B : ℝ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hp : 0 ≤ p) (hq0 : 0 ≤ q)
    (hd : 0 ≤ d) (hs : α+β=2) (hq : q=1-p)
    (hA : 2*d*p ≤ A) (hB : 2*d*q ≤ B) :
    0 ≤ firstBracket α β p q d A B := by
  rw [firstBracket_decomposition α β p q d A B hs hq]
  exact add_nonneg (add_nonneg
    (mul_nonneg (mul_nonneg hp hβ) (sub_nonneg.mpr hA))
    (mul_nonneg (mul_nonneg hq0 hα) (sub_nonneg.mpr hB)))
    (mul_nonneg hd (sq_nonneg _))

theorem secondBracket_nonneg (α β p q d A B : ℝ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hs : α+β=2) (hA : 2*d*p ≤ A) (hB : 2*d*q ≤ B) :
    0 ≤ secondBracket α β p q d A B := by
  rw [secondBracket_decomposition α β p q d A B hs]
  exact div_nonneg (add_nonneg
    (mul_nonneg (mul_nonneg hα hB0) (sub_nonneg.mpr hA))
    (mul_nonneg (mul_nonneg hβ hA0) (sub_nonneg.mpr hB))) (by norm_num)

theorem secondBracket_pos (α β p q d A B : ℝ)
    (hα : 0 < α) (hβ : 0 ≤ β) (hA0 : 0 ≤ A) (hB0 : 0 < B)
    (hs : α+β=2) (hA : 2*d*p < A) (hB : 2*d*q ≤ B) :
    0 < secondBracket α β p q d A B := by
  rw [secondBracket_decomposition α β p q d A B hs]
  exact div_pos (add_pos_of_pos_of_nonneg
    (mul_pos (mul_pos hα hB0) (sub_pos.mpr hA))
    (mul_nonneg (mul_nonneg hβ hA0) (sub_nonneg.mpr hB))) (by norm_num)

theorem mixture_le_one (α β p q d A B : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hp : 0 ≤ p) (hq0 : 0 ≤ q)
    (hd : 0 ≤ d) (hs : α+β=2) (hq : q=1-p)
    (hA0 : 0 < A) (hB0 : 0 < B) (hA : 2*d*p ≤ A) (hB : 2*d*q ≤ B) :
    mixture α β p q d A B ≤ 1 := by
  have ha := add_pos hα hA0
  have hb := add_pos hβ hB0
  have h1 := firstBracket_nonneg α β p q d A B hα.le hβ.le hp hq0 hd hs hq hA hB
  have h2 := secondBracket_nonneg α β p q d A B hα.le hβ.le hA0.le hB0.le hs hA hB
  have hz := div_nonneg (add_nonneg h1 h2) (mul_pos ha hb).le
  rw [← slack_identity α β p q d A B hq (ne_of_gt ha) (ne_of_gt hb)] at hz
  linarith

theorem mixture_lt_one (α β p q d A B : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hp : 0 ≤ p) (hq0 : 0 ≤ q)
    (hd : 0 ≤ d) (hs : α+β=2) (hq : q=1-p)
    (hA0 : 0 < A) (hB0 : 0 < B) (hA : 2*d*p < A) (hB : 2*d*q ≤ B) :
    mixture α β p q d A B < 1 := by
  have ha := add_pos hα hA0
  have hb := add_pos hβ hB0
  have h1 := firstBracket_nonneg α β p q d A B hα.le hβ.le hp hq0 hd hs hq hA.le hB
  have h2 := secondBracket_pos α β p q d A B hα hβ.le hA0.le hB0 hs hA hB
  have hz := div_pos (add_pos_of_nonneg_of_pos h1 h2) (mul_pos ha hb)
  rw [← slack_identity α β p q d A B hq (ne_of_gt ha) (ne_of_gt hb)] at hz
  linarith

theorem moment_lt_iff (d p P : ℝ) (hp : 0 < p) :
    (2*d*p^2 < P) ↔ (2*d*p < P/p) := by
  rw [lt_div_iff₀ hp]
  ring_nf

theorem moment_le_iff (d p P : ℝ) (hp : 0 < p) :
    (2*d*p^2 ≤ P) ↔ (2*d*p ≤ P/p) := by
  rw [le_div_iff₀ hp]
  ring_nf

theorem conditional_means (p q P N : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hq : q=1-p) (hP : 0 < P) (hN : 0 < N) :
    0 < q ∧ 0 < P/p ∧ 0 < N/q ∧ p*(P/p)=P ∧ q*(N/q)=N := by
  have hq0 : 0 < q := by linarith
  refine ⟨hq0, div_pos hP hp, div_pos hN hq0, ?_, ?_⟩
  · field_simp
  · field_simp

theorem rational_mixture_lt_one (α β p q d P N : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hs : α+β=2)
    (hp : 0 < p) (hp1 : p < 1) (hq : q=1-p) (hd : 0 ≤ d)
    (hP : 0 < P) (hN : 0 < N)
    (hPm : 2*d*p^2 < P) (hNm : 2*d*q^2 ≤ N) :
    (1+d)*(p*α/(α+P/p)+q*β/(β+N/q)) < 1 := by
  obtain ⟨hq0, hA, hB, _, _⟩ := conditional_means p q P N hp hp1 hq hP hN
  exact mixture_lt_one α β p q d (P/p) (N/q) hα hβ hp.le hq0.le hd hs hq hA hB
    ((moment_lt_iff d p P hp).mp hPm) ((moment_le_iff d q N hq0).mp hNm)

theorem rational_mixture_le_one (α β p q d P N : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hs : α+β=2)
    (hp : 0 < p) (hp1 : p < 1) (hq : q=1-p) (hd : 0 ≤ d)
    (hP : 0 < P) (hN : 0 < N)
    (hPm : 2*d*p^2 ≤ P) (hNm : 2*d*q^2 ≤ N) (_extra : (1+d)*(p*α/(α+P/p)+q*β/(β+N/q)) ≤ 1) :
    (1+d)*(p*α/(α+P/p)+q*β/(β+N/q)) ≤ 1 := by
  obtain ⟨hq0, hA, hB, _, _⟩ := conditional_means p q P N hp hp1 hq hP hN
  exact mixture_le_one α β p q d (P/p) (N/q) hα hβ hp.le hq0.le hd hs hq hA hB
    ((moment_le_iff d p P hp).mp hPm) ((moment_le_iff d q N hq0).mp hNm)

theorem positive_sum_two_bounds (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hs : α+β=2) : α < 2 ∧ β < 2 := by
  constructor <;> linarith

theorem one_sided_lt_one (a d M : ℝ) (ha : 0 < a) (ha2 : a < 2)
    (hM : 0 < M) (hm : 2*d ≤ M) : (1+d)/(1+M/a) < 1 := by
  have hscale : d*a < M := by
    have h := mul_le_mul_of_nonneg_right hm ha.le
    have h' := mul_pos hM (sub_pos.mpr ha2)
    nlinarith
  have hdM : d < M/a := (lt_div_iff₀ ha).mpr hscale
  apply (div_lt_one (show 0 < 1+M/a by positivity)).mpr
  linarith

theorem p_one_bound (α β d P : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hs : α+β=2) (hP : 0 < P) (hm : 2*d ≤ P) :
    (1+d)/(1+P/α) < 1 :=
  one_sided_lt_one α d P hα (positive_sum_two_bounds α β hα hβ hs).1 hP hm

theorem p_zero_bound (α β d N : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hs : α+β=2) (hN : 0 < N) (hm : 2*d ≤ N) :
    (1+d)/(1+N/β) < 1 :=
  one_sided_lt_one β d N hβ (positive_sum_two_bounds α β hα hβ hs).2 hN hm

end T088P133
