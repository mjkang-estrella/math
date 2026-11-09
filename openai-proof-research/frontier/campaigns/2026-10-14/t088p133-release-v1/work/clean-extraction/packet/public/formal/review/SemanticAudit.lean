/- Copyright (c) 2026 Myeongjin Kang. MIT.
Independent review controls for the original Proposition B use site. No probability claim. -/
import T088P133
namespace T088P133Review
open T088P133

-- Explicit expected interface types: changes cannot hide behind a prose mapping.
theorem strict_interface : (∀ (α β p q d P N : ℝ), 0 < α → 0 < β → α+β=2 →
    0 < p → p < 1 → q=1-p → 0 ≤ d → 0 < P → 0 < N →
    2*d*p^2 < P → 2*d*q^2 ≤ N →
    (1+d)*(p*α/(α+P/p)+q*β/(β+N/q)) < 1) := @rational_mixture_lt_one
theorem nonstrict_interface : (∀ (α β p q d P N : ℝ), 0 < α → 0 < β → α+β=2 →
    0 < p → p < 1 → q=1-p → 0 ≤ d → 0 < P → 0 < N →
    2*d*p^2 ≤ P → 2*d*q^2 ≤ N →
    (1+d)*(p*α/(α+P/p)+q*β/(β+N/q)) ≤ 1) := @rational_mixture_le_one
theorem means_interface : (∀ (p q P N : ℝ), 0 < p → p < 1 → q=1-p → 0 < P → 0 < N →
    0 < q ∧ 0 < P/p ∧ 0 < N/q ∧ p*(P/p)=P ∧ q*(N/q)=N) := @conditional_means
theorem strict_moment_interface : (∀ (d p P : ℝ), 0 < p → ((2*d*p^2 < P) ↔ (2*d*p < P/p))) := @moment_lt_iff
theorem weak_moment_interface : (∀ (d p P : ℝ), 0 < p → ((2*d*p^2 ≤ P) ↔ (2*d*p ≤ P/p))) := @moment_le_iff
theorem one_sided_interface : (∀ (a d M : ℝ), 0 < a → a < 2 → 0 < M → 2*d ≤ M →
    (1+d)/(1+M/a) < 1) := @one_sided_lt_one
theorem p_one_interface : (∀ (α β d P : ℝ), 0 < α → 0 < β → α+β=2 → 0 < P →
    2*d ≤ P → (1+d)/(1+P/α) < 1) := @p_one_bound
theorem p_zero_interface : (∀ (α β d N : ℝ), 0 < α → 0 < β → α+β=2 → 0 < N →
    2*d ≤ N → (1+d)/(1+N/β) < 1) := @p_zero_bound

theorem definition_contract (α β p q d A B : ℝ) :
    firstBracket α β p q d A B = p*A*β+q*B*α-d*α*β ∧
    secondBracket α β p q d A B = A*B-d*(p*α*B+q*β*A) ∧
    mixture α β p q d A B = (1+d)*(p*α/(α+A)+q*β/(β+B)) := by
  exact ⟨rfl,rfl,rfl⟩

theorem original_first_bracket (α β p q d P N : ℝ)
    (ha : α ≠ 0) (hb : β ≠ 0) (hp : p ≠ 0) (hq : q ≠ 0) :
    firstBracket α β p q d (P/p) (N/q) / (α*β) = P/α+N/β-d := by
  dsimp [firstBracket]
  field_simp

theorem original_second_bracket (α β p q d P N : ℝ)
    (ha : α ≠ 0) (hb : β ≠ 0) (hp : p ≠ 0) (hq : q ≠ 0)
    (hP : P ≠ 0) (hN : N ≠ 0) :
    secondBracket α β p q d (P/p) (N/q) / (α*β) =
      ((P/p)*(N/q)/(α*β))*(1-d*(p^2*α/P+q^2*β/N)) := by
  dsimp [secondBracket]
  field_simp

-- This is exactly the displayed, normalized two-bracket equation in Section 5.
theorem original_normalized_slack (α β p q d P N : ℝ)
    (ha : α ≠ 0) (hb : β ≠ 0) (hp : p ≠ 0) (hq : q ≠ 0)
    (hP : P ≠ 0) (hN : N ≠ 0) (hs : q=1-p)
    (hda : α+P/p ≠ 0) (hdb : β+N/q ≠ 0) :
    (α+P/p)*(β+N/q)*(1-mixture α β p q d (P/p) (N/q))/(α*β) =
      (P/α+N/β-d)+((P/p)*(N/q)/(α*β))*(1-d*(p^2*α/P+q^2*β/N)) := by
  rw [slack_identity α β p q d (P/p) (N/q) hs hda hdb]
  rw [← original_first_bracket α β p q d P N ha hb hp hq,
      ← original_second_bracket α β p q d P N ha hb hp hq hP hN]
  have hcancel (C D : ℝ) (hD : D ≠ 0) : D*(C/D)=C := by field_simp
  rw [hcancel _ _ (mul_ne_zero hda hdb), add_div]

-- An abstract scalar majorization interface only: L is not an expectation in Lean.
theorem scalar_majorization_use (α β p q d P N L : ℝ)
    (ha : 0 < α) (hb : 0 < β) (hs : α+β=2) (hp : 0 < p)
    (hp1 : p < 1) (hq : q=1-p) (hd : 0 ≤ d) (hP : 0 < P) (hN : 0 < N)
    (hmP : 2*d*p^2 < P) (hmN : 2*d*q^2 ≤ N)
    (hL : L ≤ p*α/(α+P/p)+q*β/(β+N/q)) : (1+d)*L < 1 := by
  have hscale : 0 ≤ 1+d := by linarith
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hL hscale)
    (rational_mixture_lt_one α β p q d P N ha hb hs hp hp1 hq hd hP hN hmP hmN)

theorem endpoint_expression (a d M : ℝ) (ha : 0 < a) (hM : 0 < M) :
    (1+d)*a/(a+M) = (1+d)/(1+M/a) := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have ham : a+M ≠ 0 := ne_of_gt (add_pos ha hM)
  have hden : 1+M/a ≠ 0 := ne_of_gt (show 0 < 1+M/a by positivity)
  field_simp

theorem endpoint_negative_d : (1+(-2:ℝ))/(1+1/1) = -1/2 ∧
    (1+(-2:ℝ))/(1+1/1) < 1 := by
  constructor
  · norm_num
  · exact one_sided_lt_one 1 (-2) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end T088P133Review
