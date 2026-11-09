import Mathlib

open Finset Real

namespace TrigBridge

lemma cosine_recurrence (n : ℕ) (t : ℝ) :
    Real.cos ((n+2:ℕ)*t)+Real.cos ((n:ℝ)*t)=
      2*Real.cos ((n+1:ℕ)*t)*Real.cos t := by
  have h := Real.cos_add_cos (((n+2:ℕ):ℝ)*t) ((n:ℝ)*t)
  have hm : ((((n+2:ℕ):ℝ)*t+(n:ℝ)*t)/2)=((n+1:ℕ):ℝ)*t := by push_cast; ring
  have hd : ((((n+2:ℕ):ℝ)*t-(n:ℝ)*t)/2)=t := by push_cast; ring
  rw [hm, hd] at h
  exact h

noncomputable def witnessAngle : ℝ := Real.arccos ((523:ℝ)/527)

lemma cos_witnessAngle : Real.cos witnessAngle=(523:ℝ)/527 := by
  exact Real.cos_arccos (by norm_num) (by norm_num)

/-- Integer Chebyshev data agree with scaled cosine at the rational-cosine witness. -/
theorem integer_cosine_bridge (C : ℕ → ℤ) (N : ℕ) (h0 : C 0=1) (h1 : C 1=523)
    (hrec : ∀ n, n+2≤N → C (n+2)=1046*C (n+1)-277729*C n) :
    ∀ n, n≤N → (C n:ℝ)=(527:ℝ)^n*Real.cos ((n:ℝ)*witnessAngle) := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => intro _; simp [h0]
  | one => intro _; simp [h1, cos_witnessAngle]; norm_num
  | more n ih0 ih1 =>
    intro hn
    have hr : (C (n+2):ℝ)=1046*(C (n+1):ℝ)-277729*(C n:ℝ) := by
      exact_mod_cast hrec n hn
    rw [hr, ih0 (by omega), ih1 (by omega)]
    have ht := cosine_recurrence n witnessAngle
    rw [cos_witnessAngle] at ht
    have ht' : 527*Real.cos ((n+2:ℕ)*witnessAngle)+527*Real.cos ((n:ℝ)*witnessAngle)=
        1046*Real.cos ((n+1:ℕ)*witnessAngle) := by nlinarith
    simp only [pow_succ]
    linear_combination -(527:ℝ)^n*527*ht'

/-- Horner's integer accumulator represents the scaled trigonometric partial sum. -/
theorem horner_trigonometric_identity (B C H : ℕ → ℤ) (b : ℕ → ℝ) (N : ℕ)
    (hB : ∀ k, k≤N → (B k:ℝ)=(4:ℝ)^k*b k)
    (hC : ∀ k, k≤N → (C k:ℝ)=(527:ℝ)^k*Real.cos ((k:ℝ)*witnessAngle))
    (hH0 : H 0=0)
    (hHrec : ∀ k, k≤N → H (k+1)=2108*H k+B k*C k) :
    ∀ m, m≤N → (H (m+1):ℝ)=(2108:ℝ)^m*
      ∑ k∈Finset.range (m+1), b k*Real.cos ((k:ℝ)*witnessAngle) := by
  intro m
  induction m with
  | zero =>
    intro _
    have h := hHrec 0 (by omega)
    rw [hH0] at h
    norm_num at h
    have hh : (H 1:ℝ)=(B 0:ℝ)*(C 0:ℝ) := by exact_mod_cast h
    rw [hh, hB 0 (by omega), hC 0 (by omega)]
    simp
  | succ m ih =>
    intro hm
    have hh : (H (m+1+1):ℝ)=2108*(H (m+1):ℝ)+(B (m+1):ℝ)*(C (m+1):ℝ) := by
      exact_mod_cast hHrec (m+1) hm
    rw [hh, ih (by omega), hB (m+1) hm, hC (m+1) hm]
    conv_rhs => rw [Finset.sum_range_succ]
    have hpow : (4:ℝ)^(m+1)*(527:ℝ)^(m+1)=(2108:ℝ)^(m+1) := by rw [← mul_pow]; norm_num
    calc
      _ = (2108:ℝ)*((2108:ℝ)^m*∑ k∈Finset.range (m+1),
          b k*Real.cos ((k:ℝ)*witnessAngle))+
        ((4:ℝ)^(m+1)*(527:ℝ)^(m+1))*
          (b (m+1)*Real.cos ((m+1:ℕ)*witnessAngle)) := by ring
      _ = _ := by rw [hpow, pow_succ]; ring

theorem negative_sum_of_horner (B C H : ℕ → ℤ) (b : ℕ → ℝ) (N : ℕ)
    (hB : ∀ k, k≤N → (B k:ℝ)=(4:ℝ)^k*b k)
    (hC : ∀ k, k≤N → (C k:ℝ)=(527:ℝ)^k*Real.cos ((k:ℝ)*witnessAngle))
    (hH0 : H 0=0) (hHrec : ∀ k, k≤N → H (k+1)=2108*H k+B k*C k)
    (hneg : H (N+1)<0) :
    (∑ k∈Finset.range (N+1),b k*Real.cos ((k:ℝ)*witnessAngle))<0 := by
  have hi := horner_trigonometric_identity B C H b N hB hC hH0 hHrec N le_rfl
  have hn : (H (N+1):ℝ)<0 := by exact_mod_cast hneg
  have hp : (0:ℝ)<(2108:ℝ)^N := by positivity
  rw [hi] at hn
  by_contra! hnonneg
  have h := mul_nonneg hp.le hnonneg
  linarith

end TrigBridge
