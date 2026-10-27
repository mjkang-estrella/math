import Mathlib

namespace KadarYu

open Polynomial

theorem coprime_recurrence_step {p q L : ℝ[X]} {c : ℝ}
    (hc : c ≠ 0) (hpq : IsCoprime p q) :
    IsCoprime q (L * q - C c * p) := by
  obtain ⟨u, v, huv⟩ := hpq
  have hK : C c⁻¹ * C c = (1 : ℝ[X]) := by
    rw [← C_mul, inv_mul_cancel₀ hc, C_1]
  refine ⟨v + u * C c⁻¹ * L, -u * C c⁻¹, ?_⟩
  calc
    (v + u * C c⁻¹ * L) * q + (-u * C c⁻¹) * (L * q - C c * p) =
        u * (C c⁻¹ * C c) * p + v * q := by ring
    _ = 1 := by rw [hK, mul_one, huv]

noncomputable def recurrenceSeries (L : ℕ → ℝ[X]) (c : ℕ → ℝ)
    (q1 : ℝ[X]) : ℕ → ℝ[X]
  | 0 => 1
  | 1 => q1
  | n + 2 => L n * recurrenceSeries L c q1 (n + 1) -
      C (c n) * recurrenceSeries L c q1 n

theorem recurrenceSeries_consecutive_coprime
    (L : ℕ → ℝ[X]) (c : ℕ → ℝ) (q1 : ℝ[X]) (hc : ∀ n, c n ≠ 0) :
    ∀ n, IsCoprime (recurrenceSeries L c q1 n) (recurrenceSeries L c q1 (n + 1)) := by
  intro n
  induction n with
  | zero => exact isCoprime_one_left
  | succ n ih => exact coprime_recurrence_step (hc n) ih

theorem coprime_common_factor_dvd {F a b d : ℝ[X]}
    (hab : IsCoprime a b) (ha : d ∣ F * a) (hb : d ∣ F * b) : d ∣ F := by
  obtain ⟨u, v, huv⟩ := hab
  have hcomb : F = u * (F * a) + v * (F * b) := by
    calc F = F * (u * a + v * b) := by rw [huv, mul_one]
         _ = u * (F * a) + v * (F * b) := by ring
  rw [hcomb]
  exact dvd_add (dvd_mul_of_dvd_right ha u) (dvd_mul_of_dvd_right hb v)

theorem reduced_common_factor_unique {F g p0 p1 q0 q1 : ℝ[X]}
    (hF : F.Monic) (hg : g.Monic)
    (hp : IsCoprime p0 p1) (hq : IsCoprime q0 q1)
    (h0 : F * p0 = g * q0) (h1 : F * p1 = g * q1) : F = g := by
  have hgd : g ∣ F := coprime_common_factor_dvd hp ⟨q0, h0⟩ ⟨q1, h1⟩
  have hFd : F ∣ g := coprime_common_factor_dvd hq ⟨p0, h0.symm⟩ ⟨p1, h1.symm⟩
  exact Polynomial.eq_of_monic_of_associated hF hg (associated_of_dvd_dvd hFd hgd)

theorem reduced_series_identification {F g : ℝ[X]} {p q : ℕ → ℝ[X]}
    (hF : F.Monic) (hg : g.Monic)
    (hp : IsCoprime (p 0) (p 1)) (hq : IsCoprime (q 0) (q 1))
    (hdet : ∀ n, F * p n = g * q n) :
    F = g ∧ ∀ n, p n = q n := by
  have hFG := reduced_common_factor_unique hF hg hp hq (hdet 0) (hdet 1)
  refine ⟨hFG, ?_⟩
  intro n
  have hh := hdet n
  rw [← hFG] at hh
  exact mul_left_cancel₀ hF.ne_zero hh

theorem reduced_series_boundary {p q : ℕ → ℝ[X]} {pminus qminus : ℝ[X]}
    (h : ∀ n, p n = q n)
    (hp : pminus = X * p 0 - p 1) (hq : qminus = X * q 0 - q 1) :
    pminus = qminus := by
  rw [hp, h 0, h 1, hq]

end KadarYu
