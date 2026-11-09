import UlasInitialization
import Mathlib.RingTheory.Polynomial.Chebyshev
set_option linter.unusedSimpArgs false
open Polynomial PowerSeries
namespace Ulas.Even5
open Ulas.Round4
noncomputable def s : Polynomial ℤ := 1+2*Polynomial.X
noncomputable def t (n : ℤ) : Polynomial ℤ := (Chebyshev.T ℤ n).comp s
noncomputable def u (n : ℤ) : Polynomial ℤ := (Chebyshev.U ℤ n).comp s
noncomputable def rho (k : ℕ) : Polynomial ℤ := 8*u ((k:ℤ)-1)^2

theorem u_step (n : ℤ) : u n = t n + s*u (n-1) := by
  have h := congrArg (fun p : Polynomial ℤ => p.comp s)
    (Chebyshev.U_eq_X_mul_U_add_T (R := ℤ) (n-1))
  simpa [u,t, add_comm] using h

theorem t_step (n : ℤ) : t (n+1) = s*t n + (s^2-1)*u (n-1) := by
  have h := congrArg (fun p : Polynomial ℤ => p.comp s)
    (Chebyshev.T_eq_X_mul_T_sub_pol_U (R := ℤ) (n-1))
  simp only [sub_comp, mul_comp, X_comp, one_comp, pow_comp] at h
  rw [show n-1+2 = n+1 by ring, show n-1+1 = n by ring] at h
  change t (n+1) = s*t n - (1-s^2)*u (n-1) at h
  linear_combination h

theorem pell (k : ℕ) : t k ^ 2 - (s^2-1)*u ((k:ℤ)-1)^2 = 1 := by
  induction k with
  | zero => simp [t,u]
  | succ k ih =>
    push_cast
    rw [t_step, show (k:ℤ)+1-1 = k by ring, u_step (k:ℤ)]
    linear_combination ih

theorem pell_factorization (k : ℕ) :
    t (2*(k:ℤ))-1 = Polynomial.X*(1+Polynomial.X)*rho k := by
  have ht := congrArg (fun p : Polynomial ℤ => p.comp s)
    (Chebyshev.T_mul (R := ℤ) 2 k)
  simp [Chebyshev.T_two, comp_assoc, t] at ht
  change t (2*(k:ℤ)) = 2*t k^2-1 at ht
  rw [ht]
  have hp := pell k
  unfold rho s at *
  linear_combination 2*hp

theorem represents_w_pow (m : ℕ) : Represents (w^m) (t m) (2*u ((m:ℤ)-1)) := by
  induction m with
  | zero => simpa [t,u] using represents_one
  | succ m ih =>
    have hh := represents_mul_w ih
    have ht := t_step (m:ℤ)
    have hu := u_step (m:ℤ)
    push_cast
    rw [show (m:ℤ)+1-1 = m by ring]
    convert hh using 1
    · ring
    · rw [ht]; unfold s; ring
    · rw [hu]; unfold s; ring

theorem sectionEven_w_pow (m : ℕ) : sectionEven (w^m) = ev (t m) := by
  rw [represents_w_pow, sectionEven_add, sectionEven_expand,
    sectionEven_X_expand, add_zero]

theorem first_difference (k : ℕ) :
    transferIter (2*k) 1 - 1 = y*(1+y)*ev (rho k) := by
  simp only [transferIter, pow_zero, mul_one, sectionEven_w_pow]
  have hp := congrArg ev (pell_factorization k)
  simpa only [map_sub, map_one, map_mul, ev_X, map_add, Nat.cast_mul,
    Nat.cast_ofNat] using hp

noncomputable def initial (k : ℕ) : Polynomial ℤ := rho k + Round3.reduced (2*k) (rho k)

theorem initial_represents (k : ℕ) :
    Round2.transferDiff (2*k) 0 = y*(1+y)*ev (initial k) := by
  have hd := first_difference k
  have hl := lemma_R_unconditional (2*k) (rho k)
  have hs : sectionEven (w^(2*k)*(transferIter (2*k) 1-1)) =
      transferIter (2*k) 2-transferIter (2*k) 1 := by
    rw [mul_sub, sectionEven_sub]
    rfl
  rw [hd] at hs
  rw [hl] at hs
  unfold Round2.transferDiff initial
  simp only [transferIter, map_add] at *
  linear_combination hd - hs
end Ulas.Even5
