import UlasEven5Pell
set_option linter.unusedSimpArgs false
open Polynomial
namespace Ulas.Even5
open Ulas.Round4

theorem reducedPair_chebyshev (m : ℕ) :
    reducedPair m 0 = (2*u m, t ((m:ℤ)+1)) := by
  induction m with
  | zero => simp [reducedPair,u,t,s]
  | succ m ih =>
    simp only [reducedPair,ih,Prod.mk.injEq]
    push_cast
    have hu := u_step ((m:ℤ)+1)
    have ht := t_step ((m:ℤ)+1)
    rw [show (m:ℤ)+1-1 = m by ring] at hu ht
    constructor
    · rw [hu]; unfold s; ring
    · rw [ht]; unfold s; ring

theorem binA_chebyshev (m : ℕ) : binA m = 2*u m := by
  have h := congrArg Prod.fst (reducedPair_chebyshev m)
  simpa [reducedPair_zero] using h

theorem coeff_u (m E : ℕ) : (u m).coeff E =
    (2:ℤ)^(2*E)*(Nat.choose (m+E+1) (2*E+1):ℤ) := by
  have h := congrArg (fun p : Polynomial ℤ => p.coeff E) (binA_chebyshev m)
  rw [coeff_binA, coeff_ofNat_mul, pow_succ] at h
  nlinarith

theorem coeff_u_zero (k : ℕ) : (u ((k:ℤ)-1)).coeff 0 = k := by
  rw [coeff_zero_eq_eval_zero]
  simp [u,s,eval_comp,Chebyshev.U_eval_one]

theorem rho_zero (k : ℕ) : (rho k).coeff 0 = 8*(k:ℤ)^2 := by
  simp [rho,mul_coeff_zero,coeff_u_zero,pow_two]

/-- The integral binomial identity underlying the Kummer estimate. -/
theorem binomial_kummer_identity (k a : ℕ) (hk : 1 ≤ k) :
    (k+a).choose (2*a+1) * (2*a+1) * (2*a).choose a =
      k * (k+a).choose a * (k-1).choose a := by
  have h := Nat.choose_mul (n := k+a) (k := 2*a+1) (s := a) (by omega)
  have h1 := Nat.choose_mul_succ_eq (2*a) a
  have h2 := Nat.add_one_mul_choose_eq (k-1) a
  rw [show k-1+1=k by omega] at h2
  rw [show k+a-a=k by omega, show 2*a+1-a=a+1 by omega] at h
  rw [show 2*a+1-a=a+1 by omega] at h1
  nlinarith [congrArg (fun x : ℕ => x*(a+1)) h]
end Ulas.Even5
