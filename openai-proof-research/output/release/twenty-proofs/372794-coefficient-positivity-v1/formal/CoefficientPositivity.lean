import Mathlib

noncomputable section

namespace CoefficientPositivity
open MvPolynomial
abbrev Poly := MvPolynomial (Fin 2) ℤ

def NonnegCoeffs (p : Poly) : Prop := ∀ d, 0 ≤ p.coeff d
lemma nn_add {p q : Poly} (hp : NonnegCoeffs p) (hq : NonnegCoeffs q) :
    NonnegCoeffs (p + q) := by
  intro d
  change 0 ≤ p.coeff d + q.coeff d
  exact add_nonneg (hp d) (hq d)
lemma nn_mul {p q : Poly} (hp : NonnegCoeffs p) (hq : NonnegCoeffs q) :
    NonnegCoeffs (p * q) := by
  intro d
  rw [coeff_mul]
  exact Finset.sum_nonneg fun z _ => mul_nonneg (hp z.1) (hq z.2)
lemma nn_C {z : ℤ} (hz : 0 ≤ z) : NonnegCoeffs (C z) := by
  intro d
  simp only [coeff_C]
  split <;> simp_all
lemma nn_X (i : Fin 2) : NonnegCoeffs (X i) := by
  intro d
  rw [coeff_X]
  split <;> norm_num
lemma nn_nat (n : ℕ) : NonnegCoeffs (n : Poly) := by
  simpa using nn_C (z := (n : ℤ)) (by omega)
lemma nn_pow {p : Poly} (hp : NonnegCoeffs p) (n : ℕ) : NonnegCoeffs (p ^ n) := by
  induction n with
  | zero => simpa using nn_nat 1
  | succ n ih => simpa only [pow_succ] using nn_mul ih hp

-- Homogeneous algebra, valid before substituting x = 1 + a*t.
def A (x t : Poly) := (x + 3*t)*(x+2*t)
def B (x t : Poly) := (x+t)*(x+4*t)
def Cc (x t : Poly) := (x+t)*(x+2*t)
def D (x t : Poly) := x*(x+3*t)
def K (x t : Poly) := 8*t^4*(x+2*t)
def H (x t : Poly) (n : ℕ) :=
  (x+2*t)*(A x t)^n - (x+4*t)*(B x t)^n +
    (x+2*t)*(Cc x t)^n - x*(D x t)^n
def S1 (x t : Poly) (n : ℕ) := H x t (n+1) - D x t * H x t n
def S2 (x t : Poly) (n : ℕ) := S1 x t (n+1) - Cc x t * S1 x t n

lemma initial (x t : Poly) : H x t 0 = 0 ∧ S1 x t 0 = 0 ∧ S2 x t 0 = K x t := by
  dsimp [S2, S1, H, A, B, Cc, D, K]
  constructor
  · ring
  constructor <;> ring

lemma s2_step (x t : Poly) (n : ℕ) :
    S2 x t (n+1) = B x t * S2 x t n + K x t * (A x t)^(n+1) := by
  simp only [S2, S1, H, pow_succ]
  dsimp [A, B, Cc, D, K]
  ring

lemma h_step (x t : Poly) (n : ℕ) :
    H x t (n+1) = D x t * H x t n + S1 x t n := by
  dsimp [S1]
  ring
lemma s1_step (x t : Poly) (n : ℕ) :
    S1 x t (n+1) = Cc x t * S1 x t n + S2 x t n := by
  dsimp [S2]
  ring

lemma homogeneous_nonnegative (x t : Poly) (hx : NonnegCoeffs x) (ht : NonnegCoeffs t)
    (n : ℕ) : NonnegCoeffs (H x t n) := by
  have hl (k : ℕ) : NonnegCoeffs (x + k*t) := nn_add hx (nn_mul (nn_nat k) ht)
  have ha : NonnegCoeffs (A x t) := nn_mul (hl 3) (hl 2)
  have hb : NonnegCoeffs (B x t) := by simpa [B] using nn_mul (hl 1) (hl 4)
  have hc : NonnegCoeffs (Cc x t) := by simpa [Cc] using nn_mul (hl 1) (hl 2)
  have hd : NonnegCoeffs (D x t) := nn_mul hx (hl 3)
  have hk : NonnegCoeffs (K x t) := nn_mul (nn_mul (nn_nat 8) (nn_pow ht 4)) (hl 2)
  have all (m : ℕ) : NonnegCoeffs (H x t m) ∧ NonnegCoeffs (S1 x t m) ∧
      NonnegCoeffs (S2 x t m) := by
    induction m with
    | zero =>
      rcases initial x t with ⟨hh, hs, hss⟩
      rw [hh, hs, hss]
      exact ⟨by simpa using nn_nat 0, by simpa using nn_nat 0, hk⟩
    | succ m ih =>
      rw [h_step, s1_step, s2_step]
      exact ⟨nn_add (nn_mul hd ih.1) ih.2.1,
        nn_add (nn_mul hc ih.2.1) ih.2.2,
        nn_add (nn_mul hb ih.2.2) (nn_mul hk (nn_pow ha (m+1)))⟩
  exact (all n).1

def sourcePolynomial (r : ℕ) : Poly :=
  (1+(3+X 1)*X 0)^r * ((1+(2+X 1)*X 0)^(r+1) - (1+X 1*X 0)^(r+1)) -
  (1+(1+X 1)*X 0)^r * ((1+(4+X 1)*X 0)^(r+1) - (1+(2+X 1)*X 0)^(r+1))

lemma source_bridge (r : ℕ) : sourcePolynomial r = H (1+X 1*X 0) (X 0) r := by
  simp only [sourcePolynomial, H, A, B, Cc, D, mul_pow, pow_succ]
  ring

theorem all_coefficients_nonnegative (r : ℕ) (d : Fin 2 →₀ ℕ) :
    0 ≤ (sourcePolynomial r).coeff d := by
  rw [source_bridge]
  exact homogeneous_nonnegative _ _ (nn_add (nn_nat 1) (nn_mul (nn_X 1) (nn_X 0)))
    (nn_X 0) r d
end CoefficientPositivity
