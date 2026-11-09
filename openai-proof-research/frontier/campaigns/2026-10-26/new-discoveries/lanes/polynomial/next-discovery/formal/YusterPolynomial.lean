import YusterCoefficients

open Finset Polynomial
namespace YusterCounterexample

def rhoEval (k : ℕ) (x : ℚ) : ℚ :=
  ∑ j ∈ range k, (-1 : ℚ)^j * j.factorial * sourceC k (k+1) (j+2) *
    ((x^k-1)^(k-j-1)*x^(k*j+k)-(x^k-1)^k)

def sigmaEval (k : ℕ) (x : ℚ) : ℚ :=
  ∑ j ∈ range k, (-1 : ℚ)^j * (k+1).choose (j+2) *
    (x^(j+1)*(x-1)^(k-j-1)*(∑ i ∈ range k, x^i)^k-(x^k-1)^k)

noncomputable def rho (k : ℕ) : ℚ[X] :=
  ∑ j ∈ range k, C ((-1 : ℚ)^j * j.factorial * sourceC k (k+1) (j+2)) *
    ((X^k-1)^(k-j-1)*X^(k*j+k)-(X^k-1)^k)

noncomputable def sigma (k : ℕ) : ℚ[X] :=
  ∑ j ∈ range k, C ((-1 : ℚ)^j * (k+1).choose (j+2)) *
    (X^(j+1)*(X-1)^(k-j-1)*(∑ i ∈ range k, X^i)^k-(X^k-1)^k)

noncomputable def sourceP (k : ℕ) (a : ℝ) : ℝ[X] :=
  C a * (rho k).map (Rat.castHom ℝ) - (sigma k).map (Rat.castHom ℝ)

lemma rho_eval (k : ℕ) (x : ℚ) : (rho k).eval x = rhoEval k x := by
  simp [rho, rhoEval, eval_finsetSum]

lemma sigma_eval (k : ℕ) (x : ℚ) : (sigma k).eval x = sigmaEval k x := by
  simp [sigma, sigmaEval, eval_finsetSum]

lemma sourceP_eval (k : ℕ) (a : ℝ) (x : ℚ) :
    (sourceP k a).eval (x:ℝ) = a * (rhoEval k x : ℝ) - (sigmaEval k x : ℝ) := by
  simp only [sourceP, eval_sub, eval_mul, eval_C]
  rw [← rho_eval, ← sigma_eval]
  have hr := eval₂_at_apply (p := rho k) (Rat.castHom ℝ) x
  have hs := eval₂_at_apply (p := sigma k) (Rat.castHom ℝ) x
  change (rho k).eval₂ (Rat.castHom ℝ) (x:ℝ) = (↑((rho k).eval x) : ℝ) at hr
  change (sigma k).eval₂ (Rat.castHom ℝ) (x:ℝ) = (↑((sigma k).eval x) : ℝ) at hs
  rw [eval_map, eval_map, hr, hs]

end YusterCounterexample
