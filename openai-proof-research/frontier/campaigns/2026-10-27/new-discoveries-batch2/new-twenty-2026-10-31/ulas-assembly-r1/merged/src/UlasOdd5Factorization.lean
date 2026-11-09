import UlasOdd5Crude
set_option linter.unusedSimpArgs false
open PowerSeries Polynomial
namespace Ulas.Round5Odd
open Round4

theorem halfPair_pell (h : ℕ) :
    (1+Polynomial.X)*(halfPair h).1^2 -
      Polynomial.X*(2*(halfPair h).2-(halfPair h).1)^2 = 1 := by
  induction h with
  | zero => norm_num [halfPair]
  | succ h ih =>
    calc
      _ = (1+Polynomial.X)*(halfPair h).1^2 -
          Polynomial.X*(2*(halfPair h).2-(halfPair h).1)^2 := by simp [halfPair]; ring
      _ = 1 := ih

theorem sectionEven_square {f : PowerSeries ℤ} {a b : Polynomial ℤ}
    (hf : Represents f a b) :
    sectionEven (f^2) = ev a^2 + PowerSeries.X*((1+y)*ev b)^2 := by
  rw [hf]
  have he : (expand 2 (by decide) (ev a)+PowerSeries.X*expand 2 (by decide) ((1+y)*ev b))^2 =
      expand 2 (by decide) (ev a^2+PowerSeries.X*((1+y)*ev b)^2) +
      PowerSeries.X*expand 2 (by decide) (2*ev a*((1+y)*ev b)) := by
    simp only [map_add,map_mul,map_pow,map_ofNat,PowerSeries.expand_X]
    ring
  rw [he, sectionEven_add, sectionEven_expand, sectionEven_X_expand, add_zero]

/-- Odd half-angle square factorization, proved for the actual series operator. -/
theorem odd_square_factorization (h : ℕ) :
    sectionEven (w^(2*h+1))+1 = 2*(1+y)*ev ((halfPair h).1^2) := by
  have hg : (1-PowerSeries.X)*(1+y) = 1 := by
    linear_combination -X_one_add_y
  have hw : (1-PowerSeries.X^2)*(1+y)^2 = w := by
    calc
      _ = ((1-PowerSeries.X)*(1+y))*((1+PowerSeries.X)*(1+y)) := by ring
      _ = w := by rw [hg, one_mul, one_add_y]; rfl
  have hf : w^(2*h+1) = (1-PowerSeries.X^2)*(w^h*(1+y))^2 := by
    rw [mul_pow, ← mul_assoc, mul_comm (1-PowerSeries.X^2), mul_assoc, hw,
      ← pow_mul, ← pow_succ]
    rw [Nat.mul_comm h 2]
  have hs : sectionEven (w^(2*h+1)) = (1-PowerSeries.X)*
      (ev ((1+Polynomial.X)*(halfPair h).1)^2 +
        PowerSeries.X*((1+y)*ev (2*(halfPair h).2-(halfPair h).1))^2) := by
    rw [hf]
    have he : (1-PowerSeries.X^2)*(w^h*(1+y))^2 =
        (w^h*(1+y))^2*expand 2 (by decide) (1-PowerSeries.X) := by
      simp only [map_sub,map_one,PowerSeries.expand_X]; ring
    rw [he, sectionEven_mul_expand, sectionEven_square (halfPair_correct h), mul_comm]
  have hp := congrArg ev (halfPair_pell h)
  simp only [map_sub,map_mul,map_add,map_one,map_pow,map_ofNat,ev_X] at hp
  rw [hs]
  simp only [map_mul,map_add,map_one,ev_X,map_pow,map_sub,map_ofNat]
  have hx := X_one_add_y
  calc
    _ = (1+y)*(ev (halfPair h).1)^2+y*(2*ev (halfPair h).2-ev (halfPair h).1)^2+1 := by
      linear_combination (1+y)*((ev (halfPair h).1)^2 +
        PowerSeries.X*(2*ev (halfPair h).2-ev (halfPair h).1)^2)*hg +
        (2*ev (halfPair h).2-ev (halfPair h).1)^2*hx
    _ = _ := by linear_combination -hp
end Ulas.Round5Odd
