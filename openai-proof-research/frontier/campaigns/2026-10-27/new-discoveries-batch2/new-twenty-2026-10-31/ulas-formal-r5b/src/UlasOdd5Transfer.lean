import UlasOdd5HalfAngle
set_option linter.unusedSimpArgs false
open PowerSeries Polynomial
namespace Ulas.Round5Odd
open Round4

theorem y_square : y^2 = w*expand 2 (by decide) y := by
  rw [y, map_mul, PowerSeries.expand_X, geom_expand, w]
  have h := geom_split
  calc
    _ = PowerSeries.X^2*geomStep 1*geomStep 1 := by ring
    _ = _ := by rw [h]; ring

theorem even_y_power (e : ℕ) : y^(2*e) = w^e*expand 2 (by decide) (y^e) := by
  rw [pow_mul, y_square, mul_pow, map_pow]

theorem halfAngle_even (m e : ℕ) :
    sectionEven (w^m*((1+y)*y^(2*e))) =
      (1+y)*ev (Polynomial.X^e*(halfPair (m+e)).1) := by
  rw [even_y_power]
  have he : w^m*((1+y)*(w^e*expand 2 (by decide) (y^e))) =
      (w^(m+e)*(1+y))*expand 2 (by decide) (y^e) := by rw [pow_add]; ring
  rw [he, sectionEven_mul_expand, halfAngle_constant]
  simp only [map_mul, map_pow, ev_X]
  ring

theorem halfAngle_odd (m e : ℕ) :
    sectionEven (w^m*((1+y)*y^(2*e+1))) =
      (1+y)*ev (2*Polynomial.X^(e+1)*(halfPair (m+e)).2) := by
  rw [pow_succ, even_y_power]
  have he : w^m*((1+y)*(w^e*expand 2 (by decide) (y^e)*y)) =
      (y*(w^(m+e)*(1+y)))*expand 2 (by decide) (y^e) := by rw [pow_add]; ring
  rw [he, sectionEven_mul_expand]
  have h := represents_mul_y (halfPair_correct (m+e))
  have hs : sectionEven (y*(w^(m+e)*(1+y))) =
      ev (Polynomial.X*((1+Polynomial.X)*(halfPair (m+e)).1)+
        Polynomial.X*(1+Polynomial.X)*(2*(halfPair (m+e)).2-(halfPair (m+e)).1)) := by
    rw [h, sectionEven_add, sectionEven_expand, sectionEven_X_expand, add_zero]
  rw [hs]
  have hp : Polynomial.X*((1+Polynomial.X)*(halfPair (m+e)).1)+
        Polynomial.X*(1+Polynomial.X)*(2*(halfPair (m+e)).2-(halfPair (m+e)).1) =
        (1+Polynomial.X)*(2*Polynomial.X*(halfPair (m+e)).2) := by ring
  rw [hp]
  simp only [map_mul, map_pow, ev_X, map_add, map_one, map_ofNat]
  ring
end Ulas.Round5Odd
