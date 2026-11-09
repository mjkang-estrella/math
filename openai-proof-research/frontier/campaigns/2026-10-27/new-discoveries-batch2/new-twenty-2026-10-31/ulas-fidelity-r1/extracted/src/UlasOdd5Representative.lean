import UlasOdd5Factorization
set_option linter.unusedSimpArgs false
open PowerSeries Polynomial
namespace Ulas.Round5Odd
open Round4

theorem halfTerm_bridge (m E : ℕ) :
    sectionEven (w^m*((1+y)*y^E)) = (1+y)*ev (halfTerm m E) := by
  by_cases he : E%2=0
  · have hE : E=2*(E/2) := by omega
    conv_lhs => rw [hE]
    rw [halfAngle_even]
    simp [halfTerm,he]
  · have hE : E=2*(E/2)+1 := by omega
    conv_lhs => rw [hE]
    rw [halfAngle_odd]
    simp [halfTerm,he]

theorem halfTransfer_bridge (m : ℕ) (G : Polynomial ℤ) :
    sectionEven (w^m*((1+y)*ev G)) = (1+y)*ev (halfTransfer m G) := by
  classical
  rw [ev_eq_sum]
  simp only [Finset.mul_sum]
  have he (E : ℕ) : w^m*((1+y)*(PowerSeries.C (G.coeff E)*y^E)) =
      PowerSeries.C (G.coeff E)*(w^m*((1+y)*y^E)) := by ring
  simp only [he,sectionEven_sum,sectionEven_C_mul,halfTerm_bridge]
  simp only [halfTransfer,map_sum,map_mul,ev_C,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro E _
  ring

theorem halfTerm_constant (m E : ℕ) : (halfTerm m E).coeff 0 = if E=0 then 1 else 0 := by
  by_cases he : E%2=0
  · by_cases hz : E=0
    · simp [halfTerm,he,hz,(halfPair_constants m).1]
    · have hp : E/2 ≠ 0 := by omega
      simp [halfTerm,he,Polynomial.coeff_mul,Polynomial.coeff_X_pow,hp,Ne.symm hp,hz]
  · have hz : E ≠ 0 := by omega
    simp [halfTerm,he,Polynomial.coeff_mul,Polynomial.coeff_X_pow,hz]

theorem halfTransfer_constant (m : ℕ) (G : Polynomial ℤ) :
    (halfTransfer m G).coeff 0 = G.coeff 0 := by
  classical
  simp [halfTransfer,Polynomial.coeff_C_mul,halfTerm_constant]
  intro h; exact h.symm

/-- Full odd initialization and crude bound, tied to the actual series difference. -/
theorem odd_initialization (h : ℕ) : ∃ R : Polynomial ℤ,
    Round2.transferDiff (2*h+1) 0 = y*(1+y)*ev R ∧
    (∀ F, (2:ℤ)^(2*F+3) ∣ R.coeff F) := by
  let m := 2*h+1
  let G := (halfPair h).1^2
  have hz : (halfTransfer m G-G).coeff 0 = 0 := by simp [halfTransfer_constant]
  obtain ⟨Q,hQ⟩ := (Polynomial.X_dvd_iff).mpr hz
  refine ⟨2*Q,?_,?_⟩
  · have ht : transferIter m 1+1 = 2*(1+y)*ev G := by
      simpa [transferIter,m,G] using odd_square_factorization h
    have hb := halfTransfer_bridge m G
    have hdiff : Round2.transferDiff m 0 =
        sectionEven (w^m*(transferIter m 1+1))-(transferIter m 1+1) := by
      simp only [Round2.transferDiff,transferIter,sectionEven_add,mul_add,mul_one]
      ring
    rw [hdiff,ht]
    have hc : sectionEven (w^m*(2*(1+y)*ev G)) = 2*sectionEven (w^m*((1+y)*ev G)) := by
      have he : w^m*(2*(1+y)*ev G) = PowerSeries.C 2*(w^m*((1+y)*ev G)) := by norm_num; ring
      rw [he,sectionEven_C_mul]; norm_num
    rw [hc,hb]
    have he := congrArg ev hQ
    simp only [map_sub,map_mul,ev_X] at he
    simp only [map_mul,map_ofNat]
    linear_combination 2*(1+y)*he
  · intro F
    have hc := crude_halfAngle m G (halfAngle_square_scaled h) F
    rw [hQ,Polynomial.coeff_X_mul] at hc
    simpa only [show (2:Polynomial ℤ) = Polynomial.C 2 by norm_num,
      Polynomial.coeff_C_mul] using hc
end Ulas.Round5Odd
