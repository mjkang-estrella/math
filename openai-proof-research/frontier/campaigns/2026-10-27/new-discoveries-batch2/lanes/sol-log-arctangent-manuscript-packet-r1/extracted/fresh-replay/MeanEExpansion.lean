import MeanExpansion
import MeanFiniteCertificate
import ExpPolynomial
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
namespace LogArctangentMean
theorem exp_mul_nat (x : ℝ) (n : ℕ) : Real.exp (x*n) = Real.exp x^n := by rw [mul_comm, Real.exp_nat_mul]
noncomputable def EList : List ExpQuadratic := [⟨0,-87/68,0,-87/34⟩] ++ pairExp freq0 u0 v0 ++ pairExp freq1 u1 v1 ++ pairExp freq2 u2 v2 ++ pairExp freq3 u3 v3 ++ pairExp freq4 u4 v4 ++ pairExp freq5 u5 v5 ++ pairExp freq6 u6 v6 ++ pairExp freq7 u7 v7 ++ pairExp freq8 u8 v8 ++ pairExp freq9 u9 v9 ++ pairExp freq10 u10 v10 ++ pairExp freq11 u11 v11
theorem E_eq_evalExpList : E = evalExpList EList := by
  funext t
  simp only [E, U_expansion, V_expansion, UExpansion, VExpansion, EList, pairExp, evalExpList, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, ExpQuadratic.eval]
  dsimp [freq0, u0, v0, freq1, u1, v1, freq2, u2, v2, freq3, u3, v3, freq4, u4, v4, freq5, u5, v5, freq6, u6, v6, freq7, u7, v7, freq8, u8, v8, freq9, u9, v9, freq10, u10, v10, freq11, u11, v11]
  simp only [expGrid_m10_0, expGrid_m8_0, expGrid_m7_m1, expGrid_m7_1, expGrid_m5_m1, expGrid_m5_0, expGrid_m5_1, expGrid_m4_0, expGrid_m3_m1, expGrid_m3_1, expGrid_m2_m2, expGrid_m2_0, expGrid_m2_2, expGrid_m1_0, expGrid_0_m2, expGrid_0_m1, expGrid_0_0, expGrid_0_1, expGrid_0_2, expGrid_1_0, expGrid_2_m2, expGrid_2_0, expGrid_2_2, expGrid_3_m1, expGrid_3_1, expGrid_4_0, expGrid_5_m1, expGrid_5_0, expGrid_5_1, expGrid_7_m1, expGrid_7_1, expGrid_8_0, expGrid_10_0]
  have hneg0 : Real.exp (-((7:ℝ)+(1:ℝ)*d)*t) = (Real.exp (((7:ℝ)+(1:ℝ)*d)*t))⁻¹ := by rw [neg_mul, Real.exp_neg]
  have hneg1 : Real.exp (-((2:ℝ)+(2:ℝ)*d)*t) = (Real.exp (((2:ℝ)+(2:ℝ)*d)*t))⁻¹ := by rw [neg_mul, Real.exp_neg]
  have hneg2 : Real.exp (-((10:ℝ)+(0:ℝ)*d)*t) = (Real.exp (((10:ℝ)+(0:ℝ)*d)*t))⁻¹ := by rw [neg_mul, Real.exp_neg]
  have hneg3 : Real.exp (-((5:ℝ)+(1:ℝ)*d)*t) = (Real.exp (((5:ℝ)+(1:ℝ)*d)*t))⁻¹ := by rw [neg_mul, Real.exp_neg]
  have hneg4 : Real.exp (-((0:ℝ)+(2:ℝ)*d)*t) = (Real.exp (((0:ℝ)+(2:ℝ)*d)*t))⁻¹ := by rw [neg_mul, Real.exp_neg]
  have hneg5 : Real.exp (-((8:ℝ)+(0:ℝ)*d)*t) = (Real.exp (((8:ℝ)+(0:ℝ)*d)*t))⁻¹ := by rw [neg_mul, Real.exp_neg]
  have hneg6 : Real.exp (-((3:ℝ)+(1:ℝ)*d)*t) = (Real.exp (((3:ℝ)+(1:ℝ)*d)*t))⁻¹ := by rw [neg_mul, Real.exp_neg]
  have hneg7 : Real.exp (-((-2:ℝ)+(2:ℝ)*d)*t) = (Real.exp (((-2:ℝ)+(2:ℝ)*d)*t))⁻¹ := by rw [neg_mul, Real.exp_neg]
  have hneg8 : Real.exp (-((7:ℝ)+(-1:ℝ)*d)*t) = (Real.exp (((7:ℝ)+(-1:ℝ)*d)*t))⁻¹ := by rw [neg_mul, Real.exp_neg]
  have hneg9 : Real.exp (-((2:ℝ)+(0:ℝ)*d)*t) = (Real.exp (((2:ℝ)+(0:ℝ)*d)*t))⁻¹ := by rw [neg_mul, Real.exp_neg]
  have hneg10 : Real.exp (-((-3:ℝ)+(1:ℝ)*d)*t) = (Real.exp (((-3:ℝ)+(1:ℝ)*d)*t))⁻¹ := by rw [neg_mul, Real.exp_neg]
  have hneg11 : Real.exp (-((5:ℝ)+(-1:ℝ)*d)*t) = (Real.exp (((5:ℝ)+(-1:ℝ)*d)*t))⁻¹ := by rw [neg_mul, Real.exp_neg]
  simp only [hneg0, hneg1, hneg2, hneg3, hneg4, hneg5, hneg6, hneg7, hneg8, hneg9, hneg10, hneg11]
  simp only [expGrid_m10_0, expGrid_m8_0, expGrid_m7_m1, expGrid_m7_1, expGrid_m5_m1, expGrid_m5_0, expGrid_m5_1, expGrid_m4_0, expGrid_m3_m1, expGrid_m3_1, expGrid_m2_m2, expGrid_m2_0, expGrid_m2_2, expGrid_m1_0, expGrid_0_m2, expGrid_0_m1, expGrid_0_0, expGrid_0_1, expGrid_0_2, expGrid_1_0, expGrid_2_m2, expGrid_2_0, expGrid_2_2, expGrid_3_m1, expGrid_3_1, expGrid_4_0, expGrid_5_m1, expGrid_5_0, expGrid_5_1, expGrid_7_m1, expGrid_7_1, expGrid_8_0, expGrid_10_0]
  norm_num
  field_simp [Real.exp_ne_zero]
  ring
theorem evalExpList_append (xs ys : List ExpQuadratic) (t : ℝ) : evalExpList (xs++ys) t = evalExpList xs t + evalExpList ys t := by simp [evalExpList]
theorem expListJet_append (xs ys : List ExpQuadratic) (n : ℕ) : expListJet n (xs++ys) = expListJet n xs ++ expListJet n ys := by simp only [expListJet_map, List.map_append]
theorem E_derivative24 (t : ℝ) : iteratedDeriv 24 E t / 2 =
  (c0_0*Real.cosh (freq0*t)+t*(c0_1+c0_2)*freq0*Real.sinh (freq0*t)+t^2*c0_2*freq0^2*Real.cosh (freq0*t)) +
  (c1_0*Real.cosh (freq1*t)+t*(c1_1+c1_2)*freq1*Real.sinh (freq1*t)+t^2*c1_2*freq1^2*Real.cosh (freq1*t)) +
  (c2_0*Real.cosh (freq2*t)+t*(c2_1+c2_2)*freq2*Real.sinh (freq2*t)+t^2*c2_2*freq2^2*Real.cosh (freq2*t)) +
  (c3_0*Real.cosh (freq3*t)+t*(c3_1+c3_2)*freq3*Real.sinh (freq3*t)+t^2*c3_2*freq3^2*Real.cosh (freq3*t)) +
  (c4_0*Real.cosh (freq4*t)+t*(c4_1+c4_2)*freq4*Real.sinh (freq4*t)+t^2*c4_2*freq4^2*Real.cosh (freq4*t)) +
  (c5_0*Real.cosh (freq5*t)+t*(c5_1+c5_2)*freq5*Real.sinh (freq5*t)+t^2*c5_2*freq5^2*Real.cosh (freq5*t)) +
  (c6_0*Real.cosh (freq6*t)+t*(c6_1+c6_2)*freq6*Real.sinh (freq6*t)+t^2*c6_2*freq6^2*Real.cosh (freq6*t)) +
  (c7_0*Real.cosh (freq7*t)+t*(c7_1+c7_2)*freq7*Real.sinh (freq7*t)+t^2*c7_2*freq7^2*Real.cosh (freq7*t)) +
  (c8_0*Real.cosh (freq8*t)+t*(c8_1+c8_2)*freq8*Real.sinh (freq8*t)+t^2*c8_2*freq8^2*Real.cosh (freq8*t)) +
  (c9_0*Real.cosh (freq9*t)+t*(c9_1+c9_2)*freq9*Real.sinh (freq9*t)+t^2*c9_2*freq9^2*Real.cosh (freq9*t)) +
  (c10_0*Real.cosh (freq10*t)+t*(c10_1+c10_2)*freq10*Real.sinh (freq10*t)+t^2*c10_2*freq10^2*Real.cosh (freq10*t)) +
  (c11_0*Real.cosh (freq11*t)+t*(c11_1+c11_2)*freq11*Real.sinh (freq11*t)+t^2*c11_2*freq11^2*Real.cosh (freq11*t)) := by
  rw [E_eq_evalExpList, iteratedDeriv_evalExpList]
  simp only [EList, expListJet_append, evalExpList_append, pairExp_derivative24]
  simp only [expListJet_map, List.map_cons, List.map_nil, evalExpList, List.sum_cons, List.sum_nil, ExpQuadratic.jet24, ExpQuadratic.jetFormula, ExpQuadratic.eval]
  norm_num
  dsimp [c0_0, c0_1, c0_2, c1_0, c1_1, c1_2, c2_0, c2_1, c2_2, c3_0, c3_1, c3_2, c4_0, c4_1, c4_2, c5_0, c5_1, c5_2, c6_0, c6_1, c6_2, c7_0, c7_1, c7_2, c8_0, c8_1, c8_2, c9_0, c9_1, c9_2, c10_0, c10_1, c10_2, c11_0, c11_1, c11_2]
  ring
end LogArctangentMean
