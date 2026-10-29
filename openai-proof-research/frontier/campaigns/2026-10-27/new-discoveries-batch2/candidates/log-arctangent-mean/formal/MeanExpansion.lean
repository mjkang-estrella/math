import MeanDerivatives
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
namespace LogArctangentMean
theorem expGrid_m10_0 (t : ℝ) : Real.exp (((-10:ℝ)+(0:ℝ)*d)*t) = ((Real.exp t)^10)⁻¹ * (Real.exp (d*t))^0 := by
  rw [show ((-10:ℝ)+(0:ℝ)*d)*t = -( (10:ℕ)*(t) ) + (0:ℕ)*(d*t) by ring, Real.exp_add]
  simp only [Real.exp_neg, Real.exp_nat_mul]
theorem expGrid_m8_0 (t : ℝ) : Real.exp (((-8:ℝ)+(0:ℝ)*d)*t) = ((Real.exp t)^8)⁻¹ * (Real.exp (d*t))^0 := by
  rw [show ((-8:ℝ)+(0:ℝ)*d)*t = -( (8:ℕ)*(t) ) + (0:ℕ)*(d*t) by ring, Real.exp_add]
  simp only [Real.exp_neg, Real.exp_nat_mul]
theorem expGrid_m7_m1 (t : ℝ) : Real.exp (((-7:ℝ)+(-1:ℝ)*d)*t) = ((Real.exp t)^7)⁻¹ * ((Real.exp (d*t))^1)⁻¹ := by
  rw [show ((-7:ℝ)+(-1:ℝ)*d)*t = -( (7:ℕ)*(t) ) + -( (1:ℕ)*(d*t) ) by ring, Real.exp_add]
  simp only [Real.exp_neg, Real.exp_nat_mul]
theorem expGrid_m7_1 (t : ℝ) : Real.exp (((-7:ℝ)+(1:ℝ)*d)*t) = ((Real.exp t)^7)⁻¹ * (Real.exp (d*t))^1 := by
  rw [show ((-7:ℝ)+(1:ℝ)*d)*t = -( (7:ℕ)*(t) ) + (1:ℕ)*(d*t) by ring, Real.exp_add]
  simp only [Real.exp_neg, Real.exp_nat_mul]
theorem expGrid_m5_m1 (t : ℝ) : Real.exp (((-5:ℝ)+(-1:ℝ)*d)*t) = ((Real.exp t)^5)⁻¹ * ((Real.exp (d*t))^1)⁻¹ := by
  rw [show ((-5:ℝ)+(-1:ℝ)*d)*t = -( (5:ℕ)*(t) ) + -( (1:ℕ)*(d*t) ) by ring, Real.exp_add]
  simp only [Real.exp_neg, Real.exp_nat_mul]
theorem expGrid_m5_0 (t : ℝ) : Real.exp (((-5:ℝ)+(0:ℝ)*d)*t) = ((Real.exp t)^5)⁻¹ * (Real.exp (d*t))^0 := by
  rw [show ((-5:ℝ)+(0:ℝ)*d)*t = -( (5:ℕ)*(t) ) + (0:ℕ)*(d*t) by ring, Real.exp_add]
  simp only [Real.exp_neg, Real.exp_nat_mul]
theorem expGrid_m5_1 (t : ℝ) : Real.exp (((-5:ℝ)+(1:ℝ)*d)*t) = ((Real.exp t)^5)⁻¹ * (Real.exp (d*t))^1 := by
  rw [show ((-5:ℝ)+(1:ℝ)*d)*t = -( (5:ℕ)*(t) ) + (1:ℕ)*(d*t) by ring, Real.exp_add]
  simp only [Real.exp_neg, Real.exp_nat_mul]
theorem expGrid_m4_0 (t : ℝ) : Real.exp (((-4:ℝ)+(0:ℝ)*d)*t) = ((Real.exp t)^4)⁻¹ * (Real.exp (d*t))^0 := by
  rw [show ((-4:ℝ)+(0:ℝ)*d)*t = -( (4:ℕ)*(t) ) + (0:ℕ)*(d*t) by ring, Real.exp_add]
  simp only [Real.exp_neg, Real.exp_nat_mul]
theorem expGrid_m3_m1 (t : ℝ) : Real.exp (((-3:ℝ)+(-1:ℝ)*d)*t) = ((Real.exp t)^3)⁻¹ * ((Real.exp (d*t))^1)⁻¹ := by
  rw [show ((-3:ℝ)+(-1:ℝ)*d)*t = -( (3:ℕ)*(t) ) + -( (1:ℕ)*(d*t) ) by ring, Real.exp_add]
  simp only [Real.exp_neg, Real.exp_nat_mul]
theorem expGrid_m3_1 (t : ℝ) : Real.exp (((-3:ℝ)+(1:ℝ)*d)*t) = ((Real.exp t)^3)⁻¹ * (Real.exp (d*t))^1 := by
  rw [show ((-3:ℝ)+(1:ℝ)*d)*t = -( (3:ℕ)*(t) ) + (1:ℕ)*(d*t) by ring, Real.exp_add]
  simp only [Real.exp_neg, Real.exp_nat_mul]
theorem expGrid_m2_m2 (t : ℝ) : Real.exp (((-2:ℝ)+(-2:ℝ)*d)*t) = ((Real.exp t)^2)⁻¹ * ((Real.exp (d*t))^2)⁻¹ := by
  rw [show ((-2:ℝ)+(-2:ℝ)*d)*t = -( (2:ℕ)*(t) ) + -( (2:ℕ)*(d*t) ) by ring, Real.exp_add]
  simp only [Real.exp_neg, Real.exp_nat_mul]
theorem expGrid_m2_0 (t : ℝ) : Real.exp (((-2:ℝ)+(0:ℝ)*d)*t) = ((Real.exp t)^2)⁻¹ * (Real.exp (d*t))^0 := by
  rw [show ((-2:ℝ)+(0:ℝ)*d)*t = -( (2:ℕ)*(t) ) + (0:ℕ)*(d*t) by ring, Real.exp_add]
  simp only [Real.exp_neg, Real.exp_nat_mul]
theorem expGrid_m2_2 (t : ℝ) : Real.exp (((-2:ℝ)+(2:ℝ)*d)*t) = ((Real.exp t)^2)⁻¹ * (Real.exp (d*t))^2 := by
  rw [show ((-2:ℝ)+(2:ℝ)*d)*t = -( (2:ℕ)*(t) ) + (2:ℕ)*(d*t) by ring, Real.exp_add]
  simp only [Real.exp_neg, Real.exp_nat_mul]
theorem expGrid_m1_0 (t : ℝ) : Real.exp (((-1:ℝ)+(0:ℝ)*d)*t) = ((Real.exp t)^1)⁻¹ * (Real.exp (d*t))^0 := by
  rw [show ((-1:ℝ)+(0:ℝ)*d)*t = -( (1:ℕ)*(t) ) + (0:ℕ)*(d*t) by ring, Real.exp_add]
  simp only [Real.exp_neg, Real.exp_nat_mul]
theorem expGrid_0_m2 (t : ℝ) : Real.exp (((0:ℝ)+(-2:ℝ)*d)*t) = (Real.exp t)^0 * ((Real.exp (d*t))^2)⁻¹ := by
  rw [show ((0:ℝ)+(-2:ℝ)*d)*t = (0:ℕ)*(t) + -( (2:ℕ)*(d*t) ) by ring, Real.exp_add]
  simp only [Real.exp_neg, Real.exp_nat_mul]
theorem expGrid_0_m1 (t : ℝ) : Real.exp (((0:ℝ)+(-1:ℝ)*d)*t) = (Real.exp t)^0 * ((Real.exp (d*t))^1)⁻¹ := by
  rw [show ((0:ℝ)+(-1:ℝ)*d)*t = (0:ℕ)*(t) + -( (1:ℕ)*(d*t) ) by ring, Real.exp_add]
  simp only [Real.exp_neg, Real.exp_nat_mul]
theorem expGrid_0_0 (t : ℝ) : Real.exp (((0:ℝ)+(0:ℝ)*d)*t) = (Real.exp t)^0 * (Real.exp (d*t))^0 := by
  rw [show ((0:ℝ)+(0:ℝ)*d)*t = (0:ℕ)*(t) + (0:ℕ)*(d*t) by ring, Real.exp_add]
  simp only [Real.exp_neg, Real.exp_nat_mul]
theorem expGrid_0_1 (t : ℝ) : Real.exp (((0:ℝ)+(1:ℝ)*d)*t) = (Real.exp t)^0 * (Real.exp (d*t))^1 := by
  rw [show ((0:ℝ)+(1:ℝ)*d)*t = (0:ℕ)*(t) + (1:ℕ)*(d*t) by ring, Real.exp_add]
  simp only [Real.exp_neg, Real.exp_nat_mul]
theorem expGrid_0_2 (t : ℝ) : Real.exp (((0:ℝ)+(2:ℝ)*d)*t) = (Real.exp t)^0 * (Real.exp (d*t))^2 := by
  rw [show ((0:ℝ)+(2:ℝ)*d)*t = (0:ℕ)*(t) + (2:ℕ)*(d*t) by ring, Real.exp_add]
  simp only [Real.exp_neg, Real.exp_nat_mul]
theorem expGrid_1_0 (t : ℝ) : Real.exp (((1:ℝ)+(0:ℝ)*d)*t) = (Real.exp t)^1 * (Real.exp (d*t))^0 := by
  rw [show ((1:ℝ)+(0:ℝ)*d)*t = (1:ℕ)*(t) + (0:ℕ)*(d*t) by ring, Real.exp_add]
  simp only [Real.exp_neg, Real.exp_nat_mul]
theorem expGrid_2_m2 (t : ℝ) : Real.exp (((2:ℝ)+(-2:ℝ)*d)*t) = (Real.exp t)^2 * ((Real.exp (d*t))^2)⁻¹ := by
  rw [show ((2:ℝ)+(-2:ℝ)*d)*t = (2:ℕ)*(t) + -( (2:ℕ)*(d*t) ) by ring, Real.exp_add]
  simp only [Real.exp_neg, Real.exp_nat_mul]
theorem expGrid_2_0 (t : ℝ) : Real.exp (((2:ℝ)+(0:ℝ)*d)*t) = (Real.exp t)^2 * (Real.exp (d*t))^0 := by
  rw [show ((2:ℝ)+(0:ℝ)*d)*t = (2:ℕ)*(t) + (0:ℕ)*(d*t) by ring, Real.exp_add]
  simp only [Real.exp_neg, Real.exp_nat_mul]
theorem expGrid_2_2 (t : ℝ) : Real.exp (((2:ℝ)+(2:ℝ)*d)*t) = (Real.exp t)^2 * (Real.exp (d*t))^2 := by
  rw [show ((2:ℝ)+(2:ℝ)*d)*t = (2:ℕ)*(t) + (2:ℕ)*(d*t) by ring, Real.exp_add]
  simp only [Real.exp_neg, Real.exp_nat_mul]
theorem expGrid_3_m1 (t : ℝ) : Real.exp (((3:ℝ)+(-1:ℝ)*d)*t) = (Real.exp t)^3 * ((Real.exp (d*t))^1)⁻¹ := by
  rw [show ((3:ℝ)+(-1:ℝ)*d)*t = (3:ℕ)*(t) + -( (1:ℕ)*(d*t) ) by ring, Real.exp_add]
  simp only [Real.exp_neg, Real.exp_nat_mul]
theorem expGrid_3_1 (t : ℝ) : Real.exp (((3:ℝ)+(1:ℝ)*d)*t) = (Real.exp t)^3 * (Real.exp (d*t))^1 := by
  rw [show ((3:ℝ)+(1:ℝ)*d)*t = (3:ℕ)*(t) + (1:ℕ)*(d*t) by ring, Real.exp_add]
  simp only [Real.exp_neg, Real.exp_nat_mul]
theorem expGrid_4_0 (t : ℝ) : Real.exp (((4:ℝ)+(0:ℝ)*d)*t) = (Real.exp t)^4 * (Real.exp (d*t))^0 := by
  rw [show ((4:ℝ)+(0:ℝ)*d)*t = (4:ℕ)*(t) + (0:ℕ)*(d*t) by ring, Real.exp_add]
  simp only [Real.exp_neg, Real.exp_nat_mul]
theorem expGrid_5_m1 (t : ℝ) : Real.exp (((5:ℝ)+(-1:ℝ)*d)*t) = (Real.exp t)^5 * ((Real.exp (d*t))^1)⁻¹ := by
  rw [show ((5:ℝ)+(-1:ℝ)*d)*t = (5:ℕ)*(t) + -( (1:ℕ)*(d*t) ) by ring, Real.exp_add]
  simp only [Real.exp_neg, Real.exp_nat_mul]
theorem expGrid_5_0 (t : ℝ) : Real.exp (((5:ℝ)+(0:ℝ)*d)*t) = (Real.exp t)^5 * (Real.exp (d*t))^0 := by
  rw [show ((5:ℝ)+(0:ℝ)*d)*t = (5:ℕ)*(t) + (0:ℕ)*(d*t) by ring, Real.exp_add]
  simp only [Real.exp_neg, Real.exp_nat_mul]
theorem expGrid_5_1 (t : ℝ) : Real.exp (((5:ℝ)+(1:ℝ)*d)*t) = (Real.exp t)^5 * (Real.exp (d*t))^1 := by
  rw [show ((5:ℝ)+(1:ℝ)*d)*t = (5:ℕ)*(t) + (1:ℕ)*(d*t) by ring, Real.exp_add]
  simp only [Real.exp_neg, Real.exp_nat_mul]
theorem expGrid_7_m1 (t : ℝ) : Real.exp (((7:ℝ)+(-1:ℝ)*d)*t) = (Real.exp t)^7 * ((Real.exp (d*t))^1)⁻¹ := by
  rw [show ((7:ℝ)+(-1:ℝ)*d)*t = (7:ℕ)*(t) + -( (1:ℕ)*(d*t) ) by ring, Real.exp_add]
  simp only [Real.exp_neg, Real.exp_nat_mul]
theorem expGrid_7_1 (t : ℝ) : Real.exp (((7:ℝ)+(1:ℝ)*d)*t) = (Real.exp t)^7 * (Real.exp (d*t))^1 := by
  rw [show ((7:ℝ)+(1:ℝ)*d)*t = (7:ℕ)*(t) + (1:ℕ)*(d*t) by ring, Real.exp_add]
  simp only [Real.exp_neg, Real.exp_nat_mul]
theorem expGrid_8_0 (t : ℝ) : Real.exp (((8:ℝ)+(0:ℝ)*d)*t) = (Real.exp t)^8 * (Real.exp (d*t))^0 := by
  rw [show ((8:ℝ)+(0:ℝ)*d)*t = (8:ℕ)*(t) + (0:ℕ)*(d*t) by ring, Real.exp_add]
  simp only [Real.exp_neg, Real.exp_nat_mul]
theorem expGrid_10_0 (t : ℝ) : Real.exp (((10:ℝ)+(0:ℝ)*d)*t) = (Real.exp t)^10 * (Real.exp (d*t))^0 := by
  rw [show ((10:ℝ)+(0:ℝ)*d)*t = (10:ℕ)*(t) + (0:ℕ)*(d*t) by ring, Real.exp_add]
  simp only [Real.exp_neg, Real.exp_nat_mul]
noncomputable def UExpansion (t : ℝ) : ℝ :=
    (((1:ℝ)/16)+((0:ℝ)/1)*d)*Real.exp (((10:ℝ)+(0:ℝ)*d)*t) +
    (((87:ℝ)/136)+((0:ℝ)/1)*d)*Real.exp (((2:ℝ)+(0:ℝ)*d)*t) +
    (((-5:ℝ)/32)+((21:ℝ)/544)*d)*Real.exp (((7:ℝ)+(1:ℝ)*d)*t) +
    (((-5:ℝ)/32)+((-21:ℝ)/544)*d)*Real.exp (((7:ℝ)+(-1:ℝ)*d)*t) +
    (((1:ℝ)/4)+((-13:ℝ)/136)*d)*Real.exp (((5:ℝ)+(1:ℝ)*d)*t) +
    (((1:ℝ)/4)+((13:ℝ)/136)*d)*Real.exp (((5:ℝ)+(-1:ℝ)*d)*t) +
    (((-87:ℝ)/68)+((0:ℝ)/1)*d)*Real.exp (((0:ℝ)+(0:ℝ)*d)*t) +
    (((-3:ℝ)/32)+((-31:ℝ)/544)*d)*Real.exp (((-3:ℝ)+(1:ℝ)*d)*t) +
    (((-3:ℝ)/32)+((31:ℝ)/544)*d)*Real.exp (((-3:ℝ)+(-1:ℝ)*d)*t) +
    (((1:ℝ)/4)+((13:ℝ)/136)*d)*Real.exp (((-5:ℝ)+(1:ℝ)*d)*t) +
    (((1:ℝ)/4)+((-13:ℝ)/136)*d)*Real.exp (((-5:ℝ)+(-1:ℝ)*d)*t) +
    (((21:ℝ)/272)+((0:ℝ)/1)*d)*Real.exp (((0:ℝ)+(2:ℝ)*d)*t) +
    (((21:ℝ)/272)+((0:ℝ)/1)*d)*Real.exp (((0:ℝ)+(-2:ℝ)*d)*t) +
    (((-3:ℝ)/32)+((31:ℝ)/544)*d)*Real.exp (((3:ℝ)+(1:ℝ)*d)*t) +
    (((-3:ℝ)/32)+((-31:ℝ)/544)*d)*Real.exp (((3:ℝ)+(-1:ℝ)*d)*t) +
    (((87:ℝ)/136)+((0:ℝ)/1)*d)*Real.exp (((-2:ℝ)+(0:ℝ)*d)*t) +
    (((1:ℝ)/16)+((0:ℝ)/1)*d)*Real.exp (((-10:ℝ)+(0:ℝ)*d)*t) +
    (((-5:ℝ)/32)+((-21:ℝ)/544)*d)*Real.exp (((-7:ℝ)+(1:ℝ)*d)*t) +
    (((-5:ℝ)/32)+((21:ℝ)/544)*d)*Real.exp (((-7:ℝ)+(-1:ℝ)*d)*t) +
    (((-1:ℝ)/16)+((0:ℝ)/1)*d)*Real.exp (((8:ℝ)+(0:ℝ)*d)*t) +
    (((-1:ℝ)/16)+((0:ℝ)/1)*d)*Real.exp (((-8:ℝ)+(0:ℝ)*d)*t) +
    (((-21:ℝ)/544)+((5:ℝ)/544)*d)*Real.exp (((2:ℝ)+(2:ℝ)*d)*t) +
    (((-21:ℝ)/544)+((-5:ℝ)/544)*d)*Real.exp (((2:ℝ)+(-2:ℝ)*d)*t) +
    (((-21:ℝ)/544)+((-5:ℝ)/544)*d)*Real.exp (((-2:ℝ)+(2:ℝ)*d)*t) +
    (((-21:ℝ)/544)+((5:ℝ)/544)*d)*Real.exp (((-2:ℝ)+(-2:ℝ)*d)*t)
theorem U_expansion (t : ℝ) : U t = UExpansion t := by
  simp only [U, deriv_A, deriv_B, A, B, Ap, Bp, UExpansion, Real.cosh_eq, Real.sinh_eq]
  simp only [expGrid_m10_0, expGrid_m8_0, expGrid_m7_m1, expGrid_m7_1, expGrid_m5_m1, expGrid_m5_0, expGrid_m5_1, expGrid_m4_0, expGrid_m3_m1, expGrid_m3_1, expGrid_m2_m2, expGrid_m2_0, expGrid_m2_2, expGrid_m1_0, expGrid_0_m2, expGrid_0_m1, expGrid_0_0, expGrid_0_1, expGrid_0_2, expGrid_1_0, expGrid_2_m2, expGrid_2_0, expGrid_2_2, expGrid_3_m1, expGrid_3_1, expGrid_4_0, expGrid_5_m1, expGrid_5_0, expGrid_5_1, expGrid_7_m1, expGrid_7_1, expGrid_8_0, expGrid_10_0]
  have hex4 : Real.exp ((4:ℝ)*t) = Real.exp t ^ 4 := Real.exp_nat_mul t 4
  have hex5 : Real.exp ((5:ℝ)*t) = Real.exp t ^ 5 := Real.exp_nat_mul t 5
  simp only [Real.exp_neg, hex4, hex5]
  field_simp [d_ne, Real.exp_ne_zero]
  ring_nf
  have hc : d^3 = 17*d := by
    calc d^3 = d^2*d := by ring
         _ = 17*d := by rw [d_sq]
  simp only [d_sq, hc]
  ring_nf
  all_goals simp only [d_sq]; ring
noncomputable def VExpansion (t : ℝ) : ℝ :=
    (((-1:ℝ)/8)+((0:ℝ)/1)*d)*Real.exp (((10:ℝ)+(0:ℝ)*d)*t) +
    (((-1:ℝ)/4)+((0:ℝ)/1)*d)*Real.exp (((2:ℝ)+(0:ℝ)*d)*t) +
    (((1:ℝ)/16)+((-5:ℝ)/272)*d)*Real.exp (((7:ℝ)+(1:ℝ)*d)*t) +
    (((1:ℝ)/16)+((5:ℝ)/272)*d)*Real.exp (((7:ℝ)+(-1:ℝ)*d)*t) +
    (((1:ℝ)/8)+((5:ℝ)/136)*d)*Real.exp (((5:ℝ)+(1:ℝ)*d)*t) +
    (((1:ℝ)/8)+((-5:ℝ)/136)*d)*Real.exp (((5:ℝ)+(-1:ℝ)*d)*t) +
    (((-1:ℝ)/8)+((0:ℝ)/1)*d)*Real.exp (((-8:ℝ)+(0:ℝ)*d)*t) +
    (((3:ℝ)/16)+((-5:ℝ)/272)*d)*Real.exp (((-3:ℝ)+(1:ℝ)*d)*t) +
    (((3:ℝ)/16)+((5:ℝ)/272)*d)*Real.exp (((-3:ℝ)+(-1:ℝ)*d)*t) +
    (((-1:ℝ)/8)+((5:ℝ)/136)*d)*Real.exp (((-5:ℝ)+(1:ℝ)*d)*t) +
    (((-1:ℝ)/8)+((-5:ℝ)/136)*d)*Real.exp (((-5:ℝ)+(-1:ℝ)*d)*t) +
    (((-1:ℝ)/16)+((5:ℝ)/272)*d)*Real.exp (((2:ℝ)+(2:ℝ)*d)*t) +
    (((0:ℝ)/1)+((-5:ℝ)/136)*d)*Real.exp (((0:ℝ)+(2:ℝ)*d)*t) +
    (((-1:ℝ)/16)+((-5:ℝ)/272)*d)*Real.exp (((2:ℝ)+(-2:ℝ)*d)*t) +
    (((0:ℝ)/1)+((5:ℝ)/136)*d)*Real.exp (((0:ℝ)+(-2:ℝ)*d)*t) +
    (((1:ℝ)/8)+((0:ℝ)/1)*d)*Real.exp (((8:ℝ)+(0:ℝ)*d)*t) +
    (((-3:ℝ)/16)+((-5:ℝ)/272)*d)*Real.exp (((3:ℝ)+(1:ℝ)*d)*t) +
    (((-3:ℝ)/16)+((5:ℝ)/272)*d)*Real.exp (((3:ℝ)+(-1:ℝ)*d)*t) +
    (((1:ℝ)/4)+((0:ℝ)/1)*d)*Real.exp (((-2:ℝ)+(0:ℝ)*d)*t) +
    (((1:ℝ)/8)+((0:ℝ)/1)*d)*Real.exp (((-10:ℝ)+(0:ℝ)*d)*t) +
    (((-1:ℝ)/16)+((-5:ℝ)/272)*d)*Real.exp (((-7:ℝ)+(1:ℝ)*d)*t) +
    (((-1:ℝ)/16)+((5:ℝ)/272)*d)*Real.exp (((-7:ℝ)+(-1:ℝ)*d)*t) +
    (((1:ℝ)/16)+((5:ℝ)/272)*d)*Real.exp (((-2:ℝ)+(2:ℝ)*d)*t) +
    (((1:ℝ)/16)+((-5:ℝ)/272)*d)*Real.exp (((-2:ℝ)+(-2:ℝ)*d)*t)
theorem V_expansion (t : ℝ) : V t = VExpansion t := by
  simp only [V, A, B, VExpansion, Real.cosh_eq, Real.sinh_eq]
  simp only [expGrid_m10_0, expGrid_m8_0, expGrid_m7_m1, expGrid_m7_1, expGrid_m5_m1, expGrid_m5_0, expGrid_m5_1, expGrid_m4_0, expGrid_m3_m1, expGrid_m3_1, expGrid_m2_m2, expGrid_m2_0, expGrid_m2_2, expGrid_m1_0, expGrid_0_m2, expGrid_0_m1, expGrid_0_0, expGrid_0_1, expGrid_0_2, expGrid_1_0, expGrid_2_m2, expGrid_2_0, expGrid_2_2, expGrid_3_m1, expGrid_3_1, expGrid_4_0, expGrid_5_m1, expGrid_5_0, expGrid_5_1, expGrid_7_m1, expGrid_7_1, expGrid_8_0, expGrid_10_0]
  have hex4 : Real.exp ((4:ℝ)*t) = Real.exp t ^ 4 := Real.exp_nat_mul t 4
  have hex5 : Real.exp ((5:ℝ)*t) = Real.exp t ^ 5 := Real.exp_nat_mul t 5
  simp only [Real.exp_neg, hex4, hex5]
  field_simp [d_ne, Real.exp_ne_zero]
  ring_nf
  have hc : d^3 = 17*d := by
    calc d^3 = d^2*d := by ring
         _ = 17*d := by rw [d_sq]
  simp only [d_sq, hc]
  ring_nf
  all_goals simp only [d_sq]; ring
end LogArctangentMean
