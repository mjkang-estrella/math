import UlasOdd5One
set_option linter.unusedSimpArgs false
namespace Ulas.Round5Odd
/-- Numerators from the independent review. Their identification with the actual
coefficients 1 and 2 is proved in UlasOdd5LowIdentification. -/
def lowNumerator1 (m : ℤ) : ℤ := (-1416)*m^2 + (-1456)*m^3 + (938)*m^4 + (1400)*m^5 + (476)*m^6 + (56)*m^7 + (2)*m^8
def lowNumerator2 (m : ℤ) : ℤ := (2401560)*m^2 + (2235024)*m^3 + (-2604206)*m^4 + (-3127080)*m^5 + (-183040)*m^6 + (820512)*m^7 + (379302)*m^8 + (71280)*m^9 + (6380)*m^10 + (264)*m^11 + (4)*m^12
theorem numerator1_4_3 (t : ℤ) : (2:ℤ)^7 ∣ lowNumerator1 (4*t+3) := by
  refine ⟨(6615)*t^0 + (51102)*t^1 + (164883)*t^2 + (289408)*t^3 + (300916)*t^4 + (188608)*t^5 + (68992)*t^6 + (13312)*t^7 + (1024)*t^8,?_⟩
  unfold lowNumerator1
  norm_num
  ring
theorem numerator1_16_15 (t : ℤ) : (2:ℤ)^11 ∣ lowNumerator1 (16*t+15) := by
  refine ⟨(10361925)*t^0 + (76044240)*t^1 + (242601483)*t^2 + (439219648)*t^3 + (493278016)*t^4 + (351662080)*t^5 + (155287552)*t^6 + (38797312)*t^7 + (4194304)*t^8,?_⟩
  unfold lowNumerator1
  norm_num
  ring
theorem numerator2_4_3 (t : ℤ) : (2:ℤ)^7 ∣ lowNumerator2 (4*t+3) := by
  refine ⟨(39760875)*t^0 + (460258470)*t^1 + (2317704471)*t^2 + (6710393184)*t^3 + (12428985668)*t^4 + (15489376320)*t^5 + (13284840448)*t^6 + (7874076672)*t^7 + (3186822144)*t^8 + (854261760)*t^9 + (143097856)*t^10 + (13369344)*t^11 + (524288)*t^12,?_⟩
  unfold lowNumerator2
  norm_num
  ring
theorem numerator2_16_15 (t : ℤ) : (2:ℤ)^11 ∣ lowNumerator2 (16*t+15) := by
  refine ⟨(5043706754625)*t^0 + (52881525594000)*t^1 + (252311036370255)*t^2 + (724090642955328)*t^3 + (1391402579513408)*t^4 + (1885025124618240)*t^5 + (1845084391997440)*t^6 + (1313833582854144)*t^7 + (674972779413504)*t^8 + (243782343720960)*t^9 + (58701465518080)*t^10 + (8452495638528)*t^11 + (549755813888)*t^12,?_⟩
  unfold lowNumerator2
  norm_num
  ring
theorem numerator1_16_11 (t : ℤ) : ∃ z : ℤ, lowNumerator1 (16*t+11) = 256*z+128 := by
  refine ⟨(10157647)*t^0 + (98320596)*t^1 + (412405656)*t^2 + (978224128)*t^3 + (1433696768)*t^4 + (1327857664)*t^5 + (757858304)*t^6 + (243269632)*t^7 + (33554432)*t^8,?_⟩
  unfold lowNumerator1
  ring
theorem low1_residue_4_3 (t a : ℤ)
    (h : 315*a = lowNumerator1 (4*t+3)) : (2:ℤ)^7 ∣ a := by
  have hc : IsCoprime ((2:ℤ)^7) 315 := by
    rw [Int.isCoprime_iff_gcd_eq_one]; norm_num
  apply hc.dvd_of_dvd_mul_left
  rw [h]
  exact numerator1_4_3 t
theorem low1_residue_16_15 (t a : ℤ)
    (h : 315*a = lowNumerator1 (16*t+15)) : (2:ℤ)^11 ∣ a := by
  have hc : IsCoprime ((2:ℤ)^11) 315 := by
    rw [Int.isCoprime_iff_gcd_eq_one]; norm_num
  apply hc.dvd_of_dvd_mul_left
  rw [h]
  exact numerator1_16_15 t
theorem low2_residue_4_3 (t a : ℤ)
    (h : 467775*a = lowNumerator2 (4*t+3)) : (2:ℤ)^7 ∣ a := by
  have hc : IsCoprime ((2:ℤ)^7) 467775 := by
    rw [Int.isCoprime_iff_gcd_eq_one]; norm_num
  apply hc.dvd_of_dvd_mul_left
  rw [h]
  exact numerator2_4_3 t
theorem low2_residue_16_15 (t a : ℤ)
    (h : 467775*a = lowNumerator2 (16*t+15)) : (2:ℤ)^11 ∣ a := by
  have hc : IsCoprime ((2:ℤ)^11) 467775 := by
    rw [Int.isCoprime_iff_gcd_eq_one]; norm_num
  apply hc.dvd_of_dvd_mul_left
  rw [h]
  exact numerator2_16_15 t
theorem low1_residue_16_11 (t a : ℤ)
    (h : 315*a = lowNumerator1 (16*t+11)) :
    (2:ℤ)^7 ∣ a ∧ ¬ (2:ℤ)^8 ∣ a := by
  obtain ⟨z,hz⟩ := numerator1_16_11 t
  have hc : IsCoprime ((2:ℤ)^7) 315 := by
    rw [Int.isCoprime_iff_gcd_eq_one]; norm_num
  constructor
  · apply hc.dvd_of_dvd_mul_left
    rw [h,hz]
    exact ⟨2*z+1,by norm_num; ring⟩
  · intro hd
    obtain ⟨b,hb⟩ := hd
    rw [hb] at h
    norm_num at h
    omega
end Ulas.Round5Odd
