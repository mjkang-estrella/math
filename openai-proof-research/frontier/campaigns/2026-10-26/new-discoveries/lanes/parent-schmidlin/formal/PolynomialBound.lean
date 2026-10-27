import Mathlib

namespace Schmidlin

noncomputable def stirlingUpper (z : ℝ) : ℝ :=
  1 / (12*z) - 1 / (360*z^3) + 1 / (1260*z^5)

noncomputable def cubicCoeff (z : ℝ) : ℝ :=
  120960 * z^5

noncomputable def quadCoeff (z : ℝ) : ℝ :=
  120960 * z^6 - 2520 * z^5 - 10080 * z^4 + 336 * z^2 - 96

noncomputable def linearCoeff (z : ℝ) : ℝ :=
  -20160 * z^5 + 210 * z^4 + 1008 * z^3 - 7 * z^2 - 288 * z + 2

noncomputable def constantCoeff (z : ℝ) : ℝ :=
  420 * z^5 + 672 * z^4 - 14 * z^3 - 192 * z^2 + 4 * z

noncomputable def discriminant (z : ℝ) : ℝ :=
  203212800 * z^11 - 85518720 * z^10 - 22014720 * z^9 - 79252740 * z^8 + 4294080 * z^7 - 4020996 * z^6 - 125664 * z^5 + 63623 * z^4 + 2688 * z^3 - 9188 * z^2 - 384 * z - 4

theorem quadCoeff_shift (t : ℝ) :
    quadCoeff (t+1) = (120960) * t^6 + (723240) * t^5 + (1791720) * t^4 + (2353680) * t^3 + (1729056) * t^2 + (673512) * t^1 + (108600) * t^0 := by
  unfold quadCoeff
  ring

theorem quadCoeff_pos {z : ℝ} (hz : 1 ≤ z) : 0 < quadCoeff z := by
  have ht : 0 ≤ z-1 := by linarith
  rw [show z = (z-1)+1 by ring, quadCoeff_shift]
  positivity

theorem discriminant_shift (t : ℝ) :
    discriminant (t+1) = (203212800) * t^11 + (2149822080) * t^10 + (10299502080) * t^9 + (29404384380) * t^8 + (55375719840) * t^7 + (71883106764) * t^6 + (65187512040) * t^5 + (40869159443) * t^4 + (17049349100) * t^3 + (4345739674) * t^2 + (553547260) * t^1 + (16630775) * t^0 := by
  unfold discriminant
  ring

theorem discriminant_pos {z : ℝ} (hz : 1 ≤ z) : 0 < discriminant z := by
  have ht : 0 ≤ z-1 := by linarith
  rw [show z = (z-1)+1 by ring, discriminant_shift]
  positivity

theorem discriminant_identity (z : ℝ) :
    discriminant z = 4*quadCoeff z*constantCoeff z - linearCoeff z^2 := by
  unfold discriminant quadCoeff constantCoeff linearCoeff
  ring

theorem quadratic_pos {B C E a : ℝ} (hB : 0 < B) (hD : 0 < 4*B*E-C^2) :
    0 < B*a^2+C*a+E := by
  have h : 0 < 4*B*(B*a^2+C*a+E) := by
    nlinarith only [sq_nonneg (2*B*a+C), hD]
  exact ((mul_pos_iff.mp h).resolve_right (by intro hn; linarith)).2

theorem numerator_pos {z a : ℝ} (hz : 1 ≤ z) (ha : 0 ≤ a) :
    0 < cubicCoeff z*a^3 + quadCoeff z*a^2 + linearCoeff z*a + constantCoeff z := by
  have hp := quadratic_pos (a := a) (quadCoeff_pos hz)
    (by rw [← discriminant_identity]; exact discriminant_pos hz)
  have hz0 : 0 < z := by linarith
  have hc : 0 ≤ cubicCoeff z*a^3 := by unfold cubicCoeff; positivity
  linarith

theorem rational_gap_identity {z a : ℝ} (hz : 1 ≤ z) (ha : 0 ≤ a) :
    1 / (12*(z+a)-1/4) - stirlingUpper z + a^2/(2*z+a) =
    (cubicCoeff z*a^3 + quadCoeff z*a^2 + linearCoeff z*a + constantCoeff z) /
      (2520*z^5*(a+2*z)*(48*a+48*z-1)) := by
  have hz0 : 0 < z := by linarith
  have h1 : 0 < 12*(z+a)-(1:ℝ)/4 := by linarith
  have h2 : 0 < 2*z+a := by linarith
  have h3 : 0 < 48*a+48*z-1 := by linarith
  have hd : 2520*z^5*(a+2*z)*(48*a+48*z-1) ≠ 0 := by
    apply ne_of_gt
    have : 0 < a+2*z := by linarith
    positivity
  apply (eq_div_iff hd).2
  unfold stirlingUpper cubicCoeff quadCoeff linearCoeff constantCoeff
  field_simp [ne_of_gt hz0, ne_of_gt h1, ne_of_gt h2]
  ring_nf
  field_simp [show (-1 + z*48+a*48) ≠ 0 by linarith]
  ring

theorem rational_gap_pos {z a : ℝ} (hz : 1 ≤ z) (ha : 0 ≤ a) :
    stirlingUpper z - a^2/(2*z+a) < 1 / (12*(z+a)-1/4) := by
  have hz0 : 0 < z := by linarith
  have h1 : 0 < a+2*z := by linarith
  have h2 : 0 < 48*a+48*z-1 := by linarith
  have hd : 0 < 2520*z^5*(a+2*z)*(48*a+48*z-1) := by positivity
  have h := div_pos (numerator_pos hz ha) hd
  rw [← rational_gap_identity hz ha] at h
  linarith

end Schmidlin
