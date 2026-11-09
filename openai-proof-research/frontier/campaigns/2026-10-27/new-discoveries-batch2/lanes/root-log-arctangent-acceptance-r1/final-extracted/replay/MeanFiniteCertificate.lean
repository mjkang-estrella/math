import MeanAnalyticDefs
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
namespace LogArctangentMean
theorem d_power_2 : d^2 = (17:ℝ) := by
  exact d_sq
theorem d_power_3 : d^3 = (17:ℝ) * d := by
  calc d^3 = d^2*d := by ring
       _ = 17*d := by rw [d_sq]
theorem d_power_4 : d^4 = (289:ℝ) := by
  rw [show 4 = 2+2 from rfl, pow_add, d_sq]; norm_num
theorem d_power_5 : d^5 = (289:ℝ) * d := by
  rw [show 5 = 3+2 from rfl, pow_add, d_sq, d_power_3]; ring
theorem d_power_6 : d^6 = (4913:ℝ) := by
  rw [show 6 = 4+2 from rfl, pow_add, d_sq, d_power_4]; ring
theorem d_power_7 : d^7 = (4913:ℝ) * d := by
  rw [show 7 = 5+2 from rfl, pow_add, d_sq, d_power_5]; ring
theorem d_power_8 : d^8 = (83521:ℝ) := by
  rw [show 8 = 6+2 from rfl, pow_add, d_sq, d_power_6]; ring
theorem d_power_9 : d^9 = (83521:ℝ) * d := by
  rw [show 9 = 7+2 from rfl, pow_add, d_sq, d_power_7]; ring
theorem d_power_10 : d^10 = (1419857:ℝ) := by
  rw [show 10 = 8+2 from rfl, pow_add, d_sq, d_power_8]; ring
theorem d_power_11 : d^11 = (1419857:ℝ) * d := by
  rw [show 11 = 9+2 from rfl, pow_add, d_sq, d_power_9]; ring
theorem d_power_12 : d^12 = (24137569:ℝ) := by
  rw [show 12 = 10+2 from rfl, pow_add, d_sq, d_power_10]; ring
theorem d_power_13 : d^13 = (24137569:ℝ) * d := by
  rw [show 13 = 11+2 from rfl, pow_add, d_sq, d_power_11]; ring
theorem d_power_14 : d^14 = (410338673:ℝ) := by
  rw [show 14 = 12+2 from rfl, pow_add, d_sq, d_power_12]; ring
theorem d_power_15 : d^15 = (410338673:ℝ) * d := by
  rw [show 15 = 13+2 from rfl, pow_add, d_sq, d_power_13]; ring
theorem d_power_16 : d^16 = (6975757441:ℝ) := by
  rw [show 16 = 14+2 from rfl, pow_add, d_sq, d_power_14]; ring
theorem d_power_17 : d^17 = (6975757441:ℝ) * d := by
  rw [show 17 = 15+2 from rfl, pow_add, d_sq, d_power_15]; ring
theorem d_power_18 : d^18 = (118587876497:ℝ) := by
  rw [show 18 = 16+2 from rfl, pow_add, d_sq, d_power_16]; ring
theorem d_power_19 : d^19 = (118587876497:ℝ) * d := by
  rw [show 19 = 17+2 from rfl, pow_add, d_sq, d_power_17]; ring
theorem d_power_20 : d^20 = (2015993900449:ℝ) := by
  rw [show 20 = 18+2 from rfl, pow_add, d_sq, d_power_18]; ring
theorem d_power_21 : d^21 = (2015993900449:ℝ) * d := by
  rw [show 21 = 19+2 from rfl, pow_add, d_sq, d_power_19]; ring
theorem d_power_22 : d^22 = (34271896307633:ℝ) := by
  rw [show 22 = 20+2 from rfl, pow_add, d_sq, d_power_20]; ring
theorem d_power_23 : d^23 = (34271896307633:ℝ) * d := by
  rw [show 23 = 21+2 from rfl, pow_add, d_sq, d_power_21]; ring
theorem d_power_24 : d^24 = (582622237229761:ℝ) := by
  rw [show 24 = 22+2 from rfl, pow_add, d_sq, d_power_22]; ring
theorem d_power_25 : d^25 = (582622237229761:ℝ) * d := by
  rw [show 25 = 23+2 from rfl, pow_add, d_sq, d_power_23]; ring
theorem d_power_26 : d^26 = (9904578032905937:ℝ) := by
  rw [show 26 = 24+2 from rfl, pow_add, d_sq, d_power_24]; ring
noncomputable def freq0 : ℝ := ((7:ℝ)+(1:ℝ)*d)
noncomputable def u0 : ℝ := (((-5:ℝ)/32)+((21:ℝ)/544)*d)
noncomputable def v0 : ℝ := (((1:ℝ)/16)+((-5:ℝ)/272)*d)
noncomputable def c0_0 : ℝ := freq0^22*(u0*freq0^2+24*v0*freq0+1104*u0)
noncomputable def c0_1 : ℝ := freq0^22*(v0*freq0+94*u0)
noncomputable def c0_2 : ℝ := 2*freq0^22*u0
noncomputable def freq1 : ℝ := ((2:ℝ)+(2:ℝ)*d)
noncomputable def u1 : ℝ := (((-21:ℝ)/544)+((5:ℝ)/544)*d)
noncomputable def v1 : ℝ := (((-1:ℝ)/16)+((5:ℝ)/272)*d)
noncomputable def c1_0 : ℝ := freq1^22*(u1*freq1^2+24*v1*freq1+1104*u1)
noncomputable def c1_1 : ℝ := freq1^22*(v1*freq1+94*u1)
noncomputable def c1_2 : ℝ := 2*freq1^22*u1
noncomputable def freq2 : ℝ := ((10:ℝ)+(0:ℝ)*d)
noncomputable def u2 : ℝ := (((1:ℝ)/16)+(0:ℝ)*d)
noncomputable def v2 : ℝ := (((-1:ℝ)/8)+(0:ℝ)*d)
noncomputable def c2_0 : ℝ := freq2^22*(u2*freq2^2+24*v2*freq2+1104*u2)
noncomputable def c2_1 : ℝ := freq2^22*(v2*freq2+94*u2)
noncomputable def c2_2 : ℝ := 2*freq2^22*u2
noncomputable def freq3 : ℝ := ((5:ℝ)+(1:ℝ)*d)
noncomputable def u3 : ℝ := (((1:ℝ)/4)+((-13:ℝ)/136)*d)
noncomputable def v3 : ℝ := (((1:ℝ)/8)+((5:ℝ)/136)*d)
noncomputable def c3_0 : ℝ := freq3^22*(u3*freq3^2+24*v3*freq3+1104*u3)
noncomputable def c3_1 : ℝ := freq3^22*(v3*freq3+94*u3)
noncomputable def c3_2 : ℝ := 2*freq3^22*u3
noncomputable def freq4 : ℝ := ((0:ℝ)+(2:ℝ)*d)
noncomputable def u4 : ℝ := (((21:ℝ)/272)+(0:ℝ)*d)
noncomputable def v4 : ℝ := ((0:ℝ)+((-5:ℝ)/136)*d)
noncomputable def c4_0 : ℝ := freq4^22*(u4*freq4^2+24*v4*freq4+1104*u4)
noncomputable def c4_1 : ℝ := freq4^22*(v4*freq4+94*u4)
noncomputable def c4_2 : ℝ := 2*freq4^22*u4
noncomputable def freq5 : ℝ := ((8:ℝ)+(0:ℝ)*d)
noncomputable def u5 : ℝ := (((-1:ℝ)/16)+(0:ℝ)*d)
noncomputable def v5 : ℝ := (((1:ℝ)/8)+(0:ℝ)*d)
noncomputable def c5_0 : ℝ := freq5^22*(u5*freq5^2+24*v5*freq5+1104*u5)
noncomputable def c5_1 : ℝ := freq5^22*(v5*freq5+94*u5)
noncomputable def c5_2 : ℝ := 2*freq5^22*u5
noncomputable def freq6 : ℝ := ((3:ℝ)+(1:ℝ)*d)
noncomputable def u6 : ℝ := (((-3:ℝ)/32)+((31:ℝ)/544)*d)
noncomputable def v6 : ℝ := (((-3:ℝ)/16)+((-5:ℝ)/272)*d)
noncomputable def c6_0 : ℝ := freq6^22*(u6*freq6^2+24*v6*freq6+1104*u6)
noncomputable def c6_1 : ℝ := freq6^22*(v6*freq6+94*u6)
noncomputable def c6_2 : ℝ := 2*freq6^22*u6
noncomputable def freq7 : ℝ := ((-2:ℝ)+(2:ℝ)*d)
noncomputable def u7 : ℝ := (((-21:ℝ)/544)+((-5:ℝ)/544)*d)
noncomputable def v7 : ℝ := (((1:ℝ)/16)+((5:ℝ)/272)*d)
noncomputable def c7_0 : ℝ := freq7^22*(u7*freq7^2+24*v7*freq7+1104*u7)
noncomputable def c7_1 : ℝ := freq7^22*(v7*freq7+94*u7)
noncomputable def c7_2 : ℝ := 2*freq7^22*u7
noncomputable def freq8 : ℝ := ((7:ℝ)+(-1:ℝ)*d)
noncomputable def u8 : ℝ := (((-5:ℝ)/32)+((-21:ℝ)/544)*d)
noncomputable def v8 : ℝ := (((1:ℝ)/16)+((5:ℝ)/272)*d)
noncomputable def c8_0 : ℝ := freq8^22*(u8*freq8^2+24*v8*freq8+1104*u8)
noncomputable def c8_1 : ℝ := freq8^22*(v8*freq8+94*u8)
noncomputable def c8_2 : ℝ := 2*freq8^22*u8
noncomputable def freq9 : ℝ := ((2:ℝ)+(0:ℝ)*d)
noncomputable def u9 : ℝ := (((87:ℝ)/136)+(0:ℝ)*d)
noncomputable def v9 : ℝ := (((-1:ℝ)/4)+(0:ℝ)*d)
noncomputable def c9_0 : ℝ := freq9^22*(u9*freq9^2+24*v9*freq9+1104*u9)
noncomputable def c9_1 : ℝ := freq9^22*(v9*freq9+94*u9)
noncomputable def c9_2 : ℝ := 2*freq9^22*u9
noncomputable def freq10 : ℝ := ((-3:ℝ)+(1:ℝ)*d)
noncomputable def u10 : ℝ := (((-3:ℝ)/32)+((-31:ℝ)/544)*d)
noncomputable def v10 : ℝ := (((3:ℝ)/16)+((-5:ℝ)/272)*d)
noncomputable def c10_0 : ℝ := freq10^22*(u10*freq10^2+24*v10*freq10+1104*u10)
noncomputable def c10_1 : ℝ := freq10^22*(v10*freq10+94*u10)
noncomputable def c10_2 : ℝ := 2*freq10^22*u10
noncomputable def freq11 : ℝ := ((5:ℝ)+(-1:ℝ)*d)
noncomputable def u11 : ℝ := (((1:ℝ)/4)+((13:ℝ)/136)*d)
noncomputable def v11 : ℝ := (((1:ℝ)/8)+((-5:ℝ)/136)*d)
noncomputable def c11_0 : ℝ := freq11^22*(u11*freq11^2+24*v11*freq11+1104*u11)
noncomputable def c11_1 : ℝ := freq11^22*(v11*freq11+94*u11)
noncomputable def c11_2 : ℝ := 2*freq11^22*u11
theorem frequencies_ordered : freq1 < freq0 ∧ freq2 < freq1 ∧ freq3 < freq2 ∧ freq4 < freq3 ∧ freq5 < freq4 ∧ freq6 < freq5 ∧ freq7 < freq6 ∧ freq8 < freq7 ∧ freq9 < freq8 ∧ freq10 < freq9 ∧ freq11 < freq10 ∧ 0 < freq11 := by
  have hlo := d_bounds.1
  have hhi := d_bounds.2
  dsimp [freq0, freq1, freq2, freq3, freq4, freq5, freq6, freq7, freq8, freq9, freq10, freq11]
  (repeat' apply And.intro) <;> linarith
theorem prefix_value_0_0 : c0_0 = ((1514507422733486784512:ℝ)+((6244474092277637578752:ℝ)/17)*d) := by
  dsimp [c0_0, freq0, u0, v0]
  ring_nf
  simp only [d_power_2, d_power_3, d_power_4, d_power_5, d_power_6, d_power_7, d_power_8, d_power_9, d_power_10, d_power_11, d_power_12, d_power_13, d_power_14, d_power_15, d_power_16, d_power_17, d_power_18, d_power_19, d_power_20, d_power_21, d_power_22, d_power_23, d_power_24, d_power_25, d_power_26]; ring
theorem prefix_pos_0_0 : 0 < c0_0 := by
  rw [prefix_value_0_0]
  have hlo := d_bounds.1
  have hhi := d_bounds.2
  linarith
theorem prefix_value_0_1 : c0_1 = ((6554411706290277187584:ℝ)+(1589678340019131252736:ℝ)*d) := by
  dsimp [c0_1, freq0, u0, v0]
  ring_nf
  simp only [d_power_2, d_power_3, d_power_4, d_power_5, d_power_6, d_power_7, d_power_8, d_power_9, d_power_10, d_power_11, d_power_12, d_power_13, d_power_14, d_power_15, d_power_16, d_power_17, d_power_18, d_power_19, d_power_20, d_power_21, d_power_22, d_power_23, d_power_24, d_power_25, d_power_26]; ring
theorem prefix_pos_0_1 : 0 < c0_1 := by
  rw [prefix_value_0_1]
  have hlo := d_bounds.1
  have hhi := d_bounds.2
  linarith
theorem prefix_value_0_2 : c0_2 = ((303014549705727934464:ℝ)+((1249360994568157528064:ℝ)/17)*d) := by
  dsimp [c0_2, freq0, u0, v0]
  ring_nf
  simp only [d_power_2, d_power_3, d_power_4, d_power_5, d_power_6, d_power_7, d_power_8, d_power_9, d_power_10, d_power_11, d_power_12, d_power_13, d_power_14, d_power_15, d_power_16, d_power_17, d_power_18, d_power_19, d_power_20, d_power_21, d_power_22, d_power_23, d_power_24, d_power_25, d_power_26]; ring
theorem prefix_pos_0_2 : 0 < c0_2 := by
  rw [prefix_value_0_2]
  have hlo := d_bounds.1
  have hhi := d_bounds.2
  linarith
theorem prefix_value_1_0 : c0_0 + c1_0 = (((375992454305137015914496:ℝ)/17)+((91279259277105463558144:ℝ)/17)*d) := by
  rw [show c0_0 + c1_0 = (c0_0) + c1_0 by ring, prefix_value_0_0]
  dsimp [c1_0, freq1, u1, v1]
  ring_nf
  simp only [d_power_2, d_power_3, d_power_4, d_power_5, d_power_6, d_power_7, d_power_8, d_power_9, d_power_10, d_power_11, d_power_12, d_power_13, d_power_14, d_power_15, d_power_16, d_power_17, d_power_18, d_power_19, d_power_20, d_power_21, d_power_22, d_power_23, d_power_24, d_power_25, d_power_26]; ring
theorem prefix_pos_1_0 : 0 < c0_0 + c1_0 := by
  rw [prefix_value_1_0]
  have hlo := d_bounds.1
  have hhi := d_bounds.2
  linarith
theorem prefix_value_1_1 : c0_1 + c1_1 = (((121533692805895840071680:ℝ)/17)+((29484567727361022492672:ℝ)/17)*d) := by
  rw [show c0_1 + c1_1 = (c0_1) + c1_1 by ring, prefix_value_0_1]
  dsimp [c1_1, freq1, u1, v1]
  ring_nf
  simp only [d_power_2, d_power_3, d_power_4, d_power_5, d_power_6, d_power_7, d_power_8, d_power_9, d_power_10, d_power_11, d_power_12, d_power_13, d_power_14, d_power_15, d_power_16, d_power_17, d_power_18, d_power_19, d_power_20, d_power_21, d_power_22, d_power_23, d_power_24, d_power_25, d_power_26]; ring
theorem prefix_pos_1_1 : 0 < c0_1 + c1_1 := by
  rw [prefix_value_1_1]
  have hlo := d_bounds.1
  have hhi := d_bounds.2
  linarith
theorem prefix_value_1_2 : c0_2 + c1_2 = (((4945665793356096864256:ℝ)/17)+((1199701274822724288512:ℝ)/17)*d) := by
  rw [show c0_2 + c1_2 = (c0_2) + c1_2 by ring, prefix_value_0_2]
  dsimp [c1_2, freq1, u1, v1]
  ring_nf
  simp only [d_power_2, d_power_3, d_power_4, d_power_5, d_power_6, d_power_7, d_power_8, d_power_9, d_power_10, d_power_11, d_power_12, d_power_13, d_power_14, d_power_15, d_power_16, d_power_17, d_power_18, d_power_19, d_power_20, d_power_21, d_power_22, d_power_23, d_power_24, d_power_25, d_power_26]; ring
theorem prefix_pos_1_2 : 0 < c0_2 + c1_2 := by
  rw [prefix_value_1_2]
  have hlo := d_bounds.1
  have hhi := d_bounds.2
  linarith
theorem prefix_value_2_0 : c0_0 + c1_0 + c2_0 = (((8068492454305137015914496:ℝ)/17)+((91279259277105463558144:ℝ)/17)*d) := by
  rw [show c0_0 + c1_0 + c2_0 = (c0_0 + c1_0) + c2_0 by ring, prefix_value_1_0]
  dsimp [c2_0, freq2, u2, v2]
  ring_nf
theorem prefix_pos_2_0 : 0 < c0_0 + c1_0 + c2_0 := by
  rw [prefix_value_2_0]
  have hlo := d_bounds.1
  have hhi := d_bounds.2
  linarith
theorem prefix_value_2_1 : c0_1 + c1_1 + c2_1 = (((907783692805895840071680:ℝ)/17)+((29484567727361022492672:ℝ)/17)*d) := by
  rw [show c0_1 + c1_1 + c2_1 = (c0_1 + c1_1) + c2_1 by ring, prefix_value_1_1]
  dsimp [c2_1, freq2, u2, v2]
  ring_nf
theorem prefix_pos_2_1 : 0 < c0_1 + c1_1 + c2_1 := by
  rw [prefix_value_2_1]
  have hlo := d_bounds.1
  have hhi := d_bounds.2
  linarith
theorem prefix_value_2_2 : c0_2 + c1_2 + c2_2 = (((26195665793356096864256:ℝ)/17)+((1199701274822724288512:ℝ)/17)*d) := by
  rw [show c0_2 + c1_2 + c2_2 = (c0_2 + c1_2) + c2_2 by ring, prefix_value_1_2]
  dsimp [c2_2, freq2, u2, v2]
  ring_nf
theorem prefix_pos_2_2 : 0 < c0_2 + c1_2 + c2_2 := by
  rw [prefix_value_2_2]
  have hlo := d_bounds.1
  have hhi := d_bounds.2
  linarith
theorem prefix_value_3_0 : c0_0 + c1_0 + c2_0 + c3_0 = (((6820832093783154824314880:ℝ)/17)+((-211322826095150024359936:ℝ)/17)*d) := by
  rw [show c0_0 + c1_0 + c2_0 + c3_0 = (c0_0 + c1_0 + c2_0) + c3_0 by ring, prefix_value_2_0]
  dsimp [c3_0, freq3, u3, v3]
  ring_nf
  simp only [d_power_2, d_power_3, d_power_4, d_power_5, d_power_6, d_power_7, d_power_8, d_power_9, d_power_10, d_power_11, d_power_12, d_power_13, d_power_14, d_power_15, d_power_16, d_power_17, d_power_18, d_power_19, d_power_20, d_power_21, d_power_22, d_power_23, d_power_24, d_power_25, d_power_26]; ring
theorem prefix_pos_3_0 : 0 < c0_0 + c1_0 + c2_0 + c3_0 := by
  rw [prefix_value_3_0]
  have hlo := d_bounds.1
  have hhi := d_bounds.2
  linarith
theorem prefix_value_3_1 : c0_1 + c1_1 + c2_1 + c3_1 = (((783361519558872887197696:ℝ)/17)+((-692241829484596297728:ℝ)/17)*d) := by
  rw [show c0_1 + c1_1 + c2_1 + c3_1 = (c0_1 + c1_1 + c2_1) + c3_1 by ring, prefix_value_2_1]
  dsimp [c3_1, freq3, u3, v3]
  ring_nf
  simp only [d_power_2, d_power_3, d_power_4, d_power_5, d_power_6, d_power_7, d_power_8, d_power_9, d_power_10, d_power_11, d_power_12, d_power_13, d_power_14, d_power_15, d_power_16, d_power_17, d_power_18, d_power_19, d_power_20, d_power_21, d_power_22, d_power_23, d_power_24, d_power_25, d_power_26]; ring
theorem prefix_pos_3_1 : 0 < c0_1 + c1_1 + c2_1 + c3_1 := by
  rw [prefix_value_3_1]
  have hlo := d_bounds.1
  have hhi := d_bounds.2
  linarith
theorem prefix_value_3_2 : c0_2 + c1_2 + c2_2 + c3_2 = (((22942442900638382424064:ℝ)/17)+((410678827154926206976:ℝ)/17)*d) := by
  rw [show c0_2 + c1_2 + c2_2 + c3_2 = (c0_2 + c1_2 + c2_2) + c3_2 by ring, prefix_value_2_2]
  dsimp [c3_2, freq3, u3, v3]
  ring_nf
  simp only [d_power_2, d_power_3, d_power_4, d_power_5, d_power_6, d_power_7, d_power_8, d_power_9, d_power_10, d_power_11, d_power_12, d_power_13, d_power_14, d_power_15, d_power_16, d_power_17, d_power_18, d_power_19, d_power_20, d_power_21, d_power_22, d_power_23, d_power_24, d_power_25, d_power_26]; ring
theorem prefix_pos_3_2 : 0 < c0_2 + c1_2 + c2_2 + c3_2 := by
  rw [prefix_value_3_2]
  have hlo := d_bounds.1
  have hhi := d_bounds.2
  linarith
theorem prefix_value_4_0 : c0_0 + c1_0 + c2_0 + c3_0 + c4_0 = (((6968639691291367148355584:ℝ)/17)+((-211322826095150024359936:ℝ)/17)*d) := by
  rw [show c0_0 + c1_0 + c2_0 + c3_0 + c4_0 = (c0_0 + c1_0 + c2_0 + c3_0) + c4_0 by ring, prefix_value_3_0]
  dsimp [c4_0, freq4, u4, v4]
  ring_nf
  simp only [d_power_2, d_power_3, d_power_4, d_power_5, d_power_6, d_power_7, d_power_8, d_power_9, d_power_10, d_power_11, d_power_12, d_power_13, d_power_14, d_power_15, d_power_16, d_power_17, d_power_18, d_power_19, d_power_20, d_power_21, d_power_22, d_power_23, d_power_24, d_power_25, d_power_26]; ring
theorem prefix_pos_4_0 : 0 < c0_0 + c1_0 + c2_0 + c3_0 + c4_0 := by
  rw [prefix_value_4_0]
  have hlo := d_bounds.1
  have hhi := d_bounds.2
  linarith
theorem prefix_value_4_1 : c0_1 + c1_1 + c2_1 + c3_1 + c4_1 = (((798041656583454636376064:ℝ)/17)+((-692241829484596297728:ℝ)/17)*d) := by
  rw [show c0_1 + c1_1 + c2_1 + c3_1 + c4_1 = (c0_1 + c1_1 + c2_1 + c3_1) + c4_1 by ring, prefix_value_3_1]
  dsimp [c4_1, freq4, u4, v4]
  ring_nf
  simp only [d_power_2, d_power_3, d_power_4, d_power_5, d_power_6, d_power_7, d_power_8, d_power_9, d_power_10, d_power_11, d_power_12, d_power_13, d_power_14, d_power_15, d_power_16, d_power_17, d_power_18, d_power_19, d_power_20, d_power_21, d_power_22, d_power_23, d_power_24, d_power_25, d_power_26]; ring
theorem prefix_pos_4_1 : 0 < c0_1 + c1_1 + c2_1 + c3_1 + c4_1 := by
  rw [prefix_value_4_1]
  have hlo := d_bounds.1
  have hhi := d_bounds.2
  linarith
theorem prefix_value_4_2 : c0_2 + c1_2 + c2_2 + c3_2 + c4_2 = (((23319778124036444520448:ℝ)/17)+((410678827154926206976:ℝ)/17)*d) := by
  rw [show c0_2 + c1_2 + c2_2 + c3_2 + c4_2 = (c0_2 + c1_2 + c2_2 + c3_2) + c4_2 by ring, prefix_value_3_2]
  dsimp [c4_2, freq4, u4, v4]
  ring_nf
  simp only [d_power_2, d_power_3, d_power_4, d_power_5, d_power_6, d_power_7, d_power_8, d_power_9, d_power_10, d_power_11, d_power_12, d_power_13, d_power_14, d_power_15, d_power_16, d_power_17, d_power_18, d_power_19, d_power_20, d_power_21, d_power_22, d_power_23, d_power_24, d_power_25, d_power_26]; ring
theorem prefix_pos_4_2 : 0 < c0_2 + c1_2 + c2_2 + c3_2 + c4_2 := by
  rw [prefix_value_4_2]
  have hlo := d_bounds.1
  have hhi := d_bounds.2
  linarith
theorem prefix_value_5_0 : c0_0 + c1_0 + c2_0 + c3_0 + c4_0 + c5_0 = (((6907175140037766922371072:ℝ)/17)+((-211322826095150024359936:ℝ)/17)*d) := by
  rw [show c0_0 + c1_0 + c2_0 + c3_0 + c4_0 + c5_0 = (c0_0 + c1_0 + c2_0 + c3_0 + c4_0) + c5_0 by ring, prefix_value_4_0]
  dsimp [c5_0, freq5, u5, v5]
  ring_nf
theorem prefix_pos_5_0 : 0 < c0_0 + c1_0 + c2_0 + c3_0 + c4_0 + c5_0 := by
  rw [prefix_value_5_0]
  have hlo := d_bounds.1
  have hhi := d_bounds.2
  linarith
theorem prefix_value_5_1 : c0_1 + c1_1 + c2_1 + c3_1 + c4_1 + c5_1 = (((791926560923019920015360:ℝ)/17)+((-692241829484596297728:ℝ)/17)*d) := by
  rw [show c0_1 + c1_1 + c2_1 + c3_1 + c4_1 + c5_1 = (c0_1 + c1_1 + c2_1 + c3_1 + c4_1) + c5_1 by ring, prefix_value_4_1]
  dsimp [c5_1, freq5, u5, v5]
  ring_nf
theorem prefix_pos_5_1 : 0 < c0_1 + c1_1 + c2_1 + c3_1 + c4_1 + c5_1 := by
  rw [prefix_value_5_1]
  have hlo := d_bounds.1
  have hhi := d_bounds.2
  linarith
theorem prefix_value_5_2 : c0_2 + c1_2 + c2_2 + c3_2 + c4_2 + c5_2 = (((23162980799409913331712:ℝ)/17)+((410678827154926206976:ℝ)/17)*d) := by
  rw [show c0_2 + c1_2 + c2_2 + c3_2 + c4_2 + c5_2 = (c0_2 + c1_2 + c2_2 + c3_2 + c4_2) + c5_2 by ring, prefix_value_4_2]
  dsimp [c5_2, freq5, u5, v5]
  ring_nf
theorem prefix_pos_5_2 : 0 < c0_2 + c1_2 + c2_2 + c3_2 + c4_2 + c5_2 := by
  rw [prefix_value_5_2]
  have hlo := d_bounds.1
  have hhi := d_bounds.2
  linarith
theorem prefix_value_6_0 : c0_0 + c1_0 + c2_0 + c3_0 + c4_0 + c5_0 + c6_0 = (((6912932118557182503419904:ℝ)/17)+((-209926553711622823608320:ℝ)/17)*d) := by
  rw [show c0_0 + c1_0 + c2_0 + c3_0 + c4_0 + c5_0 + c6_0 = (c0_0 + c1_0 + c2_0 + c3_0 + c4_0 + c5_0) + c6_0 by ring, prefix_value_5_0]
  dsimp [c6_0, freq6, u6, v6]
  ring_nf
  simp only [d_power_2, d_power_3, d_power_4, d_power_5, d_power_6, d_power_7, d_power_8, d_power_9, d_power_10, d_power_11, d_power_12, d_power_13, d_power_14, d_power_15, d_power_16, d_power_17, d_power_18, d_power_19, d_power_20, d_power_21, d_power_22, d_power_23, d_power_24, d_power_25, d_power_26]; ring
theorem prefix_pos_6_0 : 0 < c0_0 + c1_0 + c2_0 + c3_0 + c4_0 + c5_0 + c6_0 := by
  rw [prefix_value_6_0]
  have hlo := d_bounds.1
  have hhi := d_bounds.2
  linarith
theorem prefix_value_6_1 : c0_1 + c1_1 + c2_1 + c3_1 + c4_1 + c5_1 + c6_1 = (((792482429062743286874112:ℝ)/17)+((-557424002779005845504:ℝ)/17)*d) := by
  rw [show c0_1 + c1_1 + c2_1 + c3_1 + c4_1 + c5_1 + c6_1 = (c0_1 + c1_1 + c2_1 + c3_1 + c4_1 + c5_1) + c6_1 by ring, prefix_value_5_1]
  dsimp [c6_1, freq6, u6, v6]
  ring_nf
  simp only [d_power_2, d_power_3, d_power_4, d_power_5, d_power_6, d_power_7, d_power_8, d_power_9, d_power_10, d_power_11, d_power_12, d_power_13, d_power_14, d_power_15, d_power_16, d_power_17, d_power_18, d_power_19, d_power_20, d_power_21, d_power_22, d_power_23, d_power_24, d_power_25, d_power_26]; ring
theorem prefix_pos_6_1 : 0 < c0_1 + c1_1 + c2_1 + c3_1 + c4_1 + c5_1 + c6_1 := by
  rw [prefix_value_6_1]
  have hlo := d_bounds.1
  have hhi := d_bounds.2
  linarith
theorem prefix_value_6_2 : c0_2 + c1_2 + c2_2 + c3_2 + c4_2 + c5_2 + c6_2 = (((23176753836522429480960:ℝ)/17)+((414019279319658921984:ℝ)/17)*d) := by
  rw [show c0_2 + c1_2 + c2_2 + c3_2 + c4_2 + c5_2 + c6_2 = (c0_2 + c1_2 + c2_2 + c3_2 + c4_2 + c5_2) + c6_2 by ring, prefix_value_5_2]
  dsimp [c6_2, freq6, u6, v6]
  ring_nf
  simp only [d_power_2, d_power_3, d_power_4, d_power_5, d_power_6, d_power_7, d_power_8, d_power_9, d_power_10, d_power_11, d_power_12, d_power_13, d_power_14, d_power_15, d_power_16, d_power_17, d_power_18, d_power_19, d_power_20, d_power_21, d_power_22, d_power_23, d_power_24, d_power_25, d_power_26]; ring
theorem prefix_pos_6_2 : 0 < c0_2 + c1_2 + c2_2 + c3_2 + c4_2 + c5_2 + c6_2 := by
  rw [prefix_value_6_2]
  have hlo := d_bounds.1
  have hhi := d_bounds.2
  linarith
theorem prefix_value_7_0 : c0_0 + c1_0 + c2_0 + c3_0 + c4_0 + c5_0 + c6_0 + c7_0 = (((7263177946675850243997696:ℝ)/17)+((-294961338896450649587712:ℝ)/17)*d) := by
  rw [show c0_0 + c1_0 + c2_0 + c3_0 + c4_0 + c5_0 + c6_0 + c7_0 = (c0_0 + c1_0 + c2_0 + c3_0 + c4_0 + c5_0 + c6_0) + c7_0 by ring, prefix_value_6_0]
  dsimp [c7_0, freq7, u7, v7]
  ring_nf
  simp only [d_power_2, d_power_3, d_power_4, d_power_5, d_power_6, d_power_7, d_power_8, d_power_9, d_power_10, d_power_11, d_power_12, d_power_13, d_power_14, d_power_15, d_power_16, d_power_17, d_power_18, d_power_19, d_power_20, d_power_21, d_power_22, d_power_23, d_power_24, d_power_25, d_power_26]; ring
theorem prefix_pos_7_0 : 0 < c0_0 + c1_0 + c2_0 + c3_0 + c4_0 + c5_0 + c6_0 + c7_0 := by
  rw [prefix_value_7_0]
  have hlo := d_bounds.1
  have hhi := d_bounds.2
  linarith
theorem prefix_value_7_1 : c0_1 + c1_1 + c2_1 + c3_1 + c4_1 + c5_1 + c6_1 + c7_1 = (((802591122861704414756864:ℝ)/17)+((-3017459949814797041664:ℝ)/17)*d) := by
  rw [show c0_1 + c1_1 + c2_1 + c3_1 + c4_1 + c5_1 + c6_1 + c7_1 = (c0_1 + c1_1 + c2_1 + c3_1 + c4_1 + c5_1 + c6_1) + c7_1 by ring, prefix_value_6_1]
  dsimp [c7_1, freq7, u7, v7]
  ring_nf
  simp only [d_power_2, d_power_3, d_power_4, d_power_5, d_power_6, d_power_7, d_power_8, d_power_9, d_power_10, d_power_11, d_power_12, d_power_13, d_power_14, d_power_15, d_power_16, d_power_17, d_power_18, d_power_19, d_power_20, d_power_21, d_power_22, d_power_23, d_power_24, d_power_25, d_power_26]; ring
theorem prefix_pos_7_1 : 0 < c0_1 + c1_1 + c2_1 + c3_1 + c4_1 + c5_1 + c6_1 + c7_1 := by
  rw [prefix_value_7_1]
  have hlo := d_bounds.1
  have hhi := d_bounds.2
  linarith
theorem prefix_value_7_2 : c0_2 + c1_2 + c2_2 + c3_2 + c4_2 + c5_2 + c6_2 + c7_2 = (((22971172284881151459328:ℝ)/17)+((463678999065092161536:ℝ)/17)*d) := by
  rw [show c0_2 + c1_2 + c2_2 + c3_2 + c4_2 + c5_2 + c6_2 + c7_2 = (c0_2 + c1_2 + c2_2 + c3_2 + c4_2 + c5_2 + c6_2) + c7_2 by ring, prefix_value_6_2]
  dsimp [c7_2, freq7, u7, v7]
  ring_nf
  simp only [d_power_2, d_power_3, d_power_4, d_power_5, d_power_6, d_power_7, d_power_8, d_power_9, d_power_10, d_power_11, d_power_12, d_power_13, d_power_14, d_power_15, d_power_16, d_power_17, d_power_18, d_power_19, d_power_20, d_power_21, d_power_22, d_power_23, d_power_24, d_power_25, d_power_26]; ring
theorem prefix_pos_7_2 : 0 < c0_2 + c1_2 + c2_2 + c3_2 + c4_2 + c5_2 + c6_2 + c7_2 := by
  rw [prefix_value_7_2]
  have hlo := d_bounds.1
  have hhi := d_bounds.2
  linarith
theorem prefix_value_8_0 : c0_0 + c1_0 + c2_0 + c3_0 + c4_0 + c5_0 + c6_0 + c7_0 + c8_0 = (((7288924572862319519334400:ℝ)/17)+((-301205812988728287166464:ℝ)/17)*d) := by
  rw [show c0_0 + c1_0 + c2_0 + c3_0 + c4_0 + c5_0 + c6_0 + c7_0 + c8_0 = (c0_0 + c1_0 + c2_0 + c3_0 + c4_0 + c5_0 + c6_0 + c7_0) + c8_0 by ring, prefix_value_7_0]
  dsimp [c8_0, freq8, u8, v8]
  ring_nf
  simp only [d_power_2, d_power_3, d_power_4, d_power_5, d_power_6, d_power_7, d_power_8, d_power_9, d_power_10, d_power_11, d_power_12, d_power_13, d_power_14, d_power_15, d_power_16, d_power_17, d_power_18, d_power_19, d_power_20, d_power_21, d_power_22, d_power_23, d_power_24, d_power_25, d_power_26]; ring
theorem prefix_pos_8_0 : 0 < c0_0 + c1_0 + c2_0 + c3_0 + c4_0 + c5_0 + c6_0 + c7_0 + c8_0 := by
  rw [prefix_value_8_0]
  have hlo := d_bounds.1
  have hhi := d_bounds.2
  linarith
theorem prefix_value_8_1 : c0_1 + c1_1 + c2_1 + c3_1 + c4_1 + c5_1 + c6_1 + c7_1 + c8_1 = (((914016121868639126945792:ℝ)/17)+((-30041991730140028338176:ℝ)/17)*d) := by
  rw [show c0_1 + c1_1 + c2_1 + c3_1 + c4_1 + c5_1 + c6_1 + c7_1 + c8_1 = (c0_1 + c1_1 + c2_1 + c3_1 + c4_1 + c5_1 + c6_1 + c7_1) + c8_1 by ring, prefix_value_7_1]
  dsimp [c8_1, freq8, u8, v8]
  ring_nf
  simp only [d_power_2, d_power_3, d_power_4, d_power_5, d_power_6, d_power_7, d_power_8, d_power_9, d_power_10, d_power_11, d_power_12, d_power_13, d_power_14, d_power_15, d_power_16, d_power_17, d_power_18, d_power_19, d_power_20, d_power_21, d_power_22, d_power_23, d_power_24, d_power_25, d_power_26]; ring
theorem prefix_pos_8_1 : 0 < c0_1 + c1_1 + c2_1 + c3_1 + c4_1 + c5_1 + c6_1 + c7_1 + c8_1 := by
  rw [prefix_value_8_1]
  have hlo := d_bounds.1
  have hhi := d_bounds.2
  linarith
theorem prefix_value_8_2 : c0_2 + c1_2 + c2_2 + c3_2 + c4_2 + c5_2 + c6_2 + c7_2 + c8_2 = (((28122419629878526345216:ℝ)/17)+((-785681995503065366528:ℝ)/17)*d) := by
  rw [show c0_2 + c1_2 + c2_2 + c3_2 + c4_2 + c5_2 + c6_2 + c7_2 + c8_2 = (c0_2 + c1_2 + c2_2 + c3_2 + c4_2 + c5_2 + c6_2 + c7_2) + c8_2 by ring, prefix_value_7_2]
  dsimp [c8_2, freq8, u8, v8]
  ring_nf
  simp only [d_power_2, d_power_3, d_power_4, d_power_5, d_power_6, d_power_7, d_power_8, d_power_9, d_power_10, d_power_11, d_power_12, d_power_13, d_power_14, d_power_15, d_power_16, d_power_17, d_power_18, d_power_19, d_power_20, d_power_21, d_power_22, d_power_23, d_power_24, d_power_25, d_power_26]; ring
theorem prefix_pos_8_2 : 0 < c0_2 + c1_2 + c2_2 + c3_2 + c4_2 + c5_2 + c6_2 + c7_2 + c8_2 := by
  rw [prefix_value_8_2]
  have hlo := d_bounds.1
  have hhi := d_bounds.2
  linarith
theorem prefix_value_9_0 : c0_0 + c1_0 + c2_0 + c3_0 + c4_0 + c5_0 + c6_0 + c7_0 + c8_0 + c9_0 = ((428760268991904070762496:ℝ)+((-301205812988728287166464:ℝ)/17)*d) := by
  rw [show c0_0 + c1_0 + c2_0 + c3_0 + c4_0 + c5_0 + c6_0 + c7_0 + c8_0 + c9_0 = (c0_0 + c1_0 + c2_0 + c3_0 + c4_0 + c5_0 + c6_0 + c7_0 + c8_0) + c9_0 by ring, prefix_value_8_0]
  dsimp [c9_0, freq9, u9, v9]
  ring_nf
theorem prefix_pos_9_0 : 0 < c0_0 + c1_0 + c2_0 + c3_0 + c4_0 + c5_0 + c6_0 + c7_0 + c8_0 + c9_0 := by
  rw [prefix_value_9_0]
  have hlo := d_bounds.1
  have hhi := d_bounds.2
  linarith
theorem prefix_value_9_1 : c0_1 + c1_1 + c2_1 + c3_1 + c4_1 + c5_1 + c6_1 + c7_1 + c8_1 + c9_1 = ((53765654227567257583616:ℝ)+((-30041991730140028338176:ℝ)/17)*d) := by
  rw [show c0_1 + c1_1 + c2_1 + c3_1 + c4_1 + c5_1 + c6_1 + c7_1 + c8_1 + c9_1 = (c0_1 + c1_1 + c2_1 + c3_1 + c4_1 + c5_1 + c6_1 + c7_1 + c8_1) + c9_1 by ring, prefix_value_8_1]
  dsimp [c9_1, freq9, u9, v9]
  ring_nf
theorem prefix_pos_9_1 : 0 < c0_1 + c1_1 + c2_1 + c3_1 + c4_1 + c5_1 + c6_1 + c7_1 + c8_1 + c9_1 := by
  rw [prefix_value_9_1]
  have hlo := d_bounds.1
  have hhi := d_bounds.2
  linarith
theorem prefix_value_9_2 : c0_2 + c1_2 + c2_2 + c3_2 + c4_2 + c5_2 + c6_2 + c7_2 + c8_2 + c9_2 = ((1654259978228153974784:ℝ)+((-785681995503065366528:ℝ)/17)*d) := by
  rw [show c0_2 + c1_2 + c2_2 + c3_2 + c4_2 + c5_2 + c6_2 + c7_2 + c8_2 + c9_2 = (c0_2 + c1_2 + c2_2 + c3_2 + c4_2 + c5_2 + c6_2 + c7_2 + c8_2) + c9_2 by ring, prefix_value_8_2]
  dsimp [c9_2, freq9, u9, v9]
  ring_nf
theorem prefix_pos_9_2 : 0 < c0_2 + c1_2 + c2_2 + c3_2 + c4_2 + c5_2 + c6_2 + c7_2 + c8_2 + c9_2 := by
  rw [prefix_value_9_2]
  have hlo := d_bounds.1
  have hhi := d_bounds.2
  linarith
theorem prefix_value_10_0 : c0_0 + c1_0 + c2_0 + c3_0 + c4_0 + c5_0 + c6_0 + c7_0 + c8_0 + c9_0 + c10_0 = ((429098914787163810824192:ℝ)+((-302602085372255487918080:ℝ)/17)*d) := by
  rw [show c0_0 + c1_0 + c2_0 + c3_0 + c4_0 + c5_0 + c6_0 + c7_0 + c8_0 + c9_0 + c10_0 = (c0_0 + c1_0 + c2_0 + c3_0 + c4_0 + c5_0 + c6_0 + c7_0 + c8_0 + c9_0) + c10_0 by ring, prefix_value_9_0]
  dsimp [c10_0, freq10, u10, v10]
  ring_nf
  simp only [d_power_2, d_power_3, d_power_4, d_power_5, d_power_6, d_power_7, d_power_8, d_power_9, d_power_10, d_power_11, d_power_12, d_power_13, d_power_14, d_power_15, d_power_16, d_power_17, d_power_18, d_power_19, d_power_20, d_power_21, d_power_22, d_power_23, d_power_24, d_power_25, d_power_26]; ring
theorem prefix_pos_10_0 : 0 < c0_0 + c1_0 + c2_0 + c3_0 + c4_0 + c5_0 + c6_0 + c7_0 + c8_0 + c9_0 + c10_0 := by
  rw [prefix_value_10_0]
  have hlo := d_bounds.1
  have hhi := d_bounds.2
  linarith
theorem prefix_value_10_1 : c0_1 + c1_1 + c2_1 + c3_1 + c4_1 + c5_1 + c6_1 + c7_1 + c8_1 + c9_1 + c10_1 = ((53798352353433337987072:ℝ)+((-30176809556845618790400:ℝ)/17)*d) := by
  rw [show c0_1 + c1_1 + c2_1 + c3_1 + c4_1 + c5_1 + c6_1 + c7_1 + c8_1 + c9_1 + c10_1 = (c0_1 + c1_1 + c2_1 + c3_1 + c4_1 + c5_1 + c6_1 + c7_1 + c8_1 + c9_1) + c10_1 by ring, prefix_value_9_1]
  dsimp [c10_1, freq10, u10, v10]
  ring_nf
  simp only [d_power_2, d_power_3, d_power_4, d_power_5, d_power_6, d_power_7, d_power_8, d_power_9, d_power_10, d_power_11, d_power_12, d_power_13, d_power_14, d_power_15, d_power_16, d_power_17, d_power_18, d_power_19, d_power_20, d_power_21, d_power_22, d_power_23, d_power_24, d_power_25, d_power_26]; ring
theorem prefix_pos_10_1 : 0 < c0_1 + c1_1 + c2_1 + c3_1 + c4_1 + c5_1 + c6_1 + c7_1 + c8_1 + c9_1 + c10_1 := by
  rw [prefix_value_10_1]
  have hlo := d_bounds.1
  have hhi := d_bounds.2
  linarith
theorem prefix_value_10_2 : c0_2 + c1_2 + c2_2 + c3_2 + c4_2 + c5_2 + c6_2 + c7_2 + c8_2 + c9_2 + c10_2 = ((1655070156881831395328:ℝ)+((-789022447667798081536:ℝ)/17)*d) := by
  rw [show c0_2 + c1_2 + c2_2 + c3_2 + c4_2 + c5_2 + c6_2 + c7_2 + c8_2 + c9_2 + c10_2 = (c0_2 + c1_2 + c2_2 + c3_2 + c4_2 + c5_2 + c6_2 + c7_2 + c8_2 + c9_2) + c10_2 by ring, prefix_value_9_2]
  dsimp [c10_2, freq10, u10, v10]
  ring_nf
  simp only [d_power_2, d_power_3, d_power_4, d_power_5, d_power_6, d_power_7, d_power_8, d_power_9, d_power_10, d_power_11, d_power_12, d_power_13, d_power_14, d_power_15, d_power_16, d_power_17, d_power_18, d_power_19, d_power_20, d_power_21, d_power_22, d_power_23, d_power_24, d_power_25, d_power_26]; ring
theorem prefix_pos_10_2 : 0 < c0_2 + c1_2 + c2_2 + c3_2 + c4_2 + c5_2 + c6_2 + c7_2 + c8_2 + c9_2 + c10_2 := by
  rw [prefix_value_10_2]
  have hlo := d_bounds.1
  have hhi := d_bounds.2
  linarith
theorem prefix_value_11_0 : c0_0 + c1_0 + c2_0 + c3_0 + c4_0 + c5_0 + c6_0 + c7_0 + c8_0 + c9_0 + c10_0 + c11_0 = ((355707128874106034847744:ℝ)+(0:ℝ)*d) := by
  rw [show c0_0 + c1_0 + c2_0 + c3_0 + c4_0 + c5_0 + c6_0 + c7_0 + c8_0 + c9_0 + c10_0 + c11_0 = (c0_0 + c1_0 + c2_0 + c3_0 + c4_0 + c5_0 + c6_0 + c7_0 + c8_0 + c9_0 + c10_0) + c11_0 by ring, prefix_value_10_0]
  dsimp [c11_0, freq11, u11, v11]
  ring_nf
  simp only [d_power_2, d_power_3, d_power_4, d_power_5, d_power_6, d_power_7, d_power_8, d_power_9, d_power_10, d_power_11, d_power_12, d_power_13, d_power_14, d_power_15, d_power_16, d_power_17, d_power_18, d_power_19, d_power_20, d_power_21, d_power_22, d_power_23, d_power_24, d_power_25, d_power_26]; ring
theorem prefix_pos_11_0 : 0 < c0_0 + c1_0 + c2_0 + c3_0 + c4_0 + c5_0 + c6_0 + c7_0 + c8_0 + c9_0 + c10_0 + c11_0 := by
  rw [prefix_value_11_0]
  have hlo := d_bounds.1
  have hhi := d_bounds.2
  linarith
theorem prefix_value_11_1 : c0_1 + c1_1 + c2_1 + c3_1 + c4_1 + c5_1 + c6_1 + c7_1 + c8_1 + c9_1 + c10_1 + c11_1 = ((46479400985961399582720:ℝ)+(0:ℝ)*d) := by
  rw [show c0_1 + c1_1 + c2_1 + c3_1 + c4_1 + c5_1 + c6_1 + c7_1 + c8_1 + c9_1 + c10_1 + c11_1 = (c0_1 + c1_1 + c2_1 + c3_1 + c4_1 + c5_1 + c6_1 + c7_1 + c8_1 + c9_1 + c10_1) + c11_1 by ring, prefix_value_10_1]
  dsimp [c11_1, freq11, u11, v11]
  ring_nf
  simp only [d_power_2, d_power_3, d_power_4, d_power_5, d_power_6, d_power_7, d_power_8, d_power_9, d_power_10, d_power_11, d_power_12, d_power_13, d_power_14, d_power_15, d_power_16, d_power_17, d_power_18, d_power_19, d_power_20, d_power_21, d_power_22, d_power_23, d_power_24, d_power_25, d_power_26]; ring
theorem prefix_pos_11_1 : 0 < c0_1 + c1_1 + c2_1 + c3_1 + c4_1 + c5_1 + c6_1 + c7_1 + c8_1 + c9_1 + c10_1 + c11_1 := by
  rw [prefix_value_11_1]
  have hlo := d_bounds.1
  have hhi := d_bounds.2
  linarith
theorem prefix_value_11_2 : c0_2 + c1_2 + c2_2 + c3_2 + c4_2 + c5_2 + c6_2 + c7_2 + c8_2 + c9_2 + c10_2 + c11_2 = ((1463704104369024663552:ℝ)+(0:ℝ)*d) := by
  rw [show c0_2 + c1_2 + c2_2 + c3_2 + c4_2 + c5_2 + c6_2 + c7_2 + c8_2 + c9_2 + c10_2 + c11_2 = (c0_2 + c1_2 + c2_2 + c3_2 + c4_2 + c5_2 + c6_2 + c7_2 + c8_2 + c9_2 + c10_2) + c11_2 by ring, prefix_value_10_2]
  dsimp [c11_2, freq11, u11, v11]
  ring_nf
  simp only [d_power_2, d_power_3, d_power_4, d_power_5, d_power_6, d_power_7, d_power_8, d_power_9, d_power_10, d_power_11, d_power_12, d_power_13, d_power_14, d_power_15, d_power_16, d_power_17, d_power_18, d_power_19, d_power_20, d_power_21, d_power_22, d_power_23, d_power_24, d_power_25, d_power_26]; ring
theorem prefix_pos_11_2 : 0 < c0_2 + c1_2 + c2_2 + c3_2 + c4_2 + c5_2 + c6_2 + c7_2 + c8_2 + c9_2 + c10_2 + c11_2 := by
  rw [prefix_value_11_2]
  have hlo := d_bounds.1
  have hhi := d_bounds.2
  linarith
end LogArctangentMean
