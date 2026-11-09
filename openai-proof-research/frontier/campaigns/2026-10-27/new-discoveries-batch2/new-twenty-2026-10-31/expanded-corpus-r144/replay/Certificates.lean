import C0R0
import C0R1
import C0R2
import C0R3
import C0R4
import C0R5
import C0R6
import C0R7
import C1R0
import C1R1
import C1R2
import C1R3
import C1R4
import C1R5
import C1R6
import C1R7
namespace Rainbow
theorem cert0 : ∀ x y, x ≠ y → CutCert G color0 x y (cut0 x y) (side0 x y) := by
  intro x y h
  fin_cases x <;> fin_cases y
  · exact (h rfl).elim
  · exact cert0_0_1
  · exact cert0_0_2
  · exact cert0_0_3
  · exact cert0_0_4
  · exact cert0_0_5
  · exact cert0_0_6
  · exact cert0_0_7
  · exact cert0_1_0
  · exact (h rfl).elim
  · exact cert0_1_2
  · exact cert0_1_3
  · exact cert0_1_4
  · exact cert0_1_5
  · exact cert0_1_6
  · exact cert0_1_7
  · exact cert0_2_0
  · exact cert0_2_1
  · exact (h rfl).elim
  · exact cert0_2_3
  · exact cert0_2_4
  · exact cert0_2_5
  · exact cert0_2_6
  · exact cert0_2_7
  · exact cert0_3_0
  · exact cert0_3_1
  · exact cert0_3_2
  · exact (h rfl).elim
  · exact cert0_3_4
  · exact cert0_3_5
  · exact cert0_3_6
  · exact cert0_3_7
  · exact cert0_4_0
  · exact cert0_4_1
  · exact cert0_4_2
  · exact cert0_4_3
  · exact (h rfl).elim
  · exact cert0_4_5
  · exact cert0_4_6
  · exact cert0_4_7
  · exact cert0_5_0
  · exact cert0_5_1
  · exact cert0_5_2
  · exact cert0_5_3
  · exact cert0_5_4
  · exact (h rfl).elim
  · exact cert0_5_6
  · exact cert0_5_7
  · exact cert0_6_0
  · exact cert0_6_1
  · exact cert0_6_2
  · exact cert0_6_3
  · exact cert0_6_4
  · exact cert0_6_5
  · exact (h rfl).elim
  · exact cert0_6_7
  · exact cert0_7_0
  · exact cert0_7_1
  · exact cert0_7_2
  · exact cert0_7_3
  · exact cert0_7_4
  · exact cert0_7_5
  · exact cert0_7_6
  · exact (h rfl).elim
theorem cert1 : ∀ x y, x ≠ y → CutCert Gᶜ color1 x y (cut1 x y) (side1 x y) := by
  intro x y h
  fin_cases x <;> fin_cases y
  · exact (h rfl).elim
  · exact cert1_0_1
  · exact cert1_0_2
  · exact cert1_0_3
  · exact cert1_0_4
  · exact cert1_0_5
  · exact cert1_0_6
  · exact cert1_0_7
  · exact cert1_1_0
  · exact (h rfl).elim
  · exact cert1_1_2
  · exact cert1_1_3
  · exact cert1_1_4
  · exact cert1_1_5
  · exact cert1_1_6
  · exact cert1_1_7
  · exact cert1_2_0
  · exact cert1_2_1
  · exact (h rfl).elim
  · exact cert1_2_3
  · exact cert1_2_4
  · exact cert1_2_5
  · exact cert1_2_6
  · exact cert1_2_7
  · exact cert1_3_0
  · exact cert1_3_1
  · exact cert1_3_2
  · exact (h rfl).elim
  · exact cert1_3_4
  · exact cert1_3_5
  · exact cert1_3_6
  · exact cert1_3_7
  · exact cert1_4_0
  · exact cert1_4_1
  · exact cert1_4_2
  · exact cert1_4_3
  · exact (h rfl).elim
  · exact cert1_4_5
  · exact cert1_4_6
  · exact cert1_4_7
  · exact cert1_5_0
  · exact cert1_5_1
  · exact cert1_5_2
  · exact cert1_5_3
  · exact cert1_5_4
  · exact (h rfl).elim
  · exact cert1_5_6
  · exact cert1_5_7
  · exact cert1_6_0
  · exact cert1_6_1
  · exact cert1_6_2
  · exact cert1_6_3
  · exact cert1_6_4
  · exact cert1_6_5
  · exact (h rfl).elim
  · exact cert1_6_7
  · exact cert1_7_0
  · exact cert1_7_1
  · exact cert1_7_2
  · exact cert1_7_3
  · exact cert1_7_4
  · exact cert1_7_5
  · exact cert1_7_6
  · exact (h rfl).elim
end Rainbow
