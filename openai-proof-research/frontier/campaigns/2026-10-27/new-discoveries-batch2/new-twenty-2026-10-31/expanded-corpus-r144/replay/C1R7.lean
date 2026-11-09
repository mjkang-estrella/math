import Base
namespace Rainbow
set_option synthInstance.maxSize 1000
set_option maxRecDepth 3000
set_option maxHeartbeats 3000000
theorem cert1_7_0 : CutCert Gᶜ color1 7 0 (cut1 7 0) (side1 7 0) := by
  dsimp [CutCert, RainbowOn, cut1, side1, color1]
  decide
theorem cert1_7_1 : CutCert Gᶜ color1 7 1 (cut1 7 1) (side1 7 1) := by
  dsimp [CutCert, RainbowOn, cut1, side1, color1]
  decide
theorem cert1_7_2 : CutCert Gᶜ color1 7 2 (cut1 7 2) (side1 7 2) := by
  dsimp [CutCert, RainbowOn, cut1, side1, color1]
  decide
theorem cert1_7_3 : CutCert Gᶜ color1 7 3 (cut1 7 3) (side1 7 3) := by
  dsimp [CutCert, RainbowOn, cut1, side1, color1]
  decide
theorem cert1_7_4 : CutCert Gᶜ color1 7 4 (cut1 7 4) (side1 7 4) := by
  dsimp [CutCert, RainbowOn, cut1, side1, color1]
  decide
theorem cert1_7_5 : CutCert Gᶜ color1 7 5 (cut1 7 5) (side1 7 5) := by
  dsimp [CutCert, RainbowOn, cut1, side1, color1]
  decide
theorem cert1_7_6 : CutCert Gᶜ color1 7 6 (cut1 7 6) (side1 7 6) := by
  dsimp [CutCert, RainbowOn, cut1, side1, color1]
  decide
end Rainbow
