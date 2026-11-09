import Base
namespace Rainbow
set_option synthInstance.maxSize 1000
set_option maxRecDepth 3000
set_option maxHeartbeats 3000000
theorem cert1_4_0 : CutCert Gᶜ color1 4 0 (cut1 4 0) (side1 4 0) := by
  dsimp [CutCert, RainbowOn, cut1, side1, color1]
  decide
theorem cert1_4_1 : CutCert Gᶜ color1 4 1 (cut1 4 1) (side1 4 1) := by
  dsimp [CutCert, RainbowOn, cut1, side1, color1]
  decide
theorem cert1_4_2 : CutCert Gᶜ color1 4 2 (cut1 4 2) (side1 4 2) := by
  dsimp [CutCert, RainbowOn, cut1, side1, color1]
  decide
theorem cert1_4_3 : CutCert Gᶜ color1 4 3 (cut1 4 3) (side1 4 3) := by
  dsimp [CutCert, RainbowOn, cut1, side1, color1]
  decide
theorem cert1_4_5 : CutCert Gᶜ color1 4 5 (cut1 4 5) (side1 4 5) := by
  dsimp [CutCert, RainbowOn, cut1, side1, color1]
  decide
theorem cert1_4_6 : CutCert Gᶜ color1 4 6 (cut1 4 6) (side1 4 6) := by
  dsimp [CutCert, RainbowOn, cut1, side1, color1]
  decide
theorem cert1_4_7 : CutCert Gᶜ color1 4 7 (cut1 4 7) (side1 4 7) := by
  dsimp [CutCert, RainbowOn, cut1, side1, color1]
  decide
end Rainbow
