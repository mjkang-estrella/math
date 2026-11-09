import Base
namespace Rainbow
set_option synthInstance.maxSize 1000
set_option maxRecDepth 3000
set_option maxHeartbeats 3000000
theorem cert1_6_0 : CutCert Gᶜ color1 6 0 (cut1 6 0) (side1 6 0) := by
  dsimp [CutCert, RainbowOn, cut1, side1, color1]
  decide
theorem cert1_6_1 : CutCert Gᶜ color1 6 1 (cut1 6 1) (side1 6 1) := by
  dsimp [CutCert, RainbowOn, cut1, side1, color1]
  decide
theorem cert1_6_2 : CutCert Gᶜ color1 6 2 (cut1 6 2) (side1 6 2) := by
  dsimp [CutCert, RainbowOn, cut1, side1, color1]
  decide
theorem cert1_6_3 : CutCert Gᶜ color1 6 3 (cut1 6 3) (side1 6 3) := by
  dsimp [CutCert, RainbowOn, cut1, side1, color1]
  decide
theorem cert1_6_4 : CutCert Gᶜ color1 6 4 (cut1 6 4) (side1 6 4) := by
  dsimp [CutCert, RainbowOn, cut1, side1, color1]
  decide
theorem cert1_6_5 : CutCert Gᶜ color1 6 5 (cut1 6 5) (side1 6 5) := by
  dsimp [CutCert, RainbowOn, cut1, side1, color1]
  decide
theorem cert1_6_7 : CutCert Gᶜ color1 6 7 (cut1 6 7) (side1 6 7) := by
  dsimp [CutCert, RainbowOn, cut1, side1, color1]
  decide
end Rainbow
