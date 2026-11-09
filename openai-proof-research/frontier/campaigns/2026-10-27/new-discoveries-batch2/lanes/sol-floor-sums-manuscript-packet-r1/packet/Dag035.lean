import Dag034
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n8655 (_v : Vars) (_q : Query _v)  : (e8654 _v) := by
  have p8653 := n8653 _v _q 
  change ((e114 _v) ↔ (e118 _v)) at p8653
  simp only [e8654, e5154, e5170, p8653]
theorem n8657 (_v : Vars) (_q : Query _v)  : (e8656 _v) := by
  have p5162 := n5162 _v _q 
  have p5166 := n5166 _v _q 
  exact (Iff.trans p5162 p5166)
theorem n8660 (_v : Vars) (_q : Query _v)  : (e149 _v) := by
  have p147 := n147 _v _q 
  change ((e142 _v) = (e145 _v)) at p147
  simp only [e149, e143, e148, p147]
theorem n8661 (_v : Vars) (_q : Query _v)  : (e152 _v) := by
  simp only [e5, e6, e12, e36, e41, e145, e148, e150, e151, e152] at *
  omega
theorem n8662 (_v : Vars) (_q : Query _v)  : (e153 _v) := by
  have p8660 := n8660 _v _q 
  have p8661 := n8661 _v _q 
  exact (Iff.trans p8660 p8661)
theorem n8663 (_v : Vars) (_q : Query _v)  : (e151 _v) := by
  have p5174 := n5174 _v _q 
  have p8662 := n8662 _v _q 
  simp only [e143, e151, e153] at *
  tauto
theorem n8665 (_v : Vars) (_q : Query _v)  : (e8664 _v) := by
  have p5202 := n5202 _v _q 
  have p5205 := n5205 _v _q 
  exact (Iff.trans p5202 p5205)
theorem n8667 (_v : Vars) (_q : Query _v)  : (e8666 _v) := by
  simp only [e5, e6, e8, e12, e41, e46, e111, e210, e5208, e5211, e5215, e5218, e5219, e5220, e5221, e8666] at *
  omega
theorem n8674 (_v : Vars) (_q : Query _v)  : (e8673 _v) := by
  have p5230 := n5230 _v _q 
  have p5234 := n5234 _v _q 
  exact (Iff.trans p5230 p5234)
theorem n8676 (_v : Vars) (_q : Query _v)  : (e8675 _v) := by
  simp only [e5, e6, e10, e12, e41, e46, e111, e212, e5237, e5240, e5244, e5247, e5248, e5249, e5250, e8675] at *
  omega
theorem n8682 (_v : Vars) (_q : Query _v)  : (e5252 _v) := by
  simp only [e5237, e5240, e5247, e5248, e5249, e5252] at *
  tauto
theorem n8683 (_v : Vars) (_q : Query _v) (h5247 : (e5247 _v)) : (e5247 _v) := by
  exact h5247
theorem n8684 (_v : Vars) (_q : Query _v) (h5247 : (e5247 _v)) : (e5249 _v) := by
  have p8682 := n8682 _v _q 
  have p8683 := n8683 _v _q h5247
  simp only [e5237, e5240, e5247, e5248, e5249, e5252] at *
  tauto
theorem n8685 (_v : Vars) (_q : Query _v)  : (e5258 _v) := by
  simp only [e5208, e5211, e5218, e5219, e5220, e5258] at *
  tauto
theorem n8686 (_v : Vars) (_q : Query _v) (h5218 : (e5218 _v)) : (e5218 _v) := by
  exact h5218
theorem n8687 (_v : Vars) (_q : Query _v) (h5218 : (e5218 _v)) : (e5220 _v) := by
  have p8685 := n8685 _v _q 
  have p8686 := n8686 _v _q h5218
  simp only [e5208, e5211, e5218, e5219, e5220, e5258] at *
  tauto
theorem n8689 (_v : Vars) (_q : Query _v)  : (e8688 _v) := by
  have p273 := n273 _v _q 
  have p5264 := n5264 _v _q 
  exact (Iff.trans p273 p5264)
theorem n8691 (_v : Vars) (_q : Query _v)  : (e8690 _v) := by
  have p8689 := n8689 _v _q 
  change ((e270 _v) ↔ (e274 _v)) at p8689
  simp only [e8690, e5260, e5276, p8689]
theorem n8693 (_v : Vars) (_q : Query _v)  : (e8692 _v) := by
  have p5268 := n5268 _v _q 
  have p5272 := n5272 _v _q 
  exact (Iff.trans p5268 p5272)
theorem n8697 (_v : Vars) (_q : Query _v)  : (e8696 _v) := by
  have p309 := n309 _v _q 
  have p5284 := n5284 _v _q 
  exact (Iff.trans p309 p5284)
theorem n8699 (_v : Vars) (_q : Query _v)  : (e8698 _v) := by
  have p8697 := n8697 _v _q 
  change ((e306 _v) ↔ (e310 _v)) at p8697
  simp only [e8698, e5280, e5296, p8697]
theorem n8701 (_v : Vars) (_q : Query _v)  : (e8700 _v) := by
  have p5288 := n5288 _v _q 
  have p5292 := n5292 _v _q 
  exact (Iff.trans p5288 p5292)
theorem n8705 (_v : Vars) (_q : Query _v)  : (e8704 _v) := by
  have p344 := n344 _v _q 
  have p5304 := n5304 _v _q 
  exact (Iff.trans p344 p5304)
theorem n8707 (_v : Vars) (_q : Query _v)  : (e8706 _v) := by
  have p8705 := n8705 _v _q 
  change ((e341 _v) ↔ (e345 _v)) at p8705
  simp only [e8706, e5300, e5316, p8705]
theorem n8709 (_v : Vars) (_q : Query _v)  : (e8708 _v) := by
  have p5308 := n5308 _v _q 
  have p5312 := n5312 _v _q 
  exact (Iff.trans p5308 p5312)
theorem n8713 (_v : Vars) (_q : Query _v)  : (e8712 _v) := by
  have p374 := n374 _v _q 
  have p5324 := n5324 _v _q 
  exact (Iff.trans p374 p5324)
theorem n8715 (_v : Vars) (_q : Query _v)  : (e8714 _v) := by
  have p8713 := n8713 _v _q 
  change ((e371 _v) ↔ (e375 _v)) at p8713
  simp only [e8714, e5320, e5336, p8713]
theorem n8717 (_v : Vars) (_q : Query _v)  : (e8716 _v) := by
  have p5328 := n5328 _v _q 
  have p5332 := n5332 _v _q 
  exact (Iff.trans p5328 p5332)
theorem n8721 (_v : Vars) (_q : Query _v)  : (e8720 _v) := by
  have p419 := n419 _v _q 
  have p5350 := n5350 _v _q 
  exact (Iff.trans p419 p5350)
theorem n8724 (_v : Vars) (_q : Query _v)  : (e8723 _v) := by
  have p8721 := n8721 _v _q 
  change ((e416 _v) ↔ (e420 _v)) at p8721
  simp only [e8723, e5346, e8722, p8721]
theorem n8726 (_v : Vars) (_q : Query _v)  : (e8725 _v) := by
  have p5354 := n5354 _v _q 
  have p5358 := n5358 _v _q 
  exact (Iff.trans p5354 p5358)
theorem n8734 (_v : Vars) (_q : Query _v)  : (e8733 _v) := by
  have p5369 := n5369 _v _q 
  have p5372 := n5372 _v _q 
  exact (Iff.trans p5369 p5372)
theorem n8736 (_v : Vars) (_q : Query _v)  : (e8735 _v) := by
  simp only [e5, e6, e8, e10, e12, e41, e46, e111, e457, e5375, e5378, e5382, e5385, e5386, e5387, e5388, e8735] at *
  omega
theorem n8743 (_v : Vars) (_q : Query _v)  : (e8742 _v) := by
  have p478 := n478 _v _q 
  have p5397 := n5397 _v _q 
  exact (Iff.trans p478 p5397)
theorem n8745 (_v : Vars) (_q : Query _v)  : (e8744 _v) := by
  have p8743 := n8743 _v _q 
  change ((e475 _v) ↔ (e479 _v)) at p8743
  simp only [e8744, e5393, e5409, p8743]
theorem n8747 (_v : Vars) (_q : Query _v)  : (e8746 _v) := by
  have p5401 := n5401 _v _q 
  have p5405 := n5405 _v _q 
  exact (Iff.trans p5401 p5405)
theorem n8751 (_v : Vars) (_q : Query _v)  : (e8750 _v) := by
  have p513 := n513 _v _q 
  have p5416 := n5416 _v _q 
  exact (Iff.trans p513 p5416)
theorem n8754 (_v : Vars) (_q : Query _v)  : (e8753 _v) := by
  have p8751 := n8751 _v _q 
  change ((e510 _v) ↔ (e514 _v)) at p8751
  simp only [e8753, e5412, e8752, p8751]
theorem n8756 (_v : Vars) (_q : Query _v)  : (e8755 _v) := by
  have p5420 := n5420 _v _q 
  have p5424 := n5424 _v _q 
  exact (Iff.trans p5420 p5424)
theorem n8833 (_v : Vars) (_q : Query _v)  : (e746 _v) := by
  have p5504 := n5504 _v _q 
  change ((e532 _v) = (e142 _v)) at p5504
  simp only [e746, e745, e143, p5504]
theorem n8834 (_v : Vars) (_q : Query _v)  : (e748 _v) := by
  have p5504 := n5504 _v _q 
  change ((e532 _v) = (e142 _v)) at p5504
  simp only [e748, e533, e747, p5504]
theorem n8835 (_v : Vars) (_q : Query _v)  : (e750 _v) := by
  simp only [e5, e6, e12, e36, e142, e747, e749, e750] at *
  omega
theorem n8836 (_v : Vars) (_q : Query _v)  : (e751 _v) := by
  have p8834 := n8834 _v _q 
  have p8835 := n8835 _v _q 
  exact (Iff.trans p8834 p8835)
theorem n8838 (_v : Vars) (_q : Query _v)  : (e8837 _v) := by
  have p8836 := n8836 _v _q 
  have p5504 := n5504 _v _q 
  change ((e533 _v) ↔ (e749 _v)) at p8836
  change ((e532 _v) = (e142 _v)) at p5504
  simp only [e8837, e534, e752, p8836, p5504]
theorem n8840 (_v : Vars) (_q : Query _v)  : (e8839 _v) := by
  have p8833 := n8833 _v _q 
  have p8838 := n8838 _v _q 
  change ((e745 _v) ↔ (e143 _v)) at p8833
  change ((e534 _v) = (e752 _v)) at p8838
  simp only [e8839, e5426, e5505, p8833, p8838]
end
end Assembly
