import Dag112
import generated.th_lemma_5
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n14728 (_v : Vars) (_q : Query _v)  : (e5095 _v) := by
  have p14149 := n14149 _v _q 
  simp only [e13, e28, e30, e34, e35, e5089, e5090, e5093, e5095, e5098, e5100, e5102, e5103, e5104, e5105, e5106, e8622, e8624, e8625, e8626] at *
  tauto
theorem n14729 (_v : Vars) (_q : Query _v)  : (e5140 _v) := by
  have p14158 := n14158 _v _q 
  simp only [e79, e89, e91, e94, e95, e5134, e5135, e5138, e5140, e5143, e5145, e5147, e5148, e5149, e5150, e5151, e8647, e8649, e8650, e8651] at *
  tauto
theorem n14730 (_v : Vars) (_q : Query _v)  : (e5206 _v) := by
  have p14170 := n14170 _v _q 
  simp only [e191, e192, e193, e194, e196, e5193, e5195, e5203, e5206, e5208, e5211, e5218, e5219, e5220, e5221, e5222, e8668, e8670, e8671, e8672] at *
  tauto
theorem n14731 (_v : Vars) (_q : Query _v)  : (e5235 _v) := by
  have p14178 := n14178 _v _q 
  simp only [e214, e225, e227, e230, e231, e5223, e5231, e5232, e5235, e5237, e5240, e5247, e5248, e5249, e5250, e5251, e8677, e8679, e8680, e8681] at *
  tauto
theorem n14732 (_v : Vars) (_q : Query _v)  : (e8668 _v) := by
  have p14170 := n14170 _v _q 
  simp only [e191, e192, e193, e194, e196, e5193, e5195, e5203, e5206, e5208, e5211, e5218, e5219, e5220, e5221, e5222, e8668, e8670, e8671, e8672] at *
  tauto
theorem n14733 (_v : Vars) (_q : Query _v) (h5218 : (e5218 _v)) : (e196 _v) := by
  have p14732 := n14732 _v _q 
  have p8687 := n8687 _v _q h5218
  simp only [e196, e5208, e5211, e5218, e5219, e5220, e5221, e8668] at *
  tauto
theorem n14734 (_v : Vars) (_q : Query _v) (h191 : (e191 _v)) (h5218 : (e5218 _v)) : (e7489 _v) := by
  have p8686 := n8686 _v _q h5218
  have p253 := n253 _v _q h191
  have p14733 := n14733 _v _q h5218
  exact FloorCertificate.node_14734 (e2 _v) (e7 _v) (e17 _v) (e45 _v) (e110 _v) (e188 _v) p8686 p253 p14733
theorem n14735 (_v : Vars) (_q : Query _v)  : (e5373 _v) := by
  have p14206 := n14206 _v _q 
  simp only [e436, e440, e441, e442, e443, e5360, e5362, e5370, e5373, e5375, e5378, e5385, e5386, e5387, e5388, e5389, e8737, e8739, e8740, e8741] at *
  tauto
theorem n14736 (_v : Vars) (_q : Query _v)  : (e472 _v) := by
  simp only [e467, e468, e469, e470, e471, e472] at *
  tauto
theorem n14737 (_v : Vars) (_q : Query _v) (h496 : (e496 _v)) : (e474 _v) := by
  have p5255 := n5255 _v _q 
  have p8144 := n8144 _v _q h496
  exact FloorCertificate.node_14737 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p5255 p8144
theorem n14738 (_v : Vars) (_q : Query _v) (h496 : (e496 _v)) : (e479 _v) := by
  have p14208 := n14208 _v _q 
  have p14737 := n14737 _v _q h496
  simp only [e467, e468, e469, e470, e471, e474, e479, e5392, e5409] at *
  tauto
theorem n14739 (_v : Vars) (_q : Query _v) (h496 : (e496 _v)) : (e467 _v) := by
  have p14736 := n14736 _v _q 
  have p14738 := n14738 _v _q h496
  simp only [e467, e468, e469, e470, e471, e472, e479] at *
  tauto
theorem n14742 (_v : Vars) (_q : Query _v)  : (e14741 _v) := by
  have p13066 := n13066 _v _q 
  have p14248 := n14248 _v _q 
  change ((e6 _v) = (e6 _v)) at p13066
  change ((e8797 _v) = (e5769 _v)) at p14248
  simp only [e14741, e11650, e14740, p14248]
theorem n14745 (_v : Vars) (_q : Query _v)  : (e14744 _v) := by
  have p13066 := n13066 _v _q 
  have p14276 := n14276 _v _q 
  change ((e6 _v) = (e6 _v)) at p13066
  change ((e8817 _v) = (e5914 _v)) at p14276
  simp only [e14744, e11654, e14743, p14276]
theorem n14748 (_v : Vars) (_q : Query _v)  : (e14747 _v) := by
  have p13066 := n13066 _v _q 
  have p14298 := n14298 _v _q 
  change ((e6 _v) = (e6 _v)) at p13066
  change ((e8827 _v) = (e5988 _v)) at p14298
  simp only [e14747, e11656, e14746, p14298]
theorem n14751 (_v : Vars) (_q : Query _v)  : (e14750 _v) := by
  have p13066 := n13066 _v _q 
  have p14316 := n14316 _v _q 
  change ((e6 _v) = (e6 _v)) at p13066
  change ((e8832 _v) = (e6026 _v)) at p14316
  simp only [e14750, e11657, e14749, p14316]
theorem n14753 (_v : Vars) (_q : Query _v)  : (e14752 _v) := by
  have p11793 := n11793 _v _q 
  change ((e732 _v) = (e1550 _v)) at p11793
  simp only [e14752, e5490, e1551, p11793]
theorem n14755 (_v : Vars) (_q : Query _v)  : (e14754 _v) := by
  have p14753 := n14753 _v _q 
  have p14322 := n14322 _v _q 
  change ((e5490 _v) ↔ (e1551 _v)) at p14753
  change ((e5492 _v) = (e6042 _v)) at p14322
  simp only [e14754, e5493, e9156, p14753, p14322]
theorem n14757 (_v : Vars) (_q : Query _v)  : (e14756 _v) := by
  have p11800 := n11800 _v _q 
  change ((e733 _v) = (e1557 _v)) at p11800
  simp only [e14756, e5494, e1558, p11800]
theorem n14759 (_v : Vars) (_q : Query _v)  : (e14758 _v) := by
  have p14757 := n14757 _v _q 
  have p14324 := n14324 _v _q 
  change ((e5494 _v) ↔ (e1558 _v)) at p14757
  change ((e5496 _v) = (e6045 _v)) at p14324
  simp only [e14758, e5497, e9157, p14757, p14324]
theorem n14761 (_v : Vars) (_q : Query _v)  : (e14760 _v) := by
  have p11807 := n11807 _v _q 
  change ((e734 _v) = (e1564 _v)) at p11807
  simp only [e14760, e5498, e1565, p11807]
theorem n14763 (_v : Vars) (_q : Query _v)  : (e14762 _v) := by
  have p14761 := n14761 _v _q 
  have p14326 := n14326 _v _q 
  change ((e5498 _v) ↔ (e1565 _v)) at p14761
  change ((e5500 _v) = (e6048 _v)) at p14326
  simp only [e14762, e5501, e9158, p14761, p14326]
theorem n14764 (_v : Vars) (_q : Query _v)  : (e3056 _v) := by
  simp only [e3051, e3052, e3053, e3054, e3055, e3056] at *
  tauto
theorem n14765 (_v : Vars) (_q : Query _v) (h496 : (e496 _v)) : (e3061 _v) := by
  have p14350 := n14350 _v _q 
  have p8144 := n8144 _v _q h496
  simp only [e496, e3051, e3052, e3053, e3054, e3055, e3061, e6720, e6836] at *
  tauto
theorem n14766 (_v : Vars) (_q : Query _v) (h496 : (e496 _v)) : (e3051 _v) := by
  have p14764 := n14764 _v _q 
  have p14765 := n14765 _v _q h496
  simp only [e3051, e3052, e3053, e3054, e3055, e3056, e3061] at *
  tauto
theorem n14767 (_v : Vars) (_q : Query _v) (h2771 : (e2771 _v)) : (e3061 _v) := by
  have p14350 := n14350 _v _q 
  have p14096 := n14096 _v _q h2771
  simp only [e496, e3051, e3052, e3053, e3054, e3055, e3061, e6720, e6836] at *
  tauto
theorem n14768 (_v : Vars) (_q : Query _v) (h2771 : (e2771 _v)) : (e3051 _v) := by
  have p14764 := n14764 _v _q 
  have p14767 := n14767 _v _q h2771
  simp only [e3051, e3052, e3053, e3054, e3055, e3056, e3061] at *
  tauto
theorem n14769 (_v : Vars) (_q : Query _v)  : (e6889 _v) := by
  simp only [e3167, e3168, e3169, e3170, e6888, e6889] at *
  tauto
theorem n14770 (_v : Vars) (_q : Query _v) (h3178 : (e3178 _v)) : (e6700 _v) := by
  have p14361 := n14361 _v _q 
  have p6909 := n6909 _v _q h3178
  simp only [e2634, e3172, e3173, e3177, e3178, e3179, e3180, e6700, e6902] at *
  tauto
theorem n14771 (_v : Vars) (_q : Query _v) (h3178 : (e3178 _v)) : (e6896 _v) := by
  have p14360 := n14360 _v _q 
  have p14770 := n14770 _v _q h3178
  simp only [e2634, e3167, e3168, e3169, e3170, e6700, e6888, e6896, e6899] at *
  tauto
theorem n14772 (_v : Vars) (_q : Query _v) (h3178 : (e3178 _v)) : (e3169 _v) := by
  have p14769 := n14769 _v _q 
  have p14771 := n14771 _v _q h3178
  simp only [e3167, e3168, e3169, e3170, e6888, e6889, e6896] at *
  tauto
theorem n14773 (_v : Vars) (_q : Query _v)  : (e10600 _v) := by
  have p14367 := n14367 _v _q 
  simp only [e2641, e3200, e3202, e3205, e3206, e6910, e6911, e6912, e6913, e6914, e6920, e6921, e6924, e6926, e6931, e6932, e10600, e10602, e10603, e10604] at *
  tauto
theorem n14774 (_v : Vars) (_q : Query _v)  : (e6924 _v) := by
  have p10896 := n10896 _v _q 
  have p10893 := n10893 _v _q 
  exact FloorCertificate.node_14774 (e2 _v) (e9 _v) (e45 _v) p10896 p10893
theorem n14775 (_v : Vars) (_q : Query _v)  : (e6931 _v) := by
  have p14773 := n14773 _v _q 
  have p14774 := n14774 _v _q 
  simp only [e2641, e6910, e6911, e6912, e6913, e6914, e6924, e6931, e10600] at *
  tauto
theorem n14776 (_v : Vars) (_q : Query _v)  : (e6966 _v) := by
  simp only [e3265, e3266, e3267, e3268, e6965, e6966] at *
  tauto
theorem n14777 (_v : Vars) (_q : Query _v) (h3276 : (e3276 _v)) : (e6555 _v) := by
  have p14378 := n14378 _v _q 
  have p6984 := n6984 _v _q h3276
  simp only [e2310, e3270, e3271, e3275, e3276, e3277, e3278, e6555, e6979] at *
  tauto
theorem n14778 (_v : Vars) (_q : Query _v) (h3276 : (e3276 _v)) : (e6973 _v) := by
  have p14377 := n14377 _v _q 
  have p14777 := n14777 _v _q h3276
  simp only [e2310, e3265, e3266, e3267, e3268, e6555, e6965, e6973, e6976] at *
  tauto
theorem n14779 (_v : Vars) (_q : Query _v) (h3276 : (e3276 _v)) : (e3267 _v) := by
  have p14776 := n14776 _v _q 
  have p14778 := n14778 _v _q h3276
  simp only [e3265, e3266, e3267, e3268, e6965, e6966, e6973] at *
  tauto
theorem n14780 (_v : Vars) (_q : Query _v)  : (e10639 _v) := by
  have p14384 := n14384 _v _q 
  simp only [e2317, e3298, e3300, e3303, e3304, e6985, e6986, e6987, e6988, e6989, e6995, e6996, e6999, e7001, e7006, e7007, e10639, e10641, e10642, e10643] at *
  tauto
theorem n14781 (_v : Vars) (_q : Query _v)  : (e6999 _v) := by
  have p11375 := n11375 _v _q 
  have p10896 := n10896 _v _q 
  exact FloorCertificate.node_14781 (e2 _v) (e9 _v) (e110 _v) p11375 p10896
theorem n14782 (_v : Vars) (_q : Query _v)  : (e7006 _v) := by
  have p14780 := n14780 _v _q 
  have p14781 := n14781 _v _q 
  simp only [e2317, e6985, e6986, e6987, e6988, e6989, e6999, e7006, e10639] at *
  tauto
theorem n14783 (_v : Vars) (_q : Query _v)  : (e7182 _v) := by
  simp only [e3583, e3585, e3588, e3589, e7169, e7182] at *
  tauto
theorem n14784 (_v : Vars) (_q : Query _v) (h3571 : (e3571 _v)) : (e6656 _v) := by
  have p14426 := n14426 _v _q 
  have p7181 := n7181 _v _q h3571
  simp only [e2536, e3565, e3566, e3570, e3571, e3572, e3573, e6656, e7176] at *
  tauto
theorem n14785 (_v : Vars) (_q : Query _v) (h3571 : (e3571 _v)) : (e7170 _v) := by
  have p14427 := n14427 _v _q 
  have p14784 := n14784 _v _q h3571
  simp only [e2536, e3583, e3585, e3588, e3589, e6656, e7169, e7170, e7173] at *
  tauto
theorem n14786 (_v : Vars) (_q : Query _v) (h3571 : (e3571 _v)) : (e3585 _v) := by
  have p14783 := n14783 _v _q 
  have p14785 := n14785 _v _q h3571
  simp only [e3583, e3585, e3588, e3589, e7169, e7170, e7182] at *
  tauto
end
end Assembly
