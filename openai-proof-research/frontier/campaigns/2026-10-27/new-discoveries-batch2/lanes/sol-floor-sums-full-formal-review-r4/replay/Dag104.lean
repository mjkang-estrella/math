import Dag103
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n14207 (_v : Vars) (_q : Query _v)  : (e13050 _v) := by
  have p10365 := n10365 _v _q 
  have p13054 := n13054 _v _q 
  simp only [e467, e468, e469, e470, e471, e474, e475, e479, e480, e488, e490, e493, e494, e5392, e5393, e5394, e5395, e5402, e5403, e5406, e5409, e5411, e8748, e8749, e13050, e13053] at *
  tauto
theorem n14208 (_v : Vars) (_q : Query _v)  : (e5409 _v) := by
  have p14207 := n14207 _v _q 
  simp only [e467, e468, e469, e470, e471, e474, e479, e488, e490, e493, e494, e5392, e5402, e5403, e5406, e5409, e5411, e8748, e8749, e13050] at *
  tauto
theorem n14209 (_v : Vars) (_q : Query _v)  : (e11640 _v) := by
  have p13060 := n13060 _v _q 
  have p11639 := n11639 _v _q 
  exact (Iff.trans p13060 p11639)
theorem n14210 (_v : Vars) (_q : Query _v)  : (e8762 _v) := by
  have p5414 := n5414 _v _q 
  have p14209 := n14209 _v _q 
  simp only [e498, e499, e500, e501, e502, e505, e506, e508, e509, e510, e514, e522, e524, e527, e528, e5412, e5413, e5421, e5422, e5425, e8752, e8759, e8760, e8761, e8762, e11640] at *
  tauto
theorem n14211 (_v : Vars) (_q : Query _v)  : (e8752 _v) := by
  have p14210 := n14210 _v _q 
  simp only [e498, e499, e500, e501, e502, e505, e506, e514, e522, e524, e527, e528, e5421, e5422, e5425, e8752, e8759, e8760, e8761, e8762] at *
  tauto
theorem n14212 (_v : Vars) (_q : Query _v)  : (e514 _v) := by
  have p14211 := n14211 _v _q 
  have p11641 := n11641 _v _q 
  simp only [e498, e499, e500, e501, e502, e505, e506, e514, e8752] at *
  tauto
theorem n14214 (_v : Vars) (_q : Query _v)  : (e14213 _v) := by
  have p13070 := n13070 _v _q 
  have p11673 := n11673 _v _q 
  exact (Eq.trans p13070 p11673)
theorem n14216 (_v : Vars) (_q : Query _v)  : (e14215 _v) := by
  have p13074 := n13074 _v _q 
  have p11682 := n11682 _v _q 
  exact (Eq.trans p13074 p11682)
theorem n14218 (_v : Vars) (_q : Query _v)  : (e14217 _v) := by
  have p13082 := n13082 _v _q 
  have p13090 := n13090 _v _q 
  have p13098 := n13098 _v _q 
  have p13106 := n13106 _v _q 
  change ((e8773 _v) = (e5599 _v)) at p13082
  change ((e8774 _v) = (e5609 _v)) at p13090
  change ((e8775 _v) = (e5619 _v)) at p13098
  change ((e8776 _v) = (e5629 _v)) at p13106
  simp only [e14217, e8777, e8948, p13082, p13090, p13098, p13106]
theorem n14220 (_v : Vars) (_q : Query _v)  : (e14219 _v) := by
  have p14218 := n14218 _v _q 
  change ((e8777 _v) = (e8948 _v)) at p14218
  simp only [e14219, e11646, e8949, p14218]
theorem n14222 (_v : Vars) (_q : Query _v)  : (e14221 _v) := by
  have p13110 := n13110 _v _q 
  have p11699 := n11699 _v _q 
  exact (Eq.trans p13110 p11699)
theorem n14224 (_v : Vars) (_q : Query _v)  : (e14223 _v) := by
  have p13118 := n13118 _v _q 
  have p13126 := n13126 _v _q 
  have p13134 := n13134 _v _q 
  have p13142 := n13142 _v _q 
  change ((e8783 _v) = (e5670 _v)) at p13118
  change ((e8784 _v) = (e5680 _v)) at p13126
  change ((e8785 _v) = (e5690 _v)) at p13134
  change ((e8786 _v) = (e5700 _v)) at p13142
  simp only [e14223, e8787, e8997, p13118, p13126, p13134, p13142]
theorem n14226 (_v : Vars) (_q : Query _v)  : (e14225 _v) := by
  have p14224 := n14224 _v _q 
  change ((e8787 _v) = (e8997 _v)) at p14224
  simp only [e14225, e11648, e8998, p14224]
theorem n14228 (_v : Vars) (_q : Query _v)  : (e14227 _v) := by
  have p13150 := n13150 _v _q 
  have p13158 := n13158 _v _q 
  have p13166 := n13166 _v _q 
  have p13174 := n13174 _v _q 
  change ((e8788 _v) = (e5706 _v)) at p13150
  change ((e8789 _v) = (e5716 _v)) at p13158
  change ((e8790 _v) = (e5726 _v)) at p13166
  change ((e8791 _v) = (e5736 _v)) at p13174
  simp only [e14227, e8792, e9012, p13150, p13158, p13166, p13174]
theorem n14230 (_v : Vars) (_q : Query _v)  : (e14229 _v) := by
  have p14228 := n14228 _v _q 
  change ((e8792 _v) = (e9012 _v)) at p14228
  simp only [e14229, e11649, e9013, p14228]
theorem n14232 (_v : Vars) (_q : Query _v)  : (e14231 _v) := by
  have p11717 := n11717 _v _q 
  change ((e626 _v) = (e1167 _v)) at p11717
  simp only [e14231, e627, e1170, p11717]
theorem n14234 (_v : Vars) (_q : Query _v)  : (e14233 _v) := by
  have p14232 := n14232 _v _q 
  have p13180 := n13180 _v _q 
  change ((e627 _v) ↔ (e1170 _v)) at p14232
  change ((e5454 _v) = (e1174 _v)) at p13180
  simp only [e14233, e8793, e5765, p14232, p13180]
theorem n14236 (_v : Vars) (_q : Query _v)  : (e14235 _v) := by
  have p11719 := n11719 _v _q 
  change ((e629 _v) = (e1177 _v)) at p11719
  simp only [e14235, e630, e1180, p11719]
theorem n14238 (_v : Vars) (_q : Query _v)  : (e14237 _v) := by
  have p14236 := n14236 _v _q 
  have p13186 := n13186 _v _q 
  change ((e630 _v) ↔ (e1180 _v)) at p14236
  change ((e5455 _v) = (e1184 _v)) at p13186
  simp only [e14237, e8794, e5766, p14236, p13186]
theorem n14240 (_v : Vars) (_q : Query _v)  : (e14239 _v) := by
  have p11721 := n11721 _v _q 
  change ((e632 _v) = (e1187 _v)) at p11721
  simp only [e14239, e633, e1190, p11721]
theorem n14242 (_v : Vars) (_q : Query _v)  : (e14241 _v) := by
  have p14240 := n14240 _v _q 
  have p13192 := n13192 _v _q 
  change ((e633 _v) ↔ (e1190 _v)) at p14240
  change ((e5456 _v) = (e1194 _v)) at p13192
  simp only [e14241, e8795, e5767, p14240, p13192]
theorem n14244 (_v : Vars) (_q : Query _v)  : (e14243 _v) := by
  have p11723 := n11723 _v _q 
  change ((e635 _v) = (e1197 _v)) at p11723
  simp only [e14243, e636, e1200, p11723]
theorem n14246 (_v : Vars) (_q : Query _v)  : (e14245 _v) := by
  have p14244 := n14244 _v _q 
  have p13198 := n13198 _v _q 
  change ((e636 _v) ↔ (e1200 _v)) at p14244
  change ((e5457 _v) = (e1204 _v)) at p13198
  simp only [e14245, e8796, e5768, p14244, p13198]
theorem n14248 (_v : Vars) (_q : Query _v)  : (e14247 _v) := by
  have p14234 := n14234 _v _q 
  have p14238 := n14238 _v _q 
  have p14242 := n14242 _v _q 
  have p14246 := n14246 _v _q 
  change ((e8793 _v) = (e5765 _v)) at p14234
  change ((e8794 _v) = (e5766 _v)) at p14238
  change ((e8795 _v) = (e5767 _v)) at p14242
  change ((e8796 _v) = (e5768 _v)) at p14246
  simp only [e14247, e8797, e5769, p14234, p14238, p14242, p14246]
theorem n14250 (_v : Vars) (_q : Query _v)  : (e14249 _v) := by
  have p13202 := n13202 _v _q 
  have p11732 := n11732 _v _q 
  exact (Eq.trans p13202 p11732)
theorem n14252 (_v : Vars) (_q : Query _v)  : (e14251 _v) := by
  have p13210 := n13210 _v _q 
  have p13218 := n13218 _v _q 
  have p13226 := n13226 _v _q 
  have p13234 := n13234 _v _q 
  change ((e8803 _v) = (e5815 _v)) at p13210
  change ((e8804 _v) = (e5825 _v)) at p13218
  change ((e8805 _v) = (e5835 _v)) at p13226
  change ((e8806 _v) = (e5845 _v)) at p13234
  simp only [e14251, e8807, e9072, p13210, p13218, p13226, p13234]
theorem n14254 (_v : Vars) (_q : Query _v)  : (e14253 _v) := by
  have p14252 := n14252 _v _q 
  change ((e8807 _v) = (e9072 _v)) at p14252
  simp only [e14253, e11652, e9073, p14252]
theorem n14256 (_v : Vars) (_q : Query _v)  : (e14255 _v) := by
  have p13242 := n13242 _v _q 
  have p13250 := n13250 _v _q 
  have p13258 := n13258 _v _q 
  have p13266 := n13266 _v _q 
  change ((e8808 _v) = (e5851 _v)) at p13242
  change ((e8809 _v) = (e5861 _v)) at p13250
  change ((e8810 _v) = (e5871 _v)) at p13258
  change ((e8811 _v) = (e5881 _v)) at p13266
  simp only [e14255, e8812, e9087, p13242, p13250, p13258, p13266]
theorem n14258 (_v : Vars) (_q : Query _v)  : (e14257 _v) := by
  have p14256 := n14256 _v _q 
  change ((e8812 _v) = (e9087 _v)) at p14256
  simp only [e14257, e11653, e9088, p14256]
theorem n14260 (_v : Vars) (_q : Query _v)  : (e14259 _v) := by
  have p11750 := n11750 _v _q 
  change ((e679 _v) = (e1370 _v)) at p11750
  simp only [e14259, e680, e1373, p11750]
theorem n14262 (_v : Vars) (_q : Query _v)  : (e14261 _v) := by
  have p14260 := n14260 _v _q 
  have p13272 := n13272 _v _q 
  change ((e680 _v) ↔ (e1373 _v)) at p14260
  change ((e5470 _v) = (e1377 _v)) at p13272
  simp only [e14261, e8813, e5910, p14260, p13272]
theorem n14264 (_v : Vars) (_q : Query _v)  : (e14263 _v) := by
  have p11752 := n11752 _v _q 
  change ((e682 _v) = (e1380 _v)) at p11752
  simp only [e14263, e683, e1383, p11752]
theorem n14266 (_v : Vars) (_q : Query _v)  : (e14265 _v) := by
  have p14264 := n14264 _v _q 
  have p13278 := n13278 _v _q 
  change ((e683 _v) ↔ (e1383 _v)) at p14264
  change ((e5471 _v) = (e1387 _v)) at p13278
  simp only [e14265, e8814, e5911, p14264, p13278]
theorem n14268 (_v : Vars) (_q : Query _v)  : (e14267 _v) := by
  have p11754 := n11754 _v _q 
  change ((e685 _v) = (e1390 _v)) at p11754
  simp only [e14267, e686, e1393, p11754]
theorem n14270 (_v : Vars) (_q : Query _v)  : (e14269 _v) := by
  have p14268 := n14268 _v _q 
  have p13284 := n13284 _v _q 
  change ((e686 _v) ↔ (e1393 _v)) at p14268
  change ((e5472 _v) = (e1397 _v)) at p13284
  simp only [e14269, e8815, e5912, p14268, p13284]
theorem n14272 (_v : Vars) (_q : Query _v)  : (e14271 _v) := by
  have p11756 := n11756 _v _q 
  change ((e688 _v) = (e1400 _v)) at p11756
  simp only [e14271, e689, e1403, p11756]
theorem n14274 (_v : Vars) (_q : Query _v)  : (e14273 _v) := by
  have p14272 := n14272 _v _q 
  have p13290 := n13290 _v _q 
  change ((e689 _v) ↔ (e1403 _v)) at p14272
  change ((e5473 _v) = (e1407 _v)) at p13290
  simp only [e14273, e8816, e5913, p14272, p13290]
theorem n14276 (_v : Vars) (_q : Query _v)  : (e14275 _v) := by
  have p14262 := n14262 _v _q 
  have p14266 := n14266 _v _q 
  have p14270 := n14270 _v _q 
  have p14274 := n14274 _v _q 
  change ((e8813 _v) = (e5910 _v)) at p14262
  change ((e8814 _v) = (e5911 _v)) at p14266
  change ((e8815 _v) = (e5912 _v)) at p14270
  change ((e8816 _v) = (e5913 _v)) at p14274
  simp only [e14275, e8817, e5914, p14262, p14266, p14270, p14274]
theorem n14278 (_v : Vars) (_q : Query _v)  : (e14277 _v) := by
  have p13298 := n13298 _v _q 
  have p13306 := n13306 _v _q 
  have p13314 := n13314 _v _q 
  have p13322 := n13322 _v _q 
  change ((e8818 _v) = (e5925 _v)) at p13298
  change ((e8819 _v) = (e5935 _v)) at p13306
  change ((e8820 _v) = (e5945 _v)) at p13314
  change ((e8821 _v) = (e5955 _v)) at p13322
  simp only [e14277, e8822, e9113, p13298, p13306, p13314, p13322]
theorem n14280 (_v : Vars) (_q : Query _v)  : (e14279 _v) := by
  have p14278 := n14278 _v _q 
  change ((e8822 _v) = (e9113 _v)) at p14278
  simp only [e14279, e11655, e9114, p14278]
theorem n14282 (_v : Vars) (_q : Query _v)  : (e14281 _v) := by
  have p11766 := n11766 _v _q 
  change ((e705 _v) = (e1458 _v)) at p11766
  simp only [e14281, e706, e1461, p11766]
theorem n14284 (_v : Vars) (_q : Query _v)  : (e14283 _v) := by
  have p14282 := n14282 _v _q 
  have p13328 := n13328 _v _q 
  change ((e706 _v) ↔ (e1461 _v)) at p14282
  change ((e5478 _v) = (e1465 _v)) at p13328
  simp only [e14283, e8823, e5984, p14282, p13328]
theorem n14286 (_v : Vars) (_q : Query _v)  : (e14285 _v) := by
  have p11768 := n11768 _v _q 
  change ((e708 _v) = (e1468 _v)) at p11768
  simp only [e14285, e709, e1471, p11768]
theorem n14288 (_v : Vars) (_q : Query _v)  : (e14287 _v) := by
  have p14286 := n14286 _v _q 
  have p13334 := n13334 _v _q 
  change ((e709 _v) ↔ (e1471 _v)) at p14286
  change ((e5479 _v) = (e1475 _v)) at p13334
  simp only [e14287, e8824, e5985, p14286, p13334]
theorem n14290 (_v : Vars) (_q : Query _v)  : (e14289 _v) := by
  have p11770 := n11770 _v _q 
  change ((e711 _v) = (e1478 _v)) at p11770
  simp only [e14289, e712, e1481, p11770]
end
end Assembly
