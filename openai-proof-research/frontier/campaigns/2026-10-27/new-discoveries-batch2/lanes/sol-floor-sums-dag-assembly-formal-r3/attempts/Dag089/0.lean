import Dag088
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n13186 (_v : Vars) (_q : Query _v)  : (e13185 _v) := by
  have p13184 := n13184 _v _q 
  have p11719 := n11719 _v _q 
  change ((e631 _v) ↔ (e1183 _v)) at p13184
  change ((e629 _v) = (e1177 _v)) at p11719
  simp only [e13185, e5455, e1184, p13184, p11719]
theorem n13188 (_v : Vars) (_q : Query _v)  : (e13187 _v) := by
  have p11721 := n11721 _v _q 
  change ((e632 _v) = (e1187 _v)) at p11721
  simp only [e13187, e634, e1191, p11721]
theorem n13189 (_v : Vars) (_q : Query _v)  : (e5755 _v) := by
  simp only [e12, e266, e781, e782, e1187, e1191, e1192, e1193, e5755] at *
  omega
theorem n13190 (_v : Vars) (_q : Query _v)  : (e5756 _v) := by
  have p13188 := n13188 _v _q 
  have p13189 := n13189 _v _q 
  exact (Iff.trans p13188 p13189)
theorem n13192 (_v : Vars) (_q : Query _v)  : (e13191 _v) := by
  have p13190 := n13190 _v _q 
  have p11721 := n11721 _v _q 
  change ((e634 _v) ↔ (e1193 _v)) at p13190
  change ((e632 _v) = (e1187 _v)) at p11721
  simp only [e13191, e5456, e1194, p13190, p11721]
theorem n13194 (_v : Vars) (_q : Query _v)  : (e13193 _v) := by
  have p11723 := n11723 _v _q 
  change ((e635 _v) = (e1197 _v)) at p11723
  simp only [e13193, e637, e1201, p11723]
theorem n13195 (_v : Vars) (_q : Query _v)  : (e5763 _v) := by
  simp only [e12, e108, e802, e803, e1197, e1201, e1202, e1203, e5763] at *
  omega
theorem n13196 (_v : Vars) (_q : Query _v)  : (e5764 _v) := by
  have p13194 := n13194 _v _q 
  have p13195 := n13195 _v _q 
  exact (Iff.trans p13194 p13195)
theorem n13198 (_v : Vars) (_q : Query _v)  : (e13197 _v) := by
  have p13196 := n13196 _v _q 
  have p11723 := n11723 _v _q 
  change ((e637 _v) ↔ (e1203 _v)) at p13196
  change ((e635 _v) = (e1197 _v)) at p11723
  simp only [e13197, e5457, e1204, p13196, p11723]
theorem n13200 (_v : Vars) (_q : Query _v)  : (e13199 _v) := by
  have p11728 := n11728 _v _q 
  have p9039 := n9039 _v _q 
  have p9047 := n9047 _v _q 
  have p9055 := n9055 _v _q 
  change ((e8798 _v) = (e5779 _v)) at p11728
  change ((e8799 _v) = (e5789 _v)) at p9039
  change ((e8800 _v) = (e5799 _v)) at p9047
  change ((e8801 _v) = (e5809 _v)) at p9055
  simp only [e13199, e8802, e11729, p11728, p9039, p9047, p9055]
theorem n13202 (_v : Vars) (_q : Query _v)  : (e13201 _v) := by
  have p13066 := n13066 _v _q 
  have p13200 := n13200 _v _q 
  change ((e6 _v) = (e6 _v)) at p13066
  change ((e8802 _v) = (e11729 _v)) at p13200
  simp only [e13201, e11651, e11730, p13066, p13200]
theorem n13203 (_v : Vars) (_q : Query _v)  : (e5812 _v) := by
  have p11734 := n11734 _v _q 
  change ((e653 _v) = (e1282 _v)) at p11734
  simp only [e5812, e654, e1804, p11734]
theorem n13204 (_v : Vars) (_q : Query _v)  : (e5813 _v) := by
  have p11734 := n11734 _v _q 
  change ((e653 _v) = (e1282 _v)) at p11734
  simp only [e5813, e655, e1285, p11734]
theorem n13205 (_v : Vars) (_q : Query _v)  : (e1288 _v) := by
  simp only [e5, e6, e12, e36, e1282, e1285, e1286, e1287, e1288] at *
  omega
theorem n13206 (_v : Vars) (_q : Query _v)  : (e5814 _v) := by
  have p13204 := n13204 _v _q 
  have p13205 := n13205 _v _q 
  exact (Iff.trans p13204 p13205)
theorem n13208 (_v : Vars) (_q : Query _v)  : (e13207 _v) := by
  have p13206 := n13206 _v _q 
  have p11734 := n11734 _v _q 
  change ((e655 _v) ↔ (e1287 _v)) at p13206
  change ((e653 _v) = (e1282 _v)) at p11734
  simp only [e13207, e5462, e1289, p13206, p11734]
theorem n13210 (_v : Vars) (_q : Query _v)  : (e13209 _v) := by
  have p13203 := n13203 _v _q 
  have p13208 := n13208 _v _q 
  change ((e654 _v) ↔ (e1804 _v)) at p13203
  change ((e5462 _v) = (e1289 _v)) at p13208
  simp only [e13209, e8803, e5815, p13203, p13208]
theorem n13211 (_v : Vars) (_q : Query _v)  : (e5822 _v) := by
  have p11736 := n11736 _v _q 
  change ((e656 _v) = (e1292 _v)) at p11736
  simp only [e5822, e657, e1811, p11736]
theorem n13212 (_v : Vars) (_q : Query _v)  : (e5823 _v) := by
  have p11736 := n11736 _v _q 
  change ((e656 _v) = (e1292 _v)) at p11736
  simp only [e5823, e658, e1295, p11736]
theorem n13213 (_v : Vars) (_q : Query _v)  : (e1298 _v) := by
  simp only [e12, e43, e760, e761, e1292, e1295, e1296, e1297, e1298] at *
  omega
theorem n13214 (_v : Vars) (_q : Query _v)  : (e5824 _v) := by
  have p13212 := n13212 _v _q 
  have p13213 := n13213 _v _q 
  exact (Iff.trans p13212 p13213)
theorem n13216 (_v : Vars) (_q : Query _v)  : (e13215 _v) := by
  have p13214 := n13214 _v _q 
  have p11736 := n11736 _v _q 
  change ((e658 _v) ↔ (e1297 _v)) at p13214
  change ((e656 _v) = (e1292 _v)) at p11736
  simp only [e13215, e5463, e1299, p13214, p11736]
theorem n13218 (_v : Vars) (_q : Query _v)  : (e13217 _v) := by
  have p13211 := n13211 _v _q 
  have p13216 := n13216 _v _q 
  change ((e657 _v) ↔ (e1811 _v)) at p13211
  change ((e5463 _v) = (e1299 _v)) at p13216
  simp only [e13217, e8804, e5825, p13211, p13216]
theorem n13219 (_v : Vars) (_q : Query _v)  : (e5832 _v) := by
  have p11738 := n11738 _v _q 
  change ((e659 _v) = (e1302 _v)) at p11738
  simp only [e5832, e660, e1818, p11738]
theorem n13220 (_v : Vars) (_q : Query _v)  : (e5833 _v) := by
  have p11738 := n11738 _v _q 
  change ((e659 _v) = (e1302 _v)) at p11738
  simp only [e5833, e661, e1305, p11738]
theorem n13221 (_v : Vars) (_q : Query _v)  : (e1308 _v) := by
  simp only [e12, e266, e781, e782, e1302, e1305, e1306, e1307, e1308] at *
  omega
theorem n13222 (_v : Vars) (_q : Query _v)  : (e5834 _v) := by
  have p13220 := n13220 _v _q 
  have p13221 := n13221 _v _q 
  exact (Iff.trans p13220 p13221)
theorem n13224 (_v : Vars) (_q : Query _v)  : (e13223 _v) := by
  have p13222 := n13222 _v _q 
  have p11738 := n11738 _v _q 
  change ((e661 _v) ↔ (e1307 _v)) at p13222
  change ((e659 _v) = (e1302 _v)) at p11738
  simp only [e13223, e5464, e1309, p13222, p11738]
theorem n13226 (_v : Vars) (_q : Query _v)  : (e13225 _v) := by
  have p13219 := n13219 _v _q 
  have p13224 := n13224 _v _q 
  change ((e660 _v) ↔ (e1818 _v)) at p13219
  change ((e5464 _v) = (e1309 _v)) at p13224
  simp only [e13225, e8805, e5835, p13219, p13224]
theorem n13227 (_v : Vars) (_q : Query _v)  : (e5842 _v) := by
  have p11740 := n11740 _v _q 
  change ((e662 _v) = (e1312 _v)) at p11740
  simp only [e5842, e663, e1825, p11740]
theorem n13228 (_v : Vars) (_q : Query _v)  : (e5843 _v) := by
  have p11740 := n11740 _v _q 
  change ((e662 _v) = (e1312 _v)) at p11740
  simp only [e5843, e664, e1315, p11740]
theorem n13229 (_v : Vars) (_q : Query _v)  : (e1318 _v) := by
  simp only [e12, e108, e802, e803, e1312, e1315, e1316, e1317, e1318] at *
  omega
theorem n13230 (_v : Vars) (_q : Query _v)  : (e5844 _v) := by
  have p13228 := n13228 _v _q 
  have p13229 := n13229 _v _q 
  exact (Iff.trans p13228 p13229)
theorem n13232 (_v : Vars) (_q : Query _v)  : (e13231 _v) := by
  have p13230 := n13230 _v _q 
  have p11740 := n11740 _v _q 
  change ((e664 _v) ↔ (e1317 _v)) at p13230
  change ((e662 _v) = (e1312 _v)) at p11740
  simp only [e13231, e5465, e1319, p13230, p11740]
theorem n13234 (_v : Vars) (_q : Query _v)  : (e13233 _v) := by
  have p13227 := n13227 _v _q 
  have p13232 := n13232 _v _q 
  change ((e663 _v) ↔ (e1825 _v)) at p13227
  change ((e5465 _v) = (e1319 _v)) at p13232
  simp only [e13233, e8806, e5845, p13227, p13232]
theorem n13235 (_v : Vars) (_q : Query _v)  : (e5848 _v) := by
  have p11742 := n11742 _v _q 
  change ((e666 _v) = (e1326 _v)) at p11742
  simp only [e5848, e667, e1832, p11742]
theorem n13236 (_v : Vars) (_q : Query _v)  : (e5849 _v) := by
  have p11742 := n11742 _v _q 
  change ((e666 _v) = (e1326 _v)) at p11742
  simp only [e5849, e668, e1329, p11742]
theorem n13237 (_v : Vars) (_q : Query _v)  : (e1332 _v) := by
  simp only [e5, e6, e12, e36, e1326, e1329, e1330, e1331, e1332] at *
  omega
theorem n13238 (_v : Vars) (_q : Query _v)  : (e5850 _v) := by
  have p13236 := n13236 _v _q 
  have p13237 := n13237 _v _q 
  exact (Iff.trans p13236 p13237)
theorem n13240 (_v : Vars) (_q : Query _v)  : (e13239 _v) := by
  have p13238 := n13238 _v _q 
  have p11742 := n11742 _v _q 
  change ((e668 _v) ↔ (e1331 _v)) at p13238
  change ((e666 _v) = (e1326 _v)) at p11742
  simp only [e13239, e5466, e1333, p13238, p11742]
theorem n13242 (_v : Vars) (_q : Query _v)  : (e13241 _v) := by
  have p13235 := n13235 _v _q 
  have p13240 := n13240 _v _q 
  change ((e667 _v) ↔ (e1832 _v)) at p13235
  change ((e5466 _v) = (e1333 _v)) at p13240
  simp only [e13241, e8808, e5851, p13235, p13240]
theorem n13243 (_v : Vars) (_q : Query _v)  : (e5858 _v) := by
  have p11744 := n11744 _v _q 
  change ((e669 _v) = (e1336 _v)) at p11744
  simp only [e5858, e670, e1839, p11744]
theorem n13244 (_v : Vars) (_q : Query _v)  : (e5859 _v) := by
  have p11744 := n11744 _v _q 
  change ((e669 _v) = (e1336 _v)) at p11744
  simp only [e5859, e671, e1339, p11744]
theorem n13245 (_v : Vars) (_q : Query _v)  : (e1342 _v) := by
  simp only [e12, e43, e760, e761, e1336, e1339, e1340, e1341, e1342] at *
  omega
theorem n13246 (_v : Vars) (_q : Query _v)  : (e5860 _v) := by
  have p13244 := n13244 _v _q 
  have p13245 := n13245 _v _q 
  exact (Iff.trans p13244 p13245)
end
end Assembly
