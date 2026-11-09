import Dag089
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n13248 (_v : Vars) (_q : Query _v)  : (e13247 _v) := by
  have p13246 := n13246 _v _q 
  have p11744 := n11744 _v _q 
  change ((e671 _v) ↔ (e1341 _v)) at p13246
  change ((e669 _v) = (e1336 _v)) at p11744
  simp only [e13247, e5467, e1343, p13246, p11744]
theorem n13250 (_v : Vars) (_q : Query _v)  : (e13249 _v) := by
  have p13243 := n13243 _v _q 
  have p13248 := n13248 _v _q 
  change ((e670 _v) ↔ (e1839 _v)) at p13243
  change ((e5467 _v) = (e1343 _v)) at p13248
  simp only [e13249, e8809, e5861, p13243, p13248]
theorem n13251 (_v : Vars) (_q : Query _v)  : (e5868 _v) := by
  have p11746 := n11746 _v _q 
  change ((e672 _v) = (e1346 _v)) at p11746
  simp only [e5868, e673, e1846, p11746]
theorem n13252 (_v : Vars) (_q : Query _v)  : (e5869 _v) := by
  have p11746 := n11746 _v _q 
  change ((e672 _v) = (e1346 _v)) at p11746
  simp only [e5869, e674, e1349, p11746]
theorem n13253 (_v : Vars) (_q : Query _v)  : (e1352 _v) := by
  simp only [e12, e266, e781, e782, e1346, e1349, e1350, e1351, e1352] at *
  omega
theorem n13254 (_v : Vars) (_q : Query _v)  : (e5870 _v) := by
  have p13252 := n13252 _v _q 
  have p13253 := n13253 _v _q 
  exact (Iff.trans p13252 p13253)
theorem n13256 (_v : Vars) (_q : Query _v)  : (e13255 _v) := by
  have p13254 := n13254 _v _q 
  have p11746 := n11746 _v _q 
  change ((e674 _v) ↔ (e1351 _v)) at p13254
  change ((e672 _v) = (e1346 _v)) at p11746
  simp only [e13255, e5468, e1353, p13254, p11746]
theorem n13258 (_v : Vars) (_q : Query _v)  : (e13257 _v) := by
  have p13251 := n13251 _v _q 
  have p13256 := n13256 _v _q 
  change ((e673 _v) ↔ (e1846 _v)) at p13251
  change ((e5468 _v) = (e1353 _v)) at p13256
  simp only [e13257, e8810, e5871, p13251, p13256]
theorem n13259 (_v : Vars) (_q : Query _v)  : (e5878 _v) := by
  have p11748 := n11748 _v _q 
  change ((e675 _v) = (e1356 _v)) at p11748
  simp only [e5878, e676, e1853, p11748]
theorem n13260 (_v : Vars) (_q : Query _v)  : (e5879 _v) := by
  have p11748 := n11748 _v _q 
  change ((e675 _v) = (e1356 _v)) at p11748
  simp only [e5879, e677, e1359, p11748]
theorem n13261 (_v : Vars) (_q : Query _v)  : (e1362 _v) := by
  simp only [e12, e108, e802, e803, e1356, e1359, e1360, e1361, e1362] at *
  omega
theorem n13262 (_v : Vars) (_q : Query _v)  : (e5880 _v) := by
  have p13260 := n13260 _v _q 
  have p13261 := n13261 _v _q 
  exact (Iff.trans p13260 p13261)
theorem n13264 (_v : Vars) (_q : Query _v)  : (e13263 _v) := by
  have p13262 := n13262 _v _q 
  have p11748 := n11748 _v _q 
  change ((e677 _v) ↔ (e1361 _v)) at p13262
  change ((e675 _v) = (e1356 _v)) at p11748
  simp only [e13263, e5469, e1363, p13262, p11748]
theorem n13266 (_v : Vars) (_q : Query _v)  : (e13265 _v) := by
  have p13259 := n13259 _v _q 
  have p13264 := n13264 _v _q 
  change ((e676 _v) ↔ (e1853 _v)) at p13259
  change ((e5469 _v) = (e1363 _v)) at p13264
  simp only [e13265, e8811, e5881, p13259, p13264]
theorem n13268 (_v : Vars) (_q : Query _v)  : (e13267 _v) := by
  have p11750 := n11750 _v _q 
  change ((e679 _v) = (e1370 _v)) at p11750
  simp only [e13267, e681, e1374, p11750]
theorem n13269 (_v : Vars) (_q : Query _v)  : (e5884 _v) := by
  simp only [e5, e6, e12, e36, e1370, e1374, e1375, e1376, e5884] at *
  omega
theorem n13270 (_v : Vars) (_q : Query _v)  : (e5885 _v) := by
  have p13268 := n13268 _v _q 
  have p13269 := n13269 _v _q 
  exact (Iff.trans p13268 p13269)
theorem n13272 (_v : Vars) (_q : Query _v)  : (e13271 _v) := by
  have p13270 := n13270 _v _q 
  have p11750 := n11750 _v _q 
  change ((e681 _v) ↔ (e1376 _v)) at p13270
  change ((e679 _v) = (e1370 _v)) at p11750
  simp only [e13271, e5470, e1377, p13270, p11750]
theorem n13274 (_v : Vars) (_q : Query _v)  : (e13273 _v) := by
  have p11752 := n11752 _v _q 
  change ((e682 _v) = (e1380 _v)) at p11752
  simp only [e13273, e684, e1384, p11752]
theorem n13275 (_v : Vars) (_q : Query _v)  : (e5892 _v) := by
  simp only [e12, e43, e760, e761, e1380, e1384, e1385, e1386, e5892] at *
  omega
theorem n13276 (_v : Vars) (_q : Query _v)  : (e5893 _v) := by
  have p13274 := n13274 _v _q 
  have p13275 := n13275 _v _q 
  exact (Iff.trans p13274 p13275)
theorem n13278 (_v : Vars) (_q : Query _v)  : (e13277 _v) := by
  have p13276 := n13276 _v _q 
  have p11752 := n11752 _v _q 
  change ((e684 _v) ↔ (e1386 _v)) at p13276
  change ((e682 _v) = (e1380 _v)) at p11752
  simp only [e13277, e5471, e1387, p13276, p11752]
theorem n13280 (_v : Vars) (_q : Query _v)  : (e13279 _v) := by
  have p11754 := n11754 _v _q 
  change ((e685 _v) = (e1390 _v)) at p11754
  simp only [e13279, e687, e1394, p11754]
theorem n13281 (_v : Vars) (_q : Query _v)  : (e5900 _v) := by
  simp only [e12, e266, e781, e782, e1390, e1394, e1395, e1396, e5900] at *
  omega
theorem n13282 (_v : Vars) (_q : Query _v)  : (e5901 _v) := by
  have p13280 := n13280 _v _q 
  have p13281 := n13281 _v _q 
  exact (Iff.trans p13280 p13281)
theorem n13284 (_v : Vars) (_q : Query _v)  : (e13283 _v) := by
  have p13282 := n13282 _v _q 
  have p11754 := n11754 _v _q 
  change ((e687 _v) ↔ (e1396 _v)) at p13282
  change ((e685 _v) = (e1390 _v)) at p11754
  simp only [e13283, e5472, e1397, p13282, p11754]
theorem n13286 (_v : Vars) (_q : Query _v)  : (e13285 _v) := by
  have p11756 := n11756 _v _q 
  change ((e688 _v) = (e1400 _v)) at p11756
  simp only [e13285, e690, e1404, p11756]
theorem n13287 (_v : Vars) (_q : Query _v)  : (e5908 _v) := by
  simp only [e12, e108, e802, e803, e1400, e1404, e1405, e1406, e5908] at *
  omega
theorem n13288 (_v : Vars) (_q : Query _v)  : (e5909 _v) := by
  have p13286 := n13286 _v _q 
  have p13287 := n13287 _v _q 
  exact (Iff.trans p13286 p13287)
theorem n13290 (_v : Vars) (_q : Query _v)  : (e13289 _v) := by
  have p13288 := n13288 _v _q 
  have p11756 := n11756 _v _q 
  change ((e690 _v) ↔ (e1406 _v)) at p13288
  change ((e688 _v) = (e1400 _v)) at p11756
  simp only [e13289, e5473, e1407, p13288, p11756]
theorem n13291 (_v : Vars) (_q : Query _v)  : (e5922 _v) := by
  have p11758 := n11758 _v _q 
  change ((e692 _v) = (e1414 _v)) at p11758
  simp only [e5922, e693, e1880, p11758]
theorem n13292 (_v : Vars) (_q : Query _v)  : (e5923 _v) := by
  have p11758 := n11758 _v _q 
  change ((e692 _v) = (e1414 _v)) at p11758
  simp only [e5923, e694, e1417, p11758]
theorem n13293 (_v : Vars) (_q : Query _v)  : (e1420 _v) := by
  simp only [e5, e6, e12, e36, e1414, e1417, e1418, e1419, e1420] at *
  omega
theorem n13294 (_v : Vars) (_q : Query _v)  : (e5924 _v) := by
  have p13292 := n13292 _v _q 
  have p13293 := n13293 _v _q 
  exact (Iff.trans p13292 p13293)
theorem n13296 (_v : Vars) (_q : Query _v)  : (e13295 _v) := by
  have p13294 := n13294 _v _q 
  have p11758 := n11758 _v _q 
  change ((e694 _v) ↔ (e1419 _v)) at p13294
  change ((e692 _v) = (e1414 _v)) at p11758
  simp only [e13295, e5474, e1421, p13294, p11758]
theorem n13298 (_v : Vars) (_q : Query _v)  : (e13297 _v) := by
  have p13291 := n13291 _v _q 
  have p13296 := n13296 _v _q 
  change ((e693 _v) ↔ (e1880 _v)) at p13291
  change ((e5474 _v) = (e1421 _v)) at p13296
  simp only [e13297, e8818, e5925, p13291, p13296]
theorem n13299 (_v : Vars) (_q : Query _v)  : (e5932 _v) := by
  have p11760 := n11760 _v _q 
  change ((e695 _v) = (e1424 _v)) at p11760
  simp only [e5932, e696, e1887, p11760]
theorem n13300 (_v : Vars) (_q : Query _v)  : (e5933 _v) := by
  have p11760 := n11760 _v _q 
  change ((e695 _v) = (e1424 _v)) at p11760
  simp only [e5933, e697, e1427, p11760]
theorem n13301 (_v : Vars) (_q : Query _v)  : (e1430 _v) := by
  simp only [e12, e43, e760, e761, e1424, e1427, e1428, e1429, e1430] at *
  omega
theorem n13302 (_v : Vars) (_q : Query _v)  : (e5934 _v) := by
  have p13300 := n13300 _v _q 
  have p13301 := n13301 _v _q 
  exact (Iff.trans p13300 p13301)
theorem n13304 (_v : Vars) (_q : Query _v)  : (e13303 _v) := by
  have p13302 := n13302 _v _q 
  have p11760 := n11760 _v _q 
  change ((e697 _v) ↔ (e1429 _v)) at p13302
  change ((e695 _v) = (e1424 _v)) at p11760
  simp only [e13303, e5475, e1431, p13302, p11760]
theorem n13306 (_v : Vars) (_q : Query _v)  : (e13305 _v) := by
  have p13299 := n13299 _v _q 
  have p13304 := n13304 _v _q 
  change ((e696 _v) ↔ (e1887 _v)) at p13299
  change ((e5475 _v) = (e1431 _v)) at p13304
  simp only [e13305, e8819, e5935, p13299, p13304]
theorem n13307 (_v : Vars) (_q : Query _v)  : (e5942 _v) := by
  have p11762 := n11762 _v _q 
  change ((e698 _v) = (e1434 _v)) at p11762
  simp only [e5942, e699, e1894, p11762]
theorem n13308 (_v : Vars) (_q : Query _v)  : (e5943 _v) := by
  have p11762 := n11762 _v _q 
  change ((e698 _v) = (e1434 _v)) at p11762
  simp only [e5943, e700, e1437, p11762]
theorem n13309 (_v : Vars) (_q : Query _v)  : (e1440 _v) := by
  simp only [e12, e266, e781, e782, e1434, e1437, e1438, e1439, e1440] at *
  omega
end
end Assembly
