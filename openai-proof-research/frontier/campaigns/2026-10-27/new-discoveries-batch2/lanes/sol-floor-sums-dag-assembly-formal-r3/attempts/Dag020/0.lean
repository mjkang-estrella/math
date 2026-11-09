import Dag019
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n6036 (_v : Vars) (_q : Query _v)  : (e6035 _v) := by
  simp only [e5, e6, e36, e730, e1542, e6032, e6035] at *
  omega
theorem n6038 (_v : Vars) (_q : Query _v)  : (e6037 _v) := by
  simp only [e5, e6, e36, e730, e1542, e1543, e6037] at *
  omega
theorem n6041 (_v : Vars) (_q : Query _v)  : (e6040 _v) := by
  simp only [e43, e730, e760, e761, e1549, e1550, e6040] at *
  omega
theorem n6044 (_v : Vars) (_q : Query _v)  : (e6043 _v) := by
  simp only [e266, e730, e781, e782, e1556, e1557, e6043] at *
  omega
theorem n6047 (_v : Vars) (_q : Query _v)  : (e6046 _v) := by
  simp only [e108, e730, e802, e803, e1563, e1564, e6046] at *
  omega
theorem n6050 (_v : Vars) (_q : Query _v)  : (e6049 _v) := by
  have p1755 := n1755 _v _q 
  change ((e1167 _v) = (e1167 _v)) at p1755
  simp only [e6049, e1170, p1755]
theorem n6051 (_v : Vars) (_q : Query _v)  : (e1758 _v) := by
  have p1757 := n1757 _v _q 
  change ((e1172 _v) = (e1172 _v)) at p1757
  simp only [e1758, e1173, p1757]
theorem n6053 (_v : Vars) (_q : Query _v)  : (e6052 _v) := by
  have p6051 := n6051 _v _q 
  have p1755 := n1755 _v _q 
  change ((e1173 _v) ↔ (e1173 _v)) at p6051
  change ((e1167 _v) = (e1167 _v)) at p1755
  simp only [e6052, e1174, p6051, p1755]
theorem n6055 (_v : Vars) (_q : Query _v)  : (e6054 _v) := by
  have p6050 := n6050 _v _q 
  have p6053 := n6053 _v _q 
  change ((e1170 _v) ↔ (e1170 _v)) at p6050
  change ((e1174 _v) = (e1174 _v)) at p6053
  simp only [e6054, e5765, p6050, p6053]
theorem n6057 (_v : Vars) (_q : Query _v)  : (e6056 _v) := by
  have p6055 := n6055 _v _q 
  change ((e5765 _v) = (e5765 _v)) at p6055
  simp only [e6056, e5770, p6055]
theorem n6059 (_v : Vars) (_q : Query _v)  : (e6058 _v) := by
  have p1760 := n1760 _v _q 
  change ((e1177 _v) = (e1177 _v)) at p1760
  simp only [e6058, e1180, p1760]
theorem n6060 (_v : Vars) (_q : Query _v)  : (e1763 _v) := by
  have p1762 := n1762 _v _q 
  change ((e1182 _v) = (e1182 _v)) at p1762
  simp only [e1763, e1183, p1762]
theorem n6062 (_v : Vars) (_q : Query _v)  : (e6061 _v) := by
  have p6060 := n6060 _v _q 
  have p1760 := n1760 _v _q 
  change ((e1183 _v) ↔ (e1183 _v)) at p6060
  change ((e1177 _v) = (e1177 _v)) at p1760
  simp only [e6061, e1184, p6060, p1760]
theorem n6064 (_v : Vars) (_q : Query _v)  : (e6063 _v) := by
  have p6059 := n6059 _v _q 
  have p6062 := n6062 _v _q 
  change ((e1180 _v) ↔ (e1180 _v)) at p6059
  change ((e1184 _v) = (e1184 _v)) at p6062
  simp only [e6063, e5766, p6059, p6062]
theorem n6066 (_v : Vars) (_q : Query _v)  : (e6065 _v) := by
  have p6064 := n6064 _v _q 
  change ((e5766 _v) = (e5766 _v)) at p6064
  simp only [e6065, e5771, p6064]
theorem n6068 (_v : Vars) (_q : Query _v)  : (e6067 _v) := by
  have p1765 := n1765 _v _q 
  change ((e1187 _v) = (e1187 _v)) at p1765
  simp only [e6067, e1190, p1765]
theorem n6069 (_v : Vars) (_q : Query _v)  : (e1768 _v) := by
  have p1767 := n1767 _v _q 
  change ((e1192 _v) = (e1192 _v)) at p1767
  simp only [e1768, e1193, p1767]
theorem n6071 (_v : Vars) (_q : Query _v)  : (e6070 _v) := by
  have p6069 := n6069 _v _q 
  have p1765 := n1765 _v _q 
  change ((e1193 _v) ↔ (e1193 _v)) at p6069
  change ((e1187 _v) = (e1187 _v)) at p1765
  simp only [e6070, e1194, p6069, p1765]
theorem n6073 (_v : Vars) (_q : Query _v)  : (e6072 _v) := by
  have p6068 := n6068 _v _q 
  have p6071 := n6071 _v _q 
  change ((e1190 _v) ↔ (e1190 _v)) at p6068
  change ((e1194 _v) = (e1194 _v)) at p6071
  simp only [e6072, e5767, p6068, p6071]
theorem n6075 (_v : Vars) (_q : Query _v)  : (e6074 _v) := by
  have p6073 := n6073 _v _q 
  change ((e5767 _v) = (e5767 _v)) at p6073
  simp only [e6074, e5772, p6073]
theorem n6077 (_v : Vars) (_q : Query _v)  : (e6076 _v) := by
  have p1770 := n1770 _v _q 
  change ((e1197 _v) = (e1197 _v)) at p1770
  simp only [e6076, e1200, p1770]
theorem n6078 (_v : Vars) (_q : Query _v)  : (e1773 _v) := by
  have p1772 := n1772 _v _q 
  change ((e1202 _v) = (e1202 _v)) at p1772
  simp only [e1773, e1203, p1772]
theorem n6080 (_v : Vars) (_q : Query _v)  : (e6079 _v) := by
  have p6078 := n6078 _v _q 
  have p1770 := n1770 _v _q 
  change ((e1203 _v) ↔ (e1203 _v)) at p6078
  change ((e1197 _v) = (e1197 _v)) at p1770
  simp only [e6079, e1204, p6078, p1770]
theorem n6082 (_v : Vars) (_q : Query _v)  : (e6081 _v) := by
  have p6077 := n6077 _v _q 
  have p6080 := n6080 _v _q 
  change ((e1200 _v) ↔ (e1200 _v)) at p6077
  change ((e1204 _v) = (e1204 _v)) at p6080
  simp only [e6081, e5768, p6077, p6080]
theorem n6084 (_v : Vars) (_q : Query _v)  : (e6083 _v) := by
  have p6082 := n6082 _v _q 
  change ((e5768 _v) = (e5768 _v)) at p6082
  simp only [e6083, e5773, p6082]
theorem n6086 (_v : Vars) (_q : Query _v)  : (e6085 _v) := by
  have p1859 := n1859 _v _q 
  change ((e1370 _v) = (e1370 _v)) at p1859
  simp only [e6085, e1373, p1859]
theorem n6087 (_v : Vars) (_q : Query _v)  : (e1862 _v) := by
  have p1861 := n1861 _v _q 
  change ((e1375 _v) = (e1375 _v)) at p1861
  simp only [e1862, e1376, p1861]
theorem n6089 (_v : Vars) (_q : Query _v)  : (e6088 _v) := by
  have p6087 := n6087 _v _q 
  have p1859 := n1859 _v _q 
  change ((e1376 _v) ↔ (e1376 _v)) at p6087
  change ((e1370 _v) = (e1370 _v)) at p1859
  simp only [e6088, e1377, p6087, p1859]
theorem n6091 (_v : Vars) (_q : Query _v)  : (e6090 _v) := by
  have p6086 := n6086 _v _q 
  have p6089 := n6089 _v _q 
  change ((e1373 _v) ↔ (e1373 _v)) at p6086
  change ((e1377 _v) = (e1377 _v)) at p6089
  simp only [e6090, e5910, p6086, p6089]
theorem n6093 (_v : Vars) (_q : Query _v)  : (e6092 _v) := by
  have p6091 := n6091 _v _q 
  change ((e5910 _v) = (e5910 _v)) at p6091
  simp only [e6092, e5915, p6091]
theorem n6095 (_v : Vars) (_q : Query _v)  : (e6094 _v) := by
  have p1864 := n1864 _v _q 
  change ((e1380 _v) = (e1380 _v)) at p1864
  simp only [e6094, e1383, p1864]
theorem n6096 (_v : Vars) (_q : Query _v)  : (e1867 _v) := by
  have p1866 := n1866 _v _q 
  change ((e1385 _v) = (e1385 _v)) at p1866
  simp only [e1867, e1386, p1866]
theorem n6098 (_v : Vars) (_q : Query _v)  : (e6097 _v) := by
  have p6096 := n6096 _v _q 
  have p1864 := n1864 _v _q 
  change ((e1386 _v) ↔ (e1386 _v)) at p6096
  change ((e1380 _v) = (e1380 _v)) at p1864
  simp only [e6097, e1387, p6096, p1864]
theorem n6100 (_v : Vars) (_q : Query _v)  : (e6099 _v) := by
  have p6095 := n6095 _v _q 
  have p6098 := n6098 _v _q 
  change ((e1383 _v) ↔ (e1383 _v)) at p6095
  change ((e1387 _v) = (e1387 _v)) at p6098
  simp only [e6099, e5911, p6095, p6098]
theorem n6102 (_v : Vars) (_q : Query _v)  : (e6101 _v) := by
  have p6100 := n6100 _v _q 
  change ((e5911 _v) = (e5911 _v)) at p6100
  simp only [e6101, e5916, p6100]
theorem n6104 (_v : Vars) (_q : Query _v)  : (e6103 _v) := by
  have p1869 := n1869 _v _q 
  change ((e1390 _v) = (e1390 _v)) at p1869
  simp only [e6103, e1393, p1869]
theorem n6105 (_v : Vars) (_q : Query _v)  : (e1872 _v) := by
  have p1871 := n1871 _v _q 
  change ((e1395 _v) = (e1395 _v)) at p1871
  simp only [e1872, e1396, p1871]
theorem n6107 (_v : Vars) (_q : Query _v)  : (e6106 _v) := by
  have p6105 := n6105 _v _q 
  have p1869 := n1869 _v _q 
  change ((e1396 _v) ↔ (e1396 _v)) at p6105
  change ((e1390 _v) = (e1390 _v)) at p1869
  simp only [e6106, e1397, p6105, p1869]
theorem n6109 (_v : Vars) (_q : Query _v)  : (e6108 _v) := by
  have p6104 := n6104 _v _q 
  have p6107 := n6107 _v _q 
  change ((e1393 _v) ↔ (e1393 _v)) at p6104
  change ((e1397 _v) = (e1397 _v)) at p6107
  simp only [e6108, e5912, p6104, p6107]
theorem n6111 (_v : Vars) (_q : Query _v)  : (e6110 _v) := by
  have p6109 := n6109 _v _q 
  change ((e5912 _v) = (e5912 _v)) at p6109
  simp only [e6110, e5917, p6109]
theorem n6113 (_v : Vars) (_q : Query _v)  : (e6112 _v) := by
  have p1874 := n1874 _v _q 
  change ((e1400 _v) = (e1400 _v)) at p1874
  simp only [e6112, e1403, p1874]
theorem n6114 (_v : Vars) (_q : Query _v)  : (e1877 _v) := by
  have p1876 := n1876 _v _q 
  change ((e1405 _v) = (e1405 _v)) at p1876
  simp only [e1877, e1406, p1876]
theorem n6116 (_v : Vars) (_q : Query _v)  : (e6115 _v) := by
  have p6114 := n6114 _v _q 
  have p1874 := n1874 _v _q 
  change ((e1406 _v) ↔ (e1406 _v)) at p6114
  change ((e1400 _v) = (e1400 _v)) at p1874
  simp only [e6115, e1407, p6114, p1874]
theorem n6118 (_v : Vars) (_q : Query _v)  : (e6117 _v) := by
  have p6113 := n6113 _v _q 
  have p6116 := n6116 _v _q 
  change ((e1403 _v) ↔ (e1403 _v)) at p6113
  change ((e1407 _v) = (e1407 _v)) at p6116
  simp only [e6117, e5913, p6113, p6116]
theorem n6120 (_v : Vars) (_q : Query _v)  : (e6119 _v) := by
  have p6118 := n6118 _v _q 
  change ((e5913 _v) = (e5913 _v)) at p6118
  simp only [e6119, e5918, p6118]
end
end Assembly
