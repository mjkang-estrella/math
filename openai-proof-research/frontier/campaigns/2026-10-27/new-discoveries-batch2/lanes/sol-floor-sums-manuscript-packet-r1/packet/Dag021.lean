import Dag020
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n6122 (_v : Vars) (_q : Query _v)  : (e6121 _v) := by
  have p1907 := n1907 _v _q 
  change ((e1458 _v) = (e1458 _v)) at p1907
  simp only [e6121, e1461]
theorem n6123 (_v : Vars) (_q : Query _v)  : (e1910 _v) := by
  have p1909 := n1909 _v _q 
  change ((e1463 _v) = (e1463 _v)) at p1909
  simp only [e1910, e1464]
theorem n6125 (_v : Vars) (_q : Query _v)  : (e6124 _v) := by
  have p6123 := n6123 _v _q 
  have p1907 := n1907 _v _q 
  change ((e1464 _v) ↔ (e1464 _v)) at p6123
  change ((e1458 _v) = (e1458 _v)) at p1907
  simp only [e6124, e1465]
theorem n6127 (_v : Vars) (_q : Query _v)  : (e6126 _v) := by
  have p6122 := n6122 _v _q 
  have p6125 := n6125 _v _q 
  change ((e1461 _v) ↔ (e1461 _v)) at p6122
  change ((e1465 _v) = (e1465 _v)) at p6125
  simp only [e6126, e5984]
theorem n6129 (_v : Vars) (_q : Query _v)  : (e6128 _v) := by
  have p6127 := n6127 _v _q 
  change ((e5984 _v) = (e5984 _v)) at p6127
  simp only [e6128, e5989]
theorem n6131 (_v : Vars) (_q : Query _v)  : (e6130 _v) := by
  have p1912 := n1912 _v _q 
  change ((e1468 _v) = (e1468 _v)) at p1912
  simp only [e6130, e1471]
theorem n6132 (_v : Vars) (_q : Query _v)  : (e1915 _v) := by
  have p1914 := n1914 _v _q 
  change ((e1473 _v) = (e1473 _v)) at p1914
  simp only [e1915, e1474]
theorem n6134 (_v : Vars) (_q : Query _v)  : (e6133 _v) := by
  have p6132 := n6132 _v _q 
  have p1912 := n1912 _v _q 
  change ((e1474 _v) ↔ (e1474 _v)) at p6132
  change ((e1468 _v) = (e1468 _v)) at p1912
  simp only [e6133, e1475]
theorem n6136 (_v : Vars) (_q : Query _v)  : (e6135 _v) := by
  have p6131 := n6131 _v _q 
  have p6134 := n6134 _v _q 
  change ((e1471 _v) ↔ (e1471 _v)) at p6131
  change ((e1475 _v) = (e1475 _v)) at p6134
  simp only [e6135, e5985]
theorem n6138 (_v : Vars) (_q : Query _v)  : (e6137 _v) := by
  have p6136 := n6136 _v _q 
  change ((e5985 _v) = (e5985 _v)) at p6136
  simp only [e6137, e5990]
theorem n6140 (_v : Vars) (_q : Query _v)  : (e6139 _v) := by
  have p1917 := n1917 _v _q 
  change ((e1478 _v) = (e1478 _v)) at p1917
  simp only [e6139, e1481]
theorem n6141 (_v : Vars) (_q : Query _v)  : (e1920 _v) := by
  have p1919 := n1919 _v _q 
  change ((e1483 _v) = (e1483 _v)) at p1919
  simp only [e1920, e1484]
theorem n6143 (_v : Vars) (_q : Query _v)  : (e6142 _v) := by
  have p6141 := n6141 _v _q 
  have p1917 := n1917 _v _q 
  change ((e1484 _v) ↔ (e1484 _v)) at p6141
  change ((e1478 _v) = (e1478 _v)) at p1917
  simp only [e6142, e1485]
theorem n6145 (_v : Vars) (_q : Query _v)  : (e6144 _v) := by
  have p6140 := n6140 _v _q 
  have p6143 := n6143 _v _q 
  change ((e1481 _v) ↔ (e1481 _v)) at p6140
  change ((e1485 _v) = (e1485 _v)) at p6143
  simp only [e6144, e5986]
theorem n6147 (_v : Vars) (_q : Query _v)  : (e6146 _v) := by
  have p6145 := n6145 _v _q 
  change ((e5986 _v) = (e5986 _v)) at p6145
  simp only [e6146, e5991]
theorem n6149 (_v : Vars) (_q : Query _v)  : (e6148 _v) := by
  have p1922 := n1922 _v _q 
  change ((e1488 _v) = (e1488 _v)) at p1922
  simp only [e6148, e1491]
theorem n6150 (_v : Vars) (_q : Query _v)  : (e1925 _v) := by
  have p1924 := n1924 _v _q 
  change ((e1493 _v) = (e1493 _v)) at p1924
  simp only [e1925, e1494]
theorem n6152 (_v : Vars) (_q : Query _v)  : (e6151 _v) := by
  have p6150 := n6150 _v _q 
  have p1922 := n1922 _v _q 
  change ((e1494 _v) ↔ (e1494 _v)) at p6150
  change ((e1488 _v) = (e1488 _v)) at p1922
  simp only [e6151, e1495]
theorem n6154 (_v : Vars) (_q : Query _v)  : (e6153 _v) := by
  have p6149 := n6149 _v _q 
  have p6152 := n6152 _v _q 
  change ((e1491 _v) ↔ (e1491 _v)) at p6149
  change ((e1495 _v) = (e1495 _v)) at p6152
  simp only [e6153, e5987]
theorem n6156 (_v : Vars) (_q : Query _v)  : (e6155 _v) := by
  have p6154 := n6154 _v _q 
  change ((e5987 _v) = (e5987 _v)) at p6154
  simp only [e6155, e5992]
theorem n6158 (_v : Vars) (_q : Query _v)  : (e6157 _v) := by
  have p1927 := n1927 _v _q 
  change ((e1502 _v) = (e1502 _v)) at p1927
  simp only [e6157, e1505]
theorem n6159 (_v : Vars) (_q : Query _v)  : (e1930 _v) := by
  have p1929 := n1929 _v _q 
  change ((e1507 _v) = (e1507 _v)) at p1929
  simp only [e1930, e1508]
theorem n6161 (_v : Vars) (_q : Query _v)  : (e6160 _v) := by
  have p6159 := n6159 _v _q 
  have p1927 := n1927 _v _q 
  change ((e1508 _v) ↔ (e1508 _v)) at p6159
  change ((e1502 _v) = (e1502 _v)) at p1927
  simp only [e6160, e1509]
theorem n6163 (_v : Vars) (_q : Query _v)  : (e6162 _v) := by
  have p6158 := n6158 _v _q 
  have p6161 := n6161 _v _q 
  change ((e1505 _v) ↔ (e1505 _v)) at p6158
  change ((e1509 _v) = (e1509 _v)) at p6161
  simp only [e6162, e6022]
theorem n6165 (_v : Vars) (_q : Query _v)  : (e6164 _v) := by
  have p6163 := n6163 _v _q 
  change ((e6022 _v) = (e6022 _v)) at p6163
  simp only [e6164, e6027]
theorem n6167 (_v : Vars) (_q : Query _v)  : (e6166 _v) := by
  have p1932 := n1932 _v _q 
  change ((e1512 _v) = (e1512 _v)) at p1932
  simp only [e6166, e1515]
theorem n6168 (_v : Vars) (_q : Query _v)  : (e1935 _v) := by
  have p1934 := n1934 _v _q 
  change ((e1517 _v) = (e1517 _v)) at p1934
  simp only [e1935, e1518]
theorem n6170 (_v : Vars) (_q : Query _v)  : (e6169 _v) := by
  have p6168 := n6168 _v _q 
  have p1932 := n1932 _v _q 
  change ((e1518 _v) ↔ (e1518 _v)) at p6168
  change ((e1512 _v) = (e1512 _v)) at p1932
  simp only [e6169, e1519]
theorem n6172 (_v : Vars) (_q : Query _v)  : (e6171 _v) := by
  have p6167 := n6167 _v _q 
  have p6170 := n6170 _v _q 
  change ((e1515 _v) ↔ (e1515 _v)) at p6167
  change ((e1519 _v) = (e1519 _v)) at p6170
  simp only [e6171, e6023]
theorem n6174 (_v : Vars) (_q : Query _v)  : (e6173 _v) := by
  have p6172 := n6172 _v _q 
  change ((e6023 _v) = (e6023 _v)) at p6172
  simp only [e6173, e6028]
theorem n6176 (_v : Vars) (_q : Query _v)  : (e6175 _v) := by
  have p1937 := n1937 _v _q 
  change ((e1522 _v) = (e1522 _v)) at p1937
  simp only [e6175, e1525]
theorem n6177 (_v : Vars) (_q : Query _v)  : (e1940 _v) := by
  have p1939 := n1939 _v _q 
  change ((e1527 _v) = (e1527 _v)) at p1939
  simp only [e1940, e1528]
theorem n6179 (_v : Vars) (_q : Query _v)  : (e6178 _v) := by
  have p6177 := n6177 _v _q 
  have p1937 := n1937 _v _q 
  change ((e1528 _v) ↔ (e1528 _v)) at p6177
  change ((e1522 _v) = (e1522 _v)) at p1937
  simp only [e6178, e1529]
theorem n6181 (_v : Vars) (_q : Query _v)  : (e6180 _v) := by
  have p6176 := n6176 _v _q 
  have p6179 := n6179 _v _q 
  change ((e1525 _v) ↔ (e1525 _v)) at p6176
  change ((e1529 _v) = (e1529 _v)) at p6179
  simp only [e6180, e6024]
theorem n6183 (_v : Vars) (_q : Query _v)  : (e6182 _v) := by
  have p6181 := n6181 _v _q 
  change ((e6024 _v) = (e6024 _v)) at p6181
  simp only [e6182, e6029]
theorem n6185 (_v : Vars) (_q : Query _v)  : (e6184 _v) := by
  have p1942 := n1942 _v _q 
  change ((e1532 _v) = (e1532 _v)) at p1942
  simp only [e6184, e1535]
theorem n6186 (_v : Vars) (_q : Query _v)  : (e1945 _v) := by
  have p1944 := n1944 _v _q 
  change ((e1537 _v) = (e1537 _v)) at p1944
  simp only [e1945, e1538]
theorem n6188 (_v : Vars) (_q : Query _v)  : (e6187 _v) := by
  have p6186 := n6186 _v _q 
  have p1942 := n1942 _v _q 
  change ((e1538 _v) ↔ (e1538 _v)) at p6186
  change ((e1532 _v) = (e1532 _v)) at p1942
  simp only [e6187, e1539]
theorem n6190 (_v : Vars) (_q : Query _v)  : (e6189 _v) := by
  have p6185 := n6185 _v _q 
  have p6188 := n6188 _v _q 
  change ((e1535 _v) ↔ (e1535 _v)) at p6185
  change ((e1539 _v) = (e1539 _v)) at p6188
  simp only [e6189, e6025]
theorem n6192 (_v : Vars) (_q : Query _v)  : (e6191 _v) := by
  have p6190 := n6190 _v _q 
  change ((e6025 _v) = (e6025 _v)) at p6190
  simp only [e6191, e6030]
theorem n6407 (_v : Vars) (_q : Query _v)  : (e6406 _v) := by
  simp only [e151, e2812, e2816, e2817, e2818, e2819, e3032, e6405, e6406] at *
  by_cases hc : ((e150 _v) ≥ (e12 _v)) <;> simp [hc]
theorem n6419 (_v : Vars) (_q : Query _v)  : (e6418 _v) := by
  simp only [e1985, e2826, e2830, e2831, e2832, e2833, e3393, e6417, e6418] at *
  by_cases hc : ((e1984 _v) ≥ (e12 _v)) <;> simp [hc]
theorem n6422 (_v : Vars) (_q : Query _v)  : (e6421 _v) := by
  simp only [e163, e165, e2834, e2835, e2836, e4238, e6420, e6421] at *
  by_cases hc : ((e162 _v) ≤ (e12 _v)) <;> simp [hc]
theorem n6430 (_v : Vars) (_q : Query _v)  : (e6429 _v) := by
  simp only [e2017, e2837, e2838, e2839, e2840, e6427, e6428, e6429] at *
  by_cases hc : ((e2016 _v) ≤ (e12 _v)) <;> simp [hc]
theorem n6438 (_v : Vars) (_q : Query _v)  : (e6437 _v) := by
  simp only [e2034, e2841, e2842, e2843, e2844, e6435, e6436, e6437] at *
  by_cases hc : ((e2033 _v) ≤ (e12 _v)) <;> simp [hc]
end
end Assembly
