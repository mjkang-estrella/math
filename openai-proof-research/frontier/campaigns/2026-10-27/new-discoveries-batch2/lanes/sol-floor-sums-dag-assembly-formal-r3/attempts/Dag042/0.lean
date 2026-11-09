import Dag041
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n9281 (_v : Vars) (_q : Query _v)  : (e1798 _v) := by
  have p1796 := n1796 _v _q 
  change ((e1266 _v) = (e1266 _v)) at p1796
  simp only [e1798, e1797, p1796]
theorem n9282 (_v : Vars) (_q : Query _v)  : (e1801 _v) := by
  have p1800 := n1800 _v _q 
  change ((e1272 _v) = (e1272 _v)) at p1800
  simp only [e1801, e1273, p1800]
theorem n9284 (_v : Vars) (_q : Query _v)  : (e9283 _v) := by
  have p9282 := n9282 _v _q 
  have p1796 := n1796 _v _q 
  change ((e1273 _v) ↔ (e1273 _v)) at p9282
  change ((e1266 _v) = (e1266 _v)) at p1796
  simp only [e9283, e1275, p9282, p1796]
theorem n9286 (_v : Vars) (_q : Query _v)  : (e9285 _v) := by
  have p9281 := n9281 _v _q 
  have p9284 := n9284 _v _q 
  change ((e1797 _v) ↔ (e1797 _v)) at p9281
  change ((e1275 _v) = (e1275 _v)) at p9284
  simp only [e9285, e5809, p9281, p9284]
theorem n9288 (_v : Vars) (_q : Query _v)  : (e9287 _v) := by
  have p9286 := n9286 _v _q 
  change ((e5809 _v) = (e5809 _v)) at p9286
  simp only [e9287, e9059, p9286]
theorem n9290 (_v : Vars) (_q : Query _v)  : (e9289 _v) := by
  have p1947 := n1947 _v _q 
  change ((e1543 _v) = (e1543 _v)) at p1947
  simp only [e9289, e1544, p1947]
theorem n9292 (_v : Vars) (_q : Query _v)  : (e9291 _v) := by
  have p1949 := n1949 _v _q 
  change ((e1546 _v) = (e1546 _v)) at p1949
  simp only [e9291, e1547, p1949]
theorem n9294 (_v : Vars) (_q : Query _v)  : (e9293 _v) := by
  have p9292 := n9292 _v _q 
  have p1947 := n1947 _v _q 
  change ((e1547 _v) ↔ (e1547 _v)) at p9292
  change ((e1543 _v) = (e1543 _v)) at p1947
  simp only [e9293, e6039, p9292, p1947]
theorem n9296 (_v : Vars) (_q : Query _v)  : (e9295 _v) := by
  have p9290 := n9290 _v _q 
  have p9294 := n9294 _v _q 
  change ((e1544 _v) ↔ (e1544 _v)) at p9290
  change ((e6039 _v) = (e6039 _v)) at p9294
  simp only [e9295, e9155, p9290, p9294]
theorem n9298 (_v : Vars) (_q : Query _v)  : (e9297 _v) := by
  have p1951 := n1951 _v _q 
  change ((e1550 _v) = (e1550 _v)) at p1951
  simp only [e9297, e1551, p1951]
theorem n9300 (_v : Vars) (_q : Query _v)  : (e9299 _v) := by
  have p1953 := n1953 _v _q 
  change ((e1553 _v) = (e1553 _v)) at p1953
  simp only [e9299, e1554, p1953]
theorem n9302 (_v : Vars) (_q : Query _v)  : (e9301 _v) := by
  have p9300 := n9300 _v _q 
  have p1951 := n1951 _v _q 
  change ((e1554 _v) ↔ (e1554 _v)) at p9300
  change ((e1550 _v) = (e1550 _v)) at p1951
  simp only [e9301, e6042, p9300, p1951]
theorem n9304 (_v : Vars) (_q : Query _v)  : (e9303 _v) := by
  have p9298 := n9298 _v _q 
  have p9302 := n9302 _v _q 
  change ((e1551 _v) ↔ (e1551 _v)) at p9298
  change ((e6042 _v) = (e6042 _v)) at p9302
  simp only [e9303, e9156, p9298, p9302]
theorem n9306 (_v : Vars) (_q : Query _v)  : (e9305 _v) := by
  have p1955 := n1955 _v _q 
  change ((e1557 _v) = (e1557 _v)) at p1955
  simp only [e9305, e1558, p1955]
theorem n9308 (_v : Vars) (_q : Query _v)  : (e9307 _v) := by
  have p1957 := n1957 _v _q 
  change ((e1560 _v) = (e1560 _v)) at p1957
  simp only [e9307, e1561, p1957]
theorem n9310 (_v : Vars) (_q : Query _v)  : (e9309 _v) := by
  have p9308 := n9308 _v _q 
  have p1955 := n1955 _v _q 
  change ((e1561 _v) ↔ (e1561 _v)) at p9308
  change ((e1557 _v) = (e1557 _v)) at p1955
  simp only [e9309, e6045, p9308, p1955]
theorem n9312 (_v : Vars) (_q : Query _v)  : (e9311 _v) := by
  have p9306 := n9306 _v _q 
  have p9310 := n9310 _v _q 
  change ((e1558 _v) ↔ (e1558 _v)) at p9306
  change ((e6045 _v) = (e6045 _v)) at p9310
  simp only [e9311, e9157, p9306, p9310]
theorem n9314 (_v : Vars) (_q : Query _v)  : (e9313 _v) := by
  have p1959 := n1959 _v _q 
  change ((e1564 _v) = (e1564 _v)) at p1959
  simp only [e9313, e1565, p1959]
theorem n9316 (_v : Vars) (_q : Query _v)  : (e9315 _v) := by
  have p1961 := n1961 _v _q 
  change ((e1567 _v) = (e1567 _v)) at p1961
  simp only [e9315, e1568, p1961]
theorem n9318 (_v : Vars) (_q : Query _v)  : (e9317 _v) := by
  have p9316 := n9316 _v _q 
  have p1959 := n1959 _v _q 
  change ((e1568 _v) ↔ (e1568 _v)) at p9316
  change ((e1564 _v) = (e1564 _v)) at p1959
  simp only [e9317, e6048, p9316, p1959]
theorem n9320 (_v : Vars) (_q : Query _v)  : (e9319 _v) := by
  have p9314 := n9314 _v _q 
  have p9318 := n9318 _v _q 
  change ((e1565 _v) ↔ (e1565 _v)) at p9314
  change ((e6048 _v) = (e6048 _v)) at p9318
  simp only [e9319, e9158, p9314, p9318]
theorem n9322 (_v : Vars) (_q : Query _v)  : (e1993 _v) := by
  have p1991 := n1991 _v _q 
  change ((e827 _v) = (e1989 _v)) at p1991
  simp only [e1993, e1588, e1992, p1991]
theorem n9323 (_v : Vars) (_q : Query _v)  : (e6197 _v) := by
  simp only [e5, e6, e8, e12, e36, e41, e1989, e1992, e1994, e1995, e6197] at *
  omega
theorem n9324 (_v : Vars) (_q : Query _v)  : (e6198 _v) := by
  have p9322 := n9322 _v _q 
  have p9323 := n9323 _v _q 
  exact (Iff.trans p9322 p9323)
theorem n9325 (_v : Vars) (_q : Query _v)  : (e2000 _v) := by
  have p1998 := n1998 _v _q 
  change ((e832 _v) = (e1996 _v)) at p1998
  simp only [e2000, e833, e1999, p1998]
theorem n9326 (_v : Vars) (_q : Query _v)  : (e2001 _v) := by
  simp only [e5, e6, e8, e12, e36, e162, e163, e1996, e1999, e2001] at *
  omega
theorem n9327 (_v : Vars) (_q : Query _v)  : (e2002 _v) := by
  have p9325 := n9325 _v _q 
  have p9326 := n9326 _v _q 
  exact (Iff.trans p9325 p9326)
theorem n9329 (_v : Vars) (_q : Query _v)  : (e9328 _v) := by
  have p9327 := n9327 _v _q 
  have p1991 := n1991 _v _q 
  change ((e833 _v) ↔ (e163 _v)) at p9327
  change ((e827 _v) = (e1989 _v)) at p1991
  simp only [e9328, e835, e2003, p9327, p1991]
theorem n9332 (_v : Vars) (_q : Query _v)  : (e9331 _v) := by
  have p9324 := n9324 _v _q 
  have p9329 := n9329 _v _q 
  change ((e1588 _v) ↔ (e1995 _v)) at p9324
  change ((e835 _v) = (e2003 _v)) at p9329
  simp only [e9331, e5528, e9330, p9324, p9329]
theorem n9333 (_v : Vars) (_q : Query _v)  : (e2008 _v) := by
  have p2006 := n2006 _v _q 
  change ((e843 _v) = (e2004 _v)) at p2006
  simp only [e2008, e1595, e2007, p2006]
theorem n9334 (_v : Vars) (_q : Query _v)  : (e6199 _v) := by
  simp only [e5, e6, e8, e12, e41, e43, e44, e760, e761, e2004, e2007, e2009, e2010, e6199] at *
  omega
theorem n9335 (_v : Vars) (_q : Query _v)  : (e6200 _v) := by
  have p9333 := n9333 _v _q 
  have p9334 := n9334 _v _q 
  exact (Iff.trans p9333 p9334)
theorem n9336 (_v : Vars) (_q : Query _v)  : (e2015 _v) := by
  have p2013 := n2013 _v _q 
  change ((e849 _v) = (e2011 _v)) at p2013
  simp only [e2015, e850, e2014, p2013]
theorem n9337 (_v : Vars) (_q : Query _v)  : (e2018 _v) := by
  simp only [e5, e6, e8, e12, e43, e44, e760, e761, e2011, e2014, e2016, e2017, e2018] at *
  omega
theorem n9338 (_v : Vars) (_q : Query _v)  : (e2019 _v) := by
  have p9336 := n9336 _v _q 
  have p9337 := n9337 _v _q 
  exact (Iff.trans p9336 p9337)
theorem n9340 (_v : Vars) (_q : Query _v)  : (e9339 _v) := by
  have p9338 := n9338 _v _q 
  have p2006 := n2006 _v _q 
  change ((e850 _v) ↔ (e2017 _v)) at p9338
  change ((e843 _v) = (e2004 _v)) at p2006
  simp only [e9339, e852, e2020, p9338, p2006]
theorem n9343 (_v : Vars) (_q : Query _v)  : (e9342 _v) := by
  have p9335 := n9335 _v _q 
  have p9340 := n9340 _v _q 
  change ((e1595 _v) ↔ (e2010 _v)) at p9335
  change ((e852 _v) = (e2020 _v)) at p9340
  simp only [e9342, e5538, e9341, p9335, p9340]
theorem n9344 (_v : Vars) (_q : Query _v)  : (e2025 _v) := by
  have p2023 := n2023 _v _q 
  change ((e860 _v) = (e2021 _v)) at p2023
  simp only [e2025, e1602, e2024, p2023]
theorem n9345 (_v : Vars) (_q : Query _v)  : (e6201 _v) := by
  simp only [e5, e6, e8, e12, e41, e266, e267, e781, e782, e2021, e2024, e2026, e2027, e6201] at *
  omega
theorem n9346 (_v : Vars) (_q : Query _v)  : (e6202 _v) := by
  have p9344 := n9344 _v _q 
  have p9345 := n9345 _v _q 
  exact (Iff.trans p9344 p9345)
theorem n9347 (_v : Vars) (_q : Query _v)  : (e2032 _v) := by
  have p2030 := n2030 _v _q 
  change ((e866 _v) = (e2028 _v)) at p2030
  simp only [e2032, e867, e2031, p2030]
theorem n9348 (_v : Vars) (_q : Query _v)  : (e2035 _v) := by
  simp only [e5, e6, e8, e12, e266, e267, e781, e782, e2028, e2031, e2033, e2034, e2035] at *
  omega
theorem n9349 (_v : Vars) (_q : Query _v)  : (e2036 _v) := by
  have p9347 := n9347 _v _q 
  have p9348 := n9348 _v _q 
  exact (Iff.trans p9347 p9348)
theorem n9351 (_v : Vars) (_q : Query _v)  : (e9350 _v) := by
  have p9349 := n9349 _v _q 
  have p2023 := n2023 _v _q 
  change ((e867 _v) ↔ (e2034 _v)) at p9349
  change ((e860 _v) = (e2021 _v)) at p2023
  simp only [e9350, e869, e2037, p9349, p2023]
theorem n9354 (_v : Vars) (_q : Query _v)  : (e9353 _v) := by
  have p9346 := n9346 _v _q 
  have p9351 := n9351 _v _q 
  change ((e1602 _v) ↔ (e2027 _v)) at p9346
  change ((e869 _v) = (e2037 _v)) at p9351
  simp only [e9353, e5548, e9352, p9346, p9351]
end
end Assembly
