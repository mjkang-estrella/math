import Dag045
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n9541 (_v : Vars) (_q : Query _v)  : (e9540 _v) := by
  have p9533 := n9533 _v _q 
  have p9538 := n9538 _v _q 
  change ((e1721 _v) ↔ (e2282 _v)) at p9533
  change ((e1116 _v) = (e6260 _v)) at p9538
  simp only [e9540, e5700, e9539, p9533, p9538]
theorem n9542 (_v : Vars) (_q : Query _v)  : (e2294 _v) := by
  have p2292 := n2292 _v _q 
  change ((e1123 _v) = (e2290 _v)) at p2292
  simp only [e2294, e1728, e2293, p2292]
theorem n9543 (_v : Vars) (_q : Query _v)  : (e6261 _v) := by
  simp only [e5, e6, e10, e12, e36, e41, e111, e2290, e2293, e2295, e2296, e6261] at *
  omega
theorem n9544 (_v : Vars) (_q : Query _v)  : (e6262 _v) := by
  have p9542 := n9542 _v _q 
  have p9543 := n9543 _v _q 
  exact (Iff.trans p9542 p9543)
theorem n9545 (_v : Vars) (_q : Query _v)  : (e2301 _v) := by
  have p2299 := n2299 _v _q 
  change ((e1127 _v) = (e2297 _v)) at p2299
  simp only [e2301, e1128, e2300, p2299]
theorem n9546 (_v : Vars) (_q : Query _v)  : (e6263 _v) := by
  simp only [e5, e6, e10, e12, e36, e111, e2297, e2300, e2302, e2303, e6263] at *
  omega
theorem n9547 (_v : Vars) (_q : Query _v)  : (e6264 _v) := by
  have p9545 := n9545 _v _q 
  have p9546 := n9546 _v _q 
  exact (Iff.trans p9545 p9546)
theorem n9549 (_v : Vars) (_q : Query _v)  : (e9548 _v) := by
  have p9547 := n9547 _v _q 
  have p2292 := n2292 _v _q 
  change ((e1128 _v) ↔ (e2303 _v)) at p9547
  change ((e1123 _v) = (e2290 _v)) at p2292
  simp only [e9548, e1130, e6265, p9547, p2292]
theorem n9552 (_v : Vars) (_q : Query _v)  : (e9551 _v) := by
  have p9544 := n9544 _v _q 
  have p9549 := n9549 _v _q 
  change ((e1728 _v) ↔ (e2296 _v)) at p9544
  change ((e1130 _v) = (e6265 _v)) at p9549
  simp only [e9551, e5706, e9550, p9544, p9549]
theorem n9553 (_v : Vars) (_q : Query _v)  : (e2308 _v) := by
  have p2306 := n2306 _v _q 
  change ((e1133 _v) = (e2304 _v)) at p2306
  simp only [e2308, e1735, e2307, p2306]
theorem n9554 (_v : Vars) (_q : Query _v)  : (e6266 _v) := by
  simp only [e5, e6, e10, e12, e41, e43, e44, e111, e760, e761, e2304, e2307, e2309, e2310, e6266] at *
  omega
theorem n9555 (_v : Vars) (_q : Query _v)  : (e6267 _v) := by
  have p9553 := n9553 _v _q 
  have p9554 := n9554 _v _q 
  exact (Iff.trans p9553 p9554)
theorem n9556 (_v : Vars) (_q : Query _v)  : (e2315 _v) := by
  have p2313 := n2313 _v _q 
  change ((e1137 _v) = (e2311 _v)) at p2313
  simp only [e2315, e1138, e2314, p2313]
theorem n9557 (_v : Vars) (_q : Query _v)  : (e6268 _v) := by
  simp only [e5, e6, e10, e12, e43, e44, e111, e760, e761, e2311, e2314, e2316, e2317, e6268] at *
  omega
theorem n9558 (_v : Vars) (_q : Query _v)  : (e6269 _v) := by
  have p9556 := n9556 _v _q 
  have p9557 := n9557 _v _q 
  exact (Iff.trans p9556 p9557)
theorem n9560 (_v : Vars) (_q : Query _v)  : (e9559 _v) := by
  have p9558 := n9558 _v _q 
  have p2306 := n2306 _v _q 
  change ((e1138 _v) ↔ (e2317 _v)) at p9558
  change ((e1133 _v) = (e2304 _v)) at p2306
  simp only [e9559, e1140, e6270, p9558, p2306]
theorem n9563 (_v : Vars) (_q : Query _v)  : (e9562 _v) := by
  have p9555 := n9555 _v _q 
  have p9560 := n9560 _v _q 
  change ((e1735 _v) ↔ (e2310 _v)) at p9555
  change ((e1140 _v) = (e6270 _v)) at p9560
  simp only [e9562, e5716, e9561, p9555, p9560]
theorem n9564 (_v : Vars) (_q : Query _v)  : (e2322 _v) := by
  have p2320 := n2320 _v _q 
  change ((e1143 _v) = (e2318 _v)) at p2320
  simp only [e2322, e1742, e2321, p2320]
theorem n9565 (_v : Vars) (_q : Query _v)  : (e6271 _v) := by
  simp only [e5, e6, e10, e12, e41, e111, e266, e267, e781, e782, e2318, e2321, e2323, e2324, e6271] at *
  omega
theorem n9566 (_v : Vars) (_q : Query _v)  : (e6272 _v) := by
  have p9564 := n9564 _v _q 
  have p9565 := n9565 _v _q 
  exact (Iff.trans p9564 p9565)
theorem n9567 (_v : Vars) (_q : Query _v)  : (e2329 _v) := by
  have p2327 := n2327 _v _q 
  change ((e1147 _v) = (e2325 _v)) at p2327
  simp only [e2329, e1148, e2328, p2327]
theorem n9568 (_v : Vars) (_q : Query _v)  : (e6273 _v) := by
  simp only [e5, e6, e10, e12, e111, e266, e267, e781, e782, e2325, e2328, e2330, e2331, e6273] at *
  omega
theorem n9569 (_v : Vars) (_q : Query _v)  : (e6274 _v) := by
  have p9567 := n9567 _v _q 
  have p9568 := n9568 _v _q 
  exact (Iff.trans p9567 p9568)
theorem n9571 (_v : Vars) (_q : Query _v)  : (e9570 _v) := by
  have p9569 := n9569 _v _q 
  have p2320 := n2320 _v _q 
  change ((e1148 _v) ↔ (e2331 _v)) at p9569
  change ((e1143 _v) = (e2318 _v)) at p2320
  simp only [e9570, e1150, e6275, p9569, p2320]
theorem n9574 (_v : Vars) (_q : Query _v)  : (e9573 _v) := by
  have p9566 := n9566 _v _q 
  have p9571 := n9571 _v _q 
  change ((e1742 _v) ↔ (e2324 _v)) at p9566
  change ((e1150 _v) = (e6275 _v)) at p9571
  simp only [e9573, e5726, e9572, p9566, p9571]
theorem n9575 (_v : Vars) (_q : Query _v)  : (e2336 _v) := by
  have p2334 := n2334 _v _q 
  change ((e1153 _v) = (e2332 _v)) at p2334
  simp only [e2336, e1749, e2335, p2334]
theorem n9576 (_v : Vars) (_q : Query _v)  : (e6276 _v) := by
  simp only [e5, e6, e10, e12, e41, e108, e109, e111, e802, e803, e2332, e2335, e2337, e2338, e6276] at *
  omega
theorem n9577 (_v : Vars) (_q : Query _v)  : (e6277 _v) := by
  have p9575 := n9575 _v _q 
  have p9576 := n9576 _v _q 
  exact (Iff.trans p9575 p9576)
theorem n9578 (_v : Vars) (_q : Query _v)  : (e2343 _v) := by
  have p2341 := n2341 _v _q 
  change ((e1157 _v) = (e2339 _v)) at p2341
  simp only [e2343, e1158, e2342, p2341]
theorem n9579 (_v : Vars) (_q : Query _v)  : (e6278 _v) := by
  simp only [e5, e6, e10, e12, e108, e109, e111, e802, e803, e2339, e2342, e2344, e2345, e6278] at *
  omega
theorem n9580 (_v : Vars) (_q : Query _v)  : (e6279 _v) := by
  have p9578 := n9578 _v _q 
  have p9579 := n9579 _v _q 
  exact (Iff.trans p9578 p9579)
theorem n9582 (_v : Vars) (_q : Query _v)  : (e9581 _v) := by
  have p9580 := n9580 _v _q 
  have p2334 := n2334 _v _q 
  change ((e1158 _v) ↔ (e2345 _v)) at p9580
  change ((e1153 _v) = (e2332 _v)) at p2334
  simp only [e9581, e1160, e6280, p9580, p2334]
theorem n9585 (_v : Vars) (_q : Query _v)  : (e9584 _v) := by
  have p9577 := n9577 _v _q 
  have p9582 := n9582 _v _q 
  change ((e1749 _v) ↔ (e2338 _v)) at p9577
  change ((e1160 _v) = (e6280 _v)) at p9582
  simp only [e9584, e5736, e9583, p9577, p9582]
theorem n9587 (_v : Vars) (_q : Query _v)  : (e9586 _v) := by
  have p2348 := n2348 _v _q 
  change ((e1167 _v) = (e2346 _v)) at p2348
  simp only [e9586, e1170, e2349, p2348]
theorem n9589 (_v : Vars) (_q : Query _v)  : (e9588 _v) := by
  simp only [e5, e6, e8, e10, e12, e36, e41, e111, e2346, e2349, e2350, e2351, e9588] at *
  omega
theorem n9591 (_v : Vars) (_q : Query _v)  : (e9590 _v) := by
  have p9587 := n9587 _v _q 
  have p9589 := n9589 _v _q 
  exact (Iff.trans p9587 p9589)
theorem n9592 (_v : Vars) (_q : Query _v)  : (e2356 _v) := by
  have p2354 := n2354 _v _q 
  change ((e1172 _v) = (e2352 _v)) at p2354
  simp only [e2356, e1173, e2355, p2354]
theorem n9593 (_v : Vars) (_q : Query _v)  : (e6281 _v) := by
  simp only [e5, e6, e8, e10, e12, e36, e111, e2352, e2355, e2357, e2358, e6281] at *
  omega
theorem n9594 (_v : Vars) (_q : Query _v)  : (e6282 _v) := by
  have p9592 := n9592 _v _q 
  have p9593 := n9593 _v _q 
  exact (Iff.trans p9592 p9593)
theorem n9596 (_v : Vars) (_q : Query _v)  : (e9595 _v) := by
  have p9594 := n9594 _v _q 
  have p2348 := n2348 _v _q 
  change ((e1173 _v) ↔ (e2358 _v)) at p9594
  change ((e1167 _v) = (e2346 _v)) at p2348
  simp only [e9595, e1174, e6283, p9594, p2348]
theorem n9599 (_v : Vars) (_q : Query _v)  : (e9598 _v) := by
  have p9591 := n9591 _v _q 
  have p9596 := n9596 _v _q 
  change ((e1170 _v) ↔ (e2351 _v)) at p9591
  change ((e1174 _v) = (e6283 _v)) at p9596
  simp only [e9598, e5765, e9597, p9591, p9596]
theorem n9601 (_v : Vars) (_q : Query _v)  : (e9600 _v) := by
  have p2361 := n2361 _v _q 
  change ((e1177 _v) = (e2359 _v)) at p2361
  simp only [e9600, e1180, e2362, p2361]
theorem n9603 (_v : Vars) (_q : Query _v)  : (e9602 _v) := by
  simp only [e5, e6, e8, e10, e12, e41, e43, e44, e111, e760, e761, e2359, e2362, e2363, e2364, e9602] at *
  omega
theorem n9605 (_v : Vars) (_q : Query _v)  : (e9604 _v) := by
  have p9601 := n9601 _v _q 
  have p9603 := n9603 _v _q 
  exact (Iff.trans p9601 p9603)
theorem n9606 (_v : Vars) (_q : Query _v)  : (e2369 _v) := by
  have p2367 := n2367 _v _q 
  change ((e1182 _v) = (e2365 _v)) at p2367
  simp only [e2369, e1183, e2368, p2367]
end
end Assembly
