import Dag054
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n10270 (_v : Vars) (_q : Query _v)  : (e6586 _v) := by
  simp only [e2364, e2879, e2951, e4652, e4662, e6583, e6584, e6585, e6586] at *
  by_cases hc : ((e2363 _v) ≥ (e12 _v)) <;> simp [hc]
theorem n10272 (_v : Vars) (_q : Query _v)  : (e10271 _v) := by
  have p10270 := n10270 _v _q 
  simp only [e2364, e2879, e2951, e4652, e4662, e6583, e6584, e6585, e6586, e10267, e10271] at *
theorem n10274 (_v : Vars) (_q : Query _v)  : (e10273 _v) := by
  have p10269 := n10269 _v _q 
  have p10272 := n10272 _v _q 
  exact (Eq.trans p10269 p10272)
theorem n10275 (_v : Vars) (_q : Query _v)  : (e6590 _v) := by
  simp only [e2384, e2881, e2882, e4766, e6587, e6588, e6589, e6590] at *
  by_cases hc : ((e2383 _v) ≤ (e12 _v)) <;> simp [hc]
theorem n10277 (_v : Vars) (_q : Query _v)  : (e10276 _v) := by
  have p10275 := n10275 _v _q 
  simp only [e2384, e2881, e2882, e4766, e6289, e6587, e6588, e6589, e6590, e10276] at *
theorem n10280 (_v : Vars) (_q : Query _v)  : (e10279 _v) := by
  have p10277 := n10277 _v _q 
  change ((e6289 _v) = (e2881 _v)) at p10277
  simp only [e10279, e9625, e10278, p10277]
theorem n10281 (_v : Vars) (_q : Query _v)  : (e6594 _v) := by
  simp only [e2377, e2881, e2953, e4746, e4756, e6591, e6592, e6593, e6594] at *
  by_cases hc : ((e2376 _v) ≥ (e12 _v)) <;> simp [hc]
theorem n10283 (_v : Vars) (_q : Query _v)  : (e10282 _v) := by
  have p10281 := n10281 _v _q 
  simp only [e2377, e2881, e2953, e4746, e4756, e6591, e6592, e6593, e6594, e10278, e10282] at *
theorem n10285 (_v : Vars) (_q : Query _v)  : (e10284 _v) := by
  have p10280 := n10280 _v _q 
  have p10283 := n10283 _v _q 
  exact (Eq.trans p10280 p10283)
theorem n10290 (_v : Vars) (_q : Query _v)  : (e10289 _v) := by
  simp only [e119, e2395, e6595, e6596, e10286, e10287, e10288, e10289] at *
  by_cases hc : ((e2394 _v) ≤ (e12 _v)) <;> simp [hc]
theorem n10292 (_v : Vars) (_q : Query _v)  : (e10291 _v) := by
  have p6599 := n6599 _v _q 
  simp only [e400, e402, e2410, e2883, e2884, e2885, e4347, e6597, e6598, e10291] at *
theorem n10295 (_v : Vars) (_q : Query _v)  : (e10294 _v) := by
  have p10292 := n10292 _v _q 
  change ((e2410 _v) = (e2883 _v)) at p10292
  simp only [e10294, e9650, e10293, p10292]
theorem n10296 (_v : Vars) (_q : Query _v)  : (e6603 _v) := by
  simp only [e2402, e2883, e2955, e3925, e3930, e6600, e6601, e6602, e6603] at *
  by_cases hc : ((e2401 _v) ≥ (e12 _v)) <;> simp [hc]
theorem n10298 (_v : Vars) (_q : Query _v)  : (e10297 _v) := by
  have p10296 := n10296 _v _q 
  simp only [e2402, e2883, e2955, e3925, e3930, e6600, e6601, e6602, e6603, e10293, e10297] at *
theorem n10300 (_v : Vars) (_q : Query _v)  : (e10299 _v) := by
  have p10295 := n10295 _v _q 
  have p10298 := n10298 _v _q 
  exact (Eq.trans p10295 p10298)
theorem n10302 (_v : Vars) (_q : Query _v)  : (e10301 _v) := by
  have p6607 := n6607 _v _q 
  simp only [e2424, e2427, e2886, e2887, e2888, e2889, e6604, e6605, e6606, e10301] at *
theorem n10305 (_v : Vars) (_q : Query _v)  : (e10304 _v) := by
  have p10302 := n10302 _v _q 
  change ((e2427 _v) = (e2887 _v)) at p10302
  simp only [e10304, e9661, e10303, p10302]
theorem n10306 (_v : Vars) (_q : Query _v)  : (e6611 _v) := by
  simp only [e2417, e2887, e2957, e3468, e3473, e6608, e6609, e6610, e6611] at *
  by_cases hc : ((e2416 _v) ≥ (e12 _v)) <;> simp [hc]
theorem n10308 (_v : Vars) (_q : Query _v)  : (e10307 _v) := by
  have p10306 := n10306 _v _q 
  simp only [e2417, e2887, e2957, e3468, e3473, e6608, e6609, e6610, e6611, e10303, e10307] at *
theorem n10310 (_v : Vars) (_q : Query _v)  : (e10309 _v) := by
  have p10305 := n10305 _v _q 
  have p10308 := n10308 _v _q 
  exact (Eq.trans p10305 p10308)
theorem n10312 (_v : Vars) (_q : Query _v)  : (e10311 _v) := by
  have p6615 := n6615 _v _q 
  simp only [e2441, e2444, e2890, e2891, e2892, e2893, e6612, e6613, e6614, e10311] at *
theorem n10315 (_v : Vars) (_q : Query _v)  : (e10314 _v) := by
  have p10312 := n10312 _v _q 
  change ((e2444 _v) = (e2891 _v)) at p10312
  simp only [e10314, e9672, e10313, p10312]
theorem n10316 (_v : Vars) (_q : Query _v)  : (e6619 _v) := by
  simp only [e2434, e2891, e2959, e3774, e3779, e6616, e6617, e6618, e6619] at *
  by_cases hc : ((e2433 _v) ≥ (e12 _v)) <;> simp [hc]
theorem n10318 (_v : Vars) (_q : Query _v)  : (e10317 _v) := by
  have p10316 := n10316 _v _q 
  simp only [e2434, e2891, e2959, e3774, e3779, e6616, e6617, e6618, e6619, e10313, e10317] at *
theorem n10320 (_v : Vars) (_q : Query _v)  : (e10319 _v) := by
  have p10315 := n10315 _v _q 
  have p10318 := n10318 _v _q 
  exact (Eq.trans p10315 p10318)
theorem n10322 (_v : Vars) (_q : Query _v)  : (e10321 _v) := by
  have p6623 := n6623 _v _q 
  simp only [e2458, e2461, e2894, e2895, e2896, e2897, e6620, e6621, e6622, e10321] at *
theorem n10325 (_v : Vars) (_q : Query _v)  : (e10324 _v) := by
  have p10322 := n10322 _v _q 
  change ((e2461 _v) = (e2895 _v)) at p10322
  simp only [e10324, e9683, e10323, p10322]
theorem n10326 (_v : Vars) (_q : Query _v)  : (e6627 _v) := by
  simp only [e2451, e2895, e2961, e3493, e3498, e6624, e6625, e6626, e6627] at *
  by_cases hc : ((e2450 _v) ≥ (e12 _v)) <;> simp [hc]
theorem n10328 (_v : Vars) (_q : Query _v)  : (e10327 _v) := by
  have p10326 := n10326 _v _q 
  simp only [e2451, e2895, e2961, e3493, e3498, e6624, e6625, e6626, e6627, e10323, e10327] at *
theorem n10330 (_v : Vars) (_q : Query _v)  : (e10329 _v) := by
  have p10325 := n10325 _v _q 
  have p10328 := n10328 _v _q 
  exact (Eq.trans p10325 p10328)
theorem n10332 (_v : Vars) (_q : Query _v)  : (e10331 _v) := by
  simp only [e2475, e4541, e4548, e6628, e6629, e8038, e8039, e10331] at *
  by_cases hc : ((e2474 _v) ≤ (e12 _v)) <;> simp [hc]
theorem n10334 (_v : Vars) (_q : Query _v)  : (e10333 _v) := by
  simp only [e2489, e4324, e4326, e6634, e6635, e7853, e7854, e10333] at *
  by_cases hc : ((e2488 _v) ≤ (e12 _v)) <;> simp [hc]
theorem n10339 (_v : Vars) (_q : Query _v)  : (e10338 _v) := by
  simp only [e2503, e3671, e6640, e6641, e10335, e10336, e10337, e10338] at *
  by_cases hc : ((e2502 _v) ≤ (e12 _v)) <;> simp [hc]
theorem n10344 (_v : Vars) (_q : Query _v)  : (e10343 _v) := by
  simp only [e376, e2515, e6646, e6647, e10340, e10341, e10342, e10343] at *
  by_cases hc : ((e2514 _v) ≤ (e12 _v)) <;> simp [hc]
theorem n10346 (_v : Vars) (_q : Query _v)  : (e10345 _v) := by
  simp only [e2529, e4808, e4840, e6648, e6649, e8310, e8311, e10345] at *
  by_cases hc : ((e2528 _v) ≤ (e12 _v)) <;> simp [hc]
theorem n10348 (_v : Vars) (_q : Query _v)  : (e10347 _v) := by
  simp only [e2543, e3574, e3592, e6654, e6655, e7197, e7198, e10347] at *
  by_cases hc : ((e2542 _v) ≤ (e12 _v)) <;> simp [hc]
theorem n10353 (_v : Vars) (_q : Query _v)  : (e10352 _v) := by
  simp only [e2557, e3903, e6660, e6661, e10349, e10350, e10351, e10352] at *
  by_cases hc : ((e2556 _v) ≤ (e12 _v)) <;> simp [hc]
theorem n10358 (_v : Vars) (_q : Query _v)  : (e10357 _v) := by
  simp only [e2571, e3344, e6666, e6667, e10354, e10355, e10356, e10357] at *
  by_cases hc : ((e2570 _v) ≤ (e12 _v)) <;> simp [hc]
theorem n10359 (_v : Vars) (_q : Query _v)  : (e5198 _v) := by
  simp only [e188, e196, e198, e199, e5195, e5196, e5197, e5198] at *
  by_cases hc : ((e195 _v) ≤ (e12 _v)) <;> simp [hc]
theorem n10361 (_v : Vars) (_q : Query _v)  : (e10360 _v) := by
  have p10359 := n10359 _v _q 
  simp only [e188, e196, e198, e199, e5195, e5196, e5197, e5198, e6343, e10360] at *
theorem n10364 (_v : Vars) (_q : Query _v)  : (e10363 _v) := by
  have p10361 := n10361 _v _q 
  change ((e6343 _v) = (e188 _v)) at p10361
  simp only [e10363, e9785, e10362, p10361]
theorem n10365 (_v : Vars) (_q : Query _v)  : (e5395 _v) := by
  simp only [e188, e466, e474, e475, e480, e5392, e5393, e5394, e5395] at *
  by_cases hc : ((e473 _v) ≥ (e12 _v)) <;> simp [hc]
theorem n10367 (_v : Vars) (_q : Query _v)  : (e10366 _v) := by
  have p10365 := n10365 _v _q 
  simp only [e188, e466, e474, e475, e480, e5392, e5393, e5394, e5395, e10362, e10366] at *
theorem n10369 (_v : Vars) (_q : Query _v)  : (e10368 _v) := by
  have p10364 := n10364 _v _q 
  have p10367 := n10367 _v _q 
  exact (Eq.trans p10364 p10367)
theorem n10370 (_v : Vars) (_q : Query _v)  : (e6675 _v) := by
  simp only [e2592, e2898, e2899, e4859, e6672, e6673, e6674, e6675] at *
  by_cases hc : ((e2591 _v) ≤ (e12 _v)) <;> simp [hc]
end
end Assembly
