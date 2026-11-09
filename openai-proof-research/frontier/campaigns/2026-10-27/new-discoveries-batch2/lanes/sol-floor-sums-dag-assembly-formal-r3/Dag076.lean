import Dag075
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n12242 (_v : Vars) (_q : Query _v)  : (e12241 _v) := by
  have p10300 := n10300 _v _q 
  change ((e9650 _v) = (e2955 _v)) at p10300
  simp only [e12241, e10034, e2956, p10300]
theorem n12244 (_v : Vars) (_q : Query _v)  : (e12243 _v) := by
  have p10310 := n10310 _v _q 
  change ((e9661 _v) = (e2957 _v)) at p10310
  simp only [e12243, e10035, e2958, p10310]
theorem n12246 (_v : Vars) (_q : Query _v)  : (e12245 _v) := by
  have p10320 := n10320 _v _q 
  change ((e9672 _v) = (e2959 _v)) at p10320
  simp only [e12245, e10036, e2960, p10320]
theorem n12248 (_v : Vars) (_q : Query _v)  : (e12247 _v) := by
  have p10330 := n10330 _v _q 
  change ((e9683 _v) = (e2961 _v)) at p10330
  simp only [e12247, e10037, e2962, p10330]
theorem n12250 (_v : Vars) (_q : Query _v)  : (e12249 _v) := by
  have p10332 := n10332 _v _q 
  simp only [e2475, e4541, e4548, e6305, e6628, e6629, e8038, e8039, e10331, e12249] at *
theorem n12253 (_v : Vars) (_q : Query _v)  : (e12252 _v) := by
  have p12250 := n12250 _v _q 
  change ((e6305 _v) = (e4541 _v)) at p12250
  simp only [e12252, e9694, e12251, p12250]
theorem n12254 (_v : Vars) (_q : Query _v)  : (e6633 _v) := by
  simp only [e2468, e2963, e4541, e4789, e4799, e6630, e6631, e6632, e6633] at *
  by_cases hc : ((e2467 _v) ≥ (e12 _v)) <;> simp [hc]
theorem n12256 (_v : Vars) (_q : Query _v)  : (e12255 _v) := by
  have p12254 := n12254 _v _q 
  simp only [e2468, e2963, e4541, e4789, e4799, e6630, e6631, e6632, e6633, e12251, e12255] at *
theorem n12258 (_v : Vars) (_q : Query _v)  : (e12257 _v) := by
  have p12253 := n12253 _v _q 
  have p12256 := n12256 _v _q 
  exact (Eq.trans p12253 p12256)
theorem n12260 (_v : Vars) (_q : Query _v)  : (e12259 _v) := by
  have p10334 := n10334 _v _q 
  simp only [e2489, e4324, e4326, e6310, e6634, e6635, e7853, e7854, e10333, e12259] at *
theorem n12263 (_v : Vars) (_q : Query _v)  : (e12262 _v) := by
  have p12260 := n12260 _v _q 
  change ((e6310 _v) = (e4324 _v)) at p12260
  simp only [e12262, e9705, e12261, p12260]
theorem n12264 (_v : Vars) (_q : Query _v)  : (e6639 _v) := by
  simp only [e2482, e2964, e4324, e4396, e4406, e6636, e6637, e6638, e6639] at *
  by_cases hc : ((e2481 _v) ≥ (e12 _v)) <;> simp [hc]
theorem n12266 (_v : Vars) (_q : Query _v)  : (e12265 _v) := by
  have p12264 := n12264 _v _q 
  simp only [e2482, e2964, e4324, e4396, e4406, e6636, e6637, e6638, e6639, e12261, e12265] at *
theorem n12268 (_v : Vars) (_q : Query _v)  : (e12267 _v) := by
  have p12263 := n12263 _v _q 
  have p12266 := n12266 _v _q 
  exact (Eq.trans p12263 p12266)
theorem n12270 (_v : Vars) (_q : Query _v)  : (e12269 _v) := by
  have p10339 := n10339 _v _q 
  simp only [e2503, e3671, e6315, e6640, e6641, e10335, e10336, e10337, e10338, e12269] at *
theorem n12273 (_v : Vars) (_q : Query _v)  : (e12272 _v) := by
  have p12270 := n12270 _v _q 
  change ((e6315 _v) = (e3671 _v)) at p12270
  simp only [e12272, e9716, e12271, p12270]
theorem n12274 (_v : Vars) (_q : Query _v)  : (e6645 _v) := by
  simp only [e2496, e2965, e3666, e3671, e3672, e6642, e6643, e6644, e6645] at *
  by_cases hc : ((e2495 _v) ≥ (e12 _v)) <;> simp [hc]
theorem n12276 (_v : Vars) (_q : Query _v)  : (e12275 _v) := by
  have p12274 := n12274 _v _q 
  simp only [e2496, e2965, e3666, e3671, e3672, e6642, e6643, e6644, e6645, e12271, e12275] at *
theorem n12278 (_v : Vars) (_q : Query _v)  : (e12277 _v) := by
  have p12273 := n12273 _v _q 
  have p12276 := n12276 _v _q 
  exact (Eq.trans p12273 p12276)
theorem n12280 (_v : Vars) (_q : Query _v)  : (e12279 _v) := by
  have p10344 := n10344 _v _q 
  simp only [e376, e2515, e6320, e6646, e6647, e10340, e10341, e10342, e10343, e12279] at *
theorem n12283 (_v : Vars) (_q : Query _v)  : (e12282 _v) := by
  have p12280 := n12280 _v _q 
  change ((e6320 _v) = (e376 _v)) at p12280
  simp only [e12282, e9727, e12281, p12280]
theorem n12284 (_v : Vars) (_q : Query _v)  : (e5322 _v) := by
  simp only [e362, e370, e371, e376, e377, e5319, e5320, e5321, e5322] at *
  by_cases hc : ((e369 _v) ≥ (e12 _v)) <;> simp [hc]
theorem n12286 (_v : Vars) (_q : Query _v)  : (e12285 _v) := by
  have p12284 := n12284 _v _q 
  simp only [e362, e370, e371, e376, e377, e5319, e5320, e5321, e5322, e12281, e12285] at *
theorem n12288 (_v : Vars) (_q : Query _v)  : (e12287 _v) := by
  have p12283 := n12283 _v _q 
  have p12286 := n12286 _v _q 
  exact (Eq.trans p12283 p12286)
theorem n12290 (_v : Vars) (_q : Query _v)  : (e12289 _v) := by
  have p10346 := n10346 _v _q 
  simp only [e2529, e4808, e4840, e6325, e6648, e6649, e8310, e8311, e10345, e12289] at *
theorem n12293 (_v : Vars) (_q : Query _v)  : (e12292 _v) := by
  have p12290 := n12290 _v _q 
  change ((e6325 _v) = (e4808 _v)) at p12290
  simp only [e12292, e9738, e12291, p12290]
theorem n12294 (_v : Vars) (_q : Query _v)  : (e6653 _v) := by
  simp only [e2522, e2966, e4808, e4815, e4825, e6650, e6651, e6652, e6653] at *
  by_cases hc : ((e2521 _v) ≥ (e12 _v)) <;> simp [hc]
theorem n12296 (_v : Vars) (_q : Query _v)  : (e12295 _v) := by
  have p12294 := n12294 _v _q 
  simp only [e2522, e2966, e4808, e4815, e4825, e6650, e6651, e6652, e6653, e12291, e12295] at *
theorem n12298 (_v : Vars) (_q : Query _v)  : (e12297 _v) := by
  have p12293 := n12293 _v _q 
  have p12296 := n12296 _v _q 
  exact (Eq.trans p12293 p12296)
theorem n12300 (_v : Vars) (_q : Query _v)  : (e12299 _v) := by
  have p10348 := n10348 _v _q 
  simp only [e2543, e3574, e3592, e6330, e6654, e6655, e7197, e7198, e10347, e12299] at *
theorem n12303 (_v : Vars) (_q : Query _v)  : (e12302 _v) := by
  have p12300 := n12300 _v _q 
  change ((e6330 _v) = (e3574 _v)) at p12300
  simp only [e12302, e9749, e12301, p12300]
theorem n12304 (_v : Vars) (_q : Query _v)  : (e6659 _v) := by
  simp only [e2536, e2967, e3564, e3574, e3575, e6656, e6657, e6658, e6659] at *
  by_cases hc : ((e2535 _v) ≥ (e12 _v)) <;> simp [hc]
theorem n12306 (_v : Vars) (_q : Query _v)  : (e12305 _v) := by
  have p12304 := n12304 _v _q 
  simp only [e2536, e2967, e3564, e3574, e3575, e6656, e6657, e6658, e6659, e12301, e12305] at *
theorem n12308 (_v : Vars) (_q : Query _v)  : (e12307 _v) := by
  have p12303 := n12303 _v _q 
  have p12306 := n12306 _v _q 
  exact (Eq.trans p12303 p12306)
theorem n12310 (_v : Vars) (_q : Query _v)  : (e12309 _v) := by
  have p10353 := n10353 _v _q 
  simp only [e2557, e3903, e6335, e6660, e6661, e10349, e10350, e10351, e10352, e12309] at *
theorem n12313 (_v : Vars) (_q : Query _v)  : (e12312 _v) := by
  have p12310 := n12310 _v _q 
  change ((e6335 _v) = (e3903 _v)) at p12310
  simp only [e12312, e9760, e12311, p12310]
theorem n12314 (_v : Vars) (_q : Query _v)  : (e6665 _v) := by
  simp only [e2550, e2968, e3898, e3903, e3904, e6662, e6663, e6664, e6665] at *
  by_cases hc : ((e2549 _v) ≥ (e12 _v)) <;> simp [hc]
theorem n12316 (_v : Vars) (_q : Query _v)  : (e12315 _v) := by
  have p12314 := n12314 _v _q 
  simp only [e2550, e2968, e3898, e3903, e3904, e6662, e6663, e6664, e6665, e12311, e12315] at *
theorem n12318 (_v : Vars) (_q : Query _v)  : (e12317 _v) := by
  have p12313 := n12313 _v _q 
  have p12316 := n12316 _v _q 
  exact (Eq.trans p12313 p12316)
theorem n12320 (_v : Vars) (_q : Query _v)  : (e12319 _v) := by
  have p10358 := n10358 _v _q 
  simp only [e2571, e3344, e6340, e6666, e6667, e10354, e10355, e10356, e10357, e12319] at *
theorem n12323 (_v : Vars) (_q : Query _v)  : (e12322 _v) := by
  have p12320 := n12320 _v _q 
  change ((e6340 _v) = (e3344 _v)) at p12320
  simp only [e12322, e9771, e12321, p12320]
theorem n12324 (_v : Vars) (_q : Query _v)  : (e6671 _v) := by
  simp only [e2564, e2969, e3339, e3344, e3345, e6668, e6669, e6670, e6671] at *
  by_cases hc : ((e2563 _v) ≥ (e12 _v)) <;> simp [hc]
theorem n12326 (_v : Vars) (_q : Query _v)  : (e12325 _v) := by
  have p12324 := n12324 _v _q 
  simp only [e2564, e2969, e3339, e3344, e3345, e6668, e6669, e6670, e6671, e12321, e12325] at *
theorem n12328 (_v : Vars) (_q : Query _v)  : (e12327 _v) := by
  have p12323 := n12323 _v _q 
  have p12326 := n12326 _v _q 
  exact (Eq.trans p12323 p12326)
theorem n12330 (_v : Vars) (_q : Query _v)  : (e12329 _v) := by
  have p10369 := n10369 _v _q 
  change ((e9785 _v) = (e466 _v)) at p10369
  simp only [e12329, e10038, e486, p10369]
end
end Assembly
