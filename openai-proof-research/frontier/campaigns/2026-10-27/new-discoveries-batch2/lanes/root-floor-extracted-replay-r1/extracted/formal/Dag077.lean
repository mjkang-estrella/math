import Dag076
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n12332 (_v : Vars) (_q : Query _v)  : (e12331 _v) := by
  have p10380 := n10380 _v _q 
  change ((e9799 _v) = (e2970 _v)) at p10380
  simp only [e12331, e10039, e2971, p10380]
theorem n12334 (_v : Vars) (_q : Query _v)  : (e12333 _v) := by
  have p10391 := n10391 _v _q 
  change ((e9813 _v) = (e2972 _v)) at p10391
  simp only [e12333, e10040, e2973, p10391]
theorem n12336 (_v : Vars) (_q : Query _v)  : (e12335 _v) := by
  have p10396 := n10396 _v _q 
  simp only [e2618, e3221, e6352, e6688, e6689, e10392, e10393, e10394, e10395, e12335] at *
theorem n12339 (_v : Vars) (_q : Query _v)  : (e12338 _v) := by
  have p12336 := n12336 _v _q 
  change ((e6352 _v) = (e3221 _v)) at p12336
  simp only [e12338, e9827, e12337, p12336]
theorem n12340 (_v : Vars) (_q : Query _v)  : (e6693 _v) := by
  simp only [e2611, e2974, e3216, e3221, e3222, e6690, e6691, e6692, e6693] at *
  by_cases hc : ((e2610 _v) ≥ (e12 _v)) <;> simp [hc]
theorem n12342 (_v : Vars) (_q : Query _v)  : (e12341 _v) := by
  have p12340 := n12340 _v _q 
  simp only [e2611, e2974, e3216, e3221, e3222, e6690, e6691, e6692, e6693, e12337, e12341] at *
theorem n12344 (_v : Vars) (_q : Query _v)  : (e12343 _v) := by
  have p12339 := n12339 _v _q 
  have p12342 := n12342 _v _q 
  exact (Eq.trans p12339 p12342)
theorem n12346 (_v : Vars) (_q : Query _v)  : (e12345 _v) := by
  have p8636 := n8636 _v _q 
  simp only [e79, e80, e81, e5128, e5129, e5138, e5139, e6357, e8635, e12345] at *
theorem n12349 (_v : Vars) (_q : Query _v)  : (e12348 _v) := by
  have p12346 := n12346 _v _q 
  change ((e6357 _v) = (e80 _v)) at p12346
  simp only [e12348, e9838, e12347, p12346]
theorem n12350 (_v : Vars) (_q : Query _v)  : (e6697 _v) := by
  simp only [e80, e251, e2976, e4371, e4381, e6694, e6695, e6696, e6697] at *
  by_cases hc : ((e250 _v) ≥ (e12 _v)) <;> simp [hc]
theorem n12352 (_v : Vars) (_q : Query _v)  : (e12351 _v) := by
  have p12350 := n12350 _v _q 
  simp only [e80, e251, e2976, e4371, e4381, e6694, e6695, e6696, e6697, e12347, e12351] at *
theorem n12354 (_v : Vars) (_q : Query _v)  : (e12353 _v) := by
  have p12349 := n12349 _v _q 
  have p12352 := n12352 _v _q 
  exact (Eq.trans p12349 p12352)
theorem n12356 (_v : Vars) (_q : Query _v)  : (e12355 _v) := by
  have p10398 := n10398 _v _q 
  simp only [e2641, e3164, e3192, e6362, e6698, e6699, e6924, e6925, e10397, e12355] at *
theorem n12359 (_v : Vars) (_q : Query _v)  : (e12358 _v) := by
  have p12356 := n12356 _v _q 
  change ((e6362 _v) = (e3164 _v)) at p12356
  simp only [e12358, e9849, e12357, p12356]
theorem n12360 (_v : Vars) (_q : Query _v)  : (e6703 _v) := by
  simp only [e2634, e2977, e3164, e3171, e3181, e6700, e6701, e6702, e6703] at *
  by_cases hc : ((e2633 _v) ≥ (e12 _v)) <;> simp [hc]
theorem n12362 (_v : Vars) (_q : Query _v)  : (e12361 _v) := by
  have p12360 := n12360 _v _q 
  simp only [e2634, e2977, e3164, e3171, e3181, e6700, e6701, e6702, e6703, e12357, e12361] at *
theorem n12364 (_v : Vars) (_q : Query _v)  : (e12363 _v) := by
  have p12359 := n12359 _v _q 
  have p12362 := n12362 _v _q 
  exact (Eq.trans p12359 p12362)
theorem n12366 (_v : Vars) (_q : Query _v)  : (e12365 _v) := by
  have p10403 := n10403 _v _q 
  simp only [e2655, e3830, e6367, e6704, e6705, e10399, e10400, e10401, e10402, e12365] at *
theorem n12369 (_v : Vars) (_q : Query _v)  : (e12368 _v) := by
  have p12366 := n12366 _v _q 
  change ((e6367 _v) = (e3830 _v)) at p12366
  simp only [e12368, e9860, e12367, p12366]
theorem n12370 (_v : Vars) (_q : Query _v)  : (e6709 _v) := by
  simp only [e2648, e2978, e3825, e3830, e3831, e6706, e6707, e6708, e6709] at *
  by_cases hc : ((e2647 _v) ≥ (e12 _v)) <;> simp [hc]
theorem n12372 (_v : Vars) (_q : Query _v)  : (e12371 _v) := by
  have p12370 := n12370 _v _q 
  simp only [e2648, e2978, e3825, e3830, e3831, e6706, e6707, e6708, e6709, e12367, e12371] at *
theorem n12374 (_v : Vars) (_q : Query _v)  : (e12373 _v) := by
  have p12369 := n12369 _v _q 
  have p12372 := n12372 _v _q 
  exact (Eq.trans p12369 p12372)
theorem n12376 (_v : Vars) (_q : Query _v)  : (e12375 _v) := by
  have p10408 := n10408 _v _q 
  simp only [e2669, e3752, e6372, e6710, e6711, e10404, e10405, e10406, e10407, e12375] at *
theorem n12379 (_v : Vars) (_q : Query _v)  : (e12378 _v) := by
  have p12376 := n12376 _v _q 
  change ((e6372 _v) = (e3752 _v)) at p12376
  simp only [e12378, e9871, e12377, p12376]
theorem n12380 (_v : Vars) (_q : Query _v)  : (e6715 _v) := by
  simp only [e2662, e2979, e3747, e3752, e3753, e6712, e6713, e6714, e6715] at *
  by_cases hc : ((e2661 _v) ≥ (e12 _v)) <;> simp [hc]
theorem n12382 (_v : Vars) (_q : Query _v)  : (e12381 _v) := by
  have p12380 := n12380 _v _q 
  simp only [e2662, e2979, e3747, e3752, e3753, e6712, e6713, e6714, e6715, e12377, e12381] at *
theorem n12384 (_v : Vars) (_q : Query _v)  : (e12383 _v) := by
  have p12379 := n12379 _v _q 
  have p12382 := n12382 _v _q 
  exact (Eq.trans p12379 p12382)
theorem n12386 (_v : Vars) (_q : Query _v)  : (e12385 _v) := by
  have p10419 := n10419 _v _q 
  change ((e9885 _v) = (e2980 _v)) at p10419
  simp only [e12385, e10042, e2981, p10419]
theorem n12388 (_v : Vars) (_q : Query _v)  : (e12387 _v) := by
  have p10430 := n10430 _v _q 
  change ((e9899 _v) = (e49 _v)) at p10430
  simp only [e12387, e10043, e68, p10430]
theorem n12390 (_v : Vars) (_q : Query _v)  : (e12389 _v) := by
  have p10441 := n10441 _v _q 
  change ((e9913 _v) = (e2982 _v)) at p10441
  simp only [e12389, e10044, e2983, p10441]
theorem n12392 (_v : Vars) (_q : Query _v)  : (e12391 _v) := by
  have p10446 := n10446 _v _q 
  simp only [e2717, e3247, e6384, e6736, e6737, e10442, e10443, e10444, e10445, e12391] at *
theorem n12395 (_v : Vars) (_q : Query _v)  : (e12394 _v) := by
  have p12392 := n12392 _v _q 
  change ((e6384 _v) = (e3247 _v)) at p12392
  simp only [e12394, e9927, e12393, p12392]
theorem n12396 (_v : Vars) (_q : Query _v)  : (e6741 _v) := by
  simp only [e2710, e2984, e3242, e3247, e3248, e6738, e6739, e6740, e6741] at *
  by_cases hc : ((e2709 _v) ≥ (e12 _v)) <;> simp [hc]
theorem n12398 (_v : Vars) (_q : Query _v)  : (e12397 _v) := by
  have p12396 := n12396 _v _q 
  simp only [e2710, e2984, e3242, e3247, e3248, e6738, e6739, e6740, e6741, e12393, e12397] at *
theorem n12400 (_v : Vars) (_q : Query _v)  : (e12399 _v) := by
  have p12395 := n12395 _v _q 
  have p12398 := n12398 _v _q 
  exact (Eq.trans p12395 p12398)
theorem n12402 (_v : Vars) (_q : Query _v)  : (e12401 _v) := by
  have p10457 := n10457 _v _q 
  change ((e9941 _v) = (e2986 _v)) at p10457
  simp only [e12401, e10046, e2987, p10457]
theorem n12404 (_v : Vars) (_q : Query _v)  : (e12403 _v) := by
  have p10468 := n10468 _v _q 
  change ((e9955 _v) = (e2988 _v)) at p10468
  simp only [e12403, e10047, e2989, p10468]
theorem n12406 (_v : Vars) (_q : Query _v)  : (e12405 _v) := by
  have p10479 := n10479 _v _q 
  change ((e9969 _v) = (e2990 _v)) at p10479
  simp only [e12405, e10048, e2991, p10479]
theorem n12408 (_v : Vars) (_q : Query _v)  : (e12407 _v) := by
  have p10484 := n10484 _v _q 
  simp only [e2766, e3804, e6396, e6762, e6763, e10480, e10481, e10482, e10483, e12407] at *
theorem n12411 (_v : Vars) (_q : Query _v)  : (e12410 _v) := by
  have p12408 := n12408 _v _q 
  change ((e6396 _v) = (e3804 _v)) at p12408
  simp only [e12410, e9983, e12409, p12408]
theorem n12412 (_v : Vars) (_q : Query _v)  : (e6767 _v) := by
  simp only [e2759, e2992, e3799, e3804, e3805, e6764, e6765, e6766, e6767] at *
  by_cases hc : ((e2758 _v) ≥ (e12 _v)) <;> simp [hc]
theorem n12414 (_v : Vars) (_q : Query _v)  : (e12413 _v) := by
  have p12412 := n12412 _v _q 
  simp only [e2759, e2992, e3799, e3804, e3805, e6764, e6765, e6766, e6767, e12409, e12413] at *
theorem n12416 (_v : Vars) (_q : Query _v)  : (e12415 _v) := by
  have p12411 := n12411 _v _q 
  have p12414 := n12414 _v _q 
  exact (Eq.trans p12411 p12414)
theorem n12418 (_v : Vars) (_q : Query _v)  : (e12417 _v) := by
  have p3016 := n3016 _v _q 
  have p10534 := n10534 _v _q 
  exact (Iff.trans p3016 p10534)
theorem n12420 (_v : Vars) (_q : Query _v)  : (e12419 _v) := by
  have p3041 := n3041 _v _q 
  have p10543 := n10543 _v _q 
  exact (Iff.trans p3041 p10543)
end
end Assembly
