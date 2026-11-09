import Dag055
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n10372 (_v : Vars) (_q : Query _v)  : (e10371 _v) := by
  have p10370 := n10370 _v _q 
  simp only [e2592, e2898, e2899, e4859, e6346, e6672, e6673, e6674, e6675, e10371] at *
  tauto
theorem n10375 (_v : Vars) (_q : Query _v)  : (e10374 _v) := by
  have p10372 := n10372 _v _q 
  change ((e6346 _v) = (e2898 _v)) at p10372
  simp only [e10374, e9799, e10373, p10372]
theorem n10376 (_v : Vars) (_q : Query _v)  : (e6679 _v) := by
  simp only [e2585, e2898, e2970, e4305, e4315, e6676, e6677, e6678, e6679] at *
  by_cases hc : ((e2584 _v) ≥ (e12 _v)) <;> simp [hc]
theorem n10378 (_v : Vars) (_q : Query _v)  : (e10377 _v) := by
  have p10376 := n10376 _v _q 
  simp only [e2585, e2898, e2970, e4305, e4315, e6676, e6677, e6678, e6679, e10373, e10377] at *
  tauto
theorem n10380 (_v : Vars) (_q : Query _v)  : (e10379 _v) := by
  have p10375 := n10375 _v _q 
  have p10378 := n10378 _v _q 
  exact (Eq.trans p10375 p10378)
theorem n10381 (_v : Vars) (_q : Query _v)  : (e6683 _v) := by
  simp only [e2605, e2900, e2901, e4078, e6680, e6681, e6682, e6683] at *
  by_cases hc : ((e2604 _v) ≤ (e12 _v)) <;> simp [hc]
theorem n10383 (_v : Vars) (_q : Query _v)  : (e10382 _v) := by
  have p10381 := n10381 _v _q 
  simp only [e2605, e2900, e2901, e4078, e6349, e6680, e6681, e6682, e6683, e10382] at *
  tauto
theorem n10386 (_v : Vars) (_q : Query _v)  : (e10385 _v) := by
  have p10383 := n10383 _v _q 
  change ((e6349 _v) = (e2900 _v)) at p10383
  simp only [e10385, e9813, e10384, p10383]
theorem n10387 (_v : Vars) (_q : Query _v)  : (e6687 _v) := by
  simp only [e2598, e2900, e2972, e4058, e4068, e6684, e6685, e6686, e6687] at *
  by_cases hc : ((e2597 _v) ≥ (e12 _v)) <;> simp [hc]
theorem n10389 (_v : Vars) (_q : Query _v)  : (e10388 _v) := by
  have p10387 := n10387 _v _q 
  simp only [e2598, e2900, e2972, e4058, e4068, e6684, e6685, e6686, e6687, e10384, e10388] at *
  tauto
theorem n10391 (_v : Vars) (_q : Query _v)  : (e10390 _v) := by
  have p10386 := n10386 _v _q 
  have p10389 := n10389 _v _q 
  exact (Eq.trans p10386 p10389)
theorem n10396 (_v : Vars) (_q : Query _v)  : (e10395 _v) := by
  simp only [e2618, e3221, e6688, e6689, e10392, e10393, e10394, e10395] at *
  by_cases hc : ((e2617 _v) ≤ (e12 _v)) <;> simp [hc]
theorem n10398 (_v : Vars) (_q : Query _v)  : (e10397 _v) := by
  simp only [e2641, e3164, e3192, e6698, e6699, e6924, e6925, e10397] at *
  by_cases hc : ((e2640 _v) ≤ (e12 _v)) <;> simp [hc]
theorem n10403 (_v : Vars) (_q : Query _v)  : (e10402 _v) := by
  simp only [e2655, e3830, e6704, e6705, e10399, e10400, e10401, e10402] at *
  by_cases hc : ((e2654 _v) ≤ (e12 _v)) <;> simp [hc]
theorem n10408 (_v : Vars) (_q : Query _v)  : (e10407 _v) := by
  simp only [e2669, e3752, e6710, e6711, e10404, e10405, e10406, e10407] at *
  by_cases hc : ((e2668 _v) ≤ (e12 _v)) <;> simp [hc]
theorem n10409 (_v : Vars) (_q : Query _v)  : (e6719 _v) := by
  simp only [e2680, e2902, e2903, e4203, e6716, e6717, e6718, e6719] at *
  by_cases hc : ((e2679 _v) ≤ (e12 _v)) <;> simp [hc]
theorem n10411 (_v : Vars) (_q : Query _v)  : (e10410 _v) := by
  have p10409 := n10409 _v _q 
  simp only [e2680, e2902, e2903, e4203, e6375, e6716, e6717, e6718, e6719, e10410] at *
  tauto
theorem n10414 (_v : Vars) (_q : Query _v)  : (e10413 _v) := by
  have p10411 := n10411 _v _q 
  change ((e6375 _v) = (e2902 _v)) at p10411
  simp only [e10413, e9885, e10412, p10411]
theorem n10415 (_v : Vars) (_q : Query _v)  : (e6723 _v) := by
  simp only [e496, e2902, e2980, e3057, e3062, e6720, e6721, e6722, e6723] at *
  by_cases hc : ((e495 _v) ≥ (e12 _v)) <;> simp [hc]
theorem n10417 (_v : Vars) (_q : Query _v)  : (e10416 _v) := by
  have p10415 := n10415 _v _q 
  simp only [e496, e2902, e2980, e3057, e3062, e6720, e6721, e6722, e6723, e10412, e10416] at *
  tauto
theorem n10419 (_v : Vars) (_q : Query _v)  : (e10418 _v) := by
  have p10414 := n10414 _v _q 
  have p10417 := n10417 _v _q 
  exact (Eq.trans p10414 p10417)
theorem n10420 (_v : Vars) (_q : Query _v)  : (e6727 _v) := by
  simp only [e61, e2691, e2904, e4018, e6724, e6725, e6726, e6727] at *
  by_cases hc : ((e2690 _v) ≤ (e12 _v)) <;> simp [hc]
theorem n10422 (_v : Vars) (_q : Query _v)  : (e10421 _v) := by
  have p10420 := n10420 _v _q 
  simp only [e61, e2691, e2904, e4018, e6378, e6724, e6725, e6726, e6727, e10421] at *
  tauto
theorem n10425 (_v : Vars) (_q : Query _v)  : (e10424 _v) := by
  have p10422 := n10422 _v _q 
  change ((e6378 _v) = (e61 _v)) at p10422
  simp only [e10424, e9899, e10423, p10422]
theorem n10426 (_v : Vars) (_q : Query _v)  : (e5111 _v) := by
  simp only [e48, e49, e50, e61, e62, e5108, e5109, e5110, e5111] at *
  by_cases hc : ((e47 _v) ≥ (e12 _v)) <;> simp [hc]
theorem n10428 (_v : Vars) (_q : Query _v)  : (e10427 _v) := by
  have p10426 := n10426 _v _q 
  simp only [e48, e49, e50, e61, e62, e5108, e5109, e5110, e5111, e10423, e10427] at *
  tauto
theorem n10430 (_v : Vars) (_q : Query _v)  : (e10429 _v) := by
  have p10425 := n10425 _v _q 
  have p10428 := n10428 _v _q 
  exact (Eq.trans p10425 p10428)
theorem n10431 (_v : Vars) (_q : Query _v)  : (e6731 _v) := by
  simp only [e2704, e2905, e2906, e3995, e6728, e6729, e6730, e6731] at *
  by_cases hc : ((e2703 _v) ≤ (e12 _v)) <;> simp [hc]
theorem n10433 (_v : Vars) (_q : Query _v)  : (e10432 _v) := by
  have p10431 := n10431 _v _q 
  simp only [e2704, e2905, e2906, e3995, e6381, e6728, e6729, e6730, e6731, e10432] at *
  tauto
theorem n10436 (_v : Vars) (_q : Query _v)  : (e10435 _v) := by
  have p10433 := n10433 _v _q 
  change ((e6381 _v) = (e2905 _v)) at p10433
  simp only [e10435, e9913, e10434, p10433]
theorem n10437 (_v : Vars) (_q : Query _v)  : (e6735 _v) := by
  simp only [e2697, e2905, e2982, e4490, e4500, e6732, e6733, e6734, e6735] at *
  by_cases hc : ((e2696 _v) ≥ (e12 _v)) <;> simp [hc]
theorem n10439 (_v : Vars) (_q : Query _v)  : (e10438 _v) := by
  have p10437 := n10437 _v _q 
  simp only [e2697, e2905, e2982, e4490, e4500, e6732, e6733, e6734, e6735, e10434, e10438] at *
  tauto
theorem n10441 (_v : Vars) (_q : Query _v)  : (e10440 _v) := by
  have p10436 := n10436 _v _q 
  have p10439 := n10439 _v _q 
  exact (Eq.trans p10436 p10439)
theorem n10446 (_v : Vars) (_q : Query _v)  : (e10445 _v) := by
  simp only [e2717, e3247, e6736, e6737, e10442, e10443, e10444, e10445] at *
  by_cases hc : ((e2716 _v) ≤ (e12 _v)) <;> simp [hc]
theorem n10447 (_v : Vars) (_q : Query _v)  : (e5226 _v) := by
  simp only [e211, e214, e216, e217, e5223, e5224, e5225, e5226] at *
  by_cases hc : ((e213 _v) ≤ (e12 _v)) <;> simp [hc]
theorem n10449 (_v : Vars) (_q : Query _v)  : (e10448 _v) := by
  have p10447 := n10447 _v _q 
  simp only [e211, e214, e216, e217, e5223, e5224, e5225, e5226, e6387, e10448] at *
  tauto
theorem n10452 (_v : Vars) (_q : Query _v)  : (e10451 _v) := by
  have p10449 := n10449 _v _q 
  change ((e6387 _v) = (e211 _v)) at p10449
  simp only [e10451, e9941, e10450, p10449]
theorem n10453 (_v : Vars) (_q : Query _v)  : (e6745 _v) := by
  simp only [e211, e2722, e2986, e4876, e4886, e6742, e6743, e6744, e6745] at *
  by_cases hc : ((e2721 _v) ≥ (e12 _v)) <;> simp [hc]
theorem n10455 (_v : Vars) (_q : Query _v)  : (e10454 _v) := by
  have p10453 := n10453 _v _q 
  simp only [e211, e2722, e2986, e4876, e4886, e6742, e6743, e6744, e6745, e10450, e10454] at *
  tauto
theorem n10457 (_v : Vars) (_q : Query _v)  : (e10456 _v) := by
  have p10452 := n10452 _v _q 
  have p10455 := n10455 _v _q 
  exact (Eq.trans p10452 p10455)
theorem n10458 (_v : Vars) (_q : Query _v)  : (e6749 _v) := by
  simp only [e2740, e2907, e2908, e4120, e6746, e6747, e6748, e6749] at *
  by_cases hc : ((e2739 _v) ≤ (e12 _v)) <;> simp [hc]
theorem n10460 (_v : Vars) (_q : Query _v)  : (e10459 _v) := by
  have p10458 := n10458 _v _q 
  simp only [e2740, e2907, e2908, e4120, e6390, e6746, e6747, e6748, e6749, e10459] at *
  tauto
theorem n10463 (_v : Vars) (_q : Query _v)  : (e10462 _v) := by
  have p10460 := n10460 _v _q 
  change ((e6390 _v) = (e2907 _v)) at p10460
  simp only [e10462, e9955, e10461, p10460]
theorem n10464 (_v : Vars) (_q : Query _v)  : (e6753 _v) := by
  simp only [e2733, e2907, e2988, e4100, e4110, e6750, e6751, e6752, e6753] at *
  by_cases hc : ((e2732 _v) ≥ (e12 _v)) <;> simp [hc]
theorem n10466 (_v : Vars) (_q : Query _v)  : (e10465 _v) := by
  have p10464 := n10464 _v _q 
  simp only [e2733, e2907, e2988, e4100, e4110, e6750, e6751, e6752, e6753, e10461, e10465] at *
  tauto
end
end Assembly
