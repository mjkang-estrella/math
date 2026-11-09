import Dag233
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n20560 (_v : Vars) (_q : Query _v)  : (e104 _v) := by
  have p20559 := n20559 _v _q 
  have p14162 := n14162 _v _q 
  change (e106 _v) ∨ (e104 _v) at p20559
  change (¬ (e106 _v)) at p14162
  rcases p20559 with hlit | hlit
  · exact (False.elim (p14162 hlit))
  · exact hlit
theorem n20561 (_v : Vars) (_q : Query _v)  : (e5055 _v) := by
  simp only [e4747, e4748, e4752, e4753, e4754, e5055] at *
  tauto
theorem n20562 (_v : Vars) (_q : Query _v)  : (e4748 _v) := by
  have p20561 := n20561 _v _q 
  have p17873 := n17873 _v _q 
  change (e4754 _v) ∨ (e4748 _v) at p20561
  change (¬ (e4754 _v)) at p17873
  rcases p20561 with hlit | hlit
  · exact (False.elim (p17873 hlit))
  · exact hlit
theorem n20563 (_v : Vars) (_q : Query _v)  : (e5056 _v) := by
  simp only [e4653, e4654, e4658, e4659, e4660, e5056] at *
  tauto
theorem n20564 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e4654 _v) := by
  have p20563 := n20563 _v _q 
  have p15852 := n15852 _v _q h251
  change (e4660 _v) ∨ (e4654 _v) at p20563
  change (¬ (e4660 _v)) at p15852
  rcases p20563 with hlit | hlit
  · exact (False.elim (p15852 hlit))
  · exact hlit
theorem n20565 (_v : Vars) (_q : Query _v)  : (e5057 _v) := by
  simp only [e3714, e3715, e3716, e3717, e3718, e5057] at *
  tauto
theorem n20566 (_v : Vars) (_q : Query _v)  : (e3714 _v) := by
  have p20565 := n20565 _v _q 
  have p14453 := n14453 _v _q 
  change (e3718 _v) ∨ (e3714 _v) at p20565
  change (¬ (e3718 _v)) at p14453
  rcases p20565 with hlit | hlit
  · exact (False.elim (p14453 hlit))
  · exact hlit
theorem n20567 (_v : Vars) (_q : Query _v)  : (e5058 _v) := by
  simp only [e3512, e3513, e3514, e3515, e3516, e5058] at *
  tauto
theorem n20568 (_v : Vars) (_q : Query _v)  : (e3512 _v) := by
  have p20567 := n20567 _v _q 
  have p14420 := n14420 _v _q 
  change (e3516 _v) ∨ (e3512 _v) at p20567
  change (¬ (e3516 _v)) at p14420
  rcases p20567 with hlit | hlit
  · exact (False.elim (p14420 hlit))
  · exact hlit
theorem n20569 (_v : Vars) (_q : Query _v)  : (e5059 _v) := by
  simp only [e3270, e3271, e3275, e3276, e3277, e5059] at *
  tauto
theorem n20570 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e3278 _v) := by
  have p14378 := n14378 _v _q 
  have p12918 := n12918 _v _q h251
  change (¬ (e2310 _v)) ∨ (¬ (e3277 _v)) at p14378
  rcases p14378 with hlit | hlit
  · exact (False.elim (hlit p12918))
  · exact hlit
theorem n20571 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e3270 _v) := by
  have p20569 := n20569 _v _q 
  have p20570 := n20570 _v _q h251
  change (e3277 _v) ∨ (e3270 _v) at p20569
  change (¬ (e3277 _v)) at p20570
  rcases p20569 with hlit | hlit
  · exact (False.elim (p20570 hlit))
  · exact hlit
theorem n20572 (_v : Vars) (_q : Query _v)  : (e5061 _v) := by
  simp only [e3687, e3688, e3689, e3690, e3691, e5061] at *
  tauto
theorem n20573 (_v : Vars) (_q : Query _v)  : (e3687 _v) := by
  have p20572 := n20572 _v _q 
  have p14449 := n14449 _v _q 
  change (e3691 _v) ∨ (e3687 _v) at p20572
  change (¬ (e3691 _v)) at p14449
  rcases p20572 with hlit | hlit
  · exact (False.elim (p14449 hlit))
  · exact hlit
theorem n20574 (_v : Vars) (_q : Query _v)  : (e5062 _v) := by
  simp only [e3360, e3361, e3362, e3363, e3364, e5062] at *
  tauto
theorem n20575 (_v : Vars) (_q : Query _v)  : (e3360 _v) := by
  have p20574 := n20574 _v _q 
  have p14396 := n14396 _v _q 
  change (e3364 _v) ∨ (e3360 _v) at p20574
  change (¬ (e3364 _v)) at p14396
  rcases p20574 with hlit | hlit
  · exact (False.elim (p14396 hlit))
  · exact hlit
theorem n20576 (_v : Vars) (_q : Query _v)  : (e5063 _v) := by
  simp only [e4723, e4724, e4728, e4729, e4730, e5063] at *
  tauto
theorem n20577 (_v : Vars) (_q : Query _v)  : (e4723 _v) := by
  have p20576 := n20576 _v _q 
  have p20469 := n20469 _v _q 
  change (e4730 _v) ∨ (e4723 _v) at p20576
  change (¬ (e4730 _v)) at p20469
  rcases p20576 with hlit | hlit
  · exact (False.elim (p20469 hlit))
  · exact hlit
theorem n20578 (_v : Vars) (_q : Query _v)  : (e5064 _v) := by
  simp only [e4678, e4679, e4683, e4684, e4685, e5064] at *
  tauto
theorem n20579 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e4678 _v) := by
  have p20578 := n20578 _v _q 
  have p15864 := n15864 _v _q h251
  change (e4685 _v) ∨ (e4678 _v) at p20578
  change (¬ (e4685 _v)) at p15864
  rcases p20578 with hlit | hlit
  · exact (False.elim (p15864 hlit))
  · exact hlit
theorem n20580 (_v : Vars) (_q : Query _v)  : (e5065 _v) := by
  simp only [e3437, e3438, e3439, e3440, e3441, e5065] at *
  tauto
theorem n20581 (_v : Vars) (_q : Query _v)  : (e3439 _v) := by
  have p20580 := n20580 _v _q 
  have p14408 := n14408 _v _q 
  change (e3441 _v) ∨ (e3439 _v) at p20580
  change (¬ (e3441 _v)) at p14408
  rcases p20580 with hlit | hlit
  · exact (False.elim (p14408 hlit))
  · exact hlit
theorem n20582 (_v : Vars) (_q : Query _v)  : (e5066 _v) := by
  simp only [e298, e299, e300, e301, e302, e5066] at *
  tauto
theorem n20583 (_v : Vars) (_q : Query _v)  : (e300 _v) := by
  have p20582 := n20582 _v _q 
  have p14186 := n14186 _v _q 
  change (e302 _v) ∨ (e300 _v) at p20582
  change (¬ (e302 _v)) at p14186
  rcases p20582 with hlit | hlit
  · exact (False.elim (p14186 hlit))
  · exact hlit
theorem n20584 (_v : Vars) (_q : Query _v)  : (e5067 _v) := by
  simp only [e3610, e3611, e3612, e3613, e3614, e5067] at *
  tauto
theorem n20585 (_v : Vars) (_q : Query _v)  : (e3612 _v) := by
  have p20584 := n20584 _v _q 
  have p14437 := n14437 _v _q 
  change (e3614 _v) ∨ (e3612 _v) at p20584
  change (¬ (e3614 _v)) at p14437
  rcases p20584 with hlit | hlit
  · exact (False.elim (p14437 hlit))
  · exact hlit
theorem n20586 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e3160 _v) := by
  have p16573 := n16573 _v _q 
  have p20458 := n20458 _v _q h251
  change (e3162 _v) ∨ (e3160 _v) at p16573
  change (¬ (e3162 _v)) at p20458
  rcases p16573 with hlit | hlit
  · exact (False.elim (p20458 hlit))
  · exact hlit
theorem n20587 (_v : Vars) (_q : Query _v)  : (e5068 _v) := by
  simp only [e2999, e3000, e3001, e3002, e3003, e5068] at *
  tauto
theorem n20588 (_v : Vars) (_q : Query _v)  : (e2999 _v) := by
  have p20587 := n20587 _v _q 
  have p14344 := n14344 _v _q 
  change (e3003 _v) ∨ (e2999 _v) at p20587
  change (¬ (e3003 _v)) at p14344
  rcases p20587 with hlit | hlit
  · exact (False.elim (p14344 hlit))
  · exact hlit
theorem n20589 (_v : Vars) (_q : Query _v)  : (e5069 _v) := by
  simp only [e260, e261, e262, e263, e264, e5069] at *
  tauto
theorem n20590 (_v : Vars) (_q : Query _v)  : (e260 _v) := by
  have p20589 := n20589 _v _q 
  have p14182 := n14182 _v _q 
  change (e264 _v) ∨ (e260 _v) at p20589
  change (¬ (e264 _v)) at p14182
  rcases p20589 with hlit | hlit
  · exact (False.elim (p14182 hlit))
  · exact hlit
theorem n20591 (_v : Vars) (_q : Query _v)  : (e2139 _v) := by
  have p10892 := n10892 _v _q 
  have p20465 := n20465 _v _q 
  change (¬ (e2482 _v)) ∨ (e2139 _v) at p10892
  rcases p10892 with hlit | hlit
  · exact (False.elim (hlit p20465))
  · exact hlit
theorem n20592 (_v : Vars) (_q : Query _v)  : (e3862 _v) := by
  have p14472 := n14472 _v _q 
  have p20591 := n20591 _v _q 
  change (¬ (e2139 _v)) ∨ (¬ (e3861 _v)) at p14472
  rcases p14472 with hlit | hlit
  · exact (False.elim (hlit p20591))
  · exact hlit
theorem n20593 (_v : Vars) (_q : Query _v)  : (e3854 _v) := by
  have p17974 := n17974 _v _q 
  have p20592 := n20592 _v _q 
  change (e3861 _v) ∨ (e3854 _v) at p17974
  change (¬ (e3861 _v)) at p20592
  rcases p17974 with hlit | hlit
  · exact (False.elim (p20592 hlit))
  · exact hlit
theorem n20594 (_v : Vars) (_q : Query _v)  : (e5070 _v) := by
  simp only [e4458, e4459, e4463, e4464, e4465, e5070] at *
  tauto
theorem n20595 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e4458 _v) := by
  have p20594 := n20594 _v _q 
  have p15848 := n15848 _v _q h251
  change (e4465 _v) ∨ (e4458 _v) at p20594
  change (¬ (e4465 _v)) at p15848
  rcases p20594 with hlit | hlit
  · exact (False.elim (p15848 hlit))
  · exact hlit
theorem n20596 (_v : Vars) (_q : Query _v)  : (e5071 _v) := by
  simp only [e3412, e3413, e3414, e3415, e3416, e5071] at *
  tauto
theorem n20597 (_v : Vars) (_q : Query _v)  : (e3414 _v) := by
  have p20596 := n20596 _v _q 
  have p14404 := n14404 _v _q 
  change (e3416 _v) ∨ (e3414 _v) at p20596
  change (¬ (e3416 _v)) at p14404
  rcases p20596 with hlit | hlit
  · exact (False.elim (p14404 hlit))
  · exact hlit
theorem n20598 (_v : Vars) (_q : Query _v)  : (e5072 _v) := by
  simp only [e333, e334, e335, e336, e337, e5072] at *
  tauto
theorem n20599 (_v : Vars) (_q : Query _v)  : (e335 _v) := by
  have p20598 := n20598 _v _q 
  have p14190 := n14190 _v _q 
  change (e337 _v) ∨ (e335 _v) at p20598
  change (¬ (e337 _v)) at p14190
  rcases p20598 with hlit | hlit
  · exact (False.elim (p14190 hlit))
  · exact hlit
theorem n20600 (_v : Vars) (_q : Query _v)  : (e5073 _v) := by
  simp only [e3539, e3540, e3541, e3542, e3543, e5073] at *
  tauto
theorem n20601 (_v : Vars) (_q : Query _v)  : (e3541 _v) := by
  have p20600 := n20600 _v _q 
  have p14424 := n14424 _v _q 
  change (e3543 _v) ∨ (e3541 _v) at p20600
  change (¬ (e3543 _v)) at p14424
  rcases p20600 with hlit | hlit
  · exact (False.elim (p14424 hlit))
  · exact hlit
theorem n20602 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e4440 _v) := by
  have p16928 := n16928 _v _q 
  have p20456 := n20456 _v _q h251
  change (e4446 _v) ∨ (e4440 _v) at p16928
  change (¬ (e4446 _v)) at p20456
  rcases p16928 with hlit | hlit
  · exact (False.elim (p20456 hlit))
  · exact hlit
theorem n20603 (_v : Vars) (_q : Query _v)  : (e5074 _v) := by
  simp only [e3635, e3636, e3637, e3638, e3639, e5074] at *
  tauto
theorem n20604 (_v : Vars) (_q : Query _v)  : (e3637 _v) := by
  have p20603 := n20603 _v _q 
  have p14441 := n14441 _v _q 
  change (e3639 _v) ∨ (e3637 _v) at p20603
  change (¬ (e3639 _v)) at p14441
  rcases p20603 with hlit | hlit
  · exact (False.elim (p14441 hlit))
  · exact hlit
end
end Assembly
