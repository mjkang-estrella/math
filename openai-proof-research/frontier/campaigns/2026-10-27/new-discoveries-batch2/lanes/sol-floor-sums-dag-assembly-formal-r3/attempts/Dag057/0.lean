import Dag056
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n10468 (_v : Vars) (_q : Query _v)  : (e10467 _v) := by
  have p10463 := n10463 _v _q 
  have p10466 := n10466 _v _q 
  exact (Eq.trans p10463 p10466)
theorem n10469 (_v : Vars) (_q : Query _v)  : (e6757 _v) := by
  simp only [e2753, e2909, e2910, e4036, e6754, e6755, e6756, e6757] at *
  by_cases hc : ((e2752 _v) ≤ (e12 _v)) <;> simp [hc]
theorem n10471 (_v : Vars) (_q : Query _v)  : (e10470 _v) := by
  have p10469 := n10469 _v _q 
  simp only [e2753, e2909, e2910, e4036, e6393, e6754, e6755, e6756, e6757, e10470] at *
  tauto
theorem n10474 (_v : Vars) (_q : Query _v)  : (e10473 _v) := by
  have p10471 := n10471 _v _q 
  change ((e6393 _v) = (e2909 _v)) at p10471
  simp only [e10473, e9969, e10472, p10471]
theorem n10475 (_v : Vars) (_q : Query _v)  : (e6761 _v) := by
  simp only [e2746, e2909, e2990, e3975, e3985, e6758, e6759, e6760, e6761] at *
  by_cases hc : ((e2745 _v) ≥ (e12 _v)) <;> simp [hc]
theorem n10477 (_v : Vars) (_q : Query _v)  : (e10476 _v) := by
  have p10475 := n10475 _v _q 
  simp only [e2746, e2909, e2990, e3975, e3985, e6758, e6759, e6760, e6761, e10472, e10476] at *
  tauto
theorem n10479 (_v : Vars) (_q : Query _v)  : (e10478 _v) := by
  have p10474 := n10474 _v _q 
  have p10477 := n10477 _v _q 
  exact (Eq.trans p10474 p10477)
theorem n10484 (_v : Vars) (_q : Query _v)  : (e10483 _v) := by
  simp only [e2766, e3804, e6762, e6763, e10480, e10481, e10482, e10483] at *
  by_cases hc : ((e2765 _v) ≤ (e12 _v)) <;> simp [hc]
theorem n10485 (_v : Vars) (_q : Query _v)  : (e5365 _v) := by
  simp only [e436, e437, e445, e446, e5362, e5363, e5364, e5365] at *
  by_cases hc : ((e435 _v) ≤ (e12 _v)) <;> simp [hc]
theorem n10487 (_v : Vars) (_q : Query _v)  : (e10486 _v) := by
  have p10485 := n10485 _v _q 
  simp only [e436, e437, e445, e446, e5362, e5363, e5364, e5365, e6397, e10486] at *
  tauto
theorem n10490 (_v : Vars) (_q : Query _v)  : (e10489 _v) := by
  have p10487 := n10487 _v _q 
  change ((e6397 _v) = (e437 _v)) at p10487
  simp only [e10489, e10050, e10488, p10487]
theorem n10491 (_v : Vars) (_q : Query _v)  : (e6771 _v) := by
  simp only [e437, e2771, e2994, e3107, e3117, e6768, e6769, e6770, e6771] at *
  by_cases hc : ((e2770 _v) ≥ (e12 _v)) <;> simp [hc]
theorem n10493 (_v : Vars) (_q : Query _v)  : (e10492 _v) := by
  have p10491 := n10491 _v _q 
  simp only [e437, e2771, e2994, e3107, e3117, e6768, e6769, e6770, e6771, e10488, e10492] at *
  tauto
theorem n10495 (_v : Vars) (_q : Query _v)  : (e10494 _v) := by
  have p10490 := n10490 _v _q 
  have p10493 := n10493 _v _q 
  exact (Eq.trans p10490 p10493)
theorem n10496 (_v : Vars) (_q : Query _v)  : (e6775 _v) := by
  simp only [e2787, e2911, e2912, e4421, e6772, e6773, e6774, e6775] at *
  by_cases hc : ((e2786 _v) ≤ (e12 _v)) <;> simp [hc]
theorem n10498 (_v : Vars) (_q : Query _v)  : (e10497 _v) := by
  have p10496 := n10496 _v _q 
  simp only [e2787, e2911, e2912, e4421, e6398, e6772, e6773, e6774, e6775, e10497] at *
  tauto
theorem n10501 (_v : Vars) (_q : Query _v)  : (e10500 _v) := by
  have p10498 := n10498 _v _q 
  change ((e6398 _v) = (e2911 _v)) at p10498
  simp only [e10500, e10051, e10499, p10498]
theorem n10502 (_v : Vars) (_q : Query _v)  : (e6779 _v) := by
  simp only [e2781, e2911, e2995, e4262, e4272, e6776, e6777, e6778, e6779] at *
  by_cases hc : ((e2780 _v) ≥ (e12 _v)) <;> simp [hc]
theorem n10504 (_v : Vars) (_q : Query _v)  : (e10503 _v) := by
  have p10502 := n10502 _v _q 
  simp only [e2781, e2911, e2995, e4262, e4272, e6776, e6777, e6778, e6779, e10499, e10503] at *
  tauto
theorem n10506 (_v : Vars) (_q : Query _v)  : (e10505 _v) := by
  have p10501 := n10501 _v _q 
  have p10504 := n10504 _v _q 
  exact (Eq.trans p10501 p10504)
theorem n10507 (_v : Vars) (_q : Query _v)  : (e6783 _v) := by
  simp only [e2799, e2913, e2914, e4926, e6780, e6781, e6782, e6783] at *
  by_cases hc : ((e2798 _v) ≤ (e12 _v)) <;> simp [hc]
theorem n10509 (_v : Vars) (_q : Query _v)  : (e10508 _v) := by
  have p10507 := n10507 _v _q 
  simp only [e2799, e2913, e2914, e4926, e6399, e6780, e6781, e6782, e6783, e10508] at *
  tauto
theorem n10512 (_v : Vars) (_q : Query _v)  : (e10511 _v) := by
  have p10509 := n10509 _v _q 
  change ((e6399 _v) = (e2913 _v)) at p10509
  simp only [e10511, e10052, e10510, p10509]
theorem n10513 (_v : Vars) (_q : Query _v)  : (e6787 _v) := by
  simp only [e2793, e2913, e2996, e4901, e4911, e6784, e6785, e6786, e6787] at *
  by_cases hc : ((e2792 _v) ≥ (e12 _v)) <;> simp [hc]
theorem n10515 (_v : Vars) (_q : Query _v)  : (e10514 _v) := by
  have p10513 := n10513 _v _q 
  simp only [e2793, e2913, e2996, e4901, e4911, e6784, e6785, e6786, e6787, e10510, e10514] at *
  tauto
theorem n10517 (_v : Vars) (_q : Query _v)  : (e10516 _v) := by
  have p10512 := n10512 _v _q 
  have p10515 := n10515 _v _q 
  exact (Eq.trans p10512 p10515)
theorem n10518 (_v : Vars) (_q : Query _v)  : (e6791 _v) := by
  simp only [e2811, e2915, e2916, e4524, e6788, e6789, e6790, e6791] at *
  by_cases hc : ((e2810 _v) ≤ (e12 _v)) <;> simp [hc]
theorem n10520 (_v : Vars) (_q : Query _v)  : (e10519 _v) := by
  have p10518 := n10518 _v _q 
  simp only [e2811, e2915, e2916, e4524, e6400, e6788, e6789, e6790, e6791, e10519] at *
  tauto
theorem n10523 (_v : Vars) (_q : Query _v)  : (e10522 _v) := by
  have p10520 := n10520 _v _q 
  change ((e6400 _v) = (e2915 _v)) at p10520
  simp only [e10522, e10053, e10521, p10520]
theorem n10524 (_v : Vars) (_q : Query _v)  : (e6795 _v) := by
  simp only [e2805, e2915, e2997, e3950, e3955, e6792, e6793, e6794, e6795] at *
  by_cases hc : ((e2804 _v) ≥ (e12 _v)) <;> simp [hc]
theorem n10526 (_v : Vars) (_q : Query _v)  : (e10525 _v) := by
  have p10524 := n10524 _v _q 
  simp only [e2805, e2915, e2997, e3950, e3955, e6792, e6793, e6794, e6795, e10521, e10525] at *
  tauto
theorem n10528 (_v : Vars) (_q : Query _v)  : (e10527 _v) := by
  have p10523 := n10523 _v _q 
  have p10526 := n10526 _v _q 
  exact (Eq.trans p10523 p10526)
theorem n10530 (_v : Vars) (_q : Query _v)  : (e10529 _v) := by
  have p3008 := n3008 _v _q 
  have p6797 := n6797 _v _q 
  exact (Iff.trans p3008 p6797)
theorem n10532 (_v : Vars) (_q : Query _v)  : (e10531 _v) := by
  have p10530 := n10530 _v _q 
  change ((e3005 _v) ↔ (e3009 _v)) at p10530
  simp only [e10531, e6495, e6809, p10530]
theorem n10534 (_v : Vars) (_q : Query _v)  : (e10533 _v) := by
  have p6801 := n6801 _v _q 
  have p6805 := n6805 _v _q 
  exact (Iff.trans p6801 p6805)
theorem n10538 (_v : Vars) (_q : Query _v)  : (e10537 _v) := by
  have p3035 := n3035 _v _q 
  have p6813 := n6813 _v _q 
  exact (Iff.trans p3035 p6813)
theorem n10541 (_v : Vars) (_q : Query _v)  : (e10540 _v) := by
  have p10538 := n10538 _v _q 
  change ((e3032 _v) ↔ (e3036 _v)) at p10538
  simp only [e10540, e6405, e10539, p10538]
theorem n10543 (_v : Vars) (_q : Query _v)  : (e10542 _v) := by
  have p6817 := n6817 _v _q 
  have p6821 := n6821 _v _q 
  exact (Iff.trans p6817 p6821)
theorem n10551 (_v : Vars) (_q : Query _v)  : (e10550 _v) := by
  have p3060 := n3060 _v _q 
  have p6824 := n6824 _v _q 
  exact (Iff.trans p3060 p6824)
theorem n10553 (_v : Vars) (_q : Query _v)  : (e10552 _v) := by
  have p10551 := n10551 _v _q 
  change ((e3057 _v) ↔ (e3061 _v)) at p10551
  simp only [e10552, e6721, e6836, p10551]
theorem n10555 (_v : Vars) (_q : Query _v)  : (e10554 _v) := by
  have p6828 := n6828 _v _q 
  have p6832 := n6832 _v _q 
  exact (Iff.trans p6828 p6832)
theorem n10559 (_v : Vars) (_q : Query _v)  : (e10558 _v) := by
  have p3085 := n3085 _v _q 
  have p6840 := n6840 _v _q 
  exact (Iff.trans p3085 p6840)
theorem n10561 (_v : Vars) (_q : Query _v)  : (e10560 _v) := by
  have p10559 := n10559 _v _q 
  change ((e3082 _v) ↔ (e3086 _v)) at p10559
  simp only [e10560, e6440, e6852, p10559]
theorem n10563 (_v : Vars) (_q : Query _v)  : (e10562 _v) := by
  have p6844 := n6844 _v _q 
  have p6848 := n6848 _v _q 
  exact (Iff.trans p6844 p6848)
theorem n10567 (_v : Vars) (_q : Query _v)  : (e10566 _v) := by
  have p3112 := n3112 _v _q 
  have p6858 := n6858 _v _q 
  exact (Iff.trans p3112 p6858)
end
end Assembly
