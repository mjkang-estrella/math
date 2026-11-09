import Dag015
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n5519 (_v : Vars) (_q : Query _v)  : (e801 _v) := by
  have p797 := n797 _v _q 
  have p5518 := n5518 _v _q 
  exact (Eq.trans p797 p5518)
theorem n5520 (_v : Vars) (_q : Query _v)  : (e807 _v) := by
  have p805 := n805 _v _q 
  change ((e798 _v) = (e803 _v)) at p805
  simp only [e807, e799, e806, p805]
theorem n5522 (_v : Vars) (_q : Query _v)  : (e5521 _v) := by
  have p5519 := n5519 _v _q 
  have p5520 := n5520 _v _q 
  exact (Eq.trans p5519 p5520)
theorem n5524 (_v : Vars) (_q : Query _v)  : (e822 _v) := by
  have p820 := n820 _v _q 
  have p739 := n739 _v _q 
  change ((e545 _v) = (e818 _v)) at p820
  change ((e531 _v) = (e2 _v)) at p739
  simp only [e822, e546, e821, p820, p739]
theorem n5529 (_v : Vars) (_q : Query _v)  : (e837 _v) := by
  have p820 := n820 _v _q 
  change ((e545 _v) = (e818 _v)) at p820
  simp only [e837, e549, e836, p820]
theorem n5530 (_v : Vars) (_q : Query _v)  : (e839 _v) := by
  simp only [e5, e6, e43, e44, e756, e818, e836, e838, e839] at *
  omega
theorem n5531 (_v : Vars) (_q : Query _v)  : (e840 _v) := by
  have p5529 := n5529 _v _q 
  have p5530 := n5530 _v _q 
  exact (Eq.trans p5529 p5530)
theorem n5532 (_v : Vars) (_q : Query _v)  : (e842 _v) := by
  have p763 := n763 _v _q 
  change ((e756 _v) = (e761 _v)) at p763
  simp only [e842, e838, e841, p763]
theorem n5533 (_v : Vars) (_q : Query _v)  : (e846 _v) := by
  have p5532 := n5532 _v _q 
  have p845 := n845 _v _q 
  exact (Eq.trans p5532 p845)
theorem n5534 (_v : Vars) (_q : Query _v)  : (e847 _v) := by
  have p5531 := n5531 _v _q 
  have p5533 := n5533 _v _q 
  exact (Eq.trans p5531 p5533)
theorem n5539 (_v : Vars) (_q : Query _v)  : (e854 _v) := by
  have p820 := n820 _v _q 
  change ((e545 _v) = (e818 _v)) at p820
  simp only [e854, e552, e853, p820]
theorem n5540 (_v : Vars) (_q : Query _v)  : (e856 _v) := by
  simp only [e5, e6, e266, e267, e777, e818, e853, e855, e856] at *
  omega
theorem n5541 (_v : Vars) (_q : Query _v)  : (e857 _v) := by
  have p5539 := n5539 _v _q 
  have p5540 := n5540 _v _q 
  exact (Eq.trans p5539 p5540)
theorem n5542 (_v : Vars) (_q : Query _v)  : (e859 _v) := by
  have p784 := n784 _v _q 
  change ((e777 _v) = (e782 _v)) at p784
  simp only [e859, e855, e858, p784]
theorem n5543 (_v : Vars) (_q : Query _v)  : (e863 _v) := by
  have p5542 := n5542 _v _q 
  have p862 := n862 _v _q 
  exact (Eq.trans p5542 p862)
theorem n5544 (_v : Vars) (_q : Query _v)  : (e864 _v) := by
  have p5541 := n5541 _v _q 
  have p5543 := n5543 _v _q 
  exact (Eq.trans p5541 p5543)
theorem n5549 (_v : Vars) (_q : Query _v)  : (e871 _v) := by
  have p820 := n820 _v _q 
  change ((e545 _v) = (e818 _v)) at p820
  simp only [e871, e555, e870, p820]
theorem n5550 (_v : Vars) (_q : Query _v)  : (e873 _v) := by
  simp only [e5, e6, e108, e109, e798, e818, e870, e872, e873] at *
  omega
theorem n5551 (_v : Vars) (_q : Query _v)  : (e874 _v) := by
  have p5549 := n5549 _v _q 
  have p5550 := n5550 _v _q 
  exact (Eq.trans p5549 p5550)
theorem n5552 (_v : Vars) (_q : Query _v)  : (e876 _v) := by
  have p805 := n805 _v _q 
  change ((e798 _v) = (e803 _v)) at p805
  simp only [e876, e872, e875, p805]
theorem n5553 (_v : Vars) (_q : Query _v)  : (e880 _v) := by
  have p5552 := n5552 _v _q 
  have p879 := n879 _v _q 
  exact (Eq.trans p5552 p879)
theorem n5554 (_v : Vars) (_q : Query _v)  : (e881 _v) := by
  have p5551 := n5551 _v _q 
  have p5553 := n5553 _v _q 
  exact (Eq.trans p5551 p5553)
theorem n5559 (_v : Vars) (_q : Query _v)  : (e893 _v) := by
  have p891 := n891 _v _q 
  have p739 := n739 _v _q 
  change ((e559 _v) = (e889 _v)) at p891
  change ((e531 _v) = (e2 _v)) at p739
  simp only [e893, e560, e892, p891, p739]
theorem n5564 (_v : Vars) (_q : Query _v)  : (e908 _v) := by
  have p891 := n891 _v _q 
  change ((e559 _v) = (e889 _v)) at p891
  simp only [e908, e563, e907, p891]
theorem n5565 (_v : Vars) (_q : Query _v)  : (e910 _v) := by
  simp only [e5, e6, e43, e44, e756, e889, e907, e909, e910] at *
  omega
theorem n5566 (_v : Vars) (_q : Query _v)  : (e911 _v) := by
  have p5564 := n5564 _v _q 
  have p5565 := n5565 _v _q 
  exact (Eq.trans p5564 p5565)
theorem n5567 (_v : Vars) (_q : Query _v)  : (e913 _v) := by
  have p763 := n763 _v _q 
  change ((e756 _v) = (e761 _v)) at p763
  simp only [e913, e909, e912, p763]
theorem n5568 (_v : Vars) (_q : Query _v)  : (e917 _v) := by
  have p5567 := n5567 _v _q 
  have p916 := n916 _v _q 
  exact (Eq.trans p5567 p916)
theorem n5569 (_v : Vars) (_q : Query _v)  : (e918 _v) := by
  have p5566 := n5566 _v _q 
  have p5568 := n5568 _v _q 
  exact (Eq.trans p5566 p5568)
theorem n5574 (_v : Vars) (_q : Query _v)  : (e925 _v) := by
  have p891 := n891 _v _q 
  change ((e559 _v) = (e889 _v)) at p891
  simp only [e925, e566, e924, p891]
theorem n5575 (_v : Vars) (_q : Query _v)  : (e927 _v) := by
  simp only [e5, e6, e266, e267, e777, e889, e924, e926, e927] at *
  omega
theorem n5576 (_v : Vars) (_q : Query _v)  : (e928 _v) := by
  have p5574 := n5574 _v _q 
  have p5575 := n5575 _v _q 
  exact (Eq.trans p5574 p5575)
theorem n5577 (_v : Vars) (_q : Query _v)  : (e930 _v) := by
  have p784 := n784 _v _q 
  change ((e777 _v) = (e782 _v)) at p784
  simp only [e930, e926, e929, p784]
theorem n5578 (_v : Vars) (_q : Query _v)  : (e934 _v) := by
  have p5577 := n5577 _v _q 
  have p933 := n933 _v _q 
  exact (Eq.trans p5577 p933)
theorem n5579 (_v : Vars) (_q : Query _v)  : (e935 _v) := by
  have p5576 := n5576 _v _q 
  have p5578 := n5578 _v _q 
  exact (Eq.trans p5576 p5578)
theorem n5584 (_v : Vars) (_q : Query _v)  : (e942 _v) := by
  have p891 := n891 _v _q 
  change ((e559 _v) = (e889 _v)) at p891
  simp only [e942, e569, e941, p891]
theorem n5585 (_v : Vars) (_q : Query _v)  : (e944 _v) := by
  simp only [e5, e6, e108, e109, e798, e889, e941, e943, e944] at *
  omega
theorem n5586 (_v : Vars) (_q : Query _v)  : (e945 _v) := by
  have p5584 := n5584 _v _q 
  have p5585 := n5585 _v _q 
  exact (Eq.trans p5584 p5585)
theorem n5587 (_v : Vars) (_q : Query _v)  : (e947 _v) := by
  have p805 := n805 _v _q 
  change ((e798 _v) = (e803 _v)) at p805
  simp only [e947, e943, e946, p805]
theorem n5588 (_v : Vars) (_q : Query _v)  : (e951 _v) := by
  have p5587 := n5587 _v _q 
  have p950 := n950 _v _q 
  exact (Eq.trans p5587 p950)
theorem n5589 (_v : Vars) (_q : Query _v)  : (e952 _v) := by
  have p5586 := n5586 _v _q 
  have p5588 := n5588 _v _q 
  exact (Eq.trans p5586 p5588)
theorem n5595 (_v : Vars) (_q : Query _v)  : (e5594 _v) := by
  have p959 := n959 _v _q 
  have p739 := n739 _v _q 
  change ((e572 _v) = (e572 _v)) at p959
  change ((e531 _v) = (e2 _v)) at p739
  simp only [e5594, e573, e960, p959, p739]
theorem n5601 (_v : Vars) (_q : Query _v)  : (e5600 _v) := by
  have p959 := n959 _v _q 
  change ((e572 _v) = (e572 _v)) at p959
  simp only [e5600, e576, p959]
theorem n5603 (_v : Vars) (_q : Query _v)  : (e5602 _v) := by
  simp only [e5, e6, e43, e44, e572, e576, e756, e972, e5602] at *
  omega
theorem n5605 (_v : Vars) (_q : Query _v)  : (e5604 _v) := by
  have p763 := n763 _v _q 
  change ((e756 _v) = (e761 _v)) at p763
  simp only [e5604, e972, e973, p763]
end
end Assembly
