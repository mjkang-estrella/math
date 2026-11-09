import Dag016
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n5611 (_v : Vars) (_q : Query _v)  : (e5610 _v) := by
  have p959 := n959 _v _q 
  change ((e572 _v) = (e572 _v)) at p959
  simp only [e5610, e579]
theorem n5613 (_v : Vars) (_q : Query _v)  : (e5612 _v) := by
  simp only [e5, e6, e266, e267, e572, e579, e777, e982, e5612] at *
  omega
theorem n5615 (_v : Vars) (_q : Query _v)  : (e5614 _v) := by
  have p784 := n784 _v _q 
  change ((e777 _v) = (e782 _v)) at p784
  simp only [e5614, e982, e983, p784]
theorem n5621 (_v : Vars) (_q : Query _v)  : (e5620 _v) := by
  have p959 := n959 _v _q 
  change ((e572 _v) = (e572 _v)) at p959
  simp only [e5620, e582]
theorem n5623 (_v : Vars) (_q : Query _v)  : (e5622 _v) := by
  simp only [e5, e6, e108, e109, e572, e582, e798, e992, e5622] at *
  omega
theorem n5625 (_v : Vars) (_q : Query _v)  : (e5624 _v) := by
  have p805 := n805 _v _q 
  change ((e798 _v) = (e803 _v)) at p805
  simp only [e5624, e992, e993, p805]
theorem n5630 (_v : Vars) (_q : Query _v)  : (e1008 _v) := by
  have p1006 := n1006 _v _q 
  have p739 := n739 _v _q 
  change ((e586 _v) = (e1004 _v)) at p1006
  change ((e531 _v) = (e2 _v)) at p739
  simp only [e1008, e587, e1007, p1006, p739]
theorem n5635 (_v : Vars) (_q : Query _v)  : (e1023 _v) := by
  have p1006 := n1006 _v _q 
  change ((e586 _v) = (e1004 _v)) at p1006
  simp only [e1023, e590, e1022, p1006]
theorem n5636 (_v : Vars) (_q : Query _v)  : (e1025 _v) := by
  simp only [e5, e6, e43, e44, e756, e1004, e1022, e1024, e1025] at *
  omega
theorem n5637 (_v : Vars) (_q : Query _v)  : (e1026 _v) := by
  have p5635 := n5635 _v _q 
  have p5636 := n5636 _v _q 
  exact (Eq.trans p5635 p5636)
theorem n5638 (_v : Vars) (_q : Query _v)  : (e1028 _v) := by
  have p763 := n763 _v _q 
  change ((e756 _v) = (e761 _v)) at p763
  simp only [e1028, e1024, e1027, p763]
theorem n5639 (_v : Vars) (_q : Query _v)  : (e1032 _v) := by
  have p5638 := n5638 _v _q 
  have p1031 := n1031 _v _q 
  exact (Eq.trans p5638 p1031)
theorem n5640 (_v : Vars) (_q : Query _v)  : (e1033 _v) := by
  have p5637 := n5637 _v _q 
  have p5639 := n5639 _v _q 
  exact (Eq.trans p5637 p5639)
theorem n5645 (_v : Vars) (_q : Query _v)  : (e1040 _v) := by
  have p1006 := n1006 _v _q 
  change ((e586 _v) = (e1004 _v)) at p1006
  simp only [e1040, e593, e1039, p1006]
theorem n5646 (_v : Vars) (_q : Query _v)  : (e1042 _v) := by
  simp only [e5, e6, e266, e267, e777, e1004, e1039, e1041, e1042] at *
  omega
theorem n5647 (_v : Vars) (_q : Query _v)  : (e1043 _v) := by
  have p5645 := n5645 _v _q 
  have p5646 := n5646 _v _q 
  exact (Eq.trans p5645 p5646)
theorem n5648 (_v : Vars) (_q : Query _v)  : (e1045 _v) := by
  have p784 := n784 _v _q 
  change ((e777 _v) = (e782 _v)) at p784
  simp only [e1045, e1041, e1044, p784]
theorem n5649 (_v : Vars) (_q : Query _v)  : (e1049 _v) := by
  have p5648 := n5648 _v _q 
  have p1048 := n1048 _v _q 
  exact (Eq.trans p5648 p1048)
theorem n5650 (_v : Vars) (_q : Query _v)  : (e1050 _v) := by
  have p5647 := n5647 _v _q 
  have p5649 := n5649 _v _q 
  exact (Eq.trans p5647 p5649)
theorem n5655 (_v : Vars) (_q : Query _v)  : (e1057 _v) := by
  have p1006 := n1006 _v _q 
  change ((e586 _v) = (e1004 _v)) at p1006
  simp only [e1057, e596, e1056, p1006]
theorem n5656 (_v : Vars) (_q : Query _v)  : (e1059 _v) := by
  simp only [e5, e6, e108, e109, e798, e1004, e1056, e1058, e1059] at *
  omega
theorem n5657 (_v : Vars) (_q : Query _v)  : (e1060 _v) := by
  have p5655 := n5655 _v _q 
  have p5656 := n5656 _v _q 
  exact (Eq.trans p5655 p5656)
theorem n5658 (_v : Vars) (_q : Query _v)  : (e1062 _v) := by
  have p805 := n805 _v _q 
  change ((e798 _v) = (e803 _v)) at p805
  simp only [e1062, e1058, e1061, p805]
theorem n5659 (_v : Vars) (_q : Query _v)  : (e1066 _v) := by
  have p5658 := n5658 _v _q 
  have p1065 := n1065 _v _q 
  exact (Eq.trans p5658 p1065)
theorem n5660 (_v : Vars) (_q : Query _v)  : (e1067 _v) := by
  have p5657 := n5657 _v _q 
  have p5659 := n5659 _v _q 
  exact (Eq.trans p5657 p5659)
theorem n5666 (_v : Vars) (_q : Query _v)  : (e5665 _v) := by
  have p1074 := n1074 _v _q 
  have p739 := n739 _v _q 
  change ((e599 _v) = (e599 _v)) at p1074
  change ((e531 _v) = (e2 _v)) at p739
  simp only [e5665, e600, e1075, p739]
theorem n5672 (_v : Vars) (_q : Query _v)  : (e5671 _v) := by
  have p1074 := n1074 _v _q 
  change ((e599 _v) = (e599 _v)) at p1074
  simp only [e5671, e603]
theorem n5674 (_v : Vars) (_q : Query _v)  : (e5673 _v) := by
  simp only [e5, e6, e43, e44, e599, e603, e756, e1087, e5673] at *
  omega
theorem n5676 (_v : Vars) (_q : Query _v)  : (e5675 _v) := by
  have p763 := n763 _v _q 
  change ((e756 _v) = (e761 _v)) at p763
  simp only [e5675, e1087, e1088, p763]
theorem n5682 (_v : Vars) (_q : Query _v)  : (e5681 _v) := by
  have p1074 := n1074 _v _q 
  change ((e599 _v) = (e599 _v)) at p1074
  simp only [e5681, e606]
theorem n5684 (_v : Vars) (_q : Query _v)  : (e5683 _v) := by
  simp only [e5, e6, e266, e267, e599, e606, e777, e1097, e5683] at *
  omega
theorem n5686 (_v : Vars) (_q : Query _v)  : (e5685 _v) := by
  have p784 := n784 _v _q 
  change ((e777 _v) = (e782 _v)) at p784
  simp only [e5685, e1097, e1098, p784]
theorem n5692 (_v : Vars) (_q : Query _v)  : (e5691 _v) := by
  have p1074 := n1074 _v _q 
  change ((e599 _v) = (e599 _v)) at p1074
  simp only [e5691, e609]
theorem n5694 (_v : Vars) (_q : Query _v)  : (e5693 _v) := by
  simp only [e5, e6, e108, e109, e599, e609, e798, e1107, e5693] at *
  omega
theorem n5696 (_v : Vars) (_q : Query _v)  : (e5695 _v) := by
  have p805 := n805 _v _q 
  change ((e798 _v) = (e803 _v)) at p805
  simp only [e5695, e1107, e1108, p805]
theorem n5702 (_v : Vars) (_q : Query _v)  : (e5701 _v) := by
  have p1118 := n1118 _v _q 
  have p739 := n739 _v _q 
  change ((e612 _v) = (e612 _v)) at p1118
  change ((e531 _v) = (e2 _v)) at p739
  simp only [e5701, e613, e1119, p739]
theorem n5708 (_v : Vars) (_q : Query _v)  : (e5707 _v) := by
  have p1118 := n1118 _v _q 
  change ((e612 _v) = (e612 _v)) at p1118
  simp only [e5707, e616]
theorem n5710 (_v : Vars) (_q : Query _v)  : (e5709 _v) := by
  simp only [e5, e6, e43, e44, e612, e616, e756, e1131, e5709] at *
  omega
theorem n5712 (_v : Vars) (_q : Query _v)  : (e5711 _v) := by
  have p763 := n763 _v _q 
  change ((e756 _v) = (e761 _v)) at p763
  simp only [e5711, e1131, e1132, p763]
theorem n5718 (_v : Vars) (_q : Query _v)  : (e5717 _v) := by
  have p1118 := n1118 _v _q 
  change ((e612 _v) = (e612 _v)) at p1118
  simp only [e5717, e619]
theorem n5720 (_v : Vars) (_q : Query _v)  : (e5719 _v) := by
  simp only [e5, e6, e266, e267, e612, e619, e777, e1141, e5719] at *
  omega
theorem n5722 (_v : Vars) (_q : Query _v)  : (e5721 _v) := by
  have p784 := n784 _v _q 
  change ((e777 _v) = (e782 _v)) at p784
  simp only [e5721, e1141, e1142, p784]
theorem n5728 (_v : Vars) (_q : Query _v)  : (e5727 _v) := by
  have p1118 := n1118 _v _q 
  change ((e612 _v) = (e612 _v)) at p1118
  simp only [e5727, e622]
theorem n5730 (_v : Vars) (_q : Query _v)  : (e5729 _v) := by
  simp only [e5, e6, e108, e109, e612, e622, e798, e1151, e5729] at *
  omega
theorem n5732 (_v : Vars) (_q : Query _v)  : (e5731 _v) := by
  have p805 := n805 _v _q 
  change ((e798 _v) = (e803 _v)) at p805
  simp only [e5731, e1151, e1152, p805]
end
end Assembly
