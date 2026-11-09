import Dag094
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n13602 (_v : Vars) (_q : Query _v)  : (e7126 _v) := by
  have p13600 := n13600 _v _q 
  have p13601 := n13601 _v _q 
  exact (Iff.trans p13600 p13601)
theorem n13604 (_v : Vars) (_q : Query _v)  : (e13603 _v) := by
  have p10708 := n10708 _v _q 
  have p13602 := n13602 _v _q 
  change ((e6625 _v) ↔ (e7128 _v)) at p10708
  change ((e6626 _v) ↔ (e7125 _v)) at p13602
  simp only [e13603, e6627, e7129, p10708, p13602]
theorem n13607 (_v : Vars) (_q : Query _v)  : (e13606 _v) := by
  simp only [e5, e6, e12, e41, e46, e108, e109, e2450, e2451, e2962, e3487, e3488, e3489, e3490, e3491, e3497, e3504, e3505, e3507, e3510, e3511, e6624, e7121, e7122, e7125, e7128, e7129, e7130, e10711, e10712, e13605, e13606] at *
  omega
theorem n13609 (_v : Vars) (_q : Query _v)  : (e13608 _v) := by
  have p13604 := n13604 _v _q 
  have p13607 := n13607 _v _q 
  exact (Iff.trans p13604 p13607)
theorem n13610 (_v : Vars) (_q : Query _v)  : (e7142 _v) := by
  have p12483 := n12483 _v _q 
  change ((e3524 _v) ↔ (e7138 _v)) at p12483
  simp only [e7142, e6563, e7141, p12483]
theorem n13611 (_v : Vars) (_q : Query _v)  : (e7143 _v) := by
  simp only [e5, e6, e10, e12, e41, e111, e266, e267, e2323, e2324, e3530, e3531, e3532, e3534, e3537, e3538, e7137, e7138, e7141, e7143] at *
theorem n13612 (_v : Vars) (_q : Query _v)  : (e7142 _v) := by
  have p13610 := n13610 _v _q 
  have p13611 := n13611 _v _q 
  exact (Iff.trans p13610 p13611)
theorem n13614 (_v : Vars) (_q : Query _v)  : (e13613 _v) := by
  have p10716 := n10716 _v _q 
  have p13612 := n13612 _v _q 
  change ((e6562 _v) ↔ (e7144 _v)) at p10716
  change ((e6563 _v) ↔ (e7141 _v)) at p13612
  simp only [e13613, e6564, e7145, p10716, p13612]
theorem n13617 (_v : Vars) (_q : Query _v)  : (e13616 _v) := by
  simp only [e5, e6, e10, e12, e41, e111, e266, e267, e2323, e2324, e3512, e3513, e3514, e3515, e3516, e3522, e3530, e3531, e3532, e3534, e3537, e3538, e6561, e7137, e7138, e7141, e7144, e7145, e7146, e10719, e10720, e13615, e13616] at *
  omega
theorem n13619 (_v : Vars) (_q : Query _v)  : (e13618 _v) := by
  have p13614 := n13614 _v _q 
  have p13617 := n13617 _v _q 
  exact (Iff.trans p13614 p13617)
theorem n13620 (_v : Vars) (_q : Query _v)  : (e7158 _v) := by
  have p12485 := n12485 _v _q 
  change ((e3550 _v) ↔ (e7154 _v)) at p12485
  simp only [e7158, e6464, e7157, p12485]
theorem n13621 (_v : Vars) (_q : Query _v)  : (e7159 _v) := by
  simp only [e5, e6, e12, e41, e43, e44, e111, e2075, e2076, e2929, e3556, e3557, e3559, e3562, e3563, e7153, e7154, e7157, e7159] at *
theorem n13622 (_v : Vars) (_q : Query _v)  : (e7158 _v) := by
  have p13620 := n13620 _v _q 
  have p13621 := n13621 _v _q 
  exact (Iff.trans p13620 p13621)
theorem n13624 (_v : Vars) (_q : Query _v)  : (e13623 _v) := by
  have p10724 := n10724 _v _q 
  have p13622 := n13622 _v _q 
  change ((e6463 _v) ↔ (e7160 _v)) at p10724
  change ((e6464 _v) ↔ (e7157 _v)) at p13622
  simp only [e13623, e6465, e7161, p10724, p13622]
theorem n13627 (_v : Vars) (_q : Query _v)  : (e13626 _v) := by
  simp only [e5, e6, e12, e41, e43, e44, e111, e2075, e2076, e2929, e3539, e3540, e3541, e3542, e3543, e3549, e3556, e3557, e3559, e3562, e3563, e6462, e7153, e7154, e7157, e7160, e7161, e7162, e10727, e10728, e13625, e13626] at *
  omega
theorem n13629 (_v : Vars) (_q : Query _v)  : (e13628 _v) := by
  have p13624 := n13624 _v _q 
  have p13627 := n13627 _v _q 
  exact (Iff.trans p13624 p13627)
theorem n13630 (_v : Vars) (_q : Query _v)  : (e7174 _v) := by
  have p12487 := n12487 _v _q 
  change ((e3575 _v) ↔ (e7170 _v)) at p12487
  simp only [e7174, e6658, e7173, p12487]
theorem n13631 (_v : Vars) (_q : Query _v)  : (e7175 _v) := by
  simp only [e5, e6, e12, e41, e43, e44, e46, e111, e2535, e2536, e3581, e3582, e3583, e3585, e3588, e3589, e7169, e7170, e7173, e7175] at *
theorem n13632 (_v : Vars) (_q : Query _v)  : (e7174 _v) := by
  have p13630 := n13630 _v _q 
  have p13631 := n13631 _v _q 
  exact (Iff.trans p13630 p13631)
theorem n13634 (_v : Vars) (_q : Query _v)  : (e13633 _v) := by
  have p10732 := n10732 _v _q 
  have p13632 := n13632 _v _q 
  change ((e6657 _v) ↔ (e7176 _v)) at p10732
  change ((e6658 _v) ↔ (e7173 _v)) at p13632
  simp only [e13633, e6659, e7177, p10732, p13632]
theorem n13637 (_v : Vars) (_q : Query _v)  : (e13636 _v) := by
  simp only [e5, e6, e12, e41, e43, e44, e46, e111, e2535, e2536, e3565, e3566, e3570, e3571, e3572, e3573, e3581, e3582, e3583, e3585, e3588, e3589, e6656, e7169, e7170, e7173, e7176, e7177, e7178, e10735, e10736, e13635, e13636] at *
  omega
theorem n13639 (_v : Vars) (_q : Query _v)  : (e13638 _v) := by
  have p13634 := n13634 _v _q 
  have p13637 := n13637 _v _q 
  exact (Iff.trans p13634 p13637)
theorem n13641 (_v : Vars) (_q : Query _v)  : (e13640 _v) := by
  simp only [e5, e6, e12, e41, e43, e44, e46, e111, e2542, e2543, e3591, e7183, e7184, e7185, e7186, e7187, e7204, e10747, e13640] at *
theorem n13642 (_v : Vars) (_q : Query _v)  : (e12494 _v) := by
  have p12495 := n12495 _v _q 
  have p13641 := n13641 _v _q 
  exact (Iff.trans p12495 p13641)
theorem n13643 (_v : Vars) (_q : Query _v)  : (e7217 _v) := by
  have p12499 := n12499 _v _q 
  change ((e3621 _v) ↔ (e7213 _v)) at p12499
  simp only [e7217, e6511, e7216, p12499]
theorem n13644 (_v : Vars) (_q : Query _v)  : (e7218 _v) := by
  simp only [e5, e6, e10, e12, e41, e43, e44, e2193, e2194, e2938, e3627, e3628, e3630, e3633, e3634, e7212, e7213, e7216, e7218] at *
theorem n13645 (_v : Vars) (_q : Query _v)  : (e7217 _v) := by
  have p13643 := n13643 _v _q 
  have p13644 := n13644 _v _q 
  exact (Iff.trans p13643 p13644)
theorem n13647 (_v : Vars) (_q : Query _v)  : (e13646 _v) := by
  have p10755 := n10755 _v _q 
  have p13645 := n13645 _v _q 
  change ((e6510 _v) ↔ (e7219 _v)) at p10755
  change ((e6511 _v) ↔ (e7216 _v)) at p13645
  simp only [e13646, e6512, e7220, p10755, p13645]
theorem n13650 (_v : Vars) (_q : Query _v)  : (e13649 _v) := by
  simp only [e5, e6, e10, e12, e41, e43, e44, e2193, e2194, e2938, e3610, e3611, e3612, e3613, e3614, e3620, e3627, e3628, e3630, e3633, e3634, e6509, e7212, e7213, e7216, e7219, e7220, e7221, e10758, e10759, e13648, e13649] at *
  omega
theorem n13652 (_v : Vars) (_q : Query _v)  : (e13651 _v) := by
  have p13647 := n13647 _v _q 
  have p13650 := n13650 _v _q 
  exact (Iff.trans p13647 p13650)
theorem n13653 (_v : Vars) (_q : Query _v)  : (e7233 _v) := by
  have p12501 := n12501 _v _q 
  change ((e3646 _v) ↔ (e7229 _v)) at p12501
  simp only [e7233, e6449, e7232, p12501]
theorem n13654 (_v : Vars) (_q : Query _v)  : (e7234 _v) := by
  simp only [e5, e6, e8, e12, e41, e108, e109, e2043, e2044, e2925, e3652, e3653, e3655, e3658, e3659, e7228, e7229, e7232, e7234] at *
theorem n13655 (_v : Vars) (_q : Query _v)  : (e7233 _v) := by
  have p13653 := n13653 _v _q 
  have p13654 := n13654 _v _q 
  exact (Iff.trans p13653 p13654)
theorem n13657 (_v : Vars) (_q : Query _v)  : (e13656 _v) := by
  have p10763 := n10763 _v _q 
  have p13655 := n13655 _v _q 
  change ((e6448 _v) ↔ (e7235 _v)) at p10763
  change ((e6449 _v) ↔ (e7232 _v)) at p13655
  simp only [e13656, e6450, e7236, p10763, p13655]
theorem n13660 (_v : Vars) (_q : Query _v)  : (e13659 _v) := by
  simp only [e5, e6, e8, e12, e41, e108, e109, e2043, e2044, e2925, e3635, e3636, e3637, e3638, e3639, e3645, e3652, e3653, e3655, e3658, e3659, e6447, e7228, e7229, e7232, e7235, e7236, e7237, e10766, e10767, e13658, e13659] at *
  omega
theorem n13662 (_v : Vars) (_q : Query _v)  : (e13661 _v) := by
  have p13657 := n13657 _v _q 
  have p13660 := n13660 _v _q 
  exact (Iff.trans p13657 p13660)
theorem n13663 (_v : Vars) (_q : Query _v)  : (e7249 _v) := by
  have p12503 := n12503 _v _q 
  change ((e3672 _v) ↔ (e7245 _v)) at p12503
  simp only [e7249, e6644, e7248, p12503]
theorem n13664 (_v : Vars) (_q : Query _v)  : (e7250 _v) := by
  simp only [e5, e6, e8, e12, e41, e46, e266, e267, e2495, e2496, e3678, e3679, e3680, e3682, e3685, e3686, e7244, e7245, e7248, e7250] at *
theorem n13665 (_v : Vars) (_q : Query _v)  : (e7249 _v) := by
  have p13663 := n13663 _v _q 
  have p13664 := n13664 _v _q 
  exact (Iff.trans p13663 p13664)
theorem n13667 (_v : Vars) (_q : Query _v)  : (e13666 _v) := by
  have p10771 := n10771 _v _q 
  have p13665 := n13665 _v _q 
  change ((e6643 _v) ↔ (e7251 _v)) at p10771
  change ((e6644 _v) ↔ (e7248 _v)) at p13665
  simp only [e13666, e6645, e7252, p10771, p13665]
theorem n13670 (_v : Vars) (_q : Query _v)  : (e13669 _v) := by
  simp only [e5, e6, e8, e12, e41, e46, e266, e267, e2495, e2496, e3660, e3661, e3662, e3663, e3664, e3670, e3678, e3679, e3680, e3682, e3685, e3686, e6642, e7244, e7245, e7248, e7251, e7252, e7253, e10774, e10775, e13668, e13669] at *
  omega
theorem n13672 (_v : Vars) (_q : Query _v)  : (e13671 _v) := by
  have p13667 := n13667 _v _q 
  have p13670 := n13670 _v _q 
  exact (Iff.trans p13667 p13670)
theorem n13673 (_v : Vars) (_q : Query _v)  : (e7265 _v) := by
  have p12505 := n12505 _v _q 
  change ((e3699 _v) ↔ (e7261 _v)) at p12505
  simp only [e7265, e6545, e7264, p12505]
theorem n13674 (_v : Vars) (_q : Query _v)  : (e7266 _v) := by
  simp only [e5, e6, e8, e10, e12, e41, e108, e109, e2281, e2282, e3705, e3706, e3707, e3709, e3712, e3713, e7260, e7261, e7264, e7266] at *
theorem n13675 (_v : Vars) (_q : Query _v)  : (e7265 _v) := by
  have p13673 := n13673 _v _q 
  have p13674 := n13674 _v _q 
  exact (Iff.trans p13673 p13674)
end
end Assembly
