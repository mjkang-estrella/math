import Dag058
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n10698 (_v : Vars) (_q : Query _v)  : (e10697 _v) := by
  have p3471 := n3471 _v _q 
  have p7100 := n7100 _v _q 
  exact (Iff.trans p3471 p7100)
theorem n10700 (_v : Vars) (_q : Query _v)  : (e10699 _v) := by
  have p10698 := n10698 _v _q 
  change ((e3468 _v) ↔ (e3472 _v)) at p10698
  simp only [e10699, e6609, e7112, p10698]
theorem n10702 (_v : Vars) (_q : Query _v)  : (e10701 _v) := by
  have p7104 := n7104 _v _q 
  have p7108 := n7108 _v _q 
  exact (Iff.trans p7104 p7108)
theorem n10706 (_v : Vars) (_q : Query _v)  : (e10705 _v) := by
  have p3496 := n3496 _v _q 
  have p7116 := n7116 _v _q 
  exact (Iff.trans p3496 p7116)
theorem n10708 (_v : Vars) (_q : Query _v)  : (e10707 _v) := by
  have p10706 := n10706 _v _q 
  change ((e3493 _v) ↔ (e3497 _v)) at p10706
  simp only [e10707, e6625, e7128, p10706]
theorem n10710 (_v : Vars) (_q : Query _v)  : (e10709 _v) := by
  have p7120 := n7120 _v _q 
  have p7124 := n7124 _v _q 
  exact (Iff.trans p7120 p7124)
theorem n10714 (_v : Vars) (_q : Query _v)  : (e10713 _v) := by
  have p3521 := n3521 _v _q 
  have p7132 := n7132 _v _q 
  exact (Iff.trans p3521 p7132)
theorem n10716 (_v : Vars) (_q : Query _v)  : (e10715 _v) := by
  have p10714 := n10714 _v _q 
  change ((e3518 _v) ↔ (e3522 _v)) at p10714
  simp only [e10715, e6562, e7144, p10714]
theorem n10718 (_v : Vars) (_q : Query _v)  : (e10717 _v) := by
  have p7136 := n7136 _v _q 
  have p7140 := n7140 _v _q 
  exact (Iff.trans p7136 p7140)
theorem n10722 (_v : Vars) (_q : Query _v)  : (e10721 _v) := by
  have p3548 := n3548 _v _q 
  have p7148 := n7148 _v _q 
  exact (Iff.trans p3548 p7148)
theorem n10724 (_v : Vars) (_q : Query _v)  : (e10723 _v) := by
  have p10722 := n10722 _v _q 
  change ((e3545 _v) ↔ (e3549 _v)) at p10722
  simp only [e10723, e6463, e7160, p10722]
theorem n10726 (_v : Vars) (_q : Query _v)  : (e10725 _v) := by
  have p7152 := n7152 _v _q 
  have p7156 := n7156 _v _q 
  exact (Iff.trans p7152 p7156)
theorem n10730 (_v : Vars) (_q : Query _v)  : (e10729 _v) := by
  have p3569 := n3569 _v _q 
  have p7164 := n7164 _v _q 
  exact (Iff.trans p3569 p7164)
theorem n10732 (_v : Vars) (_q : Query _v)  : (e10731 _v) := by
  have p10730 := n10730 _v _q 
  change ((e3564 _v) ↔ (e3573 _v)) at p10730
  simp only [e10731, e6657, e7176, p10730]
theorem n10734 (_v : Vars) (_q : Query _v)  : (e10733 _v) := by
  have p7168 := n7168 _v _q 
  have p7172 := n7172 _v _q 
  exact (Iff.trans p7168 p7172)
theorem n10738 (_v : Vars) (_q : Query _v)  : (e10737 _v) := by
  have p7192 := n7192 _v _q 
  have p7196 := n7196 _v _q 
  exact (Iff.trans p7192 p7196)
theorem n10739 (_v : Vars) (_q : Query _v)  : (e7202 _v) := by
  simp only [e5, e6, e12, e41, e43, e44, e46, e111, e760, e761, e2530, e3591, e3607, e7183, e7202] at *
  omega
theorem n10740 (_v : Vars) (_q : Query _v)  : (e7203 _v) := by
  simp only [e5, e6, e12, e41, e43, e44, e46, e111, e760, e761, e2530, e3591, e3608, e7185, e7203] at *
  omega
theorem n10743 (_v : Vars) (_q : Query _v)  : (e10742 _v) := by
  have p10739 := n10739 _v _q 
  have p10740 := n10740 _v _q 
  change ((e3607 _v) ↔ (e7183 _v)) at p10739
  change ((e3608 _v) ↔ (e7185 _v)) at p10740
  simp only [e10742, e3609, e10741, p10739, p10740]
theorem n10745 (_v : Vars) (_q : Query _v)  : (e10744 _v) := by
  simp only [e5, e6, e12, e41, e43, e44, e46, e111, e3591, e7183, e7184, e7185, e7186, e7187, e7204, e10741, e10744] at *
  omega
theorem n10753 (_v : Vars) (_q : Query _v)  : (e10752 _v) := by
  have p3619 := n3619 _v _q 
  have p7207 := n7207 _v _q 
  exact (Iff.trans p3619 p7207)
theorem n10755 (_v : Vars) (_q : Query _v)  : (e10754 _v) := by
  have p10753 := n10753 _v _q 
  change ((e3616 _v) ↔ (e3620 _v)) at p10753
  simp only [e10754, e6510, e7219, p10753]
theorem n10757 (_v : Vars) (_q : Query _v)  : (e10756 _v) := by
  have p7211 := n7211 _v _q 
  have p7215 := n7215 _v _q 
  exact (Iff.trans p7211 p7215)
theorem n10761 (_v : Vars) (_q : Query _v)  : (e10760 _v) := by
  have p3644 := n3644 _v _q 
  have p7223 := n7223 _v _q 
  exact (Iff.trans p3644 p7223)
theorem n10763 (_v : Vars) (_q : Query _v)  : (e10762 _v) := by
  have p10761 := n10761 _v _q 
  change ((e3641 _v) ↔ (e3645 _v)) at p10761
  simp only [e10762, e6448, e7235, p10761]
theorem n10765 (_v : Vars) (_q : Query _v)  : (e10764 _v) := by
  have p7227 := n7227 _v _q 
  have p7231 := n7231 _v _q 
  exact (Iff.trans p7227 p7231)
theorem n10769 (_v : Vars) (_q : Query _v)  : (e10768 _v) := by
  have p3669 := n3669 _v _q 
  have p7239 := n7239 _v _q 
  exact (Iff.trans p3669 p7239)
theorem n10771 (_v : Vars) (_q : Query _v)  : (e10770 _v) := by
  have p10769 := n10769 _v _q 
  change ((e3666 _v) ↔ (e3670 _v)) at p10769
  simp only [e10770, e6643, e7251, p10769]
theorem n10773 (_v : Vars) (_q : Query _v)  : (e10772 _v) := by
  have p7243 := n7243 _v _q 
  have p7247 := n7247 _v _q 
  exact (Iff.trans p7243 p7247)
theorem n10777 (_v : Vars) (_q : Query _v)  : (e10776 _v) := by
  have p3696 := n3696 _v _q 
  have p7255 := n7255 _v _q 
  exact (Iff.trans p3696 p7255)
theorem n10779 (_v : Vars) (_q : Query _v)  : (e10778 _v) := by
  have p10777 := n10777 _v _q 
  change ((e3693 _v) ↔ (e3697 _v)) at p10777
  simp only [e10778, e6544, e7267, p10777]
theorem n10781 (_v : Vars) (_q : Query _v)  : (e10780 _v) := by
  have p7259 := n7259 _v _q 
  have p7263 := n7263 _v _q 
  exact (Iff.trans p7259 p7263)
theorem n10785 (_v : Vars) (_q : Query _v)  : (e10784 _v) := by
  have p3723 := n3723 _v _q 
  have p7271 := n7271 _v _q 
  exact (Iff.trans p3723 p7271)
theorem n10787 (_v : Vars) (_q : Query _v)  : (e10786 _v) := by
  have p10785 := n10785 _v _q 
  change ((e3720 _v) ↔ (e3724 _v)) at p10785
  simp only [e10786, e6568, e7283, p10785]
theorem n10789 (_v : Vars) (_q : Query _v)  : (e10788 _v) := by
  have p7275 := n7275 _v _q 
  have p7279 := n7279 _v _q 
  exact (Iff.trans p7275 p7279)
theorem n10793 (_v : Vars) (_q : Query _v)  : (e10792 _v) := by
  have p3750 := n3750 _v _q 
  have p7287 := n7287 _v _q 
  exact (Iff.trans p3750 p7287)
theorem n10795 (_v : Vars) (_q : Query _v)  : (e10794 _v) := by
  have p10793 := n10793 _v _q 
  change ((e3747 _v) ↔ (e3751 _v)) at p10793
  simp only [e10794, e6713, e7299, p10793]
theorem n10797 (_v : Vars) (_q : Query _v)  : (e10796 _v) := by
  have p7291 := n7291 _v _q 
  have p7295 := n7295 _v _q 
  exact (Iff.trans p7291 p7295)
theorem n10801 (_v : Vars) (_q : Query _v)  : (e10800 _v) := by
  have p3777 := n3777 _v _q 
  have p7303 := n7303 _v _q 
  exact (Iff.trans p3777 p7303)
theorem n10803 (_v : Vars) (_q : Query _v)  : (e10802 _v) := by
  have p10801 := n10801 _v _q 
  change ((e3774 _v) ↔ (e3778 _v)) at p10801
  simp only [e10802, e6617, e7315, p10801]
theorem n10805 (_v : Vars) (_q : Query _v)  : (e10804 _v) := by
  have p7307 := n7307 _v _q 
  have p7311 := n7311 _v _q 
  exact (Iff.trans p7307 p7311)
theorem n10809 (_v : Vars) (_q : Query _v)  : (e10808 _v) := by
  have p3802 := n3802 _v _q 
  have p7319 := n7319 _v _q 
  exact (Iff.trans p3802 p7319)
theorem n10811 (_v : Vars) (_q : Query _v)  : (e10810 _v) := by
  have p10809 := n10809 _v _q 
  change ((e3799 _v) ↔ (e3803 _v)) at p10809
  simp only [e10810, e6765, e7331, p10809]
theorem n10813 (_v : Vars) (_q : Query _v)  : (e10812 _v) := by
  have p7323 := n7323 _v _q 
  have p7327 := n7327 _v _q 
  exact (Iff.trans p7323 p7327)
theorem n10817 (_v : Vars) (_q : Query _v)  : (e10816 _v) := by
  have p3828 := n3828 _v _q 
  have p7335 := n7335 _v _q 
  exact (Iff.trans p3828 p7335)
end
end Assembly
