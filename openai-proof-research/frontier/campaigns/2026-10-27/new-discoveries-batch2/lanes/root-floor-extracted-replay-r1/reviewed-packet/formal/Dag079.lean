import Dag078
import generated.th_lemma_3
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n12511 (_v : Vars) (_q : Query _v)  : (e12510 _v) := by
  have p3784 := n3784 _v _q 
  have p10805 := n10805 _v _q 
  exact (Iff.trans p3784 p10805)
theorem n12513 (_v : Vars) (_q : Query _v)  : (e12512 _v) := by
  have p3810 := n3810 _v _q 
  have p10813 := n10813 _v _q 
  exact (Iff.trans p3810 p10813)
theorem n12515 (_v : Vars) (_q : Query _v)  : (e12514 _v) := by
  have p3836 := n3836 _v _q 
  have p10821 := n10821 _v _q 
  exact (Iff.trans p3836 p10821)
theorem n12517 (_v : Vars) (_q : Query _v)  : (e12516 _v) := by
  have p3868 := n3868 _v _q 
  have p10829 := n10829 _v _q 
  exact (Iff.trans p3868 p10829)
theorem n12519 (_v : Vars) (_q : Query _v)  : (e12518 _v) := by
  have p3879 := n3879 _v _q 
  have p10833 := n10833 _v _q 
  exact (Iff.trans p3879 p10833)
theorem n12520 (_v : Vars) (_q : Query _v)  : (e7388 _v) := by
  simp only [e43, e760, e761, e2133, e3889, e3890, e3891, e6484, e7388] at *
  omega
theorem n12522 (_v : Vars) (_q : Query _v)  : (e12521 _v) := by
  have p10838 := n10838 _v _q 
  have p10840 := n10840 _v _q 
  exact (Iff.trans p10838 p10840)
theorem n12523 (_v : Vars) (_q : Query _v)  : (e10841 _v) := by
  have p12520 := n12520 _v _q 
  have p12522 := n12522 _v _q 
  exact (Iff.trans p12520 p12522)
theorem n12525 (_v : Vars) (_q : Query _v)  : (e12524 _v) := by
  have p12523 := n12523 _v _q 
  change ((e6484 _v) ↔ (e7391 _v)) at p12523
  simp only [e12524, e6485, e10842, p12523]
theorem n12529 (_v : Vars) (_q : Query _v)  : (e12528 _v) := by
  have p3909 := n3909 _v _q 
  have p10852 := n10852 _v _q 
  exact (Iff.trans p3909 p10852)
theorem n12531 (_v : Vars) (_q : Query _v)  : (e12530 _v) := by
  have p3935 := n3935 _v _q 
  have p10860 := n10860 _v _q 
  exact (Iff.trans p3935 p10860)
theorem n12533 (_v : Vars) (_q : Query _v)  : (e12532 _v) := by
  have p3960 := n3960 _v _q 
  have p10868 := n10868 _v _q 
  exact (Iff.trans p3960 p10868)
theorem n12535 (_v : Vars) (_q : Query _v)  : (e12534 _v) := by
  have p3990 := n3990 _v _q 
  have p10876 := n10876 _v _q 
  exact (Iff.trans p3990 p10876)
theorem n12537 (_v : Vars) (_q : Query _v)  : (e12536 _v) := by
  have p4000 := n4000 _v _q 
  have p10880 := n10880 _v _q 
  exact (Iff.trans p4000 p10880)
theorem n12539 (_v : Vars) (_q : Query _v)  : (e12538 _v) := by
  simp only [e266, e781, e782, e2692, e2906, e4010, e4011, e7479, e12538] at *
  omega
theorem n12541 (_v : Vars) (_q : Query _v)  : (e12540 _v) := by
  have p7482 := n7482 _v _q 
  have p10882 := n10882 _v _q 
  exact (Iff.trans p7482 p10882)
theorem n12543 (_v : Vars) (_q : Query _v)  : (e12542 _v) := by
  have p12539 := n12539 _v _q 
  have p12541 := n12541 _v _q 
  exact (Iff.trans p12539 p12541)
theorem n12544 (_v : Vars) (_q : Query _v) (h5138 : (e5138 _v)) (h6636 : (e6636 _v)) : (e7489 _v) := by
  have p11487 := n11487 _v _q h5138
  have p5257 := n5257 _v _q 
  have p5255 := n5255 _v _q 
  have p11031 := n11031 _v _q h6636
  have p8663 := n8663 _v _q 
  exact FloorCertificate.node_12544 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p11487 p5257 p5255 p11031 p8663
theorem n12546 (_v : Vars) (_q : Query _v)  : (e12545 _v) := by
  by_contra hc
  change ¬ ((e79 _v) ∨ (e2482 _v)) at hc
  have h5138 : (e5138 _v) := by
    change (¬ (e79 _v))
    tauto
  have h6636 : (e6636 _v) := by
    change (¬ (e2482 _v))
    tauto
  have p12544 := n12544 _v _q h5138 h6636
  exact p12544
theorem n12547 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e6486 _v) := by
  have p10899 := n10899 _v _q 
  have p10895 := n10895 _v _q h6792
  simp only [e2139, e2805, e6486, e6792, e10898] at *
  tauto
theorem n12548 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e6636 _v) := by
  have p10892 := n10892 _v _q 
  have p12547 := n12547 _v _q h6792
  simp only [e2139, e2482, e6486, e6636, e10891] at *
  tauto
theorem n12550 (_v : Vars) (_q : Query _v)  : (e12549 _v) := by
  have p4023 := n4023 _v _q 
  have p10901 := n10901 _v _q 
  exact (Iff.trans p4023 p10901)
theorem n12552 (_v : Vars) (_q : Query _v)  : (e12551 _v) := by
  simp only [e43, e760, e761, e2681, e2904, e4033, e4034, e7513, e12551] at *
  omega
theorem n12554 (_v : Vars) (_q : Query _v)  : (e12553 _v) := by
  have p7516 := n7516 _v _q 
  have p10903 := n10903 _v _q 
  exact (Iff.trans p7516 p10903)
theorem n12556 (_v : Vars) (_q : Query _v)  : (e12555 _v) := by
  have p12552 := n12552 _v _q 
  have p12554 := n12554 _v _q 
  exact (Iff.trans p12552 p12554)
theorem n12558 (_v : Vars) (_q : Query _v)  : (e12557 _v) := by
  have p4041 := n4041 _v _q 
  have p10910 := n10910 _v _q 
  exact (Iff.trans p4041 p10910)
theorem n12560 (_v : Vars) (_q : Query _v)  : (e12559 _v) := by
  simp only [e266, e781, e782, e2741, e2910, e4051, e4052, e7540, e12559] at *
  omega
theorem n12562 (_v : Vars) (_q : Query _v)  : (e12561 _v) := by
  have p7543 := n7543 _v _q 
  have p10912 := n10912 _v _q 
  exact (Iff.trans p7543 p10912)
theorem n12564 (_v : Vars) (_q : Query _v)  : (e12563 _v) := by
  have p12560 := n12560 _v _q 
  have p12562 := n12562 _v _q 
  exact (Iff.trans p12560 p12562)
theorem n12566 (_v : Vars) (_q : Query _v)  : (e12565 _v) := by
  have p4073 := n4073 _v _q 
  have p10923 := n10923 _v _q 
  exact (Iff.trans p4073 p10923)
theorem n12568 (_v : Vars) (_q : Query _v)  : (e12567 _v) := by
  have p4083 := n4083 _v _q 
  have p10927 := n10927 _v _q 
  exact (Iff.trans p4083 p10927)
theorem n12570 (_v : Vars) (_q : Query _v)  : (e12569 _v) := by
  simp only [e266, e781, e782, e2593, e2901, e4093, e4094, e7583, e12569] at *
  omega
theorem n12572 (_v : Vars) (_q : Query _v)  : (e12571 _v) := by
  have p7586 := n7586 _v _q 
  have p10929 := n10929 _v _q 
  exact (Iff.trans p7586 p10929)
theorem n12574 (_v : Vars) (_q : Query _v)  : (e12573 _v) := by
  have p12570 := n12570 _v _q 
  have p12572 := n12572 _v _q 
  exact (Iff.trans p12570 p12572)
theorem n12576 (_v : Vars) (_q : Query _v)  : (e12575 _v) := by
  have p4115 := n4115 _v _q 
  have p10940 := n10940 _v _q 
  exact (Iff.trans p4115 p10940)
theorem n12577 (_v : Vars) (_q : Query _v) (h2585 : (e2585 _v)) (h6636 : (e6636 _v)) : (e7489 _v) := by
  have p11031 := n11031 _v _q h6636
  have p8532 := n8532 _v _q h2585
  have p10893 := n10893 _v _q 
  have p8663 := n8663 _v _q 
  have p5257 := n5257 _v _q 
  exact FloorCertificate.node_12577 (e2 _v) (e7 _v) (e17 _v) (e45 _v) (e110 _v) p11031 p8532 p10893 p8663 p5257
theorem n12579 (_v : Vars) (_q : Query _v)  : (e12578 _v) := by
  by_contra hc
  change ¬ ((e2482 _v) ∨ (¬ (e2585 _v))) at hc
  have h2585 : (e2585 _v) := by
    tauto
  have h6636 : (e6636 _v) := by
    change (¬ (e2482 _v))
    tauto
  have p12577 := n12577 _v _q h2585 h6636
  exact p12577
theorem n12581 (_v : Vars) (_q : Query _v)  : (e12580 _v) := by
  have p4125 := n4125 _v _q 
  have p10948 := n10948 _v _q 
  exact (Iff.trans p4125 p10948)
theorem n12583 (_v : Vars) (_q : Query _v)  : (e12582 _v) := by
  simp only [e43, e760, e761, e2728, e2908, e4135, e4136, e7626, e12582] at *
  omega
theorem n12585 (_v : Vars) (_q : Query _v)  : (e12584 _v) := by
  have p7629 := n7629 _v _q 
  have p10950 := n10950 _v _q 
  exact (Iff.trans p7629 p10950)
theorem n12587 (_v : Vars) (_q : Query _v)  : (e12586 _v) := by
  have p12583 := n12583 _v _q 
  have p12585 := n12585 _v _q 
  exact (Iff.trans p12583 p12585)
theorem n12589 (_v : Vars) (_q : Query _v)  : (e12588 _v) := by
  have p4148 := n4148 _v _q 
  have p10957 := n10957 _v _q 
  exact (Iff.trans p4148 p10957)
theorem n12591 (_v : Vars) (_q : Query _v)  : (e12590 _v) := by
  simp only [e5, e6, e36, e2346, e2878, e4152, e4153, e7651, e12590] at *
  omega
theorem n12593 (_v : Vars) (_q : Query _v)  : (e12592 _v) := by
  have p7654 := n7654 _v _q 
  have p10959 := n10959 _v _q 
  exact (Iff.trans p7654 p10959)
theorem n12595 (_v : Vars) (_q : Query _v)  : (e12594 _v) := by
  have p12591 := n12591 _v _q 
  have p12593 := n12593 _v _q 
  exact (Iff.trans p12591 p12593)
end
end Assembly
