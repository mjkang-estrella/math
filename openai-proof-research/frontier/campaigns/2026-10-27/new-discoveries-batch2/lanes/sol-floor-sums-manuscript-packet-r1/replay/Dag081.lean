import Dag080
import generated.th_lemma_3
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n12684 (_v : Vars) (_q : Query _v)  : (e12683 _v) := by
  have p4453 := n4453 _v _q 
  have p11121 := n11121 _v _q 
  exact (Iff.trans p4453 p11121)
theorem n12686 (_v : Vars) (_q : Query _v)  : (e12685 _v) := by
  have p4472 := n4472 _v _q 
  have p11129 := n11129 _v _q 
  exact (Iff.trans p4472 p11129)
theorem n12687 (_v : Vars) (_q : Query _v) (h5195 : (e5195 _v)) (h6656 : (e6656 _v)) : (e7489 _v) := by
  have p4016 := n4016 _v _q 
  have p8663 := n8663 _v _q 
  have p11499 := n11499 _v _q h6656
  have p8549 := n8549 _v _q h5195
  exact FloorCertificate.node_12687 (e2 _v) (e7 _v) (e17 _v) (e45 _v) (e110 _v) p4016 p8663 p11499 p8549
theorem n12689 (_v : Vars) (_q : Query _v)  : (e12688 _v) := by
  by_contra hc
  change ¬ ((e2536 _v) ∨ (e196 _v)) at hc
  have h5195 : (e5195 _v) := by
    change (¬ (e196 _v))
    tauto
  have h6656 : (e6656 _v) := by
    change (¬ (e2536 _v))
    tauto
  have p12687 := n12687 _v _q h5195 h6656
  exact p12687
theorem n12691 (_v : Vars) (_q : Query _v)  : (e12690 _v) := by
  have p4505 := n4505 _v _q 
  have p11141 := n11141 _v _q 
  exact (Iff.trans p4505 p11141)
theorem n12692 (_v : Vars) (_q : Query _v)  : (e4517 _v) := by
  have p4519 := n4519 _v _q 
  change ((e4512 _v) = (e4512 _v)) at p4519
  simp only [e4517, e4515]
theorem n12693 (_v : Vars) (_q : Query _v)  : (e4515 _v) := by
  have p11145 := n11145 _v _q 
  have p12692 := n12692 _v _q 
  simp only [e4515, e4517] at *
  tauto
theorem n12695 (_v : Vars) (_q : Query _v)  : (e12694 _v) := by
  have p4529 := n4529 _v _q 
  have p11147 := n11147 _v _q 
  exact (Iff.trans p4529 p11147)
theorem n12697 (_v : Vars) (_q : Query _v)  : (e12696 _v) := by
  simp only [e108, e802, e803, e2800, e2916, e4539, e4540, e8023, e12696] at *
  omega
theorem n12699 (_v : Vars) (_q : Query _v)  : (e12698 _v) := by
  have p8026 := n8026 _v _q 
  have p11149 := n11149 _v _q 
  exact (Iff.trans p8026 p11149)
theorem n12701 (_v : Vars) (_q : Query _v)  : (e12700 _v) := by
  have p12697 := n12697 _v _q 
  have p12699 := n12699 _v _q 
  exact (Iff.trans p12697 p12699)
theorem n12703 (_v : Vars) (_q : Query _v)  : (e12702 _v) := by
  have p4553 := n4553 _v _q 
  have p11156 := n11156 _v _q 
  exact (Iff.trans p4553 p11156)
theorem n12704 (_v : Vars) (_q : Query _v)  : (e8042 _v) := by
  simp only [e5, e6, e36, e2462, e4557, e4558, e4559, e6628, e8042] at *
  omega
theorem n12706 (_v : Vars) (_q : Query _v)  : (e12705 _v) := by
  have p11161 := n11161 _v _q 
  have p11163 := n11163 _v _q 
  exact (Iff.trans p11161 p11163)
theorem n12707 (_v : Vars) (_q : Query _v)  : (e11164 _v) := by
  have p12704 := n12704 _v _q 
  have p12706 := n12706 _v _q 
  exact (Iff.trans p12704 p12706)
theorem n12709 (_v : Vars) (_q : Query _v)  : (e12708 _v) := by
  have p12707 := n12707 _v _q 
  change ((e6628 _v) ↔ (e8050 _v)) at p12707
  simp only [e12708, e6629, e11165, p12707]
theorem n12713 (_v : Vars) (_q : Query _v)  : (e12712 _v) := by
  have p4581 := n4581 _v _q 
  have p11175 := n11175 _v _q 
  exact (Iff.trans p4581 p11175)
theorem n12715 (_v : Vars) (_q : Query _v)  : (e12714 _v) := by
  have p4594 := n4594 _v _q 
  have p11179 := n11179 _v _q 
  exact (Iff.trans p4594 p11179)
theorem n12716 (_v : Vars) (_q : Query _v)  : (e8085 _v) := by
  simp only [e5, e6, e36, e2173, e2864, e4604, e4605, e4606, e8085] at *
  omega
theorem n12717 (_v : Vars) (_q : Query _v)  : (e8092 _v) := by
  have p12716 := n12716 _v _q 
  have p11185 := n11185 _v _q 
  exact (Iff.trans p12716 p11185)
theorem n12719 (_v : Vars) (_q : Query _v)  : (e12718 _v) := by
  have p12717 := n12717 _v _q 
  change ((e2864 _v) ↔ (e8089 _v)) at p12717
  simp only [e12718, e2865, e8093, p12717]
theorem n12721 (_v : Vars) (_q : Query _v)  : (e12720 _v) := by
  simp only [e5, e6, e10, e12, e41, e184, e185, e4586, e4587, e4588, e8070, e8071, e8072, e8089, e8093, e12720] at *
theorem n12722 (_v : Vars) (_q : Query _v)  : (e12718 _v) := by
  have p12719 := n12719 _v _q 
  have p12721 := n12721 _v _q 
  exact (Iff.trans p12719 p12721)
theorem n12726 (_v : Vars) (_q : Query _v)  : (e12725 _v) := by
  have p4622 := n4622 _v _q 
  have p11196 := n11196 _v _q 
  exact (Iff.trans p4622 p11196)
theorem n12728 (_v : Vars) (_q : Query _v)  : (e12727 _v) := by
  have p4634 := n4634 _v _q 
  have p11200 := n11200 _v _q 
  exact (Iff.trans p4634 p11200)
theorem n12729 (_v : Vars) (_q : Query _v)  : (e8127 _v) := by
  simp only [e5, e6, e36, e2055, e2850, e4644, e4645, e4646, e8127] at *
  omega
theorem n12730 (_v : Vars) (_q : Query _v)  : (e8134 _v) := by
  have p12729 := n12729 _v _q 
  have p11206 := n11206 _v _q 
  exact (Iff.trans p12729 p11206)
theorem n12732 (_v : Vars) (_q : Query _v)  : (e12731 _v) := by
  have p12730 := n12730 _v _q 
  change ((e2850 _v) ↔ (e8131 _v)) at p12730
  simp only [e12731, e2851, e8135, p12730]
theorem n12734 (_v : Vars) (_q : Query _v)  : (e12733 _v) := by
  simp only [e5, e6, e12, e41, e111, e173, e174, e4626, e4627, e4628, e8112, e8113, e8114, e8131, e8135, e12733] at *
theorem n12735 (_v : Vars) (_q : Query _v)  : (e12731 _v) := by
  have p12732 := n12732 _v _q 
  have p12734 := n12734 _v _q 
  exact (Iff.trans p12732 p12734)
theorem n12738 (_v : Vars) (_q : Query _v) (h196 : (e196 _v)) (h496 : (e496 _v)) : (e7489 _v) := by
  have p8139 := n8139 _v _q 
  have p11215 := n11215 _v _q 
  have p8143 := n8143 _v _q h196
  have p8147 := n8147 _v _q h496
  have p11482 := n11482 _v _q 
  exact FloorCertificate.node_12738 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8139 p11215 p8143 p8147 p11482
theorem n12740 (_v : Vars) (_q : Query _v)  : (e12739 _v) := by
  have p4667 := n4667 _v _q 
  have p11221 := n11221 _v _q 
  exact (Iff.trans p4667 p11221)
theorem n12742 (_v : Vars) (_q : Query _v)  : (e12741 _v) := by
  have p4692 := n4692 _v _q 
  have p11229 := n11229 _v _q 
  exact (Iff.trans p4692 p11229)
theorem n12744 (_v : Vars) (_q : Query _v)  : (e12743 _v) := by
  have p4703 := n4703 _v _q 
  have p11233 := n11233 _v _q 
  exact (Iff.trans p4703 p11233)
theorem n12745 (_v : Vars) (_q : Query _v)  : (e8201 _v) := by
  simp only [e43, e760, e761, e2248, e4713, e4714, e4715, e6529, e8201] at *
  omega
theorem n12747 (_v : Vars) (_q : Query _v)  : (e12746 _v) := by
  have p11238 := n11238 _v _q 
  have p11240 := n11240 _v _q 
  exact (Iff.trans p11238 p11240)
theorem n12748 (_v : Vars) (_q : Query _v)  : (e11241 _v) := by
  have p12745 := n12745 _v _q 
  have p12747 := n12747 _v _q 
  exact (Iff.trans p12745 p12747)
theorem n12750 (_v : Vars) (_q : Query _v)  : (e12749 _v) := by
  have p12748 := n12748 _v _q 
  change ((e6529 _v) ↔ (e8204 _v)) at p12748
  simp only [e12749, e6530, e11242, p12748]
theorem n12754 (_v : Vars) (_q : Query _v)  : (e12753 _v) := by
  have p4737 := n4737 _v _q 
  have p11252 := n11252 _v _q 
  exact (Iff.trans p4737 p11252)
theorem n12756 (_v : Vars) (_q : Query _v)  : (e12755 _v) := by
  have p4761 := n4761 _v _q 
  have p11260 := n11260 _v _q 
  exact (Iff.trans p4761 p11260)
theorem n12758 (_v : Vars) (_q : Query _v)  : (e12757 _v) := by
  have p4771 := n4771 _v _q 
  have p11264 := n11264 _v _q 
  exact (Iff.trans p4771 p11264)
theorem n12760 (_v : Vars) (_q : Query _v)  : (e12759 _v) := by
  simp only [e266, e781, e782, e2372, e2882, e4781, e4782, e8261, e12759] at *
  omega
theorem n12762 (_v : Vars) (_q : Query _v)  : (e12761 _v) := by
  have p8264 := n8264 _v _q 
  have p11266 := n11266 _v _q 
  exact (Iff.trans p8264 p11266)
theorem n12764 (_v : Vars) (_q : Query _v)  : (e12763 _v) := by
  have p12760 := n12760 _v _q 
  have p12762 := n12762 _v _q 
  exact (Iff.trans p12760 p12762)
theorem n12766 (_v : Vars) (_q : Query _v)  : (e12765 _v) := by
  have p4804 := n4804 _v _q 
  have p11277 := n11277 _v _q 
  exact (Iff.trans p4804 p11277)
end
end Assembly
