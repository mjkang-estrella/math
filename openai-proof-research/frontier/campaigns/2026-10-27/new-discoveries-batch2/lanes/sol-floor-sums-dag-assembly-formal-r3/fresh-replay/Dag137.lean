import Dag136
import generated.th_lemma_11
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n15823 (_v : Vars) (_q : Query _v) (h6636 : (e6636 _v)) : (e4096 _v) := by
  have p15703 := n15703 _v _q 
  have p15822 := n15822 _v _q h6636
  simp only [e4096, e4097, e4098, e4099, e7589, e7590, e7597] at *
  tauto
theorem n15824 (_v : Vars) (_q : Query _v)  : (e7782 _v) := by
  simp only [e4258, e4259, e4260, e4261, e7781, e7782] at *
  tauto
theorem n15825 (_v : Vars) (_q : Query _v) (h6636 : (e6636 _v)) : (e7789 _v) := by
  have p14570 := n14570 _v _q 
  have p12910 := n12910 _v _q h6636
  simp only [e2781, e4258, e4259, e4260, e4261, e6776, e7781, e7789, e7792] at *
  tauto
theorem n15826 (_v : Vars) (_q : Query _v) (h6636 : (e6636 _v)) : (e4260 _v) := by
  have p15824 := n15824 _v _q 
  have p15825 := n15825 _v _q h6636
  simp only [e4258, e4259, e4260, e4261, e7781, e7782, e7789] at *
  tauto
theorem n15827 (_v : Vars) (_q : Query _v) (h6636 : (e6636 _v)) : (e6454 _v) := by
  have p11031 := n11031 _v _q h6636
  have p5257 := n5257 _v _q 
  have p10893 := n10893 _v _q 
  exact FloorCertificate.node_15827 (e2 _v) (e7 _v) (e17 _v) (e45 _v) (e110 _v) p11031 p5257 p10893
theorem n15828 (_v : Vars) (_q : Query _v) (h6636 : (e6636 _v)) : (e7955 _v) := by
  have p14601 := n14601 _v _q 
  have p15827 := n15827 _v _q h6636
  simp only [e2061, e4434, e4435, e4436, e4437, e6454, e7947, e7955, e7958] at *
  tauto
theorem n15829 (_v : Vars) (_q : Query _v) (h6636 : (e6636 _v)) : (e5108 _v) := by
  have p5257 := n5257 _v _q 
  have p5255 := n5255 _v _q 
  have p10893 := n10893 _v _q 
  have p11031 := n11031 _v _q h6636
  have p8663 := n8663 _v _q 
  exact FloorCertificate.node_15829 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p5257 p5255 p10893 p11031 p8663
theorem n15830 (_v : Vars) (_q : Query _v) (h6636 : (e6636 _v)) : (e5119 _v) := by
  have p14487 := n14487 _v _q 
  have p15829 := n15829 _v _q h6636
  simp only [e48, e70, e72, e75, e76, e5108, e5118, e5119, e5122] at *
  tauto
theorem n15831 (_v : Vars) (_q : Query _v) (h6636 : (e6636 _v)) : (e6549 _v) := by
  have p10893 := n10893 _v _q 
  have p8663 := n8663 _v _q 
  have p5257 := n5257 _v _q 
  have p5255 := n5255 _v _q 
  have p11031 := n11031 _v _q h6636
  exact FloorCertificate.node_15831 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p10893 p8663 p5257 p5255 p11031
theorem n15832 (_v : Vars) (_q : Query _v) (h6636 : (e6636 _v)) : (e6879 _v) := by
  have p14643 := n14643 _v _q 
  have p15831 := n15831 _v _q h6636
  simp only [e2296, e3150, e3152, e3155, e3156, e6549, e6878, e6879, e6882] at *
  tauto
theorem n15833 (_v : Vars) (_q : Query _v) (h6636 : (e6636 _v)) : (e6501 _v) := by
  have p10893 := n10893 _v _q 
  have p5257 := n5257 _v _q 
  have p11031 := n11031 _v _q h6636
  have p5255 := n5255 _v _q 
  exact FloorCertificate.node_15833 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p10893 p5257 p11031 p5255
theorem n15834 (_v : Vars) (_q : Query _v) (h6636 : (e6636 _v)) : (e8103 _v) := by
  have p14626 := n14626 _v _q 
  have p15833 := n15833 _v _q h6636
  simp only [e2179, e4608, e4609, e4610, e4611, e6501, e8095, e8103, e8106] at *
  tauto
theorem n15835 (_v : Vars) (_q : Query _v) (h6636 : (e6636 _v)) : (e6575 _v) := by
  have p8663 := n8663 _v _q 
  have p5255 := n5255 _v _q 
  have p10893 := n10893 _v _q 
  have p11031 := n11031 _v _q h6636
  have p5257 := n5257 _v _q 
  exact FloorCertificate.node_15835 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8663 p5255 p10893 p11031 p5257
theorem n15836 (_v : Vars) (_q : Query _v) (h6636 : (e6636 _v)) : (e7668 _v) := by
  have p14544 := n14544 _v _q 
  have p15835 := n15835 _v _q h6636
  simp only [e2351, e4156, e4157, e4158, e4159, e6575, e7660, e7668, e7671] at *
  tauto
theorem n15837 (_v : Vars) (_q : Query _v) (h6636 : (e6636 _v)) : (e6525 _v) := by
  have p10893 := n10893 _v _q 
  have p5257 := n5257 _v _q 
  have p5255 := n5255 _v _q 
  have p11031 := n11031 _v _q h6636
  have p8663 := n8663 _v _q 
  exact FloorCertificate.node_15837 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p10893 p5257 p5255 p11031 p8663
theorem n15838 (_v : Vars) (_q : Query _v) (h6636 : (e6636 _v)) : (e8174 _v) := by
  have p14634 := n14634 _v _q 
  have p15837 := n15837 _v _q h6636
  simp only [e2242, e4673, e4674, e4675, e4676, e6525, e8166, e8174, e8177] at *
  tauto
theorem n15839 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e2125 _v) := by
  have p5257 := n5257 _v _q 
  have p5255 := n5255 _v _q 
  have p11374 := n11374 _v _q h251
  have p5391 := n5391 _v _q 
  exact FloorCertificate.node_15839 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p5257 p5255 p11374 p5391
theorem n15840 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e4466 _v) := by
  have p14604 := n14604 _v _q 
  have p15839 := n15839 _v _q h251
  simp only [e2125, e4458, e4459, e4463, e4464, e4465, e4466, e6480, e7977] at *
  tauto
theorem n15841 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e4459 _v) := by
  have p8443 := n8443 _v _q 
  have p15840 := n15840 _v _q h251
  simp only [e4458, e4459, e4463, e4464, e4465, e4466, e4482] at *
  tauto
theorem n15842 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e2522 _v) := by
  have p5255 := n5255 _v _q 
  have p11374 := n11374 _v _q h251
  exact FloorCertificate.node_15842 (e2 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p5255 p11374
theorem n15843 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e4824 _v) := by
  have p14705 := n14705 _v _q 
  have p15842 := n15842 _v _q h251
  simp only [e2522, e4816, e4817, e4821, e4822, e4823, e4824, e6650, e8298] at *
  tauto
theorem n15844 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e4817 _v) := by
  have p15123 := n15123 _v _q 
  have p15843 := n15843 _v _q h251
  simp only [e4816, e4817, e4821, e4822, e4823, e4824, e4965] at *
  tauto
theorem n15845 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e2468 _v) := by
  have p5257 := n5257 _v _q 
  have p5255 := n5255 _v _q 
  have p11374 := n11374 _v _q h251
  exact FloorCertificate.node_15845 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p5257 p5255 p11374
theorem n15846 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e4798 _v) := by
  have p14690 := n14690 _v _q 
  have p15845 := n15845 _v _q h251
  simp only [e2468, e4790, e4791, e4795, e4796, e4797, e4798, e6630, e8281] at *
  tauto
theorem n15847 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e4791 _v) := by
  have p14932 := n14932 _v _q 
  have p15846 := n15846 _v _q h251
  simp only [e4790, e4791, e4795, e4796, e4797, e4798, e4953] at *
  tauto
theorem n15848 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e4466 _v) := by
  have p14604 := n14604 _v _q 
  have p12911 := n12911 _v _q h251
  simp only [e2125, e4458, e4459, e4463, e4464, e4465, e4466, e6480, e7977] at *
  tauto
theorem n15849 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e4314 _v) := by
  have p14704 := n14704 _v _q 
  have p12912 := n12912 _v _q h251
  simp only [e2585, e4306, e4307, e4311, e4312, e4313, e4314, e6676, e7836] at *
  tauto
theorem n15850 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e4306 _v) := by
  have p14984 := n14984 _v _q 
  have p15849 := n15849 _v _q h251
  simp only [e4306, e4307, e4311, e4312, e4313, e4314, e4964] at *
  tauto
theorem n15851 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e2364 _v) := by
  have p11343 := n11343 _v _q 
  have p12912 := n12912 _v _q h251
  simp only [e2364, e2585, e6676, e11342] at *
  tauto
theorem n15852 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e4661 _v) := by
  have p14686 := n14686 _v _q 
  have p15851 := n15851 _v _q h251
  simp only [e2364, e4653, e4654, e4658, e4659, e4660, e4661, e6583, e8163] at *
  tauto
theorem n15853 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e4653 _v) := by
  have p15168 := n15168 _v _q 
  have p15852 := n15852 _v _q h251
  simp only [e4653, e4654, e4658, e4659, e4660, e4661, e4939] at *
  tauto
theorem n15854 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e2296 _v) := by
  have p5255 := n5255 _v _q 
  have p11374 := n11374 _v _q h251
  have p5391 := n5391 _v _q 
  exact FloorCertificate.node_15854 (e2 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p5255 p11374 p5391
theorem n15855 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e3140 _v) := by
  have p14358 := n14358 _v _q 
  have p15854 := n15854 _v _q h251
  simp only [e2296, e3132, e3133, e3137, e3138, e3139, e3140, e6549, e6885] at *
  tauto
theorem n15856 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e3133 _v) := by
  have p15098 := n15098 _v _q 
  have p15855 := n15855 _v _q h251
  simp only [e3132, e3133, e3137, e3138, e3139, e3140, e3157] at *
  tauto
theorem n15857 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e1995 _v) := by
  have p11516 := n11516 _v _q 
  have p11374 := n11374 _v _q h251
  simp only [e251, e1995, e6694, e11515] at *
  tauto
theorem n15858 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e4575 _v) := by
  have p14696 := n14696 _v _q 
  have p15857 := n15857 _v _q h251
  simp only [e1995, e4567, e4568, e4572, e4573, e4574, e4575, e6423, e8066] at *
  tauto
theorem n15859 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e4567 _v) := by
  have p8485 := n8485 _v _q 
  have p15858 := n15858 _v _q h251
  simp only [e4567, e4568, e4572, e4573, e4574, e4575, e4956] at *
  tauto
theorem n15860 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e2468 _v) := by
  have p11374 := n11374 _v _q h251
  have p5257 := n5257 _v _q 
  have p5255 := n5255 _v _q 
  exact FloorCertificate.node_15860 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p11374 p5257 p5255
theorem n15861 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e4798 _v) := by
  have p14690 := n14690 _v _q 
  have p15860 := n15860 _v _q h251
  simp only [e2468, e4790, e4791, e4795, e4796, e4797, e4798, e6630, e8281] at *
  tauto
theorem n15862 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e4791 _v) := by
  have p14932 := n14932 _v _q 
  have p15861 := n15861 _v _q h251
  simp only [e4790, e4791, e4795, e4796, e4797, e4798, e4953] at *
  tauto
theorem n15863 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e2242 _v) := by
  have p5257 := n5257 _v _q 
  have p5391 := n5391 _v _q 
  have p5255 := n5255 _v _q 
  have p11374 := n11374 _v _q h251
  exact FloorCertificate.node_15863 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p5257 p5391 p5255 p11374
theorem n15864 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e4686 _v) := by
  have p14708 := n14708 _v _q 
  have p15863 := n15863 _v _q h251
  simp only [e2242, e4678, e4679, e4683, e4684, e4685, e4686, e6525, e8180] at *
  tauto
theorem n15865 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e2522 _v) := by
  have p11374 := n11374 _v _q h251
  have p5255 := n5255 _v _q 
  exact FloorCertificate.node_15865 (e2 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p11374 p5255
theorem n15866 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e4824 _v) := by
  have p14705 := n14705 _v _q 
  have p15865 := n15865 _v _q h251
  simp only [e2522, e4816, e4817, e4821, e4822, e4823, e4824, e6650, e8298] at *
  tauto
theorem n15867 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e4817 _v) := by
  have p15123 := n15123 _v _q 
  have p15866 := n15866 _v _q h251
  simp only [e4816, e4817, e4821, e4822, e4823, e4824, e4965] at *
  tauto
end
end Assembly
