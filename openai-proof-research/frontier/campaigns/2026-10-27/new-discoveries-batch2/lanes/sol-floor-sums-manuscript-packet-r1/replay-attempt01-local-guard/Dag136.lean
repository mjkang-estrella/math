import Dag135
import generated.th_lemma_10
import generated.th_lemma_11
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n15778 (_v : Vars) (_q : Query _v) (h6549 : (e6549 _v)) : (e3152 _v) := by
  have p15776 := n15776 _v _q 
  have p15777 := n15777 _v _q h6549
  simp only [e3150, e3152, e3155, e3156, e6878, e6879, e8223] at *
  tauto
theorem n15779 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) : (e8310 _v) := by
  have p4016 := n4016 _v _q 
  have p7488 := n7488 _v _q h5362
  have p4951 := n4951 _v _q 
  exact FloorCertificate.node_15779 (e2 _v) (e7 _v) (e9 _v) (e45 _v) (e110 _v) p4016 p7488 p4951
theorem n15780 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) : (e8322 _v) := by
  have p15218 := n15218 _v _q 
  have p15779 := n15779 _v _q h5362
  simp only [e2529, e8310, e8315, e8317, e8319, e8320, e8321, e8322, e11298] at *
  tauto
theorem n15781 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) : (e2296 _v) := by
  have p8547 := n8547 _v _q 
  have p8464 := n8464 _v _q h2351
  simp only [e2296, e2351, e6575, e8546] at *
  tauto
theorem n15782 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) : (e3140 _v) := by
  have p14358 := n14358 _v _q 
  have p15781 := n15781 _v _q h2351
  simp only [e2296, e3132, e3133, e3137, e3138, e3139, e3140, e6549, e6885] at *
  tauto
theorem n15783 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) : (e3133 _v) := by
  have p15098 := n15098 _v _q 
  have p15782 := n15782 _v _q h2351
  simp only [e3132, e3133, e3137, e3138, e3139, e3140, e3157] at *
  tauto
theorem n15784 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) : (e2061 _v) := by
  have p12904 := n12904 _v _q 
  have p8464 := n8464 _v _q h2351
  simp only [e2061, e2351, e6575, e12903] at *
  tauto
theorem n15785 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) : (e4447 _v) := by
  have p14688 := n14688 _v _q 
  have p15784 := n15784 _v _q h2351
  simp only [e2061, e4439, e4440, e4444, e4445, e4446, e4447, e6454, e7961] at *
  tauto
theorem n15786 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) : (e4439 _v) := by
  have p14925 := n14925 _v _q 
  have p15785 := n15785 _v _q h2351
  simp only [e4439, e4440, e4444, e4445, e4446, e4447, e4941] at *
  tauto
theorem n15787 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) : (e1995 _v) := by
  have p11412 := n11412 _v _q 
  have p15784 := n15784 _v _q h2351
  simp only [e1995, e2061, e6454, e11411] at *
  tauto
theorem n15788 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) : (e4575 _v) := by
  have p14696 := n14696 _v _q 
  have p15787 := n15787 _v _q h2351
  simp only [e1995, e4567, e4568, e4572, e4573, e4574, e4575, e6423, e8066] at *
  tauto
theorem n15789 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) : (e2179 _v) := by
  have p11513 := n11513 _v _q 
  have p8464 := n8464 _v _q h2351
  simp only [e2179, e2351, e6575, e11512] at *
  tauto
theorem n15790 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) : (e4616 _v) := by
  have p14684 := n14684 _v _q 
  have p15789 := n15789 _v _q h2351
  simp only [e2179, e3158, e3159, e3160, e3161, e3162, e4616, e6501, e8109] at *
  tauto
theorem n15791 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) : (e3158 _v) := by
  have p15126 := n15126 _v _q 
  have p15790 := n15790 _v _q h2351
  simp only [e3158, e3159, e3160, e3161, e3162, e3163, e4616] at *
  tauto
theorem n15792 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) : (e4169 _v) := by
  have p14695 := n14695 _v _q 
  have p8464 := n8464 _v _q h2351
  simp only [e2351, e4161, e4162, e4166, e4167, e4168, e4169, e6575, e7674] at *
  tauto
theorem n15793 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) : (e4161 _v) := by
  have p14945 := n14945 _v _q 
  have p15792 := n15792 _v _q h2351
  simp only [e4161, e4162, e4166, e4167, e4168, e4169, e4955] at *
  tauto
theorem n15794 (_v : Vars) (_q : Query _v) (h2402 : (e2402 _v)) : (e2179 _v) := by
  have p11339 := n11339 _v _q 
  have p8591 := n8591 _v _q h2402
  simp only [e2179, e2402, e6600, e11338] at *
  tauto
theorem n15795 (_v : Vars) (_q : Query _v) (h2402 : (e2402 _v)) : (e4616 _v) := by
  have p14684 := n14684 _v _q 
  have p15794 := n15794 _v _q h2402
  simp only [e2179, e3158, e3159, e3160, e3161, e3162, e4616, e6501, e8109] at *
  tauto
theorem n15796 (_v : Vars) (_q : Query _v) (h2402 : (e2402 _v)) : (e3158 _v) := by
  have p15126 := n15126 _v _q 
  have p15795 := n15795 _v _q h2402
  simp only [e3158, e3159, e3160, e3161, e3162, e3163, e4616] at *
  tauto
theorem n15797 (_v : Vars) (_q : Query _v) (h496 : (e496 _v)) : (e251 _v) := by
  have p4016 := n4016 _v _q 
  have p8144 := n8144 _v _q h496
  exact FloorCertificate.node_15797 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) p4016 p8144
theorem n15798 (_v : Vars) (_q : Query _v) (h496 : (e496 _v)) : (e4380 _v) := by
  have p14685 := n14685 _v _q 
  have p15797 := n15797 _v _q h496
  simp only [e251, e4372, e4373, e4377, e4378, e4379, e4380, e6694, e7901] at *
  tauto
theorem n15799 (_v : Vars) (_q : Query _v) (h496 : (e496 _v)) : (e4373 _v) := by
  have p15117 := n15117 _v _q 
  have p15798 := n15798 _v _q h496
  simp only [e4372, e4373, e4377, e4378, e4379, e4380, e4938] at *
  tauto
theorem n15800 (_v : Vars) (_q : Query _v) (h496 : (e496 _v)) : (e7754 _v) := by
  have p14942 := n14942 _v _q 
  have p14724 := n14724 _v _q h496
  simp only [e2132, e7742, e7747, e7749, e7751, e7752, e7753, e7754, e11001] at *
  tauto
theorem n15801 (_v : Vars) (_q : Query _v) (h496 : (e496 _v)) : (e7749 _v) := by
  have p14941 := n14941 _v _q 
  have p15800 := n15800 _v _q h496
  simp only [e7747, e7749, e7751, e7752, e7753, e7754, e8446] at *
  tauto
theorem n15802 (_v : Vars) (_q : Query _v) (h496 : (e496 _v)) : (e4661 _v) := by
  have p14686 := n14686 _v _q 
  have p14725 := n14725 _v _q h496
  simp only [e2364, e4653, e4654, e4658, e4659, e4660, e4661, e6583, e8163] at *
  tauto
theorem n15803 (_v : Vars) (_q : Query _v) (h496 : (e496 _v)) : (e2296 _v) := by
  have p4016 := n4016 _v _q 
  have p5255 := n5255 _v _q 
  have p5391 := n5391 _v _q 
  have p8144 := n8144 _v _q h496
  exact FloorCertificate.node_15803 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p4016 p5255 p5391 p8144
theorem n15804 (_v : Vars) (_q : Query _v) (h496 : (e496 _v)) : (e3140 _v) := by
  have p14358 := n14358 _v _q 
  have p15803 := n15803 _v _q h496
  simp only [e2296, e3132, e3133, e3137, e3138, e3139, e3140, e6549, e6885] at *
  tauto
theorem n15805 (_v : Vars) (_q : Query _v) (h496 : (e496 _v)) : (e3133 _v) := by
  have p15098 := n15098 _v _q 
  have p15804 := n15804 _v _q h496
  simp only [e3132, e3133, e3137, e3138, e3139, e3140, e3157] at *
  tauto
theorem n15806 (_v : Vars) (_q : Query _v) (h496 : (e496 _v)) : (e2536 _v) := by
  have p12689 := n12689 _v _q 
  have p14137 := n14137 _v _q h496
  simp only [e196, e2536, e5195, e12688] at *
  tauto
theorem n15807 (_v : Vars) (_q : Query _v) (h496 : (e496 _v)) : (e2482 _v) := by
  have p11135 := n11135 _v _q 
  have p15806 := n15806 _v _q h496
  simp only [e2482, e2536, e6656, e11134] at *
  tauto
theorem n15808 (_v : Vars) (_q : Query _v) (h496 : (e496 _v)) : (e4405 _v) := by
  have p14702 := n14702 _v _q 
  have p15807 := n15807 _v _q h496
  simp only [e2482, e4397, e4398, e4402, e4403, e4404, e4405, e6636, e7918] at *
  tauto
theorem n15809 (_v : Vars) (_q : Query _v) (h496 : (e496 _v)) : (e4398 _v) := by
  have p14976 := n14976 _v _q 
  have p15808 := n15808 _v _q h496
  simp only [e4397, e4398, e4402, e4403, e4404, e4405, e4962] at *
  tauto
theorem n15810 (_v : Vars) (_q : Query _v) (h496 : (e496 _v)) : (e2522 _v) := by
  have p8144 := n8144 _v _q h496
  have p4016 := n4016 _v _q 
  have p5255 := n5255 _v _q 
  exact FloorCertificate.node_15810 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8144 p4016 p5255
theorem n15811 (_v : Vars) (_q : Query _v) (h496 : (e496 _v)) : (e4824 _v) := by
  have p14705 := n14705 _v _q 
  have p15810 := n15810 _v _q h496
  simp only [e2522, e4816, e4817, e4821, e4822, e4823, e4824, e6650, e8298] at *
  tauto
theorem n15812 (_v : Vars) (_q : Query _v) (h496 : (e496 _v)) : (e4817 _v) := by
  have p15123 := n15123 _v _q 
  have p15811 := n15811 _v _q h496
  simp only [e4816, e4817, e4821, e4822, e4823, e4824, e4965] at *
  tauto
theorem n15813 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e2781 _v) := by
  have p5255 := n5255 _v _q 
  have p258 := n258 _v _q 
  have p5257 := n5257 _v _q 
  have p11374 := n11374 _v _q h251
  have p5391 := n5391 _v _q 
  exact FloorCertificate.node_15813 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p5255 p258 p5257 p11374 p5391
theorem n15814 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e4271 _v) := by
  have p14699 := n14699 _v _q 
  have p15813 := n15813 _v _q h251
  simp only [e2781, e4263, e4264, e4268, e4269, e4270, e4271, e6776, e7795] at *
  tauto
theorem n15815 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e4264 _v) := by
  have p14966 := n14966 _v _q 
  have p15814 := n15814 _v _q h251
  simp only [e4263, e4264, e4268, e4269, e4270, e4271, e4959] at *
  tauto
theorem n15816 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e2296 _v) := by
  have p5391 := n5391 _v _q 
  have p5255 := n5255 _v _q 
  have p11374 := n11374 _v _q h251
  exact FloorCertificate.node_15816 (e2 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p5391 p5255 p11374
theorem n15817 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e3140 _v) := by
  have p14358 := n14358 _v _q 
  have p15816 := n15816 _v _q h251
  simp only [e2296, e3132, e3133, e3137, e3138, e3139, e3140, e6549, e6885] at *
  tauto
theorem n15818 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e3133 _v) := by
  have p15098 := n15098 _v _q 
  have p15817 := n15817 _v _q h251
  simp only [e3132, e3133, e3137, e3138, e3139, e3140, e3157] at *
  tauto
theorem n15819 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e2242 _v) := by
  have p5257 := n5257 _v _q 
  have p11374 := n11374 _v _q h251
  have p5391 := n5391 _v _q 
  have p5255 := n5255 _v _q 
  exact FloorCertificate.node_15819 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p5257 p11374 p5391 p5255
theorem n15820 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e4686 _v) := by
  have p14708 := n14708 _v _q 
  have p15819 := n15819 _v _q h251
  simp only [e2242, e4678, e4679, e4683, e4684, e4685, e4686, e6525, e8180] at *
  tauto
theorem n15821 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e4679 _v) := by
  have p14989 := n14989 _v _q 
  have p15820 := n15820 _v _q h251
  simp only [e4678, e4679, e4683, e4684, e4685, e4686, e4967] at *
  tauto
theorem n15822 (_v : Vars) (_q : Query _v) (h6636 : (e6636 _v)) : (e7597 _v) := by
  have p14525 := n14525 _v _q 
  have p14139 := n14139 _v _q h6636
  simp only [e2733, e4096, e4097, e4098, e4099, e6750, e7589, e7597, e7600] at *
  tauto
end
end Assembly
