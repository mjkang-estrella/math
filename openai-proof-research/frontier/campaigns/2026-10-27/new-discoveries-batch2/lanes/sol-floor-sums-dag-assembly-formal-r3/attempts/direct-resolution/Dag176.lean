import Dag175
import generated.th_lemma_17
import generated.th_lemma_18
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n17721 (_v : Vars) (_q : Query _v) (h2722 : (e2722 _v)) : (e2402 _v) := by
  have p5257 := n5257 _v _q 
  have p5255 := n5255 _v _q 
  have p17678 := n17678 _v _q 
  have p8410 := n8410 _v _q h2722
  exact FloorCertificate.node_17721 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p5257 p5255 p17678 p8410
theorem n17722 (_v : Vars) (_q : Query _v) (h2722 : (e2722 _v)) : (e3929 _v) := by
  have p14484 := n14484 _v _q 
  have p17721 := n17721 _v _q h2722
  simp only [e2402, e3919, e3920, e3921, e3922, e3923, e3929, e6600, e7422] at *
  tauto
theorem n17723 (_v : Vars) (_q : Query _v) (h2722 : (e2722 _v)) : (e48 _v) := by
  have p17678 := n17678 _v _q 
  have p5257 := n5257 _v _q 
  have p5255 := n5255 _v _q 
  have p258 := n258 _v _q 
  have p5391 := n5391 _v _q 
  have p8410 := n8410 _v _q h2722
  exact FloorCertificate.node_17723 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p17678 p5257 p5255 p258 p5391 p8410
theorem n17724 (_v : Vars) (_q : Query _v) (h2722 : (e2722 _v)) : (e60 _v) := by
  have p14152 := n14152 _v _q 
  have p17723 := n17723 _v _q h2722
  simp only [e48, e51, e52, e57, e58, e59, e60, e5108, e5125] at *
  tauto
theorem n17725 (_v : Vars) (_q : Query _v) (h2722 : (e2722 _v)) : (e2296 _v) := by
  have p5391 := n5391 _v _q 
  have p5255 := n5255 _v _q 
  have p8410 := n8410 _v _q h2722
  have p17678 := n17678 _v _q 
  have p5257 := n5257 _v _q 
  exact FloorCertificate.node_17725 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p5391 p5255 p8410 p17678 p5257
theorem n17726 (_v : Vars) (_q : Query _v) (h2722 : (e2722 _v)) : (e3140 _v) := by
  have p14358 := n14358 _v _q 
  have p17725 := n17725 _v _q h2722
  simp only [e2296, e3132, e3133, e3137, e3138, e3139, e3140, e6549, e6885] at *
  tauto
theorem n17727 (_v : Vars) (_q : Query _v) (h2722 : (e2722 _v)) : (e2697 _v) := by
  have p5257 := n5257 _v _q 
  have p17678 := n17678 _v _q 
  have p5391 := n5391 _v _q 
  have p5255 := n5255 _v _q 
  have p258 := n258 _v _q 
  have p8410 := n8410 _v _q h2722
  exact FloorCertificate.node_17727 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p5257 p17678 p5391 p5255 p258 p8410
theorem n17728 (_v : Vars) (_q : Query _v) (h2722 : (e2722 _v)) : (e4499 _v) := by
  have p14700 := n14700 _v _q 
  have p17727 := n17727 _v _q h2722
  simp only [e2697, e4491, e4492, e4496, e4497, e4498, e4499, e6732, e7998] at *
  tauto
theorem n17729 (_v : Vars) (_q : Query _v) (h2722 : (e2722 _v)) : (e2254 _v) := by
  have p5255 := n5255 _v _q 
  have p258 := n258 _v _q 
  have p5257 := n5257 _v _q 
  have p17678 := n17678 _v _q 
  have p5391 := n5391 _v _q 
  have p8410 := n8410 _v _q h2722
  exact FloorCertificate.node_17729 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p5255 p258 p5257 p17678 p5391 p8410
theorem n17730 (_v : Vars) (_q : Query _v) (h2722 : (e2722 _v)) : (e4731 _v) := by
  have p14698 := n14698 _v _q 
  have p17729 := n17729 _v _q h2722
  simp only [e2254, e4723, e4724, e4728, e4729, e4730, e4731, e6531, e8220] at *
  tauto
theorem n17731 (_v : Vars) (_q : Query _v) (h2722 : (e2722 _v)) : (e1995 _v) := by
  have p5257 := n5257 _v _q 
  have p17678 := n17678 _v _q 
  have p5255 := n5255 _v _q 
  have p5391 := n5391 _v _q 
  have p8410 := n8410 _v _q h2722
  exact FloorCertificate.node_17731 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p5257 p17678 p5255 p5391 p8410
theorem n17732 (_v : Vars) (_q : Query _v) (h2722 : (e2722 _v)) : (e4575 _v) := by
  have p14696 := n14696 _v _q 
  have p17731 := n17731 _v _q h2722
  simp only [e1995, e4567, e4568, e4572, e4573, e4574, e4575, e6423, e8066] at *
  tauto
theorem n17733 (_v : Vars) (_q : Query _v) (h2722 : (e2722 _v)) : (e2468 _v) := by
  have p5257 := n5257 _v _q 
  have p5255 := n5255 _v _q 
  have p8410 := n8410 _v _q h2722
  have p17678 := n17678 _v _q 
  exact FloorCertificate.node_17733 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p5257 p5255 p8410 p17678
theorem n17734 (_v : Vars) (_q : Query _v) (h2722 : (e2722 _v)) : (e4798 _v) := by
  have p14690 := n14690 _v _q 
  have p17733 := n17733 _v _q h2722
  simp only [e2468, e4790, e4791, e4795, e4796, e4797, e4798, e6630, e8281] at *
  tauto
theorem n17735 (_v : Vars) (_q : Query _v) (h2722 : (e2722 _v)) : (e2482 _v) := by
  have p5255 := n5255 _v _q 
  have p5257 := n5257 _v _q 
  have p5391 := n5391 _v _q 
  have p258 := n258 _v _q 
  have p17678 := n17678 _v _q 
  have p8410 := n8410 _v _q h2722
  exact FloorCertificate.node_17735 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p5255 p5257 p5391 p258 p17678 p8410
theorem n17736 (_v : Vars) (_q : Query _v) (h2722 : (e2722 _v)) : (e4405 _v) := by
  have p14702 := n14702 _v _q 
  have p17735 := n17735 _v _q h2722
  simp only [e2482, e4397, e4398, e4402, e4403, e4404, e4405, e6636, e7918] at *
  tauto
theorem n17737 (_v : Vars) (_q : Query _v) (h2722 : (e2722 _v)) : (e2242 _v) := by
  have p5391 := n5391 _v _q 
  have p5255 := n5255 _v _q 
  have p5257 := n5257 _v _q 
  have p8410 := n8410 _v _q h2722
  have p17678 := n17678 _v _q 
  exact FloorCertificate.node_17737 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p5391 p5255 p5257 p8410 p17678
theorem n17738 (_v : Vars) (_q : Query _v) (h2722 : (e2722 _v)) : (e4686 _v) := by
  have p14708 := n14708 _v _q 
  have p17737 := n17737 _v _q h2722
  simp only [e2242, e4678, e4679, e4683, e4684, e4685, e4686, e6525, e8180] at *
  tauto
theorem n17739 (_v : Vars) (_q : Query _v) (h2722 : (e2722 _v)) : (e2522 _v) := by
  have p5255 := n5255 _v _q 
  have p8410 := n8410 _v _q h2722
  have p17678 := n17678 _v _q 
  have p5257 := n5257 _v _q 
  exact FloorCertificate.node_17739 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p5255 p8410 p17678 p5257
theorem n17740 (_v : Vars) (_q : Query _v) (h2722 : (e2722 _v)) : (e4824 _v) := by
  have p14705 := n14705 _v _q 
  have p17739 := n17739 _v _q h2722
  simp only [e2522, e4816, e4817, e4821, e4822, e4823, e4824, e6650, e8298] at *
  tauto
theorem n17741 (_v : Vars) (_q : Query _v) (h2722 : (e2722 _v)) : (e2781 _v) := by
  have p5391 := n5391 _v _q 
  have p5257 := n5257 _v _q 
  have p5255 := n5255 _v _q 
  have p258 := n258 _v _q 
  have p8410 := n8410 _v _q h2722
  have p17678 := n17678 _v _q 
  exact FloorCertificate.node_17741 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p5391 p5257 p5255 p258 p8410 p17678
theorem n17742 (_v : Vars) (_q : Query _v) (h2722 : (e2722 _v)) : (e4271 _v) := by
  have p14699 := n14699 _v _q 
  have p17741 := n17741 _v _q h2722
  simp only [e2781, e4263, e4264, e4268, e4269, e4270, e4271, e6776, e7795] at *
  tauto
theorem n17743 (_v : Vars) (_q : Query _v) (h2722 : (e2722 _v)) : (e2733 _v) := by
  have p17678 := n17678 _v _q 
  have p258 := n258 _v _q 
  have p5255 := n5255 _v _q 
  have p5257 := n5257 _v _q 
  have p5391 := n5391 _v _q 
  have p8410 := n8410 _v _q h2722
  exact FloorCertificate.node_17743 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p17678 p258 p5255 p5257 p5391 p8410
theorem n17744 (_v : Vars) (_q : Query _v) (h2722 : (e2722 _v)) : (e4109 _v) := by
  have p14689 := n14689 _v _q 
  have p17743 := n17743 _v _q h2722
  simp only [e2733, e4101, e4102, e4106, e4107, e4108, e4109, e6750, e7603] at *
  tauto
theorem n17745 (_v : Vars) (_q : Query _v) (h2722 : (e2722 _v)) : (e2793 _v) := by
  have p5257 := n5257 _v _q 
  have p5255 := n5255 _v _q 
  have p17678 := n17678 _v _q 
  have p258 := n258 _v _q 
  have p5391 := n5391 _v _q 
  have p8410 := n8410 _v _q h2722
  exact FloorCertificate.node_17745 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p5257 p5255 p17678 p258 p5391 p8410
theorem n17746 (_v : Vars) (_q : Query _v) (h2722 : (e2722 _v)) : (e4910 _v) := by
  have p14701 := n14701 _v _q 
  have p17745 := n17745 _v _q h2722
  simp only [e2793, e4902, e4903, e4907, e4908, e4909, e4910, e6784, e8381] at *
  tauto
theorem n17747 (_v : Vars) (_q : Query _v) (h2722 : (e2722 _v)) : (e2061 _v) := by
  have p5255 := n5255 _v _q 
  have p17678 := n17678 _v _q 
  have p5257 := n5257 _v _q 
  have p5391 := n5391 _v _q 
  have p8410 := n8410 _v _q h2722
  exact FloorCertificate.node_17747 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p5255 p17678 p5257 p5391 p8410
theorem n17748 (_v : Vars) (_q : Query _v) (h2722 : (e2722 _v)) : (e4447 _v) := by
  have p14688 := n14688 _v _q 
  have p17747 := n17747 _v _q h2722
  simp only [e2061, e4439, e4440, e4444, e4445, e4446, e4447, e6454, e7961] at *
  tauto
theorem n17749 (_v : Vars) (_q : Query _v) (h2722 : (e2722 _v)) : (e2746 _v) := by
  have p17678 := n17678 _v _q 
  have p5391 := n5391 _v _q 
  have p5257 := n5257 _v _q 
  have p5255 := n5255 _v _q 
  have p258 := n258 _v _q 
  have p8410 := n8410 _v _q h2722
  exact FloorCertificate.node_17749 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p17678 p5391 p5257 p5255 p258 p8410
theorem n17750 (_v : Vars) (_q : Query _v) (h2722 : (e2722 _v)) : (e3984 _v) := by
  have p14691 := n14691 _v _q 
  have p17749 := n17749 _v _q h2722
  simp only [e2746, e3976, e3977, e3981, e3982, e3983, e3984, e6758, e7456] at *
  tauto
theorem n17751 (_v : Vars) (_q : Query _v) (h2722 : (e2722 _v)) : (e2179 _v) := by
  have p5255 := n5255 _v _q 
  have p5257 := n5257 _v _q 
  have p5391 := n5391 _v _q 
  have p17678 := n17678 _v _q 
  have p8410 := n8410 _v _q h2722
  exact FloorCertificate.node_17751 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p5255 p5257 p5391 p17678 p8410
theorem n17752 (_v : Vars) (_q : Query _v) (h2722 : (e2722 _v)) : (e4616 _v) := by
  have p14684 := n14684 _v _q 
  have p17751 := n17751 _v _q h2722
  simp only [e2179, e3158, e3159, e3160, e3161, e3162, e4616, e6501, e8109] at *
  tauto
theorem n17753 (_v : Vars) (_q : Query _v) (h2722 : (e2722 _v)) : (e2585 _v) := by
  have p5257 := n5257 _v _q 
  have p258 := n258 _v _q 
  have p17678 := n17678 _v _q 
  have p5255 := n5255 _v _q 
  have p5391 := n5391 _v _q 
  have p8410 := n8410 _v _q h2722
  exact FloorCertificate.node_17753 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p5257 p258 p17678 p5255 p5391 p8410
theorem n17754 (_v : Vars) (_q : Query _v) (h2722 : (e2722 _v)) : (e4314 _v) := by
  have p14704 := n14704 _v _q 
  have p17753 := n17753 _v _q h2722
  simp only [e2585, e4306, e4307, e4311, e4312, e4313, e4314, e6676, e7836] at *
  tauto
theorem n17755 (_v : Vars) (_q : Query _v) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2781 : (e2781 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4156 : (e4156 _v)) (h4306 : (e4306 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h5208 : (e5208 _v)) (h6571 : (e6571 _v)) (h8045 : (e8045 _v)) (h8310 : (e8310 _v)) : (e1995 _v) := by
  have p17376 := n17376 _v _q 
  have p17175 := n17175 _v _q h5208
  have p8447 := n8447 _v _q h6571
  have p4992 := n4992 _v _q h442
  have p15248 := n15248 _v _q h8310
  have p5008 := n5008 _v _q h4787
  have p5006 := n5006 _v _q h4675
  have p17056 := n17056 _v _q h3946
  have p17061 := n17061 _v _q h4747
  have p4995 := n4995 _v _q h4369
  have p4983 := n4983 _v _q h4813
  have p17138 := n17138 _v _q h4306
  have p17157 := n17157 _v _q h8045
  have p4985 := n4985 _v _q h4156
  have p4988 := n4988 _v _q h488
  have p4986 := n4986 _v _q h3105
  have p4984 := n4984 _v _q h4872
  have p4991 := n4991 _v _q h4608
  have p4994 := n4994 _v _q h3069
  have p4998 := n4998 _v _q h3152
  have p4996 := n4996 _v _q h3937
  have p17134 := n17134 _v _q h4398
  have p4987 := n4987 _v _q h4434
  have p8421 := n8421 _v _q h2781
  simp only [e442, e443, e488, e493, e1995, e2358, e2781, e3069, e3074, e3105, e3106, e3152, e3156, e3937, e3942, e3946, e3947, e4156, e4157, e4306, e4311, e4369, e4370, e4398, e4403, e4434, e4435, e4608, e4609, e4675, e4676, e4747, e4752, e4787, e4788, e4813, e4814, e4872, e4873, e5208, e5218, e6571, e6776, e8045, e8048, e8317, e8320, e17375] at *
  tauto
theorem n17756 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2781 : (e2781 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4306 : (e4306 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4434 : (e4434 _v)) (h4491 : (e4491 _v)) (h4608 : (e4608 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5208 : (e5208 _v)) (h6571 : (e6571 _v)) (h7807 : (e7807 _v)) (h8045 : (e8045 _v)) (h8310 : (e8310 _v)) : (e2061 _v) := by
  have p17675 := n17675 _v _q 
  have p17755 := n17755 _v _q h442 h488 h2781 h3069 h3105 h3152 h3937 h3946 h4156 h4306 h4369 h4398 h4434 h4608 h4675 h4747 h4787 h4813 h4872 h5208 h6571 h8045 h8310
  have p4999 := n4999 _v _q h91
  have p16729 := n16729 _v _q h51
  have p5003 := n5003 _v _q h4199
  have p5007 := n5007 _v _q h225
  have p4992 := n4992 _v _q h442
  have p12935 := n12935 _v _q h2781
  have p4996 := n4996 _v _q h3937
  have p17094 := n17094 _v _q h4724
  have p17134 := n17134 _v _q h4398
  have p4987 := n4987 _v _q h4434
  have p17137 := n17137 _v _q h4059
  have p16011 := n16011 _v _q h2781
  have p17076 := n17076 _v _q h3976
  have p17128 := n17128 _v _q h4491
  have p4983 := n4983 _v _q h4813
  have p4995 := n4995 _v _q h4369
  have p16003 := n16003 _v _q h2781
  have p4998 := n4998 _v _q h3152
  have p11350 := n11350 _v _q h7807
  have p5008 := n5008 _v _q h4787
  have p17060 := n17060 _v _q h4653
  have p5006 := n5006 _v _q h4675
  have p17056 := n17056 _v _q h3946
  have p17061 := n17061 _v _q h4747
  have p4985 := n4985 _v _q h4156
  have p17129 := n17129 _v _q h4903
  have p4988 := n4988 _v _q h488
  have p17175 := n17175 _v _q h5208
  have p4986 := n4986 _v _q h3105
  have p4984 := n4984 _v _q h4872
  have p4991 := n4991 _v _q h4608
  have p4994 := n4994 _v _q h3069
  have p17138 := n17138 _v _q h4306
  have p11384 := n11384 _v _q h8310
  simp only [e51, e57, e91, e95, e225, e230, e442, e443, e488, e493, e1995, e2061, e2303, e2529, e2634, e3069, e3074, e3105, e3106, e3152, e3156, e3937, e3942, e3946, e3947, e3976, e3981, e4059, e4064, e4101, e4106, e4156, e4157, e4199, e4200, e4264, e4269, e4306, e4311, e4369, e4370, e4398, e4403, e4434, e4435, e4491, e4496, e4608, e4609, e4653, e4658, e4675, e4676, e4724, e4729, e4747, e4752, e4787, e4788, e4813, e4814, e4872, e4873, e4903, e4908, e5208, e5218, e6423, e6700, e7807, e8310, e17674] at *
  tauto
theorem n17757 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2358 : (e2358 _v)) (h2781 : (e2781 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3158 : (e3158 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4306 : (e4306 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4439 : (e4439 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5100 : (e5100 _v)) (h5208 : (e5208 _v)) (h7714 : (e7714 _v)) (h7749 : (e7749 _v)) (h7807 : (e7807 _v)) (h8038 : (e8038 _v)) (h8045 : (e8045 _v)) : (e7489 _v) := by
  have p17157 := n17157 _v _q h8045
  have p258 := n258 _v _q 
  have p17677 := n17677 _v _q h91 h191 h225 h442 h488 h2358 h2781 h3069 h3105 h3152 h3158 h3937 h3946 h3976 h4156 h4199 h4306 h4369 h4434 h4439 h4567 h4608 h4653 h4675 h4747 h4787 h4813 h4838 h4872 h4903 h5100 h5208 h7714 h7749 h7807 h8038 h8045
  have p11350 := n11350 _v _q h7807
  have p4996 := n4996 _v _q h3937
  have p5006 := n5006 _v _q h4675
  have p17159 := n17159 _v _q h5100
  have p4989 := n4989 _v _q h4838
  have p17131 := n17131 _v _q 
  have p15373 := n15373 _v _q h7807
  have p253 := n253 _v _q h191
  have p17133 := n17133 _v _q 
  have p16370 := n16370 _v _q h2358
  have p17547 := n17547 _v _q h7749
  have p17278 := n17278 _v _q h2781
  have p17136 := n17136 _v _q 
  have p13951 := n13951 _v _q 
  have p16885 := n16885 _v _q h3158
  have p16008 := n16008 _v _q h2781
  have p4999 := n4999 _v _q h91
  have p5007 := n5007 _v _q h225
  have p16778 := n16778 _v _q 
  have p17141 := n17141 _v _q 
  have p4992 := n4992 _v _q h442
  have p17143 := n17143 _v _q h4567
  have p17050 := n17050 _v _q 
  have p17053 := n17053 _v _q 
  have p17055 := n17055 _v _q 
  have p17056 := n17056 _v _q h3946
  have p17147 := n17147 _v _q 
  have p17058 := n17058 _v _q 
  have p17060 := n17060 _v _q h4653
  have p17061 := n17061 _v _q h4747
  have p11354 := n11354 _v _q h2358
  have p17064 := n17064 _v _q 
  have p4995 := n4995 _v _q h4369
  have p17067 := n17067 _v _q 
  have p17069 := n17069 _v _q 
  have p17138 := n17138 _v _q h4306
  have p17072 := n17072 _v _q 
  have p17074 := n17074 _v _q 
  have p17076 := n17076 _v _q h3976
  have p4985 := n4985 _v _q h4156
  have p17279 := n17279 _v _q h2781
  have p4988 := n4988 _v _q h488
  have p17078 := n17078 _v _q 
  have p4986 := n4986 _v _q h3105
  have p17080 := n17080 _v _q 
  have p17083 := n17083 _v _q 
  have p4984 := n4984 _v _q h4872
  have p17087 := n17087 _v _q 
  have p17091 := n17091 _v _q 
  have p16026 := n16026 _v _q h2781
  have p17093 := n17093 _v _q 
  have p17111 := n17111 _v _q 
  have p17075 := n17075 _v _q h4439
  have p17115 := n17115 _v _q 
  have p17089 := n17089 _v _q 
  have p17100 := n17100 _v _q 
  have p17098 := n17098 _v _q 
  have p17096 := n17096 _v _q 
  have p17110 := n17110 _v _q 
  have p17102 := n17102 _v _q 
  have p17104 := n17104 _v _q 
  have p17106 := n17106 _v _q 
  have p17108 := n17108 _v _q 
  have p4994 := n4994 _v _q h3069
  have p17120 := n17120 _v _q 
  have p17113 := n17113 _v _q 
  have p17117 := n17117 _v _q 
  have p17124 := n17124 _v _q 
  have p17122 := n17122 _v _q 
  have p16003 := n16003 _v _q h2781
  have p4998 := n4998 _v _q h3152
  have p16011 := n16011 _v _q h2781
  have p5003 := n5003 _v _q h4199
  have p17127 := n17127 _v _q 
  have p4983 := n4983 _v _q h4813
  have p16020 := n16020 _v _q h2781
  have p17129 := n17129 _v _q h4903
  have p5008 := n5008 _v _q h4787
  exact FloorCertificate.node_17757 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2883 _v) (e2902 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4541 _v) (e4808 _v) p17157 p258 p17677 p11350 p4996 p5006 p17159 p4989 p17131 p15373 p253 p17133 p16370 p17547 p17278 p17136 p13951 p16885 p16008 p4999 p5007 p16778 p17141 p4992 p17143 p17050 p17053 p17055 p17056 p17147 p17058 p17060 p17061 p11354 p17064 p4995 p17067 p17069 p17138 p17072 p17074 p17076 p4985 p17279 p4988 p17078 p4986 p17080 p17083 p4984 p17087 p17091 p16026 p17093 p17111 p17075 p17115 p17089 p17100 p17098 p17096 p17110 p17102 p17104 p17106 p17108 p4994 p17120 p17113 p17117 p17124 p17122 p16003 p4998 p16011 p5003 p17127 p4983 p16020 p17129 p5008
theorem n17758 (_v : Vars) (_q : Query _v)  : (e3105 _v) := by
  have p16188 := n16188 _v _q 
  have p17679 := n17679 _v _q 
  simp only [e3103, e3104, e3105, e3106, e6855, e6856, e6863] at *
  tauto
theorem n17759 (_v : Vars) (_q : Query _v) (h2061 : (e2061 _v)) (h8310 : (e8310 _v)) : (e4306 _v) := by
  have p14984 := n14984 _v _q 
  have p15227 := n15227 _v _q h2061 h8310
  simp only [e4306, e4307, e4311, e4312, e4313, e4314, e4964] at *
  tauto
theorem n17760 (_v : Vars) (_q : Query _v) (h225 : (e225 _v)) (h488 : (e488 _v)) (h2061 : (e2061 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3271 : (e3271 _v)) (h3855 : (e3855 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4491 : (e4491 _v)) (h4653 : (e4653 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5100 : (e5100 _v)) (h6571 : (e6571 _v)) (h6700 : (e6700 _v)) (h7493 : (e7493 _v)) (h7749 : (e7749 _v)) (h8045 : (e8045 _v)) (h8310 : (e8310 _v)) : (e4459 _v) := by
  have p17697 := n17697 _v _q h225 h488 h2061 h3069 h3105 h3152 h3271 h3855 h3937 h3946 h3976 h4059 h4096 h4156 h4260 h4369 h4398 h4491 h4653 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h6571 h6700 h7493 h8045 h8310
  have p16269 := n16269 _v _q h7749
  have p17659 := n17659 _v _q h225 h488 h2061 h3069 h3105 h3152 h3271 h3855 h3937 h3946 h3976 h4059 h4096 h4156 h4260 h4369 h4398 h4491 h4653 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h6571 h6700 h7493 h8045 h8310
  exact FloorCertificate.node_17760 (e2 _v) (e7 _v) (e17 _v) (e110 _v) (e2932 _v) (e4215 _v) p17697 p16269 p17659
theorem n17761 (_v : Vars) (_q : Query _v) (h225 : (e225 _v)) (h488 : (e488 _v)) (h2061 : (e2061 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3271 : (e3271 _v)) (h3855 : (e3855 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4491 : (e4491 _v)) (h4653 : (e4653 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5100 : (e5100 _v)) (h6571 : (e6571 _v)) (h6700 : (e6700 _v)) (h7493 : (e7493 _v)) (h7749 : (e7749 _v)) (h8045 : (e8045 _v)) (h8310 : (e8310 _v)) : (e5218 _v) := by
  have p17304 := n17304 _v _q 
  have p17759 := n17759 _v _q h2061 h8310
  have p17155 := n17155 _v _q h7493
  have p17076 := n17076 _v _q h3976
  have p5001 := n5001 _v _q h4096
  have p17657 := n17657 _v _q h6571 h8310
  have p15217 := n15217 _v _q h2061
  have p17056 := n17056 _v _q h3946
  have p17165 := n17165 _v _q h3271
  have p17159 := n17159 _v _q h5100
  have p17129 := n17129 _v _q h4903
  have p16352 := n16352 _v _q h6700
  have p5007 := n5007 _v _q h225
  have p5008 := n5008 _v _q h4787
  have p15234 := n15234 _v _q h6700
  have p15237 := n15237 _v _q h2061
  have p16353 := n16353 _v _q h6700
  have p4981 := n4981 _v _q h4260
  have p16803 := n16803 _v _q h6700
  have p17157 := n17157 _v _q h8045
  have p17061 := n17061 _v _q h4747
  have p4988 := n4988 _v _q h488
  have p4986 := n4986 _v _q h3105
  have p4983 := n4983 _v _q h4813
  have p17094 := n17094 _v _q h4724
  have p4994 := n4994 _v _q h3069
  have p16804 := n16804 _v _q h6700
  have p4984 := n4984 _v _q h4872
  have p4985 := n4985 _v _q h4156
  have p17134 := n17134 _v _q h4398
  have p16358 := n16358 _v _q h6700
  have p16250 := n16250 _v _q h3855
  have p17760 := n17760 _v _q h225 h488 h2061 h3069 h3105 h3152 h3271 h3855 h3937 h3946 h3976 h4059 h4096 h4156 h4260 h4369 h4398 h4491 h4653 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h6571 h6700 h7493 h7749 h8045 h8310
  have p17060 := n17060 _v _q h4653
  have p17658 := n17658 _v _q h6571 h8310
  have p15258 := n15258 _v _q h2061
  have p4998 := n4998 _v _q h3152
  have p4995 := n4995 _v _q h4369
  have p17128 := n17128 _v _q h4491
  have p4996 := n4996 _v _q h3937
  have p15248 := n15248 _v _q h8310
  have p17656 := n17656 _v _q h6571
  have p17137 := n17137 _v _q h4059
  have p16805 := n16805 _v _q h6700
  have p15251 := n15251 _v _q h6571
  simp only [e70, e75, e91, e95, e225, e230, e442, e443, e488, e493, e3069, e3074, e3105, e3106, e3152, e3156, e3169, e3170, e3271, e3276, e3566, e3571, e3855, e3860, e3937, e3942, e3946, e3947, e3976, e3981, e4059, e4064, e4096, e4097, e4156, e4157, e4199, e4200, e4260, e4261, e4306, e4311, e4369, e4370, e4398, e4403, e4439, e4444, e4459, e4464, e4491, e4496, e4567, e4572, e4608, e4609, e4653, e4658, e4675, e4676, e4724, e4729, e4747, e4752, e4787, e4788, e4813, e4814, e4872, e4873, e4903, e4908, e5100, e5103, e5208, e5218, e7493, e7494, e7606, e7607, e7645, e7655, e7814, e7817, e7935, e7943, e8045, e8048, e8317, e8320, e17303] at *
  tauto
theorem n17762 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2125 : (e2125 _v)) (h2358 : (e2358 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3976 : (e3976 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h6700 : (e6700 _v)) (h8038 : (e8038 _v)) : (e2787 _v) := by
  have p15228 := n15228 _v _q 
  have p17698 := n17698 _v _q h70 h91 h191 h225 h442 h488 h2125 h2358 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4567 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  simp only [e2787, e7932, e7935, e7942, e7943, e7944, e7945, e11111] at *
  tauto
theorem n17763 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2125 : (e2125 _v)) (h2358 : (e2358 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3976 : (e3976 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h6700 : (e6700 _v)) (h8038 : (e8038 _v)) : (e7927 _v) := by
  have p14855 := n14855 _v _q 
  have p17762 := n17762 _v _q h70 h91 h191 h225 h442 h488 h2125 h2358 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4567 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  simp only [e2787, e4417, e4418, e4419, e4420, e6772, e7921, e7927, e7930] at *
  tauto
theorem n17765 (_v : Vars) (_q : Query _v)  : (e17764 _v) := by
  by_contra hc
  change ¬ ((e2529 _v) ∨ (¬ (e3855 _v)) ∨ (e2634 _v) ∨ (¬ (e3271 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e7606 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e7749 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4477 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e7493 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e4491 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e5100 _v)) ∨ (¬ (e4903 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e3976 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e3169 _v)) ∨ (¬ (e4567 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e8045 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4724 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e4398 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e8335 _v)) ∨ (¬ (e7688 _v)) ∨ (¬ (e5208 _v)) ∨ (¬ (e2358 _v))) at hc
  have h70 : (e70 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h191 : (e191 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h225 : (e225 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))
  have h442 : (e442 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))))))))
  have h488 : (e488 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))
  have h2358 : (e2358 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))))))))))))))))))))))))))))))))))))))))
  have h3069 : (e3069 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))))))
  have h3105 : (e3105 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h3169 : (e3169 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))
  have h3271 : (e3271 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h3855 : (e3855 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h3946 : (e3946 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))
  have h3976 : (e3976 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))
  have h4059 : (e4059 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h4096 : (e4096 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h4156 : (e4156 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))))))))))
  have h4199 : (e4199 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))
  have h4260 : (e4260 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))
  have h4369 : (e4369 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4398 : (e4398 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))))))))))
  have h4477 : (e4477 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h4491 : (e4491 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))
  have h4567 : (e4567 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))
  have h4608 : (e4608 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))))))))))))
  have h4675 : (e4675 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))
  have h4724 : (e4724 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))))))
  have h4747 : (e4747 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))))
  have h4872 : (e4872 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))))))))
  have h4903 : (e4903 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))
  have h5100 : (e5100 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))
  have h5208 : (e5208 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))))))))))))))
  have h6700 : (e6700 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h7493 : (e7493 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h7606 : (e7606 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h7688 : (e7688 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))))))))))))))
  have h7749 : (e7749 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h8045 : (e8045 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))
  have h8310 : (e8310 _v) := (fun hn => hc (Or.inl hn))
  have h8335 : (e8335 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))))))))))))
  have p17700 := n17700 _v _q h70 h91 h191 h225 h442 h488 h2358 h3069 h3105 h3152 h3169 h3271 h3855 h3937 h3946 h3976 h4059 h4096 h4156 h4199 h4260 h4369 h4398 h4477 h4491 h4567 h4608 h4675 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h5208 h6700 h7493 h7606 h7688 h7749 h8045 h8310 h8335
  exact p17700
theorem n17766 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3976 : (e3976 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4572 : (e4572 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h8038 : (e8038 _v)) : (e2310 _v) := by
  have p17702 := n17702 _v _q 
  have p15179 := n15179 _v _q h4572
  have p4991 := n4991 _v _q h4608
  have p4995 := n4995 _v _q h4369
  have p4996 := n4996 _v _q h3937
  have p4998 := n4998 _v _q h3152
  have p4999 := n4999 _v _q h91
  have p5001 := n5001 _v _q h4096
  have p5003 := n5003 _v _q h4199
  have p17129 := n17129 _v _q h4903
  have p5006 := n5006 _v _q h4675
  have p17076 := n17076 _v _q h3976
  have p5007 := n5007 _v _q h225
  have p5008 := n5008 _v _q h4787
  have p5005 := n5005 _v _q h3169
  have p5010 := n5010 _v _q h70
  have p4981 := n4981 _v _q h4260
  have p4988 := n4988 _v _q h488
  have p4986 := n4986 _v _q h3105
  have p4983 := n4983 _v _q h4813
  have p4994 := n4994 _v _q h3069
  have p4992 := n4992 _v _q h442
  have p4984 := n4984 _v _q h4872
  have p4985 := n4985 _v _q h4156
  have p253 := n253 _v _q h191
  have p8602 := n8602 _v _q h8038
  simp only [e70, e75, e91, e95, e191, e192, e225, e230, e442, e443, e488, e493, e1995, e2310, e2475, e3069, e3074, e3105, e3106, e3152, e3156, e3169, e3170, e3937, e3942, e3976, e3981, e4096, e4097, e4156, e4157, e4199, e4200, e4260, e4261, e4369, e4370, e4608, e4609, e4675, e4676, e4787, e4788, e4813, e4814, e4872, e4873, e4903, e4908, e6423, e8038, e17701] at *
  tauto
end
end Assembly
