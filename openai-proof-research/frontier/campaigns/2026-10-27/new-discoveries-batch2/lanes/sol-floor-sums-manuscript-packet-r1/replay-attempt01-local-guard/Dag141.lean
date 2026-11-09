import Dag140
import generated.th_lemma_11
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n16004 (_v : Vars) (_q : Query _v) (h2781 : (e2781 _v)) (h6423 : (e6423 _v)) : (e2733 _v) := by
  have p8421 := n8421 _v _q h2781
  have p8663 := n8663 _v _q 
  have p8452 := n8452 _v _q h6423
  exact FloorCertificate.node_16004 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8421 p8663 p8452
theorem n16005 (_v : Vars) (_q : Query _v) (h2781 : (e2781 _v)) (h6423 : (e6423 _v)) : (e4109 _v) := by
  have p14689 := n14689 _v _q 
  have p16004 := n16004 _v _q h2781 h6423
  simp only [e2733, e4101, e4102, e4106, e4107, e4108, e4109, e6750, e7603] at *
  tauto
theorem n16006 (_v : Vars) (_q : Query _v) (h2781 : (e2781 _v)) : (e2598 _v) := by
  have p8421 := n8421 _v _q h2781
  have p10893 := n10893 _v _q 
  have p11376 := n11376 _v _q 
  have p8663 := n8663 _v _q 
  have p5255 := n5255 _v _q 
  have p11375 := n11375 _v _q 
  exact FloorCertificate.node_16006 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8421 p10893 p11376 p8663 p5255 p11375
theorem n16007 (_v : Vars) (_q : Query _v) (h2781 : (e2781 _v)) : (e4067 _v) := by
  have p14703 := n14703 _v _q 
  have p16006 := n16006 _v _q h2781
  simp only [e2598, e4059, e4060, e4064, e4065, e4066, e4067, e6684, e7560] at *
  tauto
theorem n16008 (_v : Vars) (_q : Query _v) (h2781 : (e2781 _v)) : (e4059 _v) := by
  have p14980 := n14980 _v _q 
  have p16007 := n16007 _v _q h2781
  simp only [e4059, e4060, e4064, e4065, e4066, e4067, e4963] at *
  tauto
theorem n16009 (_v : Vars) (_q : Query _v) (h2781 : (e2781 _v)) : (e2733 _v) := by
  have p8424 := n8424 _v _q 
  have p8421 := n8421 _v _q h2781
  simp only [e2733, e2781, e6776, e8423] at *
  tauto
theorem n16010 (_v : Vars) (_q : Query _v) (h2781 : (e2781 _v)) : (e4109 _v) := by
  have p14689 := n14689 _v _q 
  have p16009 := n16009 _v _q h2781
  simp only [e2733, e4101, e4102, e4106, e4107, e4108, e4109, e6750, e7603] at *
  tauto
theorem n16011 (_v : Vars) (_q : Query _v) (h2781 : (e2781 _v)) : (e4101 _v) := by
  have p14929 := n14929 _v _q 
  have p16010 := n16010 _v _q h2781
  simp only [e4101, e4102, e4106, e4107, e4108, e4109, e4952] at *
  tauto
theorem n16012 (_v : Vars) (_q : Query _v) (h48 : (e48 _v)) : (e60 _v) := by
  have p14152 := n14152 _v _q 
  have p11547 := n11547 _v _q h48
  simp only [e48, e51, e52, e57, e58, e59, e60, e5108, e5125] at *
  tauto
theorem n16013 (_v : Vars) (_q : Query _v) (h48 : (e48 _v)) : (e51 _v) := by
  have p14962 := n14962 _v _q 
  have p16012 := n16012 _v _q h48
  simp only [e51, e52, e57, e58, e59, e60, e77] at *
  tauto
theorem n16014 (_v : Vars) (_q : Query _v) (h7807 : (e7807 _v)) : (e7630 _v) := by
  have p15152 := n15152 _v _q 
  have p12866 := n12866 _v _q h7807
  simp only [e2740, e6746, e7606, e7607, e7608, e7609, e7610, e7630, e10951] at *
  tauto
theorem n16015 (_v : Vars) (_q : Query _v) (h2733 : (e2733 _v)) : (e48 _v) := by
  have p11369 := n11369 _v _q 
  have p8587 := n8587 _v _q h2733
  simp only [e48, e2733, e6750, e11368] at *
  tauto
theorem n16016 (_v : Vars) (_q : Query _v) (h2733 : (e2733 _v)) : (e60 _v) := by
  have p14152 := n14152 _v _q 
  have p16015 := n16015 _v _q h2733
  simp only [e48, e51, e52, e57, e58, e59, e60, e5108, e5125] at *
  tauto
theorem n16017 (_v : Vars) (_q : Query _v) (h2733 : (e2733 _v)) : (e51 _v) := by
  have p14962 := n14962 _v _q 
  have p16016 := n16016 _v _q h2733
  simp only [e51, e52, e57, e58, e59, e60, e77] at *
  tauto
theorem n16018 (_v : Vars) (_q : Query _v) (h2781 : (e2781 _v)) : (e2697 _v) := by
  have p11391 := n11391 _v _q 
  have p12937 := n12937 _v _q h2781
  simp only [e2254, e2697, e6531, e11390] at *
  tauto
theorem n16019 (_v : Vars) (_q : Query _v) (h2781 : (e2781 _v)) : (e4499 _v) := by
  have p14700 := n14700 _v _q 
  have p16018 := n16018 _v _q h2781
  simp only [e2697, e4491, e4492, e4496, e4497, e4498, e4499, e6732, e7998] at *
  tauto
theorem n16020 (_v : Vars) (_q : Query _v) (h2781 : (e2781 _v)) : (e4491 _v) := by
  have p14969 := n14969 _v _q 
  have p16019 := n16019 _v _q h2781
  simp only [e4491, e4492, e4496, e4497, e4498, e4499, e4960] at *
  tauto
theorem n16021 (_v : Vars) (_q : Query _v) (h2781 : (e2781 _v)) : (e2482 _v) := by
  have p11035 := n11035 _v _q 
  have p12935 := n12935 _v _q h2781
  simp only [e2482, e2634, e6700, e11034] at *
  tauto
theorem n16022 (_v : Vars) (_q : Query _v) (h2781 : (e2781 _v)) : (e4405 _v) := by
  have p14702 := n14702 _v _q 
  have p16021 := n16021 _v _q h2781
  simp only [e2482, e4397, e4398, e4402, e4403, e4404, e4405, e6636, e7918] at *
  tauto
theorem n16023 (_v : Vars) (_q : Query _v) (h2781 : (e2781 _v)) : (e48 _v) := by
  have p12935 := n12935 _v _q h2781
  have p5257 := n5257 _v _q 
  have p8421 := n8421 _v _q h2781
  exact FloorCertificate.node_16023 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p12935 p5257 p8421
theorem n16024 (_v : Vars) (_q : Query _v) (h2781 : (e2781 _v)) : (e60 _v) := by
  have p14152 := n14152 _v _q 
  have p16023 := n16023 _v _q h2781
  simp only [e48, e51, e52, e57, e58, e59, e60, e5108, e5125] at *
  tauto
theorem n16025 (_v : Vars) (_q : Query _v) (h2781 : (e2781 _v)) : (e4731 _v) := by
  have p14698 := n14698 _v _q 
  have p12937 := n12937 _v _q h2781
  simp only [e2254, e4723, e4724, e4728, e4729, e4730, e4731, e6531, e8220] at *
  tauto
theorem n16026 (_v : Vars) (_q : Query _v) (h2781 : (e2781 _v)) : (e4724 _v) := by
  have p15518 := n15518 _v _q 
  have p16025 := n16025 _v _q h2781
  simp only [e4723, e4724, e4728, e4729, e4730, e4731, e4958] at *
  tauto
theorem n16027 (_v : Vars) (_q : Query _v) (h2303 : (e2303 _v)) (h2781 : (e2781 _v)) : (e2468 _v) := by
  have p8581 := n8581 _v _q 
  have p8448 := n8448 _v _q h2303
  have p8421 := n8421 _v _q h2781
  simp only [e2303, e2468, e2781, e6776, e7807, e8580] at *
  tauto
theorem n16028 (_v : Vars) (_q : Query _v) (h2303 : (e2303 _v)) (h2781 : (e2781 _v)) : (e4798 _v) := by
  have p14690 := n14690 _v _q 
  have p16027 := n16027 _v _q h2303 h2781
  simp only [e2468, e4790, e4791, e4795, e4796, e4797, e4798, e6630, e8281] at *
  tauto
theorem n16029 (_v : Vars) (_q : Query _v) (h2303 : (e2303 _v)) (h2781 : (e2781 _v)) : (e4791 _v) := by
  have p14932 := n14932 _v _q 
  have p16028 := n16028 _v _q h2303 h2781
  simp only [e4790, e4791, e4795, e4796, e4797, e4798, e4953] at *
  tauto
theorem n16030 (_v : Vars) (_q : Query _v) (h2303 : (e2303 _v)) (h2781 : (e2781 _v)) : (e2242 _v) := by
  have p11553 := n11553 _v _q 
  have p8448 := n8448 _v _q h2303
  have p8421 := n8421 _v _q h2781
  simp only [e2242, e2303, e2781, e6776, e7807, e11552] at *
  tauto
theorem n16031 (_v : Vars) (_q : Query _v) (h2303 : (e2303 _v)) (h2781 : (e2781 _v)) : (e4686 _v) := by
  have p14708 := n14708 _v _q 
  have p16030 := n16030 _v _q h2303 h2781
  simp only [e2242, e4678, e4679, e4683, e4684, e4685, e4686, e6525, e8180] at *
  tauto
theorem n16032 (_v : Vars) (_q : Query _v) (h2303 : (e2303 _v)) (h2781 : (e2781 _v)) : (e4679 _v) := by
  have p14989 := n14989 _v _q 
  have p16031 := n16031 _v _q h2303 h2781
  simp only [e4678, e4679, e4683, e4684, e4685, e4686, e4967] at *
  tauto
theorem n16033 (_v : Vars) (_q : Query _v) (h196 : (e196 _v)) (h2781 : (e2781 _v)) : (e2179 _v) := by
  have p8140 := n8140 _v _q h196
  have p8421 := n8421 _v _q h2781
  exact FloorCertificate.node_16033 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8140 p8421
theorem n16034 (_v : Vars) (_q : Query _v) (h196 : (e196 _v)) (h2781 : (e2781 _v)) : (e4616 _v) := by
  have p14684 := n14684 _v _q 
  have p16033 := n16033 _v _q h196 h2781
  simp only [e2179, e3158, e3159, e3160, e3161, e3162, e4616, e6501, e8109] at *
  tauto
theorem n16035 (_v : Vars) (_q : Query _v) (h196 : (e196 _v)) (h2781 : (e2781 _v)) : (e3158 _v) := by
  have p15126 := n15126 _v _q 
  have p16034 := n16034 _v _q h196 h2781
  simp only [e3158, e3159, e3160, e3161, e3162, e3163, e4616] at *
  tauto
theorem n16036 (_v : Vars) (_q : Query _v) (h196 : (e196 _v)) (h2781 : (e2781 _v)) : (e2061 _v) := by
  have p8140 := n8140 _v _q h196
  have p8421 := n8421 _v _q h2781
  have p5255 := n5255 _v _q 
  exact FloorCertificate.node_16036 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8140 p8421 p5255
theorem n16037 (_v : Vars) (_q : Query _v) (h196 : (e196 _v)) (h2781 : (e2781 _v)) : (e1995 _v) := by
  have p11412 := n11412 _v _q 
  have p16036 := n16036 _v _q h196 h2781
  simp only [e1995, e2061, e6454, e11411] at *
  tauto
theorem n16038 (_v : Vars) (_q : Query _v) (h196 : (e196 _v)) (h2781 : (e2781 _v)) : (e4575 _v) := by
  have p14696 := n14696 _v _q 
  have p16037 := n16037 _v _q h196 h2781
  simp only [e1995, e4567, e4568, e4572, e4573, e4574, e4575, e6423, e8066] at *
  tauto
theorem n16039 (_v : Vars) (_q : Query _v) (h196 : (e196 _v)) (h2781 : (e2781 _v)) (h8038 : (e8038 _v)) : (e2364 _v) := by
  have p11343 := n11343 _v _q 
  have p11554 := n11554 _v _q h196 h2781 h8038
  simp only [e2364, e2585, e6676, e11342] at *
  tauto
theorem n16040 (_v : Vars) (_q : Query _v) (h196 : (e196 _v)) (h2781 : (e2781 _v)) (h8038 : (e8038 _v)) : (e4661 _v) := by
  have p14686 := n14686 _v _q 
  have p16039 := n16039 _v _q h196 h2781 h8038
  simp only [e2364, e4653, e4654, e4658, e4659, e4660, e4661, e6583, e8163] at *
  tauto
theorem n16041 (_v : Vars) (_q : Query _v) (h196 : (e196 _v)) (h2781 : (e2781 _v)) (h8038 : (e8038 _v)) : (e4653 _v) := by
  have p15168 := n15168 _v _q 
  have p16040 := n16040 _v _q h196 h2781 h8038
  simp only [e4653, e4654, e4658, e4659, e4660, e4661, e4939] at *
  tauto
theorem n16042 (_v : Vars) (_q : Query _v) (h196 : (e196 _v)) (h2781 : (e2781 _v)) (h8038 : (e8038 _v)) : (e4314 _v) := by
  have p14704 := n14704 _v _q 
  have p11554 := n11554 _v _q h196 h2781 h8038
  simp only [e2585, e4306, e4307, e4311, e4312, e4313, e4314, e6676, e7836] at *
  tauto
theorem n16043 (_v : Vars) (_q : Query _v) (h196 : (e196 _v)) (h2781 : (e2781 _v)) (h8038 : (e8038 _v)) : (e4306 _v) := by
  have p14984 := n14984 _v _q 
  have p16042 := n16042 _v _q h196 h2781 h8038
  simp only [e4306, e4307, e4311, e4312, e4313, e4314, e4964] at *
  tauto
theorem n16044 (_v : Vars) (_q : Query _v) (h196 : (e196 _v)) (h2781 : (e2781 _v)) : (e4447 _v) := by
  have p14688 := n14688 _v _q 
  have p16036 := n16036 _v _q h196 h2781
  simp only [e2061, e4439, e4440, e4444, e4445, e4446, e4447, e6454, e7961] at *
  tauto
theorem n16045 (_v : Vars) (_q : Query _v) (h196 : (e196 _v)) (h2781 : (e2781 _v)) : (e4439 _v) := by
  have p14925 := n14925 _v _q 
  have p16044 := n16044 _v _q h196 h2781
  simp only [e4439, e4440, e4444, e4445, e4446, e4447, e4941] at *
  tauto
theorem n16046 (_v : Vars) (_q : Query _v) (h2132 : (e2132 _v)) (h6501 : (e6501 _v)) : (e5108 _v) := by
  have p11550 := n11550 _v _q 
  have p12939 := n12939 _v _q h2132 h6501
  simp only [e48, e2585, e5108, e6676, e11549] at *
  tauto
theorem n16047 (_v : Vars) (_q : Query _v) (h2132 : (e2132 _v)) (h6501 : (e6501 _v)) : (e5119 _v) := by
  have p14487 := n14487 _v _q 
  have p16046 := n16046 _v _q h2132 h6501
  simp only [e48, e70, e72, e75, e76, e5108, e5118, e5119, e5122] at *
  tauto
theorem n16048 (_v : Vars) (_q : Query _v) (h2132 : (e2132 _v)) (h6501 : (e6501 _v)) : (e70 _v) := by
  have p15648 := n15648 _v _q 
  have p16047 := n16047 _v _q h2132 h6501
  simp only [e70, e72, e75, e76, e5118, e5119, e7441] at *
  tauto
end
end Assembly
