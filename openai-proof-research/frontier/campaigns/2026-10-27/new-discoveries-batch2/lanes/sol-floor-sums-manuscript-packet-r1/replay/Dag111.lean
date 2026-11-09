import Dag110
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n14626 (_v : Vars) (_q : Query _v)  : (e8106 _v) := by
  have p14625 := n14625 _v _q 
  simp only [e2179, e3158, e3159, e3160, e3161, e3162, e4608, e4609, e4610, e4611, e4616, e6501, e8095, e8103, e8106, e8109, e8111, e11197, e11198, e13980] at *
  tauto
theorem n14627 (_v : Vars) (_q : Query _v)  : (e8135 _v) := by
  have p13989 := n13989 _v _q 
  simp only [e174, e176, e4627, e4628, e4637, e4639, e4642, e4643, e8112, e8113, e8114, e8121, e8122, e8125, e8131, e8135, e8136, e11208, e11209, e11210] at *
  tauto
theorem n14628 (_v : Vars) (_q : Query _v)  : (e8131 _v) := by
  have p14627 := n14627 _v _q 
  have p11375 := n11375 _v _q 
  simp only [e174, e176, e4627, e4628, e8112, e8113, e8114, e8131, e8135] at *
  tauto
theorem n14629 (_v : Vars) (_q : Query _v)  : (e6833 _v) := by
  have p14349 := n14349 _v _q 
  simp only [e496, e3051, e3052, e3053, e3054, e3055, e3061, e3069, e3071, e3074, e3075, e6720, e6829, e6830, e6833, e6836, e6838, e10556, e10557, e13453] at *
  tauto
theorem n14630 (_v : Vars) (_q : Query _v)  : (e7435 _v) := by
  have p14485 := n14485 _v _q 
  simp only [e2805, e3944, e3945, e3946, e3947, e3948, e3954, e3963, e3965, e3968, e3969, e6792, e7431, e7432, e7435, e7438, e7440, e10869, e10870, e13771] at *
  tauto
theorem n14631 (_v : Vars) (_q : Query _v)  : (e14000 _v) := by
  have p10270 := n10270 _v _q 
  have p14004 := n14004 _v _q 
  simp only [e2364, e4648, e4649, e4650, e4651, e4652, e4653, e4654, e4658, e4659, e4660, e4661, e4662, e6583, e6584, e6585, e6586, e8149, e8157, e8160, e8163, e8165, e11222, e11223, e14000, e14003] at *
  tauto
theorem n14632 (_v : Vars) (_q : Query _v)  : (e8160 _v) := by
  have p14631 := n14631 _v _q 
  simp only [e2364, e4648, e4649, e4650, e4651, e4653, e4654, e4658, e4659, e4660, e4661, e6583, e8149, e8157, e8160, e8163, e8165, e11222, e11223, e14000] at *
  tauto
theorem n14633 (_v : Vars) (_q : Query _v)  : (e14010 _v) := by
  have p12150 := n12150 _v _q 
  have p14014 := n14014 _v _q 
  simp only [e2242, e4673, e4674, e4675, e4676, e4677, e4678, e4679, e4683, e4684, e4685, e4686, e4687, e6525, e6526, e6527, e6528, e8166, e8174, e8177, e8180, e8182, e11230, e11231, e14010, e14013] at *
  tauto
theorem n14634 (_v : Vars) (_q : Query _v)  : (e8177 _v) := by
  have p14633 := n14633 _v _q 
  simp only [e2242, e4673, e4674, e4675, e4676, e4678, e4679, e4683, e4684, e4685, e4686, e6525, e8166, e8174, e8177, e8180, e8182, e11230, e11231, e14010] at *
  tauto
theorem n14635 (_v : Vars) (_q : Query _v)  : (e8200 _v) := by
  have p12744 := n12744 _v _q 
  change ((e4698 _v) ↔ (e8194 _v)) at p12744
  simp only [e8200, e8198, e8199, p12744]
theorem n14636 (_v : Vars) (_q : Query _v)  : (e12751 _v) := by
  have p14635 := n14635 _v _q 
  have p14017 := n14017 _v _q 
  change ((e8198 _v) ↔ (e8199 _v)) at p14635
  change ((e6530 _v) ↔ (e11242 _v)) at p14017
  simp only [e12751, e10227, e11243, p14635, p14017]
theorem n14638 (_v : Vars) (_q : Query _v)  : (e14637 _v) := by
  simp only [e5, e6, e8, e10, e12, e41, e43, e44, e2260, e2261, e4697, e4704, e4705, e4706, e4708, e4711, e4712, e8183, e8184, e8185, e8186, e8187, e8193, e8194, e8197, e8199, e8204, e8205, e11242, e11243, e11244, e11245, e11246, e14637] at *
  omega
theorem n14639 (_v : Vars) (_q : Query _v)  : (e12752 _v) := by
  have p14636 := n14636 _v _q 
  have p14638 := n14638 _v _q 
  exact (Iff.trans p14636 p14638)
theorem n14640 (_v : Vars) (_q : Query _v)  : (e11246 _v) := by
  have p10228 := n10228 _v _q 
  have p14639 := n14639 _v _q 
  simp only [e2261, e4698, e4706, e4708, e4711, e4712, e6529, e6530, e8183, e8184, e8185, e8186, e8187, e8193, e8194, e8197, e8198, e8199, e8204, e8205, e10227, e11242, e11244, e11245, e11246, e12752] at *
  tauto
theorem n14641 (_v : Vars) (_q : Query _v)  : (e14023 _v) := by
  have p12160 := n12160 _v _q 
  have p14027 := n14027 _v _q 
  simp only [e2254, e4718, e4719, e4720, e4721, e4722, e4723, e4724, e4728, e4729, e4730, e4731, e4732, e6531, e6532, e6533, e6534, e8206, e8214, e8217, e8220, e8222, e11253, e11254, e14023, e14026] at *
  tauto
theorem n14642 (_v : Vars) (_q : Query _v)  : (e8217 _v) := by
  have p14641 := n14641 _v _q 
  simp only [e2254, e4718, e4719, e4720, e4721, e4723, e4724, e4728, e4729, e4730, e4731, e6531, e8206, e8214, e8217, e8220, e8222, e11253, e11254, e14023] at *
  tauto
theorem n14643 (_v : Vars) (_q : Query _v)  : (e6882 _v) := by
  have p14357 := n14357 _v _q 
  simp only [e2296, e3132, e3133, e3137, e3138, e3139, e3140, e3150, e3152, e3155, e3156, e6549, e6878, e6879, e6882, e6885, e6887, e10580, e10581, e13483] at *
  tauto
theorem n14644 (_v : Vars) (_q : Query _v)  : (e14033 _v) := by
  have p10281 := n10281 _v _q 
  have p14037 := n14037 _v _q 
  simp only [e2377, e4742, e4743, e4744, e4745, e4746, e4747, e4748, e4752, e4753, e4754, e4755, e4756, e6591, e6592, e6593, e6594, e8224, e8232, e8235, e8238, e8240, e11261, e11262, e14033, e14036] at *
  tauto
theorem n14645 (_v : Vars) (_q : Query _v)  : (e8235 _v) := by
  have p14644 := n14644 _v _q 
  simp only [e2377, e4742, e4743, e4744, e4745, e4747, e4748, e4752, e4753, e4754, e4755, e6591, e8224, e8232, e8235, e8238, e8240, e11261, e11262, e14033] at *
  tauto
theorem n14646 (_v : Vars) (_q : Query _v)  : (e8256 _v) := by
  have p12758 := n12758 _v _q 
  change ((e4766 _v) ↔ (e8252 _v)) at p12758
  simp only [e8256, e6588, e8255, p12758]
theorem n14648 (_v : Vars) (_q : Query _v)  : (e14647 _v) := by
  have p14646 := n14646 _v _q 
  have p14042 := n14042 _v _q 
  change ((e6588 _v) ↔ (e8255 _v)) at p14646
  change ((e6589 _v) ↔ (e11267 _v)) at p14042
  simp only [e14647, e6590, e11268, p14646, p14042]
theorem n14650 (_v : Vars) (_q : Query _v)  : (e14649 _v) := by
  simp only [e5, e6, e8, e10, e12, e41, e111, e266, e267, e2383, e2384, e4765, e4772, e4773, e4774, e4776, e4779, e4780, e6587, e8241, e8242, e8243, e8244, e8245, e8251, e8252, e8255, e8265, e8266, e11267, e11268, e11269, e11270, e11271, e14649] at *
  omega
theorem n14652 (_v : Vars) (_q : Query _v)  : (e14651 _v) := by
  have p14648 := n14648 _v _q 
  have p14650 := n14650 _v _q 
  exact (Iff.trans p14648 p14650)
theorem n14653 (_v : Vars) (_q : Query _v)  : (e11271 _v) := by
  have p10275 := n10275 _v _q 
  have p14652 := n14652 _v _q 
  simp only [e2384, e2882, e4766, e4774, e4776, e4779, e4780, e6587, e6588, e6589, e6590, e8241, e8242, e8243, e8244, e8245, e8251, e8252, e8255, e8265, e8266, e11267, e11269, e11270, e11271, e14651] at *
  tauto
theorem n14654 (_v : Vars) (_q : Query _v)  : (e14048 _v) := by
  have p12254 := n12254 _v _q 
  have p14052 := n14052 _v _q 
  simp only [e2468, e4785, e4786, e4787, e4788, e4789, e4790, e4791, e4795, e4796, e4797, e4798, e4799, e6630, e6631, e6632, e6633, e8267, e8275, e8278, e8281, e8283, e11278, e11279, e14048, e14051] at *
  tauto
theorem n14655 (_v : Vars) (_q : Query _v)  : (e8278 _v) := by
  have p14654 := n14654 _v _q 
  simp only [e2468, e4785, e4786, e4787, e4788, e4790, e4791, e4795, e4796, e4797, e4798, e6630, e8267, e8275, e8278, e8281, e8283, e11278, e11279, e14048] at *
  tauto
theorem n14656 (_v : Vars) (_q : Query _v)  : (e14058 _v) := by
  have p12294 := n12294 _v _q 
  have p14062 := n14062 _v _q 
  simp only [e2522, e4811, e4812, e4813, e4814, e4815, e4816, e4817, e4821, e4822, e4823, e4824, e4825, e6650, e6651, e6652, e6653, e8284, e8292, e8295, e8298, e8300, e11286, e11287, e14058, e14061] at *
  tauto
theorem n14657 (_v : Vars) (_q : Query _v)  : (e8295 _v) := by
  have p14656 := n14656 _v _q 
  simp only [e2522, e4811, e4812, e4813, e4814, e4816, e4817, e4821, e4822, e4823, e4824, e6650, e8284, e8292, e8295, e8298, e8300, e11286, e11287, e14058] at *
  tauto
theorem n14658 (_v : Vars) (_q : Query _v)  : (e8313 _v) := by
  have p12770 := n12770 _v _q 
  change ((e4840 _v) ↔ (e8307 _v)) at p12770
  simp only [e8313, e8311, e8312, p12770]
theorem n14659 (_v : Vars) (_q : Query _v)  : (e12777 _v) := by
  have p14658 := n14658 _v _q 
  have p14065 := n14065 _v _q 
  change ((e8311 _v) ↔ (e8312 _v)) at p14658
  change ((e6649 _v) ↔ (e11298 _v)) at p14065
  simp only [e12777, e10345, e11299, p14658, p14065]
theorem n14661 (_v : Vars) (_q : Query _v)  : (e14660 _v) := by
  simp only [e5, e6, e12, e41, e46, e111, e2528, e2529, e4834, e4835, e4836, e4837, e4838, e4839, e4852, e8301, e8307, e8310, e8312, e8315, e8317, e8319, e8320, e8321, e8322, e8323, e11298, e11299, e11300, e11301, e11302, e14660] at *
  omega
theorem n14662 (_v : Vars) (_q : Query _v)  : (e12778 _v) := by
  have p14659 := n14659 _v _q 
  have p14661 := n14661 _v _q 
  exact (Iff.trans p14659 p14661)
theorem n14663 (_v : Vars) (_q : Query _v)  : (e11302 _v) := by
  have p10346 := n10346 _v _q 
  have p14662 := n14662 _v _q 
  simp only [e2529, e4836, e4837, e4838, e4839, e4840, e6648, e6649, e8301, e8307, e8310, e8311, e8312, e8315, e8317, e8319, e8320, e8321, e8322, e8323, e10345, e11298, e11300, e11301, e11302, e12778] at *
  tauto
theorem n14664 (_v : Vars) (_q : Query _v)  : (e8334 _v) := by
  have p12783 := n12783 _v _q 
  change ((e4859 _v) ↔ (e8330 _v)) at p12783
  simp only [e8334, e6673, e8333, p12783]
theorem n14666 (_v : Vars) (_q : Query _v)  : (e14665 _v) := by
  have p14664 := n14664 _v _q 
  have p14070 := n14070 _v _q 
  change ((e6673 _v) ↔ (e8333 _v)) at p14664
  change ((e6674 _v) ↔ (e11307 _v)) at p14070
  simp only [e14665, e6675, e11308, p14664, p14070]
theorem n14668 (_v : Vars) (_q : Query _v)  : (e14667 _v) := by
  simp only [e5, e6, e8, e12, e41, e43, e44, e46, e111, e2591, e2592, e4853, e4854, e4855, e4856, e4857, e4858, e4870, e6672, e8324, e8330, e8333, e8335, e8338, e8345, e8346, e8347, e8348, e8349, e11307, e11308, e11309, e11310, e11311, e14667] at *
  omega
theorem n14670 (_v : Vars) (_q : Query _v)  : (e14669 _v) := by
  have p14666 := n14666 _v _q 
  have p14668 := n14668 _v _q 
  exact (Iff.trans p14666 p14668)
theorem n14671 (_v : Vars) (_q : Query _v)  : (e11311 _v) := by
  have p10370 := n10370 _v _q 
  have p14670 := n14670 _v _q 
  simp only [e2592, e2899, e4855, e4856, e4857, e4858, e4859, e6672, e6673, e6674, e6675, e8324, e8330, e8333, e8335, e8338, e8345, e8346, e8347, e8348, e8349, e11307, e11309, e11310, e11311, e14669] at *
  tauto
theorem n14672 (_v : Vars) (_q : Query _v)  : (e14076 _v) := by
  have p10453 := n10453 _v _q 
  have p14080 := n14080 _v _q 
  simp only [e2722, e4872, e4873, e4874, e4875, e4876, e4877, e4878, e4882, e4883, e4884, e4885, e4886, e6742, e6743, e6744, e6745, e8350, e8358, e8361, e8364, e8366, e11318, e11319, e14076, e14079] at *
  tauto
theorem n14673 (_v : Vars) (_q : Query _v)  : (e8361 _v) := by
  have p14672 := n14672 _v _q 
  simp only [e2722, e4872, e4873, e4874, e4875, e4877, e4878, e4882, e4883, e4884, e4885, e6742, e8350, e8358, e8361, e8364, e8366, e11318, e11319, e14076] at *
  tauto
theorem n14674 (_v : Vars) (_q : Query _v)  : (e14086 _v) := by
  have p10513 := n10513 _v _q 
  have p14090 := n14090 _v _q 
  simp only [e2793, e4897, e4898, e4899, e4900, e4901, e4902, e4903, e4907, e4908, e4909, e4910, e4911, e6784, e6785, e6786, e6787, e8367, e8375, e8378, e8381, e8383, e11326, e11327, e14086, e14089] at *
  tauto
theorem n14675 (_v : Vars) (_q : Query _v)  : (e8378 _v) := by
  have p14674 := n14674 _v _q 
  simp only [e2793, e4897, e4898, e4899, e4900, e4902, e4903, e4907, e4908, e4909, e4910, e6784, e8367, e8375, e8378, e8381, e8383, e11326, e11327, e14086] at *
  tauto
theorem n14676 (_v : Vars) (_q : Query _v)  : (e8394 _v) := by
  have p12795 := n12795 _v _q 
  change ((e4926 _v) ↔ (e8390 _v)) at p12795
  simp only [e8394, e6781, e8393, p12795]
theorem n14678 (_v : Vars) (_q : Query _v)  : (e14677 _v) := by
  have p14676 := n14676 _v _q 
  have p14095 := n14095 _v _q 
  change ((e6781 _v) ↔ (e8393 _v)) at p14676
  change ((e6782 _v) ↔ (e11332 _v)) at p14095
  simp only [e14677, e6783, e11333, p14676, p14095]
theorem n14680 (_v : Vars) (_q : Query _v)  : (e14679 _v) := by
  simp only [e5, e6, e8, e10, e12, e41, e46, e111, e266, e267, e2798, e2799, e4920, e4921, e4922, e4923, e4924, e4925, e4937, e6780, e8384, e8390, e8393, e8395, e8398, e8405, e8406, e8407, e8408, e8409, e11332, e11333, e11334, e11335, e11336, e14679] at *
  omega
end
end Assembly
