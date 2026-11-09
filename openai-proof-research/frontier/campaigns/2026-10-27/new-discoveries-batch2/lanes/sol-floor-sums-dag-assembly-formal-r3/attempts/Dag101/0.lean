import Dag100
import generated.th_lemma_4
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n14035 (_v : Vars) (_q : Query _v)  : (e14034 _v) := by
  simp only [e5, e6, e8, e10, e12, e41, e111, e266, e267, e2376, e2377, e2954, e4741, e4742, e4743, e4744, e4745, e4747, e4748, e4752, e4753, e4754, e4755, e6591, e8224, e8232, e8235, e8238, e8239, e8240, e11261, e11262, e14033, e14034] at *
  omega
theorem n14037 (_v : Vars) (_q : Query _v)  : (e14036 _v) := by
  have p14032 := n14032 _v _q 
  have p14035 := n14035 _v _q 
  exact (Iff.trans p14032 p14035)
theorem n14039 (_v : Vars) (_q : Query _v)  : (e14038 _v) := by
  have p12764 := n12764 _v _q 
  change ((e2882 _v) ↔ (e8265 _v)) at p12764
  simp only [e14038, e6589, e11267, p12764]
theorem n14041 (_v : Vars) (_q : Query _v)  : (e14040 _v) := by
  simp only [e5, e6, e8, e10, e12, e41, e111, e266, e267, e2383, e2384, e4765, e8241, e8242, e8243, e8244, e8245, e8265, e11267, e14040] at *
  omega
theorem n14042 (_v : Vars) (_q : Query _v)  : (e14038 _v) := by
  have p14039 := n14039 _v _q 
  have p14041 := n14041 _v _q 
  exact (Iff.trans p14039 p14041)
theorem n14043 (_v : Vars) (_q : Query _v)  : (e8279 _v) := by
  have p12766 := n12766 _v _q 
  change ((e4799 _v) ↔ (e8275 _v)) at p12766
  simp only [e8279, e6632, e8278, p12766]
theorem n14044 (_v : Vars) (_q : Query _v)  : (e8280 _v) := by
  simp only [e5, e6, e8, e12, e41, e46, e2467, e2468, e4783, e4784, e4785, e4786, e4787, e4788, e8267, e8275, e8278, e8280] at *
  omega
theorem n14045 (_v : Vars) (_q : Query _v)  : (e8279 _v) := by
  have p14043 := n14043 _v _q 
  have p14044 := n14044 _v _q 
  exact (Iff.trans p14043 p14044)
theorem n14047 (_v : Vars) (_q : Query _v)  : (e14046 _v) := by
  have p11275 := n11275 _v _q 
  have p14045 := n14045 _v _q 
  change ((e6631 _v) ↔ (e8281 _v)) at p11275
  change ((e6632 _v) ↔ (e8278 _v)) at p14045
  simp only [e14046, e6633, e8282, p11275, p14045]
theorem n14050 (_v : Vars) (_q : Query _v)  : (e14049 _v) := by
  simp only [e5, e6, e8, e12, e41, e46, e2467, e2468, e4783, e4784, e4785, e4786, e4787, e4788, e4790, e4791, e4795, e4796, e4797, e4798, e6630, e8267, e8275, e8278, e8281, e8282, e8283, e11278, e11279, e14048, e14049] at *
  omega
theorem n14052 (_v : Vars) (_q : Query _v)  : (e14051 _v) := by
  have p14047 := n14047 _v _q 
  have p14050 := n14050 _v _q 
  exact (Iff.trans p14047 p14050)
theorem n14053 (_v : Vars) (_q : Query _v)  : (e8296 _v) := by
  have p12768 := n12768 _v _q 
  change ((e4825 _v) ↔ (e8292 _v)) at p12768
  simp only [e8296, e6652, e8295, p12768]
theorem n14054 (_v : Vars) (_q : Query _v)  : (e8297 _v) := by
  simp only [e5, e6, e12, e41, e46, e111, e2521, e2522, e4809, e4810, e4811, e4812, e4813, e4814, e8284, e8292, e8295, e8297] at *
  omega
theorem n14055 (_v : Vars) (_q : Query _v)  : (e8296 _v) := by
  have p14053 := n14053 _v _q 
  have p14054 := n14054 _v _q 
  exact (Iff.trans p14053 p14054)
theorem n14057 (_v : Vars) (_q : Query _v)  : (e14056 _v) := by
  have p11283 := n11283 _v _q 
  have p14055 := n14055 _v _q 
  change ((e6651 _v) ↔ (e8298 _v)) at p11283
  change ((e6652 _v) ↔ (e8295 _v)) at p14055
  simp only [e14056, e6653, e8299, p11283, p14055]
theorem n14060 (_v : Vars) (_q : Query _v)  : (e14059 _v) := by
  simp only [e5, e6, e12, e41, e46, e111, e2521, e2522, e4809, e4810, e4811, e4812, e4813, e4814, e4816, e4817, e4821, e4822, e4823, e4824, e6650, e8284, e8292, e8295, e8298, e8299, e8300, e11286, e11287, e14058, e14059] at *
  omega
theorem n14062 (_v : Vars) (_q : Query _v)  : (e14061 _v) := by
  have p14057 := n14057 _v _q 
  have p14060 := n14060 _v _q 
  exact (Iff.trans p14057 p14060)
theorem n14064 (_v : Vars) (_q : Query _v)  : (e14063 _v) := by
  simp only [e5, e6, e12, e41, e46, e111, e2528, e2529, e4852, e8315, e8317, e8319, e8320, e8321, e8322, e11298, e14063] at *
  omega
theorem n14065 (_v : Vars) (_q : Query _v)  : (e12775 _v) := by
  have p12776 := n12776 _v _q 
  have p14064 := n14064 _v _q 
  exact (Iff.trans p12776 p14064)
theorem n14067 (_v : Vars) (_q : Query _v)  : (e14066 _v) := by
  have p12789 := n12789 _v _q 
  change ((e2899 _v) ↔ (e8348 _v)) at p12789
  simp only [e14066, e6674, e11307, p12789]
theorem n14069 (_v : Vars) (_q : Query _v)  : (e14068 _v) := by
  simp only [e5, e6, e8, e12, e41, e43, e44, e46, e111, e2591, e2592, e4870, e8335, e8338, e8345, e8346, e8347, e8348, e11307, e14068] at *
  omega
theorem n14070 (_v : Vars) (_q : Query _v)  : (e14066 _v) := by
  have p14067 := n14067 _v _q 
  have p14069 := n14069 _v _q 
  exact (Iff.trans p14067 p14069)
theorem n14071 (_v : Vars) (_q : Query _v)  : (e8362 _v) := by
  have p12791 := n12791 _v _q 
  change ((e4886 _v) ↔ (e8358 _v)) at p12791
  simp only [e8362, e6744, e8361, p12791]
theorem n14072 (_v : Vars) (_q : Query _v)  : (e8363 _v) := by
  simp only [e5, e6, e10, e12, e41, e46, e111, e2721, e2722, e2987, e4871, e4872, e4873, e4874, e4875, e8350, e8358, e8361, e8363] at *
  omega
theorem n14073 (_v : Vars) (_q : Query _v)  : (e8362 _v) := by
  have p14071 := n14071 _v _q 
  have p14072 := n14072 _v _q 
  exact (Iff.trans p14071 p14072)
theorem n14075 (_v : Vars) (_q : Query _v)  : (e14074 _v) := by
  have p11315 := n11315 _v _q 
  have p14073 := n14073 _v _q 
  change ((e6743 _v) ↔ (e8364 _v)) at p11315
  change ((e6744 _v) ↔ (e8361 _v)) at p14073
  simp only [e14074, e6745, e8365, p11315, p14073]
theorem n14078 (_v : Vars) (_q : Query _v)  : (e14077 _v) := by
  simp only [e5, e6, e10, e12, e41, e46, e111, e2721, e2722, e2987, e4871, e4872, e4873, e4874, e4875, e4877, e4878, e4882, e4883, e4884, e4885, e6742, e8350, e8358, e8361, e8364, e8365, e8366, e11318, e11319, e14076, e14077] at *
  omega
theorem n14080 (_v : Vars) (_q : Query _v)  : (e14079 _v) := by
  have p14075 := n14075 _v _q 
  have p14078 := n14078 _v _q 
  exact (Iff.trans p14075 p14078)
theorem n14081 (_v : Vars) (_q : Query _v)  : (e8379 _v) := by
  have p12793 := n12793 _v _q 
  change ((e4911 _v) ↔ (e8375 _v)) at p12793
  simp only [e8379, e6786, e8378, p12793]
theorem n14082 (_v : Vars) (_q : Query _v)  : (e8380 _v) := by
  simp only [e5, e6, e8, e10, e12, e41, e46, e111, e266, e267, e2792, e2793, e4895, e4896, e4897, e4898, e4899, e4900, e8367, e8375, e8378, e8380] at *
  omega
theorem n14083 (_v : Vars) (_q : Query _v)  : (e8379 _v) := by
  have p14081 := n14081 _v _q 
  have p14082 := n14082 _v _q 
  exact (Iff.trans p14081 p14082)
theorem n14085 (_v : Vars) (_q : Query _v)  : (e14084 _v) := by
  have p11323 := n11323 _v _q 
  have p14083 := n14083 _v _q 
  change ((e6785 _v) ↔ (e8381 _v)) at p11323
  change ((e6786 _v) ↔ (e8378 _v)) at p14083
  simp only [e14084, e6787, e8382, p11323, p14083]
theorem n14088 (_v : Vars) (_q : Query _v)  : (e14087 _v) := by
  simp only [e5, e6, e8, e10, e12, e41, e46, e111, e266, e267, e2792, e2793, e4895, e4896, e4897, e4898, e4899, e4900, e4902, e4903, e4907, e4908, e4909, e4910, e6784, e8367, e8375, e8378, e8381, e8382, e8383, e11326, e11327, e14086, e14087] at *
  omega
theorem n14090 (_v : Vars) (_q : Query _v)  : (e14089 _v) := by
  have p14085 := n14085 _v _q 
  have p14088 := n14088 _v _q 
  exact (Iff.trans p14085 p14088)
theorem n14092 (_v : Vars) (_q : Query _v)  : (e14091 _v) := by
  have p12801 := n12801 _v _q 
  change ((e2914 _v) ↔ (e8408 _v)) at p12801
  simp only [e14091, e6782, e11332, p12801]
theorem n14094 (_v : Vars) (_q : Query _v)  : (e14093 _v) := by
  simp only [e5, e6, e8, e10, e12, e41, e46, e111, e266, e267, e2798, e2799, e4937, e8395, e8398, e8405, e8406, e8407, e8408, e11332, e14093] at *
  omega
theorem n14095 (_v : Vars) (_q : Query _v)  : (e14091 _v) := by
  have p14092 := n14092 _v _q 
  have p14094 := n14094 _v _q 
  exact (Iff.trans p14092 p14094)
theorem n14096 (_v : Vars) (_q : Query _v) (h2771 : (e2771 _v)) : (e496 _v) := by
  have p3130 := n3130 _v _q 
  have p8415 := n8415 _v _q h2771
  exact FloorCertificate.node_14096 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p3130 p8415
theorem n14097 (_v : Vars) (_q : Query _v) (h2771 : (e2771 _v)) : (e5195 _v) := by
  have p13991 := n13991 _v _q 
  have p14096 := n14096 _v _q h2771
  simp only [e196, e496, e5195, e6720, e13990] at *
  tauto
theorem n14098 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e2303 _v) := by
  have p12815 := n12815 _v _q 
  have p12826 := n12826 _v _q h6591
  simp only [e2303, e2746, e6758, e12814] at *
  tauto
theorem n14099 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e6656 _v) := by
  have p11135 := n11135 _v _q 
  have p12817 := n12817 _v _q h6591
  simp only [e2482, e2536, e6636, e6656, e11134] at *
  tauto
theorem n14100 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e196 _v) := by
  have p12689 := n12689 _v _q 
  have p14099 := n14099 _v _q h6591
  simp only [e196, e2536, e6656, e12688] at *
  tauto
theorem n14101 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e6720 _v) := by
  have p13991 := n13991 _v _q 
  have p14100 := n14100 _v _q h6591
  simp only [e196, e496, e5195, e6720, e13990] at *
  tauto
theorem n14102 (_v : Vars) (_q : Query _v) (h6531 : (e6531 _v)) : (e13 _v) := by
  have p12820 := n12820 _v _q 
  have p11358 := n11358 _v _q h6531
  simp only [e13, e2254, e6531, e12819] at *
  tauto
theorem n14103 (_v : Vars) (_q : Query _v) (h2364 : (e2364 _v)) (h6531 : (e6531 _v)) : (e7489 _v) := by
  have p8527 := n8527 _v _q h2364
  have p11358 := n11358 _v _q h6531
  have p5257 := n5257 _v _q 
  have p14102 := n14102 _v _q h6531
  have p10896 := n10896 _v _q 
  exact FloorCertificate.node_14103 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e110 _v) p8527 p11358 p5257 p14102 p10896
end
end Assembly
