import Dag119
import generated.th_lemma_6
import generated.th_lemma_7
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n15057 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e5392 _v) := by
  have p10896 := n10896 _v _q 
  have p11345 := n11345 _v _q h6591
  have p8663 := n8663 _v _q 
  have p11376 := n11376 _v _q 
  have p11375 := n11375 _v _q 
  have p5391 := n5391 _v _q 
  exact FloorCertificate.node_15057 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p10896 p11345 p8663 p11376 p11375 p5391
theorem n15058 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e5403 _v) := by
  have p14577 := n14577 _v _q 
  have p15057 := n15057 _v _q h6591
  simp only [e474, e488, e490, e493, e494, e5392, e5402, e5403, e5406] at *
  tauto
theorem n15059 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e7895 _v) := by
  have p14589 := n14589 _v _q 
  have p12811 := n12811 _v _q h6591
  simp only [e251, e4367, e4368, e4369, e4370, e6694, e7887, e7895, e7898] at *
  tauto
theorem n15060 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e6525 _v) := by
  have p11376 := n11376 _v _q 
  have p11345 := n11345 _v _q h6591
  have p8663 := n8663 _v _q 
  have p11375 := n11375 _v _q 
  have p10896 := n10896 _v _q 
  exact FloorCertificate.node_15060 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e110 _v) p11376 p11345 p8663 p11375 p10896
theorem n15061 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e8174 _v) := by
  have p14634 := n14634 _v _q 
  have p15060 := n15060 _v _q h6591
  simp only [e2242, e4673, e4674, e4675, e4676, e6525, e8166, e8174, e8177] at *
  tauto
theorem n15062 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e6630 _v) := by
  have p8442 := n8442 _v _q 
  have p15013 := n15013 _v _q h6591
  simp only [e2402, e2468, e6600, e6630, e8441] at *
  tauto
theorem n15063 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e8275 _v) := by
  have p14655 := n14655 _v _q 
  have p15062 := n15062 _v _q h6591
  simp only [e2468, e4785, e4786, e4787, e4788, e6630, e8267, e8275, e8278] at *
  tauto
theorem n15064 (_v : Vars) (_q : Query _v)  : (e8368 _v) := by
  simp only [e4897, e4898, e4899, e4900, e8367, e8368] at *
  tauto
theorem n15065 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e8375 _v) := by
  have p14675 := n14675 _v _q 
  have p12827 := n12827 _v _q h6591
  simp only [e2793, e4897, e4898, e4899, e4900, e6784, e8367, e8375, e8378] at *
  tauto
theorem n15066 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e4899 _v) := by
  have p15064 := n15064 _v _q 
  have p15065 := n15065 _v _q h6591
  simp only [e4897, e4898, e4899, e4900, e8367, e8368, e8375] at *
  tauto
theorem n15067 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e6650 _v) := by
  have p11376 := n11376 _v _q 
  have p10896 := n10896 _v _q 
  have p11345 := n11345 _v _q h6591
  have p5391 := n5391 _v _q 
  have p8663 := n8663 _v _q 
  have p11375 := n11375 _v _q 
  exact FloorCertificate.node_15067 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p11376 p10896 p11345 p5391 p8663 p11375
theorem n15068 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e8292 _v) := by
  have p14657 := n14657 _v _q 
  have p15067 := n15067 _v _q h6591
  simp only [e2522, e4811, e4812, e4813, e4814, e6650, e8284, e8292, e8295] at *
  tauto
theorem n15069 (_v : Vars) (_q : Query _v) (h6501 : (e6501 _v)) : (e6600 _v) := by
  have p11339 := n11339 _v _q 
  have p8554 := n8554 _v _q h6501
  simp only [e2179, e2402, e6501, e6600, e11338] at *
  tauto
theorem n15070 (_v : Vars) (_q : Query _v) (h6501 : (e6501 _v)) : (e7416 _v) := by
  have p14534 := n14534 _v _q 
  have p15069 := n15069 _v _q h6501
  simp only [e2402, e3937, e3939, e3942, e3943, e6600, e7415, e7416, e7419] at *
  tauto
theorem n15071 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) : (e2402 _v) := by
  have p8442 := n8442 _v _q 
  have p8438 := n8438 _v _q h2468
  simp only [e2402, e2468, e6630, e8441] at *
  tauto
theorem n15072 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) : (e3929 _v) := by
  have p14484 := n14484 _v _q 
  have p15071 := n15071 _v _q h2468
  simp only [e2402, e3919, e3920, e3921, e3922, e3923, e3929, e6600, e7422] at *
  tauto
theorem n15073 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) : (e3919 _v) := by
  have p14797 := n14797 _v _q 
  have p15072 := n15072 _v _q h2468
  simp only [e3919, e3920, e3921, e3922, e3923, e3924, e3929] at *
  tauto
theorem n15074 (_v : Vars) (_q : Query _v) (h5392 : (e5392 _v)) : (e5392 _v) := by
  exact h5392
theorem n15075 (_v : Vars) (_q : Query _v) (h5392 : (e5392 _v)) : (e6720 _v) := by
  have p5255 := n5255 _v _q 
  have p15074 := n15074 _v _q h5392
  exact FloorCertificate.node_15075 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p5255 p15074
theorem n15076 (_v : Vars) (_q : Query _v) (h5392 : (e5392 _v)) : (e6830 _v) := by
  have p14629 := n14629 _v _q 
  have p15075 := n15075 _v _q h5392
  simp only [e496, e3069, e3071, e3074, e3075, e6720, e6829, e6830, e6833] at *
  tauto
theorem n15077 (_v : Vars) (_q : Query _v)  : (e10986 _v) := by
  have p14560 := n14560 _v _q 
  simp only [e2680, e4199, e4200, e4201, e4202, e6716, e7703, e7709, e7712, e7714, e7717, e7724, e7725, e7726, e7727, e7728, e10986, e10988, e10989, e10990] at *
  tauto
theorem n15078 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) (h5362 : (e5362 _v)) (h5392 : (e5392 _v)) : (e6716 _v) := by
  have p7488 := n7488 _v _q h5362
  have p8438 := n8438 _v _q h2468
  have p15074 := n15074 _v _q h5392
  exact FloorCertificate.node_15078 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p7488 p8438 p15074
theorem n15079 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) (h5362 : (e5362 _v)) (h5392 : (e5392 _v)) : (e7727 _v) := by
  have p15077 := n15077 _v _q 
  have p15078 := n15078 _v _q h2468 h5362 h5392
  simp only [e2680, e6716, e7714, e7717, e7724, e7725, e7726, e7727, e10986] at *
  tauto
theorem n15080 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) : (e5223 _v) := by
  have p8472 := n8472 _v _q 
  have p7488 := n7488 _v _q h5362
  simp only [e214, e436, e5223, e5362, e8471] at *
  tauto
theorem n15081 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) : (e5250 _v) := by
  have p14996 := n14996 _v _q 
  have p15080 := n15080 _v _q h5362
  simp only [e214, e5223, e5237, e5240, e5247, e5248, e5249, e5250, e8677] at *
  tauto
theorem n15082 (_v : Vars) (_q : Query _v) (h2296 : (e2296 _v)) : (e4314 _v) := by
  have p14704 := n14704 _v _q 
  have p11405 := n11405 _v _q h2296
  simp only [e2585, e4306, e4307, e4311, e4312, e4313, e4314, e6676, e7836] at *
  tauto
theorem n15083 (_v : Vars) (_q : Query _v) (h2296 : (e2296 _v)) : (e4306 _v) := by
  have p14984 := n14984 _v _q 
  have p15082 := n15082 _v _q h2296
  simp only [e4306, e4307, e4311, e4312, e4313, e4314, e4964] at *
  tauto
theorem n15084 (_v : Vars) (_q : Query _v)  : (e8473 _v) := by
  simp only [e5375, e5378, e5385, e5386, e5387, e8473] at *
  tauto
theorem n15085 (_v : Vars) (_q : Query _v)  : (e8737 _v) := by
  have p14206 := n14206 _v _q 
  simp only [e436, e440, e441, e442, e443, e5360, e5362, e5370, e5373, e5375, e5378, e5385, e5386, e5387, e5388, e5389, e8737, e8739, e8740, e8741] at *
  tauto
theorem n15086 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) : (e5388 _v) := by
  have p15085 := n15085 _v _q 
  have p7488 := n7488 _v _q h5362
  simp only [e436, e5362, e5375, e5378, e5385, e5386, e5387, e5388, e8737] at *
  tauto
theorem n15087 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) : (e5378 _v) := by
  have p15084 := n15084 _v _q 
  have p15086 := n15086 _v _q h5362
  simp only [e5375, e5378, e5385, e5386, e5387, e5388, e8473] at *
  tauto
theorem n15088 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) : (e2179 _v) := by
  have p11339 := n11339 _v _q 
  have p15071 := n15071 _v _q h2468
  simp only [e2179, e2402, e6600, e11338] at *
  tauto
theorem n15089 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) : (e4616 _v) := by
  have p14684 := n14684 _v _q 
  have p15088 := n15088 _v _q h2468
  simp only [e2179, e3158, e3159, e3160, e3161, e3162, e4616, e6501, e8109] at *
  tauto
theorem n15090 (_v : Vars) (_q : Query _v)  : (e7821 _v) := by
  simp only [e488, e490, e493, e494, e5402, e7821] at *
  tauto
theorem n15091 (_v : Vars) (_q : Query _v) (h5392 : (e5392 _v)) : (e5403 _v) := by
  have p14577 := n14577 _v _q 
  have p15074 := n15074 _v _q h5392
  simp only [e474, e488, e490, e493, e494, e5392, e5402, e5403, e5406] at *
  tauto
theorem n15092 (_v : Vars) (_q : Query _v) (h5392 : (e5392 _v)) : (e488 _v) := by
  have p15090 := n15090 _v _q 
  have p15091 := n15091 _v _q h5392
  simp only [e488, e490, e493, e494, e5402, e5403, e7821] at *
  tauto
theorem n15093 (_v : Vars) (_q : Query _v) (h2296 : (e2296 _v)) : (e4466 _v) := by
  have p14604 := n14604 _v _q 
  have p12828 := n12828 _v _q h2296
  simp only [e2125, e4458, e4459, e4463, e4464, e4465, e4466, e6480, e7977] at *
  tauto
theorem n15094 (_v : Vars) (_q : Query _v) (h2296 : (e2296 _v)) : (e4459 _v) := by
  have p8443 := n8443 _v _q 
  have p15093 := n15093 _v _q h2296
  simp only [e4458, e4459, e4463, e4464, e4465, e4466, e4482] at *
  tauto
theorem n15095 (_v : Vars) (_q : Query _v) (h2296 : (e2296 _v)) : (e48 _v) := by
  have p10893 := n10893 _v _q 
  have p5257 := n5257 _v _q 
  have p8583 := n8583 _v _q h2296
  exact FloorCertificate.node_15095 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p10893 p5257 p8583
theorem n15096 (_v : Vars) (_q : Query _v) (h2296 : (e2296 _v)) : (e60 _v) := by
  have p14152 := n14152 _v _q 
  have p15095 := n15095 _v _q h2296
  simp only [e48, e51, e52, e57, e58, e59, e60, e5108, e5125] at *
  tauto
theorem n15097 (_v : Vars) (_q : Query _v) (h2296 : (e2296 _v)) : (e51 _v) := by
  have p14962 := n14962 _v _q 
  have p15096 := n15096 _v _q h2296
  simp only [e51, e52, e57, e58, e59, e60, e77] at *
  tauto
theorem n15098 (_v : Vars) (_q : Query _v)  : (e3157 _v) := by
  simp only [e3132, e3133, e3137, e3138, e3139, e3157] at *
  tauto
theorem n15099 (_v : Vars) (_q : Query _v) (h2296 : (e2296 _v)) : (e3140 _v) := by
  have p14358 := n14358 _v _q 
  have p8583 := n8583 _v _q h2296
  simp only [e2296, e3132, e3133, e3137, e3138, e3139, e3140, e6549, e6885] at *
  tauto
theorem n15100 (_v : Vars) (_q : Query _v) (h2296 : (e2296 _v)) : (e3133 _v) := by
  have p15098 := n15098 _v _q 
  have p15099 := n15099 _v _q h2296
  simp only [e3132, e3133, e3137, e3138, e3139, e3140, e3157] at *
  tauto
theorem n15101 (_v : Vars) (_q : Query _v) (h2296 : (e2296 _v)) : (e4575 _v) := by
  have p14696 := n14696 _v _q 
  have p12830 := n12830 _v _q h2296
  simp only [e1995, e4567, e4568, e4572, e4573, e4574, e4575, e6423, e8066] at *
  tauto
end
end Assembly
