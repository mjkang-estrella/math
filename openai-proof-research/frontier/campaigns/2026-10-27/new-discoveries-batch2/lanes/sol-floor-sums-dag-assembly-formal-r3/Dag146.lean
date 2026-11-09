import Dag145
import generated.th_lemma_12
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n16243 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e8035 _v) := by
  have p14871 := n14871 _v _q 
  have p16242 := n16242 _v _q h6792
  simp only [e2475, e4544, e4545, e4546, e4547, e8029, e8035, e8038, e8040] at *
  tauto
theorem n16244 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e4562 _v) := by
  have p15155 := n15155 _v _q 
  have p14873 := n14873 _v _q h6792
  simp only [e4562, e4563, e4564, e4565, e8052, e8053, e8060] at *
  tauto
theorem n16245 (_v : Vars) (_q : Query _v)  : (e8069 _v) := by
  simp only [e7370, e7371, e7372, e7373, e7374, e8069] at *
  tauto
theorem n16246 (_v : Vars) (_q : Query _v)  : (e7370 _v) := by
  have p16245 := n16245 _v _q 
  have p14796 := n14796 _v _q 
  simp only [e7370, e7371, e7372, e7373, e7374, e7391, e8069] at *
  tauto
theorem n16247 (_v : Vars) (_q : Query _v) (h3852 : (e3852 _v)) : (e3852 _v) := by
  exact h3852
theorem n16248 (_v : Vars) (_q : Query _v) (h3852 : (e3852 _v)) : (e7350 _v) := by
  have p14790 := n14790 _v _q 
  have p16247 := n16247 _v _q h3852
  simp only [e3849, e3850, e3851, e3852, e7350, e7351] at *
  tauto
theorem n16249 (_v : Vars) (_q : Query _v) (h3852 : (e3852 _v)) : (e2139 _v) := by
  have p14471 := n14471 _v _q 
  have p16248 := n16248 _v _q h3852
  simp only [e2139, e3849, e3850, e3851, e3852, e7350, e7358, e7361] at *
  tauto
theorem n16250 (_v : Vars) (_q : Query _v) (h3855 : (e3855 _v)) : (e3855 _v) := by
  exact h3855
theorem n16251 (_v : Vars) (_q : Query _v) (h3852 : (e3852 _v)) (h3855 : (e3855 _v)) : (e7489 _v) := by
  have p16246 := n16246 _v _q 
  have p16249 := n16249 _v _q h3852
  have p16247 := n16247 _v _q h3852
  have p16250 := n16250 _v _q h3855
  exact FloorCertificate.node_16251 (e2 _v) (e7 _v) (e17 _v) (e110 _v) (e2933 _v) (e3846 _v) p16246 p16249 p16247 p16250
theorem n16252 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e4608 _v) := by
  have p15033 := n15033 _v _q 
  have p14875 := n14875 _v _q h6792
  simp only [e4608, e4609, e4610, e4611, e8095, e8096, e8103] at *
  tauto
theorem n16253 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e4648 _v) := by
  have p15027 := n15027 _v _q 
  have p14885 := n14885 _v _q h6792
  simp only [e4648, e4649, e4650, e4651, e8149, e8150, e8157] at *
  tauto
theorem n16254 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e4675 _v) := by
  have p15965 := n15965 _v _q 
  have p14887 := n14887 _v _q h6792
  simp only [e4673, e4674, e4675, e4676, e8166, e8167, e8174] at *
  tauto
theorem n16255 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e4720 _v) := by
  have p15030 := n15030 _v _q 
  have p14892 := n14892 _v _q h6792
  simp only [e4718, e4719, e4720, e4721, e8206, e8207, e8214] at *
  tauto
theorem n16256 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e3152 _v) := by
  have p15776 := n15776 _v _q 
  have p14894 := n14894 _v _q h6792
  simp only [e3150, e3152, e3155, e3156, e6878, e6879, e8223] at *
  tauto
theorem n16257 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e4742 _v) := by
  have p15036 := n15036 _v _q 
  have p14896 := n14896 _v _q h6792
  simp only [e4742, e4743, e4744, e4745, e8224, e8225, e8232] at *
  tauto
theorem n16258 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e4787 _v) := by
  have p15670 := n15670 _v _q 
  have p14903 := n14903 _v _q h6792
  simp only [e4785, e4786, e4787, e4788, e8267, e8268, e8275] at *
  tauto
theorem n16259 (_v : Vars) (_q : Query _v)  : (e8285 _v) := by
  simp only [e4811, e4812, e4813, e4814, e8284, e8285] at *
  tauto
theorem n16260 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e4813 _v) := by
  have p16259 := n16259 _v _q 
  have p14905 := n14905 _v _q h6792
  simp only [e4811, e4812, e4813, e4814, e8284, e8285, e8292] at *
  tauto
theorem n16261 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e2529 _v) := by
  have p12781 := n12781 _v _q 
  have p13992 := n13992 _v _q h6792
  simp only [e2529, e2536, e6656, e12780] at *
  tauto
theorem n16262 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e8307 _v) := by
  have p14906 := n14906 _v _q 
  have p16261 := n16261 _v _q h6792
  simp only [e2529, e4836, e4837, e4838, e4839, e8301, e8307, e8310, e8312] at *
  tauto
theorem n16263 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e2592 _v) := by
  have p8663 := n8663 _v _q 
  have p10895 := n10895 _v _q h6792
  have p10896 := n10896 _v _q 
  exact FloorCertificate.node_16263 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8663 p10895 p10896
theorem n16264 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e8330 _v) := by
  have p14907 := n14907 _v _q 
  have p16263 := n16263 _v _q h6792
  simp only [e2592, e4855, e4856, e4857, e4858, e6672, e8324, e8330, e8333] at *
  tauto
theorem n16265 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e4872 _v) := by
  have p14999 := n14999 _v _q 
  have p14909 := n14909 _v _q h6792
  simp only [e4872, e4873, e4874, e4875, e8350, e8351, e8358] at *
  tauto
theorem n16266 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e4899 _v) := by
  have p15064 := n15064 _v _q 
  have p14911 := n14911 _v _q h6792
  simp only [e4897, e4898, e4899, e4900, e8367, e8368, e8375] at *
  tauto
theorem n16267 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e2799 _v) := by
  have p8663 := n8663 _v _q 
  have p10895 := n10895 _v _q h6792
  exact FloorCertificate.node_16267 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8663 p10895
theorem n16268 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e8390 _v) := by
  have p14912 := n14912 _v _q 
  have p16267 := n16267 _v _q h6792
  simp only [e2799, e4922, e4923, e4924, e4925, e6780, e8384, e8390, e8393] at *
  tauto
theorem n16269 (_v : Vars) (_q : Query _v) (h7749 : (e7749 _v)) : (e7749 _v) := by
  exact h7749
theorem n16270 (_v : Vars) (_q : Query _v) (h4464 : (e4464 _v)) (h7749 : (e7749 _v)) : (e7489 _v) := by
  have p16269 := n16269 _v _q h7749
  have p14940 := n14940 _v _q h4464
  have p14938 := n14938 _v _q h4464
  have p8444 := n8444 _v _q h4464
  exact FloorCertificate.node_16270 (e2 _v) (e7 _v) (e17 _v) (e110 _v) (e2932 _v) (e4215 _v) p16269 p14940 p14938 p8444
theorem n16271 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e214 _v) := by
  have p8663 := n8663 _v _q 
  have p11376 := n11376 _v _q 
  have p11345 := n11345 _v _q h6591
  have p5391 := n5391 _v _q 
  have p11375 := n11375 _v _q 
  exact FloorCertificate.node_16271 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8663 p11376 p11345 p5391 p11375
theorem n16272 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e5232 _v) := by
  have p14731 := n14731 _v _q 
  have p16271 := n16271 _v _q h6591
  simp only [e214, e225, e227, e230, e231, e5223, e5231, e5232, e5235] at *
  tauto
theorem n16273 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e70 _v) := by
  have p15648 := n15648 _v _q 
  have p15008 := n15008 _v _q h6591
  simp only [e70, e72, e75, e76, e5118, e5119, e7441] at *
  tauto
theorem n16274 (_v : Vars) (_q : Query _v)  : (e7799 _v) := by
  simp only [e4283, e4284, e4285, e4286, e7798, e7799] at *
  tauto
theorem n16275 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e7804 _v) := by
  have p14837 := n14837 _v _q 
  have p14098 := n14098 _v _q h6591
  simp only [e2303, e4283, e4284, e4285, e4286, e7798, e7804, e7807, e7809] at *
  tauto
theorem n16276 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e4285 _v) := by
  have p16274 := n16274 _v _q 
  have p16275 := n16275 _v _q h6591
  simp only [e4283, e4284, e4285, e4286, e7798, e7799, e7804] at *
  tauto
theorem n16277 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e79 _v) := by
  have p12546 := n12546 _v _q 
  have p12817 := n12817 _v _q h6591
  simp only [e79, e2482, e6636, e12545] at *
  tauto
theorem n16278 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e5135 _v) := by
  have p14729 := n14729 _v _q 
  have p16277 := n16277 _v _q h6591
  simp only [e79, e89, e91, e94, e95, e5134, e5135, e5138, e5140] at *
  tauto
theorem n16279 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e91 _v) := by
  have p16235 := n16235 _v _q 
  have p16278 := n16278 _v _q h6591
  simp only [e89, e91, e94, e95, e5134, e5135, e7983] at *
  tauto
theorem n16280 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e4096 _v) := by
  have p15703 := n15703 _v _q 
  have p15011 := n15011 _v _q h6591
  simp only [e4096, e4097, e4098, e4099, e7589, e7590, e7597] at *
  tauto
theorem n16281 (_v : Vars) (_q : Query _v)  : (e7635 _v) := by
  simp only [e4139, e4140, e4141, e4142, e7634, e7635] at *
  tauto
theorem n16282 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e2358 _v) := by
  have p8451 := n8451 _v _q 
  have p14098 := n14098 _v _q h6591
  simp only [e2303, e2358, e7807, e8450] at *
  tauto
theorem n16283 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e7640 _v) := by
  have p14828 := n14828 _v _q 
  have p16282 := n16282 _v _q h6591
  simp only [e2358, e4139, e4140, e4141, e4142, e6571, e7634, e7640, e7643] at *
  tauto
theorem n16284 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e4139 _v) := by
  have p16281 := n16281 _v _q 
  have p16283 := n16283 _v _q h6591
  simp only [e4139, e4140, e4141, e4142, e7634, e7635, e7640] at *
  tauto
theorem n16285 (_v : Vars) (_q : Query _v)  : (e8302 _v) := by
  simp only [e4836, e4837, e4838, e4839, e8301, e8302] at *
  tauto
theorem n16286 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e2529 _v) := by
  have p11387 := n11387 _v _q 
  have p14098 := n14098 _v _q h6591
  simp only [e2303, e2529, e7807, e11386] at *
  tauto
theorem n16287 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e8307 _v) := by
  have p14906 := n14906 _v _q 
  have p16286 := n16286 _v _q h6591
  simp only [e2529, e4836, e4837, e4838, e4839, e8301, e8307, e8310, e8312] at *
  tauto
end
end Assembly
