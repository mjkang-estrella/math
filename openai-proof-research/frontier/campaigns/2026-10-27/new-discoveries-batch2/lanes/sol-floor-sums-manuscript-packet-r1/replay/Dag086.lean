import Dag085
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n12985 (_v : Vars) (_q : Query _v)  : (e12984 _v) := by
  have p11603 := n11603 _v _q 
  change ((e198 _v) ↔ (e5221 _v)) at p11603
  simp only [e12984, e5197, e8668, p11603]
theorem n12987 (_v : Vars) (_q : Query _v)  : (e12986 _v) := by
  simp only [e5, e6, e8, e12, e41, e46, e111, e195, e196, e210, e5208, e5211, e5218, e5219, e5220, e5221, e8668, e12986] at *
theorem n12988 (_v : Vars) (_q : Query _v)  : (e12984 _v) := by
  have p12985 := n12985 _v _q 
  have p12987 := n12987 _v _q 
  exact (Iff.trans p12985 p12987)
theorem n12990 (_v : Vars) (_q : Query _v)  : (e12989 _v) := by
  have p11611 := n11611 _v _q 
  change ((e216 _v) ↔ (e5250 _v)) at p11611
  simp only [e12989, e5225, e8677, p11611]
theorem n12992 (_v : Vars) (_q : Query _v)  : (e12991 _v) := by
  simp only [e5, e6, e10, e12, e41, e46, e111, e212, e213, e214, e5237, e5240, e5247, e5248, e5249, e5250, e8677, e12991] at *
theorem n12993 (_v : Vars) (_q : Query _v)  : (e12989 _v) := by
  have p12990 := n12990 _v _q 
  have p12992 := n12992 _v _q 
  exact (Iff.trans p12990 p12992)
theorem n12994 (_v : Vars) (_q : Query _v)  : (e5274 _v) := by
  have p11613 := n11613 _v _q 
  change ((e276 _v) ↔ (e5270 _v)) at p11613
  simp only [e5274, e5261, e5273, p11613]
theorem n12995 (_v : Vars) (_q : Query _v)  : (e5275 _v) := by
  simp only [e5, e6, e8, e12, e41, e111, e266, e267, e268, e269, e282, e283, e284, e286, e289, e290, e5269, e5270, e5273, e5275] at *
theorem n12996 (_v : Vars) (_q : Query _v)  : (e5274 _v) := by
  have p12994 := n12994 _v _q 
  have p12995 := n12995 _v _q 
  exact (Iff.trans p12994 p12995)
theorem n12998 (_v : Vars) (_q : Query _v)  : (e12997 _v) := by
  have p8691 := n8691 _v _q 
  have p12996 := n12996 _v _q 
  change ((e5260 _v) ↔ (e5276 _v)) at p8691
  change ((e5261 _v) ↔ (e5273 _v)) at p12996
  simp only [e12997, e5262, e5277, p8691, p12996]
theorem n13001 (_v : Vars) (_q : Query _v)  : (e13000 _v) := by
  simp only [e5, e6, e8, e12, e41, e111, e260, e261, e262, e263, e264, e266, e267, e268, e269, e274, e282, e283, e284, e286, e289, e290, e5259, e5269, e5270, e5273, e5276, e5277, e5278, e8694, e8695, e12999, e13000] at *
  omega
theorem n13003 (_v : Vars) (_q : Query _v)  : (e13002 _v) := by
  have p12998 := n12998 _v _q 
  have p13001 := n13001 _v _q 
  exact (Iff.trans p12998 p13001)
theorem n13004 (_v : Vars) (_q : Query _v)  : (e5294 _v) := by
  have p11615 := n11615 _v _q 
  change ((e312 _v) ↔ (e5290 _v)) at p11615
  simp only [e5294, e5281, e5293, p11615]
theorem n13005 (_v : Vars) (_q : Query _v)  : (e5295 _v) := by
  simp only [e5, e6, e10, e12, e41, e266, e267, e304, e305, e318, e319, e320, e322, e325, e326, e5289, e5290, e5293, e5295] at *
theorem n13006 (_v : Vars) (_q : Query _v)  : (e5294 _v) := by
  have p13004 := n13004 _v _q 
  have p13005 := n13005 _v _q 
  exact (Iff.trans p13004 p13005)
theorem n13008 (_v : Vars) (_q : Query _v)  : (e13007 _v) := by
  have p8699 := n8699 _v _q 
  have p13006 := n13006 _v _q 
  change ((e5280 _v) ↔ (e5296 _v)) at p8699
  change ((e5281 _v) ↔ (e5293 _v)) at p13006
  simp only [e13007, e5282, e5297, p8699, p13006]
theorem n13011 (_v : Vars) (_q : Query _v)  : (e13010 _v) := by
  simp only [e5, e6, e10, e12, e41, e266, e267, e298, e299, e300, e301, e302, e304, e305, e310, e318, e319, e320, e322, e325, e326, e5279, e5289, e5290, e5293, e5296, e5297, e5298, e8702, e8703, e13009, e13010] at *
  omega
theorem n13013 (_v : Vars) (_q : Query _v)  : (e13012 _v) := by
  have p13008 := n13008 _v _q 
  have p13011 := n13011 _v _q 
  exact (Iff.trans p13008 p13011)
theorem n13014 (_v : Vars) (_q : Query _v)  : (e5314 _v) := by
  have p11617 := n11617 _v _q 
  change ((e347 _v) ↔ (e5310 _v)) at p11617
  simp only [e5314, e5301, e5313, p11617]
theorem n13015 (_v : Vars) (_q : Query _v)  : (e5315 _v) := by
  simp only [e5, e6, e12, e41, e111, e266, e267, e339, e340, e353, e354, e355, e357, e360, e361, e5309, e5310, e5313, e5315] at *
theorem n13016 (_v : Vars) (_q : Query _v)  : (e5314 _v) := by
  have p13014 := n13014 _v _q 
  have p13015 := n13015 _v _q 
  exact (Iff.trans p13014 p13015)
theorem n13018 (_v : Vars) (_q : Query _v)  : (e13017 _v) := by
  have p8707 := n8707 _v _q 
  have p13016 := n13016 _v _q 
  change ((e5300 _v) ↔ (e5316 _v)) at p8707
  change ((e5301 _v) ↔ (e5313 _v)) at p13016
  simp only [e13017, e5302, e5317, p8707, p13016]
theorem n13021 (_v : Vars) (_q : Query _v)  : (e13020 _v) := by
  simp only [e5, e6, e12, e41, e111, e266, e267, e333, e334, e335, e336, e337, e339, e340, e345, e353, e354, e355, e357, e360, e361, e5299, e5309, e5310, e5313, e5316, e5317, e5318, e8710, e8711, e13019, e13020] at *
  omega
theorem n13023 (_v : Vars) (_q : Query _v)  : (e13022 _v) := by
  have p13018 := n13018 _v _q 
  have p13021 := n13021 _v _q 
  exact (Iff.trans p13018 p13021)
theorem n13024 (_v : Vars) (_q : Query _v)  : (e5334 _v) := by
  have p11619 := n11619 _v _q 
  change ((e377 _v) ↔ (e5330 _v)) at p11619
  simp only [e5334, e5321, e5333, p11619]
theorem n13025 (_v : Vars) (_q : Query _v)  : (e5335 _v) := by
  simp only [e5, e6, e8, e12, e41, e46, e108, e109, e369, e370, e383, e384, e385, e387, e390, e391, e5329, e5330, e5333, e5335] at *
theorem n13026 (_v : Vars) (_q : Query _v)  : (e5334 _v) := by
  have p13024 := n13024 _v _q 
  have p13025 := n13025 _v _q 
  exact (Iff.trans p13024 p13025)
theorem n13028 (_v : Vars) (_q : Query _v)  : (e13027 _v) := by
  have p8715 := n8715 _v _q 
  have p13026 := n13026 _v _q 
  change ((e5320 _v) ↔ (e5336 _v)) at p8715
  change ((e5321 _v) ↔ (e5333 _v)) at p13026
  simp only [e13027, e5322, e5337, p8715, p13026]
theorem n13031 (_v : Vars) (_q : Query _v)  : (e13030 _v) := by
  simp only [e5, e6, e8, e12, e41, e46, e108, e109, e363, e364, e365, e366, e367, e369, e370, e375, e383, e384, e385, e387, e390, e391, e5319, e5329, e5330, e5333, e5336, e5337, e5338, e8718, e8719, e13029, e13030] at *
  omega
theorem n13033 (_v : Vars) (_q : Query _v)  : (e13032 _v) := by
  have p13028 := n13028 _v _q 
  have p13031 := n13031 _v _q 
  exact (Iff.trans p13028 p13031)
theorem n13035 (_v : Vars) (_q : Query _v)  : (e13034 _v) := by
  have p11621 := n11621 _v _q 
  change ((e414 _v) ↔ (e5356 _v)) at p11621
  simp only [e13034, e415, e5359, p11621]
theorem n13037 (_v : Vars) (_q : Query _v)  : (e13036 _v) := by
  simp only [e5, e6, e12, e41, e266, e267, e410, e411, e426, e427, e428, e430, e433, e434, e5355, e5356, e5359, e13036] at *
theorem n13038 (_v : Vars) (_q : Query _v)  : (e13034 _v) := by
  have p13035 := n13035 _v _q 
  have p13037 := n13037 _v _q 
  exact (Iff.trans p13035 p13037)
theorem n13039 (_v : Vars) (_q : Query _v)  : (e8728 _v) := by
  have p8724 := n8724 _v _q 
  have p13038 := n13038 _v _q 
  change ((e5346 _v) ↔ (e8722 _v)) at p8724
  change ((e415 _v) ↔ (e5359 _v)) at p13038
  simp only [e8728, e5347, e8727, p8724, p13038]
theorem n13041 (_v : Vars) (_q : Query _v)  : (e13040 _v) := by
  have p11633 := n11633 _v _q 
  change ((e445 _v) ↔ (e5388 _v)) at p11633
  simp only [e13040, e5364, e8737, p11633]
theorem n13043 (_v : Vars) (_q : Query _v)  : (e13042 _v) := by
  simp only [e5, e6, e8, e10, e12, e41, e46, e111, e435, e436, e457, e5375, e5378, e5385, e5386, e5387, e5388, e8737, e13042] at *
theorem n13044 (_v : Vars) (_q : Query _v)  : (e13040 _v) := by
  have p13041 := n13041 _v _q 
  have p13043 := n13043 _v _q 
  exact (Iff.trans p13041 p13043)
theorem n13045 (_v : Vars) (_q : Query _v)  : (e5407 _v) := by
  have p11635 := n11635 _v _q 
  change ((e480 _v) ↔ (e5403 _v)) at p11635
  simp only [e5407, e5394, e5406, p11635]
theorem n13046 (_v : Vars) (_q : Query _v)  : (e5408 _v) := by
  simp only [e5, e6, e8, e12, e41, e46, e111, e473, e474, e486, e487, e488, e490, e493, e494, e5402, e5403, e5406, e5408] at *
theorem n13047 (_v : Vars) (_q : Query _v)  : (e5407 _v) := by
  have p13045 := n13045 _v _q 
  have p13046 := n13046 _v _q 
  exact (Iff.trans p13045 p13046)
theorem n13049 (_v : Vars) (_q : Query _v)  : (e13048 _v) := by
  have p8745 := n8745 _v _q 
  have p13047 := n13047 _v _q 
  change ((e5393 _v) ↔ (e5409 _v)) at p8745
  change ((e5394 _v) ↔ (e5406 _v)) at p13047
  simp only [e13048, e5395, e5410, p8745, p13047]
theorem n13052 (_v : Vars) (_q : Query _v)  : (e13051 _v) := by
  simp only [e5, e6, e8, e12, e41, e46, e111, e467, e468, e469, e470, e471, e473, e474, e479, e486, e487, e488, e490, e493, e494, e5392, e5402, e5403, e5406, e5409, e5410, e5411, e8748, e8749, e13050, e13051] at *
  omega
theorem n13054 (_v : Vars) (_q : Query _v)  : (e13053 _v) := by
  have p13049 := n13049 _v _q 
  have p13052 := n13052 _v _q 
  exact (Iff.trans p13049 p13052)
theorem n13056 (_v : Vars) (_q : Query _v)  : (e13055 _v) := by
  have p11637 := n11637 _v _q 
  change ((e508 _v) ↔ (e5422 _v)) at p11637
  simp only [e13055, e509, e5425, p11637]
theorem n13058 (_v : Vars) (_q : Query _v)  : (e13057 _v) := by
  simp only [e5, e6, e12, e41, e43, e44, e504, e505, e520, e521, e522, e524, e527, e528, e5421, e5422, e5425, e13057] at *
end
end Assembly
