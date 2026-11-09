import Dag118
import generated.th_lemma_6
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n15012 (_v : Vars) (_q : Query _v)  : (e7633 _v) := by
  simp only [e3937, e3939, e3942, e3943, e7415, e7633] at *
  tauto
theorem n15013 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e6600 _v) := by
  have p11339 := n11339 _v _q 
  have p11383 := n11383 _v _q h6591
  simp only [e2179, e2402, e6501, e6600, e11338] at *
  tauto
theorem n15014 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e7416 _v) := by
  have p14534 := n14534 _v _q 
  have p15013 := n15013 _v _q h6591
  simp only [e2402, e3937, e3939, e3942, e3943, e6600, e7415, e7416, e7419] at *
  tauto
theorem n15015 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e3937 _v) := by
  have p15012 := n15012 _v _q 
  have p15014 := n15014 _v _q h6591
  simp only [e3937, e3939, e3942, e3943, e7415, e7416, e7633] at *
  tauto
theorem n15016 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e7992 _v) := by
  have p14606 := n14606 _v _q 
  have p12821 := n12821 _v _q h6591
  simp only [e2697, e4486, e4487, e4488, e4489, e6732, e7984, e7992, e7995] at *
  tauto
theorem n15017 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e6454 _v) := by
  have p11376 := n11376 _v _q 
  have p10896 := n10896 _v _q 
  have p11345 := n11345 _v _q h6591
  exact FloorCertificate.node_15017 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e110 _v) p11376 p10896 p11345
theorem n15018 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e7955 _v) := by
  have p14601 := n14601 _v _q 
  have p15017 := n15017 _v _q h6591
  simp only [e2061, e4434, e4435, e4436, e4437, e6454, e7947, e7955, e7958] at *
  tauto
theorem n15019 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e6684 _v) := by
  have p11345 := n11345 _v _q h6591
  have p5391 := n5391 _v _q 
  exact FloorCertificate.node_15019 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p11345 p5391
theorem n15020 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e7554 _v) := by
  have p14515 := n14515 _v _q 
  have p15019 := n15019 _v _q h6591
  simp only [e2598, e4054, e4055, e4056, e4057, e6684, e7546, e7554, e7557] at *
  tauto
theorem n15021 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e6549 _v) := by
  have p11375 := n11375 _v _q 
  have p8663 := n8663 _v _q 
  have p11376 := n11376 _v _q 
  have p11345 := n11345 _v _q h6591
  have p10896 := n10896 _v _q 
  exact FloorCertificate.node_15021 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e110 _v) p11375 p8663 p11376 p11345 p10896
theorem n15022 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e6879 _v) := by
  have p14643 := n14643 _v _q 
  have p15021 := n15021 _v _q h6591
  simp only [e2296, e3150, e3152, e3155, e3156, e6549, e6878, e6879, e6882] at *
  tauto
theorem n15023 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e6830 _v) := by
  have p14629 := n14629 _v _q 
  have p14101 := n14101 _v _q h6591
  simp only [e496, e3069, e3071, e3074, e3075, e6720, e6829, e6830, e6833] at *
  tauto
theorem n15024 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e3069 _v) := by
  have p14878 := n14878 _v _q 
  have p15023 := n15023 _v _q h6591
  simp only [e3069, e3071, e3074, e3075, e6829, e6830, e8137] at *
  tauto
theorem n15025 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e6973 _v) := by
  have p14377 := n14377 _v _q 
  have p12823 := n12823 _v _q h6591
  simp only [e2310, e3265, e3266, e3267, e3268, e6555, e6965, e6973, e6976] at *
  tauto
theorem n15026 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e3267 _v) := by
  have p14776 := n14776 _v _q 
  have p15025 := n15025 _v _q h6591
  simp only [e3265, e3266, e3267, e3268, e6965, e6966, e6973] at *
  tauto
theorem n15027 (_v : Vars) (_q : Query _v)  : (e8150 _v) := by
  simp only [e4648, e4649, e4650, e4651, e8149, e8150] at *
  tauto
theorem n15028 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e8157 _v) := by
  have p14632 := n14632 _v _q 
  have p14711 := n14711 _v _q h6591
  simp only [e2364, e4648, e4649, e4650, e4651, e6583, e8149, e8157, e8160] at *
  tauto
theorem n15029 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e4648 _v) := by
  have p15027 := n15027 _v _q 
  have p15028 := n15028 _v _q h6591
  simp only [e4648, e4649, e4650, e4651, e8149, e8150, e8157] at *
  tauto
theorem n15030 (_v : Vars) (_q : Query _v)  : (e8207 _v) := by
  simp only [e4718, e4719, e4720, e4721, e8206, e8207] at *
  tauto
theorem n15031 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e8214 _v) := by
  have p14642 := n14642 _v _q 
  have p12822 := n12822 _v _q h6591
  simp only [e2254, e4718, e4719, e4720, e4721, e6531, e8206, e8214, e8217] at *
  tauto
theorem n15032 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e4720 _v) := by
  have p15030 := n15030 _v _q 
  have p15031 := n15031 _v _q h6591
  simp only [e4718, e4719, e4720, e4721, e8206, e8207, e8214] at *
  tauto
theorem n15033 (_v : Vars) (_q : Query _v)  : (e8096 _v) := by
  simp only [e4608, e4609, e4610, e4611, e8095, e8096] at *
  tauto
theorem n15034 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e8103 _v) := by
  have p14626 := n14626 _v _q 
  have p11383 := n11383 _v _q h6591
  simp only [e2179, e4608, e4609, e4610, e4611, e6501, e8095, e8103, e8106] at *
  tauto
theorem n15035 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e4608 _v) := by
  have p15033 := n15033 _v _q 
  have p15034 := n15034 _v _q h6591
  simp only [e4608, e4609, e4610, e4611, e8095, e8096, e8103] at *
  tauto
theorem n15036 (_v : Vars) (_q : Query _v)  : (e8225 _v) := by
  simp only [e4742, e4743, e4744, e4745, e8224, e8225] at *
  tauto
theorem n15037 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e8232 _v) := by
  have p14645 := n14645 _v _q 
  have p11345 := n11345 _v _q h6591
  simp only [e2377, e4742, e4743, e4744, e4745, e6591, e8224, e8232, e8235] at *
  tauto
theorem n15038 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e4742 _v) := by
  have p15036 := n15036 _v _q 
  have p15037 := n15037 _v _q h6591
  simp only [e4742, e4743, e4744, e4745, e8224, e8225, e8232] at *
  tauto
theorem n15039 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e7912 _v) := by
  have p14591 := n14591 _v _q 
  have p12817 := n12817 _v _q h6591
  simp only [e2482, e4392, e4393, e4394, e4395, e6636, e7904, e7912, e7915] at *
  tauto
theorem n15040 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e4394 _v) := by
  have p14852 := n14852 _v _q 
  have p15039 := n15039 _v _q h6591
  simp only [e4392, e4393, e4394, e4395, e7904, e7905, e7912] at *
  tauto
theorem n15041 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e7170 _v) := by
  have p14427 := n14427 _v _q 
  have p14099 := n14099 _v _q h6591
  simp only [e2536, e3583, e3585, e3588, e3589, e6656, e7169, e7170, e7173] at *
  tauto
theorem n15042 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e3585 _v) := by
  have p14783 := n14783 _v _q 
  have p15041 := n15041 _v _q h6591
  simp only [e3583, e3585, e3588, e3589, e7169, e7170, e7182] at *
  tauto
theorem n15043 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e7830 _v) := by
  have p14579 := n14579 _v _q 
  have p15009 := n15009 _v _q h6591
  simp only [e2585, e4301, e4302, e4303, e4304, e6676, e7822, e7830, e7833] at *
  tauto
theorem n15044 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e4301 _v) := by
  have p14840 := n14840 _v _q 
  have p15043 := n15043 _v _q h6591
  simp only [e4301, e4302, e4303, e4304, e7822, e7823, e7830] at *
  tauto
theorem n15045 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e6700 _v) := by
  have p11035 := n11035 _v _q 
  have p12817 := n12817 _v _q h6591
  simp only [e2482, e2634, e6636, e6700, e11034] at *
  tauto
theorem n15046 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e6896 _v) := by
  have p14360 := n14360 _v _q 
  have p15045 := n15045 _v _q h6591
  simp only [e2634, e3167, e3168, e3169, e3170, e6700, e6888, e6896, e6899] at *
  tauto
theorem n15047 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e3169 _v) := by
  have p14769 := n14769 _v _q 
  have p15046 := n15046 _v _q h6591
  simp only [e3167, e3168, e3169, e3170, e6888, e6889, e6896] at *
  tauto
theorem n15048 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e7450 _v) := by
  have p14489 := n14489 _v _q 
  have p12826 := n12826 _v _q h6591
  simp only [e2746, e3971, e3972, e3973, e3974, e6758, e7442, e7450, e7453] at *
  tauto
theorem n15049 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e6776 _v) := by
  have p11030 := n11030 _v _q 
  have p15045 := n15045 _v _q h6591
  simp only [e2634, e2781, e6700, e6776, e11029] at *
  tauto
theorem n15050 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e7789 _v) := by
  have p14570 := n14570 _v _q 
  have p15049 := n15049 _v _q h6591
  simp only [e2781, e4258, e4259, e4260, e4261, e6776, e7781, e7789, e7792] at *
  tauto
theorem n15051 (_v : Vars) (_q : Query _v) (h6486 : (e6486 _v)) : (e7358 _v) := by
  have p14471 := n14471 _v _q 
  have p10889 := n10889 _v _q h6486
  simp only [e2139, e3849, e3850, e3851, e3852, e6486, e7350, e7358, e7361] at *
  tauto
theorem n15052 (_v : Vars) (_q : Query _v) (h6486 : (e6486 _v)) : (e3851 _v) := by
  have p14790 := n14790 _v _q 
  have p15051 := n15051 _v _q h6486
  simp only [e3849, e3850, e3851, e3852, e7350, e7351, e7358] at *
  tauto
theorem n15053 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e6423 _v) := by
  have p11375 := n11375 _v _q 
  have p10896 := n10896 _v _q 
  have p11345 := n11345 _v _q h6591
  exact FloorCertificate.node_15053 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e110 _v) p11375 p10896 p11345
theorem n15054 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e8060 _v) := by
  have p14622 := n14622 _v _q 
  have p15053 := n15053 _v _q h6591
  simp only [e1995, e4562, e4563, e4564, e4565, e6423, e8052, e8060, e8063] at *
  tauto
theorem n15055 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e6575 _v) := by
  have p11375 := n11375 _v _q 
  have p11345 := n11345 _v _q h6591
  have p8663 := n8663 _v _q 
  have p11376 := n11376 _v _q 
  have p10896 := n10896 _v _q 
  exact FloorCertificate.node_15055 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e110 _v) p11375 p11345 p8663 p11376 p10896
theorem n15056 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e7668 _v) := by
  have p14544 := n14544 _v _q 
  have p15055 := n15055 _v _q h6591
  simp only [e2351, e4156, e4157, e4158, e4159, e6575, e7660, e7668, e7671] at *
  tauto
end
end Assembly
