import Dag099
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n13969 (_v : Vars) (_q : Query _v)  : (e13968 _v) := by
  have p13964 := n13964 _v _q 
  have p13967 := n13967 _v _q 
  exact (Iff.trans p13964 p13967)
theorem n13970 (_v : Vars) (_q : Query _v)  : (e8084 _v) := by
  have p12715 := n12715 _v _q 
  change ((e4589 _v) ↔ (e8080 _v)) at p12715
  simp only [e8084, e6498, e8083, p12715]
theorem n13971 (_v : Vars) (_q : Query _v)  : (e12723 _v) := by
  have p13970 := n13970 _v _q 
  have p12722 := n12722 _v _q 
  change ((e6498 _v) ↔ (e8083 _v)) at p13970
  change ((e2865 _v) ↔ (e8093 _v)) at p12722
  simp only [e12723, e6499, e11186, p13970, p12722]
theorem n13972 (_v : Vars) (_q : Query _v)  : (e12724 _v) := by
  simp only [e5, e6, e10, e12, e41, e184, e185, e187, e4586, e4587, e4588, e4595, e4596, e4597, e4599, e4602, e4603, e8070, e8071, e8072, e8079, e8080, e8083, e8089, e8093, e8094, e11186, e11187, e11188, e11189, e12724] at *
  omega
theorem n13973 (_v : Vars) (_q : Query _v)  : (e11190 _v) := by
  have p13971 := n13971 _v _q 
  have p13972 := n13972 _v _q 
  exact (Iff.trans p13971 p13972)
theorem n13974 (_v : Vars) (_q : Query _v)  : (e11189 _v) := by
  have p6500 := n6500 _v _q 
  have p13973 := n13973 _v _q 
  simp only [e185, e187, e2864, e2865, e4587, e4588, e4589, e4597, e4599, e4602, e4603, e6498, e6499, e8070, e8071, e8072, e8079, e8080, e8083, e8089, e8093, e8094, e11187, e11188, e11189, e11190] at *
  tauto
theorem n13975 (_v : Vars) (_q : Query _v)  : (e8107 _v) := by
  have p12726 := n12726 _v _q 
  change ((e4617 _v) ↔ (e8103 _v)) at p12726
  simp only [e8107, e6503, e8106, p12726]
theorem n13976 (_v : Vars) (_q : Query _v)  : (e8108 _v) := by
  simp only [e5, e6, e10, e12, e41, e2178, e2179, e2936, e4607, e4608, e4609, e4610, e4611, e8095, e8103, e8106, e8108] at *
  omega
theorem n13977 (_v : Vars) (_q : Query _v)  : (e8107 _v) := by
  have p13975 := n13975 _v _q 
  have p13976 := n13976 _v _q 
  exact (Iff.trans p13975 p13976)
theorem n13979 (_v : Vars) (_q : Query _v)  : (e13978 _v) := by
  have p11194 := n11194 _v _q 
  have p13977 := n13977 _v _q 
  change ((e6502 _v) ↔ (e8109 _v)) at p11194
  change ((e6503 _v) ↔ (e8106 _v)) at p13977
  simp only [e13978, e6504, e8110, p11194, p13977]
theorem n13982 (_v : Vars) (_q : Query _v)  : (e13981 _v) := by
  simp only [e5, e6, e10, e12, e41, e2178, e2179, e2936, e3158, e3159, e3160, e3161, e3162, e4607, e4608, e4609, e4610, e4611, e4616, e6501, e8095, e8103, e8106, e8109, e8110, e8111, e11197, e11198, e13980, e13981] at *
  omega
theorem n13984 (_v : Vars) (_q : Query _v)  : (e13983 _v) := by
  have p13979 := n13979 _v _q 
  have p13982 := n13982 _v _q 
  exact (Iff.trans p13979 p13982)
theorem n13985 (_v : Vars) (_q : Query _v)  : (e8126 _v) := by
  have p12728 := n12728 _v _q 
  change ((e4629 _v) ↔ (e8122 _v)) at p12728
  simp only [e8126, e6451, e8125, p12728]
theorem n13986 (_v : Vars) (_q : Query _v)  : (e12736 _v) := by
  have p13985 := n13985 _v _q 
  have p12735 := n12735 _v _q 
  change ((e6451 _v) ↔ (e8125 _v)) at p13985
  change ((e2851 _v) ↔ (e8135 _v)) at p12735
  simp only [e12736, e6452, e11207, p13985, p12735]
theorem n13987 (_v : Vars) (_q : Query _v)  : (e12737 _v) := by
  simp only [e5, e6, e12, e41, e111, e173, e174, e176, e4626, e4627, e4628, e4635, e4636, e4637, e4639, e4642, e4643, e8112, e8113, e8114, e8121, e8122, e8125, e8131, e8135, e8136, e11207, e11208, e11209, e11210, e12737] at *
  omega
theorem n13988 (_v : Vars) (_q : Query _v)  : (e11211 _v) := by
  have p13986 := n13986 _v _q 
  have p13987 := n13987 _v _q 
  exact (Iff.trans p13986 p13987)
theorem n13989 (_v : Vars) (_q : Query _v)  : (e11210 _v) := by
  have p6453 := n6453 _v _q 
  have p13988 := n13988 _v _q 
  simp only [e174, e176, e2850, e2851, e4627, e4628, e4629, e4637, e4639, e4642, e4643, e6451, e6452, e8112, e8113, e8114, e8121, e8122, e8125, e8131, e8135, e8136, e11208, e11209, e11210, e11211] at *
  tauto
theorem n13991 (_v : Vars) (_q : Query _v)  : (e13990 _v) := by
  by_contra hc
  change ¬ ((¬ (e196 _v)) ∨ (¬ (e496 _v))) at hc
  have h196 : (e196 _v) := by
    tauto
  have h496 : (e496 _v) := by
    tauto
  have p12738 := n12738 _v _q h196 h496
  exact p12738
theorem n13992 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e6656 _v) := by
  have p11135 := n11135 _v _q 
  have p12548 := n12548 _v _q h6792
  simp only [e2482, e2536, e6636, e6656, e11134] at *
  tauto
theorem n13993 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e196 _v) := by
  have p12689 := n12689 _v _q 
  have p13992 := n13992 _v _q h6792
  simp only [e196, e2536, e6656, e12688] at *
  tauto
theorem n13994 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e6720 _v) := by
  have p13991 := n13991 _v _q 
  have p13993 := n13993 _v _q h6792
  simp only [e196, e496, e5195, e6720, e13990] at *
  tauto
theorem n13995 (_v : Vars) (_q : Query _v)  : (e8161 _v) := by
  have p12740 := n12740 _v _q 
  change ((e4662 _v) ↔ (e8157 _v)) at p12740
  simp only [e8161, e6585, e8160, p12740]
theorem n13996 (_v : Vars) (_q : Query _v)  : (e8162 _v) := by
  simp only [e5, e6, e8, e10, e12, e41, e43, e44, e111, e2363, e2364, e2952, e4647, e4648, e4649, e4650, e4651, e8149, e8157, e8160, e8162] at *
  omega
theorem n13997 (_v : Vars) (_q : Query _v)  : (e8161 _v) := by
  have p13995 := n13995 _v _q 
  have p13996 := n13996 _v _q 
  exact (Iff.trans p13995 p13996)
theorem n13999 (_v : Vars) (_q : Query _v)  : (e13998 _v) := by
  have p11219 := n11219 _v _q 
  have p13997 := n13997 _v _q 
  change ((e6584 _v) ↔ (e8163 _v)) at p11219
  change ((e6585 _v) ↔ (e8160 _v)) at p13997
  simp only [e13998, e6586, e8164, p11219, p13997]
theorem n14002 (_v : Vars) (_q : Query _v)  : (e14001 _v) := by
  simp only [e5, e6, e8, e10, e12, e41, e43, e44, e111, e2363, e2364, e2952, e4647, e4648, e4649, e4650, e4651, e4653, e4654, e4658, e4659, e4660, e4661, e6583, e8149, e8157, e8160, e8163, e8164, e8165, e11222, e11223, e14000, e14001] at *
  omega
theorem n14004 (_v : Vars) (_q : Query _v)  : (e14003 _v) := by
  have p13999 := n13999 _v _q 
  have p14002 := n14002 _v _q 
  exact (Iff.trans p13999 p14002)
theorem n14005 (_v : Vars) (_q : Query _v)  : (e8178 _v) := by
  have p12742 := n12742 _v _q 
  change ((e4687 _v) ↔ (e8174 _v)) at p12742
  simp only [e8178, e6527, e8177, p12742]
theorem n14006 (_v : Vars) (_q : Query _v)  : (e8179 _v) := by
  simp only [e5, e6, e8, e10, e12, e41, e2241, e2242, e4671, e4672, e4673, e4674, e4675, e4676, e8166, e8174, e8177, e8179] at *
  omega
theorem n14007 (_v : Vars) (_q : Query _v)  : (e8178 _v) := by
  have p14005 := n14005 _v _q 
  have p14006 := n14006 _v _q 
  exact (Iff.trans p14005 p14006)
theorem n14009 (_v : Vars) (_q : Query _v)  : (e14008 _v) := by
  have p11227 := n11227 _v _q 
  have p14007 := n14007 _v _q 
  change ((e6526 _v) ↔ (e8180 _v)) at p11227
  change ((e6527 _v) ↔ (e8177 _v)) at p14007
  simp only [e14008, e6528, e8181, p11227, p14007]
theorem n14012 (_v : Vars) (_q : Query _v)  : (e14011 _v) := by
  simp only [e5, e6, e8, e10, e12, e41, e2241, e2242, e4671, e4672, e4673, e4674, e4675, e4676, e4678, e4679, e4683, e4684, e4685, e4686, e6525, e8166, e8174, e8177, e8180, e8181, e8182, e11230, e11231, e14010, e14011] at *
  omega
theorem n14014 (_v : Vars) (_q : Query _v)  : (e14013 _v) := by
  have p14009 := n14009 _v _q 
  have p14012 := n14012 _v _q 
  exact (Iff.trans p14009 p14012)
theorem n14016 (_v : Vars) (_q : Query _v)  : (e14015 _v) := by
  simp only [e5, e6, e8, e10, e12, e41, e43, e44, e2260, e2261, e4697, e8183, e8184, e8185, e8186, e8187, e8204, e11242, e14015] at *
  omega
theorem n14017 (_v : Vars) (_q : Query _v)  : (e12749 _v) := by
  have p12750 := n12750 _v _q 
  have p14016 := n14016 _v _q 
  exact (Iff.trans p12750 p14016)
theorem n14018 (_v : Vars) (_q : Query _v)  : (e8218 _v) := by
  have p12754 := n12754 _v _q 
  change ((e4732 _v) ↔ (e8214 _v)) at p12754
  simp only [e8218, e6533, e8217, p12754]
theorem n14019 (_v : Vars) (_q : Query _v)  : (e8219 _v) := by
  simp only [e5, e6, e8, e10, e12, e41, e43, e44, e2253, e2254, e4716, e4717, e4718, e4719, e4720, e4721, e8206, e8214, e8217, e8219] at *
  omega
theorem n14020 (_v : Vars) (_q : Query _v)  : (e8218 _v) := by
  have p14018 := n14018 _v _q 
  have p14019 := n14019 _v _q 
  exact (Iff.trans p14018 p14019)
theorem n14022 (_v : Vars) (_q : Query _v)  : (e14021 _v) := by
  have p11250 := n11250 _v _q 
  have p14020 := n14020 _v _q 
  change ((e6532 _v) ↔ (e8220 _v)) at p11250
  change ((e6533 _v) ↔ (e8217 _v)) at p14020
  simp only [e14021, e6534, e8221, p11250, p14020]
theorem n14025 (_v : Vars) (_q : Query _v)  : (e14024 _v) := by
  simp only [e5, e6, e8, e10, e12, e41, e43, e44, e2253, e2254, e4716, e4717, e4718, e4719, e4720, e4721, e4723, e4724, e4728, e4729, e4730, e4731, e6531, e8206, e8214, e8217, e8220, e8221, e8222, e11253, e11254, e14023, e14024] at *
  omega
theorem n14027 (_v : Vars) (_q : Query _v)  : (e14026 _v) := by
  have p14022 := n14022 _v _q 
  have p14025 := n14025 _v _q 
  exact (Iff.trans p14022 p14025)
theorem n14028 (_v : Vars) (_q : Query _v)  : (e8236 _v) := by
  have p12756 := n12756 _v _q 
  change ((e4756 _v) ↔ (e8232 _v)) at p12756
  simp only [e8236, e6593, e8235, p12756]
theorem n14029 (_v : Vars) (_q : Query _v)  : (e8237 _v) := by
  simp only [e5, e6, e8, e10, e12, e41, e111, e266, e267, e2376, e2377, e2954, e4741, e4742, e4743, e4744, e4745, e8224, e8232, e8235, e8237] at *
  omega
theorem n14030 (_v : Vars) (_q : Query _v)  : (e8236 _v) := by
  have p14028 := n14028 _v _q 
  have p14029 := n14029 _v _q 
  exact (Iff.trans p14028 p14029)
theorem n14032 (_v : Vars) (_q : Query _v)  : (e14031 _v) := by
  have p11258 := n11258 _v _q 
  have p14030 := n14030 _v _q 
  change ((e6592 _v) ↔ (e8238 _v)) at p11258
  change ((e6593 _v) ↔ (e8235 _v)) at p14030
  simp only [e14031, e6594, e8239, p11258, p14030]
end
end Assembly
