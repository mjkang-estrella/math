import Dag061
import generated.th_lemma_1
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n11060 (_v : Vars) (_q : Query _v) (h2310 : (e2310 _v)) (h6486 : (e6486 _v)) : (e7489 _v) := by
  have p5255 := n5255 _v _q 
  have p5257 := n5257 _v _q 
  have p11059 := n11059 _v _q h2310
  have p10889 := n10889 _v _q h6486
  exact FloorCertificate.node_11060 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e110 _v) p5255 p5257 p11059 p10889
theorem n11062 (_v : Vars) (_q : Query _v)  : (e11061 _v) := by
  by_contra hc
  change ¬ ((e2139 _v) ∨ (¬ (e2310 _v))) at hc
  have h2310 : (e2310 _v) := by
    tauto
  have h6486 : (e6486 _v) := by
    change (¬ (e2139 _v))
    tauto
  have p11060 := n11060 _v _q h2310 h6486
  exact p11060
theorem n11064 (_v : Vars) (_q : Query _v)  : (e11063 _v) := by
  have p7848 := n7848 _v _q 
  have p7852 := n7852 _v _q 
  exact (Iff.trans p7848 p7852)
theorem n11065 (_v : Vars) (_q : Query _v)  : (e7858 _v) := by
  simp only [e5, e6, e8, e12, e41, e43, e44, e46, e760, e761, e2476, e4325, e4341, e7839, e7858] at *
  omega
theorem n11066 (_v : Vars) (_q : Query _v)  : (e7859 _v) := by
  simp only [e5, e6, e8, e12, e41, e43, e44, e46, e760, e761, e2476, e4325, e4342, e7841, e7859] at *
  omega
theorem n11069 (_v : Vars) (_q : Query _v)  : (e11068 _v) := by
  have p11065 := n11065 _v _q 
  have p11066 := n11066 _v _q 
  change ((e4341 _v) ↔ (e7839 _v)) at p11065
  change ((e4342 _v) ↔ (e7841 _v)) at p11066
  simp only [e11068, e4343, e11067, p11065, p11066]
theorem n11071 (_v : Vars) (_q : Query _v)  : (e11070 _v) := by
  simp only [e5, e6, e8, e12, e41, e43, e44, e46, e4325, e7839, e7840, e7841, e7842, e7843, e7860, e11067, e11070] at *
  omega
theorem n11079 (_v : Vars) (_q : Query _v)  : (e11078 _v) := by
  have p7870 := n7870 _v _q 
  have p7874 := n7874 _v _q 
  exact (Iff.trans p7870 p7874)
theorem n11080 (_v : Vars) (_q : Query _v)  : (e7878 _v) := by
  simp only [e5, e6, e12, e36, e41, e46, e2396, e4344, e4345, e4362, e7878] at *
  omega
theorem n11081 (_v : Vars) (_q : Query _v)  : (e7879 _v) := by
  simp only [e5, e6, e12, e36, e41, e46, e2396, e4344, e4346, e4363, e7879] at *
  omega
theorem n11083 (_v : Vars) (_q : Query _v)  : (e11082 _v) := by
  have p11080 := n11080 _v _q 
  have p11081 := n11081 _v _q 
  change ((e4362 _v) ↔ (e4345 _v)) at p11080
  change ((e4363 _v) ↔ (e4346 _v)) at p11081
  simp only [e11082, e4364, e7880, p11080, p11081]
theorem n11084 (_v : Vars) (_q : Query _v)  : (e7882 _v) := by
  simp only [e5, e6, e12, e41, e46, e4344, e4345, e4346, e7862, e7863, e7864, e7880, e7881, e7882] at *
  omega
theorem n11085 (_v : Vars) (_q : Query _v)  : (e7883 _v) := by
  have p11083 := n11083 _v _q 
  have p11084 := n11084 _v _q 
  exact (Iff.trans p11083 p11084)
theorem n11092 (_v : Vars) (_q : Query _v)  : (e11091 _v) := by
  have p4376 := n4376 _v _q 
  have p7890 := n7890 _v _q 
  exact (Iff.trans p4376 p7890)
theorem n11094 (_v : Vars) (_q : Query _v)  : (e11093 _v) := by
  have p11092 := n11092 _v _q 
  change ((e4371 _v) ↔ (e4380 _v)) at p11092
  simp only [e11093, e6695, e7901, p11092]
theorem n11096 (_v : Vars) (_q : Query _v)  : (e11095 _v) := by
  have p7894 := n7894 _v _q 
  have p7897 := n7897 _v _q 
  exact (Iff.trans p7894 p7897)
theorem n11100 (_v : Vars) (_q : Query _v)  : (e11099 _v) := by
  have p4401 := n4401 _v _q 
  have p7907 := n7907 _v _q 
  exact (Iff.trans p4401 p7907)
theorem n11102 (_v : Vars) (_q : Query _v)  : (e11101 _v) := by
  have p11100 := n11100 _v _q 
  change ((e4396 _v) ↔ (e4405 _v)) at p11100
  simp only [e11101, e6637, e7918, p11100]
theorem n11104 (_v : Vars) (_q : Query _v)  : (e11103 _v) := by
  have p7911 := n7911 _v _q 
  have p7914 := n7914 _v _q 
  exact (Iff.trans p7911 p7914)
theorem n11108 (_v : Vars) (_q : Query _v)  : (e11107 _v) := by
  have p7926 := n7926 _v _q 
  have p7929 := n7929 _v _q 
  exact (Iff.trans p7926 p7929)
theorem n11110 (_v : Vars) (_q : Query _v)  : (e11109 _v) := by
  simp only [e5, e6, e8, e10, e12, e41, e43, e44, e46, e111, e4432, e7932, e7935, e7939, e7942, e7943, e7944, e7945, e11109] at *
  omega
theorem n11117 (_v : Vars) (_q : Query _v)  : (e11116 _v) := by
  have p4443 := n4443 _v _q 
  have p7950 := n7950 _v _q 
  exact (Iff.trans p4443 p7950)
theorem n11119 (_v : Vars) (_q : Query _v)  : (e11118 _v) := by
  have p11117 := n11117 _v _q 
  change ((e4438 _v) ↔ (e4447 _v)) at p11117
  simp only [e11118, e6455, e7961, p11117]
theorem n11121 (_v : Vars) (_q : Query _v)  : (e11120 _v) := by
  have p7954 := n7954 _v _q 
  have p7957 := n7957 _v _q 
  exact (Iff.trans p7954 p7957)
theorem n11125 (_v : Vars) (_q : Query _v)  : (e11124 _v) := by
  have p4462 := n4462 _v _q 
  have p7965 := n7965 _v _q 
  exact (Iff.trans p4462 p7965)
theorem n11127 (_v : Vars) (_q : Query _v)  : (e11126 _v) := by
  have p11125 := n11125 _v _q 
  change ((e4457 _v) ↔ (e4466 _v)) at p11125
  simp only [e11126, e6481, e7977, p11125]
theorem n11129 (_v : Vars) (_q : Query _v)  : (e11128 _v) := by
  have p7969 := n7969 _v _q 
  have p7973 := n7973 _v _q 
  exact (Iff.trans p7969 p7973)
theorem n11132 (_v : Vars) (_q : Query _v) (h2536 : (e2536 _v)) : (e2536 _v) := by
  exact h2536
theorem n11133 (_v : Vars) (_q : Query _v) (h2536 : (e2536 _v)) (h6636 : (e6636 _v)) : (e7489 _v) := by
  have p11132 := n11132 _v _q h2536
  have p11031 := n11031 _v _q h6636
  have p5257 := n5257 _v _q 
  exact FloorCertificate.node_11133 (e2 _v) (e7 _v) (e17 _v) (e45 _v) (e110 _v) p11132 p11031 p5257
theorem n11135 (_v : Vars) (_q : Query _v)  : (e11134 _v) := by
  by_contra hc
  change ¬ ((e2482 _v) ∨ (¬ (e2536 _v))) at hc
  have h2536 : (e2536 _v) := by
    tauto
  have h6636 : (e6636 _v) := by
    change (¬ (e2482 _v))
    tauto
  have p11133 := n11133 _v _q h2536 h6636
  exact p11133
theorem n11137 (_v : Vars) (_q : Query _v)  : (e11136 _v) := by
  have p4495 := n4495 _v _q 
  have p7987 := n7987 _v _q 
  exact (Iff.trans p4495 p7987)
theorem n11139 (_v : Vars) (_q : Query _v)  : (e11138 _v) := by
  have p11137 := n11137 _v _q 
  change ((e4490 _v) ↔ (e4499 _v)) at p11137
  simp only [e11138, e6733, e7998, p11137]
theorem n11141 (_v : Vars) (_q : Query _v)  : (e11140 _v) := by
  have p7991 := n7991 _v _q 
  have p7994 := n7994 _v _q 
  exact (Iff.trans p7991 p7994)
theorem n11144 (_v : Vars) (_q : Query _v)  : (e4517 _v) := by
  simp only [e43, e266, e2917, e4512, e4515, e4517] at *
theorem n11145 (_v : Vars) (_q : Query _v)  : (e4515 _v) := by
  have p8002 := n8002 _v _q 
  have p11144 := n11144 _v _q 
  simp only [e4515, e4517] at *
  tauto
theorem n11147 (_v : Vars) (_q : Query _v)  : (e11146 _v) := by
  have p8012 := n8012 _v _q 
  have p8016 := n8016 _v _q 
  exact (Iff.trans p8012 p8016)
theorem n11149 (_v : Vars) (_q : Query _v)  : (e11148 _v) := by
  simp only [e5, e6, e8, e10, e12, e41, e46, e108, e109, e111, e4523, e8003, e8004, e8005, e8006, e8007, e8024, e8027, e11148] at *
  omega
theorem n11156 (_v : Vars) (_q : Query _v)  : (e11155 _v) := by
  have p8034 := n8034 _v _q 
  have p8037 := n8037 _v _q 
  exact (Iff.trans p8034 p8037)
theorem n11157 (_v : Vars) (_q : Query _v)  : (e8044 _v) := by
  simp only [e5, e6, e8, e12, e36, e41, e46, e2462, e4557, e4560, e8043, e8044] at *
  omega
theorem n11158 (_v : Vars) (_q : Query _v)  : (e8046 _v) := by
  simp only [e5, e6, e8, e12, e36, e41, e46, e2462, e4558, e4560, e8045, e8046] at *
  omega
theorem n11161 (_v : Vars) (_q : Query _v)  : (e11160 _v) := by
  have p11157 := n11157 _v _q 
  have p11158 := n11158 _v _q 
  change ((e4557 _v) ↔ (e8043 _v)) at p11157
  change ((e4558 _v) ↔ (e8045 _v)) at p11158
  simp only [e11160, e4559, e11159, p11157, p11158]
theorem n11163 (_v : Vars) (_q : Query _v)  : (e11162 _v) := by
  simp only [e5, e6, e8, e12, e41, e46, e4560, e8043, e8045, e8047, e8048, e8049, e8050, e11159, e11162] at *
  omega
theorem n11171 (_v : Vars) (_q : Query _v)  : (e11170 _v) := by
  have p4571 := n4571 _v _q 
  have p8055 := n8055 _v _q 
  exact (Iff.trans p4571 p8055)
theorem n11173 (_v : Vars) (_q : Query _v)  : (e11172 _v) := by
  have p11171 := n11171 _v _q 
  change ((e4566 _v) ↔ (e4575 _v)) at p11171
  simp only [e11172, e6424, e8066, p11171]
theorem n11175 (_v : Vars) (_q : Query _v)  : (e11174 _v) := by
  have p8059 := n8059 _v _q 
  have p8062 := n8062 _v _q 
  exact (Iff.trans p8059 p8062)
end
end Assembly
