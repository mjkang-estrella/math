import Dag073
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n12062 (_v : Vars) (_q : Query _v)  : (e12061 _v) := by
  have p12058 := n12058 _v _q 
  have p12060 := n12060 _v _q 
  exact (Iff.trans p12058 p12060)
theorem n12064 (_v : Vars) (_q : Query _v)  : (e12063 _v) := by
  have p12062 := n12062 _v _q 
  have p10001 := n10001 _v _q 
  change ((e1551 _v) ↔ (e2781 _v)) at p12062
  change ((e6042 _v) = (e6398 _v)) at p10001
  simp only [e12063, e9156, e10051, p12062, p10001]
theorem n12066 (_v : Vars) (_q : Query _v)  : (e12065 _v) := by
  have p2790 := n2790 _v _q 
  change ((e1557 _v) = (e2788 _v)) at p2790
  simp only [e12065, e1558, e2791, p2790]
theorem n12068 (_v : Vars) (_q : Query _v)  : (e12067 _v) := by
  simp only [e5, e6, e8, e10, e12, e41, e46, e111, e266, e267, e781, e782, e2788, e2791, e2792, e2793, e12067] at *
  omega
theorem n12070 (_v : Vars) (_q : Query _v)  : (e12069 _v) := by
  have p12066 := n12066 _v _q 
  have p12068 := n12068 _v _q 
  exact (Iff.trans p12066 p12068)
theorem n12072 (_v : Vars) (_q : Query _v)  : (e12071 _v) := by
  have p12070 := n12070 _v _q 
  have p10009 := n10009 _v _q 
  change ((e1558 _v) ↔ (e2793 _v)) at p12070
  change ((e6045 _v) = (e6399 _v)) at p10009
  simp only [e12071, e9157, e10052, p12070, p10009]
theorem n12074 (_v : Vars) (_q : Query _v)  : (e12073 _v) := by
  have p2802 := n2802 _v _q 
  change ((e1564 _v) = (e2800 _v)) at p2802
  simp only [e12073, e1565, e2803, p2802]
theorem n12076 (_v : Vars) (_q : Query _v)  : (e12075 _v) := by
  simp only [e5, e6, e8, e10, e12, e41, e46, e108, e109, e111, e802, e803, e2800, e2803, e2804, e2805, e12075] at *
  omega
theorem n12078 (_v : Vars) (_q : Query _v)  : (e12077 _v) := by
  have p12074 := n12074 _v _q 
  have p12076 := n12076 _v _q 
  exact (Iff.trans p12074 p12076)
theorem n12080 (_v : Vars) (_q : Query _v)  : (e12079 _v) := by
  have p12078 := n12078 _v _q 
  have p10017 := n10017 _v _q 
  change ((e1565 _v) ↔ (e2805 _v)) at p12078
  change ((e6048 _v) = (e6400 _v)) at p10017
  simp only [e12079, e9158, e10053, p12078, p10017]
theorem n12082 (_v : Vars) (_q : Query _v)  : (e12081 _v) := by
  have p10102 := n10102 _v _q 
  change ((e9330 _v) = (e2918 _v)) at p10102
  simp only [e12081, e10018, e2919, p10102]
theorem n12084 (_v : Vars) (_q : Query _v)  : (e12083 _v) := by
  have p10112 := n10112 _v _q 
  change ((e9341 _v) = (e2920 _v)) at p10112
  simp only [e12083, e10019, e2921, p10112]
theorem n12086 (_v : Vars) (_q : Query _v)  : (e12085 _v) := by
  have p10122 := n10122 _v _q 
  change ((e9352 _v) = (e2922 _v)) at p10122
  simp only [e12085, e10020, e2923, p10122]
theorem n12088 (_v : Vars) (_q : Query _v)  : (e12087 _v) := by
  have p10132 := n10132 _v _q 
  change ((e9363 _v) = (e2924 _v)) at p10132
  simp only [e12087, e10021, e2925, p10132]
theorem n12090 (_v : Vars) (_q : Query _v)  : (e12089 _v) := by
  have p10142 := n10142 _v _q 
  change ((e9374 _v) = (e2926 _v)) at p10142
  simp only [e12089, e10022, e2927, p10142]
theorem n12092 (_v : Vars) (_q : Query _v)  : (e12091 _v) := by
  have p10152 := n10152 _v _q 
  change ((e9385 _v) = (e2928 _v)) at p10152
  simp only [e12091, e10023, e2929, p10152]
theorem n12094 (_v : Vars) (_q : Query _v)  : (e12093 _v) := by
  have p10162 := n10162 _v _q 
  change ((e9396 _v) = (e332 _v)) at p10162
  simp only [e12093, e10024, e353, p10162]
theorem n12096 (_v : Vars) (_q : Query _v)  : (e12095 _v) := by
  have p10172 := n10172 _v _q 
  change ((e9407 _v) = (e2930 _v)) at p10172
  simp only [e12095, e10025, e2931, p10172]
theorem n12098 (_v : Vars) (_q : Query _v)  : (e12097 _v) := by
  have p10174 := n10174 _v _q 
  simp only [e2132, e4215, e4222, e6217, e6478, e6479, e7742, e7743, e10173, e12097] at *
  tauto
theorem n12101 (_v : Vars) (_q : Query _v)  : (e12100 _v) := by
  have p12098 := n12098 _v _q 
  change ((e6217 _v) = (e4215 _v)) at p12098
  simp only [e12100, e9418, e12099, p12098]
theorem n12102 (_v : Vars) (_q : Query _v)  : (e6483 _v) := by
  simp only [e2125, e2932, e4215, e4457, e4467, e6480, e6481, e6482, e6483] at *
  by_cases hc : ((e2124 _v) ≥ (e12 _v)) <;> simp [hc]
theorem n12104 (_v : Vars) (_q : Query _v)  : (e12103 _v) := by
  have p12102 := n12102 _v _q 
  simp only [e2125, e2932, e4215, e4457, e4467, e6480, e6481, e6482, e6483, e12099, e12103] at *
  tauto
theorem n12106 (_v : Vars) (_q : Query _v)  : (e12105 _v) := by
  have p12101 := n12101 _v _q 
  have p12104 := n12104 _v _q 
  exact (Eq.trans p12101 p12104)
theorem n12108 (_v : Vars) (_q : Query _v)  : (e12107 _v) := by
  have p10176 := n10176 _v _q 
  simp only [e2146, e3846, e3874, e6222, e6484, e6485, e7384, e7385, e10175, e12107] at *
  tauto
theorem n12111 (_v : Vars) (_q : Query _v)  : (e12110 _v) := by
  have p12108 := n12108 _v _q 
  change ((e6222 _v) = (e3846 _v)) at p12108
  simp only [e12110, e9429, e12109, p12108]
theorem n12112 (_v : Vars) (_q : Query _v)  : (e6489 _v) := by
  simp only [e2139, e2933, e3846, e3853, e3863, e6486, e6487, e6488, e6489] at *
  by_cases hc : ((e2138 _v) ≥ (e12 _v)) <;> simp [hc]
theorem n12114 (_v : Vars) (_q : Query _v)  : (e12113 _v) := by
  have p12112 := n12112 _v _q 
  simp only [e2139, e2933, e3846, e3853, e3863, e6486, e6487, e6488, e6489, e12109, e12113] at *
  tauto
theorem n12116 (_v : Vars) (_q : Query _v)  : (e12115 _v) := by
  have p12111 := n12111 _v _q 
  have p12114 := n12114 _v _q 
  exact (Eq.trans p12111 p12114)
theorem n12118 (_v : Vars) (_q : Query _v)  : (e12117 _v) := by
  have p10181 := n10181 _v _q 
  simp only [e275, e2158, e6227, e6490, e6491, e10177, e10178, e10179, e10180, e12117] at *
  tauto
theorem n12121 (_v : Vars) (_q : Query _v)  : (e12120 _v) := by
  have p12118 := n12118 _v _q 
  change ((e6227 _v) = (e275 _v)) at p12118
  simp only [e12120, e9440, e12119, p12118]
theorem n12122 (_v : Vars) (_q : Query _v)  : (e5262 _v) := by
  simp only [e259, e269, e270, e275, e276, e5259, e5260, e5261, e5262] at *
  by_cases hc : ((e268 _v) ≥ (e12 _v)) <;> simp [hc]
theorem n12124 (_v : Vars) (_q : Query _v)  : (e12123 _v) := by
  have p12122 := n12122 _v _q 
  simp only [e259, e269, e270, e275, e276, e5259, e5260, e5261, e5262, e12119, e12123] at *
  tauto
theorem n12126 (_v : Vars) (_q : Query _v)  : (e12125 _v) := by
  have p12121 := n12121 _v _q 
  have p12124 := n12124 _v _q 
  exact (Eq.trans p12121 p12124)
theorem n12128 (_v : Vars) (_q : Query _v)  : (e12127 _v) := by
  have p10186 := n10186 _v _q 
  simp only [e2172, e3010, e6232, e6492, e6493, e10182, e10183, e10184, e10185, e12127] at *
  tauto
theorem n12131 (_v : Vars) (_q : Query _v)  : (e12130 _v) := by
  have p12128 := n12128 _v _q 
  change ((e6232 _v) = (e3010 _v)) at p12128
  simp only [e12130, e9451, e12129, p12128]
theorem n12132 (_v : Vars) (_q : Query _v)  : (e6497 _v) := by
  simp only [e2165, e2934, e3005, e3010, e3011, e6494, e6495, e6496, e6497] at *
  by_cases hc : ((e2164 _v) ≥ (e12 _v)) <;> simp [hc]
theorem n12134 (_v : Vars) (_q : Query _v)  : (e12133 _v) := by
  have p12132 := n12132 _v _q 
  simp only [e2165, e2934, e3005, e3010, e3011, e6494, e6495, e6496, e6497, e12129, e12133] at *
  tauto
theorem n12136 (_v : Vars) (_q : Query _v)  : (e12135 _v) := by
  have p12131 := n12131 _v _q 
  have p12134 := n12134 _v _q 
  exact (Eq.trans p12131 p12134)
theorem n12138 (_v : Vars) (_q : Query _v)  : (e12137 _v) := by
  have p10196 := n10196 _v _q 
  change ((e9462 _v) = (e2935 _v)) at p10196
  simp only [e12137, e10026, e2936, p10196]
theorem n12140 (_v : Vars) (_q : Query _v)  : (e12139 _v) := by
  have p10206 := n10206 _v _q 
  change ((e9473 _v) = (e2937 _v)) at p10206
  simp only [e12139, e10027, e2938, p10206]
theorem n12142 (_v : Vars) (_q : Query _v)  : (e12141 _v) := by
  have p10216 := n10216 _v _q 
  change ((e9484 _v) = (e297 _v)) at p10216
  simp only [e12141, e10028, e318, p10216]
theorem n12144 (_v : Vars) (_q : Query _v)  : (e12143 _v) := by
  have p10226 := n10226 _v _q 
  change ((e9495 _v) = (e2939 _v)) at p10226
  simp only [e12143, e10029, e2940, p10226]
theorem n12146 (_v : Vars) (_q : Query _v)  : (e12145 _v) := by
  have p8611 := n8611 _v _q 
  simp only [e13, e16, e18, e5083, e5084, e5093, e5094, e6245, e8610, e12145] at *
  tauto
theorem n12149 (_v : Vars) (_q : Query _v)  : (e12148 _v) := by
  have p12146 := n12146 _v _q 
  change ((e6245 _v) = (e16 _v)) at p12146
  simp only [e12148, e9506, e12147, p12146]
theorem n12150 (_v : Vars) (_q : Query _v)  : (e6528 _v) := by
  simp only [e16, e2242, e2941, e4677, e4687, e6525, e6526, e6527, e6528] at *
  by_cases hc : ((e2241 _v) ≥ (e12 _v)) <;> simp [hc]
end
end Assembly
