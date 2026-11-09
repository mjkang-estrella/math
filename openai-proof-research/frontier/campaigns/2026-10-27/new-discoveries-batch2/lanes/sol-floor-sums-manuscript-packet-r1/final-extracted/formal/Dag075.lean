import Dag074
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n12152 (_v : Vars) (_q : Query _v)  : (e12151 _v) := by
  have p12150 := n12150 _v _q 
  simp only [e16, e2242, e2941, e4677, e4687, e6525, e6526, e6527, e6528, e12147, e12151] at *
theorem n12154 (_v : Vars) (_q : Query _v)  : (e12153 _v) := by
  have p12149 := n12149 _v _q 
  have p12152 := n12152 _v _q 
  exact (Eq.trans p12149 p12152)
theorem n12156 (_v : Vars) (_q : Query _v)  : (e12155 _v) := by
  have p10228 := n10228 _v _q 
  simp only [e2261, e4696, e4698, e6250, e6529, e6530, e8197, e8198, e10227, e12155] at *
theorem n12159 (_v : Vars) (_q : Query _v)  : (e12158 _v) := by
  have p12156 := n12156 _v _q 
  change ((e6250 _v) = (e4696 _v)) at p12156
  simp only [e12158, e9517, e12157, p12156]
theorem n12160 (_v : Vars) (_q : Query _v)  : (e6534 _v) := by
  simp only [e2254, e2942, e4696, e4722, e4732, e6531, e6532, e6533, e6534] at *
  by_cases hc : ((e2253 _v) ≥ (e12 _v)) <;> simp [hc]
theorem n12162 (_v : Vars) (_q : Query _v)  : (e12161 _v) := by
  have p12160 := n12160 _v _q 
  simp only [e2254, e2942, e4696, e4722, e4732, e6531, e6532, e6533, e6534, e12157, e12161] at *
theorem n12164 (_v : Vars) (_q : Query _v)  : (e12163 _v) := by
  have p12159 := n12159 _v _q 
  have p12162 := n12162 _v _q 
  exact (Eq.trans p12159 p12162)
theorem n12166 (_v : Vars) (_q : Query _v)  : (e12165 _v) := by
  have p10233 := n10233 _v _q 
  simp only [e2275, e3371, e6255, e6535, e6536, e10229, e10230, e10231, e10232, e12165] at *
theorem n12169 (_v : Vars) (_q : Query _v)  : (e12168 _v) := by
  have p12166 := n12166 _v _q 
  change ((e6255 _v) = (e3371 _v)) at p12166
  simp only [e12168, e9528, e12167, p12166]
theorem n12170 (_v : Vars) (_q : Query _v)  : (e6540 _v) := by
  simp only [e2268, e2943, e3366, e3371, e3372, e6537, e6538, e6539, e6540] at *
  by_cases hc : ((e2267 _v) ≥ (e12 _v)) <;> simp [hc]
theorem n12172 (_v : Vars) (_q : Query _v)  : (e12171 _v) := by
  have p12170 := n12170 _v _q 
  simp only [e2268, e2943, e3366, e3371, e3372, e6537, e6538, e6539, e6540, e12167, e12171] at *
theorem n12174 (_v : Vars) (_q : Query _v)  : (e12173 _v) := by
  have p12169 := n12169 _v _q 
  have p12172 := n12172 _v _q 
  exact (Eq.trans p12169 p12172)
theorem n12176 (_v : Vars) (_q : Query _v)  : (e12175 _v) := by
  have p10238 := n10238 _v _q 
  simp only [e2289, e3698, e6260, e6541, e6542, e10234, e10235, e10236, e10237, e12175] at *
theorem n12179 (_v : Vars) (_q : Query _v)  : (e12178 _v) := by
  have p12176 := n12176 _v _q 
  change ((e6260 _v) = (e3698 _v)) at p12176
  simp only [e12178, e9539, e12177, p12176]
theorem n12180 (_v : Vars) (_q : Query _v)  : (e6546 _v) := by
  simp only [e2282, e2944, e3693, e3698, e3699, e6543, e6544, e6545, e6546] at *
  by_cases hc : ((e2281 _v) ≥ (e12 _v)) <;> simp [hc]
theorem n12182 (_v : Vars) (_q : Query _v)  : (e12181 _v) := by
  have p12180 := n12180 _v _q 
  simp only [e2282, e2944, e3693, e3698, e3699, e6543, e6544, e6545, e6546, e12177, e12181] at *
theorem n12184 (_v : Vars) (_q : Query _v)  : (e12183 _v) := by
  have p12179 := n12179 _v _q 
  have p12182 := n12182 _v _q 
  exact (Eq.trans p12179 p12182)
theorem n12186 (_v : Vars) (_q : Query _v)  : (e12185 _v) := by
  have p10240 := n10240 _v _q 
  simp only [e2303, e3141, e4287, e6265, e6547, e6548, e7807, e7808, e10239, e12185] at *
theorem n12189 (_v : Vars) (_q : Query _v)  : (e12188 _v) := by
  have p12186 := n12186 _v _q 
  change ((e6265 _v) = (e3141 _v)) at p12186
  simp only [e12188, e9550, e12187, p12186]
theorem n12190 (_v : Vars) (_q : Query _v)  : (e6552 _v) := by
  simp only [e2296, e2945, e3131, e3141, e3142, e6549, e6550, e6551, e6552] at *
  by_cases hc : ((e2295 _v) ≥ (e12 _v)) <;> simp [hc]
theorem n12192 (_v : Vars) (_q : Query _v)  : (e12191 _v) := by
  have p12190 := n12190 _v _q 
  simp only [e2296, e2945, e3131, e3141, e3142, e6549, e6550, e6551, e6552, e12187, e12191] at *
theorem n12194 (_v : Vars) (_q : Query _v)  : (e12193 _v) := by
  have p12189 := n12189 _v _q 
  have p12192 := n12192 _v _q 
  exact (Eq.trans p12189 p12192)
theorem n12196 (_v : Vars) (_q : Query _v)  : (e12195 _v) := by
  have p10242 := n10242 _v _q 
  simp only [e2317, e3262, e3290, e6270, e6553, e6554, e6999, e7000, e10241, e12195] at *
theorem n12199 (_v : Vars) (_q : Query _v)  : (e12198 _v) := by
  have p12196 := n12196 _v _q 
  change ((e6270 _v) = (e3262 _v)) at p12196
  simp only [e12198, e9561, e12197, p12196]
theorem n12200 (_v : Vars) (_q : Query _v)  : (e6558 _v) := by
  simp only [e2310, e2946, e3262, e3269, e3279, e6555, e6556, e6557, e6558] at *
  by_cases hc : ((e2309 _v) ≥ (e12 _v)) <;> simp [hc]
theorem n12202 (_v : Vars) (_q : Query _v)  : (e12201 _v) := by
  have p12200 := n12200 _v _q 
  simp only [e2310, e2946, e3262, e3269, e3279, e6555, e6556, e6557, e6558, e12197, e12201] at *
theorem n12204 (_v : Vars) (_q : Query _v)  : (e12203 _v) := by
  have p12199 := n12199 _v _q 
  have p12202 := n12202 _v _q 
  exact (Eq.trans p12199 p12202)
theorem n12206 (_v : Vars) (_q : Query _v)  : (e12205 _v) := by
  have p10247 := n10247 _v _q 
  simp only [e2331, e3523, e6275, e6559, e6560, e10243, e10244, e10245, e10246, e12205] at *
theorem n12209 (_v : Vars) (_q : Query _v)  : (e12208 _v) := by
  have p12206 := n12206 _v _q 
  change ((e6275 _v) = (e3523 _v)) at p12206
  simp only [e12208, e9572, e12207, p12206]
theorem n12210 (_v : Vars) (_q : Query _v)  : (e6564 _v) := by
  simp only [e2324, e2947, e3518, e3523, e3524, e6561, e6562, e6563, e6564] at *
  by_cases hc : ((e2323 _v) ≥ (e12 _v)) <;> simp [hc]
theorem n12212 (_v : Vars) (_q : Query _v)  : (e12211 _v) := by
  have p12210 := n12210 _v _q 
  simp only [e2324, e2947, e3518, e3523, e3524, e6561, e6562, e6563, e6564, e12207, e12211] at *
theorem n12214 (_v : Vars) (_q : Query _v)  : (e12213 _v) := by
  have p12209 := n12209 _v _q 
  have p12212 := n12212 _v _q 
  exact (Eq.trans p12209 p12212)
theorem n12216 (_v : Vars) (_q : Query _v)  : (e12215 _v) := by
  have p10252 := n10252 _v _q 
  simp only [e2345, e3725, e6280, e6565, e6566, e10248, e10249, e10250, e10251, e12215] at *
theorem n12219 (_v : Vars) (_q : Query _v)  : (e12218 _v) := by
  have p12216 := n12216 _v _q 
  change ((e6280 _v) = (e3725 _v)) at p12216
  simp only [e12218, e9583, e12217, p12216]
theorem n12220 (_v : Vars) (_q : Query _v)  : (e6570 _v) := by
  simp only [e2338, e2948, e3720, e3725, e3726, e6567, e6568, e6569, e6570] at *
  by_cases hc : ((e2337 _v) ≥ (e12 _v)) <;> simp [hc]
theorem n12222 (_v : Vars) (_q : Query _v)  : (e12221 _v) := by
  have p12220 := n12220 _v _q 
  simp only [e2338, e2948, e3720, e3725, e3726, e6567, e6568, e6569, e6570, e12217, e12221] at *
theorem n12224 (_v : Vars) (_q : Query _v)  : (e12223 _v) := by
  have p12219 := n12219 _v _q 
  have p12222 := n12222 _v _q 
  exact (Eq.trans p12219 p12222)
theorem n12226 (_v : Vars) (_q : Query _v)  : (e12225 _v) := by
  have p10263 := n10263 _v _q 
  change ((e9597 _v) = (e2949 _v)) at p10263
  simp only [e12225, e10030, e2950, p10263]
theorem n12228 (_v : Vars) (_q : Query _v)  : (e12227 _v) := by
  have p10274 := n10274 _v _q 
  change ((e9611 _v) = (e2951 _v)) at p10274
  simp only [e12227, e10031, e2952, p10274]
theorem n12230 (_v : Vars) (_q : Query _v)  : (e12229 _v) := by
  have p10285 := n10285 _v _q 
  change ((e9625 _v) = (e2953 _v)) at p10285
  simp only [e12229, e10032, e2954, p10285]
theorem n12232 (_v : Vars) (_q : Query _v)  : (e12231 _v) := by
  have p10290 := n10290 _v _q 
  simp only [e119, e2395, e6292, e6595, e6596, e10286, e10287, e10288, e10289, e12231] at *
theorem n12235 (_v : Vars) (_q : Query _v)  : (e12234 _v) := by
  have p12232 := n12232 _v _q 
  change ((e6292 _v) = (e119 _v)) at p12232
  simp only [e12234, e9639, e12233, p12232]
theorem n12236 (_v : Vars) (_q : Query _v)  : (e5156 _v) := by
  simp only [e101, e113, e114, e119, e120, e5153, e5154, e5155, e5156] at *
  by_cases hc : ((e112 _v) ≥ (e12 _v)) <;> simp [hc]
theorem n12238 (_v : Vars) (_q : Query _v)  : (e12237 _v) := by
  have p12236 := n12236 _v _q 
  simp only [e101, e113, e114, e119, e120, e5153, e5154, e5155, e5156, e12233, e12237] at *
theorem n12240 (_v : Vars) (_q : Query _v)  : (e12239 _v) := by
  have p12235 := n12235 _v _q 
  have p12238 := n12238 _v _q 
  exact (Eq.trans p12235 p12238)
end
end Assembly
