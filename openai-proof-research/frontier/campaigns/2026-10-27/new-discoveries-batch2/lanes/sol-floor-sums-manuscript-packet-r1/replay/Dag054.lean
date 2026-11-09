import Dag053
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n10164 (_v : Vars) (_q : Query _v)  : (e10163 _v) := by
  have p6473 := n6473 _v _q 
  simp only [e2115, e2118, e2859, e2860, e2861, e2862, e6470, e6471, e6472, e10163] at *
theorem n10167 (_v : Vars) (_q : Query _v)  : (e10166 _v) := by
  have p10164 := n10164 _v _q 
  change ((e2118 _v) = (e2860 _v)) at p10164
  simp only [e10166, e9407, e10165, p10164]
theorem n10168 (_v : Vars) (_q : Query _v)  : (e6477 _v) := by
  simp only [e2108, e2860, e2930, e3418, e3423, e6474, e6475, e6476, e6477] at *
  by_cases hc : ((e2107 _v) ≥ (e12 _v)) <;> simp [hc]
theorem n10170 (_v : Vars) (_q : Query _v)  : (e10169 _v) := by
  have p10168 := n10168 _v _q 
  simp only [e2108, e2860, e2930, e3418, e3423, e6474, e6475, e6476, e6477, e10165, e10169] at *
theorem n10172 (_v : Vars) (_q : Query _v)  : (e10171 _v) := by
  have p10167 := n10167 _v _q 
  have p10170 := n10170 _v _q 
  exact (Eq.trans p10167 p10170)
theorem n10174 (_v : Vars) (_q : Query _v)  : (e10173 _v) := by
  simp only [e2132, e4215, e4222, e6478, e6479, e7742, e7743, e10173] at *
  by_cases hc : ((e2131 _v) ≤ (e12 _v)) <;> simp [hc]
theorem n10176 (_v : Vars) (_q : Query _v)  : (e10175 _v) := by
  simp only [e2146, e3846, e3874, e6484, e6485, e7384, e7385, e10175] at *
  by_cases hc : ((e2145 _v) ≤ (e12 _v)) <;> simp [hc]
theorem n10181 (_v : Vars) (_q : Query _v)  : (e10180 _v) := by
  simp only [e275, e2158, e6490, e6491, e10177, e10178, e10179, e10180] at *
  by_cases hc : ((e2157 _v) ≤ (e12 _v)) <;> simp [hc]
theorem n10186 (_v : Vars) (_q : Query _v)  : (e10185 _v) := by
  simp only [e2172, e3010, e6492, e6493, e10182, e10183, e10184, e10185] at *
  by_cases hc : ((e2171 _v) ≤ (e12 _v)) <;> simp [hc]
theorem n10188 (_v : Vars) (_q : Query _v)  : (e10187 _v) := by
  have p6500 := n6500 _v _q 
  simp only [e185, e187, e2187, e2863, e2864, e2865, e4589, e6498, e6499, e10187] at *
theorem n10191 (_v : Vars) (_q : Query _v)  : (e10190 _v) := by
  have p10188 := n10188 _v _q 
  change ((e2187 _v) = (e2863 _v)) at p10188
  simp only [e10190, e9462, e10189, p10188]
theorem n10192 (_v : Vars) (_q : Query _v)  : (e6504 _v) := by
  simp only [e2179, e2863, e2935, e4612, e4617, e6501, e6502, e6503, e6504] at *
  by_cases hc : ((e2178 _v) ≥ (e12 _v)) <;> simp [hc]
theorem n10194 (_v : Vars) (_q : Query _v)  : (e10193 _v) := by
  have p10192 := n10192 _v _q 
  simp only [e2179, e2863, e2935, e4612, e4617, e6501, e6502, e6503, e6504, e10189, e10193] at *
theorem n10196 (_v : Vars) (_q : Query _v)  : (e10195 _v) := by
  have p10191 := n10191 _v _q 
  have p10194 := n10194 _v _q 
  exact (Eq.trans p10191 p10194)
theorem n10198 (_v : Vars) (_q : Query _v)  : (e10197 _v) := by
  have p6508 := n6508 _v _q 
  simp only [e2201, e2204, e2866, e2867, e2868, e2869, e6505, e6506, e6507, e10197] at *
theorem n10201 (_v : Vars) (_q : Query _v)  : (e10200 _v) := by
  have p10198 := n10198 _v _q 
  change ((e2204 _v) = (e2867 _v)) at p10198
  simp only [e10200, e9473, e10199, p10198]
theorem n10202 (_v : Vars) (_q : Query _v)  : (e6512 _v) := by
  simp only [e2194, e2867, e2937, e3616, e3621, e6509, e6510, e6511, e6512] at *
  by_cases hc : ((e2193 _v) ≥ (e12 _v)) <;> simp [hc]
theorem n10204 (_v : Vars) (_q : Query _v)  : (e10203 _v) := by
  have p10202 := n10202 _v _q 
  simp only [e2194, e2867, e2937, e3616, e3621, e6509, e6510, e6511, e6512, e10199, e10203] at *
theorem n10206 (_v : Vars) (_q : Query _v)  : (e10205 _v) := by
  have p10201 := n10201 _v _q 
  have p10204 := n10204 _v _q 
  exact (Eq.trans p10201 p10204)
theorem n10208 (_v : Vars) (_q : Query _v)  : (e10207 _v) := by
  have p6516 := n6516 _v _q 
  simp only [e311, e2216, e2219, e2870, e2871, e2872, e6513, e6514, e6515, e10207] at *
theorem n10211 (_v : Vars) (_q : Query _v)  : (e10210 _v) := by
  have p10208 := n10208 _v _q 
  change ((e2219 _v) = (e311 _v)) at p10208
  simp only [e10210, e9484, e10209, p10208]
theorem n10212 (_v : Vars) (_q : Query _v)  : (e5282 _v) := by
  simp only [e297, e305, e306, e311, e312, e5279, e5280, e5281, e5282] at *
  by_cases hc : ((e304 _v) ≥ (e12 _v)) <;> simp [hc]
theorem n10214 (_v : Vars) (_q : Query _v)  : (e10213 _v) := by
  have p10212 := n10212 _v _q 
  simp only [e297, e305, e306, e311, e312, e5279, e5280, e5281, e5282, e10209, e10213] at *
theorem n10216 (_v : Vars) (_q : Query _v)  : (e10215 _v) := by
  have p10211 := n10211 _v _q 
  have p10214 := n10214 _v _q 
  exact (Eq.trans p10211 p10214)
theorem n10218 (_v : Vars) (_q : Query _v)  : (e10217 _v) := by
  have p6520 := n6520 _v _q 
  simp only [e2233, e2236, e2873, e2874, e2875, e2876, e6517, e6518, e6519, e10217] at *
theorem n10221 (_v : Vars) (_q : Query _v)  : (e10220 _v) := by
  have p10218 := n10218 _v _q 
  change ((e2236 _v) = (e2874 _v)) at p10218
  simp only [e10220, e9495, e10219, p10218]
theorem n10222 (_v : Vars) (_q : Query _v)  : (e6524 _v) := by
  simp only [e2226, e2874, e2939, e3443, e3448, e6521, e6522, e6523, e6524] at *
  by_cases hc : ((e2225 _v) ≥ (e12 _v)) <;> simp [hc]
theorem n10224 (_v : Vars) (_q : Query _v)  : (e10223 _v) := by
  have p10222 := n10222 _v _q 
  simp only [e2226, e2874, e2939, e3443, e3448, e6521, e6522, e6523, e6524, e10219, e10223] at *
theorem n10226 (_v : Vars) (_q : Query _v)  : (e10225 _v) := by
  have p10221 := n10221 _v _q 
  have p10224 := n10224 _v _q 
  exact (Eq.trans p10221 p10224)
theorem n10228 (_v : Vars) (_q : Query _v)  : (e10227 _v) := by
  simp only [e2261, e4696, e4698, e6529, e6530, e8197, e8198, e10227] at *
  by_cases hc : ((e2260 _v) ≤ (e12 _v)) <;> simp [hc]
theorem n10233 (_v : Vars) (_q : Query _v)  : (e10232 _v) := by
  simp only [e2275, e3371, e6535, e6536, e10229, e10230, e10231, e10232] at *
  by_cases hc : ((e2274 _v) ≤ (e12 _v)) <;> simp [hc]
theorem n10238 (_v : Vars) (_q : Query _v)  : (e10237 _v) := by
  simp only [e2289, e3698, e6541, e6542, e10234, e10235, e10236, e10237] at *
  by_cases hc : ((e2288 _v) ≤ (e12 _v)) <;> simp [hc]
theorem n10240 (_v : Vars) (_q : Query _v)  : (e10239 _v) := by
  simp only [e2303, e3141, e4287, e6547, e6548, e7807, e7808, e10239] at *
  by_cases hc : ((e2302 _v) ≤ (e12 _v)) <;> simp [hc]
theorem n10242 (_v : Vars) (_q : Query _v)  : (e10241 _v) := by
  simp only [e2317, e3262, e3290, e6553, e6554, e6999, e7000, e10241] at *
  by_cases hc : ((e2316 _v) ≤ (e12 _v)) <;> simp [hc]
theorem n10247 (_v : Vars) (_q : Query _v)  : (e10246 _v) := by
  simp only [e2331, e3523, e6559, e6560, e10243, e10244, e10245, e10246] at *
  by_cases hc : ((e2330 _v) ≤ (e12 _v)) <;> simp [hc]
theorem n10252 (_v : Vars) (_q : Query _v)  : (e10251 _v) := by
  simp only [e2345, e3725, e6565, e6566, e10248, e10249, e10250, e10251] at *
  by_cases hc : ((e2344 _v) ≤ (e12 _v)) <;> simp [hc]
theorem n10253 (_v : Vars) (_q : Query _v)  : (e6574 _v) := by
  simp only [e2358, e2877, e2878, e4143, e6571, e6572, e6573, e6574] at *
  by_cases hc : ((e2357 _v) ≤ (e12 _v)) <;> simp [hc]
theorem n10255 (_v : Vars) (_q : Query _v)  : (e10254 _v) := by
  have p10253 := n10253 _v _q 
  simp only [e2358, e2877, e2878, e4143, e6283, e6571, e6572, e6573, e6574, e10254] at *
theorem n10258 (_v : Vars) (_q : Query _v)  : (e10257 _v) := by
  have p10255 := n10255 _v _q 
  change ((e6283 _v) = (e2877 _v)) at p10255
  simp only [e10257, e9597, e10256, p10255]
theorem n10259 (_v : Vars) (_q : Query _v)  : (e6578 _v) := by
  simp only [e2351, e2877, e2949, e4160, e4170, e6575, e6576, e6577, e6578] at *
  by_cases hc : ((e2350 _v) ≥ (e12 _v)) <;> simp [hc]
theorem n10261 (_v : Vars) (_q : Query _v)  : (e10260 _v) := by
  have p10259 := n10259 _v _q 
  simp only [e2351, e2877, e2949, e4160, e4170, e6575, e6576, e6577, e6578, e10256, e10260] at *
theorem n10263 (_v : Vars) (_q : Query _v)  : (e10262 _v) := by
  have p10258 := n10258 _v _q 
  have p10261 := n10261 _v _q 
  exact (Eq.trans p10258 p10261)
theorem n10264 (_v : Vars) (_q : Query _v)  : (e6582 _v) := by
  simp only [e2371, e2879, e2880, e4185, e6579, e6580, e6581, e6582] at *
  by_cases hc : ((e2370 _v) ≤ (e12 _v)) <;> simp [hc]
theorem n10266 (_v : Vars) (_q : Query _v)  : (e10265 _v) := by
  have p10264 := n10264 _v _q 
  simp only [e2371, e2879, e2880, e4185, e6286, e6579, e6580, e6581, e6582, e10265] at *
theorem n10269 (_v : Vars) (_q : Query _v)  : (e10268 _v) := by
  have p10266 := n10266 _v _q 
  change ((e6286 _v) = (e2879 _v)) at p10266
  simp only [e10268, e9611, e10267, p10266]
end
end Assembly
