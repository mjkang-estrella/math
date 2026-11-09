import Dag043
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n9415 (_v : Vars) (_q : Query _v)  : (e6216 _v) := by
  have p9413 := n9413 _v _q 
  have p9414 := n9414 _v _q 
  exact (Iff.trans p9413 p9414)
theorem n9417 (_v : Vars) (_q : Query _v)  : (e9416 _v) := by
  have p9415 := n9415 _v _q 
  have p2121 := n2121 _v _q 
  change ((e969 _v) ↔ (e2132 _v)) at p9415
  change ((e964 _v) = (e2119 _v)) at p2121
  simp only [e9416, e971, e6217, p9415, p2121]
theorem n9420 (_v : Vars) (_q : Query _v)  : (e9419 _v) := by
  have p9412 := n9412 _v _q 
  have p9417 := n9417 _v _q 
  change ((e1644 _v) ↔ (e2125 _v)) at p9412
  change ((e971 _v) = (e6217 _v)) at p9417
  simp only [e9419, e5599, e9418, p9412, p9417]
theorem n9421 (_v : Vars) (_q : Query _v)  : (e2137 _v) := by
  have p2135 := n2135 _v _q 
  change ((e974 _v) = (e2133 _v)) at p2135
  simp only [e2137, e1651, e2136, p2135]
theorem n9422 (_v : Vars) (_q : Query _v)  : (e6218 _v) := by
  simp only [e5, e6, e8, e12, e41, e43, e44, e111, e760, e761, e2133, e2136, e2138, e2139, e6218] at *
  omega
theorem n9423 (_v : Vars) (_q : Query _v)  : (e6219 _v) := by
  have p9421 := n9421 _v _q 
  have p9422 := n9422 _v _q 
  exact (Iff.trans p9421 p9422)
theorem n9424 (_v : Vars) (_q : Query _v)  : (e2144 _v) := by
  have p2142 := n2142 _v _q 
  change ((e978 _v) = (e2140 _v)) at p2142
  simp only [e2144, e979, e2143, p2142]
theorem n9425 (_v : Vars) (_q : Query _v)  : (e6220 _v) := by
  simp only [e5, e6, e8, e12, e43, e44, e111, e760, e761, e2140, e2143, e2145, e2146, e6220] at *
  omega
theorem n9426 (_v : Vars) (_q : Query _v)  : (e6221 _v) := by
  have p9424 := n9424 _v _q 
  have p9425 := n9425 _v _q 
  exact (Iff.trans p9424 p9425)
theorem n9428 (_v : Vars) (_q : Query _v)  : (e9427 _v) := by
  have p9426 := n9426 _v _q 
  have p2135 := n2135 _v _q 
  change ((e979 _v) ↔ (e2146 _v)) at p9426
  change ((e974 _v) = (e2133 _v)) at p2135
  simp only [e9427, e981, e6222, p9426, p2135]
theorem n9431 (_v : Vars) (_q : Query _v)  : (e9430 _v) := by
  have p9423 := n9423 _v _q 
  have p9428 := n9428 _v _q 
  change ((e1651 _v) ↔ (e2139 _v)) at p9423
  change ((e981 _v) = (e6222 _v)) at p9428
  simp only [e9430, e5609, e9429, p9423, p9428]
theorem n9432 (_v : Vars) (_q : Query _v)  : (e2151 _v) := by
  have p2149 := n2149 _v _q 
  change ((e984 _v) = (e2147 _v)) at p2149
  simp only [e2151, e1658, e2150, p2149]
theorem n9433 (_v : Vars) (_q : Query _v)  : (e6223 _v) := by
  simp only [e5, e6, e8, e12, e41, e111, e266, e267, e268, e269, e781, e782, e2147, e2150, e6223] at *
  omega
theorem n9434 (_v : Vars) (_q : Query _v)  : (e6224 _v) := by
  have p9432 := n9432 _v _q 
  have p9433 := n9433 _v _q 
  exact (Iff.trans p9432 p9433)
theorem n9435 (_v : Vars) (_q : Query _v)  : (e2156 _v) := by
  have p2154 := n2154 _v _q 
  change ((e988 _v) = (e2152 _v)) at p2154
  simp only [e2156, e989, e2155, p2154]
theorem n9436 (_v : Vars) (_q : Query _v)  : (e6225 _v) := by
  simp only [e5, e6, e8, e12, e111, e266, e267, e781, e782, e2152, e2155, e2157, e2158, e6225] at *
  omega
theorem n9437 (_v : Vars) (_q : Query _v)  : (e6226 _v) := by
  have p9435 := n9435 _v _q 
  have p9436 := n9436 _v _q 
  exact (Iff.trans p9435 p9436)
theorem n9439 (_v : Vars) (_q : Query _v)  : (e9438 _v) := by
  have p9437 := n9437 _v _q 
  have p2149 := n2149 _v _q 
  change ((e989 _v) ↔ (e2158 _v)) at p9437
  change ((e984 _v) = (e2147 _v)) at p2149
  simp only [e9438, e991, e6227, p9437, p2149]
theorem n9442 (_v : Vars) (_q : Query _v)  : (e9441 _v) := by
  have p9434 := n9434 _v _q 
  have p9439 := n9439 _v _q 
  change ((e1658 _v) ↔ (e269 _v)) at p9434
  change ((e991 _v) = (e6227 _v)) at p9439
  simp only [e9441, e5619, e9440, p9434, p9439]
theorem n9443 (_v : Vars) (_q : Query _v)  : (e2163 _v) := by
  have p2161 := n2161 _v _q 
  change ((e994 _v) = (e2159 _v)) at p2161
  simp only [e2163, e1665, e2162, p2161]
theorem n9444 (_v : Vars) (_q : Query _v)  : (e6228 _v) := by
  simp only [e5, e6, e8, e12, e41, e108, e109, e111, e802, e803, e2159, e2162, e2164, e2165, e6228] at *
  omega
theorem n9445 (_v : Vars) (_q : Query _v)  : (e6229 _v) := by
  have p9443 := n9443 _v _q 
  have p9444 := n9444 _v _q 
  exact (Iff.trans p9443 p9444)
theorem n9446 (_v : Vars) (_q : Query _v)  : (e2170 _v) := by
  have p2168 := n2168 _v _q 
  change ((e998 _v) = (e2166 _v)) at p2168
  simp only [e2170, e999, e2169, p2168]
theorem n9447 (_v : Vars) (_q : Query _v)  : (e6230 _v) := by
  simp only [e5, e6, e8, e12, e108, e109, e111, e802, e803, e2166, e2169, e2171, e2172, e6230] at *
  omega
theorem n9448 (_v : Vars) (_q : Query _v)  : (e6231 _v) := by
  have p9446 := n9446 _v _q 
  have p9447 := n9447 _v _q 
  exact (Iff.trans p9446 p9447)
theorem n9450 (_v : Vars) (_q : Query _v)  : (e9449 _v) := by
  have p9448 := n9448 _v _q 
  have p2161 := n2161 _v _q 
  change ((e999 _v) ↔ (e2172 _v)) at p9448
  change ((e994 _v) = (e2159 _v)) at p2161
  simp only [e9449, e1001, e6232, p9448, p2161]
theorem n9453 (_v : Vars) (_q : Query _v)  : (e9452 _v) := by
  have p9445 := n9445 _v _q 
  have p9450 := n9450 _v _q 
  change ((e1665 _v) ↔ (e2165 _v)) at p9445
  change ((e1001 _v) = (e6232 _v)) at p9450
  simp only [e9452, e5629, e9451, p9445, p9450]
theorem n9454 (_v : Vars) (_q : Query _v)  : (e2177 _v) := by
  have p2175 := n2175 _v _q 
  change ((e1013 _v) = (e2173 _v)) at p2175
  simp only [e2177, e1672, e2176, p2175]
theorem n9455 (_v : Vars) (_q : Query _v)  : (e6233 _v) := by
  simp only [e5, e6, e10, e12, e36, e41, e2173, e2176, e2178, e2179, e6233] at *
  omega
theorem n9456 (_v : Vars) (_q : Query _v)  : (e6234 _v) := by
  have p9454 := n9454 _v _q 
  have p9455 := n9455 _v _q 
  exact (Iff.trans p9454 p9455)
theorem n9457 (_v : Vars) (_q : Query _v)  : (e2184 _v) := by
  have p2182 := n2182 _v _q 
  change ((e1018 _v) = (e2180 _v)) at p2182
  simp only [e2184, e1019, e2183, p2182]
theorem n9458 (_v : Vars) (_q : Query _v)  : (e2185 _v) := by
  simp only [e5, e6, e10, e12, e36, e184, e185, e2180, e2183, e2185] at *
  omega
theorem n9459 (_v : Vars) (_q : Query _v)  : (e2186 _v) := by
  have p9457 := n9457 _v _q 
  have p9458 := n9458 _v _q 
  exact (Iff.trans p9457 p9458)
theorem n9461 (_v : Vars) (_q : Query _v)  : (e9460 _v) := by
  have p9459 := n9459 _v _q 
  have p2175 := n2175 _v _q 
  change ((e1019 _v) ↔ (e185 _v)) at p9459
  change ((e1013 _v) = (e2173 _v)) at p2175
  simp only [e9460, e1021, e2187, p9459, p2175]
theorem n9464 (_v : Vars) (_q : Query _v)  : (e9463 _v) := by
  have p9456 := n9456 _v _q 
  have p9461 := n9461 _v _q 
  change ((e1672 _v) ↔ (e2179 _v)) at p9456
  change ((e1021 _v) = (e2187 _v)) at p9461
  simp only [e9463, e5634, e9462, p9456, p9461]
theorem n9465 (_v : Vars) (_q : Query _v)  : (e2192 _v) := by
  have p2190 := n2190 _v _q 
  change ((e1029 _v) = (e2188 _v)) at p2190
  simp only [e2192, e1679, e2191, p2190]
theorem n9466 (_v : Vars) (_q : Query _v)  : (e6235 _v) := by
  simp only [e5, e6, e10, e12, e41, e43, e44, e760, e761, e2188, e2191, e2193, e2194, e6235] at *
  omega
theorem n9467 (_v : Vars) (_q : Query _v)  : (e6236 _v) := by
  have p9465 := n9465 _v _q 
  have p9466 := n9466 _v _q 
  exact (Iff.trans p9465 p9466)
theorem n9468 (_v : Vars) (_q : Query _v)  : (e2199 _v) := by
  have p2197 := n2197 _v _q 
  change ((e1035 _v) = (e2195 _v)) at p2197
  simp only [e2199, e1036, e2198, p2197]
theorem n9469 (_v : Vars) (_q : Query _v)  : (e2202 _v) := by
  simp only [e5, e6, e10, e12, e43, e44, e760, e761, e2195, e2198, e2200, e2201, e2202] at *
  omega
theorem n9470 (_v : Vars) (_q : Query _v)  : (e2203 _v) := by
  have p9468 := n9468 _v _q 
  have p9469 := n9469 _v _q 
  exact (Iff.trans p9468 p9469)
theorem n9472 (_v : Vars) (_q : Query _v)  : (e9471 _v) := by
  have p9470 := n9470 _v _q 
  have p2190 := n2190 _v _q 
  change ((e1036 _v) ↔ (e2201 _v)) at p9470
  change ((e1029 _v) = (e2188 _v)) at p2190
  simp only [e9471, e1038, e2204, p9470, p2190]
theorem n9475 (_v : Vars) (_q : Query _v)  : (e9474 _v) := by
  have p9467 := n9467 _v _q 
  have p9472 := n9472 _v _q 
  change ((e1679 _v) ↔ (e2194 _v)) at p9467
  change ((e1038 _v) = (e2204 _v)) at p9472
  simp only [e9474, e5644, e9473, p9467, p9472]
theorem n9476 (_v : Vars) (_q : Query _v)  : (e2209 _v) := by
  have p2207 := n2207 _v _q 
  change ((e1046 _v) = (e2205 _v)) at p2207
  simp only [e2209, e1686, e2208, p2207]
theorem n9477 (_v : Vars) (_q : Query _v)  : (e6237 _v) := by
  simp only [e5, e6, e10, e12, e41, e266, e267, e304, e305, e781, e782, e2205, e2208, e6237] at *
  omega
end
end Assembly
