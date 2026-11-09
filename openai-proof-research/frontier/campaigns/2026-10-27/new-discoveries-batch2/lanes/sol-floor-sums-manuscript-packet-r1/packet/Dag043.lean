import Dag042
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n9355 (_v : Vars) (_q : Query _v)  : (e2042 _v) := by
  have p2040 := n2040 _v _q 
  change ((e877 _v) = (e2038 _v)) at p2040
  simp only [e2042, e1609, e2041, p2040]
theorem n9356 (_v : Vars) (_q : Query _v)  : (e6203 _v) := by
  simp only [e5, e6, e8, e12, e41, e108, e109, e802, e803, e2038, e2041, e2043, e2044, e6203] at *
  omega
theorem n9357 (_v : Vars) (_q : Query _v)  : (e6204 _v) := by
  have p9355 := n9355 _v _q 
  have p9356 := n9356 _v _q 
  exact (Iff.trans p9355 p9356)
theorem n9358 (_v : Vars) (_q : Query _v)  : (e2049 _v) := by
  have p2047 := n2047 _v _q 
  change ((e883 _v) = (e2045 _v)) at p2047
  simp only [e2049, e884, e2048, p2047]
theorem n9359 (_v : Vars) (_q : Query _v)  : (e2052 _v) := by
  simp only [e5, e6, e8, e12, e108, e109, e802, e803, e2045, e2048, e2050, e2051, e2052] at *
  omega
theorem n9360 (_v : Vars) (_q : Query _v)  : (e2053 _v) := by
  have p9358 := n9358 _v _q 
  have p9359 := n9359 _v _q 
  exact (Iff.trans p9358 p9359)
theorem n9362 (_v : Vars) (_q : Query _v)  : (e9361 _v) := by
  have p9360 := n9360 _v _q 
  have p2040 := n2040 _v _q 
  change ((e884 _v) ↔ (e2051 _v)) at p9360
  change ((e877 _v) = (e2038 _v)) at p2040
  simp only [e9361, e886, e2054, p9360, p2040]
theorem n9365 (_v : Vars) (_q : Query _v)  : (e9364 _v) := by
  have p9357 := n9357 _v _q 
  have p9362 := n9362 _v _q 
  change ((e1609 _v) ↔ (e2044 _v)) at p9357
  change ((e886 _v) = (e2054 _v)) at p9362
  simp only [e9364, e5558, e9363, p9357, p9362]
theorem n9366 (_v : Vars) (_q : Query _v)  : (e2059 _v) := by
  have p2057 := n2057 _v _q 
  change ((e898 _v) = (e2055 _v)) at p2057
  simp only [e2059, e1616, e2058, p2057]
theorem n9367 (_v : Vars) (_q : Query _v)  : (e6205 _v) := by
  simp only [e5, e6, e12, e36, e41, e111, e2055, e2058, e2060, e2061, e6205] at *
  omega
theorem n9368 (_v : Vars) (_q : Query _v)  : (e6206 _v) := by
  have p9366 := n9366 _v _q 
  have p9367 := n9367 _v _q 
  exact (Iff.trans p9366 p9367)
theorem n9369 (_v : Vars) (_q : Query _v)  : (e2066 _v) := by
  have p2064 := n2064 _v _q 
  change ((e903 _v) = (e2062 _v)) at p2064
  simp only [e2066, e904, e2065, p2064]
theorem n9370 (_v : Vars) (_q : Query _v)  : (e2067 _v) := by
  simp only [e5, e6, e12, e36, e111, e173, e174, e2062, e2065, e2067] at *
  omega
theorem n9371 (_v : Vars) (_q : Query _v)  : (e2068 _v) := by
  have p9369 := n9369 _v _q 
  have p9370 := n9370 _v _q 
  exact (Iff.trans p9369 p9370)
theorem n9373 (_v : Vars) (_q : Query _v)  : (e9372 _v) := by
  have p9371 := n9371 _v _q 
  have p2057 := n2057 _v _q 
  change ((e904 _v) ↔ (e174 _v)) at p9371
  change ((e898 _v) = (e2055 _v)) at p2057
  simp only [e9372, e906, e2069, p9371, p2057]
theorem n9376 (_v : Vars) (_q : Query _v)  : (e9375 _v) := by
  have p9368 := n9368 _v _q 
  have p9373 := n9373 _v _q 
  change ((e1616 _v) ↔ (e2061 _v)) at p9368
  change ((e906 _v) = (e2069 _v)) at p9373
  simp only [e9375, e5563, e9374, p9368, p9373]
theorem n9377 (_v : Vars) (_q : Query _v)  : (e2074 _v) := by
  have p2072 := n2072 _v _q 
  change ((e914 _v) = (e2070 _v)) at p2072
  simp only [e2074, e1623, e2073, p2072]
theorem n9378 (_v : Vars) (_q : Query _v)  : (e6207 _v) := by
  simp only [e5, e6, e12, e41, e43, e44, e111, e760, e761, e2070, e2073, e2075, e2076, e6207] at *
  omega
theorem n9379 (_v : Vars) (_q : Query _v)  : (e6208 _v) := by
  have p9377 := n9377 _v _q 
  have p9378 := n9378 _v _q 
  exact (Iff.trans p9377 p9378)
theorem n9380 (_v : Vars) (_q : Query _v)  : (e2081 _v) := by
  have p2079 := n2079 _v _q 
  change ((e920 _v) = (e2077 _v)) at p2079
  simp only [e2081, e921, e2080, p2079]
theorem n9381 (_v : Vars) (_q : Query _v)  : (e2084 _v) := by
  simp only [e5, e6, e12, e43, e44, e111, e760, e761, e2077, e2080, e2082, e2083, e2084] at *
  omega
theorem n9382 (_v : Vars) (_q : Query _v)  : (e2085 _v) := by
  have p9380 := n9380 _v _q 
  have p9381 := n9381 _v _q 
  exact (Iff.trans p9380 p9381)
theorem n9384 (_v : Vars) (_q : Query _v)  : (e9383 _v) := by
  have p9382 := n9382 _v _q 
  have p2072 := n2072 _v _q 
  change ((e921 _v) ↔ (e2083 _v)) at p9382
  change ((e914 _v) = (e2070 _v)) at p2072
  simp only [e9383, e923, e2086, p9382, p2072]
theorem n9387 (_v : Vars) (_q : Query _v)  : (e9386 _v) := by
  have p9379 := n9379 _v _q 
  have p9384 := n9384 _v _q 
  change ((e1623 _v) ↔ (e2076 _v)) at p9379
  change ((e923 _v) = (e2086 _v)) at p9384
  simp only [e9386, e5573, e9385, p9379, p9384]
theorem n9388 (_v : Vars) (_q : Query _v)  : (e2091 _v) := by
  have p2089 := n2089 _v _q 
  change ((e931 _v) = (e2087 _v)) at p2089
  simp only [e2091, e1630, e2090, p2089]
theorem n9389 (_v : Vars) (_q : Query _v)  : (e6209 _v) := by
  simp only [e5, e6, e12, e41, e111, e266, e267, e339, e340, e781, e782, e2087, e2090, e6209] at *
  omega
theorem n9390 (_v : Vars) (_q : Query _v)  : (e6210 _v) := by
  have p9388 := n9388 _v _q 
  have p9389 := n9389 _v _q 
  exact (Iff.trans p9388 p9389)
theorem n9391 (_v : Vars) (_q : Query _v)  : (e2096 _v) := by
  have p2094 := n2094 _v _q 
  change ((e937 _v) = (e2092 _v)) at p2094
  simp only [e2096, e938, e2095, p2094]
theorem n9392 (_v : Vars) (_q : Query _v)  : (e2099 _v) := by
  simp only [e5, e6, e12, e111, e266, e267, e781, e782, e2092, e2095, e2097, e2098, e2099] at *
  omega
theorem n9393 (_v : Vars) (_q : Query _v)  : (e2100 _v) := by
  have p9391 := n9391 _v _q 
  have p9392 := n9392 _v _q 
  exact (Iff.trans p9391 p9392)
theorem n9395 (_v : Vars) (_q : Query _v)  : (e9394 _v) := by
  have p9393 := n9393 _v _q 
  have p2089 := n2089 _v _q 
  change ((e938 _v) ↔ (e2098 _v)) at p9393
  change ((e931 _v) = (e2087 _v)) at p2089
  simp only [e9394, e940, e2101, p9393, p2089]
theorem n9398 (_v : Vars) (_q : Query _v)  : (e9397 _v) := by
  have p9390 := n9390 _v _q 
  have p9395 := n9395 _v _q 
  change ((e1630 _v) ↔ (e340 _v)) at p9390
  change ((e940 _v) = (e2101 _v)) at p9395
  simp only [e9397, e5583, e9396, p9390, p9395]
theorem n9399 (_v : Vars) (_q : Query _v)  : (e2106 _v) := by
  have p2104 := n2104 _v _q 
  change ((e948 _v) = (e2102 _v)) at p2104
  simp only [e2106, e1637, e2105, p2104]
theorem n9400 (_v : Vars) (_q : Query _v)  : (e6211 _v) := by
  simp only [e5, e6, e12, e41, e108, e109, e111, e802, e803, e2102, e2105, e2107, e2108, e6211] at *
  omega
theorem n9401 (_v : Vars) (_q : Query _v)  : (e6212 _v) := by
  have p9399 := n9399 _v _q 
  have p9400 := n9400 _v _q 
  exact (Iff.trans p9399 p9400)
theorem n9402 (_v : Vars) (_q : Query _v)  : (e2113 _v) := by
  have p2111 := n2111 _v _q 
  change ((e954 _v) = (e2109 _v)) at p2111
  simp only [e2113, e955, e2112, p2111]
theorem n9403 (_v : Vars) (_q : Query _v)  : (e2116 _v) := by
  simp only [e5, e6, e12, e108, e109, e111, e802, e803, e2109, e2112, e2114, e2115, e2116] at *
  omega
theorem n9404 (_v : Vars) (_q : Query _v)  : (e2117 _v) := by
  have p9402 := n9402 _v _q 
  have p9403 := n9403 _v _q 
  exact (Iff.trans p9402 p9403)
theorem n9406 (_v : Vars) (_q : Query _v)  : (e9405 _v) := by
  have p9404 := n9404 _v _q 
  have p2104 := n2104 _v _q 
  change ((e955 _v) ↔ (e2115 _v)) at p9404
  change ((e948 _v) = (e2102 _v)) at p2104
  simp only [e9405, e957, e2118, p9404, p2104]
theorem n9409 (_v : Vars) (_q : Query _v)  : (e9408 _v) := by
  have p9401 := n9401 _v _q 
  have p9406 := n9406 _v _q 
  change ((e1637 _v) ↔ (e2108 _v)) at p9401
  change ((e957 _v) = (e2118 _v)) at p9406
  simp only [e9408, e5593, e9407, p9401, p9406]
theorem n9410 (_v : Vars) (_q : Query _v)  : (e2123 _v) := by
  have p2121 := n2121 _v _q 
  change ((e964 _v) = (e2119 _v)) at p2121
  simp only [e2123, e1644, e2122, p2121]
theorem n9411 (_v : Vars) (_q : Query _v)  : (e6213 _v) := by
  simp only [e5, e6, e8, e12, e36, e41, e111, e2119, e2122, e2124, e2125, e6213] at *
  omega
theorem n9412 (_v : Vars) (_q : Query _v)  : (e6214 _v) := by
  have p9410 := n9410 _v _q 
  have p9411 := n9411 _v _q 
  exact (Iff.trans p9410 p9411)
theorem n9413 (_v : Vars) (_q : Query _v)  : (e2130 _v) := by
  have p2128 := n2128 _v _q 
  change ((e968 _v) = (e2126 _v)) at p2128
  simp only [e2130, e969, e2129, p2128]
theorem n9414 (_v : Vars) (_q : Query _v)  : (e6215 _v) := by
  simp only [e5, e6, e8, e12, e36, e111, e2126, e2129, e2131, e2132, e6215] at *
  omega
end
end Assembly
