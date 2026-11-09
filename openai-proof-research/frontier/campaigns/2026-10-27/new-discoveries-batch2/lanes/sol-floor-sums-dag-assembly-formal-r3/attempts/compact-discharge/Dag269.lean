import Dag268
import generated.th_lemma_36
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n22292 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) : (e5148 _v) := by
  have p22291 := n22291 _v _q 
  have p16729 := n16729 _v _q h51
  simp only [e51, e57, e5145, e5148, e22290] at *
  tauto
theorem n22293 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) : (e5149 _v) := by
  have p15925 := n15925 _v _q 
  have p22292 := n22292 _v _q h51
  simp only [e5143, e5145, e5147, e5148, e5149, e5152] at *
  tauto
theorem n22294 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) : (e79 _v) := by
  have p15115 := n15115 _v _q 
  have p22293 := n22293 _v _q h51
  simp only [e79, e5143, e5145, e5147, e5148, e5149, e5150, e8647] at *
  tauto
theorem n22295 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) : (e5135 _v) := by
  have p14729 := n14729 _v _q 
  have p22294 := n22294 _v _q h51
  simp only [e79, e89, e91, e94, e95, e5134, e5135, e5138, e5140] at *
  tauto
theorem n22296 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) : (e91 _v) := by
  have p16235 := n16235 _v _q 
  have p22295 := n22295 _v _q h51
  simp only [e89, e91, e94, e95, e5134, e5135, e7983] at *
  tauto
theorem n22297 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) : (e7489 _v) := by
  have p22285 := n22285 _v _q h51
  have p5391 := n5391 _v _q 
  have p22288 := n22288 _v _q h51
  have p22292 := n22292 _v _q h51
  have p17117 := n17117 _v _q 
  have p17113 := n17113 _v _q 
  have p20467 := n20467 _v _q 
  have p17133 := n17133 _v _q 
  have p17120 := n17120 _v _q 
  have p22247 := n22247 _v _q h51
  have p22272 := n22272 _v _q h51
  have p17256 := n17256 _v _q 
  have p22273 := n22273 _v _q h51
  have p17089 := n17089 _v _q 
  have p22274 := n22274 _v _q h51
  have p13951 := n13951 _v _q 
  have p17104 := n17104 _v _q 
  have p20470 := n20470 _v _q 
  have p20274 := n20274 _v _q 
  have p17286 := n17286 _v _q h51
  have p17288 := n17288 _v _q h51
  have p19665 := n19665 _v _q 
  have p22256 := n22256 _v _q h51
  have p16778 := n16778 _v _q 
  have p22275 := n22275 _v _q h51
  have p17127 := n17127 _v _q 
  have p17050 := n17050 _v _q 
  have p17122 := n17122 _v _q 
  have p22260 := n22260 _v _q h51
  have p16729 := n16729 _v _q h51
  have p20126 := n20126 _v _q 
  have p20426 := n20426 _v _q 
  have p17110 := n17110 _v _q 
  have p20829 := n20829 _v _q 
  have p20653 := n20653 _v _q 
  have p22244 := n22244 _v _q h51
  have p22263 := n22263 _v _q h51
  have p5257 := n5257 _v _q 
  have p17131 := n17131 _v _q 
  have p17108 := n17108 _v _q 
  have p17294 := n17294 _v _q 
  have p16943 := n16943 _v _q 
  have p17064 := n17064 _v _q 
  have p17067 := n17067 _v _q 
  have p17080 := n17080 _v _q 
  have p17053 := n17053 _v _q 
  have p17072 := n17072 _v _q 
  have p17074 := n17074 _v _q 
  have p17069 := n17069 _v _q 
  have p20096 := n20096 _v _q 
  have p20836 := n20836 _v _q 
  have p20461 := n20461 _v _q 
  have p17874 := n17874 _v _q 
  have p22266 := n22266 _v _q h51
  have p17136 := n17136 _v _q 
  have p17087 := n17087 _v _q 
  have p17055 := n17055 _v _q 
  have p17058 := n17058 _v _q 
  have p17098 := n17098 _v _q 
  have p17083 := n17083 _v _q 
  have p17106 := n17106 _v _q 
  have p17020 := n17020 _v _q 
  have p17093 := n17093 _v _q 
  have p22276 := n22276 _v _q h51
  have p17100 := n17100 _v _q 
  have p17141 := n17141 _v _q 
  have p17102 := n17102 _v _q 
  have p17091 := n17091 _v _q 
  have p17096 := n17096 _v _q 
  have p22271 := n22271 _v _q h51
  have p17758 := n17758 _v _q 
  have p17124 := n17124 _v _q 
  have p19610 := n19610 _v _q 
  have p17111 := n17111 _v _q 
  have p17115 := n17115 _v _q 
  have p17078 := n17078 _v _q 
  have p258 := n258 _v _q 
  have p22296 := n22296 _v _q h51
  exact FloorCertificate.node_22297 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2902 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) p22285 p5391 p22288 p22292 p17117 p17113 p20467 p17133 p17120 p22247 p22272 p17256 p22273 p17089 p22274 p13951 p17104 p20470 p20274 p17286 p17288 p19665 p22256 p16778 p22275 p17127 p17050 p17122 p22260 p16729 p20126 p20426 p17110 p20829 p20653 p22244 p22263 p5257 p17131 p17108 p17294 p16943 p17064 p17067 p17080 p17053 p17072 p17074 p17069 p20096 p20836 p20461 p17874 p22266 p17136 p17087 p17055 p17058 p17098 p17083 p17106 p17020 p17093 p22276 p17100 p17141 p17102 p17091 p17096 p22271 p17758 p17124 p19610 p17111 p17115 p17078 p258 p22296
theorem n22298 (_v : Vars) (_q : Query _v)  : (e57 _v) := by
  by_contra hc
  change ¬ (¬ (e51 _v)) at hc
  have h51 : (e51 _v) := by
    tauto
  have p22297 := n22297 _v _q h51
  exact p22297
theorem n22299 (_v : Vars) (_q : Query _v)  : (e59 _v) := by
  have p14962 := n14962 _v _q 
  have p22298 := n22298 _v _q 
  simp only [e51, e52, e57, e58, e59, e77] at *
  tauto
theorem n22300 (_v : Vars) (_q : Query _v)  : (e5108 _v) := by
  have p14152 := n14152 _v _q 
  have p22299 := n22299 _v _q 
  simp only [e48, e51, e52, e57, e58, e59, e60, e5108, e5125] at *
  tauto
theorem n22301 (_v : Vars) (_q : Query _v)  : (e5119 _v) := by
  have p14487 := n14487 _v _q 
  have p22300 := n22300 _v _q 
  simp only [e48, e70, e72, e75, e76, e5108, e5118, e5119, e5122] at *
  tauto
theorem n22302 (_v : Vars) (_q : Query _v)  : (e70 _v) := by
  have p15648 := n15648 _v _q 
  have p22301 := n22301 _v _q 
  simp only [e70, e72, e75, e76, e5118, e5119, e7441] at *
  tauto
theorem n22303 (_v : Vars) (_q : Query _v)  : (e6750 _v) := by
  have p11369 := n11369 _v _q 
  have p22300 := n22300 _v _q 
  simp only [e48, e2733, e5108, e6750, e11368] at *
  tauto
theorem n22304 (_v : Vars) (_q : Query _v)  : (e6549 _v) := by
  have p11571 := n11571 _v _q 
  have p22303 := n22303 _v _q 
  simp only [e2296, e2733, e6549, e6750, e11570] at *
  tauto
theorem n22305 (_v : Vars) (_q : Query _v)  : (e6776 _v) := by
  have p8424 := n8424 _v _q 
  have p22303 := n22303 _v _q 
  simp only [e2733, e2781, e6750, e6776, e8423] at *
  tauto
theorem n22306 (_v : Vars) (_q : Query _v)  : (e7597 _v) := by
  have p14525 := n14525 _v _q 
  have p22303 := n22303 _v _q 
  simp only [e2733, e4096, e4097, e4098, e4099, e6750, e7589, e7597, e7600] at *
  tauto
theorem n22307 (_v : Vars) (_q : Query _v)  : (e6525 _v) := by
  have p10893 := n10893 _v _q 
  have p22300 := n22300 _v _q 
  exact FloorCertificate.node_22307 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) p10893 p22300
theorem n22308 (_v : Vars) (_q : Query _v)  : (e8174 _v) := by
  have p14634 := n14634 _v _q 
  have p22307 := n22307 _v _q 
  simp only [e2242, e4673, e4674, e4675, e4676, e6525, e8166, e8174, e8177] at *
  tauto
theorem n22309 (_v : Vars) (_q : Query _v)  : (e6630 _v) := by
  have p10896 := n10896 _v _q 
  have p22300 := n22300 _v _q 
  exact FloorCertificate.node_22309 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) p10896 p22300
theorem n22310 (_v : Vars) (_q : Query _v)  : (e8275 _v) := by
  have p14655 := n14655 _v _q 
  have p22309 := n22309 _v _q 
  simp only [e2468, e4785, e4786, e4787, e4788, e6630, e8267, e8275, e8278] at *
  tauto
theorem n22311 (_v : Vars) (_q : Query _v)  : (e6650 _v) := by
  have p22300 := n22300 _v _q 
  have p10896 := n10896 _v _q 
  have p5257 := n5257 _v _q 
  exact FloorCertificate.node_22311 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p22300 p10896 p5257
theorem n22312 (_v : Vars) (_q : Query _v)  : (e8292 _v) := by
  have p14657 := n14657 _v _q 
  have p22311 := n22311 _v _q 
  simp only [e2522, e4811, e4812, e4813, e4814, e6650, e8284, e8292, e8295] at *
  tauto
theorem n22313 (_v : Vars) (_q : Query _v) (h2402 : (e2402 _v)) : (e2303 _v) := by
  have p8591 := n8591 _v _q h2402
  have p5257 := n5257 _v _q 
  have p22300 := n22300 _v _q 
  exact FloorCertificate.node_22313 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8591 p5257 p22300
theorem n22314 (_v : Vars) (_q : Query _v) (h2402 : (e2402 _v)) : (e7804 _v) := by
  have p14837 := n14837 _v _q 
  have p22313 := n22313 _v _q h2402
  simp only [e2303, e4283, e4284, e4285, e4286, e7798, e7804, e7807, e7809] at *
  tauto
theorem n22315 (_v : Vars) (_q : Query _v) (h2402 : (e2402 _v)) : (e13 _v) := by
  have p22300 := n22300 _v _q 
  have p8591 := n8591 _v _q h2402
  exact FloorCertificate.node_22315 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) p22300 p8591
theorem n22316 (_v : Vars) (_q : Query _v) (h2402 : (e2402 _v)) : (e5090 _v) := by
  have p14728 := n14728 _v _q 
  have p22315 := n22315 _v _q h2402
  simp only [e13, e28, e30, e34, e35, e5089, e5090, e5093, e5095] at *
  tauto
theorem n22317 (_v : Vars) (_q : Query _v)  : (e6879 _v) := by
  have p14643 := n14643 _v _q 
  have p22304 := n22304 _v _q 
  simp only [e2296, e3150, e3152, e3155, e3156, e6549, e6878, e6879, e6882] at *
  tauto
theorem n22318 (_v : Vars) (_q : Query _v)  : (e3152 _v) := by
  have p15776 := n15776 _v _q 
  have p22317 := n22317 _v _q 
  simp only [e3150, e3152, e3155, e3156, e6878, e6879, e8223] at *
  tauto
theorem n22319 (_v : Vars) (_q : Query _v)  : (e7789 _v) := by
  have p14570 := n14570 _v _q 
  have p22305 := n22305 _v _q 
  simp only [e2781, e4258, e4259, e4260, e4261, e6776, e7781, e7789, e7792] at *
  tauto
theorem n22320 (_v : Vars) (_q : Query _v)  : (e4260 _v) := by
  have p15824 := n15824 _v _q 
  have p22319 := n22319 _v _q 
  simp only [e4258, e4259, e4260, e4261, e7781, e7782, e7789] at *
  tauto
theorem n22321 (_v : Vars) (_q : Query _v)  : (e4096 _v) := by
  have p15703 := n15703 _v _q 
  have p22306 := n22306 _v _q 
  simp only [e4096, e4097, e4098, e4099, e7589, e7590, e7597] at *
  tauto
theorem n22322 (_v : Vars) (_q : Query _v)  : (e4675 _v) := by
  have p15965 := n15965 _v _q 
  have p22308 := n22308 _v _q 
  simp only [e4673, e4674, e4675, e4676, e8166, e8167, e8174] at *
  tauto
theorem n22323 (_v : Vars) (_q : Query _v)  : (e4787 _v) := by
  have p15670 := n15670 _v _q 
  have p22310 := n22310 _v _q 
  simp only [e4785, e4786, e4787, e4788, e8267, e8268, e8275] at *
  tauto
theorem n22324 (_v : Vars) (_q : Query _v)  : (e4813 _v) := by
  have p16259 := n16259 _v _q 
  have p22312 := n22312 _v _q 
  simp only [e4811, e4812, e4813, e4814, e8284, e8285, e8292] at *
  tauto
theorem n22325 (_v : Vars) (_q : Query _v) (h2402 : (e2402 _v)) : (e4285 _v) := by
  have p16274 := n16274 _v _q 
  have p22314 := n22314 _v _q h2402
  simp only [e4283, e4284, e4285, e4286, e7798, e7799, e7804] at *
  tauto
theorem n22326 (_v : Vars) (_q : Query _v) (h2402 : (e2402 _v)) : (e30 _v) := by
  have p16290 := n16290 _v _q 
  have p22316 := n22316 _v _q h2402
  simp only [e28, e30, e34, e35, e5089, e5090, e5107] at *
  tauto
theorem n22328 (_v : Vars) (_q : Query _v)  : (e22327 _v) := by
  by_contra hc
  change ¬ ((e48 _v) ∨ (¬ (e4260 _v)) ∨ (e1995 _v)) at hc
  have h4260 : (e4260 _v) := by
    tauto
  have h5108 : (e5108 _v) := by
    change (¬ (e48 _v))
    tauto
  have h6423 : (e6423 _v) := by
    change (¬ (e1995 _v))
    tauto
  have p21141 := n21141 _v _q h4260 h5108 h6423
  exact p21141
theorem n22329 (_v : Vars) (_q : Query _v)  : (e1995 _v) := by
  have p22328 := n22328 _v _q 
  have p22320 := n22320 _v _q 
  have p22300 := n22300 _v _q 
  simp only [e48, e1995, e4260, e4261, e5108, e22327] at *
  tauto
theorem n22331 (_v : Vars) (_q : Query _v)  : (e22330 _v) := by
  have p20056 := n20056 _v _q 
  have p17020 := n17020 _v _q 
  have p20461 := n20461 _v _q 
  have p20829 := n20829 _v _q 
  have p20836 := n20836 _v _q 
  have p16943 := n16943 _v _q 
  have p20426 := n20426 _v _q 
  have p20653 := n20653 _v _q 
  simp only [e70, e75, e91, e95, e225, e230, e442, e443, e488, e493, e2179, e3069, e3074, e3152, e3156, e4096, e4097, e4156, e4157, e4199, e4200, e4260, e4261, e4369, e4370, e4434, e4435, e4675, e4676, e4787, e4788, e4813, e4814, e20055, e22330] at *
  tauto
theorem n22332 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h4675 : (e4675 _v)) (h6454 : (e6454 _v)) : (e2179 _v) := by
  have p22331 := n22331 _v _q 
  have p15764 := n15764 _v _q h6454
  have p22302 := n22302 _v _q 
  have p4999 := n4999 _v _q h91
  have p22323 := n22323 _v _q 
  have p22324 := n22324 _v _q 
  have p22318 := n22318 _v _q 
  have p22320 := n22320 _v _q 
  have p5006 := n5006 _v _q h4675
  have p22321 := n22321 _v _q 
  simp only [e70, e75, e91, e95, e2179, e3152, e3156, e4096, e4097, e4260, e4261, e4434, e4435, e4675, e4676, e4787, e4788, e4813, e4814, e22330] at *
  tauto
theorem n22333 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h4675 : (e4675 _v)) (h6454 : (e6454 _v)) : (e4616 _v) := by
  have p14684 := n14684 _v _q 
  have p22332 := n22332 _v _q h91 h4675 h6454
  simp only [e2179, e3158, e3159, e3160, e3161, e3162, e4616, e6501, e8109] at *
  tauto
theorem n22334 (_v : Vars) (_q : Query _v)  : (e79 _v) := by
  have p22300 := n22300 _v _q 
  have p22329 := n22329 _v _q 
  exact FloorCertificate.node_22334 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) p22300 p22329
theorem n22335 (_v : Vars) (_q : Query _v)  : (e5135 _v) := by
  have p14729 := n14729 _v _q 
  have p22334 := n22334 _v _q 
  simp only [e79, e89, e91, e94, e95, e5134, e5135, e5138, e5140] at *
  tauto
theorem n22336 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h4675 : (e4675 _v)) (h6454 : (e6454 _v)) : (e3158 _v) := by
  have p15126 := n15126 _v _q 
  have p22333 := n22333 _v _q h91 h4675 h6454
  simp only [e3158, e3159, e3160, e3161, e3162, e3163, e4616] at *
  tauto
theorem n22337 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h4675 : (e4675 _v)) (h6454 : (e6454 _v)) : (e7489 _v) := by
  have p5255 := n5255 _v _q 
  have p22336 := n22336 _v _q h91 h4675 h6454
  have p16578 := n16578 _v _q 
  have p8430 := n8430 _v _q h6454
  have p16858 := n16858 _v _q 
  exact FloorCertificate.node_22337 (e2 _v) (e9 _v) (e17 _v) (e110 _v) (e2863 _v) (e2935 _v) p5255 p22336 p16578 p8430 p16858
theorem n22339 (_v : Vars) (_q : Query _v)  : (e22338 _v) := by
  by_contra hc
  change ¬ ((e2061 _v) ∨ (¬ (e91 _v)) ∨ (¬ (e4675 _v))) at hc
  have h91 : (e91 _v) := by
    tauto
  have h4675 : (e4675 _v) := by
    tauto
  have h6454 : (e6454 _v) := by
    change (¬ (e2061 _v))
    tauto
  have p22337 := n22337 _v _q h91 h4675 h6454
  exact p22337
end
end Assembly
