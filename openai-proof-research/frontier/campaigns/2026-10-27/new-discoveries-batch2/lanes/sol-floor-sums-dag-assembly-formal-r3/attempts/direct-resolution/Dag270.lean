import Dag269
import generated.th_lemma_36
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n22340 (_v : Vars) (_q : Query _v)  : (e4575 _v) := by
  have p14696 := n14696 _v _q 
  have p22329 := n22329 _v _q 
  simp only [e1995, e4567, e4568, e4572, e4573, e4574, e4575, e6423, e8066] at *
  tauto
theorem n22341 (_v : Vars) (_q : Query _v)  : (e4567 _v) := by
  have p8485 := n8485 _v _q 
  have p22340 := n22340 _v _q 
  simp only [e4567, e4568, e4572, e4573, e4574, e4575, e4956] at *
  tauto
theorem n22342 (_v : Vars) (_q : Query _v) (h6583 : (e6583 _v)) (h7807 : (e7807 _v)) : (e7489 _v) := by
  have p22329 := n22329 _v _q 
  have p11340 := n11340 _v _q h6583
  have p11350 := n11350 _v _q h7807
  exact FloorCertificate.node_22342 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e110 _v) p22329 p11340 p11350
theorem n22344 (_v : Vars) (_q : Query _v)  : (e22343 _v) := by
  by_contra hc
  change ¬ ((e2303 _v) ∨ (e2364 _v)) at hc
  have h6583 : (e6583 _v) := (fun hn => hc (Or.inr hn))
  have h7807 : (e7807 _v) := (fun hn => hc (Or.inl hn))
  have p22342 := n22342 _v _q h6583 h7807
  exact p22342
theorem n22345 (_v : Vars) (_q : Query _v) (h6676 : (e6676 _v)) : (e2529 _v) := by
  have p10943 := n10943 _v _q h6676
  have p22329 := n22329 _v _q 
  exact FloorCertificate.node_22345 (e2 _v) (e7 _v) (e17 _v) (e45 _v) (e110 _v) p10943 p22329
theorem n22346 (_v : Vars) (_q : Query _v) (h6676 : (e6676 _v)) : (e8307 _v) := by
  have p14906 := n14906 _v _q 
  have p22345 := n22345 _v _q h6676
  simp only [e2529, e4836, e4837, e4838, e4839, e8301, e8307, e8310, e8312] at *
  tauto
theorem n22347 (_v : Vars) (_q : Query _v)  : (e91 _v) := by
  have p16235 := n16235 _v _q 
  have p22335 := n22335 _v _q 
  simp only [e89, e91, e94, e95, e5134, e5135, e7983] at *
  tauto
theorem n22348 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h4675 : (e4675 _v)) : (e2061 _v) := by
  have p22339 := n22339 _v _q 
  have p4999 := n4999 _v _q h91
  have p5006 := n5006 _v _q h4675
  simp only [e91, e95, e2061, e4675, e4676, e22338] at *
  tauto
theorem n22349 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h4675 : (e4675 _v)) : (e4447 _v) := by
  have p14688 := n14688 _v _q 
  have p22348 := n22348 _v _q h91 h4675
  simp only [e2061, e4439, e4440, e4444, e4445, e4446, e4447, e6454, e7961] at *
  tauto
theorem n22350 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h4675 : (e4675 _v)) : (e4439 _v) := by
  have p14925 := n14925 _v _q 
  have p22349 := n22349 _v _q h91 h4675
  simp only [e4439, e4440, e4444, e4445, e4446, e4447, e4941] at *
  tauto
theorem n22351 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h191 : (e191 _v)) (h4675 : (e4675 _v)) (h4838 : (e4838 _v)) (h6501 : (e6501 _v)) : (e7742 _v) := by
  have p20854 := n20854 _v _q 
  have p8554 := n8554 _v _q h6501
  have p4989 := n4989 _v _q h4838
  have p22318 := n22318 _v _q 
  have p253 := n253 _v _q h191
  have p5006 := n5006 _v _q h4675
  have p4999 := n4999 _v _q h91
  have p22324 := n22324 _v _q 
  have p22323 := n22323 _v _q 
  have p22320 := n22320 _v _q 
  have p22348 := n22348 _v _q h91 h4675
  simp only [e91, e95, e191, e192, e2061, e2132, e2179, e3152, e3156, e4260, e4261, e4675, e4676, e4787, e4788, e4813, e4814, e4838, e4839, e6454, e6501, e7742, e20853] at *
  tauto
theorem n22352 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h191 : (e191 _v)) (h4675 : (e4675 _v)) (h4838 : (e4838 _v)) (h6501 : (e6501 _v)) : (e7754 _v) := by
  have p14942 := n14942 _v _q 
  have p22351 := n22351 _v _q h91 h191 h4675 h4838 h6501
  simp only [e2132, e7742, e7747, e7749, e7751, e7752, e7753, e7754, e11001] at *
  tauto
theorem n22353 (_v : Vars) (_q : Query _v) (h6583 : (e6583 _v)) : (e2303 _v) := by
  have p22344 := n22344 _v _q 
  have p11340 := n11340 _v _q h6583
  simp only [e2303, e2364, e6583, e22343] at *
  tauto
theorem n22354 (_v : Vars) (_q : Query _v) (h6583 : (e6583 _v)) : (e79 _v) := by
  have p11490 := n11490 _v _q 
  have p22353 := n22353 _v _q h6583
  simp only [e79, e2303, e7807, e11489] at *
  tauto
theorem n22355 (_v : Vars) (_q : Query _v) (h6583 : (e6583 _v)) : (e7804 _v) := by
  have p14837 := n14837 _v _q 
  have p22353 := n22353 _v _q h6583
  simp only [e2303, e4283, e4284, e4285, e4286, e7798, e7804, e7807, e7809] at *
  tauto
theorem n22356 (_v : Vars) (_q : Query _v) (h6583 : (e6583 _v)) : (e2529 _v) := by
  have p11387 := n11387 _v _q 
  have p22353 := n22353 _v _q h6583
  simp only [e2303, e2529, e7807, e11386] at *
  tauto
theorem n22357 (_v : Vars) (_q : Query _v) (h6676 : (e6676 _v)) : (e4838 _v) := by
  have p16285 := n16285 _v _q 
  have p22346 := n22346 _v _q h6676
  simp only [e4836, e4837, e4838, e4839, e8301, e8302, e8307] at *
  tauto
theorem n22358 (_v : Vars) (_q : Query _v) (h3937 : (e3937 _v)) (h4608 : (e4608 _v)) (h8038 : (e8038 _v)) : (e2634 _v) := by
  have p20871 := n20871 _v _q 
  have p8602 := n8602 _v _q h8038
  have p22302 := n22302 _v _q 
  have p22318 := n22318 _v _q 
  have p22347 := n22347 _v _q 
  have p22321 := n22321 _v _q 
  have p22322 := n22322 _v _q 
  have p22323 := n22323 _v _q 
  have p4991 := n4991 _v _q h4608
  have p22320 := n22320 _v _q 
  have p4996 := n4996 _v _q h3937
  have p22324 := n22324 _v _q 
  simp only [e70, e75, e91, e95, e2475, e2634, e3152, e3156, e3937, e3942, e4096, e4097, e4260, e4261, e4608, e4609, e4675, e4676, e4787, e4788, e4813, e4814, e8038, e20870] at *
  tauto
theorem n22359 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h191 : (e191 _v)) (h4675 : (e4675 _v)) (h4838 : (e4838 _v)) (h6501 : (e6501 _v)) : (e7749 _v) := by
  have p14941 := n14941 _v _q 
  have p22352 := n22352 _v _q h91 h191 h4675 h4838 h6501
  simp only [e7747, e7749, e7751, e7752, e7753, e7754, e8446] at *
  tauto
theorem n22360 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h4139 : (e4139 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4419 : (e4419 _v)) (h4546 : (e4546 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4838 : (e4838 _v)) (h6501 : (e6501 _v)) : (e7489 _v) := by
  have p10893 := n10893 _v _q 
  have p10896 := n10896 _v _q 
  have p5000 := n5000 _v _q h30
  have p16994 := n16994 _v _q 
  have p4980 := n4980 _v _q h4301
  have p16913 := n16913 _v _q 
  have p22329 := n22329 _v _q 
  have p22348 := n22348 _v _q h91 h4675
  have p22350 := n22350 _v _q h91 h4675
  have p22323 := n22323 _v _q 
  have p16911 := n16911 _v _q 
  have p4971 := n4971 _v _q h4419
  have p22302 := n22302 _v _q 
  have p13951 := n13951 _v _q 
  have p15641 := n15641 _v _q h6501
  have p17147 := n17147 _v _q 
  have p16576 := n16576 _v _q 
  have p16325 := n16325 _v _q h6501
  have p22320 := n22320 _v _q 
  have p4979 := n4979 _v _q h4139
  have p17115 := n17115 _v _q 
  have p253 := n253 _v _q h191
  have p17078 := n17078 _v _q 
  have p17117 := n17117 _v _q 
  have p17113 := n17113 _v _q 
  have p20467 := n20467 _v _q 
  have p17133 := n17133 _v _q 
  have p17120 := n17120 _v _q 
  have p22359 := n22359 _v _q h91 h191 h4675 h4838 h6501
  have p17221 := n17221 _v _q 
  have p22321 := n22321 _v _q 
  have p17089 := n17089 _v _q 
  have p22318 := n22318 _v _q 
  have p4999 := n4999 _v _q h91
  have p17104 := n17104 _v _q 
  have p20470 := n20470 _v _q 
  have p20274 := n20274 _v _q 
  have p19665 := n19665 _v _q 
  have p4976 := n4976 _v _q h4546
  have p16778 := n16778 _v _q 
  have p17127 := n17127 _v _q 
  have p17050 := n17050 _v _q 
  have p17122 := n17122 _v _q 
  have p4977 := n4977 _v _q h4285
  have p20126 := n20126 _v _q 
  have p20426 := n20426 _v _q 
  have p17110 := n17110 _v _q 
  have p20829 := n20829 _v _q 
  have p20653 := n20653 _v _q 
  have p4989 := n4989 _v _q h4838
  have p17111 := n17111 _v _q 
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
  have p17136 := n17136 _v _q 
  have p17087 := n17087 _v _q 
  have p17055 := n17055 _v _q 
  have p17058 := n17058 _v _q 
  have p17098 := n17098 _v _q 
  have p17083 := n17083 _v _q 
  have p17106 := n17106 _v _q 
  have p17020 := n17020 _v _q 
  have p17093 := n17093 _v _q 
  have p5006 := n5006 _v _q h4675
  have p17100 := n17100 _v _q 
  have p17141 := n17141 _v _q 
  have p17102 := n17102 _v _q 
  have p17091 := n17091 _v _q 
  have p17096 := n17096 _v _q 
  have p22341 := n22341 _v _q 
  have p17758 := n17758 _v _q 
  have p17124 := n17124 _v _q 
  have p19610 := n19610 _v _q 
  have p4990 := n4990 _v _q h4648
  have p22324 := n22324 _v _q 
  have p17009 := n17009 _v _q 
  exact FloorCertificate.node_22360 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e61 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2863 _v) (e2877 _v) (e2879 _v) (e2883 _v) (e2898 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p10893 p10896 p5000 p16994 p4980 p16913 p22329 p22348 p22350 p22323 p16911 p4971 p22302 p13951 p15641 p17147 p16576 p16325 p22320 p4979 p17115 p253 p17078 p17117 p17113 p20467 p17133 p17120 p22359 p17221 p22321 p17089 p22318 p4999 p17104 p20470 p20274 p19665 p4976 p16778 p17127 p17050 p17122 p4977 p20126 p20426 p17110 p20829 p20653 p4989 p17111 p17131 p17108 p17294 p16943 p17064 p17067 p17080 p17053 p17072 p17074 p17069 p20096 p20836 p20461 p17874 p17136 p17087 p17055 p17058 p17098 p17083 p17106 p17020 p17093 p5006 p17100 p17141 p17102 p17091 p17096 p22341 p17758 p17124 p19610 p4990 p22324 p17009
theorem n22361 (_v : Vars) (_q : Query _v) (h6583 : (e6583 _v)) : (e5135 _v) := by
  have p14729 := n14729 _v _q 
  have p22354 := n22354 _v _q h6583
  simp only [e79, e89, e91, e94, e95, e5134, e5135, e5138, e5140] at *
  tauto
theorem n22362 (_v : Vars) (_q : Query _v) (h6583 : (e6583 _v)) : (e91 _v) := by
  have p16235 := n16235 _v _q 
  have p22361 := n22361 _v _q h6583
  simp only [e89, e91, e94, e95, e5134, e5135, e7983] at *
  tauto
theorem n22363 (_v : Vars) (_q : Query _v) (h6583 : (e6583 _v)) : (e4285 _v) := by
  have p16274 := n16274 _v _q 
  have p22355 := n22355 _v _q h6583
  simp only [e4283, e4284, e4285, e4286, e7798, e7799, e7804] at *
  tauto
theorem n22364 (_v : Vars) (_q : Query _v) (h6583 : (e6583 _v)) : (e8307 _v) := by
  have p14906 := n14906 _v _q 
  have p22356 := n22356 _v _q h6583
  simp only [e2529, e4836, e4837, e4838, e4839, e8301, e8307, e8310, e8312] at *
  tauto
theorem n22365 (_v : Vars) (_q : Query _v) (h6583 : (e6583 _v)) : (e4838 _v) := by
  have p16285 := n16285 _v _q 
  have p22364 := n22364 _v _q h6583
  simp only [e4836, e4837, e4838, e4839, e8301, e8302, e8307] at *
  tauto
theorem n22366 (_v : Vars) (_q : Query _v)  : (e2061 _v) := by
  have p22339 := n22339 _v _q 
  have p22347 := n22347 _v _q 
  have p22322 := n22322 _v _q 
  simp only [e91, e95, e2061, e4675, e4676, e22338] at *
  tauto
theorem n22367 (_v : Vars) (_q : Query _v)  : (e4447 _v) := by
  have p14688 := n14688 _v _q 
  have p22366 := n22366 _v _q 
  simp only [e2061, e4439, e4440, e4444, e4445, e4446, e4447, e6454, e7961] at *
  tauto
theorem n22368 (_v : Vars) (_q : Query _v)  : (e4439 _v) := by
  have p14925 := n14925 _v _q 
  have p22367 := n22367 _v _q 
  simp only [e4439, e4440, e4444, e4445, e4446, e4447, e4941] at *
  tauto
theorem n22369 (_v : Vars) (_q : Query _v) (h6676 : (e6676 _v)) : (e2475 _v) := by
  have p22366 := n22366 _v _q 
  have p10943 := n10943 _v _q h6676
  exact FloorCertificate.node_22369 (e2 _v) (e7 _v) (e17 _v) (e45 _v) (e110 _v) p22366 p10943
theorem n22371 (_v : Vars) (_q : Query _v)  : (e22370 _v) := by
  by_contra hc
  change ¬ ((e2179 _v) ∨ (¬ (e30 _v)) ∨ (¬ (e4301 _v)) ∨ (¬ (e4419 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e4546 _v)) ∨ (¬ (e4285 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4648 _v))) at hc
  have h30 : (e30 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h191 : (e191 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h4139 : (e4139 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4285 : (e4285 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h4301 : (e4301 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4419 : (e4419 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4546 : (e4546 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h4648 : (e4648 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))))))))
  have h4675 : (e4675 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h4838 : (e4838 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h6501 : (e6501 _v) := (fun hn => hc (Or.inl hn))
  have p22360 := n22360 _v _q h30 h91 h191 h4139 h4285 h4301 h4419 h4546 h4648 h4675 h4838 h6501
  exact p22360
theorem n22372 (_v : Vars) (_q : Query _v) (h6583 : (e6583 _v)) : (e2061 _v) := by
  have p22339 := n22339 _v _q 
  have p22362 := n22362 _v _q h6583
  have p16749 := n16749 _v _q h6583
  simp only [e91, e95, e2061, e4675, e4676, e22338] at *
  tauto
theorem n22373 (_v : Vars) (_q : Query _v) (h6583 : (e6583 _v)) : (e13 _v) := by
  have p11340 := n11340 _v _q h6583
  have p22372 := n22372 _v _q h6583
  exact FloorCertificate.node_22373 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e110 _v) p11340 p22372
theorem n22374 (_v : Vars) (_q : Query _v) (h6583 : (e6583 _v)) : (e5090 _v) := by
  have p14728 := n14728 _v _q 
  have p22373 := n22373 _v _q h6583
  simp only [e13, e28, e30, e34, e35, e5089, e5090, e5093, e5095] at *
  tauto
theorem n22375 (_v : Vars) (_q : Query _v) (h6583 : (e6583 _v)) : (e2787 _v) := by
  have p5391 := n5391 _v _q 
  have p22329 := n22329 _v _q 
  have p11340 := n11340 _v _q h6583
  have p22372 := n22372 _v _q h6583
  exact FloorCertificate.node_22375 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p5391 p22329 p11340 p22372
theorem n22376 (_v : Vars) (_q : Query _v) (h6583 : (e6583 _v)) : (e7927 _v) := by
  have p14855 := n14855 _v _q 
  have p22375 := n22375 _v _q h6583
  simp only [e2787, e4417, e4418, e4419, e4420, e6772, e7921, e7927, e7930] at *
  tauto
theorem n22377 (_v : Vars) (_q : Query _v) (h6583 : (e6583 _v)) : (e2475 _v) := by
  have p11340 := n11340 _v _q h6583
  have p5391 := n5391 _v _q 
  have p22372 := n22372 _v _q h6583
  exact FloorCertificate.node_22377 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p11340 p5391 p22372
theorem n22378 (_v : Vars) (_q : Query _v) (h6583 : (e6583 _v)) : (e8035 _v) := by
  have p14871 := n14871 _v _q 
  have p22377 := n22377 _v _q h6583
  simp only [e2475, e4544, e4545, e4546, e4547, e8029, e8035, e8038, e8040] at *
  tauto
theorem n22379 (_v : Vars) (_q : Query _v) (h6676 : (e6676 _v)) : (e8035 _v) := by
  have p14871 := n14871 _v _q 
  have p22369 := n22369 _v _q h6676
  simp only [e2475, e4544, e4545, e4546, e4547, e8029, e8035, e8038, e8040] at *
  tauto
theorem n22380 (_v : Vars) (_q : Query _v) (h6676 : (e6676 _v)) : (e4546 _v) := by
  have p16307 := n16307 _v _q 
  have p22379 := n22379 _v _q h6676
  simp only [e4544, e4545, e4546, e4547, e8029, e8030, e8035] at *
  tauto
theorem n22381 (_v : Vars) (_q : Query _v) (h2303 : (e2303 _v)) (h6676 : (e6676 _v)) : (e2787 _v) := by
  have p8461 := n8461 _v _q 
  have p8448 := n8448 _v _q h2303
  have p22369 := n22369 _v _q h6676
  simp only [e2303, e2475, e2787, e7807, e8038, e8460] at *
  tauto
theorem n22382 (_v : Vars) (_q : Query _v) (h2303 : (e2303 _v)) (h6676 : (e6676 _v)) : (e7927 _v) := by
  have p14855 := n14855 _v _q 
  have p22381 := n22381 _v _q h2303 h6676
  simp only [e2787, e4417, e4418, e4419, e4420, e6772, e7921, e7927, e7930] at *
  tauto
theorem n22383 (_v : Vars) (_q : Query _v) (h2303 : (e2303 _v)) (h6676 : (e6676 _v)) : (e4419 _v) := by
  have p16347 := n16347 _v _q 
  have p22382 := n22382 _v _q h2303 h6676
  simp only [e4417, e4418, e4419, e4420, e7921, e7922, e7927] at *
  tauto
theorem n22384 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h4139 : (e4139 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4419 : (e4419 _v)) (h4546 : (e4546 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4838 : (e4838 _v)) : (e2179 _v) := by
  have p22371 := n22371 _v _q 
  have p5000 := n5000 _v _q h30
  have p4980 := n4980 _v _q h4301
  have p4971 := n4971 _v _q h4419
  have p4979 := n4979 _v _q h4139
  have p253 := n253 _v _q h191
  have p4999 := n4999 _v _q h91
  have p4976 := n4976 _v _q h4546
  have p4977 := n4977 _v _q h4285
  have p4989 := n4989 _v _q h4838
  have p5006 := n5006 _v _q h4675
  have p4990 := n4990 _v _q h4648
  simp only [e30, e35, e91, e95, e191, e192, e2179, e4139, e4140, e4285, e4286, e4301, e4302, e4419, e4420, e4546, e4547, e4648, e4649, e4675, e4676, e4838, e4839, e22370] at *
  tauto
theorem n22385 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h4139 : (e4139 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4419 : (e4419 _v)) (h4546 : (e4546 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4838 : (e4838 _v)) : (e4616 _v) := by
  have p14684 := n14684 _v _q 
  have p22384 := n22384 _v _q h30 h91 h191 h4139 h4285 h4301 h4419 h4546 h4648 h4675 h4838
  simp only [e2179, e3158, e3159, e3160, e3161, e3162, e4616, e6501, e8109] at *
  tauto
theorem n22386 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h4139 : (e4139 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4419 : (e4419 _v)) (h4546 : (e4546 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4838 : (e4838 _v)) : (e3158 _v) := by
  have p15126 := n15126 _v _q 
  have p22385 := n22385 _v _q h30 h91 h191 h4139 h4285 h4301 h4419 h4546 h4648 h4675 h4838
  simp only [e3158, e3159, e3160, e3161, e3162, e3163, e4616] at *
  tauto
end
end Assembly
