import Dag270
import generated.th_lemma_36
import generated.th_lemma_37
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n22387 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h4139 : (e4139 _v)) (h4220 : (e4220 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4419 : (e4419 _v)) (h4546 : (e4546 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4838 : (e4838 _v)) (h6600 : (e6600 _v)) : (e7489 _v) := by
  have p8439 := n8439 _v _q h6600
  have p20285 := n20285 _v _q 
  have p10893 := n10893 _v _q 
  have p22386 := n22386 _v _q h30 h91 h191 h4139 h4285 h4301 h4419 h4546 h4648 h4675 h4838
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
  have p17147 := n17147 _v _q 
  have p15907 := n15907 _v _q h6600
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
  have p17009 := n17009 _v _q 
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
  have p5004 := n5004 _v _q h4220
  exact FloorCertificate.node_22387 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e61 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2879 _v) (e2883 _v) (e2898 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p8439 p20285 p10893 p22386 p5000 p16994 p4980 p16913 p22329 p22348 p22350 p22323 p16911 p4971 p22302 p13951 p17147 p15907 p22320 p4979 p17115 p253 p17078 p17117 p17113 p20467 p17133 p17120 p17009 p17221 p22321 p17089 p22318 p4999 p17104 p20470 p20274 p19665 p4976 p16778 p17127 p17050 p17122 p4977 p20126 p20426 p17110 p20829 p20653 p4989 p17111 p17131 p17108 p17294 p16943 p17064 p17067 p17080 p17053 p17072 p17074 p17069 p20096 p20836 p20461 p17874 p17136 p17087 p17055 p17058 p17098 p17083 p17106 p17020 p17093 p5006 p17100 p17141 p17102 p17091 p17096 p22341 p17758 p17124 p19610 p4990 p22324 p5004
theorem n22388 (_v : Vars) (_q : Query _v) (h6583 : (e6583 _v)) : (e30 _v) := by
  have p16290 := n16290 _v _q 
  have p22374 := n22374 _v _q h6583
  simp only [e28, e30, e34, e35, e5089, e5090, e5107] at *
  tauto
theorem n22389 (_v : Vars) (_q : Query _v) (h6583 : (e6583 _v)) : (e4419 _v) := by
  have p16347 := n16347 _v _q 
  have p22376 := n22376 _v _q h6583
  simp only [e4417, e4418, e4419, e4420, e7921, e7922, e7927] at *
  tauto
theorem n22390 (_v : Vars) (_q : Query _v) (h6583 : (e6583 _v)) : (e4546 _v) := by
  have p16307 := n16307 _v _q 
  have p22378 := n22378 _v _q h6583
  simp only [e4544, e4545, e4546, e4547, e8029, e8030, e8035] at *
  tauto
theorem n22391 (_v : Vars) (_q : Query _v) (h6583 : (e6583 _v)) : (e2179 _v) := by
  have p22371 := n22371 _v _q 
  have p22388 := n22388 _v _q h6583
  have p16388 := n16388 _v _q h6583
  have p22389 := n22389 _v _q h6583
  have p16869 := n16869 _v _q h6583
  have p16663 := n16663 _v _q h6583
  have p22362 := n22362 _v _q h6583
  have p22390 := n22390 _v _q h6583
  have p22363 := n22363 _v _q h6583
  have p22365 := n22365 _v _q h6583
  have p16749 := n16749 _v _q h6583
  have p15338 := n15338 _v _q h6583
  simp only [e30, e35, e91, e95, e191, e192, e2179, e4139, e4140, e4285, e4286, e4301, e4302, e4419, e4420, e4546, e4547, e4648, e4649, e4675, e4676, e4838, e4839, e22370] at *
  tauto
theorem n22392 (_v : Vars) (_q : Query _v) (h6583 : (e6583 _v)) : (e4616 _v) := by
  have p14684 := n14684 _v _q 
  have p22391 := n22391 _v _q h6583
  simp only [e2179, e3158, e3159, e3160, e3161, e3162, e4616, e6501, e8109] at *
  tauto
theorem n22393 (_v : Vars) (_q : Query _v) (h6583 : (e6583 _v)) : (e3158 _v) := by
  have p15126 := n15126 _v _q 
  have p22392 := n22392 _v _q h6583
  simp only [e3158, e3159, e3160, e3161, e3162, e3163, e4616] at *
  tauto
theorem n22394 (_v : Vars) (_q : Query _v) (h6583 : (e6583 _v)) : (e2132 _v) := by
  have p16578 := n16578 _v _q 
  have p11340 := n11340 _v _q h6583
  have p16858 := n16858 _v _q 
  have p22393 := n22393 _v _q h6583
  exact FloorCertificate.node_22394 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e110 _v) (e2863 _v) (e2935 _v) p16578 p11340 p16858 p22393
theorem n22395 (_v : Vars) (_q : Query _v) (h6583 : (e6583 _v)) : (e7739 _v) := by
  have p14833 := n14833 _v _q 
  have p22394 := n22394 _v _q h6583
  simp only [e2132, e4218, e4219, e4220, e4221, e7733, e7739, e7742, e7744] at *
  tauto
theorem n22396 (_v : Vars) (_q : Query _v) (h6583 : (e6583 _v)) : (e4220 _v) := by
  have p16334 := n16334 _v _q 
  have p22395 := n22395 _v _q h6583
  simp only [e4218, e4219, e4220, e4221, e7733, e7734, e7739] at *
  tauto
theorem n22398 (_v : Vars) (_q : Query _v)  : (e22397 _v) := by
  by_contra hc
  change ¬ ((e2402 _v) ∨ (¬ (e30 _v)) ∨ (¬ (e4301 _v)) ∨ (¬ (e4419 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e4546 _v)) ∨ (¬ (e4285 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4648 _v)) ∨ (¬ (e4220 _v))) at hc
  have h30 : (e30 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h191 : (e191 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h4139 : (e4139 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4220 : (e4220 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn)))))))))))))
  have h4285 : (e4285 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h4301 : (e4301 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4419 : (e4419 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4546 : (e4546 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h4648 : (e4648 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h4675 : (e4675 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h4838 : (e4838 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h6600 : (e6600 _v) := (fun hn => hc (Or.inl hn))
  have p22387 := n22387 _v _q h30 h91 h191 h4139 h4220 h4285 h4301 h4419 h4546 h4648 h4675 h4838 h6600
  exact p22387
theorem n22399 (_v : Vars) (_q : Query _v) (h6583 : (e6583 _v)) : (e2402 _v) := by
  have p22398 := n22398 _v _q 
  have p22388 := n22388 _v _q h6583
  have p16388 := n16388 _v _q h6583
  have p22389 := n22389 _v _q h6583
  have p16869 := n16869 _v _q h6583
  have p16663 := n16663 _v _q h6583
  have p22362 := n22362 _v _q h6583
  have p22390 := n22390 _v _q h6583
  have p22363 := n22363 _v _q h6583
  have p22365 := n22365 _v _q h6583
  have p16749 := n16749 _v _q h6583
  have p15338 := n15338 _v _q h6583
  have p22396 := n22396 _v _q h6583
  simp only [e30, e35, e91, e95, e191, e192, e2402, e4139, e4140, e4220, e4221, e4285, e4286, e4301, e4302, e4419, e4420, e4546, e4547, e4648, e4649, e4675, e4676, e4838, e4839, e22397] at *
  tauto
theorem n22400 (_v : Vars) (_q : Query _v) (h6583 : (e6583 _v)) : (e3929 _v) := by
  have p14484 := n14484 _v _q 
  have p22399 := n22399 _v _q h6583
  simp only [e2402, e3919, e3920, e3921, e3922, e3923, e3929, e6600, e7422] at *
  tauto
theorem n22401 (_v : Vars) (_q : Query _v) (h6583 : (e6583 _v)) : (e3919 _v) := by
  have p14797 := n14797 _v _q 
  have p22400 := n22400 _v _q h6583
  simp only [e3919, e3920, e3921, e3922, e3923, e3924, e3929] at *
  tauto
theorem n22402 (_v : Vars) (_q : Query _v) (h6583 : (e6583 _v)) : (e4447 _v) := by
  have p14688 := n14688 _v _q 
  have p22372 := n22372 _v _q h6583
  simp only [e2061, e4439, e4440, e4444, e4445, e4446, e4447, e6454, e7961] at *
  tauto
theorem n22403 (_v : Vars) (_q : Query _v) (h6583 : (e6583 _v)) : (e4439 _v) := by
  have p14925 := n14925 _v _q 
  have p22402 := n22402 _v _q h6583
  simp only [e4439, e4440, e4444, e4445, e4446, e4447, e4941] at *
  tauto
theorem n22404 (_v : Vars) (_q : Query _v) (h6583 : (e6583 _v)) : (e7489 _v) := by
  have p258 := n258 _v _q 
  have p22324 := n22324 _v _q 
  have p22401 := n22401 _v _q h6583
  have p22396 := n22396 _v _q h6583
  have p20285 := n20285 _v _q 
  have p22393 := n22393 _v _q h6583
  have p22388 := n22388 _v _q h6583
  have p16994 := n16994 _v _q 
  have p16388 := n16388 _v _q h6583
  have p16913 := n16913 _v _q 
  have p22329 := n22329 _v _q 
  have p22372 := n22372 _v _q h6583
  have p22403 := n22403 _v _q h6583
  have p22323 := n22323 _v _q 
  have p16911 := n16911 _v _q 
  have p22389 := n22389 _v _q h6583
  have p22302 := n22302 _v _q 
  have p13951 := n13951 _v _q 
  have p22320 := n22320 _v _q 
  have p16869 := n16869 _v _q h6583
  have p17115 := n17115 _v _q 
  have p16663 := n16663 _v _q h6583
  have p17078 := n17078 _v _q 
  have p17117 := n17117 _v _q 
  have p17113 := n17113 _v _q 
  have p20467 := n20467 _v _q 
  have p17133 := n17133 _v _q 
  have p17120 := n17120 _v _q 
  have p17009 := n17009 _v _q 
  have p17221 := n17221 _v _q 
  have p22321 := n22321 _v _q 
  have p17089 := n17089 _v _q 
  have p22318 := n22318 _v _q 
  have p22362 := n22362 _v _q h6583
  have p17104 := n17104 _v _q 
  have p20470 := n20470 _v _q 
  have p20274 := n20274 _v _q 
  have p19665 := n19665 _v _q 
  have p22390 := n22390 _v _q h6583
  have p16778 := n16778 _v _q 
  have p17127 := n17127 _v _q 
  have p17050 := n17050 _v _q 
  have p17122 := n17122 _v _q 
  have p22363 := n22363 _v _q h6583
  have p20126 := n20126 _v _q 
  have p20426 := n20426 _v _q 
  have p17110 := n17110 _v _q 
  have p20829 := n20829 _v _q 
  have p20653 := n20653 _v _q 
  have p22365 := n22365 _v _q h6583
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
  have p16749 := n16749 _v _q h6583
  have p17100 := n17100 _v _q 
  have p17141 := n17141 _v _q 
  have p17102 := n17102 _v _q 
  have p17091 := n17091 _v _q 
  have p17096 := n17096 _v _q 
  have p22341 := n22341 _v _q 
  have p17758 := n17758 _v _q 
  have p17124 := n17124 _v _q 
  have p19610 := n19610 _v _q 
  have p15338 := n15338 _v _q h6583
  exact FloorCertificate.node_22404 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e61 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2879 _v) (e2898 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p258 p22324 p22401 p22396 p20285 p22393 p22388 p16994 p16388 p16913 p22329 p22372 p22403 p22323 p16911 p22389 p22302 p13951 p22320 p16869 p17115 p16663 p17078 p17117 p17113 p20467 p17133 p17120 p17009 p17221 p22321 p17089 p22318 p22362 p17104 p20470 p20274 p19665 p22390 p16778 p17127 p17050 p17122 p22363 p20126 p20426 p17110 p20829 p20653 p22365 p17111 p17131 p17108 p17294 p16943 p17064 p17067 p17080 p17053 p17072 p17074 p17069 p20096 p20836 p20461 p17874 p17136 p17087 p17055 p17058 p17098 p17083 p17106 p17020 p17093 p16749 p17100 p17141 p17102 p17091 p17096 p22341 p17758 p17124 p19610 p15338
theorem n22405 (_v : Vars) (_q : Query _v)  : (e2364 _v) := by
  by_contra hc
  change ¬ (e2364 _v) at hc
  have h6583 : (e6583 _v) := (fun hn => hc hn)
  have p22404 := n22404 _v _q h6583
  exact p22404
theorem n22406 (_v : Vars) (_q : Query _v)  : (e4661 _v) := by
  have p14686 := n14686 _v _q 
  have p22405 := n22405 _v _q 
  simp only [e2364, e4653, e4654, e4658, e4659, e4660, e4661, e6583, e8163] at *
  tauto
theorem n22407 (_v : Vars) (_q : Query _v)  : (e4653 _v) := by
  have p15168 := n15168 _v _q 
  have p22406 := n22406 _v _q 
  simp only [e4653, e4654, e4658, e4659, e4660, e4661, e4939] at *
  tauto
theorem n22408 (_v : Vars) (_q : Query _v) (h3937 : (e3937 _v)) (h4608 : (e4608 _v)) (h5195 : (e5195 _v)) : (e2634 _v) := by
  have p20871 := n20871 _v _q 
  have p12926 := n12926 _v _q h5195
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
theorem n22409 (_v : Vars) (_q : Query _v) (h3937 : (e3937 _v)) (h4608 : (e4608 _v)) (h5195 : (e5195 _v)) : (e7489 _v) := by
  have p16113 := n16113 _v _q h5195
  have p15223 := n15223 _v _q h5195
  have p17141 := n17141 _v _q 
  have p17102 := n17102 _v _q 
  have p5257 := n5257 _v _q 
  have p17091 := n17091 _v _q 
  have p22300 := n22300 _v _q 
  have p17276 := n17276 _v _q h5195
  have p17256 := n17256 _v _q 
  have p15938 := n15938 _v _q h5195
  have p16109 := n16109 _v _q h5195
  have p4996 := n4996 _v _q h3937
  have p17147 := n17147 _v _q 
  have p16101 := n16101 _v _q h5195
  have p20107 := n20107 _v _q h5195
  have p22407 := n22407 _v _q 
  have p17124 := n17124 _v _q 
  have p22341 := n22341 _v _q 
  have p22324 := n22324 _v _q 
  have p19610 := n19610 _v _q 
  have p13951 := n13951 _v _q 
  have p22408 := n22408 _v _q h3937 h4608 h5195
  have p4991 := n4991 _v _q h4608
  have p16576 := n16576 _v _q 
  have p22368 := n22368 _v _q 
  have p22323 := n22323 _v _q 
  have p17100 := n17100 _v _q 
  have p22302 := n22302 _v _q 
  have p17758 := n17758 _v _q 
  have p22320 := n22320 _v _q 
  have p17115 := n17115 _v _q 
  have p17953 := n17953 _v _q 
  have p17078 := n17078 _v _q 
  have p17117 := n17117 _v _q 
  have p17113 := n17113 _v _q 
  have p20467 := n20467 _v _q 
  have p17133 := n17133 _v _q 
  have p17120 := n17120 _v _q 
  have p17009 := n17009 _v _q 
  have p22321 := n22321 _v _q 
  have p17089 := n17089 _v _q 
  have p22318 := n22318 _v _q 
  have p22347 := n22347 _v _q 
  have p17104 := n17104 _v _q 
  have p20470 := n20470 _v _q 
  have p20274 := n20274 _v _q 
  have p19665 := n19665 _v _q 
  have p16778 := n16778 _v _q 
  have p17127 := n17127 _v _q 
  have p17050 := n17050 _v _q 
  have p17122 := n17122 _v _q 
  have p17096 := n17096 _v _q 
  have p20126 := n20126 _v _q 
  have p20426 := n20426 _v _q 
  have p17110 := n17110 _v _q 
  have p20829 := n20829 _v _q 
  have p20653 := n20653 _v _q 
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
  have p22322 := n22322 _v _q 
  have p16674 := n16674 _v _q h5195
  have p16977 := n16977 _v _q 
  have p12839 := n12839 _v _q h5195
  have p8549 := n8549 _v _q h5195
  exact FloorCertificate.node_22409 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e61 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2863 _v) (e2877 _v) (e2883 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p16113 p15223 p17141 p17102 p5257 p17091 p22300 p17276 p17256 p15938 p16109 p4996 p17147 p16101 p20107 p22407 p17124 p22341 p22324 p19610 p13951 p22408 p4991 p16576 p22368 p22323 p17100 p22302 p17758 p22320 p17115 p17953 p17078 p17117 p17113 p20467 p17133 p17120 p17009 p22321 p17089 p22318 p22347 p17104 p20470 p20274 p19665 p16778 p17127 p17050 p17122 p17096 p20126 p20426 p17110 p20829 p20653 p17111 p17131 p17108 p17294 p16943 p17064 p17067 p17080 p17053 p17072 p17074 p17069 p20096 p20836 p20461 p17874 p17136 p17087 p17055 p17058 p17098 p17083 p17106 p17020 p17093 p22322 p16674 p16977 p12839 p8549
theorem n22411 (_v : Vars) (_q : Query _v)  : (e22410 _v) := by
  by_contra hc
  change ¬ ((e196 _v) ∨ (¬ (e3937 _v)) ∨ (¬ (e4608 _v))) at hc
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h4608 : (e4608 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr hn)))
  have h5195 : (e5195 _v) := (fun hn => hc (Or.inl hn))
  have p22409 := n22409 _v _q h3937 h4608 h5195
  exact p22409
theorem n22412 (_v : Vars) (_q : Query _v) (h3937 : (e3937 _v)) (h4608 : (e4608 _v)) : (e196 _v) := by
  have p22411 := n22411 _v _q 
  have p4996 := n4996 _v _q h3937
  have p4991 := n4991 _v _q h4608
  simp only [e196, e3937, e3942, e4608, e4609, e22410] at *
  tauto
theorem n22413 (_v : Vars) (_q : Query _v) (h6501 : (e6501 _v)) : (e196 _v) := by
  have p22411 := n22411 _v _q 
  have p16325 := n16325 _v _q h6501
  have p15641 := n15641 _v _q h6501
  simp only [e196, e3937, e3942, e4608, e4609, e22410] at *
  tauto
theorem n22414 (_v : Vars) (_q : Query _v) (h6501 : (e6501 _v)) : (e5203 _v) := by
  have p14730 := n14730 _v _q 
  have p22413 := n22413 _v _q h6501
  simp only [e191, e192, e193, e194, e196, e5193, e5195, e5203, e5206] at *
  tauto
theorem n22415 (_v : Vars) (_q : Query _v) (h3937 : (e3937 _v)) (h4608 : (e4608 _v)) : (e5203 _v) := by
  have p14730 := n14730 _v _q 
  have p22412 := n22412 _v _q h3937 h4608
  simp only [e191, e192, e193, e194, e196, e5193, e5195, e5203, e5206] at *
  tauto
theorem n22416 (_v : Vars) (_q : Query _v) (h3937 : (e3937 _v)) (h4608 : (e4608 _v)) : (e191 _v) := by
  have p16442 := n16442 _v _q 
  have p22415 := n22415 _v _q h3937 h4608
  simp only [e191, e192, e193, e194, e5193, e5194, e5203] at *
  tauto
theorem n22417 (_v : Vars) (_q : Query _v) (h6501 : (e6501 _v)) : (e191 _v) := by
  have p16442 := n16442 _v _q 
  have p22414 := n22414 _v _q h6501
  simp only [e191, e192, e193, e194, e5193, e5194, e5203] at *
  tauto
theorem n22418 (_v : Vars) (_q : Query _v) (h3937 : (e3937 _v)) (h4306 : (e4306 _v)) (h4608 : (e4608 _v)) (h7749 : (e7749 _v)) (h8310 : (e8310 _v)) : (e7489 _v) := by
  have p12885 := n12885 _v _q h8310
  have p17100 := n17100 _v _q 
  have p22412 := n22412 _v _q h3937 h4608
  have p22322 := n22322 _v _q 
  have p15248 := n15248 _v _q h8310
  have p19839 := n19839 _v _q h8310
  have p16977 := n16977 _v _q 
  have p15608 := n15608 _v _q h8310
  have p17091 := n17091 _v _q 
  have p18630 := n18630 _v _q h8310
  have p15606 := n15606 _v _q h8310
  have p17102 := n17102 _v _q 
  have p17138 := n17138 _v _q h4306
  have p12880 := n12880 _v _q h8310
  have p17141 := n17141 _v _q 
  have p17256 := n17256 _v _q 
  have p17453 := n17453 _v _q h8310
  have p22416 := n22416 _v _q h3937 h4608
  have p4996 := n4996 _v _q h3937
  have p17147 := n17147 _v _q 
  have p16269 := n16269 _v _q h7749
  have p22407 := n22407 _v _q 
  have p17124 := n17124 _v _q 
  have p22341 := n22341 _v _q 
  have p22324 := n22324 _v _q 
  have p19610 := n19610 _v _q 
  have p13951 := n13951 _v _q 
  have p4991 := n4991 _v _q h4608
  have p16576 := n16576 _v _q 
  have p22368 := n22368 _v _q 
  have p22323 := n22323 _v _q 
  have p22302 := n22302 _v _q 
  have p17758 := n17758 _v _q 
  have p22320 := n22320 _v _q 
  have p17115 := n17115 _v _q 
  have p17078 := n17078 _v _q 
  have p17117 := n17117 _v _q 
  have p17113 := n17113 _v _q 
  have p20467 := n20467 _v _q 
  have p17133 := n17133 _v _q 
  have p17120 := n17120 _v _q 
  have p17009 := n17009 _v _q 
  have p22321 := n22321 _v _q 
  have p17089 := n17089 _v _q 
  have p22318 := n22318 _v _q 
  have p22347 := n22347 _v _q 
  have p17104 := n17104 _v _q 
  have p20470 := n20470 _v _q 
  have p20274 := n20274 _v _q 
  have p19665 := n19665 _v _q 
  have p16778 := n16778 _v _q 
  have p17127 := n17127 _v _q 
  have p17050 := n17050 _v _q 
  have p17122 := n17122 _v _q 
  have p17096 := n17096 _v _q 
  have p20126 := n20126 _v _q 
  have p20426 := n20426 _v _q 
  have p17110 := n17110 _v _q 
  have p20829 := n20829 _v _q 
  have p20653 := n20653 _v _q 
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
  have p11384 := n11384 _v _q h8310
  exact FloorCertificate.node_22418 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e61 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2863 _v) (e2877 _v) (e2883 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p12885 p17100 p22412 p22322 p15248 p19839 p16977 p15608 p17091 p18630 p15606 p17102 p17138 p12880 p17141 p17256 p17453 p22416 p4996 p17147 p16269 p22407 p17124 p22341 p22324 p19610 p13951 p4991 p16576 p22368 p22323 p22302 p17758 p22320 p17115 p17078 p17117 p17113 p20467 p17133 p17120 p17009 p22321 p17089 p22318 p22347 p17104 p20470 p20274 p19665 p16778 p17127 p17050 p17122 p17096 p20126 p20426 p17110 p20829 p20653 p17111 p17131 p17108 p17294 p16943 p17064 p17067 p17080 p17053 p17072 p17074 p17069 p20096 p20836 p20461 p17874 p17136 p17087 p17055 p17058 p17098 p17083 p17106 p17020 p17093 p11384
theorem n22419 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h3937 : (e3937 _v)) (h4139 : (e4139 _v)) (h4285 : (e4285 _v)) (h4419 : (e4419 _v)) (h4608 : (e4608 _v)) (h6676 : (e6676 _v)) (h7749 : (e7749 _v)) : (e7489 _v) := by
  have p10896 := n10896 _v _q 
  have p22329 := n22329 _v _q 
  have p10893 := n10893 _v _q 
  have p10943 := n10943 _v _q h6676
  have p16911 := n16911 _v _q 
  have p22366 := n22366 _v _q 
  have p16913 := n16913 _v _q 
  have p4977 := n4977 _v _q h4285
  have p16994 := n16994 _v _q 
  have p15342 := n15342 _v _q h6676
  have p5000 := n5000 _v _q h30
  have p4979 := n4979 _v _q h4139
  have p22380 := n22380 _v _q h6676
  have p22357 := n22357 _v _q h6676
  have p22416 := n22416 _v _q h3937 h4608
  have p4996 := n4996 _v _q h3937
  have p17147 := n17147 _v _q 
  have p16269 := n16269 _v _q h7749
  have p22407 := n22407 _v _q 
  have p17124 := n17124 _v _q 
  have p22341 := n22341 _v _q 
  have p22324 := n22324 _v _q 
  have p19610 := n19610 _v _q 
  have p13951 := n13951 _v _q 
  have p4991 := n4991 _v _q h4608
  have p16576 := n16576 _v _q 
  have p22368 := n22368 _v _q 
  have p22323 := n22323 _v _q 
  have p4971 := n4971 _v _q h4419
  have p22302 := n22302 _v _q 
  have p17758 := n17758 _v _q 
  have p22320 := n22320 _v _q 
  have p17115 := n17115 _v _q 
  have p17078 := n17078 _v _q 
  have p17117 := n17117 _v _q 
  have p17113 := n17113 _v _q 
  have p20467 := n20467 _v _q 
  have p17133 := n17133 _v _q 
  have p17120 := n17120 _v _q 
  have p17009 := n17009 _v _q 
  have p22321 := n22321 _v _q 
  have p17089 := n17089 _v _q 
  have p22318 := n22318 _v _q 
  have p22347 := n22347 _v _q 
  have p17104 := n17104 _v _q 
  have p20470 := n20470 _v _q 
  have p20274 := n20274 _v _q 
  have p19665 := n19665 _v _q 
  have p16778 := n16778 _v _q 
  have p17127 := n17127 _v _q 
  have p17050 := n17050 _v _q 
  have p17122 := n17122 _v _q 
  have p17096 := n17096 _v _q 
  have p20126 := n20126 _v _q 
  have p20426 := n20426 _v _q 
  have p17110 := n17110 _v _q 
  have p20829 := n20829 _v _q 
  have p20653 := n20653 _v _q 
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
  have p22322 := n22322 _v _q 
  have p17100 := n17100 _v _q 
  have p17141 := n17141 _v _q 
  have p17102 := n17102 _v _q 
  have p17091 := n17091 _v _q 
  exact FloorCertificate.node_22419 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e61 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2863 _v) (e2877 _v) (e2883 _v) (e2898 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p10896 p22329 p10893 p10943 p16911 p22366 p16913 p4977 p16994 p15342 p5000 p4979 p22380 p22357 p22416 p4996 p17147 p16269 p22407 p17124 p22341 p22324 p19610 p13951 p4991 p16576 p22368 p22323 p4971 p22302 p17758 p22320 p17115 p17078 p17117 p17113 p20467 p17133 p17120 p17009 p22321 p17089 p22318 p22347 p17104 p20470 p20274 p19665 p16778 p17127 p17050 p17122 p17096 p20126 p20426 p17110 p20829 p20653 p17111 p17131 p17108 p17294 p16943 p17064 p17067 p17080 p17053 p17072 p17074 p17069 p20096 p20836 p20461 p17874 p17136 p17087 p17055 p17058 p17098 p17083 p17106 p17020 p17093 p22322 p17100 p17141 p17102 p17091
theorem n22420 (_v : Vars) (_q : Query _v) (h6501 : (e6501 _v)) (h6676 : (e6676 _v)) : (e7742 _v) := by
  have p20854 := n20854 _v _q 
  have p22357 := n22357 _v _q h6676
  have p8554 := n8554 _v _q h6501
  have p22318 := n22318 _v _q 
  have p22417 := n22417 _v _q h6501
  have p22322 := n22322 _v _q 
  have p22347 := n22347 _v _q 
  have p22324 := n22324 _v _q 
  have p22323 := n22323 _v _q 
  have p22320 := n22320 _v _q 
  have p22366 := n22366 _v _q 
  simp only [e91, e95, e191, e192, e2061, e2132, e2179, e3152, e3156, e4260, e4261, e4675, e4676, e4787, e4788, e4813, e4814, e4838, e4839, e6454, e6501, e7742, e20853] at *
  tauto
theorem n22421 (_v : Vars) (_q : Query _v) (h6501 : (e6501 _v)) (h6676 : (e6676 _v)) : (e7754 _v) := by
  have p14942 := n14942 _v _q 
  have p22420 := n22420 _v _q h6501 h6676
  simp only [e2132, e7742, e7747, e7749, e7751, e7752, e7753, e7754, e11001] at *
  tauto
theorem n22422 (_v : Vars) (_q : Query _v) (h2132 : (e2132 _v)) (h6501 : (e6501 _v)) : (e4839 _v) := by
  have p20854 := n20854 _v _q 
  have p11349 := n11349 _v _q h2132
  have p8554 := n8554 _v _q h6501
  have p22318 := n22318 _v _q 
  have p22417 := n22417 _v _q h6501
  have p22322 := n22322 _v _q 
  have p22347 := n22347 _v _q 
  have p22324 := n22324 _v _q 
  have p22323 := n22323 _v _q 
  have p22320 := n22320 _v _q 
  have p22366 := n22366 _v _q 
  simp only [e91, e95, e191, e192, e2061, e2132, e2179, e3152, e3156, e4260, e4261, e4675, e4676, e4787, e4788, e4813, e4814, e4838, e4839, e6454, e6501, e7742, e20853] at *
  tauto
theorem n22423 (_v : Vars) (_q : Query _v) (h2132 : (e2132 _v)) (h6501 : (e6501 _v)) : (e8301 _v) := by
  have p16285 := n16285 _v _q 
  have p22422 := n22422 _v _q h2132 h6501
  simp only [e4836, e4837, e4838, e4839, e8301, e8302] at *
  tauto
theorem n22425 (_v : Vars) (_q : Query _v)  : (e22424 _v) := by
  by_contra hc
  change ¬ ((e2529 _v) ∨ (¬ (e4306 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e7749 _v)) ∨ (¬ (e4608 _v))) at hc
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h4608 : (e4608 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr hn)))))
  have h7749 : (e7749 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h8310 : (e8310 _v) := (fun hn => hc (Or.inl hn))
  have p22418 := n22418 _v _q h3937 h4306 h4608 h7749 h8310
  exact p22418
theorem n22427 (_v : Vars) (_q : Query _v)  : (e22426 _v) := by
  by_contra hc
  change ¬ ((¬ (e30 _v)) ∨ (e2585 _v) ∨ (¬ (e4285 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e7749 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e4419 _v))) at hc
  have h30 : (e30 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4139 : (e4139 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4285 : (e4285 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4419 : (e4419 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))))
  have h4608 : (e4608 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h6676 : (e6676 _v) := (fun hn => hc (Or.inr (Or.inl hn)))
  have h7749 : (e7749 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have p22419 := n22419 _v _q h30 h3937 h4139 h4285 h4419 h4608 h6676 h7749
  exact p22419
theorem n22428 (_v : Vars) (_q : Query _v) (h2132 : (e2132 _v)) (h6501 : (e6501 _v)) : (e7489 _v) := by
  have p14906 := n14906 _v _q 
  have p22423 := n22423 _v _q h2132 h6501
  have p16750 := n16750 _v _q h2132
  simp only [e2529, e4836, e4837, e4838, e4839, e8301, e8307, e8310, e8312] at *
  tauto
theorem n22429 (_v : Vars) (_q : Query _v) (h3937 : (e3937 _v)) (h4306 : (e4306 _v)) (h4608 : (e4608 _v)) (h7749 : (e7749 _v)) : (e2529 _v) := by
  have p22425 := n22425 _v _q 
  have p17138 := n17138 _v _q h4306
  have p4996 := n4996 _v _q h3937
  have p16269 := n16269 _v _q h7749
  have p4991 := n4991 _v _q h4608
  simp only [e2529, e3937, e3942, e4306, e4311, e4608, e4609, e7749, e7752, e22424] at *
  tauto
theorem n22430 (_v : Vars) (_q : Query _v) (h2303 : (e2303 _v)) (h3937 : (e3937 _v)) (h4608 : (e4608 _v)) (h6676 : (e6676 _v)) (h7749 : (e7749 _v)) : (e35 _v) := by
  have p22427 := n22427 _v _q 
  have p16436 := n16436 _v _q h2303
  have p10943 := n10943 _v _q h6676
  have p16439 := n16439 _v _q h2303
  have p4996 := n4996 _v _q h3937
  have p16269 := n16269 _v _q h7749
  have p4991 := n4991 _v _q h4608
  have p22383 := n22383 _v _q h2303 h6676
  simp only [e30, e35, e2585, e3937, e3942, e4139, e4140, e4285, e4286, e4419, e4420, e4608, e4609, e6676, e7749, e7752, e22426] at *
  tauto
theorem n22431 (_v : Vars) (_q : Query _v) (h2303 : (e2303 _v)) (h3937 : (e3937 _v)) (h4608 : (e4608 _v)) (h6676 : (e6676 _v)) (h7749 : (e7749 _v)) : (e5089 _v) := by
  have p16290 := n16290 _v _q 
  have p22430 := n22430 _v _q h2303 h3937 h4608 h6676 h7749
  simp only [e28, e30, e34, e35, e5089, e5107] at *
  tauto
theorem n22433 (_v : Vars) (_q : Query _v)  : (e22432 _v) := by
  by_contra hc
  change ¬ ((¬ (e2132 _v)) ∨ (e2179 _v)) at hc
  have h2132 : (e2132 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h6501 : (e6501 _v) := (fun hn => hc (Or.inr hn))
  have p22428 := n22428 _v _q h2132 h6501
  exact p22428
theorem n22434 (_v : Vars) (_q : Query _v) (h6501 : (e6501 _v)) : (e7742 _v) := by
  have p22433 := n22433 _v _q 
  have p8554 := n8554 _v _q h6501
  simp only [e2132, e2179, e6501, e7742, e22432] at *
  tauto
theorem n22435 (_v : Vars) (_q : Query _v) (h3937 : (e3937 _v)) (h4306 : (e4306 _v)) (h4608 : (e4608 _v)) (h7749 : (e7749 _v)) : (e8307 _v) := by
  have p14906 := n14906 _v _q 
  have p22429 := n22429 _v _q h3937 h4306 h4608 h7749
  simp only [e2529, e4836, e4837, e4838, e4839, e8301, e8307, e8310, e8312] at *
  tauto
theorem n22436 (_v : Vars) (_q : Query _v) (h3937 : (e3937 _v)) (h4306 : (e4306 _v)) (h4608 : (e4608 _v)) (h7749 : (e7749 _v)) : (e4838 _v) := by
  have p16285 := n16285 _v _q 
  have p22435 := n22435 _v _q h3937 h4306 h4608 h7749
  simp only [e4836, e4837, e4838, e4839, e8301, e8302, e8307] at *
  tauto
end
end Assembly
