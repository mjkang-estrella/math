import Dag229
import generated.th_lemma_29
import generated.th_lemma_30
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n20377 (_v : Vars) (_q : Query _v)  : (e20376 _v) := by
  by_contra hc
  change ¬ ((e2179 _v) ∨ (e2351 _v) ∨ (e436 _v)) at hc
  have h5362 : (e5362 _v) := by
    change (¬ (e436 _v))
    tauto
  have h6501 : (e6501 _v) := by
    change (¬ (e2179 _v))
    tauto
  have h6575 : (e6575 _v) := by
    change (¬ (e2351 _v))
    tauto
  have p20375 := n20375 _v _q h5362 h6501 h6575
  exact p20375
theorem n20378 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) (h6575 : (e6575 _v)) : (e2179 _v) := by
  have p20377 := n20377 _v _q 
  have p11413 := n11413 _v _q h6575
  have p7488 := n7488 _v _q h5362
  simp only [e436, e2179, e2351, e5362, e6575, e20376] at *
  tauto
theorem n20379 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) (h6575 : (e6575 _v)) : (e4616 _v) := by
  have p14684 := n14684 _v _q 
  have p20378 := n20378 _v _q h5362 h6575
  simp only [e2179, e3158, e3159, e3160, e3161, e3162, e4616, e6501, e8109] at *
  tauto
theorem n20380 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) (h6575 : (e6575 _v)) : (e3158 _v) := by
  have p15126 := n15126 _v _q 
  have p20379 := n20379 _v _q h5362 h6575
  simp only [e3158, e3159, e3160, e3161, e3162, e3163, e4616] at *
  tauto
theorem n20381 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) (h6575 : (e6575 _v)) : (e6525 _v) := by
  have p20366 := n20366 _v _q 
  have p20380 := n20380 _v _q h5362 h6575
  have p20357 := n20357 _v _q h5362 h6575
  have p20372 := n20372 _v _q h5362 h6575
  have p15771 := n15771 _v _q h6575
  have p7488 := n7488 _v _q h5362
  simp only [e436, e2242, e2296, e3158, e3159, e4156, e4157, e5362, e6525, e6549, e8317, e8320, e20365] at *
  tauto
theorem n20382 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) (h6575 : (e6575 _v)) : (e8174 _v) := by
  have p14634 := n14634 _v _q 
  have p20381 := n20381 _v _q h5362 h6575
  simp only [e2242, e4673, e4674, e4675, e4676, e6525, e8166, e8174, e8177] at *
  tauto
theorem n20383 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) (h6575 : (e6575 _v)) : (e4675 _v) := by
  have p15965 := n15965 _v _q 
  have p20382 := n20382 _v _q h5362 h6575
  simp only [e4673, e4674, e4675, e4676, e8166, e8167, e8174] at *
  tauto
theorem n20384 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) (h6575 : (e6575 _v)) : (e3942 _v) := by
  have p20380 := n20380 _v _q h5362 h6575
  have p16578 := n16578 _v _q 
  have p5255 := n5255 _v _q 
  have p13951 := n13951 _v _q 
  have p17147 := n17147 _v _q 
  have p20318 := n20318 _v _q h5362
  have p20374 := n20374 _v _q h5362 h6575
  have p20352 := n20352 _v _q h5362
  have p19693 := n19693 _v _q h5362
  have p15733 := n15733 _v _q h5362
  have p17120 := n17120 _v _q 
  have p17953 := n17953 _v _q 
  have p17256 := n17256 _v _q 
  have p19694 := n19694 _v _q h5362
  have p16858 := n16858 _v _q 
  have p16778 := n16778 _v _q 
  have p15591 := n15591 _v _q h5362
  have p20286 := n20286 _v _q h5362
  have p20357 := n20357 _v _q h5362 h6575
  have p17111 := n17111 _v _q 
  have p15742 := n15742 _v _q h5362
  have p17252 := n17252 _v _q h5362
  have p19720 := n19720 _v _q h5362
  have p17874 := n17874 _v _q 
  have p17127 := n17127 _v _q 
  have p15595 := n15595 _v _q h5362
  have p20274 := n20274 _v _q 
  have p18120 := n18120 _v _q h5362
  have p17253 := n17253 _v _q h5362
  have p17050 := n17050 _v _q 
  have p17009 := n17009 _v _q 
  have p17133 := n17133 _v _q 
  have p17089 := n17089 _v _q 
  have p19665 := n19665 _v _q 
  have p16992 := n16992 _v _q 
  have p17055 := n17055 _v _q 
  have p17108 := n17108 _v _q 
  have p20372 := n20372 _v _q h5362 h6575
  have p15771 := n15771 _v _q h6575
  have p20126 := n20126 _v _q 
  have p15087 := n15087 _v _q h5362
  have p17131 := n17131 _v _q 
  have p17110 := n17110 _v _q 
  have p17053 := n17053 _v _q 
  have p15723 := n15723 _v _q h5362
  have p20096 := n20096 _v _q 
  have p17294 := n17294 _v _q 
  have p15725 := n15725 _v _q h5362
  have p17058 := n17058 _v _q 
  have p17064 := n17064 _v _q 
  have p17067 := n17067 _v _q 
  have p17069 := n17069 _v _q 
  have p17072 := n17072 _v _q 
  have p17136 := n17136 _v _q 
  have p19728 := n19728 _v _q h5362
  have p17078 := n17078 _v _q 
  have p17080 := n17080 _v _q 
  have p17083 := n17083 _v _q 
  have p17074 := n17074 _v _q 
  have p17087 := n17087 _v _q 
  have p17758 := n17758 _v _q 
  have p17091 := n17091 _v _q 
  have p17093 := n17093 _v _q 
  have p15728 := n15728 _v _q h5362
  have p17141 := n17141 _v _q 
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p17100 := n17100 _v _q 
  have p17102 := n17102 _v _q 
  have p19610 := n19610 _v _q 
  have p17104 := n17104 _v _q 
  have p17096 := n17096 _v _q 
  have p17113 := n17113 _v _q 
  have p15731 := n15731 _v _q h5362
  have p17122 := n17122 _v _q 
  have p17117 := n17117 _v _q 
  have p17124 := n17124 _v _q 
  have p17115 := n17115 _v _q 
  have p20351 := n20351 _v _q h5362 h6575
  have p20323 := n20323 _v _q h5362
  have p7488 := n7488 _v _q h5362
  have p20383 := n20383 _v _q h5362 h6575
  have p15736 := n15736 _v _q h5362
  have p20381 := n20381 _v _q h5362 h6575
  exact FloorCertificate.node_20384 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2863 _v) (e2877 _v) (e2883 _v) (e2902 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p20380 p16578 p5255 p13951 p17147 p20318 p20374 p20352 p19693 p15733 p17120 p17953 p17256 p19694 p16858 p16778 p15591 p20286 p20357 p17111 p15742 p17252 p19720 p17874 p17127 p15595 p20274 p18120 p17253 p17050 p17009 p17133 p17089 p19665 p16992 p17055 p17108 p20372 p15771 p20126 p15087 p17131 p17110 p17053 p15723 p20096 p17294 p15725 p17058 p17064 p17067 p17069 p17072 p17136 p19728 p17078 p17080 p17083 p17074 p17087 p17758 p17091 p17093 p15728 p17141 p17098 p17106 p17100 p17102 p19610 p17104 p17096 p17113 p15731 p17122 p17117 p17124 p17115 p20351 p20323 p7488 p20383 p15736 p20381
theorem n20385 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) (h6575 : (e6575 _v)) : (e3920 _v) := by
  have p20318 := n20318 _v _q h5362
  have p20372 := n20372 _v _q h5362 h6575
  have p15736 := n15736 _v _q h5362
  have p16858 := n16858 _v _q 
  have p20380 := n20380 _v _q h5362 h6575
  have p13951 := n13951 _v _q 
  have p20374 := n20374 _v _q h5362 h6575
  have p20352 := n20352 _v _q h5362
  have p19693 := n19693 _v _q h5362
  have p15733 := n15733 _v _q h5362
  have p17120 := n17120 _v _q 
  have p17953 := n17953 _v _q 
  have p17256 := n17256 _v _q 
  have p19694 := n19694 _v _q h5362
  have p16578 := n16578 _v _q 
  have p16778 := n16778 _v _q 
  have p15591 := n15591 _v _q h5362
  have p20286 := n20286 _v _q h5362
  have p20357 := n20357 _v _q h5362 h6575
  have p17111 := n17111 _v _q 
  have p15742 := n15742 _v _q h5362
  have p17252 := n17252 _v _q h5362
  have p19720 := n19720 _v _q h5362
  have p17874 := n17874 _v _q 
  have p17127 := n17127 _v _q 
  have p15595 := n15595 _v _q h5362
  have p20274 := n20274 _v _q 
  have p18120 := n18120 _v _q h5362
  have p17253 := n17253 _v _q h5362
  have p17050 := n17050 _v _q 
  have p17009 := n17009 _v _q 
  have p17133 := n17133 _v _q 
  have p17089 := n17089 _v _q 
  have p19665 := n19665 _v _q 
  have p16992 := n16992 _v _q 
  have p17055 := n17055 _v _q 
  have p17108 := n17108 _v _q 
  have p7488 := n7488 _v _q h5362
  have p15771 := n15771 _v _q h6575
  have p20126 := n20126 _v _q 
  have p15087 := n15087 _v _q h5362
  have p17131 := n17131 _v _q 
  have p17110 := n17110 _v _q 
  have p17053 := n17053 _v _q 
  have p15723 := n15723 _v _q h5362
  have p20096 := n20096 _v _q 
  have p17294 := n17294 _v _q 
  have p15725 := n15725 _v _q h5362
  have p17058 := n17058 _v _q 
  have p17064 := n17064 _v _q 
  have p17067 := n17067 _v _q 
  have p17069 := n17069 _v _q 
  have p17072 := n17072 _v _q 
  have p17136 := n17136 _v _q 
  have p19728 := n19728 _v _q h5362
  have p17078 := n17078 _v _q 
  have p17080 := n17080 _v _q 
  have p17083 := n17083 _v _q 
  have p17074 := n17074 _v _q 
  have p17087 := n17087 _v _q 
  have p17758 := n17758 _v _q 
  have p17091 := n17091 _v _q 
  have p17093 := n17093 _v _q 
  have p15728 := n15728 _v _q h5362
  have p17141 := n17141 _v _q 
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p17100 := n17100 _v _q 
  have p17102 := n17102 _v _q 
  have p19610 := n19610 _v _q 
  have p17104 := n17104 _v _q 
  have p17096 := n17096 _v _q 
  have p17113 := n17113 _v _q 
  have p15731 := n15731 _v _q h5362
  have p17122 := n17122 _v _q 
  have p17117 := n17117 _v _q 
  have p17124 := n17124 _v _q 
  have p17115 := n17115 _v _q 
  have p20351 := n20351 _v _q h5362 h6575
  have p20323 := n20323 _v _q h5362
  have p5255 := n5255 _v _q 
  have p20383 := n20383 _v _q h5362 h6575
  exact FloorCertificate.node_20385 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2863 _v) (e2877 _v) (e2902 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p20318 p20372 p15736 p16858 p20380 p13951 p20374 p20352 p19693 p15733 p17120 p17953 p17256 p19694 p16578 p16778 p15591 p20286 p20357 p17111 p15742 p17252 p19720 p17874 p17127 p15595 p20274 p18120 p17253 p17050 p17009 p17133 p17089 p19665 p16992 p17055 p17108 p7488 p15771 p20126 p15087 p17131 p17110 p17053 p15723 p20096 p17294 p15725 p17058 p17064 p17067 p17069 p17072 p17136 p19728 p17078 p17080 p17083 p17074 p17087 p17758 p17091 p17093 p15728 p17141 p17098 p17106 p17100 p17102 p19610 p17104 p17096 p17113 p15731 p17122 p17117 p17124 p17115 p20351 p20323 p5255 p20383
theorem n20386 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) (h6575 : (e6575 _v)) : (e3923 _v) := by
  have p14797 := n14797 _v _q 
  have p20385 := n20385 _v _q h5362 h6575
  simp only [e3919, e3920, e3921, e3922, e3923, e3924] at *
  tauto
theorem n20387 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) (h6575 : (e6575 _v)) : (e7415 _v) := by
  have p15012 := n15012 _v _q 
  have p20384 := n20384 _v _q h5362 h6575
  simp only [e3937, e3939, e3942, e3943, e7415, e7633] at *
  tauto
theorem n20388 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) (h6575 : (e6575 _v)) : (e2402 _v) := by
  have p14534 := n14534 _v _q 
  have p20387 := n20387 _v _q h5362 h6575
  simp only [e2402, e3937, e3939, e3942, e3943, e7415, e7416, e7419] at *
  tauto
theorem n20389 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) (h6575 : (e6575 _v)) : (e7489 _v) := by
  have p14484 := n14484 _v _q 
  have p20388 := n20388 _v _q h5362 h6575
  have p20386 := n20386 _v _q h5362 h6575
  simp only [e2402, e3919, e3920, e3921, e3922, e3923, e3929, e6600, e7422] at *
  tauto
theorem n20391 (_v : Vars) (_q : Query _v)  : (e20390 _v) := by
  by_contra hc
  change ¬ ((e2351 _v) ∨ (e436 _v)) at hc
  have h5362 : (e5362 _v) := by
    change (¬ (e436 _v))
    tauto
  have h6575 : (e6575 _v) := by
    change (¬ (e2351 _v))
    tauto
  have p20389 := n20389 _v _q h5362 h6575
  exact p20389
theorem n20392 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) : (e2351 _v) := by
  have p20391 := n20391 _v _q 
  have p7488 := n7488 _v _q h5362
  simp only [e436, e2351, e5362, e20390] at *
  tauto
theorem n20393 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) : (e2242 _v) := by
  have p8467 := n8467 _v _q 
  have p20392 := n20392 _v _q h5362
  simp only [e2242, e2351, e6575, e8466] at *
  tauto
theorem n20394 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) : (e4686 _v) := by
  have p14708 := n14708 _v _q 
  have p20393 := n20393 _v _q h5362
  simp only [e2242, e4678, e4679, e4683, e4684, e4685, e4686, e6525, e8180] at *
  tauto
theorem n20395 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) : (e4684 _v) := by
  have p20347 := n20347 _v _q 
  have p20392 := n20392 _v _q h5362
  have p20286 := n20286 _v _q h5362
  have p7488 := n7488 _v _q h5362
  simp only [e436, e2351, e4679, e4684, e5362, e6575, e7714, e7724, e20346] at *
  tauto
theorem n20396 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) : (e7489 _v) := by
  have p14989 := n14989 _v _q 
  have p20394 := n20394 _v _q h5362
  have p20395 := n20395 _v _q h5362
  simp only [e4678, e4679, e4683, e4684, e4685, e4686, e4967] at *
  tauto
theorem n20397 (_v : Vars) (_q : Query _v)  : (e436 _v) := by
  by_contra hc
  change ¬ (e436 _v) at hc
  have h5362 : (e5362 _v) := by
    change (¬ (e436 _v))
    tauto
  have p20396 := n20396 _v _q h5362
  exact p20396
theorem n20398 (_v : Vars) (_q : Query _v) (h496 : (e496 _v)) : (e2179 _v) := by
  have p4016 := n4016 _v _q 
  have p5391 := n5391 _v _q 
  have p5255 := n5255 _v _q 
  have p8144 := n8144 _v _q h496
  have p20397 := n20397 _v _q 
  have p258 := n258 _v _q 
  exact FloorCertificate.node_20398 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p4016 p5391 p5255 p8144 p20397 p258
theorem n20399 (_v : Vars) (_q : Query _v) (h496 : (e496 _v)) : (e4616 _v) := by
  have p14684 := n14684 _v _q 
  have p20398 := n20398 _v _q h496
  simp only [e2179, e3158, e3159, e3160, e3161, e3162, e4616, e6501, e8109] at *
  tauto
theorem n20400 (_v : Vars) (_q : Query _v) (h496 : (e496 _v)) : (e3158 _v) := by
  have p15126 := n15126 _v _q 
  have p20399 := n20399 _v _q h496
  simp only [e3158, e3159, e3160, e3161, e3162, e3163, e4616] at *
  tauto
theorem n20401 (_v : Vars) (_q : Query _v) (h496 : (e496 _v)) : (e2402 _v) := by
  have p5255 := n5255 _v _q 
  have p258 := n258 _v _q 
  have p4016 := n4016 _v _q 
  have p20397 := n20397 _v _q 
  have p8144 := n8144 _v _q h496
  exact FloorCertificate.node_20401 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p5255 p258 p4016 p20397 p8144
theorem n20402 (_v : Vars) (_q : Query _v) (h496 : (e496 _v)) : (e3929 _v) := by
  have p14484 := n14484 _v _q 
  have p20401 := n20401 _v _q h496
  simp only [e2402, e3919, e3920, e3921, e3922, e3923, e3929, e6600, e7422] at *
  tauto
theorem n20403 (_v : Vars) (_q : Query _v) (h496 : (e496 _v)) : (e3919 _v) := by
  have p14797 := n14797 _v _q 
  have p20402 := n20402 _v _q h496
  simp only [e3919, e3920, e3921, e3922, e3923, e3924, e3929] at *
  tauto
theorem n20404 (_v : Vars) (_q : Query _v) (h496 : (e496 _v)) : (e48 _v) := by
  have p8144 := n8144 _v _q h496
  have p20397 := n20397 _v _q 
  have p258 := n258 _v _q 
  have p5255 := n5255 _v _q 
  have p5391 := n5391 _v _q 
  have p4016 := n4016 _v _q 
  exact FloorCertificate.node_20404 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8144 p20397 p258 p5255 p5391 p4016
theorem n20405 (_v : Vars) (_q : Query _v) (h496 : (e496 _v)) : (e60 _v) := by
  have p14152 := n14152 _v _q 
  have p20404 := n20404 _v _q h496
  simp only [e48, e51, e52, e57, e58, e59, e60, e5108, e5125] at *
  tauto
theorem n20406 (_v : Vars) (_q : Query _v) (h496 : (e496 _v)) : (e51 _v) := by
  have p14962 := n14962 _v _q 
  have p20405 := n20405 _v _q h496
  simp only [e51, e52, e57, e58, e59, e60, e77] at *
  tauto
theorem n20407 (_v : Vars) (_q : Query _v) (h496 : (e496 _v)) : (e1995 _v) := by
  have p20397 := n20397 _v _q 
  have p258 := n258 _v _q 
  have p8144 := n8144 _v _q h496
  have p5255 := n5255 _v _q 
  have p5391 := n5391 _v _q 
  exact FloorCertificate.node_20407 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p20397 p258 p8144 p5255 p5391
theorem n20408 (_v : Vars) (_q : Query _v) (h496 : (e496 _v)) : (e4575 _v) := by
  have p14696 := n14696 _v _q 
  have p20407 := n20407 _v _q h496
  simp only [e1995, e4567, e4568, e4572, e4573, e4574, e4575, e6423, e8066] at *
  tauto
theorem n20409 (_v : Vars) (_q : Query _v) (h496 : (e496 _v)) : (e4567 _v) := by
  have p8485 := n8485 _v _q 
  have p20408 := n20408 _v _q h496
  simp only [e4567, e4568, e4572, e4573, e4574, e4575, e4956] at *
  tauto
theorem n20410 (_v : Vars) (_q : Query _v) (h496 : (e496 _v)) : (e2468 _v) := by
  have p8144 := n8144 _v _q h496
  have p20397 := n20397 _v _q 
  have p258 := n258 _v _q 
  have p5255 := n5255 _v _q 
  exact FloorCertificate.node_20410 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8144 p20397 p258 p5255
theorem n20411 (_v : Vars) (_q : Query _v) (h496 : (e496 _v)) : (e4798 _v) := by
  have p14690 := n14690 _v _q 
  have p20410 := n20410 _v _q h496
  simp only [e2468, e4790, e4791, e4795, e4796, e4797, e4798, e6630, e8281] at *
  tauto
theorem n20412 (_v : Vars) (_q : Query _v) (h496 : (e496 _v)) : (e4791 _v) := by
  have p14932 := n14932 _v _q 
  have p20411 := n20411 _v _q h496
  simp only [e4790, e4791, e4795, e4796, e4797, e4798, e4953] at *
  tauto
theorem n20413 (_v : Vars) (_q : Query _v) (h496 : (e496 _v)) : (e2242 _v) := by
  have p5255 := n5255 _v _q 
  have p5391 := n5391 _v _q 
  have p258 := n258 _v _q 
  have p20397 := n20397 _v _q 
  have p8144 := n8144 _v _q h496
  exact FloorCertificate.node_20413 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p5255 p5391 p258 p20397 p8144
theorem n20414 (_v : Vars) (_q : Query _v) (h496 : (e496 _v)) : (e4686 _v) := by
  have p14708 := n14708 _v _q 
  have p20413 := n20413 _v _q h496
  simp only [e2242, e4678, e4679, e4683, e4684, e4685, e4686, e6525, e8180] at *
  tauto
theorem n20415 (_v : Vars) (_q : Query _v) (h496 : (e496 _v)) : (e4679 _v) := by
  have p14989 := n14989 _v _q 
  have p20414 := n20414 _v _q h496
  simp only [e4678, e4679, e4683, e4684, e4685, e4686, e4967] at *
  tauto
theorem n20416 (_v : Vars) (_q : Query _v) (h496 : (e496 _v)) : (e2781 _v) := by
  have p20397 := n20397 _v _q 
  have p8144 := n8144 _v _q h496
  have p4016 := n4016 _v _q 
  have p5391 := n5391 _v _q 
  have p5255 := n5255 _v _q 
  have p258 := n258 _v _q 
  exact FloorCertificate.node_20416 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p20397 p8144 p4016 p5391 p5255 p258
theorem n20417 (_v : Vars) (_q : Query _v) (h496 : (e496 _v)) : (e4271 _v) := by
  have p14699 := n14699 _v _q 
  have p20416 := n20416 _v _q h496
  simp only [e2781, e4263, e4264, e4268, e4269, e4270, e4271, e6776, e7795] at *
  tauto
theorem n20418 (_v : Vars) (_q : Query _v) (h496 : (e496 _v)) : (e4264 _v) := by
  have p14966 := n14966 _v _q 
  have p20417 := n20417 _v _q h496
  simp only [e4263, e4264, e4268, e4269, e4270, e4271, e4959] at *
  tauto
theorem n20419 (_v : Vars) (_q : Query _v) (h496 : (e496 _v)) : (e2733 _v) := by
  have p20397 := n20397 _v _q 
  have p5255 := n5255 _v _q 
  have p8144 := n8144 _v _q h496
  have p5391 := n5391 _v _q 
  have p4016 := n4016 _v _q 
  have p258 := n258 _v _q 
  exact FloorCertificate.node_20419 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p20397 p5255 p8144 p5391 p4016 p258
theorem n20420 (_v : Vars) (_q : Query _v) (h496 : (e496 _v)) : (e4109 _v) := by
  have p14689 := n14689 _v _q 
  have p20419 := n20419 _v _q h496
  simp only [e2733, e4101, e4102, e4106, e4107, e4108, e4109, e6750, e7603] at *
  tauto
theorem n20421 (_v : Vars) (_q : Query _v) (h496 : (e496 _v)) : (e4101 _v) := by
  have p14929 := n14929 _v _q 
  have p20420 := n20420 _v _q h496
  simp only [e4101, e4102, e4106, e4107, e4108, e4109, e4952] at *
  tauto
theorem n20422 (_v : Vars) (_q : Query _v) (h496 : (e496 _v)) : (e2061 _v) := by
  have p4016 := n4016 _v _q 
  have p5255 := n5255 _v _q 
  have p5391 := n5391 _v _q 
  have p20397 := n20397 _v _q 
  have p8144 := n8144 _v _q h496
  have p258 := n258 _v _q 
  exact FloorCertificate.node_20422 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p4016 p5255 p5391 p20397 p8144 p258
end
end Assembly
