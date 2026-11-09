import Dag227
import generated.th_lemma_29
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n20278 (_v : Vars) (_q : Query _v) (h6636 : (e6636 _v)) : (e8292 _v) := by
  have p14657 := n14657 _v _q 
  have p20277 := n20277 _v _q h6636
  change (e2522 _v) ∨ (¬ (e8284 _v)) at p14657
  change (¬ (e2522 _v)) at p20277
  rcases p14657 with hlit | hlit
  · exact (False.elim (p20277 hlit))
  · exact hlit
theorem n20279 (_v : Vars) (_q : Query _v) (h6636 : (e6636 _v)) : (e6694 _v) := by
  have p8663 := n8663 _v _q 
  have p20272 := n20272 _v _q 
  have p5255 := n5255 _v _q 
  have p10893 := n10893 _v _q 
  have p11031 := n11031 _v _q h6636
  have p5257 := n5257 _v _q 
  exact FloorCertificate.node_20279 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8663 p20272 p5255 p10893 p11031 p5257
theorem n20280 (_v : Vars) (_q : Query _v) (h6636 : (e6636 _v)) : (e7895 _v) := by
  have p14589 := n14589 _v _q 
  have p20279 := n20279 _v _q h6636
  change (e251 _v) ∨ (¬ (e7887 _v)) at p14589
  change (¬ (e251 _v)) at p20279
  rcases p14589 with hlit | hlit
  · exact (False.elim (p20279 hlit))
  · exact hlit
theorem n20281 (_v : Vars) (_q : Query _v) (h6636 : (e6636 _v)) : (e6630 _v) := by
  have p8663 := n8663 _v _q 
  have p10893 := n10893 _v _q 
  have p11031 := n11031 _v _q h6636
  have p5257 := n5257 _v _q 
  have p5255 := n5255 _v _q 
  have p20272 := n20272 _v _q 
  exact FloorCertificate.node_20281 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8663 p10893 p11031 p5257 p5255 p20272
theorem n20282 (_v : Vars) (_q : Query _v) (h6636 : (e6636 _v)) : (e8275 _v) := by
  have p14655 := n14655 _v _q 
  have p20281 := n20281 _v _q h6636
  change (e2468 _v) ∨ (¬ (e8267 _v)) at p14655
  change (¬ (e2468 _v)) at p20281
  rcases p14655 with hlit | hlit
  · exact (False.elim (p20281 hlit))
  · exact hlit
theorem n20283 (_v : Vars) (_q : Query _v) (h6636 : (e6636 _v)) : (e5392 _v) := by
  have p11031 := n11031 _v _q h6636
  have p8663 := n8663 _v _q 
  have p10893 := n10893 _v _q 
  have p20272 := n20272 _v _q 
  have p5255 := n5255 _v _q 
  have p5257 := n5257 _v _q 
  exact FloorCertificate.node_20283 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p11031 p8663 p10893 p20272 p5255 p5257
theorem n20284 (_v : Vars) (_q : Query _v) (h6636 : (e6636 _v)) : (e5403 _v) := by
  have p14577 := n14577 _v _q 
  have p20283 := n20283 _v _q h6636
  change (e474 _v) ∨ (¬ (e5402 _v)) at p14577
  change (¬ (e474 _v)) at p20283
  rcases p14577 with hlit | hlit
  · exact (False.elim (p20283 hlit))
  · exact hlit
theorem n20285 (_v : Vars) (_q : Query _v)  : (e6780 _v) := by
  have p19394 := n19394 _v _q 
  have p20272 := n20272 _v _q 
  change (¬ (e2799 _v)) ∨ (¬ (e2793 _v)) at p19394
  rcases p19394 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p20272))
theorem n20286 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) : (e7714 _v) := by
  have p16861 := n16861 _v _q 
  have p15593 := n15593 _v _q h5362
  change (e7726 _v) ∨ (e7714 _v) at p16861
  change (¬ (e7726 _v)) at p15593
  rcases p16861 with hlit | hlit
  · exact (False.elim (p15593 hlit))
  · exact hlit
theorem n20287 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) (h5362 : (e5362 _v)) : (e4684 _v) := by
  have p15073 := n15073 _v _q h2468
  have p19693 := n19693 _v _q h5362
  have p5255 := n5255 _v _q 
  have p19673 := n19673 _v _q h5362
  have p17120 := n17120 _v _q 
  have p17953 := n17953 _v _q 
  have p17256 := n17256 _v _q 
  have p19694 := n19694 _v _q h5362
  have p16778 := n16778 _v _q 
  have p15591 := n15591 _v _q h5362
  have p20286 := n20286 _v _q h5362
  have p19763 := n19763 _v _q h2468 h5362
  have p17111 := n17111 _v _q 
  have p15104 := n15104 _v _q h2468
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
  have p16938 := n16938 _v _q h2468
  have p16941 := n16941 _v _q h2468
  have p17108 := n17108 _v _q 
  have p15071 := n15071 _v _q h2468
  have p19775 := n19775 _v _q h2468 h5362
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
  have p13951 := n13951 _v _q 
  have p7488 := n7488 _v _q h5362
  have p16859 := n16859 _v _q h2468
  have p15733 := n15733 _v _q h5362
  have p19777 := n19777 _v _q h2468 h5362
  exact FloorCertificate.node_20287 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2902 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4808 _v) p15073 p19693 p5255 p19673 p17120 p17953 p17256 p19694 p16778 p15591 p20286 p19763 p17111 p15104 p17252 p19720 p17874 p17127 p15595 p20274 p18120 p17253 p17050 p17009 p17133 p17089 p19665 p16992 p17055 p16938 p16941 p17108 p15071 p19775 p20126 p15087 p17131 p17110 p17053 p15723 p20096 p17294 p15725 p17058 p17064 p17067 p17069 p17072 p17136 p19728 p17078 p17080 p17083 p17074 p17087 p17758 p17091 p17093 p15728 p17141 p17098 p17106 p17100 p17102 p19610 p17104 p17096 p17113 p15731 p17122 p17117 p17124 p17115 p13951 p7488 p16859 p15733 p19777
theorem n20288 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h2468 : (e2468 _v)) (h5362 : (e5362 _v)) : (e4686 _v) := by
  have p14708 := n14708 _v _q 
  have p19688 := n19688 _v _q h2351 h2468 h5362
  change (¬ (e2242 _v)) ∨ (¬ (e4685 _v)) at p14708
  rcases p14708 with hlit | hlit
  · exact (False.elim (hlit p19688))
  · exact hlit
theorem n20289 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h2468 : (e2468 _v)) (h5362 : (e5362 _v)) : (e4679 _v) := by
  have p14989 := n14989 _v _q 
  have p20288 := n20288 _v _q h2351 h2468 h5362
  change (e4685 _v) ∨ (e4679 _v) at p14989
  change (¬ (e4685 _v)) at p20288
  rcases p14989 with hlit | hlit
  · exact (False.elim (p20288 hlit))
  · exact hlit
theorem n20290 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h2468 : (e2468 _v)) (h5362 : (e5362 _v)) : (e4447 _v) := by
  have p14688 := n14688 _v _q 
  have p19690 := n19690 _v _q h2351 h2468 h5362
  change (¬ (e2061 _v)) ∨ (¬ (e4446 _v)) at p14688
  rcases p14688 with hlit | hlit
  · exact (False.elim (hlit p19690))
  · exact hlit
theorem n20291 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h2468 : (e2468 _v)) (h5362 : (e5362 _v)) : (e4439 _v) := by
  have p14925 := n14925 _v _q 
  have p20290 := n20290 _v _q h2351 h2468 h5362
  change (e4446 _v) ∨ (e4439 _v) at p14925
  change (¬ (e4446 _v)) at p20290
  rcases p14925 with hlit | hlit
  · exact (False.elim (p20290 hlit))
  · exact hlit
theorem n20292 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h2468 : (e2468 _v)) (h5362 : (e5362 _v)) : (e4575 _v) := by
  have p14696 := n14696 _v _q 
  have p19691 := n19691 _v _q h2351 h2468 h5362
  change (¬ (e1995 _v)) ∨ (¬ (e4574 _v)) at p14696
  rcases p14696 with hlit | hlit
  · exact (False.elim (hlit p19691))
  · exact hlit
theorem n20293 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h2468 : (e2468 _v)) (h5362 : (e5362 _v)) : (e4567 _v) := by
  have p8485 := n8485 _v _q 
  have p20292 := n20292 _v _q h2351 h2468 h5362
  change (e4574 _v) ∨ (e4567 _v) at p8485
  change (¬ (e4574 _v)) at p20292
  rcases p8485 with hlit | hlit
  · exact (False.elim (p20292 hlit))
  · exact hlit
theorem n20294 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) : (e4459 _v) := by
  have p16784 := n16784 _v _q 
  have p15591 := n15591 _v _q h5362
  change (e4459 _v) ∨ (¬ (e7749 _v)) at p16784
  rcases p16784 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p15591))
theorem n20295 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h2468 : (e2468 _v)) (h3133 : (e3133 _v)) (h4813 : (e4813 _v)) (h5362 : (e5362 _v)) (h7714 : (e7714 _v)) : (e7489 _v) := by
  have p17953 := n17953 _v _q 
  have p19674 := n19674 _v _q h5362
  have p19694 := n19694 _v _q h5362
  have p20289 := n20289 _v _q h2351 h2468 h5362
  have p8438 := n8438 _v _q h2468
  have p5255 := n5255 _v _q 
  have p17247 := n17247 _v _q h7714
  have p15073 := n15073 _v _q h2468
  have p17111 := n17111 _v _q 
  have p15104 := n15104 _v _q h2468
  have p17252 := n17252 _v _q h5362
  have p19720 := n19720 _v _q h5362
  have p13951 := n13951 _v _q 
  have p19718 := n19718 _v _q h2468 h5362
  have p15595 := n15595 _v _q h5362
  have p20274 := n20274 _v _q 
  have p7488 := n7488 _v _q h5362
  have p17253 := n17253 _v _q h5362
  have p17050 := n17050 _v _q 
  have p17062 := n17062 _v _q h3133
  have p17133 := n17133 _v _q 
  have p17089 := n17089 _v _q 
  have p19665 := n19665 _v _q 
  have p16992 := n16992 _v _q 
  have p17055 := n17055 _v _q 
  have p20291 := n20291 _v _q h2351 h2468 h5362
  have p20293 := n20293 _v _q h2351 h2468 h5362
  have p17108 := n17108 _v _q 
  have p16859 := n16859 _v _q h2468
  have p15793 := n15793 _v _q h2351
  have p20126 := n20126 _v _q 
  have p15087 := n15087 _v _q h5362
  have p17131 := n17131 _v _q 
  have p17110 := n17110 _v _q 
  have p17053 := n17053 _v _q 
  have p15723 := n15723 _v _q h5362
  have p20096 := n20096 _v _q 
  have p17294 := n17294 _v _q 
  have p8464 := n8464 _v _q h2351
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
  have p4983 := n4983 _v _q h4813
  have p17113 := n17113 _v _q 
  have p15731 := n15731 _v _q h5362
  have p17122 := n17122 _v _q 
  have p17117 := n17117 _v _q 
  have p17124 := n17124 _v _q 
  have p17115 := n17115 _v _q 
  have p17120 := n17120 _v _q 
  have p18120 := n18120 _v _q h5362
  have p17127 := n17127 _v _q 
  have p16778 := n16778 _v _q 
  have p17874 := n17874 _v _q 
  have p20294 := n20294 _v _q h5362
  exact FloorCertificate.node_20295 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2902 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e4808 _v) p17953 p19674 p19694 p20289 p8438 p5255 p17247 p15073 p17111 p15104 p17252 p19720 p13951 p19718 p15595 p20274 p7488 p17253 p17050 p17062 p17133 p17089 p19665 p16992 p17055 p20291 p20293 p17108 p16859 p15793 p20126 p15087 p17131 p17110 p17053 p15723 p20096 p17294 p8464 p15725 p17058 p17064 p17067 p17069 p17072 p17136 p19728 p17078 p17080 p17083 p17074 p17087 p17758 p17091 p17093 p15728 p17141 p17098 p17106 p17100 p17102 p19610 p17104 p17096 p4983 p17113 p15731 p17122 p17117 p17124 p17115 p17120 p18120 p17127 p16778 p17874 p20294
theorem n20296 (_v : Vars) (_q : Query _v) (h6636 : (e6636 _v)) : (e3937 _v) := by
  have p15012 := n15012 _v _q 
  have p20276 := n20276 _v _q h6636
  change (e7415 _v) ∨ (e3937 _v) at p15012
  change (¬ (e7415 _v)) at p20276
  rcases p15012 with hlit | hlit
  · exact (False.elim (p20276 hlit))
  · exact hlit
theorem n20297 (_v : Vars) (_q : Query _v) (h6636 : (e6636 _v)) : (e4813 _v) := by
  have p16259 := n16259 _v _q 
  have p20278 := n20278 _v _q h6636
  change (e8284 _v) ∨ (e4813 _v) at p16259
  change (¬ (e8284 _v)) at p20278
  rcases p16259 with hlit | hlit
  · exact (False.elim (p20278 hlit))
  · exact hlit
theorem n20298 (_v : Vars) (_q : Query _v) (h6636 : (e6636 _v)) : (e4369 _v) := by
  have p16222 := n16222 _v _q 
  have p20280 := n20280 _v _q h6636
  change (e7887 _v) ∨ (e4369 _v) at p16222
  change (¬ (e7887 _v)) at p20280
  rcases p16222 with hlit | hlit
  · exact (False.elim (p20280 hlit))
  · exact hlit
theorem n20299 (_v : Vars) (_q : Query _v) (h6636 : (e6636 _v)) : (e4787 _v) := by
  have p15670 := n15670 _v _q 
  have p20282 := n20282 _v _q h6636
  change (e8267 _v) ∨ (e4787 _v) at p15670
  change (¬ (e8267 _v)) at p20282
  rcases p15670 with hlit | hlit
  · exact (False.elim (p20282 hlit))
  · exact hlit
theorem n20300 (_v : Vars) (_q : Query _v) (h6636 : (e6636 _v)) : (e488 _v) := by
  have p15090 := n15090 _v _q 
  have p20284 := n20284 _v _q h6636
  change (e5402 _v) ∨ (e488 _v) at p15090
  change (¬ (e5402 _v)) at p20284
  rcases p15090 with hlit | hlit
  · exact (False.elim (p20284 hlit))
  · exact hlit
theorem n20301 (_v : Vars) (_q : Query _v)  : (e8408 _v) := by
  have p15435 := n15435 _v _q 
  have p20285 := n20285 _v _q 
  change (e2799 _v) ∨ (¬ (e8407 _v)) at p15435
  change (¬ (e2799 _v)) at p20285
  rcases p15435 with hlit | hlit
  · exact (False.elim (p20285 hlit))
  · exact hlit
theorem n20302 (_v : Vars) (_q : Query _v)  : (e8395 _v) := by
  have p19396 := n19396 _v _q 
  have p20301 := n20301 _v _q 
  change (e8407 _v) ∨ (e8395 _v) at p19396
  change (¬ (e8407 _v)) at p20301
  rcases p19396 with hlit | hlit
  · exact (False.elim (p20301 hlit))
  · exact hlit
theorem n20303 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) (h5362 : (e5362 _v)) : (e4685 _v) := by
  have p14989 := n14989 _v _q 
  have p20287 := n20287 _v _q h2468 h5362
  change (e4685 _v) ∨ (e4679 _v) at p14989
  change (¬ (e4679 _v)) at p20287
  rcases p14989 with hlit | hlit
  · exact hlit
  · exact (False.elim (p20287 hlit))
theorem n20305 (_v : Vars) (_q : Query _v)  : (e20304 _v) := by
  by_contra hc
  change ¬ ((¬ (e2468 _v)) ∨ (¬ (e7714 _v)) ∨ (e436 _v) ∨ (¬ (e3133 _v)) ∨ (¬ (e2351 _v)) ∨ (¬ (e4813 _v))) at hc
  have h2351 : (e2351 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h2468 : (e2468 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h3133 : (e3133 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))
  have h5362 : (e5362 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h7714 : (e7714 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have p20295 := n20295 _v _q h2351 h2468 h3133 h4813 h5362 h7714
  exact p20295
theorem n20306 (_v : Vars) (_q : Query _v)  : (e4899 _v) := by
  have p20302 := n20302 _v _q 
  have p20274 := n20274 _v _q 
  have p20272 := n20272 _v _q 
  exact FloorCertificate.node_20306 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) (e2913 _v) (e2996 _v) p20302 p20274 p20272
theorem n20307 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) (h5362 : (e5362 _v)) : (e6525 _v) := by
  have p14708 := n14708 _v _q 
  have p20303 := n20303 _v _q h2468 h5362
  change (¬ (e2242 _v)) ∨ (¬ (e4685 _v)) at p14708
  rcases p14708 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p20303))
theorem n20308 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) (h5362 : (e5362 _v)) : (e8174 _v) := by
  have p14634 := n14634 _v _q 
  have p20307 := n20307 _v _q h2468 h5362
  change (e2242 _v) ∨ (¬ (e8166 _v)) at p14634
  change (¬ (e2242 _v)) at p20307
  rcases p14634 with hlit | hlit
  · exact (False.elim (p20307 hlit))
  · exact hlit
theorem n20309 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) (h5362 : (e5362 _v)) : (e4675 _v) := by
  have p15965 := n15965 _v _q 
  have p20308 := n20308 _v _q h2468 h5362
  change (e8166 _v) ∨ (e4675 _v) at p15965
  change (¬ (e8166 _v)) at p20308
  rcases p15965 with hlit | hlit
  · exact (False.elim (p20308 hlit))
  · exact hlit
theorem n20310 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h5362 : (e5362 _v)) (h7714 : (e7714 _v)) : (e6630 _v) := by
  have p20305 := n20305 _v _q 
  have p17247 := n17247 _v _q h7714
  have p7488 := n7488 _v _q h5362
  have p15783 := n15783 _v _q h2351
  have p8464 := n8464 _v _q h2351
  have p19687 := n19687 _v _q h2351 h5362
  change (¬ (e2468 _v)) ∨ (¬ (e7714 _v)) ∨ (e436 _v) ∨ (¬ (e3133 _v)) ∨ (¬ (e2351 _v)) ∨ (¬ (e4813 _v)) at p20305
  change (¬ (e436 _v)) at p7488
  rcases p20305 with hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p17247))
  · exact (False.elim (p7488 hlit))
  · exact (False.elim (hlit p15783))
  · exact (False.elim (hlit p8464))
  · exact (False.elim (hlit p19687))
theorem n20311 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) (h5362 : (e5362 _v)) : (e7489 _v) := by
  have p20309 := n20309 _v _q h2468 h5362
  have p15736 := n15736 _v _q h5362
  have p20307 := n20307 _v _q h2468 h5362
  have p17256 := n17256 _v _q 
  have p17009 := n17009 _v _q 
  have p16859 := n16859 _v _q h2468
  have p15073 := n15073 _v _q h2468
  have p19693 := n19693 _v _q h5362
  have p5255 := n5255 _v _q 
  have p19673 := n19673 _v _q h5362
  have p17120 := n17120 _v _q 
  have p17953 := n17953 _v _q 
  have p19694 := n19694 _v _q h5362
  have p16778 := n16778 _v _q 
  have p15591 := n15591 _v _q h5362
  have p20286 := n20286 _v _q h5362
  have p19763 := n19763 _v _q h2468 h5362
  have p17111 := n17111 _v _q 
  have p15104 := n15104 _v _q h2468
  have p17252 := n17252 _v _q h5362
  have p19720 := n19720 _v _q h5362
  have p17874 := n17874 _v _q 
  have p17127 := n17127 _v _q 
  have p15595 := n15595 _v _q h5362
  have p20274 := n20274 _v _q 
  have p18120 := n18120 _v _q h5362
  have p17253 := n17253 _v _q h5362
  have p17050 := n17050 _v _q 
  have p7488 := n7488 _v _q h5362
  have p17133 := n17133 _v _q 
  have p17089 := n17089 _v _q 
  have p19665 := n19665 _v _q 
  have p16992 := n16992 _v _q 
  have p17055 := n17055 _v _q 
  have p16938 := n16938 _v _q h2468
  have p16941 := n16941 _v _q h2468
  have p17108 := n17108 _v _q 
  have p15071 := n15071 _v _q h2468
  have p19775 := n19775 _v _q h2468 h5362
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
  have p13951 := n13951 _v _q 
  have p15733 := n15733 _v _q h5362
  have p19777 := n19777 _v _q h2468 h5362
  exact FloorCertificate.node_20311 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2902 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4808 _v) p20309 p15736 p20307 p17256 p17009 p16859 p15073 p19693 p5255 p19673 p17120 p17953 p19694 p16778 p15591 p20286 p19763 p17111 p15104 p17252 p19720 p17874 p17127 p15595 p20274 p18120 p17253 p17050 p7488 p17133 p17089 p19665 p16992 p17055 p16938 p16941 p17108 p15071 p19775 p20126 p15087 p17131 p17110 p17053 p15723 p20096 p17294 p15725 p17058 p17064 p17067 p17069 p17072 p17136 p19728 p17078 p17080 p17083 p17074 p17087 p17758 p17091 p17093 p15728 p17141 p17098 p17106 p17100 p17102 p19610 p17104 p17096 p17113 p15731 p17122 p17117 p17124 p17115 p13951 p15733 p19777
theorem n20312 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h5362 : (e5362 _v)) (h7714 : (e7714 _v)) : (e8275 _v) := by
  have p14655 := n14655 _v _q 
  have p20310 := n20310 _v _q h2351 h5362 h7714
  change (e2468 _v) ∨ (¬ (e8267 _v)) at p14655
  change (¬ (e2468 _v)) at p20310
  rcases p14655 with hlit | hlit
  · exact (False.elim (p20310 hlit))
  · exact hlit
theorem n20313 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h5362 : (e5362 _v)) (h7714 : (e7714 _v)) : (e4787 _v) := by
  have p15670 := n15670 _v _q 
  have p20312 := n20312 _v _q h2351 h5362 h7714
  change (e8267 _v) ∨ (e4787 _v) at p15670
  change (¬ (e8267 _v)) at p20312
  rcases p15670 with hlit | hlit
  · exact (False.elim (p20312 hlit))
  · exact hlit
theorem n20314 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h2402 : (e2402 _v)) (h5362 : (e5362 _v)) (h7714 : (e7714 _v)) : (e8310 _v) := by
  have p20310 := n20310 _v _q h2351 h5362 h7714
  have p7488 := n7488 _v _q h5362
  have p8591 := n8591 _v _q h2402
  have p5255 := n5255 _v _q 
  have p5257 := n5257 _v _q 
  exact FloorCertificate.node_20314 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p20310 p7488 p8591 p5255 p5257
theorem n20315 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h2402 : (e2402 _v)) (h5362 : (e5362 _v)) (h7714 : (e7714 _v)) : (e8322 _v) := by
  have p15218 := n15218 _v _q 
  have p20314 := n20314 _v _q h2351 h2402 h5362 h7714
  change (e2529 _v) ∨ (¬ (e8321 _v)) at p15218
  change (¬ (e2529 _v)) at p20314
  rcases p15218 with hlit | hlit
  · exact (False.elim (p20314 hlit))
  · exact hlit
theorem n20317 (_v : Vars) (_q : Query _v)  : (e20316 _v) := by
  by_contra hc
  change ¬ ((¬ (e2468 _v)) ∨ (e436 _v)) at hc
  have h2468 : (e2468 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h5362 : (e5362 _v) := (fun hn => hc (Or.inr hn))
  have p20311 := n20311 _v _q h2468 h5362
  exact p20311
theorem n20318 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) : (e6630 _v) := by
  have p20317 := n20317 _v _q 
  have p7488 := n7488 _v _q h5362
  change (¬ (e2468 _v)) ∨ (e436 _v) at p20317
  change (¬ (e436 _v)) at p7488
  rcases p20317 with hlit | hlit
  · exact hlit
  · exact (False.elim (p7488 hlit))
theorem n20319 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) : (e4567 _v) := by
  have p8485 := n8485 _v _q 
  have p15788 := n15788 _v _q h2351
  change (e4574 _v) ∨ (e4567 _v) at p8485
  change (¬ (e4574 _v)) at p15788
  rcases p8485 with hlit | hlit
  · exact (False.elim (p15788 hlit))
  · exact hlit
theorem n20320 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h2402 : (e2402 _v)) (h5362 : (e5362 _v)) (h7714 : (e7714 _v)) : (e8317 _v) := by
  have p11541 := n11541 _v _q 
  have p20315 := n20315 _v _q h2351 h2402 h5362 h7714
  change (e8321 _v) ∨ (e8317 _v) at p11541
  change (¬ (e8321 _v)) at p20315
  rcases p11541 with hlit | hlit
  · exact (False.elim (p20315 hlit))
  · exact hlit
theorem n20321 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h2402 : (e2402 _v)) (h4679 : (e4679 _v)) (h5362 : (e5362 _v)) (h7714 : (e7714 _v)) : (e7489 _v) := by
  have p17953 := n17953 _v _q 
  have p15742 := n15742 _v _q h5362
  have p19694 := n19694 _v _q h5362
  have p17070 := n17070 _v _q h4679
  have p16778 := n16778 _v _q 
  have p20313 := n20313 _v _q h2351 h5362 h7714
  have p17247 := n17247 _v _q h7714
  have p14799 := n14799 _v _q h2402
  have p17111 := n17111 _v _q 
  have p20294 := n20294 _v _q h5362
  have p17252 := n17252 _v _q h5362
  have p19720 := n19720 _v _q h5362
  have p17874 := n17874 _v _q 
  have p17127 := n17127 _v _q 
  have p15595 := n15595 _v _q h5362
  have p20274 := n20274 _v _q 
  have p18120 := n18120 _v _q h5362
  have p17253 := n17253 _v _q h5362
  have p17050 := n17050 _v _q 
  have p15783 := n15783 _v _q h2351
  have p17133 := n17133 _v _q 
  have p17089 := n17089 _v _q 
  have p19665 := n19665 _v _q 
  have p16992 := n16992 _v _q 
  have p17055 := n17055 _v _q 
  have p15786 := n15786 _v _q h2351
  have p20319 := n20319 _v _q h2351
  have p17108 := n17108 _v _q 
  have p15796 := n15796 _v _q h2402
  have p15793 := n15793 _v _q h2351
  have p20126 := n20126 _v _q 
  have p15087 := n15087 _v _q h5362
  have p17131 := n17131 _v _q 
  have p17110 := n17110 _v _q 
  have p17053 := n17053 _v _q 
  have p15723 := n15723 _v _q h5362
  have p20096 := n20096 _v _q 
  have p17294 := n17294 _v _q 
  have p5255 := n5255 _v _q 
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
  have p20310 := n20310 _v _q h2351 h5362 h7714
  have p17113 := n17113 _v _q 
  have p15731 := n15731 _v _q h5362
  have p17122 := n17122 _v _q 
  have p17117 := n17117 _v _q 
  have p17124 := n17124 _v _q 
  have p17115 := n17115 _v _q 
  have p17120 := n17120 _v _q 
  have p13951 := n13951 _v _q 
  have p8591 := n8591 _v _q h2402
  have p8464 := n8464 _v _q h2351
  have p7488 := n7488 _v _q h5362
  have p5257 := n5257 _v _q 
  have p19687 := n19687 _v _q h2351 h5362
  have p20320 := n20320 _v _q h2351 h2402 h5362 h7714
  exact FloorCertificate.node_20321 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2902 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e4541 _v) (e4808 _v) p17953 p15742 p19694 p17070 p16778 p20313 p17247 p14799 p17111 p20294 p17252 p19720 p17874 p17127 p15595 p20274 p18120 p17253 p17050 p15783 p17133 p17089 p19665 p16992 p17055 p15786 p20319 p17108 p15796 p15793 p20126 p15087 p17131 p17110 p17053 p15723 p20096 p17294 p5255 p15725 p17058 p17064 p17067 p17069 p17072 p17136 p19728 p17078 p17080 p17083 p17074 p17087 p17758 p17091 p17093 p15728 p17141 p17098 p17106 p17100 p17102 p19610 p17104 p17096 p20310 p17113 p15731 p17122 p17117 p17124 p17115 p17120 p13951 p8591 p8464 p7488 p5257 p19687 p20320
theorem n20322 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) : (e8275 _v) := by
  have p14655 := n14655 _v _q 
  have p20318 := n20318 _v _q h5362
  change (e2468 _v) ∨ (¬ (e8267 _v)) at p14655
  change (¬ (e2468 _v)) at p20318
  rcases p14655 with hlit | hlit
  · exact (False.elim (p20318 hlit))
  · exact hlit
theorem n20323 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) : (e4787 _v) := by
  have p15670 := n15670 _v _q 
  have p20322 := n20322 _v _q h5362
  change (e8267 _v) ∨ (e4787 _v) at p15670
  change (¬ (e8267 _v)) at p20322
  rcases p15670 with hlit | hlit
  · exact (False.elim (p20322 hlit))
  · exact hlit
theorem n20325 (_v : Vars) (_q : Query _v)  : (e20324 _v) := by
  by_contra hc
  change ¬ ((¬ (e2402 _v)) ∨ (¬ (e4679 _v)) ∨ (¬ (e7714 _v)) ∨ (¬ (e2351 _v)) ∨ (e436 _v)) at hc
  have h2351 : (e2351 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h2402 : (e2402 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h4679 : (e4679 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h5362 : (e5362 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr hn)))))
  have h7714 : (e7714 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have p20321 := n20321 _v _q h2351 h2402 h4679 h5362 h7714
  exact p20321
end
end Assembly
