import Dag267
import generated.th_lemma_36
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n22245 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) : (e2242 _v) := by
  have p5257 := n5257 _v _q 
  have p5391 := n5391 _v _q 
  have p22244 := n22244 _v _q h51
  exact FloorCertificate.node_22245 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p5257 p5391 p22244
theorem n22246 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) : (e4686 _v) := by
  have p14708 := n14708 _v _q 
  have p22245 := n22245 _v _q h51
  change (¬ (e2242 _v)) ∨ (¬ (e4685 _v)) at p14708
  rcases p14708 with hlit | hlit
  · exact (False.elim (hlit p22245))
  · exact hlit
theorem n22247 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) : (e4679 _v) := by
  have p14989 := n14989 _v _q 
  have p22246 := n22246 _v _q h51
  change (e4685 _v) ∨ (e4679 _v) at p14989
  change (¬ (e4685 _v)) at p22246
  rcases p14989 with hlit | hlit
  · exact (False.elim (p22246 hlit))
  · exact hlit
theorem n22248 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) : (e2125 _v) := by
  have p5391 := n5391 _v _q 
  have p22244 := n22244 _v _q h51
  have p5257 := n5257 _v _q 
  have p20651 := n20651 _v _q 
  exact FloorCertificate.node_22248 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p5391 p22244 p5257 p20651
theorem n22249 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) : (e4466 _v) := by
  have p14604 := n14604 _v _q 
  have p22248 := n22248 _v _q h51
  change (¬ (e2125 _v)) ∨ (¬ (e4465 _v)) at p14604
  rcases p14604 with hlit | hlit
  · exact (False.elim (hlit p22248))
  · exact hlit
theorem n22250 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) : (e2179 _v) := by
  have p20827 := n20827 _v _q 
  have p5391 := n5391 _v _q 
  have p5257 := n5257 _v _q 
  have p22244 := n22244 _v _q h51
  exact FloorCertificate.node_22250 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p20827 p5391 p5257 p22244
theorem n22251 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) : (e4616 _v) := by
  have p14684 := n14684 _v _q 
  have p22250 := n22250 _v _q h51
  change (¬ (e2179 _v)) ∨ (¬ (e3162 _v)) at p14684
  rcases p14684 with hlit | hlit
  · exact (False.elim (hlit p22250))
  · exact hlit
theorem n22252 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) : (e2733 _v) := by
  have p22244 := n22244 _v _q h51
  have p5391 := n5391 _v _q 
  have p5257 := n5257 _v _q 
  have p258 := n258 _v _q 
  have p20827 := n20827 _v _q 
  exact FloorCertificate.node_22252 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p22244 p5391 p5257 p258 p20827
theorem n22253 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) : (e4109 _v) := by
  have p14689 := n14689 _v _q 
  have p22252 := n22252 _v _q h51
  change (¬ (e2733 _v)) ∨ (¬ (e4108 _v)) at p14689
  rcases p14689 with hlit | hlit
  · exact (False.elim (hlit p22252))
  · exact hlit
theorem n22254 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) : (e2781 _v) := by
  have p5391 := n5391 _v _q 
  have p5257 := n5257 _v _q 
  have p258 := n258 _v _q 
  have p22244 := n22244 _v _q h51
  exact FloorCertificate.node_22254 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p5391 p5257 p258 p22244
theorem n22255 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) : (e4271 _v) := by
  have p14699 := n14699 _v _q 
  have p22254 := n22254 _v _q h51
  change (¬ (e2781 _v)) ∨ (¬ (e4270 _v)) at p14699
  rcases p14699 with hlit | hlit
  · exact (False.elim (hlit p22254))
  · exact hlit
theorem n22256 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) : (e4264 _v) := by
  have p14966 := n14966 _v _q 
  have p22255 := n22255 _v _q h51
  change (e4270 _v) ∨ (e4264 _v) at p14966
  change (¬ (e4270 _v)) at p22255
  rcases p14966 with hlit | hlit
  · exact (False.elim (p22255 hlit))
  · exact hlit
theorem n22257 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) : (e2402 _v) := by
  have p5391 := n5391 _v _q 
  have p5257 := n5257 _v _q 
  have p22244 := n22244 _v _q h51
  have p20827 := n20827 _v _q 
  exact FloorCertificate.node_22257 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p5391 p5257 p22244 p20827
theorem n22258 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) : (e3929 _v) := by
  have p14484 := n14484 _v _q 
  have p22257 := n22257 _v _q h51
  change (¬ (e2402 _v)) ∨ (¬ (e3923 _v)) at p14484
  rcases p14484 with hlit | hlit
  · exact (False.elim (hlit p22257))
  · exact hlit
theorem n22259 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) : (e4824 _v) := by
  have p14705 := n14705 _v _q 
  have p22244 := n22244 _v _q h51
  change (¬ (e2522 _v)) ∨ (¬ (e4823 _v)) at p14705
  rcases p14705 with hlit | hlit
  · exact (False.elim (hlit p22244))
  · exact hlit
theorem n22260 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) : (e4817 _v) := by
  have p15123 := n15123 _v _q 
  have p22259 := n22259 _v _q h51
  change (e4823 _v) ∨ (e4817 _v) at p15123
  change (¬ (e4823 _v)) at p22259
  rcases p15123 with hlit | hlit
  · exact (False.elim (p22259 hlit))
  · exact hlit
theorem n22261 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) : (e2468 _v) := by
  have p5257 := n5257 _v _q 
  have p22244 := n22244 _v _q h51
  exact FloorCertificate.node_22261 (e2 _v) (e7 _v) (e17 _v) (e45 _v) (e110 _v) p5257 p22244
theorem n22262 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) : (e4798 _v) := by
  have p14690 := n14690 _v _q 
  have p22261 := n22261 _v _q h51
  change (¬ (e2468 _v)) ∨ (¬ (e4797 _v)) at p14690
  rcases p14690 with hlit | hlit
  · exact (False.elim (hlit p22261))
  · exact hlit
theorem n22263 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) : (e4791 _v) := by
  have p14932 := n14932 _v _q 
  have p22262 := n22262 _v _q h51
  change (e4797 _v) ∨ (e4791 _v) at p14932
  change (¬ (e4797 _v)) at p22262
  rcases p14932 with hlit | hlit
  · exact (False.elim (p22262 hlit))
  · exact hlit
theorem n22264 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) : (e2296 _v) := by
  have p22244 := n22244 _v _q h51
  have p5391 := n5391 _v _q 
  exact FloorCertificate.node_22264 (e2 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p22244 p5391
theorem n22265 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) : (e3140 _v) := by
  have p14358 := n14358 _v _q 
  have p22264 := n22264 _v _q h51
  change (¬ (e2296 _v)) ∨ (¬ (e3139 _v)) at p14358
  rcases p14358 with hlit | hlit
  · exact (False.elim (hlit p22264))
  · exact hlit
theorem n22266 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) : (e3133 _v) := by
  have p15098 := n15098 _v _q 
  have p22265 := n22265 _v _q h51
  change (e3139 _v) ∨ (e3133 _v) at p15098
  change (¬ (e3139 _v)) at p22265
  rcases p15098 with hlit | hlit
  · exact (False.elim (p22265 hlit))
  · exact hlit
theorem n22267 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) : (e2061 _v) := by
  have p20827 := n20827 _v _q 
  have p5257 := n5257 _v _q 
  have p22244 := n22244 _v _q h51
  have p5391 := n5391 _v _q 
  have p20651 := n20651 _v _q 
  exact FloorCertificate.node_22267 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p20827 p5257 p22244 p5391 p20651
theorem n22268 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) : (e4447 _v) := by
  have p14688 := n14688 _v _q 
  have p22267 := n22267 _v _q h51
  change (¬ (e2061 _v)) ∨ (¬ (e4446 _v)) at p14688
  rcases p14688 with hlit | hlit
  · exact (False.elim (hlit p22267))
  · exact hlit
theorem n22269 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) : (e1995 _v) := by
  have p12932 := n12932 _v _q 
  have p22244 := n22244 _v _q h51
  change (¬ (e2522 _v)) ∨ (e1995 _v) at p12932
  rcases p12932 with hlit | hlit
  · exact (False.elim (hlit p22244))
  · exact hlit
theorem n22270 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) : (e4575 _v) := by
  have p14696 := n14696 _v _q 
  have p22269 := n22269 _v _q h51
  change (¬ (e1995 _v)) ∨ (¬ (e4574 _v)) at p14696
  rcases p14696 with hlit | hlit
  · exact (False.elim (hlit p22269))
  · exact hlit
theorem n22271 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) : (e4567 _v) := by
  have p8485 := n8485 _v _q 
  have p22270 := n22270 _v _q h51
  change (e4574 _v) ∨ (e4567 _v) at p8485
  change (¬ (e4574 _v)) at p22270
  rcases p8485 with hlit | hlit
  · exact (False.elim (p22270 hlit))
  · exact hlit
theorem n22272 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) : (e4459 _v) := by
  have p8443 := n8443 _v _q 
  have p22249 := n22249 _v _q h51
  change (e4465 _v) ∨ (e4459 _v) at p8443
  change (¬ (e4465 _v)) at p22249
  rcases p8443 with hlit | hlit
  · exact (False.elim (p22249 hlit))
  · exact hlit
theorem n22273 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) : (e3158 _v) := by
  have p15126 := n15126 _v _q 
  have p22251 := n22251 _v _q h51
  change (e3162 _v) ∨ (e3158 _v) at p15126
  change (¬ (e3162 _v)) at p22251
  rcases p15126 with hlit | hlit
  · exact (False.elim (p22251 hlit))
  · exact hlit
theorem n22274 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) : (e4101 _v) := by
  have p14929 := n14929 _v _q 
  have p22253 := n22253 _v _q h51
  change (e4108 _v) ∨ (e4101 _v) at p14929
  change (¬ (e4108 _v)) at p22253
  rcases p14929 with hlit | hlit
  · exact (False.elim (p22253 hlit))
  · exact hlit
theorem n22275 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) : (e3919 _v) := by
  have p14797 := n14797 _v _q 
  have p22258 := n22258 _v _q h51
  change (e3923 _v) ∨ (e3919 _v) at p14797
  change (¬ (e3923 _v)) at p22258
  rcases p14797 with hlit | hlit
  · exact (False.elim (p22258 hlit))
  · exact hlit
theorem n22276 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) : (e4439 _v) := by
  have p14925 := n14925 _v _q 
  have p22268 := n22268 _v _q h51
  change (e4446 _v) ∨ (e4439 _v) at p14925
  change (¬ (e4446 _v)) at p22268
  rcases p14925 with hlit | hlit
  · exact (False.elim (p22268 hlit))
  · exact hlit
theorem n22277 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) : (e5148 _v) := by
  have p17117 := n17117 _v _q 
  have p20651 := n20651 _v _q 
  have p20467 := n20467 _v _q 
  have p17953 := n17953 _v _q 
  have p17133 := n17133 _v _q 
  have p5391 := n5391 _v _q 
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
  have p17113 := n17113 _v _q 
  exact FloorCertificate.node_22277 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2902 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) p17117 p20651 p20467 p17953 p17133 p5391 p17120 p22247 p22272 p17256 p22273 p17089 p22274 p13951 p17104 p20470 p20274 p17286 p17288 p19665 p22256 p16778 p22275 p17127 p17050 p17122 p22260 p16729 p20126 p20426 p17110 p20829 p20653 p22244 p22263 p5257 p17131 p17108 p17294 p16943 p17064 p17067 p17080 p17053 p17072 p17074 p17069 p20096 p20836 p20461 p17874 p22266 p17136 p17087 p17055 p17058 p17098 p17083 p17106 p17020 p17093 p22276 p17100 p17141 p17102 p17091 p17096 p22271 p17758 p17124 p19610 p17111 p17115 p17078 p17113
theorem n22278 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h6571 : (e6571 _v)) : (e95 _v) := by
  have p17953 := n17953 _v _q 
  have p17133 := n17133 _v _q 
  have p5391 := n5391 _v _q 
  have p17120 := n17120 _v _q 
  have p22247 := n22247 _v _q h51
  have p22272 := n22272 _v _q h51
  have p17256 := n17256 _v _q 
  have p22273 := n22273 _v _q h51
  have p17089 := n17089 _v _q 
  have p22274 := n22274 _v _q h51
  have p13951 := n13951 _v _q 
  have p17104 := n17104 _v _q 
  have p20651 := n20651 _v _q 
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
  have p17113 := n17113 _v _q 
  have p17117 := n17117 _v _q 
  have p20467 := n20467 _v _q 
  have p8447 := n8447 _v _q h6571
  have p20827 := n20827 _v _q 
  exact FloorCertificate.node_22278 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2902 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) p17953 p17133 p5391 p17120 p22247 p22272 p17256 p22273 p17089 p22274 p13951 p17104 p20651 p20470 p20274 p17286 p17288 p19665 p22256 p16778 p22275 p17127 p17050 p17122 p22260 p16729 p20126 p20426 p17110 p20829 p20653 p22244 p22263 p5257 p17131 p17108 p17294 p16943 p17064 p17067 p17080 p17053 p17072 p17074 p17069 p20096 p20836 p20461 p17874 p22266 p17136 p17087 p17055 p17058 p17098 p17083 p17106 p17020 p17093 p22276 p17100 p17141 p17102 p17091 p17096 p22271 p17758 p17124 p19610 p17111 p17115 p17078 p17113 p17117 p20467 p8447 p20827
theorem n22279 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) : (e5149 _v) := by
  have p15925 := n15925 _v _q 
  have p22277 := n22277 _v _q h51
  change (e5149 _v) ∨ (e5145 _v) at p15925
  change (¬ (e5145 _v)) at p22277
  rcases p15925 with hlit | hlit
  · exact hlit
  · exact (False.elim (p22277 hlit))
theorem n22280 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) : (e79 _v) := by
  have p15115 := n15115 _v _q 
  have p22279 := n22279 _v _q h51
  change (e79 _v) ∨ (¬ (e5149 _v)) at p15115
  rcases p15115 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p22279))
theorem n22281 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h6571 : (e6571 _v)) : (e5134 _v) := by
  have p16235 := n16235 _v _q 
  have p22278 := n22278 _v _q h51 h6571
  change (e5134 _v) ∨ (e91 _v) at p16235
  change (¬ (e91 _v)) at p22278
  rcases p16235 with hlit | hlit
  · exact hlit
  · exact (False.elim (p22278 hlit))
theorem n22282 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h6571 : (e6571 _v)) : (e7489 _v) := by
  have p14729 := n14729 _v _q 
  have p22280 := n22280 _v _q h51
  have p22281 := n22281 _v _q h51 h6571
  change (¬ (e79 _v)) ∨ (¬ (e5134 _v)) at p14729
  rcases p14729 with hlit | hlit
  · exact (False.elim (hlit p22280))
  · exact (False.elim (hlit p22281))
theorem n22284 (_v : Vars) (_q : Query _v)  : (e22283 _v) := by
  by_contra hc
  change ¬ ((e2358 _v) ∨ (¬ (e51 _v))) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr hn))
  have h6571 : (e6571 _v) := (fun hn => hc (Or.inl hn))
  have p22282 := n22282 _v _q h51 h6571
  exact p22282
theorem n22285 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) : (e2358 _v) := by
  have p22284 := n22284 _v _q 
  have p16729 := n16729 _v _q h51
  change (e2358 _v) ∨ (¬ (e51 _v)) at p22284
  rcases p22284 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p16729))
theorem n22286 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) : (e196 _v) := by
  have p11357 := n11357 _v _q 
  have p22285 := n22285 _v _q h51
  change (e196 _v) ∨ (¬ (e2358 _v)) at p11357
  rcases p11357 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p22285))
theorem n22287 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) : (e5203 _v) := by
  have p14730 := n14730 _v _q 
  have p22286 := n22286 _v _q h51
  change (¬ (e196 _v)) ∨ (¬ (e5193 _v)) at p14730
  rcases p14730 with hlit | hlit
  · exact (False.elim (hlit p22286))
  · exact hlit
theorem n22288 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) : (e191 _v) := by
  have p16442 := n16442 _v _q 
  have p22287 := n22287 _v _q h51
  change (e5193 _v) ∨ (e191 _v) at p16442
  change (¬ (e5193 _v)) at p22287
  rcases p16442 with hlit | hlit
  · exact (False.elim (p22287 hlit))
  · exact hlit
theorem n22289 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h5145 : (e5145 _v)) : (e7489 _v) := by
  have p22285 := n22285 _v _q h51
  have p5391 := n5391 _v _q 
  have p22288 := n22288 _v _q h51
  have p17245 := n17245 _v _q h5145
  have p17117 := n17117 _v _q 
  have p20651 := n20651 _v _q 
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
  have p17113 := n17113 _v _q 
  exact FloorCertificate.node_22289 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2902 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) p22285 p5391 p22288 p17245 p17117 p20651 p20467 p17133 p17120 p22247 p22272 p17256 p22273 p17089 p22274 p13951 p17104 p20470 p20274 p17286 p17288 p19665 p22256 p16778 p22275 p17127 p17050 p17122 p22260 p16729 p20126 p20426 p17110 p20829 p20653 p22244 p22263 p5257 p17131 p17108 p17294 p16943 p17064 p17067 p17080 p17053 p17072 p17074 p17069 p20096 p20836 p20461 p17874 p22266 p17136 p17087 p17055 p17058 p17098 p17083 p17106 p17020 p17093 p22276 p17100 p17141 p17102 p17091 p17096 p22271 p17758 p17124 p19610 p17111 p17115 p17078 p17113
theorem n22291 (_v : Vars) (_q : Query _v)  : (e22290 _v) := by
  by_contra hc
  change ¬ ((¬ (e5145 _v)) ∨ (¬ (e51 _v))) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr hn))
  have h5145 : (e5145 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have p22289 := n22289 _v _q h51 h5145
  exact p22289
end
end Assembly
