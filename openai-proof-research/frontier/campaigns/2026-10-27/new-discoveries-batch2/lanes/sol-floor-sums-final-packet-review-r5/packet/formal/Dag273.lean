import Dag272
import generated.th_lemma_37
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n22487 (_v : Vars) (_q : Query _v) (h3937 : (e3937 _v)) (h4139 : (e4139 _v)) (h4285 : (e4285 _v)) (h4306 : (e4306 _v)) (h4608 : (e4608 _v)) (h7749 : (e7749 _v)) : (e8035 _v) := by
  have p14871 := n14871 _v _q 
  have p22486 := n22486 _v _q h3937 h4139 h4285 h4306 h4608 h7749
  change (¬ (e2475 _v)) ∨ (¬ (e8029 _v)) at p14871
  rcases p14871 with hlit | hlit
  · exact (False.elim (hlit p22486))
  · exact hlit
theorem n22488 (_v : Vars) (_q : Query _v) (h2303 : (e2303 _v)) (h3937 : (e3937 _v)) (h4306 : (e4306 _v)) (h4608 : (e4608 _v)) (h7749 : (e7749 _v)) : (e2475 _v) := by
  have p22481 := n22481 _v _q 
  have p16436 := n16436 _v _q h2303
  have p16439 := n16439 _v _q h2303
  have p17138 := n17138 _v _q h4306
  have p4996 := n4996 _v _q h3937
  have p16269 := n16269 _v _q h7749
  have p4991 := n4991 _v _q h4608
  change (e2475 _v) ∨ (¬ (e4285 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e7749 _v)) ∨ (¬ (e4608 _v)) at p22481
  rcases p22481 with hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p16436))
  · exact (False.elim (hlit p16439))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p4996))
  · exact (False.elim (hlit p16269))
  · exact (False.elim (hlit p4991))
theorem n22489 (_v : Vars) (_q : Query _v) (h6501 : (e6501 _v)) (h6676 : (e6676 _v)) : (e2787 _v) := by
  have p15228 := n15228 _v _q 
  have p22483 := n22483 _v _q h6501 h6676
  change (e2787 _v) ∨ (¬ (e7944 _v)) at p15228
  rcases p15228 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p22483))
theorem n22490 (_v : Vars) (_q : Query _v) (h6501 : (e6501 _v)) (h6676 : (e6676 _v)) : (e7927 _v) := by
  have p14855 := n14855 _v _q 
  have p22489 := n22489 _v _q h6501 h6676
  change (¬ (e2787 _v)) ∨ (¬ (e7921 _v)) at p14855
  rcases p14855 with hlit | hlit
  · exact (False.elim (hlit p22489))
  · exact hlit
theorem n22491 (_v : Vars) (_q : Query _v) (h6501 : (e6501 _v)) (h6676 : (e6676 _v)) : (e4139 _v) := by
  have p16281 := n16281 _v _q 
  have p22485 := n22485 _v _q h6501 h6676
  change (e7634 _v) ∨ (e4139 _v) at p16281
  change (¬ (e7634 _v)) at p22485
  rcases p16281 with hlit | hlit
  · exact (False.elim (p22485 hlit))
  · exact hlit
theorem n22492 (_v : Vars) (_q : Query _v) (h3937 : (e3937 _v)) (h4139 : (e4139 _v)) (h4285 : (e4285 _v)) (h4306 : (e4306 _v)) (h4608 : (e4608 _v)) (h7749 : (e7749 _v)) : (e4546 _v) := by
  have p16307 := n16307 _v _q 
  have p22487 := n22487 _v _q h3937 h4139 h4285 h4306 h4608 h7749
  change (e8029 _v) ∨ (e4546 _v) at p16307
  change (¬ (e8029 _v)) at p22487
  rcases p16307 with hlit | hlit
  · exact (False.elim (p22487 hlit))
  · exact hlit
theorem n22493 (_v : Vars) (_q : Query _v) (h2303 : (e2303 _v)) (h3937 : (e3937 _v)) (h4306 : (e4306 _v)) (h4608 : (e4608 _v)) (h7749 : (e7749 _v)) : (e8035 _v) := by
  have p14871 := n14871 _v _q 
  have p22488 := n22488 _v _q h2303 h3937 h4306 h4608 h7749
  change (¬ (e2475 _v)) ∨ (¬ (e8029 _v)) at p14871
  rcases p14871 with hlit | hlit
  · exact (False.elim (hlit p22488))
  · exact hlit
theorem n22494 (_v : Vars) (_q : Query _v) (h2303 : (e2303 _v)) (h3937 : (e3937 _v)) (h4306 : (e4306 _v)) (h4608 : (e4608 _v)) (h7749 : (e7749 _v)) : (e4546 _v) := by
  have p16307 := n16307 _v _q 
  have p22493 := n22493 _v _q h2303 h3937 h4306 h4608 h7749
  change (e8029 _v) ∨ (e4546 _v) at p16307
  change (¬ (e8029 _v)) at p22493
  rcases p16307 with hlit | hlit
  · exact (False.elim (p22493 hlit))
  · exact hlit
theorem n22495 (_v : Vars) (_q : Query _v) (h2303 : (e2303 _v)) (h3937 : (e3937 _v)) (h4306 : (e4306 _v)) (h4608 : (e4608 _v)) (h7749 : (e7749 _v)) : (e2787 _v) := by
  have p8461 := n8461 _v _q 
  have p22488 := n22488 _v _q h2303 h3937 h4306 h4608 h7749
  have p8448 := n8448 _v _q h2303
  change (¬ (e2475 _v)) ∨ (¬ (e2303 _v)) ∨ (e2787 _v) at p8461
  rcases p8461 with hlit | hlit | hlit
  · exact (False.elim (hlit p22488))
  · exact (False.elim (hlit p8448))
  · exact hlit
theorem n22496 (_v : Vars) (_q : Query _v) (h2303 : (e2303 _v)) (h3937 : (e3937 _v)) (h4306 : (e4306 _v)) (h4608 : (e4608 _v)) (h7749 : (e7749 _v)) : (e7927 _v) := by
  have p14855 := n14855 _v _q 
  have p22495 := n22495 _v _q h2303 h3937 h4306 h4608 h7749
  change (¬ (e2787 _v)) ∨ (¬ (e7921 _v)) at p14855
  rcases p14855 with hlit | hlit
  · exact (False.elim (hlit p22495))
  · exact hlit
theorem n22497 (_v : Vars) (_q : Query _v) (h2303 : (e2303 _v)) (h3937 : (e3937 _v)) (h4306 : (e4306 _v)) (h4608 : (e4608 _v)) (h7749 : (e7749 _v)) : (e4419 _v) := by
  have p16347 := n16347 _v _q 
  have p22496 := n22496 _v _q h2303 h3937 h4306 h4608 h7749
  change (e7921 _v) ∨ (e4419 _v) at p16347
  change (¬ (e7921 _v)) at p22496
  rcases p16347 with hlit | hlit
  · exact (False.elim (p22496 hlit))
  · exact hlit
theorem n22498 (_v : Vars) (_q : Query _v) (h6501 : (e6501 _v)) (h6676 : (e6676 _v)) : (e4419 _v) := by
  have p16347 := n16347 _v _q 
  have p22490 := n22490 _v _q h6501 h6676
  change (e7921 _v) ∨ (e4419 _v) at p16347
  change (¬ (e7921 _v)) at p22490
  rcases p16347 with hlit | hlit
  · exact (False.elim (p22490 hlit))
  · exact hlit
theorem n22499 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h2787 : (e2787 _v)) (h3937 : (e3937 _v)) (h4139 : (e4139 _v)) (h4285 : (e4285 _v)) (h4306 : (e4306 _v)) (h4608 : (e4608 _v)) (h7749 : (e7749 _v)) : (e7489 _v) := by
  have p16911 := n16911 _v _q 
  have p10893 := n10893 _v _q 
  have p17083 := n17083 _v _q 
  have p17098 := n17098 _v _q 
  have p22302 := n22302 _v _q 
  have p17106 := n17106 _v _q 
  have p16913 := n16913 _v _q 
  have p11430 := n11430 _v _q h2787
  have p22492 := n22492 _v _q h3937 h4139 h4285 h4306 h4608 h7749
  have p5000 := n5000 _v _q h30
  have p17093 := n17093 _v _q 
  have p16349 := n16349 _v _q h2787
  have p22436 := n22436 _v _q h3937 h4306 h4608 h7749
  have p13951 := n13951 _v _q 
  have p4977 := n4977 _v _q h4285
  have p4979 := n4979 _v _q h4139
  have p17100 := n17100 _v _q 
  have p22322 := n22322 _v _q 
  have p17091 := n17091 _v _q 
  have p17102 := n17102 _v _q 
  have p17138 := n17138 _v _q h4306
  have p17141 := n17141 _v _q 
  have p22416 := n22416 _v _q h3937 h4608
  have p4996 := n4996 _v _q h3937
  have p17147 := n17147 _v _q 
  have p16269 := n16269 _v _q h7749
  have p22407 := n22407 _v _q 
  have p17124 := n17124 _v _q 
  have p22341 := n22341 _v _q 
  have p22324 := n22324 _v _q 
  have p19610 := n19610 _v _q 
  have p17020 := n17020 _v _q 
  have p4991 := n4991 _v _q h4608
  have p16576 := n16576 _v _q 
  have p22368 := n22368 _v _q 
  have p22323 := n22323 _v _q 
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
  have p10896 := n10896 _v _q 
  exact FloorCertificate.node_22499 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e61 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2863 _v) (e2877 _v) (e2883 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p16911 p10893 p17083 p17098 p22302 p17106 p16913 p11430 p22492 p5000 p17093 p16349 p22436 p13951 p4977 p4979 p17100 p22322 p17091 p17102 p17138 p17141 p22416 p4996 p17147 p16269 p22407 p17124 p22341 p22324 p19610 p17020 p4991 p16576 p22368 p22323 p17758 p22320 p17115 p17078 p17117 p17113 p20467 p17133 p17120 p17009 p22321 p17089 p22318 p22347 p17104 p20470 p20274 p19665 p16778 p17127 p17050 p17122 p17096 p20126 p20426 p17110 p20829 p20653 p17111 p17131 p17108 p17294 p16943 p17064 p17067 p17080 p17053 p17072 p17074 p17069 p20096 p20836 p20461 p17874 p17136 p17087 p17055 p17058 p10896
theorem n22500 (_v : Vars) (_q : Query _v) (h6501 : (e6501 _v)) (h6676 : (e6676 _v)) : (e7493 _v) := by
  have p15195 := n15195 _v _q 
  have p22462 := n22462 _v _q h6501 h6676
  change (e7497 _v) ∨ (e7493 _v) at p15195
  change (¬ (e7497 _v)) at p22462
  rcases p15195 with hlit | hlit
  · exact (False.elim (p22462 hlit))
  · exact hlit
theorem n22501 (_v : Vars) (_q : Query _v) (h6501 : (e6501 _v)) (h6676 : (e6676 _v)) : (e7489 _v) := by
  have p16977 := n16977 _v _q 
  have p22457 := n22457 _v _q h6501 h6676
  have p17091 := n17091 _v _q 
  have p17141 := n17141 _v _q 
  have p22459 := n22459 _v _q h6501 h6676
  have p10893 := n10893 _v _q 
  have p22500 := n22500 _v _q h6501 h6676
  have p17102 := n17102 _v _q 
  have p16994 := n16994 _v _q 
  have p15342 := n15342 _v _q h6676
  have p10943 := n10943 _v _q h6676
  have p22366 := n22366 _v _q 
  have p22380 := n22380 _v _q h6676
  have p22357 := n22357 _v _q h6676
  have p22417 := n22417 _v _q h6501
  have p16325 := n16325 _v _q h6501
  have p17147 := n17147 _v _q 
  have p22450 := n22450 _v _q h6501 h6676
  have p22407 := n22407 _v _q 
  have p17124 := n17124 _v _q 
  have p22341 := n22341 _v _q 
  have p22324 := n22324 _v _q 
  have p19610 := n19610 _v _q 
  have p13951 := n13951 _v _q 
  have p15641 := n15641 _v _q h6501
  have p16576 := n16576 _v _q 
  have p22368 := n22368 _v _q 
  have p22323 := n22323 _v _q 
  have p22498 := n22498 _v _q h6501 h6676
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
  have p22455 := n22455 _v _q h6501 h6676
  have p22491 := n22491 _v _q h6501 h6676
  have p22329 := n22329 _v _q 
  exact FloorCertificate.node_22501 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e61 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2863 _v) (e2877 _v) (e2883 _v) (e2898 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p16977 p22457 p17091 p17141 p22459 p10893 p22500 p17102 p16994 p15342 p10943 p22366 p22380 p22357 p22417 p16325 p17147 p22450 p22407 p17124 p22341 p22324 p19610 p13951 p15641 p16576 p22368 p22323 p22498 p22302 p17758 p22320 p17115 p17078 p17117 p17113 p20467 p17133 p17120 p17009 p22321 p17089 p22318 p22347 p17104 p20470 p20274 p19665 p16778 p17127 p17050 p17122 p17096 p20126 p20426 p17110 p20829 p20653 p17111 p17131 p17108 p17294 p16943 p17064 p17067 p17080 p17053 p17072 p17074 p17069 p20096 p20836 p20461 p17874 p17136 p17087 p17055 p17058 p17098 p17083 p17106 p17020 p17093 p22322 p17100 p22455 p22491 p22329
theorem n22503 (_v : Vars) (_q : Query _v)  : (e22502 _v) := by
  by_contra hc
  change ¬ ((¬ (e30 _v)) ∨ (¬ (e2787 _v)) ∨ (¬ (e4285 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e7749 _v)) ∨ (¬ (e4608 _v))) at hc
  have h30 : (e30 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h2787 : (e2787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h4139 : (e4139 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4285 : (e4285 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4608 : (e4608 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))))
  have h7749 : (e7749 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have p22499 := n22499 _v _q h30 h2787 h3937 h4139 h4285 h4306 h4608 h7749
  exact p22499
theorem n22505 (_v : Vars) (_q : Query _v)  : (e22504 _v) := by
  by_contra hc
  change ¬ ((e2585 _v) ∨ (e2179 _v)) at hc
  have h6501 : (e6501 _v) := (fun hn => hc (Or.inr hn))
  have h6676 : (e6676 _v) := (fun hn => hc (Or.inl hn))
  have p22501 := n22501 _v _q h6501 h6676
  exact p22501
theorem n22506 (_v : Vars) (_q : Query _v) (h6501 : (e6501 _v)) : (e2585 _v) := by
  have p22505 := n22505 _v _q 
  have p8554 := n8554 _v _q h6501
  change (e2585 _v) ∨ (e2179 _v) at p22505
  change (¬ (e2179 _v)) at p8554
  rcases p22505 with hlit | hlit
  · exact hlit
  · exact (False.elim (p8554 hlit))
theorem n22507 (_v : Vars) (_q : Query _v) (h6501 : (e6501 _v)) : (e4314 _v) := by
  have p14704 := n14704 _v _q 
  have p22506 := n22506 _v _q h6501
  change (¬ (e2585 _v)) ∨ (¬ (e4313 _v)) at p14704
  rcases p14704 with hlit | hlit
  · exact (False.elim (hlit p22506))
  · exact hlit
theorem n22508 (_v : Vars) (_q : Query _v) (h2303 : (e2303 _v)) (h3937 : (e3937 _v)) (h4306 : (e4306 _v)) (h4608 : (e4608 _v)) (h7749 : (e7749 _v)) : (e35 _v) := by
  have p22503 := n22503 _v _q 
  have p22495 := n22495 _v _q h2303 h3937 h4306 h4608 h7749
  have p16436 := n16436 _v _q h2303
  have p16439 := n16439 _v _q h2303
  have p17138 := n17138 _v _q h4306
  have p4996 := n4996 _v _q h3937
  have p16269 := n16269 _v _q h7749
  have p4991 := n4991 _v _q h4608
  change (¬ (e30 _v)) ∨ (¬ (e2787 _v)) ∨ (¬ (e4285 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e7749 _v)) ∨ (¬ (e4608 _v)) at p22503
  rcases p22503 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p22495))
  · exact (False.elim (hlit p16436))
  · exact (False.elim (hlit p16439))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p4996))
  · exact (False.elim (hlit p16269))
  · exact (False.elim (hlit p4991))
theorem n22509 (_v : Vars) (_q : Query _v) (h2303 : (e2303 _v)) (h3937 : (e3937 _v)) (h4306 : (e4306 _v)) (h4608 : (e4608 _v)) (h7749 : (e7749 _v)) : (e5089 _v) := by
  have p16290 := n16290 _v _q 
  have p22508 := n22508 _v _q h2303 h3937 h4306 h4608 h7749
  change (e5089 _v) ∨ (e30 _v) at p16290
  change (¬ (e30 _v)) at p22508
  rcases p16290 with hlit | hlit
  · exact hlit
  · exact (False.elim (p22508 hlit))
theorem n22510 (_v : Vars) (_q : Query _v) (h6501 : (e6501 _v)) : (e4306 _v) := by
  have p14984 := n14984 _v _q 
  have p22507 := n22507 _v _q h6501
  change (e4313 _v) ∨ (e4306 _v) at p14984
  change (¬ (e4313 _v)) at p22507
  rcases p14984 with hlit | hlit
  · exact (False.elim (p22507 hlit))
  · exact hlit
theorem n22511 (_v : Vars) (_q : Query _v) (h6501 : (e6501 _v)) : (e2529 _v) := by
  have p22425 := n22425 _v _q 
  have p22510 := n22510 _v _q h6501
  have p16325 := n16325 _v _q h6501
  have p22441 := n22441 _v _q h6501
  have p15641 := n15641 _v _q h6501
  change (e2529 _v) ∨ (¬ (e4306 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e7749 _v)) ∨ (¬ (e4608 _v)) at p22425
  rcases p22425 with hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p22510))
  · exact (False.elim (hlit p16325))
  · exact (False.elim (hlit p22441))
  · exact (False.elim (hlit p15641))
theorem n22512 (_v : Vars) (_q : Query _v) (h6501 : (e6501 _v)) : (e8307 _v) := by
  have p14906 := n14906 _v _q 
  have p22511 := n22511 _v _q h6501
  change (¬ (e2529 _v)) ∨ (¬ (e8301 _v)) at p14906
  rcases p14906 with hlit | hlit
  · exact (False.elim (hlit p22511))
  · exact hlit
theorem n22513 (_v : Vars) (_q : Query _v) (h2303 : (e2303 _v)) (h3937 : (e3937 _v)) (h4306 : (e4306 _v)) (h4608 : (e4608 _v)) (h7749 : (e7749 _v)) : (e5093 _v) := by
  have p14728 := n14728 _v _q 
  have p22509 := n22509 _v _q h2303 h3937 h4306 h4608 h7749
  change (¬ (e13 _v)) ∨ (¬ (e5089 _v)) at p14728
  rcases p14728 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p22509))
theorem n22514 (_v : Vars) (_q : Query _v) (h2303 : (e2303 _v)) (h3937 : (e3937 _v)) (h4306 : (e4306 _v)) (h4608 : (e4608 _v)) (h7749 : (e7749 _v)) : (e5105 _v) := by
  have p15204 := n15204 _v _q 
  have p22513 := n22513 _v _q h2303 h3937 h4306 h4608 h7749
  change (e13 _v) ∨ (¬ (e5104 _v)) at p15204
  change (¬ (e13 _v)) at p22513
  rcases p15204 with hlit | hlit
  · exact (False.elim (p22513 hlit))
  · exact hlit
theorem n22515 (_v : Vars) (_q : Query _v) (h2303 : (e2303 _v)) (h3937 : (e3937 _v)) (h4306 : (e4306 _v)) (h4608 : (e4608 _v)) (h7749 : (e7749 _v)) : (e5100 _v) := by
  have p15319 := n15319 _v _q 
  have p22514 := n22514 _v _q h2303 h3937 h4306 h4608 h7749
  change (e5104 _v) ∨ (e5100 _v) at p15319
  change (¬ (e5104 _v)) at p22514
  rcases p15319 with hlit | hlit
  · exact (False.elim (p22514 hlit))
  · exact hlit
theorem n22516 (_v : Vars) (_q : Query _v) (h6501 : (e6501 _v)) : (e4838 _v) := by
  have p16285 := n16285 _v _q 
  have p22512 := n22512 _v _q h6501
  change (e8301 _v) ∨ (e4838 _v) at p16285
  change (¬ (e8301 _v)) at p22512
  rcases p16285 with hlit | hlit
  · exact (False.elim (p22512 hlit))
  · exact hlit
theorem n22517 (_v : Vars) (_q : Query _v) (h2303 : (e2303 _v)) (h3937 : (e3937 _v)) (h4306 : (e4306 _v)) (h4608 : (e4608 _v)) (h7749 : (e7749 _v)) : (e7489 _v) := by
  have p22513 := n22513 _v _q h2303 h3937 h4306 h4608 h7749
  have p22515 := n22515 _v _q h2303 h3937 h4306 h4608 h7749
  have p16911 := n16911 _v _q 
  have p10893 := n10893 _v _q 
  have p17083 := n17083 _v _q 
  have p17098 := n17098 _v _q 
  have p22302 := n22302 _v _q 
  have p17106 := n17106 _v _q 
  have p16913 := n16913 _v _q 
  have p22495 := n22495 _v _q h2303 h3937 h4306 h4608 h7749
  have p22494 := n22494 _v _q h2303 h3937 h4306 h4608 h7749
  have p17093 := n17093 _v _q 
  have p22497 := n22497 _v _q h2303 h3937 h4306 h4608 h7749
  have p22436 := n22436 _v _q h3937 h4306 h4608 h7749
  have p13951 := n13951 _v _q 
  have p16436 := n16436 _v _q h2303
  have p16439 := n16439 _v _q h2303
  have p17100 := n17100 _v _q 
  have p22322 := n22322 _v _q 
  have p17091 := n17091 _v _q 
  have p17102 := n17102 _v _q 
  have p17138 := n17138 _v _q h4306
  have p17141 := n17141 _v _q 
  have p22416 := n22416 _v _q h3937 h4608
  have p4996 := n4996 _v _q h3937
  have p17147 := n17147 _v _q 
  have p16269 := n16269 _v _q h7749
  have p22407 := n22407 _v _q 
  have p17124 := n17124 _v _q 
  have p22341 := n22341 _v _q 
  have p22324 := n22324 _v _q 
  have p19610 := n19610 _v _q 
  have p17020 := n17020 _v _q 
  have p4991 := n4991 _v _q h4608
  have p16576 := n16576 _v _q 
  have p22368 := n22368 _v _q 
  have p22323 := n22323 _v _q 
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
  have p22488 := n22488 _v _q h2303 h3937 h4306 h4608 h7749
  exact FloorCertificate.node_22517 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e61 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2863 _v) (e2877 _v) (e2883 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p22513 p22515 p16911 p10893 p17083 p17098 p22302 p17106 p16913 p22495 p22494 p17093 p22497 p22436 p13951 p16436 p16439 p17100 p22322 p17091 p17102 p17138 p17141 p22416 p4996 p17147 p16269 p22407 p17124 p22341 p22324 p19610 p17020 p4991 p16576 p22368 p22323 p17758 p22320 p17115 p17078 p17117 p17113 p20467 p17133 p17120 p17009 p22321 p17089 p22318 p22347 p17104 p20470 p20274 p19665 p16778 p17127 p17050 p17122 p17096 p20126 p20426 p17110 p20829 p20653 p17111 p17131 p17108 p17294 p16943 p17064 p17067 p17080 p17053 p17072 p17074 p17069 p20096 p20836 p20461 p17874 p17136 p17087 p17055 p17058 p22488
theorem n22519 (_v : Vars) (_q : Query _v)  : (e22518 _v) := by
  by_contra hc
  change ¬ ((¬ (e2303 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e7749 _v)) ∨ (¬ (e4608 _v))) at hc
  have h2303 : (e2303 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h4608 : (e4608 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr hn)))))
  have h7749 : (e7749 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have p22517 := n22517 _v _q h2303 h3937 h4306 h4608 h7749
  exact p22517
theorem n22520 (_v : Vars) (_q : Query _v) (h6501 : (e6501 _v)) : (e7807 _v) := by
  have p22519 := n22519 _v _q 
  have p22510 := n22510 _v _q h6501
  have p16325 := n16325 _v _q h6501
  have p22441 := n22441 _v _q h6501
  have p15641 := n15641 _v _q h6501
  change (¬ (e2303 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e7749 _v)) ∨ (¬ (e4608 _v)) at p22519
  rcases p22519 with hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p22510))
  · exact (False.elim (hlit p16325))
  · exact (False.elim (hlit p22441))
  · exact (False.elim (hlit p15641))
theorem n22521 (_v : Vars) (_q : Query _v) (h3937 : (e3937 _v)) (h4306 : (e4306 _v)) (h4608 : (e4608 _v)) (h7749 : (e7749 _v)) : (e7807 _v) := by
  have p22519 := n22519 _v _q 
  have p17138 := n17138 _v _q h4306
  have p4996 := n4996 _v _q h3937
  have p16269 := n16269 _v _q h7749
  have p4991 := n4991 _v _q h4608
  change (¬ (e2303 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e7749 _v)) ∨ (¬ (e4608 _v)) at p22519
  rcases p22519 with hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p4996))
  · exact (False.elim (hlit p16269))
  · exact (False.elim (hlit p4991))
theorem n22522 (_v : Vars) (_q : Query _v) (h6501 : (e6501 _v)) : (e6746 _v) := by
  have p11429 := n11429 _v _q 
  have p22520 := n22520 _v _q h6501
  change (¬ (e2740 _v)) ∨ (e2303 _v) at p11429
  change (¬ (e2303 _v)) at p22520
  rcases p11429 with hlit | hlit
  · exact hlit
  · exact (False.elim (p22520 hlit))
theorem n22523 (_v : Vars) (_q : Query _v) (h6501 : (e6501 _v)) : (e6724 _v) := by
  have p11461 := n11461 _v _q 
  have p22522 := n22522 _v _q h6501
  change (¬ (e2691 _v)) ∨ (e2740 _v) at p11461
  change (¬ (e2740 _v)) at p22522
  rcases p11461 with hlit | hlit
  · exact hlit
  · exact (False.elim (p22522 hlit))
theorem n22524 (_v : Vars) (_q : Query _v) (h6501 : (e6501 _v)) : (e7517 _v) := by
  have p15196 := n15196 _v _q 
  have p22523 := n22523 _v _q h6501
  change (e2691 _v) ∨ (¬ (e7497 _v)) at p15196
  change (¬ (e2691 _v)) at p22523
  rcases p15196 with hlit | hlit
  · exact (False.elim (p22523 hlit))
  · exact hlit
theorem n22525 (_v : Vars) (_q : Query _v) (h3937 : (e3937 _v)) (h4306 : (e4306 _v)) (h4608 : (e4608 _v)) (h7749 : (e7749 _v)) : (e6746 _v) := by
  have p11429 := n11429 _v _q 
  have p22521 := n22521 _v _q h3937 h4306 h4608 h7749
  change (¬ (e2740 _v)) ∨ (e2303 _v) at p11429
  change (¬ (e2303 _v)) at p22521
  rcases p11429 with hlit | hlit
  · exact hlit
  · exact (False.elim (p22521 hlit))
theorem n22526 (_v : Vars) (_q : Query _v) (h3937 : (e3937 _v)) (h4306 : (e4306 _v)) (h4608 : (e4608 _v)) (h7749 : (e7749 _v)) : (e6724 _v) := by
  have p11461 := n11461 _v _q 
  have p22525 := n22525 _v _q h3937 h4306 h4608 h7749
  change (¬ (e2691 _v)) ∨ (e2740 _v) at p11461
  change (¬ (e2740 _v)) at p22525
  rcases p11461 with hlit | hlit
  · exact hlit
  · exact (False.elim (p22525 hlit))
theorem n22527 (_v : Vars) (_q : Query _v) (h3937 : (e3937 _v)) (h4306 : (e4306 _v)) (h4608 : (e4608 _v)) (h7749 : (e7749 _v)) : (e7517 _v) := by
  have p15196 := n15196 _v _q 
  have p22526 := n22526 _v _q h3937 h4306 h4608 h7749
  change (e2691 _v) ∨ (¬ (e7497 _v)) at p15196
  change (¬ (e2691 _v)) at p22526
  rcases p15196 with hlit | hlit
  · exact (False.elim (p22526 hlit))
  · exact hlit
theorem n22528 (_v : Vars) (_q : Query _v) (h3937 : (e3937 _v)) (h4306 : (e4306 _v)) (h4608 : (e4608 _v)) (h7749 : (e7749 _v)) (h8038 : (e8038 _v)) : (e4420 _v) := by
  have p16832 := n16832 _v _q 
  have p8602 := n8602 _v _q h8038
  have p22521 := n22521 _v _q h3937 h4306 h4608 h7749
  change (e2303 _v) ∨ (¬ (e4419 _v)) ∨ (e2475 _v) at p16832
  change (¬ (e2475 _v)) at p8602
  change (¬ (e2303 _v)) at p22521
  rcases p16832 with hlit | hlit | hlit
  · exact (False.elim (p22521 hlit))
  · exact hlit
  · exact (False.elim (p8602 hlit))
theorem n22529 (_v : Vars) (_q : Query _v) (h3937 : (e3937 _v)) (h4306 : (e4306 _v)) (h4608 : (e4608 _v)) (h7749 : (e7749 _v)) (h8038 : (e8038 _v)) : (e7921 _v) := by
  have p16347 := n16347 _v _q 
  have p22528 := n22528 _v _q h3937 h4306 h4608 h7749 h8038
  change (e7921 _v) ∨ (e4419 _v) at p16347
  change (¬ (e4419 _v)) at p22528
  rcases p16347 with hlit | hlit
  · exact hlit
  · exact (False.elim (p22528 hlit))
theorem n22530 (_v : Vars) (_q : Query _v) (h3937 : (e3937 _v)) (h4306 : (e4306 _v)) (h4608 : (e4608 _v)) (h7749 : (e7749 _v)) : (e5093 _v) := by
  have p11468 := n11468 _v _q 
  have p22521 := n22521 _v _q h3937 h4306 h4608 h7749
  change (¬ (e13 _v)) ∨ (e2303 _v) at p11468
  change (¬ (e2303 _v)) at p22521
  rcases p11468 with hlit | hlit
  · exact hlit
  · exact (False.elim (p22521 hlit))
theorem n22531 (_v : Vars) (_q : Query _v) (h3937 : (e3937 _v)) (h4306 : (e4306 _v)) (h4608 : (e4608 _v)) (h7749 : (e7749 _v)) : (e5105 _v) := by
  have p15204 := n15204 _v _q 
  have p22530 := n22530 _v _q h3937 h4306 h4608 h7749
  change (e13 _v) ∨ (¬ (e5104 _v)) at p15204
  change (¬ (e13 _v)) at p22530
  rcases p15204 with hlit | hlit
  · exact (False.elim (p22530 hlit))
  · exact hlit
theorem n22532 (_v : Vars) (_q : Query _v) (h3937 : (e3937 _v)) (h4306 : (e4306 _v)) (h4608 : (e4608 _v)) (h7749 : (e7749 _v)) : (e5100 _v) := by
  have p15319 := n15319 _v _q 
  have p22531 := n22531 _v _q h3937 h4306 h4608 h7749
  change (e5104 _v) ∨ (e5100 _v) at p15319
  change (¬ (e5104 _v)) at p22531
  rcases p15319 with hlit | hlit
  · exact (False.elim (p22531 hlit))
  · exact hlit
theorem n22533 (_v : Vars) (_q : Query _v) (h3937 : (e3937 _v)) (h4306 : (e4306 _v)) (h4608 : (e4608 _v)) (h7749 : (e7749 _v)) : (e7819 _v) := by
  have p14994 := n14994 _v _q 
  have p22521 := n22521 _v _q h3937 h4306 h4608 h7749
  change (e2303 _v) ∨ (¬ (e7818 _v)) at p14994
  change (¬ (e2303 _v)) at p22521
  rcases p14994 with hlit | hlit
  · exact (False.elim (p22521 hlit))
  · exact hlit
theorem n22534 (_v : Vars) (_q : Query _v) (h3937 : (e3937 _v)) (h4306 : (e4306 _v)) (h4608 : (e4608 _v)) (h7749 : (e7749 _v)) : (e7814 _v) := by
  have p15221 := n15221 _v _q 
  have p22533 := n22533 _v _q h3937 h4306 h4608 h7749
  change (e7818 _v) ∨ (e7814 _v) at p15221
  change (¬ (e7818 _v)) at p22533
  rcases p15221 with hlit | hlit
  · exact (False.elim (p22533 hlit))
  · exact hlit
end
end Assembly
