import Dag231
import generated.th_lemma_30
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n20468 (_v : Vars) (_q : Query _v)  : (e2254 _v) := by
  have p11455 := n11455 _v _q 
  have p20465 := n20465 _v _q 
  change (¬ (e2482 _v)) ∨ (e2254 _v) at p11455
  rcases p11455 with hlit | hlit
  · exact (False.elim (hlit p20465))
  · exact hlit
theorem n20469 (_v : Vars) (_q : Query _v)  : (e4731 _v) := by
  have p14698 := n14698 _v _q 
  have p20468 := n20468 _v _q 
  change (¬ (e2254 _v)) ∨ (¬ (e4730 _v)) at p14698
  rcases p14698 with hlit | hlit
  · exact (False.elim (hlit p20468))
  · exact hlit
theorem n20470 (_v : Vars) (_q : Query _v)  : (e4724 _v) := by
  have p15518 := n15518 _v _q 
  have p20469 := n20469 _v _q 
  change (e4730 _v) ∨ (e4724 _v) at p15518
  change (¬ (e4730 _v)) at p20469
  rcases p15518 with hlit | hlit
  · exact (False.elim (p20469 hlit))
  · exact hlit
theorem n20471 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e3158 _v) := by
  have p15126 := n15126 _v _q 
  have p20439 := n20439 _v _q h251
  change (e3162 _v) ∨ (e3158 _v) at p15126
  change (¬ (e3162 _v)) at p20439
  rcases p15126 with hlit | hlit
  · exact (False.elim (p20439 hlit))
  · exact hlit
theorem n20472 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e4439 _v) := by
  have p14925 := n14925 _v _q 
  have p20441 := n20441 _v _q h251
  change (e4446 _v) ∨ (e4439 _v) at p14925
  change (¬ (e4446 _v)) at p20441
  rcases p14925 with hlit | hlit
  · exact (False.elim (p20441 hlit))
  · exact hlit
theorem n20473 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e3919 _v) := by
  have p14797 := n14797 _v _q 
  have p20443 := n20443 _v _q h251
  change (e3923 _v) ∨ (e3919 _v) at p14797
  change (¬ (e3923 _v)) at p20443
  rcases p14797 with hlit | hlit
  · exact (False.elim (p20443 hlit))
  · exact hlit
theorem n20474 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e4101 _v) := by
  have p14929 := n14929 _v _q 
  have p20445 := n20445 _v _q h251
  change (e4108 _v) ∨ (e4101 _v) at p14929
  change (¬ (e4108 _v)) at p20445
  rcases p14929 with hlit | hlit
  · exact (False.elim (p20445 hlit))
  · exact hlit
theorem n20475 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e4567 _v) := by
  have p8485 := n8485 _v _q 
  have p20447 := n20447 _v _q h251
  change (e4574 _v) ∨ (e4567 _v) at p8485
  change (¬ (e4574 _v)) at p20447
  rcases p8485 with hlit | hlit
  · exact (False.elim (p20447 hlit))
  · exact hlit
theorem n20476 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e4306 _v) := by
  have p14984 := n14984 _v _q 
  have p20450 := n20450 _v _q h251
  change (e4313 _v) ∨ (e4306 _v) at p14984
  change (¬ (e4313 _v)) at p20450
  rcases p14984 with hlit | hlit
  · exact (False.elim (p20450 hlit))
  · exact hlit
theorem n20477 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e51 _v) := by
  have p14962 := n14962 _v _q 
  have p20452 := n20452 _v _q h251
  change (e59 _v) ∨ (e51 _v) at p14962
  change (¬ (e59 _v)) at p20452
  rcases p14962 with hlit | hlit
  · exact (False.elim (p20452 hlit))
  · exact hlit
theorem n20478 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e4653 _v) := by
  have p15168 := n15168 _v _q 
  have p20454 := n20454 _v _q h251
  change (e4660 _v) ∨ (e4653 _v) at p15168
  change (¬ (e4660 _v)) at p20454
  rcases p15168 with hlit | hlit
  · exact (False.elim (p20454 hlit))
  · exact hlit
theorem n20479 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) (h474 : (e474 _v)) (h4199 : (e4199 _v)) : (e7489 _v) := by
  have p5257 := n5257 _v _q 
  have p258 := n258 _v _q 
  have p16992 := n16992 _v _q 
  have p20437 := n20437 _v _q 
  have p20471 := n20471 _v _q h251
  have p15131 := n15131 _v _q h474
  have p17122 := n17122 _v _q 
  have p17096 := n17096 _v _q 
  have p15815 := n15815 _v _q h251
  have p20472 := n20472 _v _q h251
  have p11374 := n11374 _v _q h251
  have p20473 := n20473 _v _q h251
  have p15818 := n15818 _v _q h251
  have p20474 := n20474 _v _q h251
  have p15821 := n15821 _v _q h251
  have p20475 := n20475 _v _q h251
  have p17115 := n17115 _v _q 
  have p15129 := n15129 _v _q h474
  have p17120 := n17120 _v _q 
  have p17111 := n17111 _v _q 
  have p17124 := n17124 _v _q 
  have p17050 := n17050 _v _q 
  have p16778 := n16778 _v _q 
  have p17113 := n17113 _v _q 
  have p17117 := n17117 _v _q 
  have p20467 := n20467 _v _q 
  have p15841 := n15841 _v _q h251
  have p11414 := n11414 _v _q h474
  have p15844 := n15844 _v _q h251
  have p17104 := n17104 _v _q 
  have p17874 := n17874 _v _q 
  have p17127 := n17127 _v _q 
  have p20476 := n20476 _v _q h251
  have p20274 := n20274 _v _q 
  have p15133 := n15133 _v _q h474
  have p15119 := n15119 _v _q h251
  have p20470 := n20470 _v _q 
  have p17133 := n17133 _v _q 
  have p17089 := n17089 _v _q 
  have p19665 := n19665 _v _q 
  have p20426 := n20426 _v _q 
  have p17055 := n17055 _v _q 
  have p17108 := n17108 _v _q 
  have p20461 := n20461 _v _q 
  have p20126 := n20126 _v _q 
  have p17131 := n17131 _v _q 
  have p17110 := n17110 _v _q 
  have p17053 := n17053 _v _q 
  have p20477 := n20477 _v _q h251
  have p20096 := n20096 _v _q 
  have p17294 := n17294 _v _q 
  have p5003 := n5003 _v _q h4199
  have p17058 := n17058 _v _q 
  have p17064 := n17064 _v _q 
  have p17067 := n17067 _v _q 
  have p17069 := n17069 _v _q 
  have p17072 := n17072 _v _q 
  have p17136 := n17136 _v _q 
  have p13951 := n13951 _v _q 
  have p17078 := n17078 _v _q 
  have p17080 := n17080 _v _q 
  have p17083 := n17083 _v _q 
  have p17074 := n17074 _v _q 
  have p17087 := n17087 _v _q 
  have p17758 := n17758 _v _q 
  have p17091 := n17091 _v _q 
  have p17093 := n17093 _v _q 
  have p20478 := n20478 _v _q h251
  have p17141 := n17141 _v _q 
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p17100 := n17100 _v _q 
  have p17102 := n17102 _v _q 
  have p19610 := n19610 _v _q 
  have p15847 := n15847 _v _q h251
  exact FloorCertificate.node_20479 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e101 _v) (e110 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2902 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) p5257 p258 p16992 p20437 p20471 p15131 p17122 p17096 p15815 p20472 p11374 p20473 p15818 p20474 p15821 p20475 p17115 p15129 p17120 p17111 p17124 p17050 p16778 p17113 p17117 p20467 p15841 p11414 p15844 p17104 p17874 p17127 p20476 p20274 p15133 p15119 p20470 p17133 p17089 p19665 p20426 p17055 p17108 p20461 p20126 p17131 p17110 p17053 p20477 p20096 p17294 p5003 p17058 p17064 p17067 p17069 p17072 p17136 p13951 p17078 p17080 p17083 p17074 p17087 p17758 p17091 p17093 p20478 p17141 p17098 p17106 p17100 p17102 p19610 p15847
theorem n20481 (_v : Vars) (_q : Query _v)  : (e20480 _v) := by
  by_contra hc
  change ¬ ((¬ (e4199 _v)) ∨ (¬ (e251 _v)) ∨ (¬ (e474 _v))) at hc
  have h251 : (e251 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h474 : (e474 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr hn)))
  have h4199 : (e4199 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have p20479 := n20479 _v _q h251 h474 h4199
  exact p20479
theorem n20482 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e5392 _v) := by
  have p20481 := n20481 _v _q 
  have p11374 := n11374 _v _q h251
  have p16943 := n16943 _v _q 
  change (¬ (e4199 _v)) ∨ (¬ (e251 _v)) ∨ (¬ (e474 _v)) at p20481
  rcases p20481 with hlit | hlit | hlit
  · exact (False.elim (hlit p16943))
  · exact (False.elim (hlit p11374))
  · exact hlit
theorem n20483 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e5403 _v) := by
  have p14577 := n14577 _v _q 
  have p20482 := n20482 _v _q h251
  change (e474 _v) ∨ (¬ (e5402 _v)) at p14577
  change (¬ (e474 _v)) at p20482
  rcases p14577 with hlit | hlit
  · exact (False.elim (p20482 hlit))
  · exact hlit
theorem n20484 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e488 _v) := by
  have p15090 := n15090 _v _q 
  have p20483 := n20483 _v _q h251
  change (e5402 _v) ∨ (e488 _v) at p15090
  change (¬ (e5402 _v)) at p20483
  rcases p15090 with hlit | hlit
  · exact (False.elim (p20483 hlit))
  · exact hlit
theorem n20485 (_v : Vars) (_q : Query _v)  : (e8564 _v) := by
  simp only [e488, e490, e493, e494, e5402, e8564] at *
  tauto
theorem n20486 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e490 _v) := by
  have p20485 := n20485 _v _q 
  have p20483 := n20483 _v _q h251
  change (e5402 _v) ∨ (e490 _v) at p20485
  change (¬ (e5402 _v)) at p20483
  rcases p20485 with hlit | hlit
  · exact (False.elim (p20483 hlit))
  · exact hlit
theorem n20487 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e4439 _v) := by
  have p14925 := n14925 _v _q 
  have p20456 := n20456 _v _q h251
  change (e4446 _v) ∨ (e4439 _v) at p14925
  change (¬ (e4446 _v)) at p20456
  rcases p14925 with hlit | hlit
  · exact (False.elim (p20456 hlit))
  · exact hlit
theorem n20488 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e3158 _v) := by
  have p15126 := n15126 _v _q 
  have p20458 := n20458 _v _q h251
  change (e3162 _v) ∨ (e3158 _v) at p15126
  change (¬ (e3162 _v)) at p20458
  rcases p15126 with hlit | hlit
  · exact (False.elim (p20458 hlit))
  · exact hlit
theorem n20489 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e4459 _v) := by
  have p8443 := n8443 _v _q 
  have p15848 := n15848 _v _q h251
  change (e4465 _v) ∨ (e4459 _v) at p8443
  change (¬ (e4465 _v)) at p15848
  rcases p8443 with hlit | hlit
  · exact (False.elim (p15848 hlit))
  · exact hlit
theorem n20490 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e3919 _v) := by
  have p14797 := n14797 _v _q 
  have p20460 := n20460 _v _q h251
  change (e3923 _v) ∨ (e3919 _v) at p14797
  change (¬ (e3923 _v)) at p20460
  rcases p14797 with hlit | hlit
  · exact (False.elim (p20460 hlit))
  · exact hlit
theorem n20491 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e4679 _v) := by
  have p14989 := n14989 _v _q 
  have p15864 := n15864 _v _q h251
  change (e4685 _v) ∨ (e4679 _v) at p14989
  change (¬ (e4685 _v)) at p15864
  rcases p14989 with hlit | hlit
  · exact (False.elim (p15864 hlit))
  · exact hlit
theorem n20492 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e4101 _v) := by
  have p14929 := n14929 _v _q 
  have p15870 := n15870 _v _q h251
  change (e4108 _v) ∨ (e4101 _v) at p14929
  change (¬ (e4108 _v)) at p15870
  rcases p14929 with hlit | hlit
  · exact (False.elim (p15870 hlit))
  · exact hlit
theorem n20493 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) (h4156 : (e4156 _v)) : (e196 _v) := by
  have p18214 := n18214 _v _q 
  have p4985 := n4985 _v _q h4156
  have p16992 := n16992 _v _q 
  have p20461 := n20461 _v _q 
  have p11374 := n11374 _v _q h251
  have p20484 := n20484 _v _q h251
  have p20126 := n20126 _v _q 
  have p20426 := n20426 _v _q 
  have p20487 := n20487 _v _q h251
  have p20488 := n20488 _v _q h251
  have p20489 := n20489 _v _q h251
  have p15850 := n15850 _v _q h251
  have p19610 := n19610 _v _q 
  have p20490 := n20490 _v _q h251
  have p15853 := n15853 _v _q h251
  have p15856 := n15856 _v _q h251
  have p20096 := n20096 _v _q 
  have p20470 := n20470 _v _q 
  have p15859 := n15859 _v _q h251
  have p15862 := n15862 _v _q h251
  have p20467 := n20467 _v _q 
  have p20491 := n20491 _v _q h251
  have p15867 := n15867 _v _q h251
  have p15869 := n15869 _v _q h251
  have p20492 := n20492 _v _q h251
  have p20274 := n20274 _v _q 
  have p15872 := n15872 _v _q h251
  change (¬ (e5237 _v)) ∨ (¬ (e251 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e4439 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e3976 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e3158 _v)) ∨ (¬ (e4459 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e3919 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e3133 _v)) ∨ (¬ (e4491 _v)) ∨ (¬ (e4724 _v)) ∨ (¬ (e4567 _v)) ∨ (¬ (e4791 _v)) ∨ (¬ (e4398 _v)) ∨ (¬ (e4679 _v)) ∨ (¬ (e4817 _v)) ∨ (¬ (e4264 _v)) ∨ (¬ (e4101 _v)) ∨ (¬ (e4903 _v)) ∨ (e196 _v) at p18214
  rcases p18214 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact (False.elim (hlit p16992))
  · exact (False.elim (hlit p11374))
  · exact (False.elim (hlit p20461))
  · exact (False.elim (hlit p4985))
  · exact (False.elim (hlit p20487))
  · exact (False.elim (hlit p20484))
  · exact (False.elim (hlit p20126))
  · exact (False.elim (hlit p20426))
  · exact (False.elim (hlit p15850))
  · exact (False.elim (hlit p20488))
  · exact (False.elim (hlit p20489))
  · exact (False.elim (hlit p15853))
  · exact (False.elim (hlit p19610))
  · exact (False.elim (hlit p20490))
  · exact (False.elim (hlit p15872))
  · exact (False.elim (hlit p15856))
  · exact (False.elim (hlit p20096))
  · exact (False.elim (hlit p20470))
  · exact (False.elim (hlit p15859))
  · exact (False.elim (hlit p15862))
  · exact (False.elim (hlit p20467))
  · exact (False.elim (hlit p20491))
  · exact (False.elim (hlit p15867))
  · exact (False.elim (hlit p15869))
  · exact (False.elim (hlit p20492))
  · exact (False.elim (hlit p20274))
  · exact hlit
theorem n20494 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) (h4156 : (e4156 _v)) : (e5203 _v) := by
  have p14730 := n14730 _v _q 
  have p20493 := n20493 _v _q h251 h4156
  change (¬ (e196 _v)) ∨ (¬ (e5193 _v)) at p14730
  rcases p14730 with hlit | hlit
  · exact (False.elim (hlit p20493))
  · exact hlit
theorem n20495 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) (h4156 : (e4156 _v)) : (e191 _v) := by
  have p16442 := n16442 _v _q 
  have p20494 := n20494 _v _q h251 h4156
  change (e5193 _v) ∨ (e191 _v) at p16442
  change (¬ (e5193 _v)) at p20494
  rcases p16442 with hlit | hlit
  · exact (False.elim (p20494 hlit))
  · exact hlit
theorem n20496 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) (h4156 : (e4156 _v)) : (e214 _v) := by
  have p11523 := n11523 _v _q 
  have p20493 := n20493 _v _q h251 h4156
  change (e214 _v) ∨ (¬ (e196 _v)) at p11523
  rcases p11523 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p20493))
theorem n20497 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) (h4156 : (e4156 _v)) : (e5232 _v) := by
  have p14731 := n14731 _v _q 
  have p20496 := n20496 _v _q h251 h4156
  change (¬ (e214 _v)) ∨ (¬ (e5231 _v)) at p14731
  rcases p14731 with hlit | hlit
  · exact (False.elim (hlit p20496))
  · exact hlit
theorem n20498 (_v : Vars) (_q : Query _v)  : (e8563 _v) := by
  simp only [e191, e192, e193, e194, e5193, e8563] at *
  tauto
theorem n20499 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) (h4156 : (e4156 _v)) : (e193 _v) := by
  have p20498 := n20498 _v _q 
  have p20494 := n20494 _v _q h251 h4156
  change (e5193 _v) ∨ (e193 _v) at p20498
  change (¬ (e5193 _v)) at p20494
  rcases p20498 with hlit | hlit
  · exact (False.elim (p20494 hlit))
  · exact hlit
theorem n20500 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) (h4156 : (e4156 _v)) (h6571 : (e6571 _v)) : (e7489 _v) := by
  have p20493 := n20493 _v _q h251 h4156
  have p5255 := n5255 _v _q 
  have p20496 := n20496 _v _q h251 h4156
  have p15862 := n15862 _v _q h251
  have p16992 := n16992 _v _q 
  have p19610 := n19610 _v _q 
  have p20488 := n20488 _v _q h251
  have p11374 := n11374 _v _q h251
  have p17122 := n17122 _v _q 
  have p17096 := n17096 _v _q 
  have p15869 := n15869 _v _q h251
  have p20487 := n20487 _v _q h251
  have p4985 := n4985 _v _q h4156
  have p20490 := n20490 _v _q h251
  have p15856 := n15856 _v _q h251
  have p20492 := n20492 _v _q h251
  have p20491 := n20491 _v _q h251
  have p15859 := n15859 _v _q h251
  have p17115 := n17115 _v _q 
  have p17256 := n17256 _v _q 
  have p17120 := n17120 _v _q 
  have p17111 := n17111 _v _q 
  have p17124 := n17124 _v _q 
  have p17050 := n17050 _v _q 
  have p16778 := n16778 _v _q 
  have p17113 := n17113 _v _q 
  have p17117 := n17117 _v _q 
  have p20467 := n20467 _v _q 
  have p20489 := n20489 _v _q h251
  have p20484 := n20484 _v _q h251
  have p15867 := n15867 _v _q h251
  have p17104 := n17104 _v _q 
  have p17874 := n17874 _v _q 
  have p17127 := n17127 _v _q 
  have p15850 := n15850 _v _q h251
  have p20274 := n20274 _v _q 
  have p15119 := n15119 _v _q h251
  have p20470 := n20470 _v _q 
  have p17133 := n17133 _v _q 
  have p17089 := n17089 _v _q 
  have p19665 := n19665 _v _q 
  have p20426 := n20426 _v _q 
  have p17055 := n17055 _v _q 
  have p17108 := n17108 _v _q 
  have p20461 := n20461 _v _q 
  have p20126 := n20126 _v _q 
  have p17131 := n17131 _v _q 
  have p17110 := n17110 _v _q 
  have p17053 := n17053 _v _q 
  have p15872 := n15872 _v _q h251
  have p20096 := n20096 _v _q 
  have p17294 := n17294 _v _q 
  have p16943 := n16943 _v _q 
  have p17058 := n17058 _v _q 
  have p17064 := n17064 _v _q 
  have p17067 := n17067 _v _q 
  have p17069 := n17069 _v _q 
  have p17072 := n17072 _v _q 
  have p17136 := n17136 _v _q 
  have p13951 := n13951 _v _q 
  have p17078 := n17078 _v _q 
  have p17080 := n17080 _v _q 
  have p17083 := n17083 _v _q 
  have p17074 := n17074 _v _q 
  have p17087 := n17087 _v _q 
  have p17758 := n17758 _v _q 
  have p17091 := n17091 _v _q 
  have p17093 := n17093 _v _q 
  have p15853 := n15853 _v _q h251
  have p17141 := n17141 _v _q 
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p17100 := n17100 _v _q 
  have p17102 := n17102 _v _q 
  have p20495 := n20495 _v _q h251 h4156
  have p8447 := n8447 _v _q h6571
  exact FloorCertificate.node_20500 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2902 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) p20493 p5255 p20496 p15862 p16992 p19610 p20488 p11374 p17122 p17096 p15869 p20487 p4985 p20490 p15856 p20492 p20491 p15859 p17115 p17256 p17120 p17111 p17124 p17050 p16778 p17113 p17117 p20467 p20489 p20484 p15867 p17104 p17874 p17127 p15850 p20274 p15119 p20470 p17133 p17089 p19665 p20426 p17055 p17108 p20461 p20126 p17131 p17110 p17053 p15872 p20096 p17294 p16943 p17058 p17064 p17067 p17069 p17072 p17136 p13951 p17078 p17080 p17083 p17074 p17087 p17758 p17091 p17093 p15853 p17141 p17098 p17106 p17100 p17102 p20495 p8447
theorem n20501 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) (h4156 : (e4156 _v)) : (e225 _v) := by
  have p16653 := n16653 _v _q 
  have p20497 := n20497 _v _q h251 h4156
  change (e5231 _v) ∨ (e225 _v) at p16653
  change (¬ (e5231 _v)) at p20497
  rcases p16653 with hlit | hlit
  · exact (False.elim (p20497 hlit))
  · exact hlit
theorem n20502 (_v : Vars) (_q : Query _v)  : (e8560 _v) := by
  simp only [e225, e227, e230, e231, e5231, e8560] at *
  tauto
theorem n20503 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) (h4156 : (e4156 _v)) : (e227 _v) := by
  have p20502 := n20502 _v _q 
  have p20497 := n20497 _v _q h251 h4156
  change (e5231 _v) ∨ (e227 _v) at p20502
  change (¬ (e5231 _v)) at p20497
  rcases p20502 with hlit | hlit
  · exact (False.elim (p20497 hlit))
  · exact hlit
theorem n20505 (_v : Vars) (_q : Query _v)  : (e20504 _v) := by
  by_contra hc
  change ¬ ((e2358 _v) ∨ (¬ (e251 _v)) ∨ (¬ (e4156 _v))) at hc
  have h251 : (e251 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h4156 : (e4156 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr hn)))
  have h6571 : (e6571 _v) := (fun hn => hc (Or.inl hn))
  have p20500 := n20500 _v _q h251 h4156 h6571
  exact p20500
theorem n20506 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) (h7668 : (e7668 _v)) : (e2358 _v) := by
  have p20505 := n20505 _v _q 
  have p11526 := n11526 _v _q h7668
  have p11374 := n11374 _v _q h251
  change (e2358 _v) ∨ (¬ (e251 _v)) ∨ (¬ (e4156 _v)) at p20505
  rcases p20505 with hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p11374))
  · exact (False.elim (hlit p11526))
theorem n20507 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) (h4156 : (e4156 _v)) : (e2358 _v) := by
  have p20505 := n20505 _v _q 
  have p4985 := n4985 _v _q h4156
  have p11374 := n11374 _v _q h251
  change (e2358 _v) ∨ (¬ (e251 _v)) ∨ (¬ (e4156 _v)) at p20505
  rcases p20505 with hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p11374))
  · exact (False.elim (hlit p4985))
theorem n20508 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) (h4156 : (e4156 _v)) : (e7640 _v) := by
  have p14828 := n14828 _v _q 
  have p20507 := n20507 _v _q h251 h4156
  change (¬ (e2358 _v)) ∨ (¬ (e7634 _v)) at p14828
  rcases p14828 with hlit | hlit
  · exact (False.elim (hlit p20507))
  · exact hlit
theorem n20509 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) (h4156 : (e4156 _v)) : (e4139 _v) := by
  have p16281 := n16281 _v _q 
  have p20508 := n20508 _v _q h251 h4156
  change (e7634 _v) ∨ (e4139 _v) at p16281
  change (¬ (e7634 _v)) at p20508
  rcases p16281 with hlit | hlit
  · exact (False.elim (p20508 hlit))
  · exact hlit
theorem n20510 (_v : Vars) (_q : Query _v)  : (e8562 _v) := by
  simp only [e4139, e4140, e4141, e4142, e7634, e8562] at *
  tauto
theorem n20511 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) (h4156 : (e4156 _v)) : (e4141 _v) := by
  have p20510 := n20510 _v _q 
  have p20508 := n20508 _v _q h251 h4156
  change (e7634 _v) ∨ (e4141 _v) at p20510
  change (¬ (e7634 _v)) at p20508
  rcases p20510 with hlit | hlit
  · exact (False.elim (p20508 hlit))
  · exact hlit
theorem n20512 (_v : Vars) (_q : Query _v)  : (e5028 _v) := by
  simp only [e4902, e4903, e4907, e4908, e4909, e5028] at *
  tauto
theorem n20513 (_v : Vars) (_q : Query _v)  : (e4902 _v) := by
  have p20512 := n20512 _v _q 
  have p20273 := n20273 _v _q 
  change (e4909 _v) ∨ (e4902 _v) at p20512
  change (¬ (e4909 _v)) at p20273
  rcases p20512 with hlit | hlit
  · exact (False.elim (p20273 hlit))
  · exact hlit
theorem n20514 (_v : Vars) (_q : Query _v)  : (e5030 _v) := by
  simp only [e3793, e3794, e3795, e3796, e3797, e5030] at *
  tauto
end
end Assembly
