import Dag273
import generated.th_lemma_37
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n22535 (_v : Vars) (_q : Query _v) (h6501 : (e6501 _v)) : (e5093 _v) := by
  have p11468 := n11468 _v _q 
  have p22520 := n22520 _v _q h6501
  change (¬ (e13 _v)) ∨ (e2303 _v) at p11468
  change (¬ (e2303 _v)) at p22520
  rcases p11468 with hlit | hlit
  · exact hlit
  · exact (False.elim (p22520 hlit))
theorem n22536 (_v : Vars) (_q : Query _v) (h6501 : (e6501 _v)) : (e5105 _v) := by
  have p15204 := n15204 _v _q 
  have p22535 := n22535 _v _q h6501
  change (e13 _v) ∨ (¬ (e5104 _v)) at p15204
  change (¬ (e13 _v)) at p22535
  rcases p15204 with hlit | hlit
  · exact (False.elim (p22535 hlit))
  · exact hlit
theorem n22537 (_v : Vars) (_q : Query _v) (h6501 : (e6501 _v)) : (e5100 _v) := by
  have p15319 := n15319 _v _q 
  have p22536 := n22536 _v _q h6501
  change (e5104 _v) ∨ (e5100 _v) at p15319
  change (¬ (e5104 _v)) at p22536
  rcases p15319 with hlit | hlit
  · exact (False.elim (p22536 hlit))
  · exact hlit
theorem n22538 (_v : Vars) (_q : Query _v) (h6501 : (e6501 _v)) : (e7819 _v) := by
  have p14994 := n14994 _v _q 
  have p22520 := n22520 _v _q h6501
  change (e2303 _v) ∨ (¬ (e7818 _v)) at p14994
  change (¬ (e2303 _v)) at p22520
  rcases p14994 with hlit | hlit
  · exact (False.elim (p22520 hlit))
  · exact hlit
theorem n22539 (_v : Vars) (_q : Query _v) (h6501 : (e6501 _v)) : (e7814 _v) := by
  have p15221 := n15221 _v _q 
  have p22538 := n22538 _v _q h6501
  change (e7818 _v) ∨ (e7814 _v) at p15221
  change (¬ (e7818 _v)) at p22538
  rcases p15221 with hlit | hlit
  · exact (False.elim (p22538 hlit))
  · exact hlit
theorem n22540 (_v : Vars) (_q : Query _v) (h3937 : (e3937 _v)) (h4306 : (e4306 _v)) (h4608 : (e4608 _v)) (h7749 : (e7749 _v)) (h8038 : (e8038 _v)) : (e6772 _v) := by
  have p14855 := n14855 _v _q 
  have p22529 := n22529 _v _q h3937 h4306 h4608 h7749 h8038
  change (¬ (e2787 _v)) ∨ (¬ (e7921 _v)) at p14855
  rcases p14855 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p22529))
theorem n22541 (_v : Vars) (_q : Query _v) (h3937 : (e3937 _v)) (h4306 : (e4306 _v)) (h4608 : (e4608 _v)) (h7749 : (e7749 _v)) (h8038 : (e8038 _v)) : (e7945 _v) := by
  have p15228 := n15228 _v _q 
  have p22540 := n22540 _v _q h3937 h4306 h4608 h7749 h8038
  change (e2787 _v) ∨ (¬ (e7944 _v)) at p15228
  change (¬ (e2787 _v)) at p22540
  rcases p15228 with hlit | hlit
  · exact (False.elim (p22540 hlit))
  · exact hlit
theorem n22542 (_v : Vars) (_q : Query _v) (h3937 : (e3937 _v)) (h4306 : (e4306 _v)) (h4608 : (e4608 _v)) (h7749 : (e7749 _v)) (h8038 : (e8038 _v)) : (e7935 _v) := by
  have p15266 := n15266 _v _q 
  have p22541 := n22541 _v _q h3937 h4306 h4608 h7749 h8038
  change (e7944 _v) ∨ (e7935 _v) at p15266
  change (¬ (e7944 _v)) at p22541
  rcases p15266 with hlit | hlit
  · exact (False.elim (p22541 hlit))
  · exact hlit
theorem n22543 (_v : Vars) (_q : Query _v) (h3937 : (e3937 _v)) (h4306 : (e4306 _v)) (h4608 : (e4608 _v)) (h7749 : (e7749 _v)) : (e7493 _v) := by
  have p15195 := n15195 _v _q 
  have p22527 := n22527 _v _q h3937 h4306 h4608 h7749
  change (e7497 _v) ∨ (e7493 _v) at p15195
  change (¬ (e7497 _v)) at p22527
  rcases p15195 with hlit | hlit
  · exact (False.elim (p22527 hlit))
  · exact hlit
theorem n22544 (_v : Vars) (_q : Query _v) (h3937 : (e3937 _v)) (h4306 : (e4306 _v)) (h4608 : (e4608 _v)) (h7749 : (e7749 _v)) (h8038 : (e8038 _v)) : (e6571 _v) := by
  have p20876 := n20876 _v _q 
  have p22542 := n22542 _v _q h3937 h4306 h4608 h7749 h8038
  have p22302 := n22302 _v _q 
  have p4991 := n4991 _v _q h4608
  have p22324 := n22324 _v _q 
  have p22368 := n22368 _v _q 
  have p22320 := n22320 _v _q 
  have p22407 := n22407 _v _q 
  have p22416 := n22416 _v _q h3937 h4608
  have p22341 := n22341 _v _q 
  have p17138 := n17138 _v _q h4306
  have p22436 := n22436 _v _q h3937 h4306 h4608 h7749
  have p4996 := n4996 _v _q h3937
  have p22318 := n22318 _v _q 
  have p22347 := n22347 _v _q 
  have p22321 := n22321 _v _q 
  have p22322 := n22322 _v _q 
  have p22323 := n22323 _v _q 
  have p22534 := n22534 _v _q h3937 h4306 h4608 h7749
  have p8602 := n8602 _v _q h8038
  change (¬ (e7814 _v)) ∨ (e2475 _v) ∨ (¬ (e4260 _v)) ∨ (¬ (e7935 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4567 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4439 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e2358 _v)) at p20876
  change (¬ (e2475 _v)) at p8602
  rcases p20876 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact (False.elim (hlit p22534))
  · exact (False.elim (p8602 hlit))
  · exact (False.elim (hlit p22320))
  · exact (False.elim (hlit p22542))
  · exact (False.elim (hlit p22324))
  · exact (False.elim (hlit p22407))
  · exact (False.elim (hlit p22341))
  · exact (False.elim (hlit p22436))
  · exact (False.elim (hlit p22416))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p4991))
  · exact (False.elim (hlit p4996))
  · exact (False.elim (hlit p22318))
  · exact (False.elim (hlit p22368))
  · exact (False.elim (hlit p22347))
  · exact (False.elim (hlit p22321))
  · exact (False.elim (hlit p22322))
  · exact (False.elim (hlit p22323))
  · exact (False.elim (hlit p22302))
  · exact hlit
theorem n22545 (_v : Vars) (_q : Query _v) (h3937 : (e3937 _v)) (h4306 : (e4306 _v)) (h4608 : (e4608 _v)) (h7749 : (e7749 _v)) (h8038 : (e8038 _v)) : (e7489 _v) := by
  have p22542 := n22542 _v _q h3937 h4306 h4608 h7749 h8038
  have p16977 := n16977 _v _q 
  have p15209 := n15209 _v _q h8038
  have p22532 := n22532 _v _q h3937 h4306 h4608 h7749
  have p22534 := n22534 _v _q h3937 h4306 h4608 h7749
  have p22298 := n22298 _v _q 
  have p17083 := n17083 _v _q 
  have p17098 := n17098 _v _q 
  have p22302 := n22302 _v _q 
  have p17106 := n17106 _v _q 
  have p22543 := n22543 _v _q h3937 h4306 h4608 h7749
  have p17256 := n17256 _v _q 
  have p17093 := n17093 _v _q 
  have p22436 := n22436 _v _q h3937 h4306 h4608 h7749
  have p13951 := n13951 _v _q 
  have p22429 := n22429 _v _q h3937 h4306 h4608 h7749
  have p22544 := n22544 _v _q h3937 h4306 h4608 h7749 h8038
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
  have p22358 := n22358 _v _q h3937 h4608 h8038
  have p8602 := n8602 _v _q h8038
  exact FloorCertificate.node_22545 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e61 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2863 _v) (e2877 _v) (e2883 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p22542 p16977 p15209 p22532 p22534 p22298 p17083 p17098 p22302 p17106 p22543 p17256 p17093 p22436 p13951 p22429 p22544 p17100 p22322 p17091 p17102 p17138 p17141 p22416 p4996 p17147 p16269 p22407 p17124 p22341 p22324 p19610 p17020 p4991 p16576 p22368 p22323 p17758 p22320 p17115 p17078 p17117 p17113 p20467 p17133 p17120 p17009 p22321 p17089 p22318 p22347 p17104 p20470 p20274 p19665 p16778 p17127 p17050 p17122 p17096 p20126 p20426 p17110 p20829 p20653 p17111 p17131 p17108 p17294 p16943 p17064 p17067 p17080 p17053 p17072 p17074 p17069 p20096 p20836 p20461 p17874 p17136 p17087 p17055 p17058 p22358 p8602
theorem n22547 (_v : Vars) (_q : Query _v)  : (e22546 _v) := by
  by_contra hc
  change ¬ ((e2475 _v) ∨ (¬ (e4306 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e7749 _v)) ∨ (¬ (e4608 _v))) at hc
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h4608 : (e4608 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr hn)))))
  have h7749 : (e7749 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h8038 : (e8038 _v) := (fun hn => hc (Or.inl hn))
  have p22545 := n22545 _v _q h3937 h4306 h4608 h7749 h8038
  exact p22545
theorem n22548 (_v : Vars) (_q : Query _v) (h3937 : (e3937 _v)) (h4306 : (e4306 _v)) (h4608 : (e4608 _v)) (h7749 : (e7749 _v)) : (e2475 _v) := by
  have p22547 := n22547 _v _q 
  have p17138 := n17138 _v _q h4306
  have p4996 := n4996 _v _q h3937
  have p16269 := n16269 _v _q h7749
  have p4991 := n4991 _v _q h4608
  change (e2475 _v) ∨ (¬ (e4306 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e7749 _v)) ∨ (¬ (e4608 _v)) at p22547
  rcases p22547 with hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p4996))
  · exact (False.elim (hlit p16269))
  · exact (False.elim (hlit p4991))
theorem n22549 (_v : Vars) (_q : Query _v) (h3937 : (e3937 _v)) (h4306 : (e4306 _v)) (h4608 : (e4608 _v)) (h7749 : (e7749 _v)) : (e8035 _v) := by
  have p14871 := n14871 _v _q 
  have p22548 := n22548 _v _q h3937 h4306 h4608 h7749
  change (¬ (e2475 _v)) ∨ (¬ (e8029 _v)) at p14871
  rcases p14871 with hlit | hlit
  · exact (False.elim (hlit p22548))
  · exact hlit
theorem n22550 (_v : Vars) (_q : Query _v) (h6501 : (e6501 _v)) : (e2475 _v) := by
  have p22547 := n22547 _v _q 
  have p22510 := n22510 _v _q h6501
  have p16325 := n16325 _v _q h6501
  have p22441 := n22441 _v _q h6501
  have p15641 := n15641 _v _q h6501
  change (e2475 _v) ∨ (¬ (e4306 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e7749 _v)) ∨ (¬ (e4608 _v)) at p22547
  rcases p22547 with hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p22510))
  · exact (False.elim (hlit p16325))
  · exact (False.elim (hlit p22441))
  · exact (False.elim (hlit p15641))
theorem n22551 (_v : Vars) (_q : Query _v) (h6501 : (e6501 _v)) : (e8035 _v) := by
  have p14871 := n14871 _v _q 
  have p22550 := n22550 _v _q h6501
  change (¬ (e2475 _v)) ∨ (¬ (e8029 _v)) at p14871
  rcases p14871 with hlit | hlit
  · exact (False.elim (hlit p22550))
  · exact hlit
theorem n22552 (_v : Vars) (_q : Query _v) (h3937 : (e3937 _v)) (h4306 : (e4306 _v)) (h4608 : (e4608 _v)) (h7749 : (e7749 _v)) : (e4546 _v) := by
  have p16307 := n16307 _v _q 
  have p22549 := n22549 _v _q h3937 h4306 h4608 h7749
  change (e8029 _v) ∨ (e4546 _v) at p16307
  change (¬ (e8029 _v)) at p22549
  rcases p16307 with hlit | hlit
  · exact (False.elim (p22549 hlit))
  · exact hlit
theorem n22553 (_v : Vars) (_q : Query _v) (h6501 : (e6501 _v)) : (e4546 _v) := by
  have p16307 := n16307 _v _q 
  have p22551 := n22551 _v _q h6501
  change (e8029 _v) ∨ (e4546 _v) at p16307
  change (¬ (e8029 _v)) at p22551
  rcases p16307 with hlit | hlit
  · exact (False.elim (p22551 hlit))
  · exact hlit
theorem n22554 (_v : Vars) (_q : Query _v) (h3937 : (e3937 _v)) (h4306 : (e4306 _v)) (h4608 : (e4608 _v)) (h7749 : (e7749 _v)) (h7935 : (e7935 _v)) : (e7489 _v) := by
  have p17874 := n17874 _v _q 
  have p4016 := n4016 _v _q 
  have p10896 := n10896 _v _q 
  have p10893 := n10893 _v _q 
  have p22543 := n22543 _v _q h3937 h4306 h4608 h7749
  have p17136 := n17136 _v _q 
  have p22302 := n22302 _v _q 
  have p5257 := n5257 _v _q 
  have p13951 := n13951 _v _q 
  have p17055 := n17055 _v _q 
  have p17058 := n17058 _v _q 
  have p22552 := n22552 _v _q h3937 h4306 h4608 h7749
  have p17163 := n17163 _v _q h7935
  have p16977 := n16977 _v _q 
  have p22532 := n22532 _v _q h3937 h4306 h4608 h7749
  have p22534 := n22534 _v _q h3937 h4306 h4608 h7749
  have p17083 := n17083 _v _q 
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p17256 := n17256 _v _q 
  have p17093 := n17093 _v _q 
  have p22436 := n22436 _v _q h3937 h4306 h4608 h7749
  have p17087 := n17087 _v _q 
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
  exact FloorCertificate.node_22554 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e61 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2863 _v) (e2877 _v) (e2883 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p17874 p4016 p10896 p10893 p22543 p17136 p22302 p5257 p13951 p17055 p17058 p22552 p17163 p16977 p22532 p22534 p17083 p17098 p17106 p17256 p17093 p22436 p17087 p17100 p22322 p17091 p17102 p17138 p17141 p22416 p4996 p17147 p16269 p22407 p17124 p22341 p22324 p19610 p17020 p4991 p16576 p22368 p22323 p17758 p22320 p17115 p17078 p17117 p17113 p20467 p17133 p17120 p17009 p22321 p17089 p22318 p22347 p17104 p20470 p20274 p19665 p16778 p17127 p17050 p17122 p17096 p20126 p20426 p17110 p20829 p20653 p17111 p17131 p17108 p17294 p16943 p17064 p17067 p17080 p17053 p17072 p17074 p17069 p20096 p20836 p20461
theorem n22556 (_v : Vars) (_q : Query _v)  : (e22555 _v) := by
  by_contra hc
  change ¬ ((¬ (e7935 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e7749 _v)) ∨ (¬ (e4608 _v))) at hc
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h4608 : (e4608 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr hn)))))
  have h7749 : (e7749 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h7935 : (e7935 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have p22554 := n22554 _v _q h3937 h4306 h4608 h7749 h7935
  exact p22554
theorem n22557 (_v : Vars) (_q : Query _v) (h6501 : (e6501 _v)) : (e7943 _v) := by
  have p22556 := n22556 _v _q 
  have p22510 := n22510 _v _q h6501
  have p16325 := n16325 _v _q h6501
  have p22441 := n22441 _v _q h6501
  have p15641 := n15641 _v _q h6501
  change (¬ (e7935 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e7749 _v)) ∨ (¬ (e4608 _v)) at p22556
  rcases p22556 with hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p22510))
  · exact (False.elim (hlit p16325))
  · exact (False.elim (hlit p22441))
  · exact (False.elim (hlit p15641))
theorem n22558 (_v : Vars) (_q : Query _v) (h6501 : (e6501 _v)) : (e7944 _v) := by
  have p15266 := n15266 _v _q 
  have p22557 := n22557 _v _q h6501
  change (e7944 _v) ∨ (e7935 _v) at p15266
  change (¬ (e7935 _v)) at p22557
  rcases p15266 with hlit | hlit
  · exact hlit
  · exact (False.elim (p22557 hlit))
theorem n22559 (_v : Vars) (_q : Query _v) (h6501 : (e6501 _v)) : (e2787 _v) := by
  have p15228 := n15228 _v _q 
  have p22558 := n22558 _v _q h6501
  change (e2787 _v) ∨ (¬ (e7944 _v)) at p15228
  rcases p15228 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p22558))
theorem n22560 (_v : Vars) (_q : Query _v) (h6501 : (e6501 _v)) : (e7927 _v) := by
  have p14855 := n14855 _v _q 
  have p22559 := n22559 _v _q h6501
  change (¬ (e2787 _v)) ∨ (¬ (e7921 _v)) at p14855
  rcases p14855 with hlit | hlit
  · exact (False.elim (hlit p22559))
  · exact hlit
theorem n22561 (_v : Vars) (_q : Query _v) (h6501 : (e6501 _v)) : (e2358 _v) := by
  have p11498 := n11498 _v _q 
  have p22559 := n22559 _v _q h6501
  change (¬ (e2787 _v)) ∨ (e2358 _v) at p11498
  rcases p11498 with hlit | hlit
  · exact (False.elim (hlit p22559))
  · exact hlit
theorem n22562 (_v : Vars) (_q : Query _v) (h6501 : (e6501 _v)) : (e4419 _v) := by
  have p16347 := n16347 _v _q 
  have p22560 := n22560 _v _q h6501
  change (e7921 _v) ∨ (e4419 _v) at p16347
  change (¬ (e7921 _v)) at p22560
  rcases p16347 with hlit | hlit
  · exact (False.elim (p22560 hlit))
  · exact hlit
theorem n22563 (_v : Vars) (_q : Query _v) (h6501 : (e6501 _v)) : (e7640 _v) := by
  have p14828 := n14828 _v _q 
  have p22561 := n22561 _v _q h6501
  change (¬ (e2358 _v)) ∨ (¬ (e7634 _v)) at p14828
  rcases p14828 with hlit | hlit
  · exact (False.elim (hlit p22561))
  · exact hlit
theorem n22564 (_v : Vars) (_q : Query _v) (h6501 : (e6501 _v)) : (e4139 _v) := by
  have p16281 := n16281 _v _q 
  have p22563 := n22563 _v _q h6501
  change (e7634 _v) ∨ (e4139 _v) at p16281
  change (¬ (e7634 _v)) at p22563
  rcases p16281 with hlit | hlit
  · exact (False.elim (p22563 hlit))
  · exact hlit
theorem n22565 (_v : Vars) (_q : Query _v) (h6501 : (e6501 _v)) : (e7493 _v) := by
  have p15195 := n15195 _v _q 
  have p22524 := n22524 _v _q h6501
  change (e7497 _v) ∨ (e7493 _v) at p15195
  change (¬ (e7497 _v)) at p22524
  rcases p15195 with hlit | hlit
  · exact (False.elim (p22524 hlit))
  · exact hlit
theorem n22566 (_v : Vars) (_q : Query _v) (h6501 : (e6501 _v)) : (e7489 _v) := by
  have p20461 := n20461 _v _q 
  have p22565 := n22565 _v _q h6501
  have p22562 := n22562 _v _q h6501
  have p17874 := n17874 _v _q 
  have p22302 := n22302 _v _q 
  have p17136 := n17136 _v _q 
  have p13951 := n13951 _v _q 
  have p17055 := n17055 _v _q 
  have p17058 := n17058 _v _q 
  have p10893 := n10893 _v _q 
  have p20836 := n20836 _v _q 
  have p22553 := n22553 _v _q h6501
  have p16977 := n16977 _v _q 
  have p22537 := n22537 _v _q h6501
  have p22539 := n22539 _v _q h6501
  have p17083 := n17083 _v _q 
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p22559 := n22559 _v _q h6501
  have p17093 := n17093 _v _q 
  have p22516 := n22516 _v _q h6501
  have p17087 := n17087 _v _q 
  have p17100 := n17100 _v _q 
  have p22322 := n22322 _v _q 
  have p17091 := n17091 _v _q 
  have p17102 := n17102 _v _q 
  have p22510 := n22510 _v _q h6501
  have p17141 := n17141 _v _q 
  have p22417 := n22417 _v _q h6501
  have p16325 := n16325 _v _q h6501
  have p17147 := n17147 _v _q 
  have p22441 := n22441 _v _q h6501
  have p22407 := n22407 _v _q 
  have p17124 := n17124 _v _q 
  have p22341 := n22341 _v _q 
  have p22324 := n22324 _v _q 
  have p19610 := n19610 _v _q 
  have p17020 := n17020 _v _q 
  have p15641 := n15641 _v _q h6501
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
  have p5257 := n5257 _v _q 
  have p22520 := n22520 _v _q h6501
  have p22564 := n22564 _v _q h6501
  exact FloorCertificate.node_22566 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e61 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2863 _v) (e2877 _v) (e2883 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p20461 p22565 p22562 p17874 p22302 p17136 p13951 p17055 p17058 p10893 p20836 p22553 p16977 p22537 p22539 p17083 p17098 p17106 p22559 p17093 p22516 p17087 p17100 p22322 p17091 p17102 p22510 p17141 p22417 p16325 p17147 p22441 p22407 p17124 p22341 p22324 p19610 p17020 p15641 p16576 p22368 p22323 p17758 p22320 p17115 p17078 p17117 p17113 p20467 p17133 p17120 p17009 p22321 p17089 p22318 p22347 p17104 p20470 p20274 p19665 p16778 p17127 p17050 p17122 p17096 p20126 p20426 p17110 p20829 p20653 p17111 p17131 p17108 p17294 p16943 p17064 p17067 p17080 p17053 p17072 p17074 p17069 p20096 p5257 p22520 p22564
theorem n22567 (_v : Vars) (_q : Query _v)  : (e2179 _v) := by
  by_contra hc
  change ¬ (e2179 _v) at hc
  have h6501 : (e6501 _v) := (fun hn => hc hn)
  have p22566 := n22566 _v _q h6501
  exact p22566
theorem n22568 (_v : Vars) (_q : Query _v) (h2402 : (e2402 _v)) : (e2787 _v) := by
  have p22300 := n22300 _v _q 
  have p22567 := n22567 _v _q 
  have p8591 := n8591 _v _q h2402
  have p5257 := n5257 _v _q 
  exact FloorCertificate.node_22568 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p22300 p22567 p8591 p5257
theorem n22569 (_v : Vars) (_q : Query _v) (h2402 : (e2402 _v)) : (e7927 _v) := by
  have p14855 := n14855 _v _q 
  have p22568 := n22568 _v _q h2402
  change (¬ (e2787 _v)) ∨ (¬ (e7921 _v)) at p14855
  rcases p14855 with hlit | hlit
  · exact (False.elim (hlit p22568))
  · exact hlit
theorem n22570 (_v : Vars) (_q : Query _v)  : (e4616 _v) := by
  have p14684 := n14684 _v _q 
  have p22567 := n22567 _v _q 
  change (¬ (e2179 _v)) ∨ (¬ (e3162 _v)) at p14684
  rcases p14684 with hlit | hlit
  · exact (False.elim (hlit p22567))
  · exact hlit
theorem n22571 (_v : Vars) (_q : Query _v)  : (e3158 _v) := by
  have p15126 := n15126 _v _q 
  have p22570 := n22570 _v _q 
  change (e3162 _v) ∨ (e3158 _v) at p15126
  change (¬ (e3162 _v)) at p22570
  rcases p15126 with hlit | hlit
  · exact (False.elim (p22570 hlit))
  · exact hlit
theorem n22572 (_v : Vars) (_q : Query _v) (h5195 : (e5195 _v)) : (e7489 _v) := by
  have p12926 := n12926 _v _q h5195
  have p22302 := n22302 _v _q 
  have p16674 := n16674 _v _q h5195
  have p22567 := n22567 _v _q 
  have p22298 := n22298 _v _q 
  exact FloorCertificate.node_22572 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e61 _v) p12926 p22302 p16674 p22567 p22298
theorem n22573 (_v : Vars) (_q : Query _v) (h8038 : (e8038 _v)) : (e7489 _v) := by
  have p8602 := n8602 _v _q h8038
  have p22567 := n22567 _v _q 
  have p22300 := n22300 _v _q 
  exact FloorCertificate.node_22573 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) p8602 p22567 p22300
theorem n22574 (_v : Vars) (_q : Query _v)  : (e2475 _v) := by
  by_contra hc
  change ¬ (e2475 _v) at hc
  have h8038 : (e8038 _v) := (fun hn => hc hn)
  have p22573 := n22573 _v _q h8038
  exact p22573
theorem n22575 (_v : Vars) (_q : Query _v) (h2402 : (e2402 _v)) : (e4419 _v) := by
  have p16347 := n16347 _v _q 
  have p22569 := n22569 _v _q h2402
  change (e7921 _v) ∨ (e4419 _v) at p16347
  change (¬ (e7921 _v)) at p22569
  rcases p16347 with hlit | hlit
  · exact (False.elim (p22569 hlit))
  · exact hlit
theorem n22576 (_v : Vars) (_q : Query _v)  : (e196 _v) := by
  by_contra hc
  change ¬ (e196 _v) at hc
  have h5195 : (e5195 _v) := (fun hn => hc hn)
  have p22572 := n22572 _v _q h5195
  exact p22572
theorem n22577 (_v : Vars) (_q : Query _v)  : (e5203 _v) := by
  have p14730 := n14730 _v _q 
  have p22576 := n22576 _v _q 
  change (¬ (e196 _v)) ∨ (¬ (e5193 _v)) at p14730
  rcases p14730 with hlit | hlit
  · exact (False.elim (hlit p22576))
  · exact hlit
theorem n22578 (_v : Vars) (_q : Query _v)  : (e191 _v) := by
  have p16442 := n16442 _v _q 
  have p22577 := n22577 _v _q 
  change (e5193 _v) ∨ (e191 _v) at p16442
  change (¬ (e5193 _v)) at p22577
  rcases p16442 with hlit | hlit
  · exact (False.elim (p22577 hlit))
  · exact hlit
theorem n22579 (_v : Vars) (_q : Query _v) (h6772 : (e6772 _v)) : (e7807 _v) := by
  have p8461 := n8461 _v _q 
  have p8458 := n8458 _v _q h6772
  have p22574 := n22574 _v _q 
  change (¬ (e2475 _v)) ∨ (¬ (e2303 _v)) ∨ (e2787 _v) at p8461
  change (¬ (e2787 _v)) at p8458
  rcases p8461 with hlit | hlit | hlit
  · exact (False.elim (hlit p22574))
  · exact hlit
  · exact (False.elim (p8458 hlit))
theorem n22580 (_v : Vars) (_q : Query _v) (h6772 : (e6772 _v)) : (e5093 _v) := by
  have p11468 := n11468 _v _q 
  have p22579 := n22579 _v _q h6772
  change (¬ (e13 _v)) ∨ (e2303 _v) at p11468
  change (¬ (e2303 _v)) at p22579
  rcases p11468 with hlit | hlit
  · exact hlit
  · exact (False.elim (p22579 hlit))
theorem n22581 (_v : Vars) (_q : Query _v)  : (e8035 _v) := by
  have p14871 := n14871 _v _q 
  have p22574 := n22574 _v _q 
  change (¬ (e2475 _v)) ∨ (¬ (e8029 _v)) at p14871
  rcases p14871 with hlit | hlit
  · exact (False.elim (hlit p22574))
  · exact hlit
end
end Assembly
