import Dag271
import generated.th_lemma_37
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n22437 (_v : Vars) (_q : Query _v) (h2303 : (e2303 _v)) (h3937 : (e3937 _v)) (h4608 : (e4608 _v)) (h6676 : (e6676 _v)) (h7749 : (e7749 _v)) : (e5093 _v) := by
  have p14728 := n14728 _v _q 
  have p22431 := n22431 _v _q h2303 h3937 h4608 h6676 h7749
  change (¬ (e13 _v)) ∨ (¬ (e5089 _v)) at p14728
  rcases p14728 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p22431))
theorem n22438 (_v : Vars) (_q : Query _v) (h2303 : (e2303 _v)) (h3937 : (e3937 _v)) (h4608 : (e4608 _v)) (h6676 : (e6676 _v)) (h7749 : (e7749 _v)) : (e5105 _v) := by
  have p15204 := n15204 _v _q 
  have p22437 := n22437 _v _q h2303 h3937 h4608 h6676 h7749
  change (e13 _v) ∨ (¬ (e5104 _v)) at p15204
  change (¬ (e13 _v)) at p22437
  rcases p15204 with hlit | hlit
  · exact (False.elim (p22437 hlit))
  · exact hlit
theorem n22439 (_v : Vars) (_q : Query _v) (h2303 : (e2303 _v)) (h3937 : (e3937 _v)) (h4608 : (e4608 _v)) (h6676 : (e6676 _v)) (h7749 : (e7749 _v)) : (e5100 _v) := by
  have p15319 := n15319 _v _q 
  have p22438 := n22438 _v _q h2303 h3937 h4608 h6676 h7749
  change (e5104 _v) ∨ (e5100 _v) at p15319
  change (¬ (e5104 _v)) at p22438
  rcases p15319 with hlit | hlit
  · exact (False.elim (p22438 hlit))
  · exact hlit
theorem n22440 (_v : Vars) (_q : Query _v) (h6501 : (e6501 _v)) : (e7754 _v) := by
  have p14942 := n14942 _v _q 
  have p22434 := n22434 _v _q h6501
  change (e2132 _v) ∨ (¬ (e7753 _v)) at p14942
  change (¬ (e2132 _v)) at p22434
  rcases p14942 with hlit | hlit
  · exact (False.elim (p22434 hlit))
  · exact hlit
theorem n22441 (_v : Vars) (_q : Query _v) (h6501 : (e6501 _v)) : (e7749 _v) := by
  have p14941 := n14941 _v _q 
  have p22440 := n22440 _v _q h6501
  change (e7753 _v) ∨ (e7749 _v) at p14941
  change (¬ (e7753 _v)) at p22440
  rcases p14941 with hlit | hlit
  · exact (False.elim (p22440 hlit))
  · exact hlit
theorem n22442 (_v : Vars) (_q : Query _v) (h3937 : (e3937 _v)) (h4139 : (e4139 _v)) (h4285 : (e4285 _v)) (h4306 : (e4306 _v)) (h4608 : (e4608 _v)) (h7749 : (e7749 _v)) (h7935 : (e7935 _v)) (h8038 : (e8038 _v)) : (e7489 _v) := by
  have p8602 := n8602 _v _q h8038
  have p258 := n258 _v _q 
  have p22302 := n22302 _v _q 
  have p15571 := n15571 _v _q h8038
  have p22298 := n22298 _v _q 
  have p22429 := n22429 _v _q h3937 h4306 h4608 h7749
  have p22358 := n22358 _v _q h3937 h4608 h8038
  have p22436 := n22436 _v _q h3937 h4306 h4608 h7749
  have p4977 := n4977 _v _q h4285
  have p4979 := n4979 _v _q h4139
  have p17100 := n17100 _v _q 
  have p22322 := n22322 _v _q 
  have p17163 := n17163 _v _q h7935
  have p16977 := n16977 _v _q 
  have p19045 := n19045 _v _q h8038
  have p17091 := n17091 _v _q 
  have p17102 := n17102 _v _q 
  have p17138 := n17138 _v _q h4306
  have p17141 := n17141 _v _q 
  have p15209 := n15209 _v _q h8038
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
  exact FloorCertificate.node_22442 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e61 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2863 _v) (e2877 _v) (e2883 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p8602 p258 p22302 p15571 p22298 p22429 p22358 p22436 p4977 p4979 p17100 p22322 p17163 p16977 p19045 p17091 p17102 p17138 p17141 p15209 p22416 p4996 p17147 p16269 p22407 p17124 p22341 p22324 p19610 p13951 p4991 p16576 p22368 p22323 p17758 p22320 p17115 p17078 p17117 p17113 p20467 p17133 p17120 p17009 p22321 p17089 p22318 p22347 p17104 p20470 p20274 p19665 p16778 p17127 p17050 p17122 p17096 p20126 p20426 p17110 p20829 p20653 p17111 p17131 p17108 p17294 p16943 p17064 p17067 p17080 p17053 p17072 p17074 p17069 p20096 p20836 p20461 p17874 p17136 p17087 p17055 p17058 p17098 p17083 p17106 p17020 p17093
theorem n22443 (_v : Vars) (_q : Query _v) (h2303 : (e2303 _v)) (h3937 : (e3937 _v)) (h4608 : (e4608 _v)) (h6676 : (e6676 _v)) (h7749 : (e7749 _v)) : (e7489 _v) := by
  have p22366 := n22366 _v _q 
  have p22439 := n22439 _v _q h2303 h3937 h4608 h6676 h7749
  have p17091 := n17091 _v _q 
  have p22329 := n22329 _v _q 
  have p16911 := n16911 _v _q 
  have p10893 := n10893 _v _q 
  have p16913 := n16913 _v _q 
  have p16436 := n16436 _v _q h2303
  have p16994 := n16994 _v _q 
  have p15342 := n15342 _v _q h6676
  have p10943 := n10943 _v _q h6676
  have p16439 := n16439 _v _q h2303
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
  have p22383 := n22383 _v _q h2303 h6676
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
  exact FloorCertificate.node_22443 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e61 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2863 _v) (e2877 _v) (e2883 _v) (e2898 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p22366 p22439 p17091 p22329 p16911 p10893 p16913 p16436 p16994 p15342 p10943 p16439 p22380 p22357 p22416 p4996 p17147 p16269 p22407 p17124 p22341 p22324 p19610 p13951 p4991 p16576 p22368 p22323 p22383 p22302 p17758 p22320 p17115 p17078 p17117 p17113 p20467 p17133 p17120 p17009 p22321 p17089 p22318 p22347 p17104 p20470 p20274 p19665 p16778 p17127 p17050 p17122 p17096 p20126 p20426 p17110 p20829 p20653 p17111 p17131 p17108 p17294 p16943 p17064 p17067 p17080 p17053 p17072 p17074 p17069 p20096 p20836 p20461 p17874 p17136 p17087 p17055 p17058 p17098 p17083 p17106 p17020 p17093 p22322 p17100 p17141 p17102
theorem n22445 (_v : Vars) (_q : Query _v)  : (e22444 _v) := by
  by_contra hc
  change ¬ ((¬ (e7935 _v)) ∨ (e2475 _v) ∨ (¬ (e4285 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e7749 _v)) ∨ (¬ (e4608 _v))) at hc
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h4139 : (e4139 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4285 : (e4285 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4608 : (e4608 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))))
  have h7749 : (e7749 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h7935 : (e7935 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h8038 : (e8038 _v) := (fun hn => hc (Or.inr (Or.inl hn)))
  have p22442 := n22442 _v _q h3937 h4139 h4285 h4306 h4608 h7749 h7935 h8038
  exact p22442
theorem n22447 (_v : Vars) (_q : Query _v)  : (e22446 _v) := by
  by_contra hc
  change ¬ ((¬ (e2303 _v)) ∨ (e2585 _v) ∨ (¬ (e3937 _v)) ∨ (¬ (e7749 _v)) ∨ (¬ (e4608 _v))) at hc
  have h2303 : (e2303 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4608 : (e4608 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr hn)))))
  have h6676 : (e6676 _v) := (fun hn => hc (Or.inr (Or.inl hn)))
  have h7749 : (e7749 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have p22443 := n22443 _v _q h2303 h3937 h4608 h6676 h7749
  exact p22443
theorem n22448 (_v : Vars) (_q : Query _v) (h3937 : (e3937 _v)) (h4139 : (e4139 _v)) (h4285 : (e4285 _v)) (h4306 : (e4306 _v)) (h4608 : (e4608 _v)) (h7749 : (e7749 _v)) (h8038 : (e8038 _v)) : (e7943 _v) := by
  have p22445 := n22445 _v _q 
  have p8602 := n8602 _v _q h8038
  have p4977 := n4977 _v _q h4285
  have p4979 := n4979 _v _q h4139
  have p17138 := n17138 _v _q h4306
  have p4996 := n4996 _v _q h3937
  have p16269 := n16269 _v _q h7749
  have p4991 := n4991 _v _q h4608
  change (¬ (e7935 _v)) ∨ (e2475 _v) ∨ (¬ (e4285 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e7749 _v)) ∨ (¬ (e4608 _v)) at p22445
  change (¬ (e2475 _v)) at p8602
  rcases p22445 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (p8602 hlit))
  · exact (False.elim (hlit p4977))
  · exact (False.elim (hlit p4979))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p4996))
  · exact (False.elim (hlit p16269))
  · exact (False.elim (hlit p4991))
theorem n22449 (_v : Vars) (_q : Query _v) (h3937 : (e3937 _v)) (h4139 : (e4139 _v)) (h4285 : (e4285 _v)) (h4306 : (e4306 _v)) (h4608 : (e4608 _v)) (h7749 : (e7749 _v)) (h8038 : (e8038 _v)) : (e7944 _v) := by
  have p15266 := n15266 _v _q 
  have p22448 := n22448 _v _q h3937 h4139 h4285 h4306 h4608 h7749 h8038
  change (e7944 _v) ∨ (e7935 _v) at p15266
  change (¬ (e7935 _v)) at p22448
  rcases p15266 with hlit | hlit
  · exact hlit
  · exact (False.elim (p22448 hlit))
theorem n22450 (_v : Vars) (_q : Query _v) (h6501 : (e6501 _v)) (h6676 : (e6676 _v)) : (e7749 _v) := by
  have p14941 := n14941 _v _q 
  have p22421 := n22421 _v _q h6501 h6676
  change (e7753 _v) ∨ (e7749 _v) at p14941
  change (¬ (e7753 _v)) at p22421
  rcases p14941 with hlit | hlit
  · exact (False.elim (p22421 hlit))
  · exact hlit
theorem n22451 (_v : Vars) (_q : Query _v) (h6501 : (e6501 _v)) (h6676 : (e6676 _v)) : (e7807 _v) := by
  have p22447 := n22447 _v _q 
  have p10943 := n10943 _v _q h6676
  have p16325 := n16325 _v _q h6501
  have p22450 := n22450 _v _q h6501 h6676
  have p15641 := n15641 _v _q h6501
  change (¬ (e2303 _v)) ∨ (e2585 _v) ∨ (¬ (e3937 _v)) ∨ (¬ (e7749 _v)) ∨ (¬ (e4608 _v)) at p22447
  change (¬ (e2585 _v)) at p10943
  rcases p22447 with hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (p10943 hlit))
  · exact (False.elim (hlit p16325))
  · exact (False.elim (hlit p22450))
  · exact (False.elim (hlit p15641))
theorem n22452 (_v : Vars) (_q : Query _v) (h3937 : (e3937 _v)) (h4608 : (e4608 _v)) (h6676 : (e6676 _v)) (h7749 : (e7749 _v)) : (e7807 _v) := by
  have p22447 := n22447 _v _q 
  have p10943 := n10943 _v _q h6676
  have p4996 := n4996 _v _q h3937
  have p16269 := n16269 _v _q h7749
  have p4991 := n4991 _v _q h4608
  change (¬ (e2303 _v)) ∨ (e2585 _v) ∨ (¬ (e3937 _v)) ∨ (¬ (e7749 _v)) ∨ (¬ (e4608 _v)) at p22447
  change (¬ (e2585 _v)) at p10943
  rcases p22447 with hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (p10943 hlit))
  · exact (False.elim (hlit p4996))
  · exact (False.elim (hlit p16269))
  · exact (False.elim (hlit p4991))
theorem n22453 (_v : Vars) (_q : Query _v) (h3937 : (e3937 _v)) (h4139 : (e4139 _v)) (h4285 : (e4285 _v)) (h4306 : (e4306 _v)) (h4608 : (e4608 _v)) (h7749 : (e7749 _v)) (h8038 : (e8038 _v)) : (e2787 _v) := by
  have p15228 := n15228 _v _q 
  have p22449 := n22449 _v _q h3937 h4139 h4285 h4306 h4608 h7749 h8038
  change (e2787 _v) ∨ (¬ (e7944 _v)) at p15228
  rcases p15228 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p22449))
theorem n22454 (_v : Vars) (_q : Query _v) (h3937 : (e3937 _v)) (h4139 : (e4139 _v)) (h4285 : (e4285 _v)) (h4306 : (e4306 _v)) (h4608 : (e4608 _v)) (h7749 : (e7749 _v)) (h8038 : (e8038 _v)) : (e7927 _v) := by
  have p14855 := n14855 _v _q 
  have p22453 := n22453 _v _q h3937 h4139 h4285 h4306 h4608 h7749 h8038
  change (¬ (e2787 _v)) ∨ (¬ (e7921 _v)) at p14855
  rcases p14855 with hlit | hlit
  · exact (False.elim (hlit p22453))
  · exact hlit
theorem n22455 (_v : Vars) (_q : Query _v) (h6501 : (e6501 _v)) (h6676 : (e6676 _v)) : (e5093 _v) := by
  have p11468 := n11468 _v _q 
  have p22451 := n22451 _v _q h6501 h6676
  change (¬ (e13 _v)) ∨ (e2303 _v) at p11468
  change (¬ (e2303 _v)) at p22451
  rcases p11468 with hlit | hlit
  · exact hlit
  · exact (False.elim (p22451 hlit))
theorem n22456 (_v : Vars) (_q : Query _v) (h6501 : (e6501 _v)) (h6676 : (e6676 _v)) : (e5105 _v) := by
  have p15204 := n15204 _v _q 
  have p22455 := n22455 _v _q h6501 h6676
  change (e13 _v) ∨ (¬ (e5104 _v)) at p15204
  change (¬ (e13 _v)) at p22455
  rcases p15204 with hlit | hlit
  · exact (False.elim (p22455 hlit))
  · exact hlit
theorem n22457 (_v : Vars) (_q : Query _v) (h6501 : (e6501 _v)) (h6676 : (e6676 _v)) : (e5100 _v) := by
  have p15319 := n15319 _v _q 
  have p22456 := n22456 _v _q h6501 h6676
  change (e5104 _v) ∨ (e5100 _v) at p15319
  change (¬ (e5104 _v)) at p22456
  rcases p15319 with hlit | hlit
  · exact (False.elim (p22456 hlit))
  · exact hlit
theorem n22458 (_v : Vars) (_q : Query _v) (h6501 : (e6501 _v)) (h6676 : (e6676 _v)) : (e7819 _v) := by
  have p14994 := n14994 _v _q 
  have p22451 := n22451 _v _q h6501 h6676
  change (e2303 _v) ∨ (¬ (e7818 _v)) at p14994
  change (¬ (e2303 _v)) at p22451
  rcases p14994 with hlit | hlit
  · exact (False.elim (p22451 hlit))
  · exact hlit
theorem n22459 (_v : Vars) (_q : Query _v) (h6501 : (e6501 _v)) (h6676 : (e6676 _v)) : (e7814 _v) := by
  have p15221 := n15221 _v _q 
  have p22458 := n22458 _v _q h6501 h6676
  change (e7818 _v) ∨ (e7814 _v) at p15221
  change (¬ (e7818 _v)) at p22458
  rcases p15221 with hlit | hlit
  · exact (False.elim (p22458 hlit))
  · exact hlit
theorem n22460 (_v : Vars) (_q : Query _v) (h6501 : (e6501 _v)) (h6676 : (e6676 _v)) : (e6746 _v) := by
  have p11429 := n11429 _v _q 
  have p22451 := n22451 _v _q h6501 h6676
  change (¬ (e2740 _v)) ∨ (e2303 _v) at p11429
  change (¬ (e2303 _v)) at p22451
  rcases p11429 with hlit | hlit
  · exact hlit
  · exact (False.elim (p22451 hlit))
theorem n22461 (_v : Vars) (_q : Query _v) (h6501 : (e6501 _v)) (h6676 : (e6676 _v)) : (e6724 _v) := by
  have p11461 := n11461 _v _q 
  have p22460 := n22460 _v _q h6501 h6676
  change (¬ (e2691 _v)) ∨ (e2740 _v) at p11461
  change (¬ (e2740 _v)) at p22460
  rcases p11461 with hlit | hlit
  · exact hlit
  · exact (False.elim (p22460 hlit))
theorem n22462 (_v : Vars) (_q : Query _v) (h6501 : (e6501 _v)) (h6676 : (e6676 _v)) : (e7517 _v) := by
  have p15196 := n15196 _v _q 
  have p22461 := n22461 _v _q h6501 h6676
  change (e2691 _v) ∨ (¬ (e7497 _v)) at p15196
  change (¬ (e2691 _v)) at p22461
  rcases p15196 with hlit | hlit
  · exact (False.elim (p22461 hlit))
  · exact hlit
theorem n22463 (_v : Vars) (_q : Query _v) (h3937 : (e3937 _v)) (h4608 : (e4608 _v)) (h6676 : (e6676 _v)) (h7749 : (e7749 _v)) : (e5093 _v) := by
  have p11468 := n11468 _v _q 
  have p22452 := n22452 _v _q h3937 h4608 h6676 h7749
  change (¬ (e13 _v)) ∨ (e2303 _v) at p11468
  change (¬ (e2303 _v)) at p22452
  rcases p11468 with hlit | hlit
  · exact hlit
  · exact (False.elim (p22452 hlit))
theorem n22464 (_v : Vars) (_q : Query _v) (h3937 : (e3937 _v)) (h4608 : (e4608 _v)) (h6676 : (e6676 _v)) (h7749 : (e7749 _v)) : (e5105 _v) := by
  have p15204 := n15204 _v _q 
  have p22463 := n22463 _v _q h3937 h4608 h6676 h7749
  change (e13 _v) ∨ (¬ (e5104 _v)) at p15204
  change (¬ (e13 _v)) at p22463
  rcases p15204 with hlit | hlit
  · exact (False.elim (p22463 hlit))
  · exact hlit
theorem n22465 (_v : Vars) (_q : Query _v) (h3937 : (e3937 _v)) (h4608 : (e4608 _v)) (h6676 : (e6676 _v)) (h7749 : (e7749 _v)) : (e5100 _v) := by
  have p15319 := n15319 _v _q 
  have p22464 := n22464 _v _q h3937 h4608 h6676 h7749
  change (e5104 _v) ∨ (e5100 _v) at p15319
  change (¬ (e5104 _v)) at p22464
  rcases p15319 with hlit | hlit
  · exact (False.elim (p22464 hlit))
  · exact hlit
theorem n22466 (_v : Vars) (_q : Query _v) (h3937 : (e3937 _v)) (h4608 : (e4608 _v)) (h6676 : (e6676 _v)) (h7749 : (e7749 _v)) : (e7819 _v) := by
  have p14994 := n14994 _v _q 
  have p22452 := n22452 _v _q h3937 h4608 h6676 h7749
  change (e2303 _v) ∨ (¬ (e7818 _v)) at p14994
  change (¬ (e2303 _v)) at p22452
  rcases p14994 with hlit | hlit
  · exact (False.elim (p22452 hlit))
  · exact hlit
theorem n22467 (_v : Vars) (_q : Query _v) (h3937 : (e3937 _v)) (h4608 : (e4608 _v)) (h6676 : (e6676 _v)) (h7749 : (e7749 _v)) : (e7814 _v) := by
  have p15221 := n15221 _v _q 
  have p22466 := n22466 _v _q h3937 h4608 h6676 h7749
  change (e7818 _v) ∨ (e7814 _v) at p15221
  change (¬ (e7818 _v)) at p22466
  rcases p15221 with hlit | hlit
  · exact (False.elim (p22466 hlit))
  · exact hlit
theorem n22468 (_v : Vars) (_q : Query _v) (h3937 : (e3937 _v)) (h4608 : (e4608 _v)) (h6676 : (e6676 _v)) (h7749 : (e7749 _v)) : (e6746 _v) := by
  have p11429 := n11429 _v _q 
  have p22452 := n22452 _v _q h3937 h4608 h6676 h7749
  change (¬ (e2740 _v)) ∨ (e2303 _v) at p11429
  change (¬ (e2303 _v)) at p22452
  rcases p11429 with hlit | hlit
  · exact hlit
  · exact (False.elim (p22452 hlit))
theorem n22469 (_v : Vars) (_q : Query _v) (h3937 : (e3937 _v)) (h4608 : (e4608 _v)) (h6676 : (e6676 _v)) (h7749 : (e7749 _v)) : (e6724 _v) := by
  have p11461 := n11461 _v _q 
  have p22468 := n22468 _v _q h3937 h4608 h6676 h7749
  change (¬ (e2691 _v)) ∨ (e2740 _v) at p11461
  change (¬ (e2740 _v)) at p22468
  rcases p11461 with hlit | hlit
  · exact hlit
  · exact (False.elim (p22468 hlit))
theorem n22470 (_v : Vars) (_q : Query _v) (h3937 : (e3937 _v)) (h4608 : (e4608 _v)) (h6676 : (e6676 _v)) (h7749 : (e7749 _v)) : (e7517 _v) := by
  have p15196 := n15196 _v _q 
  have p22469 := n22469 _v _q h3937 h4608 h6676 h7749
  change (e2691 _v) ∨ (¬ (e7497 _v)) at p15196
  change (¬ (e2691 _v)) at p22469
  rcases p15196 with hlit | hlit
  · exact (False.elim (p22469 hlit))
  · exact hlit
theorem n22471 (_v : Vars) (_q : Query _v) (h3937 : (e3937 _v)) (h4139 : (e4139 _v)) (h4285 : (e4285 _v)) (h4306 : (e4306 _v)) (h4608 : (e4608 _v)) (h7749 : (e7749 _v)) (h8038 : (e8038 _v)) : (e4419 _v) := by
  have p16347 := n16347 _v _q 
  have p22454 := n22454 _v _q h3937 h4139 h4285 h4306 h4608 h7749 h8038
  change (e7921 _v) ∨ (e4419 _v) at p16347
  change (¬ (e7921 _v)) at p22454
  rcases p16347 with hlit | hlit
  · exact (False.elim (p22454 hlit))
  · exact hlit
theorem n22472 (_v : Vars) (_q : Query _v) (h3937 : (e3937 _v)) (h4608 : (e4608 _v)) (h6676 : (e6676 _v)) (h7749 : (e7749 _v)) : (e7493 _v) := by
  have p15195 := n15195 _v _q 
  have p22470 := n22470 _v _q h3937 h4608 h6676 h7749
  change (e7497 _v) ∨ (e7493 _v) at p15195
  change (¬ (e7497 _v)) at p22470
  rcases p15195 with hlit | hlit
  · exact (False.elim (p22470 hlit))
  · exact hlit
theorem n22473 (_v : Vars) (_q : Query _v) (h3937 : (e3937 _v)) (h4608 : (e4608 _v)) (h6676 : (e6676 _v)) (h7749 : (e7749 _v)) (h7935 : (e7935 _v)) : (e7489 _v) := by
  have p10893 := n10893 _v _q 
  have p10943 := n10943 _v _q h6676
  have p22366 := n22366 _v _q 
  have p10896 := n10896 _v _q 
  have p22329 := n22329 _v _q 
  have p17163 := n17163 _v _q h7935
  have p16977 := n16977 _v _q 
  have p22465 := n22465 _v _q h3937 h4608 h6676 h7749
  have p17091 := n17091 _v _q 
  have p22467 := n22467 _v _q h3937 h4608 h6676 h7749
  have p22472 := n22472 _v _q h3937 h4608 h6676 h7749
  have p17102 := n17102 _v _q 
  have p16994 := n16994 _v _q 
  have p15342 := n15342 _v _q h6676
  have p17141 := n17141 _v _q 
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
  have p17256 := n17256 _v _q 
  exact FloorCertificate.node_22473 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e61 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2863 _v) (e2877 _v) (e2883 _v) (e2898 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p10893 p10943 p22366 p10896 p22329 p17163 p16977 p22465 p17091 p22467 p22472 p17102 p16994 p15342 p17141 p22380 p22357 p22416 p4996 p17147 p16269 p22407 p17124 p22341 p22324 p19610 p13951 p4991 p16576 p22368 p22323 p22302 p17758 p22320 p17115 p17078 p17117 p17113 p20467 p17133 p17120 p17009 p22321 p17089 p22318 p22347 p17104 p20470 p20274 p19665 p16778 p17127 p17050 p17122 p17096 p20126 p20426 p17110 p20829 p20653 p17111 p17131 p17108 p17294 p16943 p17064 p17067 p17080 p17053 p17072 p17074 p17069 p20096 p20836 p20461 p17874 p17136 p17087 p17055 p17058 p17098 p17083 p17106 p17020 p17093 p22322 p17100 p17256
theorem n22474 (_v : Vars) (_q : Query _v) (h3937 : (e3937 _v)) (h4608 : (e4608 _v)) (h6571 : (e6571 _v)) (h6676 : (e6676 _v)) (h7749 : (e7749 _v)) : (e7489 _v) := by
  have p17255 := n17255 _v _q h6571
  have p16977 := n16977 _v _q 
  have p22329 := n22329 _v _q 
  have p10943 := n10943 _v _q h6676
  have p22366 := n22366 _v _q 
  have p22465 := n22465 _v _q h3937 h4608 h6676 h7749
  have p17091 := n17091 _v _q 
  have p22467 := n22467 _v _q h3937 h4608 h6676 h7749
  have p10893 := n10893 _v _q 
  have p22472 := n22472 _v _q h3937 h4608 h6676 h7749
  have p17102 := n17102 _v _q 
  have p16994 := n16994 _v _q 
  have p15342 := n15342 _v _q h6676
  have p17141 := n17141 _v _q 
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
  have p17256 := n17256 _v _q 
  have p8447 := n8447 _v _q h6571
  exact FloorCertificate.node_22474 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e61 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2863 _v) (e2877 _v) (e2883 _v) (e2898 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p17255 p16977 p22329 p10943 p22366 p22465 p17091 p22467 p10893 p22472 p17102 p16994 p15342 p17141 p22380 p22357 p22416 p4996 p17147 p16269 p22407 p17124 p22341 p22324 p19610 p13951 p4991 p16576 p22368 p22323 p22302 p17758 p22320 p17115 p17078 p17117 p17113 p20467 p17133 p17120 p17009 p22321 p17089 p22318 p22347 p17104 p20470 p20274 p19665 p16778 p17127 p17050 p17122 p17096 p20126 p20426 p17110 p20829 p20653 p17111 p17131 p17108 p17294 p16943 p17064 p17067 p17080 p17053 p17072 p17074 p17069 p20096 p20836 p20461 p17874 p17136 p17087 p17055 p17058 p17098 p17083 p17106 p17020 p17093 p22322 p17100 p17256 p8447
theorem n22475 (_v : Vars) (_q : Query _v) (h3937 : (e3937 _v)) (h4139 : (e4139 _v)) (h4285 : (e4285 _v)) (h4306 : (e4306 _v)) (h4608 : (e4608 _v)) (h7749 : (e7749 _v)) (h8038 : (e8038 _v)) : (e7489 _v) := by
  have p17093 := n17093 _v _q 
  have p22358 := n22358 _v _q h3937 h4608 h8038
  have p22471 := n22471 _v _q h3937 h4139 h4285 h4306 h4608 h7749 h8038
  have p22436 := n22436 _v _q h3937 h4306 h4608 h7749
  have p13951 := n13951 _v _q 
  have p4977 := n4977 _v _q h4285
  have p4979 := n4979 _v _q h4139
  have p17100 := n17100 _v _q 
  have p22322 := n22322 _v _q 
  have p16977 := n16977 _v _q 
  have p19045 := n19045 _v _q h8038
  have p17091 := n17091 _v _q 
  have p15571 := n15571 _v _q h8038
  have p17102 := n17102 _v _q 
  have p17138 := n17138 _v _q h4306
  have p17141 := n17141 _v _q 
  have p22298 := n22298 _v _q 
  have p15209 := n15209 _v _q h8038
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
  have p8602 := n8602 _v _q h8038
  have p5391 := n5391 _v _q 
  exact FloorCertificate.node_22475 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e61 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2863 _v) (e2877 _v) (e2883 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p17093 p22358 p22471 p22436 p13951 p4977 p4979 p17100 p22322 p16977 p19045 p17091 p15571 p17102 p17138 p17141 p22298 p15209 p22416 p4996 p17147 p16269 p22407 p17124 p22341 p22324 p19610 p17020 p4991 p16576 p22368 p22323 p22302 p17758 p22320 p17115 p17078 p17117 p17113 p20467 p17133 p17120 p17009 p22321 p17089 p22318 p22347 p17104 p20470 p20274 p19665 p16778 p17127 p17050 p17122 p17096 p20126 p20426 p17110 p20829 p20653 p17111 p17131 p17108 p17294 p16943 p17064 p17067 p17080 p17053 p17072 p17074 p17069 p20096 p20836 p20461 p17874 p17136 p17087 p17055 p17058 p17098 p17083 p17106 p8602 p5391
theorem n22477 (_v : Vars) (_q : Query _v)  : (e22476 _v) := by
  by_contra hc
  change ¬ ((¬ (e7935 _v)) ∨ (e2585 _v) ∨ (¬ (e3937 _v)) ∨ (¬ (e7749 _v)) ∨ (¬ (e4608 _v))) at hc
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4608 : (e4608 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr hn)))))
  have h6676 : (e6676 _v) := (fun hn => hc (Or.inr (Or.inl hn)))
  have h7749 : (e7749 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h7935 : (e7935 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have p22473 := n22473 _v _q h3937 h4608 h6676 h7749 h7935
  exact p22473
theorem n22479 (_v : Vars) (_q : Query _v)  : (e22478 _v) := by
  by_contra hc
  change ¬ ((e2358 _v) ∨ (e2585 _v) ∨ (¬ (e3937 _v)) ∨ (¬ (e7749 _v)) ∨ (¬ (e4608 _v))) at hc
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4608 : (e4608 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr hn)))))
  have h6571 : (e6571 _v) := (fun hn => hc (Or.inl hn))
  have h6676 : (e6676 _v) := (fun hn => hc (Or.inr (Or.inl hn)))
  have h7749 : (e7749 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have p22474 := n22474 _v _q h3937 h4608 h6571 h6676 h7749
  exact p22474
theorem n22481 (_v : Vars) (_q : Query _v)  : (e22480 _v) := by
  by_contra hc
  change ¬ ((e2475 _v) ∨ (¬ (e4285 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e7749 _v)) ∨ (¬ (e4608 _v))) at hc
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4139 : (e4139 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4285 : (e4285 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4608 : (e4608 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn)))))))
  have h7749 : (e7749 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h8038 : (e8038 _v) := (fun hn => hc (Or.inl hn))
  have p22475 := n22475 _v _q h3937 h4139 h4285 h4306 h4608 h7749 h8038
  exact p22475
theorem n22482 (_v : Vars) (_q : Query _v) (h6501 : (e6501 _v)) (h6676 : (e6676 _v)) : (e7943 _v) := by
  have p22477 := n22477 _v _q 
  have p10943 := n10943 _v _q h6676
  have p16325 := n16325 _v _q h6501
  have p22450 := n22450 _v _q h6501 h6676
  have p15641 := n15641 _v _q h6501
  change (¬ (e7935 _v)) ∨ (e2585 _v) ∨ (¬ (e3937 _v)) ∨ (¬ (e7749 _v)) ∨ (¬ (e4608 _v)) at p22477
  change (¬ (e2585 _v)) at p10943
  rcases p22477 with hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (p10943 hlit))
  · exact (False.elim (hlit p16325))
  · exact (False.elim (hlit p22450))
  · exact (False.elim (hlit p15641))
theorem n22483 (_v : Vars) (_q : Query _v) (h6501 : (e6501 _v)) (h6676 : (e6676 _v)) : (e7944 _v) := by
  have p15266 := n15266 _v _q 
  have p22482 := n22482 _v _q h6501 h6676
  change (e7944 _v) ∨ (e7935 _v) at p15266
  change (¬ (e7935 _v)) at p22482
  rcases p15266 with hlit | hlit
  · exact hlit
  · exact (False.elim (p22482 hlit))
theorem n22484 (_v : Vars) (_q : Query _v) (h6501 : (e6501 _v)) (h6676 : (e6676 _v)) : (e2358 _v) := by
  have p22479 := n22479 _v _q 
  have p10943 := n10943 _v _q h6676
  have p16325 := n16325 _v _q h6501
  have p22450 := n22450 _v _q h6501 h6676
  have p15641 := n15641 _v _q h6501
  change (e2358 _v) ∨ (e2585 _v) ∨ (¬ (e3937 _v)) ∨ (¬ (e7749 _v)) ∨ (¬ (e4608 _v)) at p22479
  change (¬ (e2585 _v)) at p10943
  rcases p22479 with hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (p10943 hlit))
  · exact (False.elim (hlit p16325))
  · exact (False.elim (hlit p22450))
  · exact (False.elim (hlit p15641))
theorem n22485 (_v : Vars) (_q : Query _v) (h6501 : (e6501 _v)) (h6676 : (e6676 _v)) : (e7640 _v) := by
  have p14828 := n14828 _v _q 
  have p22484 := n22484 _v _q h6501 h6676
  change (¬ (e2358 _v)) ∨ (¬ (e7634 _v)) at p14828
  rcases p14828 with hlit | hlit
  · exact (False.elim (hlit p22484))
  · exact hlit
theorem n22486 (_v : Vars) (_q : Query _v) (h3937 : (e3937 _v)) (h4139 : (e4139 _v)) (h4285 : (e4285 _v)) (h4306 : (e4306 _v)) (h4608 : (e4608 _v)) (h7749 : (e7749 _v)) : (e2475 _v) := by
  have p22481 := n22481 _v _q 
  have p4977 := n4977 _v _q h4285
  have p4979 := n4979 _v _q h4139
  have p17138 := n17138 _v _q h4306
  have p4996 := n4996 _v _q h3937
  have p16269 := n16269 _v _q h7749
  have p4991 := n4991 _v _q h4608
  change (e2475 _v) ∨ (¬ (e4285 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e7749 _v)) ∨ (¬ (e4608 _v)) at p22481
  rcases p22481 with hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p4977))
  · exact (False.elim (hlit p4979))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p4996))
  · exact (False.elim (hlit p16269))
  · exact (False.elim (hlit p4991))
end
end Assembly
