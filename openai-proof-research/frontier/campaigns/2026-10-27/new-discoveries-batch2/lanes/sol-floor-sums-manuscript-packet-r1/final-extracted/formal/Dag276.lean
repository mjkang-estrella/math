import Dag275
import generated.th_lemma_37
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n22632 (_v : Vars) (_q : Query _v) (h6676 : (e6676 _v)) : (e5093 _v) := by
  have p22631 := n22631 _v _q 
  have p10943 := n10943 _v _q h6676
  change (¬ (e13 _v)) ∨ (e2585 _v) at p22631
  change (¬ (e2585 _v)) at p10943
  rcases p22631 with hlit | hlit
  · exact hlit
  · exact (False.elim (p10943 hlit))
theorem n22633 (_v : Vars) (_q : Query _v) (h6676 : (e6676 _v)) : (e5105 _v) := by
  have p15204 := n15204 _v _q 
  have p22632 := n22632 _v _q h6676
  change (e13 _v) ∨ (¬ (e5104 _v)) at p15204
  change (¬ (e13 _v)) at p22632
  rcases p15204 with hlit | hlit
  · exact (False.elim (p22632 hlit))
  · exact hlit
theorem n22634 (_v : Vars) (_q : Query _v) (h6676 : (e6676 _v)) : (e5100 _v) := by
  have p15319 := n15319 _v _q 
  have p22633 := n22633 _v _q h6676
  change (e5104 _v) ∨ (e5100 _v) at p15319
  change (¬ (e5104 _v)) at p22633
  rcases p15319 with hlit | hlit
  · exact (False.elim (p22633 hlit))
  · exact hlit
theorem n22635 (_v : Vars) (_q : Query _v) (h6676 : (e6676 _v)) : (e6724 _v) := by
  have p10893 := n10893 _v _q 
  have p22632 := n22632 _v _q h6676
  exact FloorCertificate.node_22635 (e2 _v) (e7 _v) (e9 _v) (e45 _v) p10893 p22632
theorem n22636 (_v : Vars) (_q : Query _v) (h6676 : (e6676 _v)) : (e7517 _v) := by
  have p15196 := n15196 _v _q 
  have p22635 := n22635 _v _q h6676
  change (e2691 _v) ∨ (¬ (e7497 _v)) at p15196
  change (¬ (e2691 _v)) at p22635
  rcases p15196 with hlit | hlit
  · exact (False.elim (p22635 hlit))
  · exact hlit
theorem n22637 (_v : Vars) (_q : Query _v) (h6676 : (e6676 _v)) : (e7493 _v) := by
  have p15195 := n15195 _v _q 
  have p22636 := n22636 _v _q h6676
  change (e7497 _v) ∨ (e7493 _v) at p15195
  change (¬ (e7497 _v)) at p22636
  rcases p15195 with hlit | hlit
  · exact (False.elim (p22636 hlit))
  · exact hlit
theorem n22638 (_v : Vars) (_q : Query _v) (h6676 : (e6676 _v)) (h7814 : (e7814 _v)) : (e7489 _v) := by
  have p10893 := n10893 _v _q 
  have p4951 := n4951 _v _q 
  have p5257 := n5257 _v _q 
  have p17111 := n17111 _v _q 
  have p22637 := n22637 _v _q h6676
  have p10943 := n10943 _v _q h6676
  have p17172 := n17172 _v _q h7814
  have p22634 := n22634 _v _q h6676
  have p16913 := n16913 _v _q 
  have p17131 := n17131 _v _q 
  have p22625 := n22625 _v _q h6676
  have p17108 := n17108 _v _q 
  have p17294 := n17294 _v _q 
  have p22620 := n22620 _v _q h6676
  have p15342 := n15342 _v _q h6676
  have p16994 := n16994 _v _q 
  have p13951 := n13951 _v _q 
  have p17147 := n17147 _v _q 
  have p22612 := n22612 _v _q 
  have p22302 := n22302 _v _q 
  have p17067 := n17067 _v _q 
  have p17072 := n17072 _v _q 
  have p17053 := n17053 _v _q 
  have p17074 := n17074 _v _q 
  have p16943 := n16943 _v _q 
  have p17069 := n17069 _v _q 
  have p20096 := n20096 _v _q 
  have p22571 := n22571 _v _q 
  have p22628 := n22628 _v _q h6676
  have p17064 := n17064 _v _q 
  have p20461 := n20461 _v _q 
  have p17874 := n17874 _v _q 
  have p17136 := n17136 _v _q 
  have p17080 := n17080 _v _q 
  have p17055 := n17055 _v _q 
  have p17058 := n17058 _v _q 
  have p20836 := n20836 _v _q 
  have p22582 := n22582 _v _q 
  have p17083 := n17083 _v _q 
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p17093 := n17093 _v _q 
  have p22585 := n22585 _v _q 
  have p17087 := n17087 _v _q 
  have p17100 := n17100 _v _q 
  have p22322 := n22322 _v _q 
  have p17091 := n17091 _v _q 
  have p17102 := n17102 _v _q 
  have p17141 := n17141 _v _q 
  have p22578 := n22578 _v _q 
  have p22407 := n22407 _v _q 
  have p17124 := n17124 _v _q 
  have p22341 := n22341 _v _q 
  have p22324 := n22324 _v _q 
  have p19610 := n19610 _v _q 
  have p17020 := n17020 _v _q 
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
  have p8663 := n8663 _v _q 
  exact FloorCertificate.node_22638 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e61 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2883 _v) (e2898 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p10893 p4951 p5257 p17111 p22637 p10943 p17172 p22634 p16913 p17131 p22625 p17108 p17294 p22620 p15342 p16994 p13951 p17147 p22612 p22302 p17067 p17072 p17053 p17074 p16943 p17069 p20096 p22571 p22628 p17064 p20461 p17874 p17136 p17080 p17055 p17058 p20836 p22582 p17083 p17098 p17106 p17093 p22585 p17087 p17100 p22322 p17091 p17102 p17141 p22578 p22407 p17124 p22341 p22324 p19610 p17020 p22368 p22323 p17758 p22320 p17115 p17078 p17117 p17113 p20467 p17133 p17120 p17009 p22321 p17089 p22318 p22347 p17104 p20470 p20274 p19665 p16778 p17127 p17050 p17122 p17096 p20126 p20426 p17110 p20829 p20653 p8663
theorem n22640 (_v : Vars) (_q : Query _v)  : (e22639 _v) := by
  by_contra hc
  change ¬ ((¬ (e7814 _v)) ∨ (e2585 _v)) at hc
  have h6676 : (e6676 _v) := (fun hn => hc (Or.inr hn))
  have h7814 : (e7814 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have p22638 := n22638 _v _q h6676 h7814
  exact p22638
theorem n22641 (_v : Vars) (_q : Query _v) (h6676 : (e6676 _v)) : (e7817 _v) := by
  have p22640 := n22640 _v _q 
  have p10943 := n10943 _v _q h6676
  change (¬ (e7814 _v)) ∨ (e2585 _v) at p22640
  change (¬ (e2585 _v)) at p10943
  rcases p22640 with hlit | hlit
  · exact hlit
  · exact (False.elim (p10943 hlit))
theorem n22642 (_v : Vars) (_q : Query _v) (h6676 : (e6676 _v)) : (e7818 _v) := by
  have p15221 := n15221 _v _q 
  have p22641 := n22641 _v _q h6676
  change (e7818 _v) ∨ (e7814 _v) at p15221
  change (¬ (e7814 _v)) at p22641
  rcases p15221 with hlit | hlit
  · exact hlit
  · exact (False.elim (p22641 hlit))
theorem n22643 (_v : Vars) (_q : Query _v) (h6676 : (e6676 _v)) : (e2303 _v) := by
  have p14994 := n14994 _v _q 
  have p22642 := n22642 _v _q h6676
  change (e2303 _v) ∨ (¬ (e7818 _v)) at p14994
  rcases p14994 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p22642))
theorem n22644 (_v : Vars) (_q : Query _v) (h6676 : (e6676 _v)) : (e7804 _v) := by
  have p14837 := n14837 _v _q 
  have p22643 := n22643 _v _q h6676
  change (¬ (e2303 _v)) ∨ (¬ (e7798 _v)) at p14837
  rcases p14837 with hlit | hlit
  · exact (False.elim (hlit p22643))
  · exact hlit
theorem n22645 (_v : Vars) (_q : Query _v) (h6676 : (e6676 _v)) : (e4285 _v) := by
  have p16274 := n16274 _v _q 
  have p22644 := n22644 _v _q h6676
  change (e7798 _v) ∨ (e4285 _v) at p16274
  change (¬ (e7798 _v)) at p22644
  rcases p16274 with hlit | hlit
  · exact (False.elim (p22644 hlit))
  · exact hlit
theorem n22646 (_v : Vars) (_q : Query _v) (h6676 : (e6676 _v)) : (e7489 _v) := by
  have p22634 := n22634 _v _q h6676
  have p10893 := n10893 _v _q 
  have p22637 := n22637 _v _q h6676
  have p16913 := n16913 _v _q 
  have p17111 := n17111 _v _q 
  have p17131 := n17131 _v _q 
  have p10943 := n10943 _v _q h6676
  have p20653 := n20653 _v _q 
  have p22625 := n22625 _v _q h6676
  have p17108 := n17108 _v _q 
  have p17294 := n17294 _v _q 
  have p22610 := n22610 _v _q 
  have p22645 := n22645 _v _q h6676
  have p22620 := n22620 _v _q h6676
  have p15342 := n15342 _v _q h6676
  have p16994 := n16994 _v _q 
  have p13951 := n13951 _v _q 
  have p17147 := n17147 _v _q 
  have p22612 := n22612 _v _q 
  have p22302 := n22302 _v _q 
  have p17067 := n17067 _v _q 
  have p17072 := n17072 _v _q 
  have p17053 := n17053 _v _q 
  have p17074 := n17074 _v _q 
  have p16943 := n16943 _v _q 
  have p17069 := n17069 _v _q 
  have p20096 := n20096 _v _q 
  have p22571 := n22571 _v _q 
  have p22628 := n22628 _v _q h6676
  have p17064 := n17064 _v _q 
  have p20461 := n20461 _v _q 
  have p17874 := n17874 _v _q 
  have p17136 := n17136 _v _q 
  have p17080 := n17080 _v _q 
  have p17055 := n17055 _v _q 
  have p17058 := n17058 _v _q 
  have p20836 := n20836 _v _q 
  have p22582 := n22582 _v _q 
  have p17083 := n17083 _v _q 
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p17093 := n17093 _v _q 
  have p22585 := n22585 _v _q 
  have p17087 := n17087 _v _q 
  have p17100 := n17100 _v _q 
  have p22322 := n22322 _v _q 
  have p17091 := n17091 _v _q 
  have p17102 := n17102 _v _q 
  have p17141 := n17141 _v _q 
  have p22578 := n22578 _v _q 
  have p22407 := n22407 _v _q 
  have p17124 := n17124 _v _q 
  have p22341 := n22341 _v _q 
  have p22324 := n22324 _v _q 
  have p19610 := n19610 _v _q 
  have p17020 := n17020 _v _q 
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
  have p22366 := n22366 _v _q 
  have p22567 := n22567 _v _q 
  have p22643 := n22643 _v _q h6676
  exact FloorCertificate.node_22646 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e61 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2883 _v) (e2898 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p22634 p10893 p22637 p16913 p17111 p17131 p10943 p20653 p22625 p17108 p17294 p22610 p22645 p22620 p15342 p16994 p13951 p17147 p22612 p22302 p17067 p17072 p17053 p17074 p16943 p17069 p20096 p22571 p22628 p17064 p20461 p17874 p17136 p17080 p17055 p17058 p20836 p22582 p17083 p17098 p17106 p17093 p22585 p17087 p17100 p22322 p17091 p17102 p17141 p22578 p22407 p17124 p22341 p22324 p19610 p17020 p22368 p22323 p17758 p22320 p17115 p17078 p17117 p17113 p20467 p17133 p17120 p17009 p22321 p17089 p22318 p22347 p17104 p20470 p20274 p19665 p16778 p17127 p17050 p17122 p17096 p20126 p20426 p17110 p20829 p22366 p22567 p22643
theorem n22647 (_v : Vars) (_q : Query _v)  : (e2585 _v) := by
  by_contra hc
  change ¬ (e2585 _v) at hc
  have h6676 : (e6676 _v) := (fun hn => hc hn)
  have p22646 := n22646 _v _q h6676
  exact p22646
theorem n22648 (_v : Vars) (_q : Query _v)  : (e4314 _v) := by
  have p14704 := n14704 _v _q 
  have p22647 := n22647 _v _q 
  change (¬ (e2585 _v)) ∨ (¬ (e4313 _v)) at p14704
  rcases p14704 with hlit | hlit
  · exact (False.elim (hlit p22647))
  · exact hlit
theorem n22649 (_v : Vars) (_q : Query _v)  : (e4306 _v) := by
  have p14984 := n14984 _v _q 
  have p22648 := n22648 _v _q 
  change (e4313 _v) ∨ (e4306 _v) at p14984
  change (¬ (e4313 _v)) at p22648
  rcases p14984 with hlit | hlit
  · exact (False.elim (p22648 hlit))
  · exact hlit
theorem n22650 (_v : Vars) (_q : Query _v) (h2402 : (e2402 _v)) : (e7489 _v) := by
  have p10893 := n10893 _v _q 
  have p258 := n258 _v _q 
  have p16911 := n16911 _v _q 
  have p22302 := n22302 _v _q 
  have p17110 := n17110 _v _q 
  have p16913 := n16913 _v _q 
  have p17111 := n17111 _v _q 
  have p17131 := n17131 _v _q 
  have p22300 := n22300 _v _q 
  have p20653 := n20653 _v _q 
  have p22575 := n22575 _v _q h2402
  have p17108 := n17108 _v _q 
  have p17294 := n17294 _v _q 
  have p20829 := n20829 _v _q 
  have p22325 := n22325 _v _q h2402
  have p22567 := n22567 _v _q 
  have p5257 := n5257 _v _q 
  have p22649 := n22649 _v _q 
  have p13951 := n13951 _v _q 
  have p14799 := n14799 _v _q h2402
  have p22612 := n22612 _v _q 
  have p17067 := n17067 _v _q 
  have p17072 := n17072 _v _q 
  have p17053 := n17053 _v _q 
  have p17074 := n17074 _v _q 
  have p16943 := n16943 _v _q 
  have p17069 := n17069 _v _q 
  have p20096 := n20096 _v _q 
  have p22571 := n22571 _v _q 
  have p22589 := n22589 _v _q h2402
  have p17064 := n17064 _v _q 
  have p20461 := n20461 _v _q 
  have p17874 := n17874 _v _q 
  have p17136 := n17136 _v _q 
  have p17080 := n17080 _v _q 
  have p17055 := n17055 _v _q 
  have p17058 := n17058 _v _q 
  have p20836 := n20836 _v _q 
  have p22582 := n22582 _v _q 
  have p17083 := n17083 _v _q 
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p17093 := n17093 _v _q 
  have p22585 := n22585 _v _q 
  have p17087 := n17087 _v _q 
  have p17100 := n17100 _v _q 
  have p22322 := n22322 _v _q 
  have p17091 := n17091 _v _q 
  have p17102 := n17102 _v _q 
  have p17141 := n17141 _v _q 
  have p22578 := n22578 _v _q 
  have p22407 := n22407 _v _q 
  have p17124 := n17124 _v _q 
  have p22341 := n22341 _v _q 
  have p22324 := n22324 _v _q 
  have p19610 := n19610 _v _q 
  have p17020 := n17020 _v _q 
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
  have p22326 := n22326 _v _q h2402
  exact FloorCertificate.node_22650 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e61 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p10893 p258 p16911 p22302 p17110 p16913 p17111 p17131 p22300 p20653 p22575 p17108 p17294 p20829 p22325 p22567 p5257 p22649 p13951 p14799 p22612 p17067 p17072 p17053 p17074 p16943 p17069 p20096 p22571 p22589 p17064 p20461 p17874 p17136 p17080 p17055 p17058 p20836 p22582 p17083 p17098 p17106 p17093 p22585 p17087 p17100 p22322 p17091 p17102 p17141 p22578 p22407 p17124 p22341 p22324 p19610 p17020 p22368 p22323 p17758 p22320 p17115 p17078 p17117 p17113 p20467 p17133 p17120 p17009 p22321 p17089 p22318 p22347 p17104 p20470 p20274 p19665 p16778 p17127 p17050 p17122 p17096 p20126 p20426 p22326
theorem n22651 (_v : Vars) (_q : Query _v)  : (e6600 _v) := by
  by_contra hc
  change ¬ (¬ (e2402 _v)) at hc
  have h2402 : (e2402 _v) := Classical.byContradiction (fun hn => hc hn)
  have p22650 := n22650 _v _q h2402
  exact p22650
theorem n22652 (_v : Vars) (_q : Query _v)  : (e7416 _v) := by
  have p14534 := n14534 _v _q 
  have p22651 := n22651 _v _q 
  change (e2402 _v) ∨ (¬ (e7415 _v)) at p14534
  change (¬ (e2402 _v)) at p22651
  rcases p14534 with hlit | hlit
  · exact (False.elim (p22651 hlit))
  · exact hlit
theorem n22653 (_v : Vars) (_q : Query _v)  : (e3937 _v) := by
  have p15012 := n15012 _v _q 
  have p22652 := n22652 _v _q 
  change (e7415 _v) ∨ (e3937 _v) at p15012
  change (¬ (e7415 _v)) at p22652
  rcases p15012 with hlit | hlit
  · exact (False.elim (p22652 hlit))
  · exact hlit
theorem n22654 (_v : Vars) (_q : Query _v) (h6772 : (e6772 _v)) : (e7489 _v) := by
  have p22300 := n22300 _v _q 
  have p15944 := n15944 _v _q h6772
  have p10893 := n10893 _v _q 
  have p22567 := n22567 _v _q 
  have p5257 := n5257 _v _q 
  have p17096 := n17096 _v _q 
  have p17256 := n17256 _v _q 
  have p20126 := n20126 _v _q 
  have p22592 := n22592 _v _q h6772
  have p20426 := n20426 _v _q 
  have p22616 := n22616 _v _q h6772
  have p22302 := n22302 _v _q 
  have p17110 := n17110 _v _q 
  have p16753 := n16753 _v _q h6772
  have p17111 := n17111 _v _q 
  have p17131 := n17131 _v _q 
  have p20653 := n20653 _v _q 
  have p17108 := n17108 _v _q 
  have p17294 := n17294 _v _q 
  have p20829 := n20829 _v _q 
  have p22653 := n22653 _v _q 
  have p22649 := n22649 _v _q 
  have p13951 := n13951 _v _q 
  have p17147 := n17147 _v _q 
  have p22612 := n22612 _v _q 
  have p17067 := n17067 _v _q 
  have p17072 := n17072 _v _q 
  have p17053 := n17053 _v _q 
  have p17074 := n17074 _v _q 
  have p16943 := n16943 _v _q 
  have p17069 := n17069 _v _q 
  have p20096 := n20096 _v _q 
  have p22571 := n22571 _v _q 
  have p17064 := n17064 _v _q 
  have p20461 := n20461 _v _q 
  have p17874 := n17874 _v _q 
  have p17136 := n17136 _v _q 
  have p17080 := n17080 _v _q 
  have p17055 := n17055 _v _q 
  have p17058 := n17058 _v _q 
  have p20836 := n20836 _v _q 
  have p22582 := n22582 _v _q 
  have p17083 := n17083 _v _q 
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p17093 := n17093 _v _q 
  have p22585 := n22585 _v _q 
  have p17087 := n17087 _v _q 
  have p17100 := n17100 _v _q 
  have p22322 := n22322 _v _q 
  have p17091 := n17091 _v _q 
  have p17102 := n17102 _v _q 
  have p17141 := n17141 _v _q 
  have p22578 := n22578 _v _q 
  have p22407 := n22407 _v _q 
  have p17124 := n17124 _v _q 
  have p22341 := n22341 _v _q 
  have p22324 := n22324 _v _q 
  have p19610 := n19610 _v _q 
  have p17020 := n17020 _v _q 
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
  have p16977 := n16977 _v _q 
  have p8458 := n8458 _v _q h6772
  exact FloorCertificate.node_22654 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e61 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2883 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p22300 p15944 p10893 p22567 p5257 p17096 p17256 p20126 p22592 p20426 p22616 p22302 p17110 p16753 p17111 p17131 p20653 p17108 p17294 p20829 p22653 p22649 p13951 p17147 p22612 p17067 p17072 p17053 p17074 p16943 p17069 p20096 p22571 p17064 p20461 p17874 p17136 p17080 p17055 p17058 p20836 p22582 p17083 p17098 p17106 p17093 p22585 p17087 p17100 p22322 p17091 p17102 p17141 p22578 p22407 p17124 p22341 p22324 p19610 p17020 p22368 p22323 p17758 p22320 p17115 p17078 p17117 p17113 p20467 p17133 p17120 p17009 p22321 p17089 p22318 p22347 p17104 p20470 p20274 p19665 p16778 p17127 p17050 p17122 p16977 p8458
theorem n22655 (_v : Vars) (_q : Query _v)  : (e2787 _v) := by
  by_contra hc
  change ¬ (e2787 _v) at hc
  have h6772 : (e6772 _v) := (fun hn => hc hn)
  have p22654 := n22654 _v _q h6772
  exact p22654
theorem n22656 (_v : Vars) (_q : Query _v)  : (e2358 _v) := by
  have p11498 := n11498 _v _q 
  have p22655 := n22655 _v _q 
  change (¬ (e2787 _v)) ∨ (e2358 _v) at p11498
  rcases p11498 with hlit | hlit
  · exact (False.elim (hlit p22655))
  · exact hlit
theorem n22657 (_v : Vars) (_q : Query _v)  : (e7640 _v) := by
  have p14828 := n14828 _v _q 
  have p22656 := n22656 _v _q 
  change (¬ (e2358 _v)) ∨ (¬ (e7634 _v)) at p14828
  rcases p14828 with hlit | hlit
  · exact (False.elim (hlit p22656))
  · exact hlit
theorem n22658 (_v : Vars) (_q : Query _v)  : (e4139 _v) := by
  have p16281 := n16281 _v _q 
  have p22657 := n22657 _v _q 
  change (e7634 _v) ∨ (e4139 _v) at p16281
  change (¬ (e7634 _v)) at p22657
  rcases p16281 with hlit | hlit
  · exact (False.elim (p22657 hlit))
  · exact hlit
theorem n22659 (_v : Vars) (_q : Query _v)  : (e7927 _v) := by
  have p14855 := n14855 _v _q 
  have p22655 := n22655 _v _q 
  change (¬ (e2787 _v)) ∨ (¬ (e7921 _v)) at p14855
  rcases p14855 with hlit | hlit
  · exact (False.elim (hlit p22655))
  · exact hlit
theorem n22660 (_v : Vars) (_q : Query _v)  : (e4419 _v) := by
  have p16347 := n16347 _v _q 
  have p22659 := n22659 _v _q 
  change (e7921 _v) ∨ (e4419 _v) at p16347
  change (¬ (e7921 _v)) at p22659
  rcases p16347 with hlit | hlit
  · exact (False.elim (p22659 hlit))
  · exact hlit
theorem n22661 (_v : Vars) (_q : Query _v) (h7807 : (e7807 _v)) : (e7489 _v) := by
  have p258 := n258 _v _q 
  have p10893 := n10893 _v _q 
  have p22300 := n22300 _v _q 
  have p5257 := n5257 _v _q 
  have p22567 := n22567 _v _q 
  have p20126 := n20126 _v _q 
  have p15373 := n15373 _v _q h7807
  have p20426 := n20426 _v _q 
  have p17096 := n17096 _v _q 
  have p16977 := n16977 _v _q 
  have p22302 := n22302 _v _q 
  have p17110 := n17110 _v _q 
  have p15485 := n15485 _v _q h7807
  have p17111 := n17111 _v _q 
  have p17131 := n17131 _v _q 
  have p20653 := n20653 _v _q 
  have p22660 := n22660 _v _q 
  have p17108 := n17108 _v _q 
  have p17294 := n17294 _v _q 
  have p20829 := n20829 _v _q 
  have p18959 := n18959 _v _q h7807
  have p22649 := n22649 _v _q 
  have p13951 := n13951 _v _q 
  have p17147 := n17147 _v _q 
  have p22612 := n22612 _v _q 
  have p17067 := n17067 _v _q 
  have p17072 := n17072 _v _q 
  have p17053 := n17053 _v _q 
  have p17074 := n17074 _v _q 
  have p16943 := n16943 _v _q 
  have p17069 := n17069 _v _q 
  have p20096 := n20096 _v _q 
  have p22571 := n22571 _v _q 
  have p17064 := n17064 _v _q 
  have p20461 := n20461 _v _q 
  have p17874 := n17874 _v _q 
  have p17136 := n17136 _v _q 
  have p17080 := n17080 _v _q 
  have p17055 := n17055 _v _q 
  have p17058 := n17058 _v _q 
  have p20836 := n20836 _v _q 
  have p22582 := n22582 _v _q 
  have p17083 := n17083 _v _q 
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p17093 := n17093 _v _q 
  have p22585 := n22585 _v _q 
  have p17087 := n17087 _v _q 
  have p17100 := n17100 _v _q 
  have p22322 := n22322 _v _q 
  have p17091 := n17091 _v _q 
  have p17102 := n17102 _v _q 
  have p17141 := n17141 _v _q 
  have p22578 := n22578 _v _q 
  have p22407 := n22407 _v _q 
  have p17124 := n17124 _v _q 
  have p22341 := n22341 _v _q 
  have p22324 := n22324 _v _q 
  have p19610 := n19610 _v _q 
  have p17020 := n17020 _v _q 
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
  have p22653 := n22653 _v _q 
  have p22658 := n22658 _v _q 
  exact FloorCertificate.node_22661 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e61 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2883 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p258 p10893 p22300 p5257 p22567 p20126 p15373 p20426 p17096 p16977 p22302 p17110 p15485 p17111 p17131 p20653 p22660 p17108 p17294 p20829 p18959 p22649 p13951 p17147 p22612 p17067 p17072 p17053 p17074 p16943 p17069 p20096 p22571 p17064 p20461 p17874 p17136 p17080 p17055 p17058 p20836 p22582 p17083 p17098 p17106 p17093 p22585 p17087 p17100 p22322 p17091 p17102 p17141 p22578 p22407 p17124 p22341 p22324 p19610 p17020 p22368 p22323 p17758 p22320 p17115 p17078 p17117 p17113 p20467 p17133 p17120 p17009 p22321 p17089 p22318 p22347 p17104 p20470 p20274 p19665 p16778 p17127 p17050 p17122 p22653 p22658
theorem n22662 (_v : Vars) (_q : Query _v)  : (e2303 _v) := by
  by_contra hc
  change ¬ (e2303 _v) at hc
  have h7807 : (e7807 _v) := (fun hn => hc hn)
  have p22661 := n22661 _v _q h7807
  exact p22661
theorem n22663 (_v : Vars) (_q : Query _v)  : (e7804 _v) := by
  have p14837 := n14837 _v _q 
  have p22662 := n22662 _v _q 
  change (¬ (e2303 _v)) ∨ (¬ (e7798 _v)) at p14837
  rcases p14837 with hlit | hlit
  · exact (False.elim (hlit p22662))
  · exact hlit
theorem n22664 (_v : Vars) (_q : Query _v)  : (e4285 _v) := by
  have p16274 := n16274 _v _q 
  have p22663 := n22663 _v _q 
  change (e7798 _v) ∨ (e4285 _v) at p16274
  change (¬ (e7798 _v)) at p22663
  rcases p16274 with hlit | hlit
  · exact (False.elim (p22663 hlit))
  · exact hlit
theorem n22665 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) : (e7489 _v) := by
  have p22300 := n22300 _v _q 
  have p16911 := n16911 _v _q 
  have p22651 := n22651 _v _q 
  have p10893 := n10893 _v _q 
  have p5000 := n5000 _v _q h30
  have p22658 := n22658 _v _q 
  have p22567 := n22567 _v _q 
  have p16913 := n16913 _v _q 
  have p5257 := n5257 _v _q 
  have p20126 := n20126 _v _q 
  have p13951 := n13951 _v _q 
  have p20426 := n20426 _v _q 
  have p17096 := n17096 _v _q 
  have p22302 := n22302 _v _q 
  have p17110 := n17110 _v _q 
  have p17111 := n17111 _v _q 
  have p17131 := n17131 _v _q 
  have p20653 := n20653 _v _q 
  have p22660 := n22660 _v _q 
  have p17108 := n17108 _v _q 
  have p17294 := n17294 _v _q 
  have p20829 := n20829 _v _q 
  have p22649 := n22649 _v _q 
  have p22653 := n22653 _v _q 
  have p17147 := n17147 _v _q 
  have p22612 := n22612 _v _q 
  have p17067 := n17067 _v _q 
  have p17072 := n17072 _v _q 
  have p17053 := n17053 _v _q 
  have p17074 := n17074 _v _q 
  have p16943 := n16943 _v _q 
  have p17069 := n17069 _v _q 
  have p20096 := n20096 _v _q 
  have p22571 := n22571 _v _q 
  have p17064 := n17064 _v _q 
  have p20461 := n20461 _v _q 
  have p17874 := n17874 _v _q 
  have p17136 := n17136 _v _q 
  have p17080 := n17080 _v _q 
  have p17055 := n17055 _v _q 
  have p17058 := n17058 _v _q 
  have p20836 := n20836 _v _q 
  have p22582 := n22582 _v _q 
  have p17083 := n17083 _v _q 
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p17093 := n17093 _v _q 
  have p22585 := n22585 _v _q 
  have p17087 := n17087 _v _q 
  have p17100 := n17100 _v _q 
  have p22322 := n22322 _v _q 
  have p17091 := n17091 _v _q 
  have p17102 := n17102 _v _q 
  have p17141 := n17141 _v _q 
  have p22578 := n22578 _v _q 
  have p22407 := n22407 _v _q 
  have p17124 := n17124 _v _q 
  have p22341 := n22341 _v _q 
  have p22324 := n22324 _v _q 
  have p19610 := n19610 _v _q 
  have p17020 := n17020 _v _q 
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
  have p22664 := n22664 _v _q 
  exact FloorCertificate.node_22665 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e61 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2883 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p22300 p16911 p22651 p10893 p5000 p22658 p22567 p16913 p5257 p20126 p13951 p20426 p17096 p22302 p17110 p17111 p17131 p20653 p22660 p17108 p17294 p20829 p22649 p22653 p17147 p22612 p17067 p17072 p17053 p17074 p16943 p17069 p20096 p22571 p17064 p20461 p17874 p17136 p17080 p17055 p17058 p20836 p22582 p17083 p17098 p17106 p17093 p22585 p17087 p17100 p22322 p17091 p17102 p17141 p22578 p22407 p17124 p22341 p22324 p19610 p17020 p22368 p22323 p17758 p22320 p17115 p17078 p17117 p17113 p20467 p17133 p17120 p17009 p22321 p17089 p22318 p22347 p17104 p20470 p20274 p19665 p16778 p17127 p17050 p17122 p22664
theorem n22666 (_v : Vars) (_q : Query _v)  : (e35 _v) := by
  by_contra hc
  change ¬ (¬ (e30 _v)) at hc
  have h30 : (e30 _v) := Classical.byContradiction (fun hn => hc hn)
  have p22665 := n22665 _v _q h30
  exact p22665
theorem n22667 (_v : Vars) (_q : Query _v)  : (e5089 _v) := by
  have p16290 := n16290 _v _q 
  have p22666 := n22666 _v _q 
  change (e5089 _v) ∨ (e30 _v) at p16290
  change (¬ (e30 _v)) at p22666
  rcases p16290 with hlit | hlit
  · exact hlit
  · exact (False.elim (p22666 hlit))
theorem n22668 (_v : Vars) (_q : Query _v)  : (e5093 _v) := by
  have p14728 := n14728 _v _q 
  have p22667 := n22667 _v _q 
  change (¬ (e13 _v)) ∨ (¬ (e5089 _v)) at p14728
  rcases p14728 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p22667))
theorem n22669 (_v : Vars) (_q : Query _v)  : (e5105 _v) := by
  have p15204 := n15204 _v _q 
  have p22668 := n22668 _v _q 
  change (e13 _v) ∨ (¬ (e5104 _v)) at p15204
  change (¬ (e13 _v)) at p22668
  rcases p15204 with hlit | hlit
  · exact (False.elim (p22668 hlit))
  · exact hlit
theorem n22670 (_v : Vars) (_q : Query _v)  : (e5100 _v) := by
  have p15319 := n15319 _v _q 
  have p22669 := n22669 _v _q 
  change (e5104 _v) ∨ (e5100 _v) at p15319
  change (¬ (e5104 _v)) at p22669
  rcases p15319 with hlit | hlit
  · exact (False.elim (p22669 hlit))
  · exact hlit
theorem n22671 (_v : Vars) (_q : Query _v)  : (e7489 _v) := by
  have p22668 := n22668 _v _q 
  have p22670 := n22670 _v _q 
  have p22300 := n22300 _v _q 
  have p16911 := n16911 _v _q 
  have p22664 := n22664 _v _q 
  have p10893 := n10893 _v _q 
  have p22658 := n22658 _v _q 
  have p22567 := n22567 _v _q 
  have p16913 := n16913 _v _q 
  have p20126 := n20126 _v _q 
  have p13951 := n13951 _v _q 
  have p20426 := n20426 _v _q 
  have p17096 := n17096 _v _q 
  have p22302 := n22302 _v _q 
  have p17110 := n17110 _v _q 
  have p17111 := n17111 _v _q 
  have p17131 := n17131 _v _q 
  have p20653 := n20653 _v _q 
  have p22660 := n22660 _v _q 
  have p17108 := n17108 _v _q 
  have p17294 := n17294 _v _q 
  have p20829 := n20829 _v _q 
  have p22649 := n22649 _v _q 
  have p22653 := n22653 _v _q 
  have p17147 := n17147 _v _q 
  have p22612 := n22612 _v _q 
  have p17067 := n17067 _v _q 
  have p17072 := n17072 _v _q 
  have p17053 := n17053 _v _q 
  have p17074 := n17074 _v _q 
  have p16943 := n16943 _v _q 
  have p17069 := n17069 _v _q 
  have p20096 := n20096 _v _q 
  have p22571 := n22571 _v _q 
  have p17064 := n17064 _v _q 
  have p20461 := n20461 _v _q 
  have p17874 := n17874 _v _q 
  have p17136 := n17136 _v _q 
  have p17080 := n17080 _v _q 
  have p17055 := n17055 _v _q 
  have p17058 := n17058 _v _q 
  have p20836 := n20836 _v _q 
  have p22582 := n22582 _v _q 
  have p17083 := n17083 _v _q 
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p17093 := n17093 _v _q 
  have p22585 := n22585 _v _q 
  have p17087 := n17087 _v _q 
  have p17100 := n17100 _v _q 
  have p22322 := n22322 _v _q 
  have p17091 := n17091 _v _q 
  have p17102 := n17102 _v _q 
  have p17141 := n17141 _v _q 
  have p22578 := n22578 _v _q 
  have p22407 := n22407 _v _q 
  have p17124 := n17124 _v _q 
  have p22341 := n22341 _v _q 
  have p22324 := n22324 _v _q 
  have p19610 := n19610 _v _q 
  have p17020 := n17020 _v _q 
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
  have p22662 := n22662 _v _q 
  exact FloorCertificate.node_22671 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e61 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2883 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p22668 p22670 p22300 p16911 p22664 p10893 p22658 p22567 p16913 p20126 p13951 p20426 p17096 p22302 p17110 p17111 p17131 p20653 p22660 p17108 p17294 p20829 p22649 p22653 p17147 p22612 p17067 p17072 p17053 p17074 p16943 p17069 p20096 p22571 p17064 p20461 p17874 p17136 p17080 p17055 p17058 p20836 p22582 p17083 p17098 p17106 p17093 p22585 p17087 p17100 p22322 p17091 p17102 p17141 p22578 p22407 p17124 p22341 p22324 p19610 p17020 p22368 p22323 p17758 p22320 p17115 p17078 p17117 p17113 p20467 p17133 p17120 p17009 p22321 p17089 p22318 p22347 p17104 p20470 p20274 p19665 p16778 p17127 p17050 p17122 p22662
end
end Assembly
