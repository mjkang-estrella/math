import Dag252
import generated.th_lemma_34
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n21515 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2402 : (e2402 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) (h8038 : (e8038 _v)) : (e7804 _v) := by
  have p14837 := n14837 _v _q 
  have p21514 := n21514 _v _q h51 h91 h2402 h2529 h4306 h4653 h4813 h6525 h8038
  change (¬ (e2303 _v)) ∨ (¬ (e7798 _v)) at p14837
  rcases p14837 with hlit | hlit
  · exact (False.elim (hlit p21514))
  · exact hlit
theorem n21516 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2402 : (e2402 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) (h8038 : (e8038 _v)) : (e4285 _v) := by
  have p16274 := n16274 _v _q 
  have p21515 := n21515 _v _q h51 h91 h2402 h2529 h4306 h4653 h4813 h6525 h8038
  change (e7798 _v) ∨ (e4285 _v) at p16274
  change (¬ (e7798 _v)) at p21515
  rcases p16274 with hlit | hlit
  · exact (False.elim (p21515 hlit))
  · exact hlit
theorem n21517 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2402 : (e2402 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) (h8038 : (e8038 _v)) : (e7943 _v) := by
  have p21510 := n21510 _v _q 
  have p21516 := n21516 _v _q h51 h91 h2402 h2529 h4306 h4653 h4813 h6525 h8038
  have p8548 := n8548 _v _q h2529
  have p8463 := n8463 _v _q h6525
  have p15209 := n15209 _v _q h8038
  have p14799 := n14799 _v _q h2402
  have p4999 := n4999 _v _q h91
  have p16729 := n16729 _v _q h51
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4983 := n4983 _v _q h4813
  change (¬ (e7935 _v)) ∨ (e2242 _v) ∨ (¬ (e2529 _v)) ∨ (¬ (e4285 _v)) ∨ (¬ (e8045 _v)) ∨ (¬ (e3919 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) at p21510
  change (¬ (e2242 _v)) at p8463
  rcases p21510 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (p8463 hlit))
  · exact (False.elim (hlit p8548))
  · exact (False.elim (hlit p21516))
  · exact (False.elim (hlit p15209))
  · exact (False.elim (hlit p14799))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p4983))
theorem n21518 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2402 : (e2402 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) (h8038 : (e8038 _v)) : (e7944 _v) := by
  have p15266 := n15266 _v _q 
  have p21517 := n21517 _v _q h51 h91 h2402 h2529 h4306 h4653 h4813 h6525 h8038
  change (e7944 _v) ∨ (e7935 _v) at p15266
  change (¬ (e7935 _v)) at p21517
  rcases p15266 with hlit | hlit
  · exact hlit
  · exact (False.elim (p21517 hlit))
theorem n21519 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2402 : (e2402 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) (h8038 : (e8038 _v)) : (e2787 _v) := by
  have p15228 := n15228 _v _q 
  have p21518 := n21518 _v _q h51 h91 h2402 h2529 h4306 h4653 h4813 h6525 h8038
  change (e2787 _v) ∨ (¬ (e7944 _v)) at p15228
  rcases p15228 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p21518))
theorem n21520 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2402 : (e2402 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) (h8038 : (e8038 _v)) : (e7927 _v) := by
  have p14855 := n14855 _v _q 
  have p21519 := n21519 _v _q h51 h91 h2402 h2529 h4306 h4653 h4813 h6525 h8038
  change (¬ (e2787 _v)) ∨ (¬ (e7921 _v)) at p14855
  rcases p14855 with hlit | hlit
  · exact (False.elim (hlit p21519))
  · exact hlit
theorem n21521 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2402 : (e2402 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) (h8038 : (e8038 _v)) : (e4419 _v) := by
  have p16347 := n16347 _v _q 
  have p21520 := n21520 _v _q h51 h91 h2402 h2529 h4306 h4653 h4813 h6525 h8038
  change (e7921 _v) ∨ (e4419 _v) at p16347
  change (¬ (e7921 _v)) at p21520
  rcases p16347 with hlit | hlit
  · exact (False.elim (p21520 hlit))
  · exact hlit
theorem n21522 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2402 : (e2402 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) (h8038 : (e8038 _v)) : (e7489 _v) := by
  have p21521 := n21521 _v _q h51 h91 h2402 h2529 h4306 h4653 h4813 h6525 h8038
  have p21519 := n21519 _v _q h51 h91 h2402 h2529 h4306 h4653 h4813 h6525 h8038
  have p8463 := n8463 _v _q h6525
  have p21504 := n21504 _v _q h51 h91 h2402 h2529 h4306 h4653 h4813 h6525
  have p13951 := n13951 _v _q 
  have p16778 := n16778 _v _q 
  have p17122 := n17122 _v _q 
  have p21516 := n21516 _v _q h51 h91 h2402 h2529 h4306 h4653 h4813 h6525 h8038
  have p21498 := n21498 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  have p20829 := n20829 _v _q 
  have p21508 := n21508 _v _q h51 h91 h2402 h2529 h4306 h4653 h4813 h6525
  have p20426 := n20426 _v _q 
  have p20126 := n20126 _v _q 
  have p17110 := n17110 _v _q 
  have p21484 := n21484 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  have p17053 := n17053 _v _q 
  have p20096 := n20096 _v _q 
  have p17131 := n17131 _v _q 
  have p17108 := n17108 _v _q 
  have p17294 := n17294 _v _q 
  have p16943 := n16943 _v _q 
  have p17058 := n17058 _v _q 
  have p15209 := n15209 _v _q h8038
  have p14799 := n14799 _v _q h2402
  have p17064 := n17064 _v _q 
  have p17067 := n17067 _v _q 
  have p17080 := n17080 _v _q 
  have p17072 := n17072 _v _q 
  have p17074 := n17074 _v _q 
  have p17069 := n17069 _v _q 
  have p20461 := n20461 _v _q 
  have p20836 := n20836 _v _q 
  have p20653 := n20653 _v _q 
  have p17078 := n17078 _v _q 
  have p17136 := n17136 _v _q 
  have p17087 := n17087 _v _q 
  have p17083 := n17083 _v _q 
  have p21476 := n21476 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  have p17055 := n17055 _v _q 
  have p17093 := n17093 _v _q 
  have p17091 := n17091 _v _q 
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p21487 := n21487 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  have p21477 := n21477 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  have p17141 := n17141 _v _q 
  have p17100 := n17100 _v _q 
  have p19610 := n19610 _v _q 
  have p16706 := n16706 _v _q h2529 h6525
  have p17102 := n17102 _v _q 
  have p21190 := n21190 _v _q h51 h91 h2529 h4306 h4653 h4813
  have p17009 := n17009 _v _q 
  have p16058 := n16058 _v _q h6525
  have p16689 := n16689 _v _q h6525
  have p17096 := n17096 _v _q 
  have p17115 := n17115 _v _q 
  have p17758 := n17758 _v _q 
  have p17124 := n17124 _v _q 
  have p17111 := n17111 _v _q 
  have p19665 := n19665 _v _q 
  have p17113 := n17113 _v _q 
  have p17117 := n17117 _v _q 
  have p20467 := n20467 _v _q 
  have p17120 := n17120 _v _q 
  have p4999 := n4999 _v _q h91
  have p17133 := n17133 _v _q 
  have p17874 := n17874 _v _q 
  have p17104 := n17104 _v _q 
  have p17127 := n17127 _v _q 
  have p17089 := n17089 _v _q 
  have p20470 := n20470 _v _q 
  have p16705 := n16705 _v _q h2529
  have p17020 := n17020 _v _q 
  have p20274 := n20274 _v _q 
  have p21478 := n21478 _v _q h51 h2529 h4306 h4653 h4813 h6525
  have p16729 := n16729 _v _q h51
  have p17050 := n17050 _v _q 
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p16572 := n16572 _v _q h2529
  have p4983 := n4983 _v _q h4813
  have p21482 := n21482 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  exact FloorCertificate.node_21522 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2902 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p21521 p21519 p8463 p21504 p13951 p16778 p17122 p21516 p21498 p20829 p21508 p20426 p20126 p17110 p21484 p17053 p20096 p17131 p17108 p17294 p16943 p17058 p15209 p14799 p17064 p17067 p17080 p17072 p17074 p17069 p20461 p20836 p20653 p17078 p17136 p17087 p17083 p21476 p17055 p17093 p17091 p17098 p17106 p21487 p21477 p17141 p17100 p19610 p16706 p17102 p21190 p17009 p16058 p16689 p17096 p17115 p17758 p17124 p17111 p19665 p17113 p17117 p20467 p17120 p4999 p17133 p17874 p17104 p17127 p17089 p20470 p16705 p17020 p20274 p21478 p16729 p17050 p17138 p17060 p16572 p4983 p21482
theorem n21524 (_v : Vars) (_q : Query _v)  : (e21523 _v) := by
  by_contra hc
  change ¬ ((e2475 _v) ∨ (e2242 _v) ∨ (¬ (e91 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e2529 _v)) ∨ (¬ (e2402 _v))) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h2402 : (e2402 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn)))))))))
  have h2529 : (e2529 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h6525 : (e6525 _v) := (fun hn => hc (Or.inr (Or.inl hn)))
  have h8038 : (e8038 _v) := (fun hn => hc (Or.inl hn))
  have p21522 := n21522 _v _q h51 h91 h2402 h2529 h4306 h4653 h4813 h6525 h8038
  exact p21522
theorem n21525 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2402 : (e2402 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e2475 _v) := by
  have p21524 := n21524 _v _q 
  have p8591 := n8591 _v _q h2402
  have p4999 := n4999 _v _q h91
  have p16729 := n16729 _v _q h51
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4983 := n4983 _v _q h4813
  have p8548 := n8548 _v _q h2529
  have p8463 := n8463 _v _q h6525
  change (e2475 _v) ∨ (e2242 _v) ∨ (¬ (e91 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e2529 _v)) ∨ (¬ (e2402 _v)) at p21524
  change (¬ (e2242 _v)) at p8463
  rcases p21524 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (p8463 hlit))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p8548))
  · exact (False.elim (hlit p8591))
theorem n21526 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2402 : (e2402 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e8035 _v) := by
  have p14871 := n14871 _v _q 
  have p21525 := n21525 _v _q h51 h91 h2402 h2529 h4306 h4653 h4813 h6525
  change (¬ (e2475 _v)) ∨ (¬ (e8029 _v)) at p14871
  rcases p14871 with hlit | hlit
  · exact (False.elim (hlit p21525))
  · exact hlit
theorem n21527 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2402 : (e2402 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e4546 _v) := by
  have p16307 := n16307 _v _q 
  have p21526 := n21526 _v _q h51 h91 h2402 h2529 h4306 h4653 h4813 h6525
  change (e8029 _v) ∨ (e4546 _v) at p16307
  change (¬ (e8029 _v)) at p21526
  rcases p16307 with hlit | hlit
  · exact (False.elim (p21526 hlit))
  · exact hlit
theorem n21528 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2402 : (e2402 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e7817 _v) := by
  have p21329 := n21329 _v _q 
  have p21527 := n21527 _v _q h51 h91 h2402 h2529 h4306 h4653 h4813 h6525
  have p8463 := n8463 _v _q h6525
  have p21504 := n21504 _v _q h51 h91 h2402 h2529 h4306 h4653 h4813 h6525
  have p21498 := n21498 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  have p21484 := n21484 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  have p4983 := n4983 _v _q h4813
  have p21487 := n21487 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  have p16706 := n16706 _v _q h2529 h6525
  have p21190 := n21190 _v _q h51 h91 h2529 h4306 h4653 h4813
  have p4999 := n4999 _v _q h91
  have p16705 := n16705 _v _q h2529
  have p16729 := n16729 _v _q h51
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p16572 := n16572 _v _q h2529
  have p8591 := n8591 _v _q h2402
  change (¬ (e7814 _v)) ∨ (¬ (e4546 _v)) ∨ (e2242 _v) ∨ (e13 _v) ∨ (¬ (e4139 _v)) ∨ (¬ (e4101 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e3158 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e2402 _v)) at p21329
  change (¬ (e2242 _v)) at p8463
  change (¬ (e13 _v)) at p21504
  rcases p21329 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p21527))
  · exact (False.elim (p8463 hlit))
  · exact (False.elim (p21504 hlit))
  · exact (False.elim (hlit p21498))
  · exact (False.elim (hlit p21484))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p21487))
  · exact (False.elim (hlit p16706))
  · exact (False.elim (hlit p21190))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p16705))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p16572))
  · exact (False.elim (hlit p8591))
theorem n21529 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2402 : (e2402 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e7818 _v) := by
  have p15221 := n15221 _v _q 
  have p21528 := n21528 _v _q h51 h91 h2402 h2529 h4306 h4653 h4813 h6525
  change (e7818 _v) ∨ (e7814 _v) at p15221
  change (¬ (e7814 _v)) at p21528
  rcases p15221 with hlit | hlit
  · exact hlit
  · exact (False.elim (p21528 hlit))
theorem n21530 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2402 : (e2402 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e2303 _v) := by
  have p14994 := n14994 _v _q 
  have p21529 := n21529 _v _q h51 h91 h2402 h2529 h4306 h4653 h4813 h6525
  change (e2303 _v) ∨ (¬ (e7818 _v)) at p14994
  rcases p14994 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p21529))
theorem n21531 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2402 : (e2402 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e2787 _v) := by
  have p8461 := n8461 _v _q 
  have p21530 := n21530 _v _q h51 h91 h2402 h2529 h4306 h4653 h4813 h6525
  have p21525 := n21525 _v _q h51 h91 h2402 h2529 h4306 h4653 h4813 h6525
  change (¬ (e2475 _v)) ∨ (¬ (e2303 _v)) ∨ (e2787 _v) at p8461
  rcases p8461 with hlit | hlit | hlit
  · exact (False.elim (hlit p21525))
  · exact (False.elim (hlit p21530))
  · exact hlit
theorem n21532 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2402 : (e2402 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e7804 _v) := by
  have p14837 := n14837 _v _q 
  have p21530 := n21530 _v _q h51 h91 h2402 h2529 h4306 h4653 h4813 h6525
  change (¬ (e2303 _v)) ∨ (¬ (e7798 _v)) at p14837
  rcases p14837 with hlit | hlit
  · exact (False.elim (hlit p21530))
  · exact hlit
theorem n21533 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2402 : (e2402 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e7927 _v) := by
  have p14855 := n14855 _v _q 
  have p21531 := n21531 _v _q h51 h91 h2402 h2529 h4306 h4653 h4813 h6525
  change (¬ (e2787 _v)) ∨ (¬ (e7921 _v)) at p14855
  rcases p14855 with hlit | hlit
  · exact (False.elim (hlit p21531))
  · exact hlit
theorem n21534 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2402 : (e2402 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e4419 _v) := by
  have p16347 := n16347 _v _q 
  have p21533 := n21533 _v _q h51 h91 h2402 h2529 h4306 h4653 h4813 h6525
  change (e7921 _v) ∨ (e4419 _v) at p16347
  change (¬ (e7921 _v)) at p21533
  rcases p16347 with hlit | hlit
  · exact (False.elim (p21533 hlit))
  · exact hlit
theorem n21535 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2402 : (e2402 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e4285 _v) := by
  have p16274 := n16274 _v _q 
  have p21532 := n21532 _v _q h51 h91 h2402 h2529 h4306 h4653 h4813 h6525
  change (e7798 _v) ∨ (e4285 _v) at p16274
  change (¬ (e7798 _v)) at p21532
  rcases p16274 with hlit | hlit
  · exact (False.elim (p21532 hlit))
  · exact hlit
theorem n21536 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2402 : (e2402 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e7489 _v) := by
  have p21534 := n21534 _v _q h51 h91 h2402 h2529 h4306 h4653 h4813 h6525
  have p21527 := n21527 _v _q h51 h91 h2402 h2529 h4306 h4653 h4813 h6525
  have p8463 := n8463 _v _q h6525
  have p21504 := n21504 _v _q h51 h91 h2402 h2529 h4306 h4653 h4813 h6525
  have p13951 := n13951 _v _q 
  have p16778 := n16778 _v _q 
  have p17122 := n17122 _v _q 
  have p21528 := n21528 _v _q h51 h91 h2402 h2529 h4306 h4653 h4813 h6525
  have p21498 := n21498 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  have p20829 := n20829 _v _q 
  have p21508 := n21508 _v _q h51 h91 h2402 h2529 h4306 h4653 h4813 h6525
  have p20426 := n20426 _v _q 
  have p20126 := n20126 _v _q 
  have p17110 := n17110 _v _q 
  have p21484 := n21484 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  have p17053 := n17053 _v _q 
  have p20096 := n20096 _v _q 
  have p17131 := n17131 _v _q 
  have p17108 := n17108 _v _q 
  have p17294 := n17294 _v _q 
  have p16943 := n16943 _v _q 
  have p17058 := n17058 _v _q 
  have p4983 := n4983 _v _q h4813
  have p14799 := n14799 _v _q h2402
  have p17064 := n17064 _v _q 
  have p17067 := n17067 _v _q 
  have p17080 := n17080 _v _q 
  have p17072 := n17072 _v _q 
  have p17074 := n17074 _v _q 
  have p17069 := n17069 _v _q 
  have p20461 := n20461 _v _q 
  have p20836 := n20836 _v _q 
  have p20653 := n20653 _v _q 
  have p17078 := n17078 _v _q 
  have p17136 := n17136 _v _q 
  have p17087 := n17087 _v _q 
  have p17083 := n17083 _v _q 
  have p21476 := n21476 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  have p17055 := n17055 _v _q 
  have p17093 := n17093 _v _q 
  have p17091 := n17091 _v _q 
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p21487 := n21487 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  have p21477 := n21477 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  have p17141 := n17141 _v _q 
  have p17100 := n17100 _v _q 
  have p19610 := n19610 _v _q 
  have p16706 := n16706 _v _q h2529 h6525
  have p17102 := n17102 _v _q 
  have p21190 := n21190 _v _q h51 h91 h2529 h4306 h4653 h4813
  have p17009 := n17009 _v _q 
  have p16058 := n16058 _v _q h6525
  have p16689 := n16689 _v _q h6525
  have p17096 := n17096 _v _q 
  have p17115 := n17115 _v _q 
  have p17758 := n17758 _v _q 
  have p17124 := n17124 _v _q 
  have p17111 := n17111 _v _q 
  have p19665 := n19665 _v _q 
  have p17113 := n17113 _v _q 
  have p17117 := n17117 _v _q 
  have p20467 := n20467 _v _q 
  have p17120 := n17120 _v _q 
  have p4999 := n4999 _v _q h91
  have p17133 := n17133 _v _q 
  have p17874 := n17874 _v _q 
  have p17104 := n17104 _v _q 
  have p17127 := n17127 _v _q 
  have p17089 := n17089 _v _q 
  have p20470 := n20470 _v _q 
  have p16705 := n16705 _v _q h2529
  have p17020 := n17020 _v _q 
  have p20274 := n20274 _v _q 
  have p21478 := n21478 _v _q h51 h2529 h4306 h4653 h4813 h6525
  have p16729 := n16729 _v _q h51
  have p17050 := n17050 _v _q 
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p16572 := n16572 _v _q h2529
  have p21535 := n21535 _v _q h51 h91 h2402 h2529 h4306 h4653 h4813 h6525
  have p21525 := n21525 _v _q h51 h91 h2402 h2529 h4306 h4653 h4813 h6525
  have p21482 := n21482 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  exact FloorCertificate.node_21536 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2902 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p21534 p21527 p8463 p21504 p13951 p16778 p17122 p21528 p21498 p20829 p21508 p20426 p20126 p17110 p21484 p17053 p20096 p17131 p17108 p17294 p16943 p17058 p4983 p14799 p17064 p17067 p17080 p17072 p17074 p17069 p20461 p20836 p20653 p17078 p17136 p17087 p17083 p21476 p17055 p17093 p17091 p17098 p17106 p21487 p21477 p17141 p17100 p19610 p16706 p17102 p21190 p17009 p16058 p16689 p17096 p17115 p17758 p17124 p17111 p19665 p17113 p17117 p20467 p17120 p4999 p17133 p17874 p17104 p17127 p17089 p20470 p16705 p17020 p20274 p21478 p16729 p17050 p17138 p17060 p16572 p21535 p21525 p21482
theorem n21538 (_v : Vars) (_q : Query _v)  : (e21537 _v) := by
  by_contra hc
  change ¬ ((¬ (e2402 _v)) ∨ (e2242 _v) ∨ (¬ (e4813 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e2529 _v))) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h2402 : (e2402 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h2529 : (e2529 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h6525 : (e6525 _v) := (fun hn => hc (Or.inr (Or.inl hn)))
  have p21536 := n21536 _v _q h51 h91 h2402 h2529 h4306 h4653 h4813 h6525
  exact p21536
theorem n21539 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e6600 _v) := by
  have p21538 := n21538 _v _q 
  have p8463 := n8463 _v _q h6525
  have p4983 := n4983 _v _q h4813
  have p4999 := n4999 _v _q h91
  have p16729 := n16729 _v _q h51
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p8548 := n8548 _v _q h2529
  change (¬ (e2402 _v)) ∨ (e2242 _v) ∨ (¬ (e4813 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e2529 _v)) at p21538
  change (¬ (e2242 _v)) at p8463
  rcases p21538 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (p8463 hlit))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p8548))
theorem n21540 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e7807 _v) := by
  have p21539 := n21539 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  have p21482 := n21482 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  exact FloorCertificate.node_21540 (e2 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p21539 p21482
theorem n21541 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e7819 _v) := by
  have p14994 := n14994 _v _q 
  have p21540 := n21540 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  change (e2303 _v) ∨ (¬ (e7818 _v)) at p14994
  change (¬ (e2303 _v)) at p21540
  rcases p14994 with hlit | hlit
  · exact (False.elim (p21540 hlit))
  · exact hlit
theorem n21542 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e7814 _v) := by
  have p15221 := n15221 _v _q 
  have p21541 := n21541 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  change (e7818 _v) ∨ (e7814 _v) at p15221
  change (¬ (e7818 _v)) at p21541
  rcases p15221 with hlit | hlit
  · exact (False.elim (p21541 hlit))
  · exact hlit
theorem n21543 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e5093 _v) := by
  have p5257 := n5257 _v _q 
  have p21539 := n21539 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  have p21482 := n21482 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  exact FloorCertificate.node_21543 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p5257 p21539 p21482
theorem n21544 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e5105 _v) := by
  have p15204 := n15204 _v _q 
  have p21543 := n21543 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  change (e13 _v) ∨ (¬ (e5104 _v)) at p15204
  change (¬ (e13 _v)) at p21543
  rcases p15204 with hlit | hlit
  · exact (False.elim (p21543 hlit))
  · exact hlit
theorem n21545 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e5100 _v) := by
  have p15319 := n15319 _v _q 
  have p21544 := n21544 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  change (e5104 _v) ∨ (e5100 _v) at p15319
  change (¬ (e5104 _v)) at p21544
  rcases p15319 with hlit | hlit
  · exact (False.elim (p21544 hlit))
  · exact hlit
theorem n21546 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e7416 _v) := by
  have p14534 := n14534 _v _q 
  have p21539 := n21539 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  change (e2402 _v) ∨ (¬ (e7415 _v)) at p14534
  change (¬ (e2402 _v)) at p21539
  rcases p14534 with hlit | hlit
  · exact (False.elim (p21539 hlit))
  · exact hlit
theorem n21547 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e3937 _v) := by
  have p15012 := n15012 _v _q 
  have p21546 := n21546 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  change (e7415 _v) ∨ (e3937 _v) at p15012
  change (¬ (e7415 _v)) at p21546
  rcases p15012 with hlit | hlit
  · exact (False.elim (p21546 hlit))
  · exact hlit
theorem n21548 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e7943 _v) := by
  have p21314 := n21314 _v _q 
  have p21496 := n21496 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  have p16572 := n16572 _v _q h2529
  have p17060 := n17060 _v _q h4653
  have p21542 := n21542 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  have p4983 := n4983 _v _q h4813
  have p21545 := n21545 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  have p21484 := n21484 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  have p16706 := n16706 _v _q h2529 h6525
  have p21190 := n21190 _v _q h51 h91 h2529 h4306 h4653 h4813
  have p4999 := n4999 _v _q h91
  have p16705 := n16705 _v _q h2529
  have p16729 := n16729 _v _q h51
  have p17138 := n17138 _v _q h4306
  have p8463 := n8463 _v _q h6525
  have p21485 := n21485 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  have p21539 := n21539 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  change (¬ (e7935 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e2358 _v)) ∨ (¬ (e7814 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e5100 _v)) ∨ (¬ (e4101 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4306 _v)) ∨ (e2242 _v) ∨ (¬ (e2179 _v)) ∨ (e2402 _v) at p21314
  change (¬ (e2242 _v)) at p8463
  change (¬ (e2402 _v)) at p21539
  rcases p21314 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p16572))
  · exact (False.elim (hlit p21496))
  · exact (False.elim (hlit p21542))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p21545))
  · exact (False.elim (hlit p21484))
  · exact (False.elim (hlit p16706))
  · exact (False.elim (hlit p21190))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p16705))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (p8463 hlit))
  · exact (False.elim (hlit p21485))
  · exact (False.elim (p21539 hlit))
theorem n21549 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e7944 _v) := by
  have p15266 := n15266 _v _q 
  have p21548 := n21548 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  change (e7944 _v) ∨ (e7935 _v) at p15266
  change (¬ (e7935 _v)) at p21548
  rcases p15266 with hlit | hlit
  · exact hlit
  · exact (False.elim (p21548 hlit))
theorem n21550 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e2787 _v) := by
  have p15228 := n15228 _v _q 
  have p21549 := n21549 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  change (e2787 _v) ∨ (¬ (e7944 _v)) at p15228
  rcases p15228 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p21549))
theorem n21551 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e7927 _v) := by
  have p14855 := n14855 _v _q 
  have p21550 := n21550 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  change (¬ (e2787 _v)) ∨ (¬ (e7921 _v)) at p14855
  rcases p14855 with hlit | hlit
  · exact (False.elim (hlit p21550))
  · exact hlit
theorem n21552 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e4419 _v) := by
  have p16347 := n16347 _v _q 
  have p21551 := n21551 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  change (e7921 _v) ∨ (e4419 _v) at p16347
  change (¬ (e7921 _v)) at p21551
  rcases p16347 with hlit | hlit
  · exact (False.elim (p21551 hlit))
  · exact hlit
theorem n21553 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e2475 _v) := by
  have p16832 := n16832 _v _q 
  have p21552 := n21552 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  have p21540 := n21540 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  change (e2303 _v) ∨ (¬ (e4419 _v)) ∨ (e2475 _v) at p16832
  change (¬ (e2303 _v)) at p21540
  rcases p16832 with hlit | hlit | hlit
  · exact (False.elim (p21540 hlit))
  · exact (False.elim (hlit p21552))
  · exact hlit
theorem n21554 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e8035 _v) := by
  have p14871 := n14871 _v _q 
  have p21553 := n21553 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  change (¬ (e2475 _v)) ∨ (¬ (e8029 _v)) at p14871
  rcases p14871 with hlit | hlit
  · exact (False.elim (hlit p21553))
  · exact hlit
theorem n21555 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e4546 _v) := by
  have p16307 := n16307 _v _q 
  have p21554 := n21554 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  change (e8029 _v) ∨ (e4546 _v) at p16307
  change (¬ (e8029 _v)) at p21554
  rcases p16307 with hlit | hlit
  · exact (False.elim (p21554 hlit))
  · exact hlit
theorem n21556 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e7489 _v) := by
  have p21552 := n21552 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  have p17060 := n17060 _v _q h4653
  have p13951 := n13951 _v _q 
  have p16572 := n16572 _v _q h2529
  have p21539 := n21539 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  have p21547 := n21547 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  have p17147 := n17147 _v _q 
  have p21542 := n21542 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  have p21555 := n21555 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  have p10893 := n10893 _v _q 
  have p16778 := n16778 _v _q 
  have p17122 := n17122 _v _q 
  have p4983 := n4983 _v _q h4813
  have p21498 := n21498 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  have p20829 := n20829 _v _q 
  have p21545 := n21545 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  have p20426 := n20426 _v _q 
  have p20126 := n20126 _v _q 
  have p17110 := n17110 _v _q 
  have p21484 := n21484 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  have p17053 := n17053 _v _q 
  have p20096 := n20096 _v _q 
  have p17131 := n17131 _v _q 
  have p17108 := n17108 _v _q 
  have p17294 := n17294 _v _q 
  have p16943 := n16943 _v _q 
  have p17058 := n17058 _v _q 
  have p17064 := n17064 _v _q 
  have p17067 := n17067 _v _q 
  have p17080 := n17080 _v _q 
  have p17072 := n17072 _v _q 
  have p17074 := n17074 _v _q 
  have p17069 := n17069 _v _q 
  have p20461 := n20461 _v _q 
  have p20836 := n20836 _v _q 
  have p20653 := n20653 _v _q 
  have p17078 := n17078 _v _q 
  have p17136 := n17136 _v _q 
  have p17087 := n17087 _v _q 
  have p17083 := n17083 _v _q 
  have p21476 := n21476 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  have p17055 := n17055 _v _q 
  have p17093 := n17093 _v _q 
  have p17091 := n17091 _v _q 
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p21487 := n21487 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  have p21477 := n21477 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  have p17141 := n17141 _v _q 
  have p17100 := n17100 _v _q 
  have p19610 := n19610 _v _q 
  have p16706 := n16706 _v _q h2529 h6525
  have p17102 := n17102 _v _q 
  have p21190 := n21190 _v _q h51 h91 h2529 h4306 h4653 h4813
  have p17009 := n17009 _v _q 
  have p16058 := n16058 _v _q h6525
  have p16689 := n16689 _v _q h6525
  have p17096 := n17096 _v _q 
  have p17115 := n17115 _v _q 
  have p17758 := n17758 _v _q 
  have p17124 := n17124 _v _q 
  have p17111 := n17111 _v _q 
  have p19665 := n19665 _v _q 
  have p17113 := n17113 _v _q 
  have p17117 := n17117 _v _q 
  have p20467 := n20467 _v _q 
  have p17120 := n17120 _v _q 
  have p4999 := n4999 _v _q h91
  have p17133 := n17133 _v _q 
  have p17874 := n17874 _v _q 
  have p17104 := n17104 _v _q 
  have p17127 := n17127 _v _q 
  have p17089 := n17089 _v _q 
  have p20470 := n20470 _v _q 
  have p16705 := n16705 _v _q h2529
  have p17020 := n17020 _v _q 
  have p20274 := n20274 _v _q 
  have p21478 := n21478 _v _q h51 h2529 h4306 h4653 h4813 h6525
  have p16729 := n16729 _v _q h51
  have p17050 := n17050 _v _q 
  have p17138 := n17138 _v _q h4306
  have p21550 := n21550 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  exact FloorCertificate.node_21556 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2883 _v) (e2902 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p21552 p17060 p13951 p16572 p21539 p21547 p17147 p21542 p21555 p10893 p16778 p17122 p4983 p21498 p20829 p21545 p20426 p20126 p17110 p21484 p17053 p20096 p17131 p17108 p17294 p16943 p17058 p17064 p17067 p17080 p17072 p17074 p17069 p20461 p20836 p20653 p17078 p17136 p17087 p17083 p21476 p17055 p17093 p17091 p17098 p17106 p21487 p21477 p17141 p17100 p19610 p16706 p17102 p21190 p17009 p16058 p16689 p17096 p17115 p17758 p17124 p17111 p19665 p17113 p17117 p20467 p17120 p4999 p17133 p17874 p17104 p17127 p17089 p20470 p16705 p17020 p20274 p21478 p16729 p17050 p17138 p21550
theorem n21558 (_v : Vars) (_q : Query _v)  : (e21557 _v) := by
  by_contra hc
  change ¬ ((e2242 _v) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e2529 _v))) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h2529 : (e2529 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn)))))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h6525 : (e6525 _v) := (fun hn => hc (Or.inl hn))
  have p21556 := n21556 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  exact p21556
theorem n21559 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2475 : (e2475 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e95 _v) := by
  have p21558 := n21558 _v _q 
  have p16737 := n16737 _v _q h2475
  have p4983 := n4983 _v _q h4813
  have p17060 := n17060 _v _q h4653
  have p16729 := n16729 _v _q h51
  have p17138 := n17138 _v _q h4306
  have p8463 := n8463 _v _q h6525
  change (e2242 _v) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e2529 _v)) at p21558
  change (¬ (e2242 _v)) at p8463
  rcases p21558 with hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact (False.elim (p8463 hlit))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p4983))
  · exact hlit
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p16737))
theorem n21560 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2475 : (e2475 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e7489 _v) := by
  have p16235 := n16235 _v _q 
  have p16688 := n16688 _v _q h2475
  have p21559 := n21559 _v _q h51 h2475 h4306 h4653 h4813 h6525
  change (e5134 _v) ∨ (e91 _v) at p16235
  change (¬ (e5134 _v)) at p16688
  change (¬ (e91 _v)) at p21559
  rcases p16235 with hlit | hlit
  · exact (False.elim (p16688 hlit))
  · exact (False.elim (p21559 hlit))
theorem n21561 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h8320 : (e8320 _v)) : (e2242 _v) := by
  have p21558 := n21558 _v _q 
  have p17024 := n17024 _v _q h8320
  have p4983 := n4983 _v _q h4813
  have p17060 := n17060 _v _q h4653
  have p16729 := n16729 _v _q h51
  have p17138 := n17138 _v _q h4306
  have p16087 := n16087 _v _q h8320
  change (e2242 _v) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e2529 _v)) at p21558
  rcases p21558 with hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p17024))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p16087))
theorem n21562 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e2242 _v) := by
  have p21558 := n21558 _v _q 
  have p4999 := n4999 _v _q h91
  have p4983 := n4983 _v _q h4813
  have p17060 := n17060 _v _q h4653
  have p16729 := n16729 _v _q h51
  have p17138 := n17138 _v _q h4306
  have p8548 := n8548 _v _q h2529
  change (e2242 _v) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e2529 _v)) at p21558
  rcases p21558 with hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p8548))
end
end Assembly
