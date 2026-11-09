import Dag255
import generated.th_lemma_34
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n21657 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2296 : (e2296 _v)) (h2529 : (e2529 _v)) (h4264 : (e4264 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e8035 _v) := by
  have p14871 := n14871 _v _q 
  have p21656 := n21656 _v _q h51 h91 h2296 h2529 h4264 h4306 h4653 h4813
  change (¬ (e2475 _v)) ∨ (¬ (e8029 _v)) at p14871
  rcases p14871 with hlit | hlit
  · exact (False.elim (hlit p21656))
  · exact hlit
theorem n21658 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2296 : (e2296 _v)) (h2529 : (e2529 _v)) (h4264 : (e4264 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e4546 _v) := by
  have p16307 := n16307 _v _q 
  have p21657 := n21657 _v _q h51 h91 h2296 h2529 h4264 h4306 h4653 h4813
  change (e8029 _v) ∨ (e4546 _v) at p16307
  change (¬ (e8029 _v)) at p21657
  rcases p16307 with hlit | hlit
  · exact (False.elim (p21657 hlit))
  · exact hlit
theorem n21659 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2296 : (e2296 _v)) (h2529 : (e2529 _v)) (h3937 : (e3937 _v)) (h4264 : (e4264 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6571 : (e6571 _v)) : (e7489 _v) := by
  have p8447 := n8447 _v _q h6571
  have p10893 := n10893 _v _q 
  have p8583 := n8583 _v _q h2296
  have p21658 := n21658 _v _q h51 h91 h2296 h2529 h4264 h4306 h4653 h4813
  have p17138 := n17138 _v _q h4306
  have p5255 := n5255 _v _q 
  have p17118 := n17118 _v _q h4264
  have p17256 := n17256 _v _q 
  have p17060 := n17060 _v _q h4653
  have p13951 := n13951 _v _q 
  have p16572 := n16572 _v _q h2529
  have p4996 := n4996 _v _q h3937
  have p17147 := n17147 _v _q 
  have p15100 := n15100 _v _q h2296
  have p17050 := n17050 _v _q 
  have p16778 := n16778 _v _q 
  have p17122 := n17122 _v _q 
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p20829 := n20829 _v _q 
  have p21574 := n21574 _v _q h51 h91 h2529 h4306 h4653 h4813
  have p20426 := n20426 _v _q 
  have p20126 := n20126 _v _q 
  have p17110 := n17110 _v _q 
  have p15113 := n15113 _v _q h2296
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
  have p8548 := n8548 _v _q h2529
  have p17055 := n17055 _v _q 
  have p17093 := n17093 _v _q 
  have p17091 := n17091 _v _q 
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p21577 := n21577 _v _q h51 h91 h2529 h4306 h4653 h4813
  have p21579 := n21579 _v _q h51 h91 h2529 h4306 h4653 h4813
  have p17141 := n17141 _v _q 
  have p17100 := n17100 _v _q 
  have p19610 := n19610 _v _q 
  have p17102 := n17102 _v _q 
  have p21190 := n21190 _v _q h51 h91 h2529 h4306 h4653 h4813
  have p21581 := n21581 _v _q h51 h91 h2529 h4306 h4653 h4813
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
  have p21597 := n21597 _v _q h51 h91 h2529 h4306 h4653 h4813
  exact FloorCertificate.node_21659 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2883 _v) (e2902 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e4541 _v) (e4808 _v) p8447 p10893 p8583 p21658 p17138 p5255 p17118 p17256 p17060 p13951 p16572 p4996 p17147 p15100 p17050 p16778 p17122 p4983 p16729 p20829 p21574 p20426 p20126 p17110 p15113 p17053 p20096 p17131 p17108 p17294 p16943 p17058 p17064 p17067 p17080 p17072 p17074 p17069 p20461 p20836 p20653 p17078 p17136 p17087 p17083 p8548 p17055 p17093 p17091 p17098 p17106 p21577 p21579 p17141 p17100 p19610 p17102 p21190 p21581 p17096 p17115 p17758 p17124 p17111 p19665 p17113 p17117 p20467 p17120 p4999 p17133 p17874 p17104 p17127 p17089 p20470 p16705 p17020 p20274 p21597
theorem n21661 (_v : Vars) (_q : Query _v)  : (e21660 _v) := by
  by_contra hc
  change ¬ ((¬ (e3937 _v)) ∨ (e2358 _v) ∨ (¬ (e2296 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4264 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e2529 _v)) ∨ (¬ (e91 _v))) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))))))
  have h2296 : (e2296 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h2529 : (e2529 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h4264 : (e4264 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h6571 : (e6571 _v) := (fun hn => hc (Or.inr (Or.inl hn)))
  have p21659 := n21659 _v _q h51 h91 h2296 h2529 h3937 h4264 h4306 h4653 h4813 h6571
  exact p21659
theorem n21662 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2296 : (e2296 _v)) (h2529 : (e2529 _v)) (h4264 : (e4264 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6571 : (e6571 _v)) : (e3942 _v) := by
  have p21661 := n21661 _v _q 
  have p8447 := n8447 _v _q h6571
  have p8583 := n8583 _v _q h2296
  have p17138 := n17138 _v _q h4306
  have p17118 := n17118 _v _q h4264
  have p17060 := n17060 _v _q h4653
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p8548 := n8548 _v _q h2529
  have p4999 := n4999 _v _q h91
  change (¬ (e3937 _v)) ∨ (e2358 _v) ∨ (¬ (e2296 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4264 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e2529 _v)) ∨ (¬ (e91 _v)) at p21661
  change (¬ (e2358 _v)) at p8447
  rcases p21661 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (p8447 hlit))
  · exact (False.elim (hlit p8583))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17118))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p8548))
  · exact (False.elim (hlit p4999))
theorem n21663 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2296 : (e2296 _v)) (h2529 : (e2529 _v)) (h4264 : (e4264 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6571 : (e6571 _v)) : (e7415 _v) := by
  have p15012 := n15012 _v _q 
  have p21662 := n21662 _v _q h51 h91 h2296 h2529 h4264 h4306 h4653 h4813 h6571
  change (e7415 _v) ∨ (e3937 _v) at p15012
  change (¬ (e3937 _v)) at p21662
  rcases p15012 with hlit | hlit
  · exact hlit
  · exact (False.elim (p21662 hlit))
theorem n21664 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2296 : (e2296 _v)) (h2529 : (e2529 _v)) (h4264 : (e4264 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6571 : (e6571 _v)) : (e2402 _v) := by
  have p14534 := n14534 _v _q 
  have p21663 := n21663 _v _q h51 h91 h2296 h2529 h4264 h4306 h4653 h4813 h6571
  change (e2402 _v) ∨ (¬ (e7415 _v)) at p14534
  rcases p14534 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p21663))
theorem n21665 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2296 : (e2296 _v)) (h2529 : (e2529 _v)) (h4264 : (e4264 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6571 : (e6571 _v)) : (e3929 _v) := by
  have p14484 := n14484 _v _q 
  have p21664 := n21664 _v _q h51 h91 h2296 h2529 h4264 h4306 h4653 h4813 h6571
  change (¬ (e2402 _v)) ∨ (¬ (e3923 _v)) at p14484
  rcases p14484 with hlit | hlit
  · exact (False.elim (hlit p21664))
  · exact hlit
theorem n21666 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2296 : (e2296 _v)) (h2529 : (e2529 _v)) (h4264 : (e4264 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6571 : (e6571 _v)) : (e3919 _v) := by
  have p14797 := n14797 _v _q 
  have p21665 := n21665 _v _q h51 h91 h2296 h2529 h4264 h4306 h4653 h4813 h6571
  change (e3923 _v) ∨ (e3919 _v) at p14797
  change (¬ (e3923 _v)) at p21665
  rcases p14797 with hlit | hlit
  · exact (False.elim (p21665 hlit))
  · exact hlit
theorem n21667 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2296 : (e2296 _v)) (h2529 : (e2529 _v)) (h4264 : (e4264 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6571 : (e6571 _v)) : (e7489 _v) := by
  have p20827 := n20827 _v _q 
  have p8583 := n8583 _v _q h2296
  have p10893 := n10893 _v _q 
  have p8447 := n8447 _v _q h6571
  have p21666 := n21666 _v _q h51 h91 h2296 h2529 h4264 h4306 h4653 h4813 h6571
  have p21658 := n21658 _v _q h51 h91 h2296 h2529 h4264 h4306 h4653 h4813
  have p17138 := n17138 _v _q h4306
  have p5255 := n5255 _v _q 
  have p17118 := n17118 _v _q h4264
  have p17256 := n17256 _v _q 
  have p17060 := n17060 _v _q h4653
  have p13951 := n13951 _v _q 
  have p16572 := n16572 _v _q h2529
  have p15100 := n15100 _v _q h2296
  have p17050 := n17050 _v _q 
  have p16778 := n16778 _v _q 
  have p17122 := n17122 _v _q 
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p20829 := n20829 _v _q 
  have p21574 := n21574 _v _q h51 h91 h2529 h4306 h4653 h4813
  have p20426 := n20426 _v _q 
  have p20126 := n20126 _v _q 
  have p17110 := n17110 _v _q 
  have p15113 := n15113 _v _q h2296
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
  have p8548 := n8548 _v _q h2529
  have p17055 := n17055 _v _q 
  have p17093 := n17093 _v _q 
  have p17091 := n17091 _v _q 
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p21577 := n21577 _v _q h51 h91 h2529 h4306 h4653 h4813
  have p21579 := n21579 _v _q h51 h91 h2529 h4306 h4653 h4813
  have p17141 := n17141 _v _q 
  have p17100 := n17100 _v _q 
  have p19610 := n19610 _v _q 
  have p17102 := n17102 _v _q 
  have p21190 := n21190 _v _q h51 h91 h2529 h4306 h4653 h4813
  have p21581 := n21581 _v _q h51 h91 h2529 h4306 h4653 h4813
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
  have p21597 := n21597 _v _q h51 h91 h2529 h4306 h4653 h4813
  exact FloorCertificate.node_21667 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2902 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e4541 _v) (e4808 _v) p20827 p8583 p10893 p8447 p21666 p21658 p17138 p5255 p17118 p17256 p17060 p13951 p16572 p15100 p17050 p16778 p17122 p4983 p16729 p20829 p21574 p20426 p20126 p17110 p15113 p17053 p20096 p17131 p17108 p17294 p16943 p17058 p17064 p17067 p17080 p17072 p17074 p17069 p20461 p20836 p20653 p17078 p17136 p17087 p17083 p8548 p17055 p17093 p17091 p17098 p17106 p21577 p21579 p17141 p17100 p19610 p17102 p21190 p21581 p17096 p17115 p17758 p17124 p17111 p19665 p17113 p17117 p20467 p17120 p4999 p17133 p17874 p17104 p17127 p17089 p20470 p16705 p17020 p20274 p21597
theorem n21669 (_v : Vars) (_q : Query _v)  : (e21668 _v) := by
  by_contra hc
  change ¬ ((e2358 _v) ∨ (¬ (e2296 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4264 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e2529 _v)) ∨ (¬ (e91 _v))) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn)))))))))
  have h2296 : (e2296 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h2529 : (e2529 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h4264 : (e4264 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h6571 : (e6571 _v) := (fun hn => hc (Or.inl hn))
  have p21667 := n21667 _v _q h51 h91 h2296 h2529 h4264 h4306 h4653 h4813 h6571
  exact p21667
theorem n21670 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2296 : (e2296 _v)) (h2529 : (e2529 _v)) (h4264 : (e4264 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e2358 _v) := by
  have p21669 := n21669 _v _q 
  have p17118 := n17118 _v _q h4264
  have p17138 := n17138 _v _q h4306
  have p8583 := n8583 _v _q h2296
  have p17060 := n17060 _v _q h4653
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p8548 := n8548 _v _q h2529
  have p4999 := n4999 _v _q h91
  change (e2358 _v) ∨ (¬ (e2296 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4264 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e2529 _v)) ∨ (¬ (e91 _v)) at p21669
  rcases p21669 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p8583))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17118))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p8548))
  · exact (False.elim (hlit p4999))
theorem n21671 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2296 : (e2296 _v)) (h2529 : (e2529 _v)) (h4264 : (e4264 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e2402 _v) := by
  have p20923 := n20923 _v _q 
  have p21670 := n21670 _v _q h51 h91 h2296 h2529 h4264 h4306 h4653 h4813
  have p8583 := n8583 _v _q h2296
  have p21658 := n21658 _v _q h51 h91 h2296 h2529 h4264 h4306 h4653 h4813
  have p17138 := n17138 _v _q h4306
  have p17118 := n17118 _v _q h4264
  have p17060 := n17060 _v _q h4653
  have p16572 := n16572 _v _q h2529
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p21574 := n21574 _v _q h51 h91 h2529 h4306 h4653 h4813
  have p21597 := n21597 _v _q h51 h91 h2529 h4306 h4653 h4813
  have p21577 := n21577 _v _q h51 h91 h2529 h4306 h4653 h4813
  have p21579 := n21579 _v _q h51 h91 h2529 h4306 h4653 h4813
  have p21190 := n21190 _v _q h51 h91 h2529 h4306 h4653 h4813
  have p21581 := n21581 _v _q h51 h91 h2529 h4306 h4653 h4813
  have p4999 := n4999 _v _q h91
  have p16705 := n16705 _v _q h2529
  change (e2402 _v) ∨ (¬ (e2358 _v)) ∨ (¬ (e2296 _v)) ∨ (¬ (e4546 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4264 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4679 _v)) ∨ (¬ (e4567 _v)) ∨ (¬ (e3158 _v)) ∨ (¬ (e4439 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4459 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e191 _v)) at p20923
  rcases p20923 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p21670))
  · exact (False.elim (hlit p8583))
  · exact (False.elim (hlit p21658))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17118))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p16572))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p21574))
  · exact (False.elim (hlit p21597))
  · exact (False.elim (hlit p21577))
  · exact (False.elim (hlit p21579))
  · exact (False.elim (hlit p21190))
  · exact (False.elim (hlit p21581))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p16705))
theorem n21672 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2296 : (e2296 _v)) (h2529 : (e2529 _v)) (h4264 : (e4264 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e3929 _v) := by
  have p14484 := n14484 _v _q 
  have p21671 := n21671 _v _q h51 h91 h2296 h2529 h4264 h4306 h4653 h4813
  change (¬ (e2402 _v)) ∨ (¬ (e3923 _v)) at p14484
  rcases p14484 with hlit | hlit
  · exact (False.elim (hlit p21671))
  · exact hlit
theorem n21673 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2296 : (e2296 _v)) (h2529 : (e2529 _v)) (h4264 : (e4264 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e3919 _v) := by
  have p14797 := n14797 _v _q 
  have p21672 := n21672 _v _q h51 h91 h2296 h2529 h4264 h4306 h4653 h4813
  change (e3923 _v) ∨ (e3919 _v) at p14797
  change (¬ (e3923 _v)) at p21672
  rcases p14797 with hlit | hlit
  · exact (False.elim (p21672 hlit))
  · exact hlit
theorem n21674 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2296 : (e2296 _v)) (h2529 : (e2529 _v)) (h4264 : (e4264 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e7489 _v) := by
  have p258 := n258 _v _q 
  have p5257 := n5257 _v _q 
  have p21597 := n21597 _v _q h51 h91 h2529 h4306 h4653 h4813
  have p8583 := n8583 _v _q h2296
  have p21670 := n21670 _v _q h51 h91 h2296 h2529 h4264 h4306 h4653 h4813
  have p21673 := n21673 _v _q h51 h91 h2296 h2529 h4264 h4306 h4653 h4813
  have p21658 := n21658 _v _q h51 h91 h2296 h2529 h4264 h4306 h4653 h4813
  have p17138 := n17138 _v _q h4306
  have p5255 := n5255 _v _q 
  have p17118 := n17118 _v _q h4264
  have p17256 := n17256 _v _q 
  have p17060 := n17060 _v _q h4653
  have p13951 := n13951 _v _q 
  have p16572 := n16572 _v _q h2529
  have p15100 := n15100 _v _q h2296
  have p17050 := n17050 _v _q 
  have p16778 := n16778 _v _q 
  have p17122 := n17122 _v _q 
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p20829 := n20829 _v _q 
  have p21574 := n21574 _v _q h51 h91 h2529 h4306 h4653 h4813
  have p20426 := n20426 _v _q 
  have p20126 := n20126 _v _q 
  have p17110 := n17110 _v _q 
  have p15113 := n15113 _v _q h2296
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
  have p17055 := n17055 _v _q 
  have p17093 := n17093 _v _q 
  have p17091 := n17091 _v _q 
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p21577 := n21577 _v _q h51 h91 h2529 h4306 h4653 h4813
  have p21579 := n21579 _v _q h51 h91 h2529 h4306 h4653 h4813
  have p17141 := n17141 _v _q 
  have p17100 := n17100 _v _q 
  have p19610 := n19610 _v _q 
  have p17102 := n17102 _v _q 
  have p21190 := n21190 _v _q h51 h91 h2529 h4306 h4653 h4813
  have p21581 := n21581 _v _q h51 h91 h2529 h4306 h4653 h4813
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
  exact FloorCertificate.node_21674 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2902 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e4541 _v) (e4808 _v) p258 p5257 p21597 p8583 p21670 p21673 p21658 p17138 p5255 p17118 p17256 p17060 p13951 p16572 p15100 p17050 p16778 p17122 p4983 p16729 p20829 p21574 p20426 p20126 p17110 p15113 p17053 p20096 p17131 p17108 p17294 p16943 p17058 p17064 p17067 p17080 p17072 p17074 p17069 p20461 p20836 p20653 p17078 p17136 p17087 p17083 p17055 p17093 p17091 p17098 p17106 p21577 p21579 p17141 p17100 p19610 p17102 p21190 p21581 p17096 p17115 p17758 p17124 p17111 p19665 p17113 p17117 p20467 p17120 p4999 p17133 p17874 p17104 p17127 p17089 p20470 p16705 p17020 p20274
theorem n21676 (_v : Vars) (_q : Query _v)  : (e21675 _v) := by
  by_contra hc
  change ¬ ((¬ (e4264 _v)) ∨ (¬ (e2296 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e2529 _v))) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h2296 : (e2296 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h2529 : (e2529 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))))
  have h4264 : (e4264 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have p21674 := n21674 _v _q h51 h91 h2296 h2529 h4264 h4306 h4653 h4813
  exact p21674
theorem n21677 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2296 : (e2296 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e4269 _v) := by
  have p21676 := n21676 _v _q 
  have p8583 := n8583 _v _q h2296
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p4999 := n4999 _v _q h91
  have p8548 := n8548 _v _q h2529
  change (¬ (e4264 _v)) ∨ (¬ (e2296 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e2529 _v)) at p21676
  rcases p21676 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p8583))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p8548))
theorem n21678 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2296 : (e2296 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e4270 _v) := by
  have p14966 := n14966 _v _q 
  have p21677 := n21677 _v _q h51 h91 h2296 h2529 h4306 h4653 h4813
  change (e4270 _v) ∨ (e4264 _v) at p14966
  change (¬ (e4264 _v)) at p21677
  rcases p14966 with hlit | hlit
  · exact hlit
  · exact (False.elim (p21677 hlit))
theorem n21679 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2296 : (e2296 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e6776 _v) := by
  have p14699 := n14699 _v _q 
  have p21678 := n21678 _v _q h51 h91 h2296 h2529 h4306 h4653 h4813
  change (¬ (e2781 _v)) ∨ (¬ (e4270 _v)) at p14699
  rcases p14699 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p21678))
theorem n21680 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2296 : (e2296 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e4420 _v) := by
  have p21076 := n21076 _v _q 
  have p8583 := n8583 _v _q h2296
  have p21679 := n21679 _v _q h51 h91 h2296 h2529 h4306 h4653 h4813
  have p16705 := n16705 _v _q h2529
  have p21597 := n21597 _v _q h51 h91 h2529 h4306 h4653 h4813
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p16572 := n16572 _v _q h2529
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p21574 := n21574 _v _q h51 h91 h2529 h4306 h4653 h4813
  have p21577 := n21577 _v _q h51 h91 h2529 h4306 h4653 h4813
  have p21579 := n21579 _v _q h51 h91 h2529 h4306 h4653 h4813
  have p21190 := n21190 _v _q h51 h91 h2529 h4306 h4653 h4813
  have p21581 := n21581 _v _q h51 h91 h2529 h4306 h4653 h4813
  have p4999 := n4999 _v _q h91
  change (¬ (e4419 _v)) ∨ (¬ (e2296 _v)) ∨ (e2781 _v) ∨ (¬ (e191 _v)) ∨ (¬ (e4567 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4679 _v)) ∨ (¬ (e3158 _v)) ∨ (¬ (e4439 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4459 _v)) ∨ (¬ (e91 _v)) at p21076
  change (¬ (e2781 _v)) at p21679
  rcases p21076 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p8583))
  · exact (False.elim (p21679 hlit))
  · exact (False.elim (hlit p16705))
  · exact (False.elim (hlit p21597))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p16572))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p21574))
  · exact (False.elim (hlit p21577))
  · exact (False.elim (hlit p21579))
  · exact (False.elim (hlit p21190))
  · exact (False.elim (hlit p21581))
  · exact (False.elim (hlit p4999))
theorem n21681 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2296 : (e2296 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e7921 _v) := by
  have p16347 := n16347 _v _q 
  have p21680 := n21680 _v _q h51 h91 h2296 h2529 h4306 h4653 h4813
  change (e7921 _v) ∨ (e4419 _v) at p16347
  change (¬ (e4419 _v)) at p21680
  rcases p16347 with hlit | hlit
  · exact hlit
  · exact (False.elim (p21680 hlit))
theorem n21682 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2296 : (e2296 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e2402 _v) := by
  have p20992 := n20992 _v _q 
  have p8583 := n8583 _v _q h2296
  have p21679 := n21679 _v _q h51 h91 h2296 h2529 h4306 h4653 h4813
  have p16705 := n16705 _v _q h2529
  have p21597 := n21597 _v _q h51 h91 h2529 h4306 h4653 h4813
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p16572 := n16572 _v _q h2529
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p21574 := n21574 _v _q h51 h91 h2529 h4306 h4653 h4813
  have p21577 := n21577 _v _q h51 h91 h2529 h4306 h4653 h4813
  have p21579 := n21579 _v _q h51 h91 h2529 h4306 h4653 h4813
  have p21190 := n21190 _v _q h51 h91 h2529 h4306 h4653 h4813
  have p21581 := n21581 _v _q h51 h91 h2529 h4306 h4653 h4813
  have p4999 := n4999 _v _q h91
  change (e2402 _v) ∨ (¬ (e2296 _v)) ∨ (e2781 _v) ∨ (¬ (e191 _v)) ∨ (¬ (e4567 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4679 _v)) ∨ (¬ (e3158 _v)) ∨ (¬ (e4439 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4459 _v)) ∨ (¬ (e91 _v)) at p20992
  change (¬ (e2781 _v)) at p21679
  rcases p20992 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p8583))
  · exact (False.elim (p21679 hlit))
  · exact (False.elim (hlit p16705))
  · exact (False.elim (hlit p21597))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p16572))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p21574))
  · exact (False.elim (hlit p21577))
  · exact (False.elim (hlit p21579))
  · exact (False.elim (hlit p21190))
  · exact (False.elim (hlit p21581))
  · exact (False.elim (hlit p4999))
theorem n21683 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2296 : (e2296 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e7789 _v) := by
  have p14570 := n14570 _v _q 
  have p21679 := n21679 _v _q h51 h91 h2296 h2529 h4306 h4653 h4813
  change (e2781 _v) ∨ (¬ (e7781 _v)) at p14570
  change (¬ (e2781 _v)) at p21679
  rcases p14570 with hlit | hlit
  · exact (False.elim (p21679 hlit))
  · exact hlit
theorem n21684 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2296 : (e2296 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e4260 _v) := by
  have p15824 := n15824 _v _q 
  have p21683 := n21683 _v _q h51 h91 h2296 h2529 h4306 h4653 h4813
  change (e7781 _v) ∨ (e4260 _v) at p15824
  change (¬ (e7781 _v)) at p21683
  rcases p15824 with hlit | hlit
  · exact (False.elim (p21683 hlit))
  · exact hlit
theorem n21685 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2296 : (e2296 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e2475 _v) := by
  have p21679 := n21679 _v _q h51 h91 h2296 h2529 h4306 h4653 h4813
  have p8583 := n8583 _v _q h2296
  exact FloorCertificate.node_21685 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p21679 p8583
theorem n21686 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2296 : (e2296 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e8035 _v) := by
  have p14871 := n14871 _v _q 
  have p21685 := n21685 _v _q h51 h91 h2296 h2529 h4306 h4653 h4813
  change (¬ (e2475 _v)) ∨ (¬ (e8029 _v)) at p14871
  rcases p14871 with hlit | hlit
  · exact (False.elim (hlit p21685))
  · exact hlit
theorem n21687 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2296 : (e2296 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e6772 _v) := by
  have p14855 := n14855 _v _q 
  have p21681 := n21681 _v _q h51 h91 h2296 h2529 h4306 h4653 h4813
  change (¬ (e2787 _v)) ∨ (¬ (e7921 _v)) at p14855
  rcases p14855 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p21681))
theorem n21688 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2296 : (e2296 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e7945 _v) := by
  have p15228 := n15228 _v _q 
  have p21687 := n21687 _v _q h51 h91 h2296 h2529 h4306 h4653 h4813
  change (e2787 _v) ∨ (¬ (e7944 _v)) at p15228
  change (¬ (e2787 _v)) at p21687
  rcases p15228 with hlit | hlit
  · exact (False.elim (p21687 hlit))
  · exact hlit
theorem n21689 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2296 : (e2296 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e7935 _v) := by
  have p15266 := n15266 _v _q 
  have p21688 := n21688 _v _q h51 h91 h2296 h2529 h4306 h4653 h4813
  change (e7944 _v) ∨ (e7935 _v) at p15266
  change (¬ (e7944 _v)) at p21688
  rcases p15266 with hlit | hlit
  · exact (False.elim (p21688 hlit))
  · exact hlit
theorem n21690 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2296 : (e2296 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e2358 _v) := by
  have p21682 := n21682 _v _q h51 h91 h2296 h2529 h4306 h4653 h4813
  have p21679 := n21679 _v _q h51 h91 h2296 h2529 h4306 h4653 h4813
  exact FloorCertificate.node_21690 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p21682 p21679
theorem n21691 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2296 : (e2296 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e7640 _v) := by
  have p14828 := n14828 _v _q 
  have p21690 := n21690 _v _q h51 h91 h2296 h2529 h4306 h4653 h4813
  change (¬ (e2358 _v)) ∨ (¬ (e7634 _v)) at p14828
  rcases p14828 with hlit | hlit
  · exact (False.elim (hlit p21690))
  · exact hlit
theorem n21692 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2296 : (e2296 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e4546 _v) := by
  have p16307 := n16307 _v _q 
  have p21686 := n21686 _v _q h51 h91 h2296 h2529 h4306 h4653 h4813
  change (e8029 _v) ∨ (e4546 _v) at p16307
  change (¬ (e8029 _v)) at p21686
  rcases p16307 with hlit | hlit
  · exact (False.elim (p21686 hlit))
  · exact hlit
theorem n21693 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2296 : (e2296 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e4139 _v) := by
  have p16281 := n16281 _v _q 
  have p21691 := n21691 _v _q h51 h91 h2296 h2529 h4306 h4653 h4813
  change (e7634 _v) ∨ (e4139 _v) at p16281
  change (¬ (e7634 _v)) at p21691
  rcases p16281 with hlit | hlit
  · exact (False.elim (p21691 hlit))
  · exact hlit
theorem n21694 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2296 : (e2296 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e3929 _v) := by
  have p14484 := n14484 _v _q 
  have p21682 := n21682 _v _q h51 h91 h2296 h2529 h4306 h4653 h4813
  change (¬ (e2402 _v)) ∨ (¬ (e3923 _v)) at p14484
  rcases p14484 with hlit | hlit
  · exact (False.elim (hlit p21682))
  · exact hlit
theorem n21695 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2296 : (e2296 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e3919 _v) := by
  have p14797 := n14797 _v _q 
  have p21694 := n21694 _v _q h51 h91 h2296 h2529 h4306 h4653 h4813
  change (e3923 _v) ∨ (e3919 _v) at p14797
  change (¬ (e3923 _v)) at p21694
  rcases p14797 with hlit | hlit
  · exact (False.elim (p21694 hlit))
  · exact hlit
theorem n21696 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2296 : (e2296 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e7489 _v) := by
  have p21679 := n21679 _v _q h51 h91 h2296 h2529 h4306 h4653 h4813
  have p21689 := n21689 _v _q h51 h91 h2296 h2529 h4306 h4653 h4813
  have p5255 := n5255 _v _q 
  have p21687 := n21687 _v _q h51 h91 h2296 h2529 h4306 h4653 h4813
  have p21695 := n21695 _v _q h51 h91 h2296 h2529 h4306 h4653 h4813
  have p21693 := n21693 _v _q h51 h91 h2296 h2529 h4306 h4653 h4813
  have p8583 := n8583 _v _q h2296
  have p21684 := n21684 _v _q h51 h91 h2296 h2529 h4306 h4653 h4813
  have p16705 := n16705 _v _q h2529
  have p21597 := n21597 _v _q h51 h91 h2529 h4306 h4653 h4813
  have p17020 := n17020 _v _q 
  have p21692 := n21692 _v _q h51 h91 h2296 h2529 h4306 h4653 h4813
  have p17138 := n17138 _v _q h4306
  have p20274 := n20274 _v _q 
  have p17060 := n17060 _v _q h4653
  have p20470 := n20470 _v _q 
  have p16572 := n16572 _v _q h2529
  have p15100 := n15100 _v _q h2296
  have p17050 := n17050 _v _q 
  have p16778 := n16778 _v _q 
  have p17122 := n17122 _v _q 
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p20829 := n20829 _v _q 
  have p21574 := n21574 _v _q h51 h91 h2529 h4306 h4653 h4813
  have p20426 := n20426 _v _q 
  have p20126 := n20126 _v _q 
  have p17110 := n17110 _v _q 
  have p15113 := n15113 _v _q h2296
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
  have p17055 := n17055 _v _q 
  have p17093 := n17093 _v _q 
  have p17091 := n17091 _v _q 
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p21577 := n21577 _v _q h51 h91 h2529 h4306 h4653 h4813
  have p21579 := n21579 _v _q h51 h91 h2529 h4306 h4653 h4813
  have p17141 := n17141 _v _q 
  have p17100 := n17100 _v _q 
  have p19610 := n19610 _v _q 
  have p17102 := n17102 _v _q 
  have p21190 := n21190 _v _q h51 h91 h2529 h4306 h4653 h4813
  have p21581 := n21581 _v _q h51 h91 h2529 h4306 h4653 h4813
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
  have p5257 := n5257 _v _q 
  have p13951 := n13951 _v _q 
  have p21682 := n21682 _v _q h51 h91 h2296 h2529 h4306 h4653 h4813
  exact FloorCertificate.node_21696 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2902 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e4541 _v) (e4808 _v) p21679 p21689 p5255 p21687 p21695 p21693 p8583 p21684 p16705 p21597 p17020 p21692 p17138 p20274 p17060 p20470 p16572 p15100 p17050 p16778 p17122 p4983 p16729 p20829 p21574 p20426 p20126 p17110 p15113 p17053 p20096 p17131 p17108 p17294 p16943 p17058 p17064 p17067 p17080 p17072 p17074 p17069 p20461 p20836 p20653 p17078 p17136 p17087 p17083 p17055 p17093 p17091 p17098 p17106 p21577 p21579 p17141 p17100 p19610 p17102 p21190 p21581 p17096 p17115 p17758 p17124 p17111 p19665 p17113 p17117 p20467 p17120 p4999 p17133 p17874 p17104 p17127 p17089 p5257 p13951 p21682
theorem n21698 (_v : Vars) (_q : Query _v)  : (e21697 _v) := by
  by_contra hc
  change ¬ ((¬ (e2296 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e2529 _v))) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h2296 : (e2296 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h2529 : (e2529 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn)))))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have p21696 := n21696 _v _q h51 h91 h2296 h2529 h4306 h4653 h4813
  exact p21696
theorem n21699 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h8320 : (e8320 _v)) : (e6549 _v) := by
  have p21698 := n21698 _v _q 
  have p17024 := n17024 _v _q h8320
  have p17060 := n17060 _v _q h4653
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p17138 := n17138 _v _q h4306
  have p16087 := n16087 _v _q h8320
  change (¬ (e2296 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e2529 _v)) at p21698
  rcases p21698 with hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p17024))
  · exact (False.elim (hlit p16087))
theorem n21700 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h8320 : (e8320 _v)) : (e6879 _v) := by
  have p14643 := n14643 _v _q 
  have p21699 := n21699 _v _q h51 h4306 h4653 h4813 h8320
  change (e2296 _v) ∨ (¬ (e6878 _v)) at p14643
  change (¬ (e2296 _v)) at p21699
  rcases p14643 with hlit | hlit
  · exact (False.elim (p21699 hlit))
  · exact hlit
theorem n21701 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h8320 : (e8320 _v)) : (e3152 _v) := by
  have p15776 := n15776 _v _q 
  have p21700 := n21700 _v _q h51 h4306 h4653 h4813 h8320
  change (e6878 _v) ∨ (e3152 _v) at p15776
  change (¬ (e6878 _v)) at p21700
  rcases p15776 with hlit | hlit
  · exact (False.elim (p21700 hlit))
  · exact hlit
theorem n21702 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h8320 : (e8320 _v)) : (e4567 _v) := by
  have p8485 := n8485 _v _q 
  have p21585 := n21585 _v _q h51 h4306 h4653 h4813 h8320
  change (e4574 _v) ∨ (e4567 _v) at p8485
  change (¬ (e4574 _v)) at p21585
  rcases p8485 with hlit | hlit
  · exact (False.elim (p21585 hlit))
  · exact hlit
theorem n21703 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h8320 : (e8320 _v)) : (e6776 _v) := by
  have p21031 := n21031 _v _q 
  have p21699 := n21699 _v _q h51 h4306 h4653 h4813 h8320
  have p16724 := n16724 _v _q h8320
  have p21702 := n21702 _v _q h51 h4306 h4653 h4813 h8320
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p16868 := n16868 _v _q h8320
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p21587 := n21587 _v _q h51 h4306 h4653 h4813 h8320
  have p21590 := n21590 _v _q h51 h4306 h4653 h4813 h8320
  have p21592 := n21592 _v _q h51 h4306 h4653 h4813 h8320
  have p21594 := n21594 _v _q h51 h4306 h4653 h4813 h8320
  have p17024 := n17024 _v _q h8320
  have p21182 := n21182 _v _q h51 h4306 h4653 h4813 h8320
  change (¬ (e2781 _v)) ∨ (e2296 _v) ∨ (¬ (e191 _v)) ∨ (¬ (e4567 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4679 _v)) ∨ (¬ (e3158 _v)) ∨ (¬ (e4439 _v)) ∨ (¬ (e4459 _v)) ∨ (¬ (e91 _v)) ∨ (e2468 _v) at p21031
  change (¬ (e2296 _v)) at p21699
  change (¬ (e2468 _v)) at p21182
  rcases p21031 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (p21699 hlit))
  · exact (False.elim (hlit p16724))
  · exact (False.elim (hlit p21702))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p16868))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p21587))
  · exact (False.elim (hlit p21590))
  · exact (False.elim (hlit p21592))
  · exact (False.elim (hlit p21594))
  · exact (False.elim (hlit p17024))
  · exact (False.elim (p21182 hlit))
theorem n21704 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h8320 : (e8320 _v)) : (e2733 _v) := by
  have p21392 := n21392 _v _q 
  have p21182 := n21182 _v _q h51 h4306 h4653 h4813 h8320
  have p21701 := n21701 _v _q h51 h4306 h4653 h4813 h8320
  have p21561 := n21561 _v _q h51 h4306 h4653 h4813 h8320
  have p16724 := n16724 _v _q h8320
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p16868 := n16868 _v _q h8320
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p17024 := n17024 _v _q h8320
  have p21703 := n21703 _v _q h51 h4306 h4653 h4813 h8320
  change (e2733 _v) ∨ (e2468 _v) ∨ (¬ (e3152 _v)) ∨ (¬ (e2242 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e91 _v)) ∨ (e2781 _v) at p21392
  change (¬ (e2468 _v)) at p21182
  change (¬ (e2781 _v)) at p21703
  rcases p21392 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (p21182 hlit))
  · exact (False.elim (hlit p21701))
  · exact (False.elim (hlit p21561))
  · exact (False.elim (hlit p16724))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p16868))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p17024))
  · exact (False.elim (p21703 hlit))
theorem n21705 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h8320 : (e8320 _v)) : (e7789 _v) := by
  have p14570 := n14570 _v _q 
  have p21703 := n21703 _v _q h51 h4306 h4653 h4813 h8320
  change (e2781 _v) ∨ (¬ (e7781 _v)) at p14570
  change (¬ (e2781 _v)) at p21703
  rcases p14570 with hlit | hlit
  · exact (False.elim (p21703 hlit))
  · exact hlit
end
end Assembly
