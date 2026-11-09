import Dag257
import generated.th_lemma_34
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n21756 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2468 : (e2468 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5195 : (e5195 _v)) : (e5149 _v) := by
  have p15925 := n15925 _v _q 
  have p21755 := n21755 _v _q h51 h2468 h4306 h4653 h4813 h5195
  change (e5149 _v) ∨ (e5145 _v) at p15925
  change (¬ (e5145 _v)) at p21755
  rcases p15925 with hlit | hlit
  · exact hlit
  · exact (False.elim (p21755 hlit))
theorem n21757 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2468 : (e2468 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5195 : (e5195 _v)) : (e79 _v) := by
  have p15115 := n15115 _v _q 
  have p21756 := n21756 _v _q h51 h2468 h4306 h4653 h4813 h5195
  change (e79 _v) ∨ (¬ (e5149 _v)) at p15115
  rcases p15115 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p21756))
theorem n21758 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2468 : (e2468 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5195 : (e5195 _v)) : (e5135 _v) := by
  have p14729 := n14729 _v _q 
  have p21757 := n21757 _v _q h51 h2468 h4306 h4653 h4813 h5195
  change (¬ (e79 _v)) ∨ (¬ (e5134 _v)) at p14729
  rcases p14729 with hlit | hlit
  · exact (False.elim (hlit p21757))
  · exact hlit
theorem n21759 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2468 : (e2468 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5195 : (e5195 _v)) : (e91 _v) := by
  have p16235 := n16235 _v _q 
  have p21758 := n21758 _v _q h51 h2468 h4306 h4653 h4813 h5195
  change (e5134 _v) ∨ (e91 _v) at p16235
  change (¬ (e5134 _v)) at p21758
  rcases p16235 with hlit | hlit
  · exact (False.elim (p21758 hlit))
  · exact hlit
theorem n21760 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2468 : (e2468 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5195 : (e5195 _v)) : (e3156 _v) := by
  have p17758 := n17758 _v _q 
  have p21737 := n21737 _v _q h51 h4306 h4653 h4813 h5195
  have p13951 := n13951 _v _q 
  have p17124 := n17124 _v _q 
  have p15223 := n15223 _v _q h5195
  have p17111 := n17111 _v _q 
  have p17115 := n17115 _v _q 
  have p20827 := n20827 _v _q 
  have p17256 := n17256 _v _q 
  have p16072 := n16072 _v _q h2468
  have p17113 := n17113 _v _q 
  have p17117 := n17117 _v _q 
  have p20467 := n20467 _v _q 
  have p15073 := n15073 _v _q h2468
  have p16956 := n16956 _v _q h2468 h5195
  have p19665 := n19665 _v _q 
  have p17133 := n17133 _v _q 
  have p17120 := n17120 _v _q 
  have p21759 := n21759 _v _q h51 h2468 h4306 h4653 h4813 h5195
  have p17104 := n17104 _v _q 
  have p17874 := n17874 _v _q 
  have p17127 := n17127 _v _q 
  have p17089 := n17089 _v _q 
  have p16859 := n16859 _v _q h2468
  have p21727 := n21727 _v _q h51 h4306 h4653 h4813
  have p16963 := n16963 _v _q h2468 h5195
  have p15104 := n15104 _v _q h2468
  have p17138 := n17138 _v _q h4306
  have p20274 := n20274 _v _q 
  have p17060 := n17060 _v _q h4653
  have p20470 := n20470 _v _q 
  have p17953 := n17953 _v _q 
  have p17050 := n17050 _v _q 
  have p16778 := n16778 _v _q 
  have p17122 := n17122 _v _q 
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p20829 := n20829 _v _q 
  have p16074 := n16074 _v _q h2468
  have p20426 := n20426 _v _q 
  have p20126 := n20126 _v _q 
  have p17110 := n17110 _v _q 
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
  have p21740 := n21740 _v _q h5195
  have p16067 := n16067 _v _q h2468
  have p17141 := n17141 _v _q 
  have p17100 := n17100 _v _q 
  have p19610 := n19610 _v _q 
  have p17102 := n17102 _v _q 
  have p17096 := n17096 _v _q 
  have p8549 := n8549 _v _q h5195
  have p12839 := n12839 _v _q h5195
  have p17020 := n17020 _v _q 
  have p21755 := n21755 _v _q h51 h2468 h4306 h4653 h4813 h5195
  exact FloorCertificate.node_21760 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2902 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4808 _v) p17758 p21737 p13951 p17124 p15223 p17111 p17115 p20827 p17256 p16072 p17113 p17117 p20467 p15073 p16956 p19665 p17133 p17120 p21759 p17104 p17874 p17127 p17089 p16859 p21727 p16963 p15104 p17138 p20274 p17060 p20470 p17953 p17050 p16778 p17122 p4983 p16729 p20829 p16074 p20426 p20126 p17110 p17053 p20096 p17131 p17108 p17294 p16943 p17058 p17064 p17067 p17080 p17072 p17074 p17069 p20461 p20836 p20653 p17078 p17136 p17087 p17083 p17055 p17093 p17091 p17098 p17106 p21740 p16067 p17141 p17100 p19610 p17102 p17096 p8549 p12839 p17020 p21755
theorem n21761 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2468 : (e2468 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5195 : (e5195 _v)) : (e6878 _v) := by
  have p15776 := n15776 _v _q 
  have p21760 := n21760 _v _q h51 h2468 h4306 h4653 h4813 h5195
  change (e6878 _v) ∨ (e3152 _v) at p15776
  change (¬ (e3152 _v)) at p21760
  rcases p15776 with hlit | hlit
  · exact hlit
  · exact (False.elim (p21760 hlit))
theorem n21762 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2468 : (e2468 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5195 : (e5195 _v)) : (e2296 _v) := by
  have p14643 := n14643 _v _q 
  have p21761 := n21761 _v _q h51 h2468 h4306 h4653 h4813 h5195
  change (e2296 _v) ∨ (¬ (e6878 _v)) at p14643
  rcases p14643 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p21761))
theorem n21763 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2468 : (e2468 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5195 : (e5195 _v)) : (e3140 _v) := by
  have p14358 := n14358 _v _q 
  have p21762 := n21762 _v _q h51 h2468 h4306 h4653 h4813 h5195
  change (¬ (e2296 _v)) ∨ (¬ (e3139 _v)) at p14358
  rcases p14358 with hlit | hlit
  · exact (False.elim (hlit p21762))
  · exact hlit
theorem n21764 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2468 : (e2468 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5195 : (e5195 _v)) : (e3133 _v) := by
  have p15098 := n15098 _v _q 
  have p21763 := n21763 _v _q h51 h2468 h4306 h4653 h4813 h5195
  change (e3139 _v) ∨ (e3133 _v) at p15098
  change (¬ (e3139 _v)) at p21763
  rcases p15098 with hlit | hlit
  · exact (False.elim (p21763 hlit))
  · exact hlit
theorem n21765 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2468 : (e2468 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5195 : (e5195 _v)) : (e7489 _v) := by
  have p17096 := n17096 _v _q 
  have p15104 := n15104 _v _q h2468
  have p21764 := n21764 _v _q h51 h2468 h4306 h4653 h4813 h5195
  have p17758 := n17758 _v _q 
  have p17256 := n17256 _v _q 
  have p17953 := n17953 _v _q 
  have p17124 := n17124 _v _q 
  have p17111 := n17111 _v _q 
  have p17115 := n17115 _v _q 
  have p16067 := n16067 _v _q h2468
  have p8549 := n8549 _v _q h5195
  have p17113 := n17113 _v _q 
  have p17117 := n17117 _v _q 
  have p20467 := n20467 _v _q 
  have p15073 := n15073 _v _q h2468
  have p16956 := n16956 _v _q h2468 h5195
  have p19665 := n19665 _v _q 
  have p17133 := n17133 _v _q 
  have p17120 := n17120 _v _q 
  have p21759 := n21759 _v _q h51 h2468 h4306 h4653 h4813 h5195
  have p17104 := n17104 _v _q 
  have p17874 := n17874 _v _q 
  have p17127 := n17127 _v _q 
  have p17089 := n17089 _v _q 
  have p13951 := n13951 _v _q 
  have p21727 := n21727 _v _q h51 h4306 h4653 h4813
  have p16963 := n16963 _v _q h2468 h5195
  have p21762 := n21762 _v _q h51 h2468 h4306 h4653 h4813 h5195
  have p17138 := n17138 _v _q h4306
  have p20274 := n20274 _v _q 
  have p17060 := n17060 _v _q h4653
  have p20470 := n20470 _v _q 
  have p20827 := n20827 _v _q 
  have p17050 := n17050 _v _q 
  have p16778 := n16778 _v _q 
  have p17122 := n17122 _v _q 
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p20829 := n20829 _v _q 
  have p16074 := n16074 _v _q h2468
  have p20426 := n20426 _v _q 
  have p20126 := n20126 _v _q 
  have p17110 := n17110 _v _q 
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
  have p16859 := n16859 _v _q h2468
  have p21737 := n21737 _v _q h51 h4306 h4653 h4813 h5195
  have p17141 := n17141 _v _q 
  have p17100 := n17100 _v _q 
  have p19610 := n19610 _v _q 
  have p17102 := n17102 _v _q 
  have p21740 := n21740 _v _q h5195
  have p16072 := n16072 _v _q h2468
  have p12839 := n12839 _v _q h5195
  have p17020 := n17020 _v _q 
  have p21755 := n21755 _v _q h51 h2468 h4306 h4653 h4813 h5195
  exact FloorCertificate.node_21765 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2902 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e4808 _v) p17096 p15104 p21764 p17758 p17256 p17953 p17124 p17111 p17115 p16067 p8549 p17113 p17117 p20467 p15073 p16956 p19665 p17133 p17120 p21759 p17104 p17874 p17127 p17089 p13951 p21727 p16963 p21762 p17138 p20274 p17060 p20470 p20827 p17050 p16778 p17122 p4983 p16729 p20829 p16074 p20426 p20126 p17110 p17053 p20096 p17131 p17108 p17294 p16943 p17058 p17064 p17067 p17080 p17072 p17074 p17069 p20461 p20836 p20653 p17078 p17136 p17087 p17083 p17055 p17093 p17091 p17098 p17106 p16859 p21737 p17141 p17100 p19610 p17102 p21740 p16072 p12839 p17020 p21755
theorem n21767 (_v : Vars) (_q : Query _v)  : (e21766 _v) := by
  by_contra hc
  change ¬ ((¬ (e2468 _v)) ∨ (e196 _v) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v))) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))
  have h2468 : (e2468 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h5195 : (e5195 _v) := (fun hn => hc (Or.inr (Or.inl hn)))
  have p21765 := n21765 _v _q h51 h2468 h4306 h4653 h4813 h5195
  exact p21765
theorem n21768 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5195 : (e5195 _v)) : (e6630 _v) := by
  have p21767 := n21767 _v _q 
  have p8549 := n8549 _v _q h5195
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  change (¬ (e2468 _v)) ∨ (e196 _v) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) at p21767
  change (¬ (e196 _v)) at p8549
  rcases p21767 with hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (p8549 hlit))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p16729))
theorem n21769 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5195 : (e5195 _v)) : (e8275 _v) := by
  have p14655 := n14655 _v _q 
  have p21768 := n21768 _v _q h51 h4306 h4653 h4813 h5195
  change (e2468 _v) ∨ (¬ (e8267 _v)) at p14655
  change (¬ (e2468 _v)) at p21768
  rcases p14655 with hlit | hlit
  · exact (False.elim (p21768 hlit))
  · exact hlit
theorem n21770 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5195 : (e5195 _v)) : (e4787 _v) := by
  have p15670 := n15670 _v _q 
  have p21769 := n21769 _v _q h51 h4306 h4653 h4813 h5195
  change (e8267 _v) ∨ (e4787 _v) at p15670
  change (¬ (e8267 _v)) at p21769
  rcases p15670 with hlit | hlit
  · exact (False.elim (p21769 hlit))
  · exact hlit
theorem n21771 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5195 : (e5195 _v)) (h6454 : (e6454 _v)) : (e95 _v) := by
  have p20183 := n20183 _v _q 
  have p15762 := n15762 _v _q h6454
  have p17953 := n17953 _v _q 
  have p8549 := n8549 _v _q h5195
  have p21737 := n21737 _v _q h51 h4306 h4653 h4813 h5195
  have p15764 := n15764 _v _q h6454
  have p16943 := n16943 _v _q 
  have p16632 := n16632 _v _q h6454
  have p20096 := n20096 _v _q 
  have p4983 := n4983 _v _q h4813
  have p21770 := n21770 _v _q h51 h4306 h4653 h4813 h5195
  have p20274 := n20274 _v _q 
  have p16727 := n16727 _v _q h6454
  have p16726 := n16726 _v _q h6454
  have p16109 := n16109 _v _q h5195
  have p20467 := n20467 _v _q 
  have p15938 := n15938 _v _q h5195
  have p19610 := n19610 _v _q 
  have p17138 := n17138 _v _q h4306
  have p17020 := n17020 _v _q 
  have p20426 := n20426 _v _q 
  have p20461 := n20461 _v _q 
  have p17294 := n17294 _v _q 
  have p17060 := n17060 _v _q h4653
  have p17874 := n17874 _v _q 
  have p20653 := n20653 _v _q 
  have p20126 := n20126 _v _q 
  have p20829 := n20829 _v _q 
  have p20836 := n20836 _v _q 
  have p17758 := n17758 _v _q 
  have p19665 := n19665 _v _q 
  have p20470 := n20470 _v _q 
  have p12840 := n12840 _v _q h5195
  have p12839 := n12839 _v _q h5195
  change (e196 _v) ∨ (¬ (e3069 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4491 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4903 _v)) ∨ (¬ (e5208 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e5100 _v)) ∨ (¬ (e4398 _v)) ∨ (¬ (e8045 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e4567 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e3976 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4724 _v)) ∨ (e2303 _v) ∨ (e2358 _v) at p20183
  change (¬ (e196 _v)) at p8549
  change (¬ (e2303 _v)) at p12840
  change (¬ (e2358 _v)) at p12839
  rcases p20183 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact (False.elim (p8549 hlit))
  · exact (False.elim (hlit p20461))
  · exact (False.elim (hlit p15764))
  · exact (False.elim (hlit p16632))
  · exact hlit
  · exact (False.elim (hlit p15762))
  · exact (False.elim (hlit p16943))
  · exact (False.elim (hlit p16727))
  · exact (False.elim (hlit p20096))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p21770))
  · exact (False.elim (hlit p20274))
  · exact (False.elim (hlit p17953))
  · exact (False.elim (hlit p16726))
  · exact (False.elim (hlit p16109))
  · exact (False.elim (hlit p20467))
  · exact (False.elim (hlit p15938))
  · exact (False.elim (hlit p19610))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17020))
  · exact (False.elim (hlit p20426))
  · exact (False.elim (hlit p21737))
  · exact (False.elim (hlit p17294))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p17874))
  · exact (False.elim (hlit p20653))
  · exact (False.elim (hlit p20126))
  · exact (False.elim (hlit p20829))
  · exact (False.elim (hlit p20836))
  · exact (False.elim (hlit p17758))
  · exact (False.elim (hlit p19665))
  · exact (False.elim (hlit p20470))
  · exact (False.elim (p12840 hlit))
  · exact (False.elim (p12839 hlit))
theorem n21772 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5195 : (e5195 _v)) (h6454 : (e6454 _v)) : (e5134 _v) := by
  have p16235 := n16235 _v _q 
  have p21771 := n21771 _v _q h51 h4306 h4653 h4813 h5195 h6454
  change (e5134 _v) ∨ (e91 _v) at p16235
  change (¬ (e91 _v)) at p21771
  rcases p16235 with hlit | hlit
  · exact hlit
  · exact (False.elim (p21771 hlit))
theorem n21773 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5195 : (e5195 _v)) (h6454 : (e6454 _v)) : (e5138 _v) := by
  have p14729 := n14729 _v _q 
  have p21772 := n21772 _v _q h51 h4306 h4653 h4813 h5195 h6454
  change (¬ (e79 _v)) ∨ (¬ (e5134 _v)) at p14729
  rcases p14729 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p21772))
theorem n21774 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5195 : (e5195 _v)) (h6454 : (e6454 _v)) : (e5150 _v) := by
  have p15115 := n15115 _v _q 
  have p21773 := n21773 _v _q h51 h4306 h4653 h4813 h5195 h6454
  change (e79 _v) ∨ (¬ (e5149 _v)) at p15115
  change (¬ (e79 _v)) at p21773
  rcases p15115 with hlit | hlit
  · exact (False.elim (p21773 hlit))
  · exact hlit
theorem n21775 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5195 : (e5195 _v)) (h6454 : (e6454 _v)) : (e5145 _v) := by
  have p15925 := n15925 _v _q 
  have p21774 := n21774 _v _q h51 h4306 h4653 h4813 h5195 h6454
  change (e5149 _v) ∨ (e5145 _v) at p15925
  change (¬ (e5149 _v)) at p21774
  rcases p15925 with hlit | hlit
  · exact (False.elim (p21774 hlit))
  · exact hlit
theorem n21776 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5195 : (e5195 _v)) (h6454 : (e6454 _v)) : (e6776 _v) := by
  have p20929 := n20929 _v _q 
  have p8430 := n8430 _v _q h6454
  have p21732 := n21732 _v _q h51 h4306 h4653 h4813 h5195
  have p16729 := n16729 _v _q h51
  have p4983 := n4983 _v _q h4813
  have p21775 := n21775 _v _q h51 h4306 h4653 h4813 h5195 h6454
  have p12840 := n12840 _v _q h5195
  have p21770 := n21770 _v _q h51 h4306 h4653 h4813 h5195
  have p17060 := n17060 _v _q h4653
  have p17138 := n17138 _v _q h4306
  have p12925 := n12925 _v _q h5195
  change (¬ (e2781 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e1995 _v)) ∨ (e2061 _v) ∨ (¬ (e4813 _v)) ∨ (¬ (e5145 _v)) ∨ (e2303 _v) ∨ (¬ (e4787 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4306 _v)) ∨ (e2529 _v) at p20929
  change (¬ (e2061 _v)) at p8430
  change (¬ (e2303 _v)) at p12840
  change (¬ (e2529 _v)) at p12925
  rcases p20929 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p21732))
  · exact (False.elim (p8430 hlit))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p21775))
  · exact (False.elim (p12840 hlit))
  · exact (False.elim (hlit p21770))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (p12925 hlit))
theorem n21777 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5195 : (e5195 _v)) (h6454 : (e6454 _v)) : (e7789 _v) := by
  have p14570 := n14570 _v _q 
  have p21776 := n21776 _v _q h51 h4306 h4653 h4813 h5195 h6454
  change (e2781 _v) ∨ (¬ (e7781 _v)) at p14570
  change (¬ (e2781 _v)) at p21776
  rcases p14570 with hlit | hlit
  · exact (False.elim (p21776 hlit))
  · exact hlit
theorem n21778 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5195 : (e5195 _v)) (h6454 : (e6454 _v)) : (e4260 _v) := by
  have p15824 := n15824 _v _q 
  have p21777 := n21777 _v _q h51 h4306 h4653 h4813 h5195 h6454
  change (e7781 _v) ∨ (e4260 _v) at p15824
  change (¬ (e7781 _v)) at p21777
  rcases p15824 with hlit | hlit
  · exact (False.elim (p21777 hlit))
  · exact hlit
theorem n21779 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5195 : (e5195 _v)) (h6454 : (e6454 _v)) : (e4106 _v) := by
  have p17758 := n17758 _v _q 
  have p21737 := n21737 _v _q h51 h4306 h4653 h4813 h5195
  have p13951 := n13951 _v _q 
  have p17124 := n17124 _v _q 
  have p15223 := n15223 _v _q h5195
  have p17111 := n17111 _v _q 
  have p17115 := n17115 _v _q 
  have p16929 := n16929 _v _q 
  have p17256 := n17256 _v _q 
  have p16726 := n16726 _v _q h6454
  have p17113 := n17113 _v _q 
  have p17117 := n17117 _v _q 
  have p20467 := n20467 _v _q 
  have p16109 := n16109 _v _q h5195
  have p19665 := n19665 _v _q 
  have p17133 := n17133 _v _q 
  have p17120 := n17120 _v _q 
  have p21775 := n21775 _v _q h51 h4306 h4653 h4813 h5195 h6454
  have p17104 := n17104 _v _q 
  have p17874 := n17874 _v _q 
  have p17127 := n17127 _v _q 
  have p17089 := n17089 _v _q 
  have p16727 := n16727 _v _q h6454
  have p8549 := n8549 _v _q h5195
  have p21727 := n21727 _v _q h51 h4306 h4653 h4813
  have p4016 := n4016 _v _q 
  have p21776 := n21776 _v _q h51 h4306 h4653 h4813 h5195 h6454
  have p17138 := n17138 _v _q h4306
  have p20274 := n20274 _v _q 
  have p17060 := n17060 _v _q h4653
  have p20470 := n20470 _v _q 
  have p17953 := n17953 _v _q 
  have p17050 := n17050 _v _q 
  have p16778 := n16778 _v _q 
  have p17122 := n17122 _v _q 
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p20829 := n20829 _v _q 
  have p16576 := n16576 _v _q 
  have p20426 := n20426 _v _q 
  have p20126 := n20126 _v _q 
  have p17110 := n17110 _v _q 
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
  have p15764 := n15764 _v _q h6454
  have p8663 := n8663 _v _q 
  have p17141 := n17141 _v _q 
  have p17100 := n17100 _v _q 
  have p19610 := n19610 _v _q 
  have p17102 := n17102 _v _q 
  have p17096 := n17096 _v _q 
  have p17147 := n17147 _v _q 
  have p15938 := n15938 _v _q h5195
  have p17020 := n17020 _v _q 
  have p21770 := n21770 _v _q h51 h4306 h4653 h4813 h5195
  have p17009 := n17009 _v _q 
  have p16101 := n16101 _v _q h5195
  have p16632 := n16632 _v _q h6454
  have p15762 := n15762 _v _q h6454
  have p5391 := n5391 _v _q 
  have p21778 := n21778 _v _q h51 h4306 h4653 h4813 h5195 h6454
  have p16113 := n16113 _v _q h5195
  exact FloorCertificate.node_21779 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2849 _v) (e2863 _v) (e2877 _v) (e2883 _v) (e2902 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p17758 p21737 p13951 p17124 p15223 p17111 p17115 p16929 p17256 p16726 p17113 p17117 p20467 p16109 p19665 p17133 p17120 p21775 p17104 p17874 p17127 p17089 p16727 p8549 p21727 p4016 p21776 p17138 p20274 p17060 p20470 p17953 p17050 p16778 p17122 p4983 p16729 p20829 p16576 p20426 p20126 p17110 p17053 p20096 p17131 p17108 p17294 p16943 p17058 p17064 p17067 p17080 p17072 p17074 p17069 p20461 p20836 p20653 p17078 p17136 p17087 p17083 p17055 p17093 p17091 p17098 p17106 p15764 p8663 p17141 p17100 p19610 p17102 p17096 p17147 p15938 p17020 p21770 p17009 p16101 p16632 p15762 p5391 p21778 p16113
theorem n21780 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5195 : (e5195 _v)) (h6454 : (e6454 _v)) : (e4097 _v) := by
  have p8549 := n8549 _v _q h5195
  have p16977 := n16977 _v _q 
  have p4016 := n4016 _v _q 
  have p16109 := n16109 _v _q h5195
  have p21775 := n21775 _v _q h51 h4306 h4653 h4813 h5195 h6454
  have p17758 := n17758 _v _q 
  have p21737 := n21737 _v _q h51 h4306 h4653 h4813 h5195
  have p13951 := n13951 _v _q 
  have p17124 := n17124 _v _q 
  have p15223 := n15223 _v _q h5195
  have p17111 := n17111 _v _q 
  have p17115 := n17115 _v _q 
  have p16929 := n16929 _v _q 
  have p17256 := n17256 _v _q 
  have p16726 := n16726 _v _q h6454
  have p17113 := n17113 _v _q 
  have p17117 := n17117 _v _q 
  have p20467 := n20467 _v _q 
  have p16632 := n16632 _v _q h6454
  have p19665 := n19665 _v _q 
  have p17133 := n17133 _v _q 
  have p17120 := n17120 _v _q 
  have p17147 := n17147 _v _q 
  have p17104 := n17104 _v _q 
  have p17874 := n17874 _v _q 
  have p17127 := n17127 _v _q 
  have p17089 := n17089 _v _q 
  have p16727 := n16727 _v _q h6454
  have p21727 := n21727 _v _q h51 h4306 h4653 h4813
  have p21776 := n21776 _v _q h51 h4306 h4653 h4813 h5195 h6454
  have p15762 := n15762 _v _q h6454
  have p17138 := n17138 _v _q h4306
  have p20274 := n20274 _v _q 
  have p17060 := n17060 _v _q h4653
  have p20470 := n20470 _v _q 
  have p17953 := n17953 _v _q 
  have p17050 := n17050 _v _q 
  have p16778 := n16778 _v _q 
  have p17122 := n17122 _v _q 
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p20829 := n20829 _v _q 
  have p16576 := n16576 _v _q 
  have p20426 := n20426 _v _q 
  have p20126 := n20126 _v _q 
  have p17110 := n17110 _v _q 
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
  have p15764 := n15764 _v _q h6454
  have p8663 := n8663 _v _q 
  have p17141 := n17141 _v _q 
  have p17100 := n17100 _v _q 
  have p19610 := n19610 _v _q 
  have p17102 := n17102 _v _q 
  have p17096 := n17096 _v _q 
  have p15938 := n15938 _v _q h5195
  have p17020 := n17020 _v _q 
  have p21770 := n21770 _v _q h51 h4306 h4653 h4813 h5195
  have p17009 := n17009 _v _q 
  have p16101 := n16101 _v _q h5195
  have p5391 := n5391 _v _q 
  have p21778 := n21778 _v _q h51 h4306 h4653 h4813 h5195 h6454
  have p16113 := n16113 _v _q h5195
  exact FloorCertificate.node_21780 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2849 _v) (e2863 _v) (e2877 _v) (e2883 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p8549 p16977 p4016 p16109 p21775 p17758 p21737 p13951 p17124 p15223 p17111 p17115 p16929 p17256 p16726 p17113 p17117 p20467 p16632 p19665 p17133 p17120 p17147 p17104 p17874 p17127 p17089 p16727 p21727 p21776 p15762 p17138 p20274 p17060 p20470 p17953 p17050 p16778 p17122 p4983 p16729 p20829 p16576 p20426 p20126 p17110 p17053 p20096 p17131 p17108 p17294 p16943 p17058 p17064 p17067 p17080 p17072 p17074 p17069 p20461 p20836 p20653 p17078 p17136 p17087 p17083 p17055 p17093 p17091 p17098 p17106 p15764 p8663 p17141 p17100 p19610 p17102 p17096 p15938 p17020 p21770 p17009 p16101 p5391 p21778 p16113
theorem n21781 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5195 : (e5195 _v)) (h6454 : (e6454 _v)) : (e4108 _v) := by
  have p14929 := n14929 _v _q 
  have p21779 := n21779 _v _q h51 h4306 h4653 h4813 h5195 h6454
  change (e4108 _v) ∨ (e4101 _v) at p14929
  change (¬ (e4101 _v)) at p21779
  rcases p14929 with hlit | hlit
  · exact hlit
  · exact (False.elim (p21779 hlit))
theorem n21782 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5195 : (e5195 _v)) (h6454 : (e6454 _v)) : (e6750 _v) := by
  have p14689 := n14689 _v _q 
  have p21781 := n21781 _v _q h51 h4306 h4653 h4813 h5195 h6454
  change (¬ (e2733 _v)) ∨ (¬ (e4108 _v)) at p14689
  rcases p14689 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p21781))
theorem n21783 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5195 : (e5195 _v)) (h6454 : (e6454 _v)) : (e7589 _v) := by
  have p15703 := n15703 _v _q 
  have p21780 := n21780 _v _q h51 h4306 h4653 h4813 h5195 h6454
  change (e7589 _v) ∨ (e4096 _v) at p15703
  change (¬ (e4096 _v)) at p21780
  rcases p15703 with hlit | hlit
  · exact hlit
  · exact (False.elim (p21780 hlit))
theorem n21784 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5195 : (e5195 _v)) (h6454 : (e6454 _v)) : (e7489 _v) := by
  have p14525 := n14525 _v _q 
  have p21782 := n21782 _v _q h51 h4306 h4653 h4813 h5195 h6454
  have p21783 := n21783 _v _q h51 h4306 h4653 h4813 h5195 h6454
  change (e2733 _v) ∨ (¬ (e7589 _v)) at p14525
  change (¬ (e2733 _v)) at p21782
  rcases p14525 with hlit | hlit
  · exact (False.elim (p21782 hlit))
  · exact (False.elim (hlit p21783))
theorem n21786 (_v : Vars) (_q : Query _v)  : (e21785 _v) := by
  by_contra hc
  change ¬ ((e2061 _v) ∨ (e196 _v) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v))) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h5195 : (e5195 _v) := (fun hn => hc (Or.inr (Or.inl hn)))
  have h6454 : (e6454 _v) := (fun hn => hc (Or.inl hn))
  have p21784 := n21784 _v _q h51 h4306 h4653 h4813 h5195 h6454
  exact p21784
theorem n21787 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5195 : (e5195 _v)) : (e2061 _v) := by
  have p21786 := n21786 _v _q 
  have p8549 := n8549 _v _q h5195
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  change (e2061 _v) ∨ (e196 _v) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) at p21786
  change (¬ (e196 _v)) at p8549
  rcases p21786 with hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (p8549 hlit))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p16729))
theorem n21788 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5195 : (e5195 _v)) : (e4447 _v) := by
  have p14688 := n14688 _v _q 
  have p21787 := n21787 _v _q h51 h4306 h4653 h4813 h5195
  change (¬ (e2061 _v)) ∨ (¬ (e4446 _v)) at p14688
  rcases p14688 with hlit | hlit
  · exact (False.elim (hlit p21787))
  · exact hlit
theorem n21789 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5195 : (e5195 _v)) : (e4439 _v) := by
  have p14925 := n14925 _v _q 
  have p21788 := n21788 _v _q h51 h4306 h4653 h4813 h5195
  change (e4446 _v) ∨ (e4439 _v) at p14925
  change (¬ (e4446 _v)) at p21788
  rcases p14925 with hlit | hlit
  · exact (False.elim (p21788 hlit))
  · exact hlit
theorem n21790 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5138 : (e5138 _v)) (h5195 : (e5195 _v)) : (e2733 _v) := by
  have p11487 := n11487 _v _q h5138
  have p21787 := n21787 _v _q h51 h4306 h4653 h4813 h5195
  exact FloorCertificate.node_21790 (e2 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p11487 p21787
theorem n21791 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5138 : (e5138 _v)) (h5195 : (e5195 _v)) : (e4109 _v) := by
  have p14689 := n14689 _v _q 
  have p21790 := n21790 _v _q h51 h4306 h4653 h4813 h5138 h5195
  change (¬ (e2733 _v)) ∨ (¬ (e4108 _v)) at p14689
  rcases p14689 with hlit | hlit
  · exact (False.elim (hlit p21790))
  · exact hlit
theorem n21792 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5195 : (e5195 _v)) : (e4791 _v) := by
  have p21770 := n21770 _v _q h51 h4306 h4653 h4813 h5195
  have p15938 := n15938 _v _q h5195
  have p21768 := n21768 _v _q h51 h4306 h4653 h4813 h5195
  exact FloorCertificate.node_21792 (e2 _v) (e7 _v) (e17 _v) (e45 _v) (e2963 _v) (e4541 _v) p21770 p15938 p21768
theorem n21793 (_v : Vars) (_q : Query _v) (h2296 : (e2296 _v)) : (e3158 _v) := by
  have p15126 := n15126 _v _q 
  have p16104 := n16104 _v _q h2296
  change (e3162 _v) ∨ (e3158 _v) at p15126
  change (¬ (e3162 _v)) at p16104
  rcases p15126 with hlit | hlit
  · exact (False.elim (p16104 hlit))
  · exact hlit
theorem n21794 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2296 : (e2296 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5145 : (e5145 _v)) (h5195 : (e5195 _v)) : (e3920 _v) := by
  have p21746 := n21746 _v _q 
  have p17245 := n17245 _v _q h5145
  have p21789 := n21789 _v _q h51 h4306 h4653 h4813 h5195
  have p8549 := n8549 _v _q h5195
  have p8583 := n8583 _v _q h2296
  have p21792 := n21792 _v _q h51 h4306 h4653 h4813 h5195
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p21793 := n21793 _v _q h2296
  have p16102 := n16102 _v _q h2296
  change (¬ (e2296 _v)) ∨ (¬ (e4791 _v)) ∨ (¬ (e4439 _v)) ∨ (e196 _v) ∨ (¬ (e3919 _v)) ∨ (¬ (e5145 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e3158 _v)) ∨ (¬ (e2242 _v)) at p21746
  change (¬ (e196 _v)) at p8549
  rcases p21746 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact (False.elim (hlit p8583))
  · exact (False.elim (hlit p21792))
  · exact (False.elim (hlit p21789))
  · exact (False.elim (p8549 hlit))
  · exact hlit
  · exact (False.elim (hlit p17245))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p21793))
  · exact (False.elim (hlit p16102))
theorem n21795 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2296 : (e2296 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5145 : (e5145 _v)) (h5195 : (e5195 _v)) : (e3923 _v) := by
  have p14797 := n14797 _v _q 
  have p21794 := n21794 _v _q h51 h2296 h4306 h4653 h4813 h5145 h5195
  change (e3923 _v) ∨ (e3919 _v) at p14797
  change (¬ (e3919 _v)) at p21794
  rcases p14797 with hlit | hlit
  · exact hlit
  · exact (False.elim (p21794 hlit))
theorem n21796 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2296 : (e2296 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5145 : (e5145 _v)) (h5195 : (e5195 _v)) : (e6600 _v) := by
  have p14484 := n14484 _v _q 
  have p21795 := n21795 _v _q h51 h2296 h4306 h4653 h4813 h5145 h5195
  change (¬ (e2402 _v)) ∨ (¬ (e3923 _v)) at p14484
  rcases p14484 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p21795))
theorem n21797 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2296 : (e2296 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5145 : (e5145 _v)) (h5195 : (e5195 _v)) : (e7416 _v) := by
  have p14534 := n14534 _v _q 
  have p21796 := n21796 _v _q h51 h2296 h4306 h4653 h4813 h5145 h5195
  change (e2402 _v) ∨ (¬ (e7415 _v)) at p14534
  change (¬ (e2402 _v)) at p21796
  rcases p14534 with hlit | hlit
  · exact (False.elim (p21796 hlit))
  · exact hlit
theorem n21798 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2296 : (e2296 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5145 : (e5145 _v)) (h5195 : (e5195 _v)) : (e3937 _v) := by
  have p15012 := n15012 _v _q 
  have p21797 := n21797 _v _q h51 h2296 h4306 h4653 h4813 h5145 h5195
  change (e7415 _v) ∨ (e3937 _v) at p15012
  change (¬ (e7415 _v)) at p21797
  rcases p15012 with hlit | hlit
  · exact (False.elim (p21797 hlit))
  · exact hlit
theorem n21799 (_v : Vars) (_q : Query _v) (h2296 : (e2296 _v)) (h5195 : (e5195 _v)) : (e4101 _v) := by
  have p14929 := n14929 _v _q 
  have p20833 := n20833 _v _q h2296 h5195
  change (e4108 _v) ∨ (e4101 _v) at p14929
  change (¬ (e4108 _v)) at p20833
  rcases p14929 with hlit | hlit
  · exact (False.elim (p20833 hlit))
  · exact hlit
theorem n21800 (_v : Vars) (_q : Query _v) (h2296 : (e2296 _v)) (h5195 : (e5195 _v)) : (e4264 _v) := by
  have p14966 := n14966 _v _q 
  have p20835 := n20835 _v _q h2296 h5195
  change (e4270 _v) ∨ (e4264 _v) at p14966
  change (¬ (e4270 _v)) at p20835
  rcases p14966 with hlit | hlit
  · exact (False.elim (p20835 hlit))
  · exact hlit
theorem n21801 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2296 : (e2296 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5145 : (e5145 _v)) (h5195 : (e5195 _v)) : (e7489 _v) := by
  have p17758 := n17758 _v _q 
  have p21737 := n21737 _v _q h51 h4306 h4653 h4813 h5195
  have p21793 := n21793 _v _q h2296
  have p17124 := n17124 _v _q 
  have p15100 := n15100 _v _q h2296
  have p17111 := n17111 _v _q 
  have p17115 := n17115 _v _q 
  have p21789 := n21789 _v _q h51 h4306 h4653 h4813 h5195
  have p17256 := n17256 _v _q 
  have p13951 := n13951 _v _q 
  have p17113 := n17113 _v _q 
  have p17117 := n17117 _v _q 
  have p20467 := n20467 _v _q 
  have p16115 := n16115 _v _q h2296
  have p21799 := n21799 _v _q h2296 h5195
  have p19665 := n19665 _v _q 
  have p17133 := n17133 _v _q 
  have p17120 := n17120 _v _q 
  have p17245 := n17245 _v _q h5145
  have p17104 := n17104 _v _q 
  have p17874 := n17874 _v _q 
  have p17127 := n17127 _v _q 
  have p17089 := n17089 _v _q 
  have p16101 := n16101 _v _q h5195
  have p21770 := n21770 _v _q h51 h4306 h4653 h4813 h5195
  have p21727 := n21727 _v _q h51 h4306 h4653 h4813
  have p16992 := n16992 _v _q 
  have p21798 := n21798 _v _q h51 h2296 h4306 h4653 h4813 h5145 h5195
  have p17138 := n17138 _v _q h4306
  have p20274 := n20274 _v _q 
  have p17060 := n17060 _v _q h4653
  have p20470 := n20470 _v _q 
  have p17953 := n17953 _v _q 
  have p17050 := n17050 _v _q 
  have p16778 := n16778 _v _q 
  have p17122 := n17122 _v _q 
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p20829 := n20829 _v _q 
  have p17009 := n17009 _v _q 
  have p20426 := n20426 _v _q 
  have p20126 := n20126 _v _q 
  have p17110 := n17110 _v _q 
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
  have p8583 := n8583 _v _q h2296
  have p8549 := n8549 _v _q h5195
  have p17141 := n17141 _v _q 
  have p17100 := n17100 _v _q 
  have p19610 := n19610 _v _q 
  have p17102 := n17102 _v _q 
  have p17096 := n17096 _v _q 
  have p17147 := n17147 _v _q 
  have p15938 := n15938 _v _q h5195
  have p21800 := n21800 _v _q h2296 h5195
  have p20827 := n20827 _v _q 
  have p16102 := n16102 _v _q h2296
  have p21796 := n21796 _v _q h51 h2296 h4306 h4653 h4813 h5145 h5195
  exact FloorCertificate.node_21801 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2883 _v) (e2902 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e4215 _v) (e4541 _v) (e4808 _v) p17758 p21737 p21793 p17124 p15100 p17111 p17115 p21789 p17256 p13951 p17113 p17117 p20467 p16115 p21799 p19665 p17133 p17120 p17245 p17104 p17874 p17127 p17089 p16101 p21770 p21727 p16992 p21798 p17138 p20274 p17060 p20470 p17953 p17050 p16778 p17122 p4983 p16729 p20829 p17009 p20426 p20126 p17110 p17053 p20096 p17131 p17108 p17294 p16943 p17058 p17064 p17067 p17080 p17072 p17074 p17069 p20461 p20836 p20653 p17078 p17136 p17087 p17083 p17055 p17093 p17091 p17098 p17106 p8583 p8549 p17141 p17100 p19610 p17102 p17096 p17147 p15938 p21800 p20827 p16102 p21796
theorem n21803 (_v : Vars) (_q : Query _v)  : (e21802 _v) := by
  by_contra hc
  change ¬ ((¬ (e5145 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e2296 _v)) ∨ (e196 _v)) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h2296 : (e2296 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h5145 : (e5145 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h5195 : (e5195 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn)))))))
  have p21801 := n21801 _v _q h51 h2296 h4306 h4653 h4813 h5145 h5195
  exact p21801
end
end Assembly
