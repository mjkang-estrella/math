import Dag237
import generated.th_lemma_31
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n20754 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h5145 : (e5145 _v)) (h5195 : (e5195 _v)) (h6630 : (e6630 _v)) (h8045 : (e8045 _v)) : (e7489 _v) := by
  have p17953 := n17953 _v _q 
  have p20096 := n20096 _v _q 
  have p20730 := n20730 _v _q h2351
  have p5255 := n5255 _v _q 
  have p17294 := n17294 _v _q 
  have p17058 := n17058 _v _q 
  have p16992 := n16992 _v _q 
  have p16943 := n16943 _v _q 
  have p17157 := n17157 _v _q h8045
  have p13951 := n13951 _v _q 
  have p17064 := n17064 _v _q 
  have p8434 := n8434 _v _q h6630
  have p20732 := n20732 _v _q h2351
  have p8464 := n8464 _v _q h2351
  have p17067 := n17067 _v _q 
  have p17069 := n17069 _v _q 
  have p17080 := n17080 _v _q 
  have p17072 := n17072 _v _q 
  have p17083 := n17083 _v _q 
  have p17074 := n17074 _v _q 
  have p17245 := n17245 _v _q h5145
  have p20678 := n20678 _v _q h2351
  have p20663 := n20663 _v _q h2351
  have p17078 := n17078 _v _q 
  have p20653 := n20653 _v _q 
  have p17087 := n17087 _v _q 
  have p17136 := n17136 _v _q 
  have p15793 := n15793 _v _q h2351
  have p17091 := n17091 _v _q 
  have p17093 := n17093 _v _q 
  have p20682 := n20682 _v _q h2351
  have p17141 := n17141 _v _q 
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p17102 := n17102 _v _q 
  have p17100 := n17100 _v _q 
  have p19610 := n19610 _v _q 
  have p15791 := n15791 _v _q h2351
  have p17122 := n17122 _v _q 
  have p17096 := n17096 _v _q 
  have p15909 := n15909 _v _q h2351
  have p15786 := n15786 _v _q h2351
  have p17758 := n17758 _v _q 
  have p15783 := n15783 _v _q h2351
  have p15911 := n15911 _v _q h2351
  have p15905 := n15905 _v _q h2351
  have p20319 := n20319 _v _q h2351
  have p17115 := n17115 _v _q 
  have p17120 := n17120 _v _q 
  have p17111 := n17111 _v _q 
  have p17124 := n17124 _v _q 
  have p17050 := n17050 _v _q 
  have p16778 := n16778 _v _q 
  have p17113 := n17113 _v _q 
  have p17117 := n17117 _v _q 
  have p20467 := n20467 _v _q 
  have p17104 := n17104 _v _q 
  have p17874 := n17874 _v _q 
  have p17127 := n17127 _v _q 
  have p15914 := n15914 _v _q h2351
  have p20274 := n20274 _v _q 
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
  have p15917 := n15917 _v _q h2351
  have p20751 := n20751 _v _q h2351
  have p15934 := n15934 _v _q h6630
  have p20753 := n20753 _v _q h2351
  have p17276 := n17276 _v _q h5195
  have p8549 := n8549 _v _q h5195
  exact FloorCertificate.node_20754 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2902 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e4541 _v) (e4808 _v) p17953 p20096 p20730 p5255 p17294 p17058 p16992 p16943 p17157 p13951 p17064 p8434 p20732 p8464 p17067 p17069 p17080 p17072 p17083 p17074 p17245 p20678 p20663 p17078 p20653 p17087 p17136 p15793 p17091 p17093 p20682 p17141 p17098 p17106 p17102 p17100 p19610 p15791 p17122 p17096 p15909 p15786 p17758 p15783 p15911 p15905 p20319 p17115 p17120 p17111 p17124 p17050 p16778 p17113 p17117 p20467 p17104 p17874 p17127 p15914 p20274 p20470 p17133 p17089 p19665 p20426 p17055 p17108 p20461 p20126 p17131 p17110 p17053 p15917 p20751 p15934 p20753 p17276 p8549
theorem n20756 (_v : Vars) (_q : Query _v)  : (e20755 _v) := by
  by_contra hc
  change ¬ ((e196 _v) ∨ (¬ (e8045 _v)) ∨ (e2468 _v) ∨ (¬ (e2351 _v)) ∨ (¬ (e5145 _v))) at hc
  have h2351 : (e2351 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h5145 : (e5145 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr hn)))))
  have h5195 : (e5195 _v) := (fun hn => hc (Or.inl hn))
  have h6630 : (e6630 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h8045 : (e8045 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have p20754 := n20754 _v _q h2351 h5145 h5195 h6630 h8045
  exact p20754
theorem n20757 (_v : Vars) (_q : Query _v) (h5138 : (e5138 _v)) : (e8045 _v) := by
  have p15206 := n15206 _v _q 
  have p15936 := n15936 _v _q h5138
  change (e8049 _v) ∨ (e8045 _v) at p15206
  change (¬ (e8049 _v)) at p15936
  rcases p15206 with hlit | hlit
  · exact (False.elim (p15936 hlit))
  · exact hlit
theorem n20758 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h5138 : (e5138 _v)) (h6630 : (e6630 _v)) : (e196 _v) := by
  have p20756 := n20756 _v _q 
  have p20757 := n20757 _v _q h5138
  have p8434 := n8434 _v _q h6630
  have p8464 := n8464 _v _q h2351
  have p15927 := n15927 _v _q h5138
  change (e196 _v) ∨ (¬ (e8045 _v)) ∨ (e2468 _v) ∨ (¬ (e2351 _v)) ∨ (¬ (e5145 _v)) at p20756
  change (¬ (e2468 _v)) at p8434
  rcases p20756 with hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p20757))
  · exact (False.elim (p8434 hlit))
  · exact (False.elim (hlit p8464))
  · exact (False.elim (hlit p15927))
theorem n20759 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h5138 : (e5138 _v)) (h6630 : (e6630 _v)) : (e5203 _v) := by
  have p14730 := n14730 _v _q 
  have p20758 := n20758 _v _q h2351 h5138 h6630
  change (¬ (e196 _v)) ∨ (¬ (e5193 _v)) at p14730
  rcases p14730 with hlit | hlit
  · exact (False.elim (hlit p20758))
  · exact hlit
theorem n20760 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h5138 : (e5138 _v)) (h6630 : (e6630 _v)) : (e191 _v) := by
  have p16442 := n16442 _v _q 
  have p20759 := n20759 _v _q h2351 h5138 h6630
  change (e5193 _v) ∨ (e191 _v) at p16442
  change (¬ (e5193 _v)) at p20759
  rcases p16442 with hlit | hlit
  · exact (False.elim (p20759 hlit))
  · exact hlit
theorem n20761 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h5138 : (e5138 _v)) (h6630 : (e6630 _v)) : (e8320 _v) := by
  have p20730 := n20730 _v _q h2351
  have p8434 := n8434 _v _q h6630
  have p17058 := n17058 _v _q 
  have p16992 := n16992 _v _q 
  have p17294 := n17294 _v _q 
  have p16943 := n16943 _v _q 
  have p20760 := n20760 _v _q h2351 h5138 h6630
  have p20757 := n20757 _v _q h5138
  have p13951 := n13951 _v _q 
  have p17064 := n17064 _v _q 
  have p5255 := n5255 _v _q 
  have p20732 := n20732 _v _q h2351
  have p8464 := n8464 _v _q h2351
  have p17067 := n17067 _v _q 
  have p17069 := n17069 _v _q 
  have p17080 := n17080 _v _q 
  have p17072 := n17072 _v _q 
  have p17083 := n17083 _v _q 
  have p17074 := n17074 _v _q 
  have p20751 := n20751 _v _q h2351
  have p20678 := n20678 _v _q h2351
  have p20663 := n20663 _v _q h2351
  have p17078 := n17078 _v _q 
  have p20653 := n20653 _v _q 
  have p17087 := n17087 _v _q 
  have p17136 := n17136 _v _q 
  have p15793 := n15793 _v _q h2351
  have p17091 := n17091 _v _q 
  have p17093 := n17093 _v _q 
  have p20682 := n20682 _v _q h2351
  have p17141 := n17141 _v _q 
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p17102 := n17102 _v _q 
  have p17100 := n17100 _v _q 
  have p19610 := n19610 _v _q 
  have p15791 := n15791 _v _q h2351
  have p17122 := n17122 _v _q 
  have p17096 := n17096 _v _q 
  have p15909 := n15909 _v _q h2351
  have p15786 := n15786 _v _q h2351
  have p17758 := n17758 _v _q 
  have p15783 := n15783 _v _q h2351
  have p15911 := n15911 _v _q h2351
  have p15905 := n15905 _v _q h2351
  have p20319 := n20319 _v _q h2351
  have p17115 := n17115 _v _q 
  have p17120 := n17120 _v _q 
  have p17111 := n17111 _v _q 
  have p17124 := n17124 _v _q 
  have p17050 := n17050 _v _q 
  have p16778 := n16778 _v _q 
  have p17113 := n17113 _v _q 
  have p17117 := n17117 _v _q 
  have p20467 := n20467 _v _q 
  have p17104 := n17104 _v _q 
  have p17874 := n17874 _v _q 
  have p17127 := n17127 _v _q 
  have p15914 := n15914 _v _q h2351
  have p20274 := n20274 _v _q 
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
  have p15917 := n15917 _v _q h2351
  have p20096 := n20096 _v _q 
  have p15934 := n15934 _v _q h6630
  have p15927 := n15927 _v _q h5138
  have p20753 := n20753 _v _q h2351
  exact FloorCertificate.node_20761 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2902 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e4541 _v) (e4808 _v) p20730 p8434 p17058 p16992 p17294 p16943 p20760 p20757 p13951 p17064 p5255 p20732 p8464 p17067 p17069 p17080 p17072 p17083 p17074 p20751 p20678 p20663 p17078 p20653 p17087 p17136 p15793 p17091 p17093 p20682 p17141 p17098 p17106 p17102 p17100 p19610 p15791 p17122 p17096 p15909 p15786 p17758 p15783 p15911 p15905 p20319 p17115 p17120 p17111 p17124 p17050 p16778 p17113 p17117 p20467 p17104 p17874 p17127 p15914 p20274 p20470 p17133 p17089 p19665 p20426 p17055 p17108 p20461 p20126 p17131 p17110 p17053 p15917 p20096 p15934 p15927 p20753
theorem n20762 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h5138 : (e5138 _v)) (h6630 : (e6630 _v)) : (e8321 _v) := by
  have p11541 := n11541 _v _q 
  have p20761 := n20761 _v _q h2351 h5138 h6630
  change (e8321 _v) ∨ (e8317 _v) at p11541
  change (¬ (e8317 _v)) at p20761
  rcases p11541 with hlit | hlit
  · exact hlit
  · exact (False.elim (p20761 hlit))
theorem n20763 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h5138 : (e5138 _v)) (h6630 : (e6630 _v)) : (e2529 _v) := by
  have p15218 := n15218 _v _q 
  have p20762 := n20762 _v _q h2351 h5138 h6630
  change (e2529 _v) ∨ (¬ (e8321 _v)) at p15218
  rcases p15218 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p20762))
theorem n20764 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h5138 : (e5138 _v)) (h6630 : (e6630 _v)) : (e8307 _v) := by
  have p14906 := n14906 _v _q 
  have p20763 := n20763 _v _q h2351 h5138 h6630
  change (¬ (e2529 _v)) ∨ (¬ (e8301 _v)) at p14906
  rcases p14906 with hlit | hlit
  · exact (False.elim (hlit p20763))
  · exact hlit
theorem n20765 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h5138 : (e5138 _v)) (h6630 : (e6630 _v)) : (e4838 _v) := by
  have p16285 := n16285 _v _q 
  have p20764 := n20764 _v _q h2351 h5138 h6630
  change (e8301 _v) ∨ (e4838 _v) at p16285
  change (¬ (e8301 _v)) at p20764
  rcases p16285 with hlit | hlit
  · exact (False.elim (p20764 hlit))
  · exact hlit
theorem n20766 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h5138 : (e5138 _v)) (h6630 : (e6630 _v)) : (e7489 _v) := by
  have p20753 := n20753 _v _q h2351
  have p20765 := n20765 _v _q h2351 h5138 h6630
  have p8434 := n8434 _v _q h6630
  have p20730 := n20730 _v _q h2351
  have p17058 := n17058 _v _q 
  have p16992 := n16992 _v _q 
  have p17294 := n17294 _v _q 
  have p16943 := n16943 _v _q 
  have p20760 := n20760 _v _q h2351 h5138 h6630
  have p20757 := n20757 _v _q h5138
  have p13951 := n13951 _v _q 
  have p17064 := n17064 _v _q 
  have p5255 := n5255 _v _q 
  have p20732 := n20732 _v _q h2351
  have p8464 := n8464 _v _q h2351
  have p17067 := n17067 _v _q 
  have p17069 := n17069 _v _q 
  have p17080 := n17080 _v _q 
  have p17072 := n17072 _v _q 
  have p17083 := n17083 _v _q 
  have p17074 := n17074 _v _q 
  have p20763 := n20763 _v _q h2351 h5138 h6630
  have p20678 := n20678 _v _q h2351
  have p20663 := n20663 _v _q h2351
  have p17078 := n17078 _v _q 
  have p20653 := n20653 _v _q 
  have p17087 := n17087 _v _q 
  have p17136 := n17136 _v _q 
  have p15793 := n15793 _v _q h2351
  have p17091 := n17091 _v _q 
  have p17093 := n17093 _v _q 
  have p20682 := n20682 _v _q h2351
  have p17141 := n17141 _v _q 
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p17102 := n17102 _v _q 
  have p17100 := n17100 _v _q 
  have p19610 := n19610 _v _q 
  have p15791 := n15791 _v _q h2351
  have p17122 := n17122 _v _q 
  have p17096 := n17096 _v _q 
  have p15909 := n15909 _v _q h2351
  have p15786 := n15786 _v _q h2351
  have p17758 := n17758 _v _q 
  have p15783 := n15783 _v _q h2351
  have p15911 := n15911 _v _q h2351
  have p15905 := n15905 _v _q h2351
  have p20319 := n20319 _v _q h2351
  have p17115 := n17115 _v _q 
  have p17120 := n17120 _v _q 
  have p17111 := n17111 _v _q 
  have p17124 := n17124 _v _q 
  have p17050 := n17050 _v _q 
  have p16778 := n16778 _v _q 
  have p17113 := n17113 _v _q 
  have p17117 := n17117 _v _q 
  have p20467 := n20467 _v _q 
  have p17104 := n17104 _v _q 
  have p17874 := n17874 _v _q 
  have p17127 := n17127 _v _q 
  have p15914 := n15914 _v _q h2351
  have p20274 := n20274 _v _q 
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
  have p15917 := n15917 _v _q h2351
  have p20096 := n20096 _v _q 
  have p15934 := n15934 _v _q h6630
  have p15927 := n15927 _v _q h5138
  have p12954 := n12954 _v _q h5138
  exact FloorCertificate.node_20766 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2902 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e4541 _v) (e4808 _v) p20753 p20765 p8434 p20730 p17058 p16992 p17294 p16943 p20760 p20757 p13951 p17064 p5255 p20732 p8464 p17067 p17069 p17080 p17072 p17083 p17074 p20763 p20678 p20663 p17078 p20653 p17087 p17136 p15793 p17091 p17093 p20682 p17141 p17098 p17106 p17102 p17100 p19610 p15791 p17122 p17096 p15909 p15786 p17758 p15783 p15911 p15905 p20319 p17115 p17120 p17111 p17124 p17050 p16778 p17113 p17117 p20467 p17104 p17874 p17127 p15914 p20274 p20470 p17133 p17089 p19665 p20426 p17055 p17108 p20461 p20126 p17131 p17110 p17053 p15917 p20096 p15934 p15927 p12954
theorem n20768 (_v : Vars) (_q : Query _v)  : (e20767 _v) := by
  by_contra hc
  change ¬ ((e79 _v) ∨ (e2468 _v) ∨ (¬ (e2351 _v))) at hc
  have h2351 : (e2351 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr hn)))
  have h5138 : (e5138 _v) := (fun hn => hc (Or.inl hn))
  have h6630 : (e6630 _v) := (fun hn => hc (Or.inr (Or.inl hn)))
  have p20766 := n20766 _v _q h2351 h5138 h6630
  exact p20766
theorem n20769 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h6630 : (e6630 _v)) : (e79 _v) := by
  have p20768 := n20768 _v _q 
  have p8434 := n8434 _v _q h6630
  have p8464 := n8464 _v _q h2351
  change (e79 _v) ∨ (e2468 _v) ∨ (¬ (e2351 _v)) at p20768
  change (¬ (e2468 _v)) at p8434
  rcases p20768 with hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (p8434 hlit))
  · exact (False.elim (hlit p8464))
theorem n20770 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h6630 : (e6630 _v)) : (e5135 _v) := by
  have p14729 := n14729 _v _q 
  have p20769 := n20769 _v _q h2351 h6630
  change (¬ (e79 _v)) ∨ (¬ (e5134 _v)) at p14729
  rcases p14729 with hlit | hlit
  · exact (False.elim (hlit p20769))
  · exact hlit
theorem n20771 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h6630 : (e6630 _v)) : (e91 _v) := by
  have p16235 := n16235 _v _q 
  have p20770 := n20770 _v _q h2351 h6630
  change (e5134 _v) ∨ (e91 _v) at p16235
  change (¬ (e5134 _v)) at p20770
  rcases p16235 with hlit | hlit
  · exact (False.elim (p20770 hlit))
  · exact hlit
theorem n20772 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h5195 : (e5195 _v)) (h6630 : (e6630 _v)) : (e7489 _v) := by
  have p20730 := n20730 _v _q h2351
  have p20771 := n20771 _v _q h2351 h6630
  have p5257 := n5257 _v _q 
  have p8549 := n8549 _v _q h5195
  have p8434 := n8434 _v _q h6630
  have p17953 := n17953 _v _q 
  have p20753 := n20753 _v _q h2351
  have p17058 := n17058 _v _q 
  have p16992 := n16992 _v _q 
  have p17294 := n17294 _v _q 
  have p16943 := n16943 _v _q 
  have p15938 := n15938 _v _q h5195
  have p13951 := n13951 _v _q 
  have p17064 := n17064 _v _q 
  have p20732 := n20732 _v _q h2351
  have p8464 := n8464 _v _q h2351
  have p17067 := n17067 _v _q 
  have p17069 := n17069 _v _q 
  have p17080 := n17080 _v _q 
  have p17072 := n17072 _v _q 
  have p17083 := n17083 _v _q 
  have p17074 := n17074 _v _q 
  have p17276 := n17276 _v _q h5195
  have p20678 := n20678 _v _q h2351
  have p20663 := n20663 _v _q h2351
  have p17078 := n17078 _v _q 
  have p20653 := n20653 _v _q 
  have p17087 := n17087 _v _q 
  have p17136 := n17136 _v _q 
  have p15793 := n15793 _v _q h2351
  have p17091 := n17091 _v _q 
  have p17093 := n17093 _v _q 
  have p20682 := n20682 _v _q h2351
  have p17141 := n17141 _v _q 
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p17102 := n17102 _v _q 
  have p17100 := n17100 _v _q 
  have p19610 := n19610 _v _q 
  have p15791 := n15791 _v _q h2351
  have p17122 := n17122 _v _q 
  have p17096 := n17096 _v _q 
  have p15909 := n15909 _v _q h2351
  have p15786 := n15786 _v _q h2351
  have p17758 := n17758 _v _q 
  have p15783 := n15783 _v _q h2351
  have p15911 := n15911 _v _q h2351
  have p15905 := n15905 _v _q h2351
  have p20319 := n20319 _v _q h2351
  have p17115 := n17115 _v _q 
  have p17120 := n17120 _v _q 
  have p17111 := n17111 _v _q 
  have p17124 := n17124 _v _q 
  have p17050 := n17050 _v _q 
  have p16778 := n16778 _v _q 
  have p17113 := n17113 _v _q 
  have p17117 := n17117 _v _q 
  have p20467 := n20467 _v _q 
  have p17104 := n17104 _v _q 
  have p17874 := n17874 _v _q 
  have p17127 := n17127 _v _q 
  have p15914 := n15914 _v _q h2351
  have p20274 := n20274 _v _q 
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
  have p15917 := n15917 _v _q h2351
  have p20096 := n20096 _v _q 
  have p15934 := n15934 _v _q h6630
  exact FloorCertificate.node_20772 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2902 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e4541 _v) (e4808 _v) p20730 p20771 p5257 p8549 p8434 p17953 p20753 p17058 p16992 p17294 p16943 p15938 p13951 p17064 p20732 p8464 p17067 p17069 p17080 p17072 p17083 p17074 p17276 p20678 p20663 p17078 p20653 p17087 p17136 p15793 p17091 p17093 p20682 p17141 p17098 p17106 p17102 p17100 p19610 p15791 p17122 p17096 p15909 p15786 p17758 p15783 p15911 p15905 p20319 p17115 p17120 p17111 p17124 p17050 p16778 p17113 p17117 p20467 p17104 p17874 p17127 p15914 p20274 p20470 p17133 p17089 p19665 p20426 p17055 p17108 p20461 p20126 p17131 p17110 p17053 p15917 p20096 p15934
theorem n20774 (_v : Vars) (_q : Query _v)  : (e20773 _v) := by
  by_contra hc
  change ¬ ((e196 _v) ∨ (e2468 _v) ∨ (¬ (e2351 _v))) at hc
  have h2351 : (e2351 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr hn)))
  have h5195 : (e5195 _v) := (fun hn => hc (Or.inl hn))
  have h6630 : (e6630 _v) := (fun hn => hc (Or.inr (Or.inl hn)))
  have p20772 := n20772 _v _q h2351 h5195 h6630
  exact p20772
theorem n20775 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h6630 : (e6630 _v)) : (e196 _v) := by
  have p20774 := n20774 _v _q 
  have p8434 := n8434 _v _q h6630
  have p8464 := n8464 _v _q h2351
  change (e196 _v) ∨ (e2468 _v) ∨ (¬ (e2351 _v)) at p20774
  change (¬ (e2468 _v)) at p8434
  rcases p20774 with hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (p8434 hlit))
  · exact (False.elim (hlit p8464))
theorem n20776 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h6630 : (e6630 _v)) : (e5203 _v) := by
  have p14730 := n14730 _v _q 
  have p20775 := n20775 _v _q h2351 h6630
  change (¬ (e196 _v)) ∨ (¬ (e5193 _v)) at p14730
  rcases p14730 with hlit | hlit
  · exact (False.elim (hlit p20775))
  · exact hlit
theorem n20777 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h6630 : (e6630 _v)) : (e191 _v) := by
  have p16442 := n16442 _v _q 
  have p20776 := n20776 _v _q h2351 h6630
  change (e5193 _v) ∨ (e191 _v) at p16442
  change (¬ (e5193 _v)) at p20776
  rcases p16442 with hlit | hlit
  · exact (False.elim (p20776 hlit))
  · exact hlit
theorem n20778 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h6630 : (e6630 _v)) : (e214 _v) := by
  have p11523 := n11523 _v _q 
  have p20775 := n20775 _v _q h2351 h6630
  change (e214 _v) ∨ (¬ (e196 _v)) at p11523
  rcases p11523 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p20775))
theorem n20779 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h6630 : (e6630 _v)) : (e5232 _v) := by
  have p14731 := n14731 _v _q 
  have p20778 := n20778 _v _q h2351 h6630
  change (¬ (e214 _v)) ∨ (¬ (e5231 _v)) at p14731
  rcases p14731 with hlit | hlit
  · exact (False.elim (hlit p20778))
  · exact hlit
theorem n20780 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h6630 : (e6630 _v)) : (e225 _v) := by
  have p16653 := n16653 _v _q 
  have p20779 := n20779 _v _q h2351 h6630
  change (e5231 _v) ∨ (e225 _v) at p16653
  change (¬ (e5231 _v)) at p20779
  rcases p16653 with hlit | hlit
  · exact (False.elim (p20779 hlit))
  · exact hlit
theorem n20781 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h6630 : (e6630 _v)) (h8310 : (e8310 _v)) : (e7489 _v) := by
  have p5257 := n5257 _v _q 
  have p20769 := n20769 _v _q h2351 h6630
  have p20730 := n20730 _v _q h2351
  have p331 := n331 _v _q 
  have p8464 := n8464 _v _q h2351
  have p8434 := n8434 _v _q h6630
  have p20777 := n20777 _v _q h2351 h6630
  have p20771 := n20771 _v _q h2351 h6630
  have p20753 := n20753 _v _q h2351
  have p17058 := n17058 _v _q 
  have p15934 := n15934 _v _q h6630
  have p17294 := n17294 _v _q 
  have p16943 := n16943 _v _q 
  have p17453 := n17453 _v _q h8310
  have p13951 := n13951 _v _q 
  have p17064 := n17064 _v _q 
  have p20732 := n20732 _v _q h2351
  have p17067 := n17067 _v _q 
  have p17069 := n17069 _v _q 
  have p17080 := n17080 _v _q 
  have p17072 := n17072 _v _q 
  have p17083 := n17083 _v _q 
  have p17074 := n17074 _v _q 
  have p15248 := n15248 _v _q h8310
  have p20678 := n20678 _v _q h2351
  have p20663 := n20663 _v _q h2351
  have p17078 := n17078 _v _q 
  have p20653 := n20653 _v _q 
  have p17087 := n17087 _v _q 
  have p17136 := n17136 _v _q 
  have p15793 := n15793 _v _q h2351
  have p17091 := n17091 _v _q 
  have p17093 := n17093 _v _q 
  have p20682 := n20682 _v _q h2351
  have p17141 := n17141 _v _q 
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p17102 := n17102 _v _q 
  have p17100 := n17100 _v _q 
  have p19610 := n19610 _v _q 
  have p15791 := n15791 _v _q h2351
  have p17122 := n17122 _v _q 
  have p17096 := n17096 _v _q 
  have p15909 := n15909 _v _q h2351
  have p15786 := n15786 _v _q h2351
  have p17758 := n17758 _v _q 
  have p15783 := n15783 _v _q h2351
  have p15911 := n15911 _v _q h2351
  have p15905 := n15905 _v _q h2351
  have p20319 := n20319 _v _q h2351
  have p17115 := n17115 _v _q 
  have p17120 := n17120 _v _q 
  have p17111 := n17111 _v _q 
  have p17124 := n17124 _v _q 
  have p17050 := n17050 _v _q 
  have p16778 := n16778 _v _q 
  have p17113 := n17113 _v _q 
  have p17117 := n17117 _v _q 
  have p20467 := n20467 _v _q 
  have p17104 := n17104 _v _q 
  have p17874 := n17874 _v _q 
  have p17127 := n17127 _v _q 
  have p15914 := n15914 _v _q h2351
  have p20274 := n20274 _v _q 
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
  have p15917 := n15917 _v _q h2351
  have p20096 := n20096 _v _q 
  have p20780 := n20780 _v _q h2351 h6630
  exact FloorCertificate.node_20781 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2902 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e4541 _v) (e4808 _v) p5257 p20769 p20730 p331 p8464 p8434 p20777 p20771 p20753 p17058 p15934 p17294 p16943 p17453 p13951 p17064 p20732 p17067 p17069 p17080 p17072 p17083 p17074 p15248 p20678 p20663 p17078 p20653 p17087 p17136 p15793 p17091 p17093 p20682 p17141 p17098 p17106 p17102 p17100 p19610 p15791 p17122 p17096 p15909 p15786 p17758 p15783 p15911 p15905 p20319 p17115 p17120 p17111 p17124 p17050 p16778 p17113 p17117 p20467 p17104 p17874 p17127 p15914 p20274 p20470 p17133 p17089 p19665 p20426 p17055 p17108 p20461 p20126 p17131 p17110 p17053 p15917 p20096 p20780
theorem n20783 (_v : Vars) (_q : Query _v)  : (e20782 _v) := by
  by_contra hc
  change ¬ ((e2529 _v) ∨ (¬ (e2351 _v)) ∨ (e2468 _v)) at hc
  have h2351 : (e2351 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h6630 : (e6630 _v) := (fun hn => hc (Or.inr (Or.inr hn)))
  have h8310 : (e8310 _v) := (fun hn => hc (Or.inl hn))
  have p20781 := n20781 _v _q h2351 h6630 h8310
  exact p20781
theorem n20784 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h6630 : (e6630 _v)) : (e2529 _v) := by
  have p20783 := n20783 _v _q 
  have p8434 := n8434 _v _q h6630
  have p8464 := n8464 _v _q h2351
  change (e2529 _v) ∨ (¬ (e2351 _v)) ∨ (e2468 _v) at p20783
  change (¬ (e2468 _v)) at p8434
  rcases p20783 with hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p8464))
  · exact (False.elim (p8434 hlit))
theorem n20785 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h6630 : (e6630 _v)) : (e8307 _v) := by
  have p14906 := n14906 _v _q 
  have p20784 := n20784 _v _q h2351 h6630
  change (¬ (e2529 _v)) ∨ (¬ (e8301 _v)) at p14906
  rcases p14906 with hlit | hlit
  · exact (False.elim (hlit p20784))
  · exact hlit
theorem n20786 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h6630 : (e6630 _v)) : (e4838 _v) := by
  have p16285 := n16285 _v _q 
  have p20785 := n20785 _v _q h2351 h6630
  change (e8301 _v) ∨ (e4838 _v) at p16285
  change (¬ (e8301 _v)) at p20785
  rcases p16285 with hlit | hlit
  · exact (False.elim (p20785 hlit))
  · exact hlit
theorem n20787 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h4546 : (e4546 _v)) (h6630 : (e6630 _v)) : (e7489 _v) := by
  have p5257 := n5257 _v _q 
  have p20786 := n20786 _v _q h2351 h6630
  have p258 := n258 _v _q 
  have p8434 := n8434 _v _q h6630
  have p4976 := n4976 _v _q h4546
  have p20096 := n20096 _v _q 
  have p20780 := n20780 _v _q h2351 h6630
  have p20777 := n20777 _v _q h2351 h6630
  have p20771 := n20771 _v _q h2351 h6630
  have p20753 := n20753 _v _q h2351
  have p17058 := n17058 _v _q 
  have p15934 := n15934 _v _q h6630
  have p17294 := n17294 _v _q 
  have p16943 := n16943 _v _q 
  have p13951 := n13951 _v _q 
  have p17064 := n17064 _v _q 
  have p20732 := n20732 _v _q h2351
  have p15917 := n15917 _v _q h2351
  have p17067 := n17067 _v _q 
  have p17069 := n17069 _v _q 
  have p17080 := n17080 _v _q 
  have p17072 := n17072 _v _q 
  have p17083 := n17083 _v _q 
  have p17074 := n17074 _v _q 
  have p20678 := n20678 _v _q h2351
  have p20663 := n20663 _v _q h2351
  have p17078 := n17078 _v _q 
  have p20653 := n20653 _v _q 
  have p17087 := n17087 _v _q 
  have p17136 := n17136 _v _q 
  have p15793 := n15793 _v _q h2351
  have p17091 := n17091 _v _q 
  have p17093 := n17093 _v _q 
  have p20682 := n20682 _v _q h2351
  have p17141 := n17141 _v _q 
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p17102 := n17102 _v _q 
  have p17100 := n17100 _v _q 
  have p19610 := n19610 _v _q 
  have p15791 := n15791 _v _q h2351
  have p17122 := n17122 _v _q 
  have p17096 := n17096 _v _q 
  have p15909 := n15909 _v _q h2351
  have p15786 := n15786 _v _q h2351
  have p17758 := n17758 _v _q 
  have p15783 := n15783 _v _q h2351
  have p15911 := n15911 _v _q h2351
  have p15905 := n15905 _v _q h2351
  have p20319 := n20319 _v _q h2351
  have p17115 := n17115 _v _q 
  have p17120 := n17120 _v _q 
  have p17111 := n17111 _v _q 
  have p17124 := n17124 _v _q 
  have p17050 := n17050 _v _q 
  have p16778 := n16778 _v _q 
  have p17113 := n17113 _v _q 
  have p17117 := n17117 _v _q 
  have p20467 := n20467 _v _q 
  have p17104 := n17104 _v _q 
  have p17874 := n17874 _v _q 
  have p17127 := n17127 _v _q 
  have p15914 := n15914 _v _q h2351
  have p20274 := n20274 _v _q 
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
  have p20730 := n20730 _v _q h2351
  have p8464 := n8464 _v _q h2351
  have p20769 := n20769 _v _q h2351 h6630
  exact FloorCertificate.node_20787 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2902 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e4541 _v) (e4808 _v) p5257 p20786 p258 p8434 p4976 p20096 p20780 p20777 p20771 p20753 p17058 p15934 p17294 p16943 p13951 p17064 p20732 p15917 p17067 p17069 p17080 p17072 p17083 p17074 p20678 p20663 p17078 p20653 p17087 p17136 p15793 p17091 p17093 p20682 p17141 p17098 p17106 p17102 p17100 p19610 p15791 p17122 p17096 p15909 p15786 p17758 p15783 p15911 p15905 p20319 p17115 p17120 p17111 p17124 p17050 p16778 p17113 p17117 p20467 p17104 p17874 p17127 p15914 p20274 p20470 p17133 p17089 p19665 p20426 p17055 p17108 p20461 p20126 p17131 p17110 p17053 p20730 p8464 p20769
theorem n20789 (_v : Vars) (_q : Query _v)  : (e20788 _v) := by
  by_contra hc
  change ¬ ((¬ (e4546 _v)) ∨ (e2468 _v) ∨ (¬ (e2351 _v))) at hc
  have h2351 : (e2351 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr hn)))
  have h4546 : (e4546 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h6630 : (e6630 _v) := (fun hn => hc (Or.inr (Or.inl hn)))
  have p20787 := n20787 _v _q h2351 h4546 h6630
  exact p20787
theorem n20790 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h6630 : (e6630 _v)) : (e4547 _v) := by
  have p20789 := n20789 _v _q 
  have p8434 := n8434 _v _q h6630
  have p8464 := n8464 _v _q h2351
  change (¬ (e4546 _v)) ∨ (e2468 _v) ∨ (¬ (e2351 _v)) at p20789
  change (¬ (e2468 _v)) at p8434
  rcases p20789 with hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (p8434 hlit))
  · exact (False.elim (hlit p8464))
theorem n20791 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h6630 : (e6630 _v)) : (e8029 _v) := by
  have p16307 := n16307 _v _q 
  have p20790 := n20790 _v _q h2351 h6630
  change (e8029 _v) ∨ (e4546 _v) at p16307
  change (¬ (e4546 _v)) at p20790
  rcases p16307 with hlit | hlit
  · exact hlit
  · exact (False.elim (p20790 hlit))
theorem n20792 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h6630 : (e6630 _v)) : (e8038 _v) := by
  have p14871 := n14871 _v _q 
  have p20791 := n20791 _v _q h2351 h6630
  change (¬ (e2475 _v)) ∨ (¬ (e8029 _v)) at p14871
  rcases p14871 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p20791))
theorem n20793 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h6630 : (e6630 _v)) : (e8050 _v) := by
  have p15207 := n15207 _v _q 
  have p20792 := n20792 _v _q h2351 h6630
  change (e2475 _v) ∨ (¬ (e8049 _v)) at p15207
  change (¬ (e2475 _v)) at p20792
  rcases p15207 with hlit | hlit
  · exact (False.elim (p20792 hlit))
  · exact hlit
theorem n20794 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h6630 : (e6630 _v)) : (e8045 _v) := by
  have p15206 := n15206 _v _q 
  have p20793 := n20793 _v _q h2351 h6630
  change (e8049 _v) ∨ (e8045 _v) at p15206
  change (¬ (e8049 _v)) at p20793
  rcases p15206 with hlit | hlit
  · exact (False.elim (p20793 hlit))
  · exact hlit
theorem n20795 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h6630 : (e6630 _v)) : (e7489 _v) := by
  have p20794 := n20794 _v _q h2351 h6630
  have p20792 := n20792 _v _q h2351 h6630
  have p20786 := n20786 _v _q h2351 h6630
  have p20769 := n20769 _v _q h2351 h6630
  have p8434 := n8434 _v _q h6630
  have p20096 := n20096 _v _q 
  have p20780 := n20780 _v _q h2351 h6630
  have p20777 := n20777 _v _q h2351 h6630
  have p20771 := n20771 _v _q h2351 h6630
  have p20753 := n20753 _v _q h2351
  have p17058 := n17058 _v _q 
  have p15934 := n15934 _v _q h6630
  have p17294 := n17294 _v _q 
  have p16943 := n16943 _v _q 
  have p13951 := n13951 _v _q 
  have p17064 := n17064 _v _q 
  have p20732 := n20732 _v _q h2351
  have p15917 := n15917 _v _q h2351
  have p17067 := n17067 _v _q 
  have p17069 := n17069 _v _q 
  have p17080 := n17080 _v _q 
  have p17072 := n17072 _v _q 
  have p17083 := n17083 _v _q 
  have p17074 := n17074 _v _q 
  have p20678 := n20678 _v _q h2351
  have p20663 := n20663 _v _q h2351
  have p17078 := n17078 _v _q 
  have p20653 := n20653 _v _q 
  have p17087 := n17087 _v _q 
  have p17136 := n17136 _v _q 
  have p15793 := n15793 _v _q h2351
  have p17091 := n17091 _v _q 
  have p17093 := n17093 _v _q 
  have p20682 := n20682 _v _q h2351
  have p17141 := n17141 _v _q 
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p17102 := n17102 _v _q 
  have p17100 := n17100 _v _q 
  have p19610 := n19610 _v _q 
  have p15791 := n15791 _v _q h2351
  have p17122 := n17122 _v _q 
  have p17096 := n17096 _v _q 
  have p15909 := n15909 _v _q h2351
  have p15786 := n15786 _v _q h2351
  have p17758 := n17758 _v _q 
  have p15783 := n15783 _v _q h2351
  have p15911 := n15911 _v _q h2351
  have p15905 := n15905 _v _q h2351
  have p20319 := n20319 _v _q h2351
  have p17115 := n17115 _v _q 
  have p17120 := n17120 _v _q 
  have p17111 := n17111 _v _q 
  have p17124 := n17124 _v _q 
  have p17050 := n17050 _v _q 
  have p16778 := n16778 _v _q 
  have p17113 := n17113 _v _q 
  have p17117 := n17117 _v _q 
  have p20467 := n20467 _v _q 
  have p17104 := n17104 _v _q 
  have p17874 := n17874 _v _q 
  have p17127 := n17127 _v _q 
  have p15914 := n15914 _v _q h2351
  have p20274 := n20274 _v _q 
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
  have p20730 := n20730 _v _q h2351
  have p8464 := n8464 _v _q h2351
  have p20784 := n20784 _v _q h2351 h6630
  exact FloorCertificate.node_20795 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2902 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e4541 _v) (e4808 _v) p20794 p20792 p20786 p20769 p8434 p20096 p20780 p20777 p20771 p20753 p17058 p15934 p17294 p16943 p13951 p17064 p20732 p15917 p17067 p17069 p17080 p17072 p17083 p17074 p20678 p20663 p17078 p20653 p17087 p17136 p15793 p17091 p17093 p20682 p17141 p17098 p17106 p17102 p17100 p19610 p15791 p17122 p17096 p15909 p15786 p17758 p15783 p15911 p15905 p20319 p17115 p17120 p17111 p17124 p17050 p16778 p17113 p17117 p20467 p17104 p17874 p17127 p15914 p20274 p20470 p17133 p17089 p19665 p20426 p17055 p17108 p20461 p20126 p17131 p17110 p17053 p20730 p8464 p20784
theorem n20797 (_v : Vars) (_q : Query _v)  : (e20796 _v) := by
  by_contra hc
  change ¬ ((e2468 _v) ∨ (¬ (e2351 _v))) at hc
  have h2351 : (e2351 _v) := Classical.byContradiction (fun hn => hc (Or.inr hn))
  have h6630 : (e6630 _v) := (fun hn => hc (Or.inl hn))
  have p20795 := n20795 _v _q h2351 h6630
  exact p20795
theorem n20798 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) : (e2468 _v) := by
  have p20797 := n20797 _v _q 
  have p8464 := n8464 _v _q h2351
  change (e2468 _v) ∨ (¬ (e2351 _v)) at p20797
  rcases p20797 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p8464))
theorem n20799 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) : (e4798 _v) := by
  have p14690 := n14690 _v _q 
  have p20798 := n20798 _v _q h2351
  change (¬ (e2468 _v)) ∨ (¬ (e4797 _v)) at p14690
  rcases p14690 with hlit | hlit
  · exact (False.elim (hlit p20798))
  · exact hlit
theorem n20800 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) : (e4791 _v) := by
  have p14932 := n14932 _v _q 
  have p20799 := n20799 _v _q h2351
  change (e4797 _v) ∨ (e4791 _v) at p14932
  change (¬ (e4797 _v)) at p20799
  rcases p14932 with hlit | hlit
  · exact (False.elim (p20799 hlit))
  · exact hlit
theorem n20801 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h5145 : (e5145 _v)) (h5223 : (e5223 _v)) (h8317 : (e8317 _v)) : (e7489 _v) := by
  have p20126 := n20126 _v _q 
  have p20730 := n20730 _v _q h2351
  have p20751 := n20751 _v _q h2351
  have p16992 := n16992 _v _q 
  have p13951 := n13951 _v _q 
  have p17245 := n17245 _v _q h5145
  have p17953 := n17953 _v _q 
  have p5255 := n5255 _v _q 
  have p17110 := n17110 _v _q 
  have p17174 := n17174 _v _q h8317
  have p20800 := n20800 _v _q h2351
  have p17053 := n17053 _v _q 
  have p17131 := n17131 _v _q 
  have p20096 := n20096 _v _q 
  have p8464 := n8464 _v _q h2351
  have p20753 := n20753 _v _q h2351
  have p17058 := n17058 _v _q 
  have p17294 := n17294 _v _q 
  have p16943 := n16943 _v _q 
  have p17064 := n17064 _v _q 
  have p20732 := n20732 _v _q h2351
  have p15917 := n15917 _v _q h2351
  have p17067 := n17067 _v _q 
  have p17069 := n17069 _v _q 
  have p17080 := n17080 _v _q 
  have p17072 := n17072 _v _q 
  have p17083 := n17083 _v _q 
  have p17074 := n17074 _v _q 
  have p20678 := n20678 _v _q h2351
  have p20663 := n20663 _v _q h2351
  have p17078 := n17078 _v _q 
  have p20653 := n20653 _v _q 
  have p17087 := n17087 _v _q 
  have p17136 := n17136 _v _q 
  have p15793 := n15793 _v _q h2351
  have p17091 := n17091 _v _q 
  have p17093 := n17093 _v _q 
  have p20682 := n20682 _v _q h2351
  have p17141 := n17141 _v _q 
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p17102 := n17102 _v _q 
  have p17100 := n17100 _v _q 
  have p19610 := n19610 _v _q 
  have p15791 := n15791 _v _q h2351
  have p17122 := n17122 _v _q 
  have p17096 := n17096 _v _q 
  have p15909 := n15909 _v _q h2351
  have p15786 := n15786 _v _q h2351
  have p17758 := n17758 _v _q 
  have p15783 := n15783 _v _q h2351
  have p15911 := n15911 _v _q h2351
  have p15905 := n15905 _v _q h2351
  have p20319 := n20319 _v _q h2351
  have p17115 := n17115 _v _q 
  have p17120 := n17120 _v _q 
  have p17111 := n17111 _v _q 
  have p17124 := n17124 _v _q 
  have p17050 := n17050 _v _q 
  have p16778 := n16778 _v _q 
  have p17113 := n17113 _v _q 
  have p17117 := n17117 _v _q 
  have p20467 := n20467 _v _q 
  have p17104 := n17104 _v _q 
  have p17874 := n17874 _v _q 
  have p17127 := n17127 _v _q 
  have p15914 := n15914 _v _q h2351
  have p20274 := n20274 _v _q 
  have p20470 := n20470 _v _q 
  have p17133 := n17133 _v _q 
  have p17089 := n17089 _v _q 
  have p19665 := n19665 _v _q 
  have p20426 := n20426 _v _q 
  have p17055 := n17055 _v _q 
  have p17108 := n17108 _v _q 
  have p20461 := n20461 _v _q 
  have p11520 := n11520 _v _q h5223
  exact FloorCertificate.node_20801 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2902 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e4808 _v) p20126 p20730 p20751 p16992 p13951 p17245 p17953 p5255 p17110 p17174 p20800 p17053 p17131 p20096 p8464 p20753 p17058 p17294 p16943 p17064 p20732 p15917 p17067 p17069 p17080 p17072 p17083 p17074 p20678 p20663 p17078 p20653 p17087 p17136 p15793 p17091 p17093 p20682 p17141 p17098 p17106 p17102 p17100 p19610 p15791 p17122 p17096 p15909 p15786 p17758 p15783 p15911 p15905 p20319 p17115 p17120 p17111 p17124 p17050 p16778 p17113 p17117 p20467 p17104 p17874 p17127 p15914 p20274 p20470 p17133 p17089 p19665 p20426 p17055 p17108 p20461 p11520
theorem n20803 (_v : Vars) (_q : Query _v)  : (e20802 _v) := by
  by_contra hc
  change ¬ ((e214 _v) ∨ (¬ (e5145 _v)) ∨ (¬ (e8317 _v)) ∨ (¬ (e2351 _v))) at hc
  have h2351 : (e2351 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr hn))))
  have h5145 : (e5145 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h5223 : (e5223 _v) := (fun hn => hc (Or.inl hn))
  have h8317 : (e8317 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have p20801 := n20801 _v _q h2351 h5145 h5223 h8317
  exact p20801
theorem n20804 (_v : Vars) (_q : Query _v) (h5138 : (e5138 _v)) : (e8317 _v) := by
  have p11541 := n11541 _v _q 
  have p15929 := n15929 _v _q h5138
  change (e8321 _v) ∨ (e8317 _v) at p11541
  change (¬ (e8321 _v)) at p15929
  rcases p11541 with hlit | hlit
  · exact (False.elim (p15929 hlit))
  · exact hlit
theorem n20805 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h5138 : (e5138 _v)) : (e214 _v) := by
  have p20803 := n20803 _v _q 
  have p15927 := n15927 _v _q h5138
  have p20804 := n20804 _v _q h5138
  have p8464 := n8464 _v _q h2351
  change (e214 _v) ∨ (¬ (e5145 _v)) ∨ (¬ (e8317 _v)) ∨ (¬ (e2351 _v)) at p20803
  rcases p20803 with hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p15927))
  · exact (False.elim (hlit p20804))
  · exact (False.elim (hlit p8464))
end
end Assembly
