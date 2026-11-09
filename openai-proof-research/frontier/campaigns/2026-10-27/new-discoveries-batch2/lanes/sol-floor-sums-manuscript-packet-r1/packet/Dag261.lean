import Dag260
import generated.th_lemma_35
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n21903 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6454 : (e6454 _v)) : (e6776 _v) := by
  have p21900 := n21900 _v _q h51 h4306 h4653 h4813
  have p5255 := n5255 _v _q 
  have p8430 := n8430 _v _q h6454
  exact FloorCertificate.node_21903 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p21900 p5255 p8430
theorem n21904 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6454 : (e6454 _v)) : (e7789 _v) := by
  have p14570 := n14570 _v _q 
  have p21903 := n21903 _v _q h51 h4306 h4653 h4813 h6454
  change (e2781 _v) ∨ (¬ (e7781 _v)) at p14570
  change (¬ (e2781 _v)) at p21903
  rcases p14570 with hlit | hlit
  · exact (False.elim (p21903 hlit))
  · exact hlit
theorem n21905 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e5203 _v) := by
  have p14730 := n14730 _v _q 
  have p21899 := n21899 _v _q h51 h4306 h4653 h4813
  change (¬ (e196 _v)) ∨ (¬ (e5193 _v)) at p14730
  rcases p14730 with hlit | hlit
  · exact (False.elim (hlit p21899))
  · exact hlit
theorem n21906 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e191 _v) := by
  have p16442 := n16442 _v _q 
  have p21905 := n21905 _v _q h51 h4306 h4653 h4813
  change (e5193 _v) ∨ (e191 _v) at p16442
  change (¬ (e5193 _v)) at p21905
  rcases p16442 with hlit | hlit
  · exact (False.elim (p21905 hlit))
  · exact hlit
theorem n21907 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2468 : (e2468 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e4101 _v) := by
  have p14929 := n14929 _v _q 
  have p21203 := n21203 _v _q h51 h2468 h4306 h4653 h4813
  change (e4108 _v) ∨ (e4101 _v) at p14929
  change (¬ (e4108 _v)) at p21203
  rcases p14929 with hlit | hlit
  · exact (False.elim (p21203 hlit))
  · exact hlit
theorem n21908 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) : (e4459 _v) := by
  have p8443 := n8443 _v _q 
  have p16122 := n16122 _v _q h2468
  change (e4465 _v) ∨ (e4459 _v) at p8443
  change (¬ (e4465 _v)) at p16122
  rcases p8443 with hlit | hlit
  · exact (False.elim (p16122 hlit))
  · exact hlit
theorem n21909 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2296 : (e2296 _v)) (h2468 : (e2468 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5145 : (e5145 _v)) : (e7489 _v) := by
  have p8583 := n8583 _v _q h2296
  have p5257 := n5257 _v _q 
  have p21900 := n21900 _v _q h51 h4306 h4653 h4813
  have p8438 := n8438 _v _q h2468
  have p13951 := n13951 _v _q 
  have p20651 := n20651 _v _q 
  have p17136 := n17136 _v _q 
  have p21902 := n21902 _v _q h51 h4306 h4653 h4813
  have p17087 := n17087 _v _q 
  have p17055 := n17055 _v _q 
  have p15073 := n15073 _v _q h2468
  have p17098 := n17098 _v _q 
  have p15104 := n15104 _v _q h2468
  have p21907 := n21907 _v _q h51 h2468 h4306 h4653 h4813
  have p17083 := n17083 _v _q 
  have p16074 := n16074 _v _q h2468
  have p17106 := n17106 _v _q 
  have p17020 := n17020 _v _q 
  have p17093 := n17093 _v _q 
  have p17245 := n17245 _v _q h5145
  have p16859 := n16859 _v _q h2468
  have p17100 := n17100 _v _q 
  have p16067 := n16067 _v _q h2468
  have p17141 := n17141 _v _q 
  have p17102 := n17102 _v _q 
  have p17091 := n17091 _v _q 
  have p15100 := n15100 _v _q h2296
  have p17096 := n17096 _v _q 
  have p21748 := n21748 _v _q h51 h4306 h4653 h4813
  have p16120 := n16120 _v _q h2296 h2468
  have p17758 := n17758 _v _q 
  have p21908 := n21908 _v _q h2468
  have p17124 := n17124 _v _q 
  have p19610 := n19610 _v _q 
  have p17111 := n17111 _v _q 
  have p17115 := n17115 _v _q 
  have p17256 := n17256 _v _q 
  have p17078 := n17078 _v _q 
  have p17113 := n17113 _v _q 
  have p17117 := n17117 _v _q 
  have p20467 := n20467 _v _q 
  have p19665 := n19665 _v _q 
  have p17133 := n17133 _v _q 
  have p17120 := n17120 _v _q 
  have p17104 := n17104 _v _q 
  have p17874 := n17874 _v _q 
  have p17127 := n17127 _v _q 
  have p17089 := n17089 _v _q 
  have p20653 := n20653 _v _q 
  have p21727 := n21727 _v _q h51 h4306 h4653 h4813
  have p17138 := n17138 _v _q h4306
  have p20274 := n20274 _v _q 
  have p17060 := n17060 _v _q h4653
  have p20470 := n20470 _v _q 
  have p17050 := n17050 _v _q 
  have p16778 := n16778 _v _q 
  have p17122 := n17122 _v _q 
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p20829 := n20829 _v _q 
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
  exact FloorCertificate.node_21909 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2902 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e4808 _v) p8583 p5257 p21900 p8438 p13951 p20651 p17136 p21902 p17087 p17055 p15073 p17098 p15104 p21907 p17083 p16074 p17106 p17020 p17093 p17245 p16859 p17100 p16067 p17141 p17102 p17091 p15100 p17096 p21748 p16120 p17758 p21908 p17124 p19610 p17111 p17115 p17256 p17078 p17113 p17117 p20467 p19665 p17133 p17120 p17104 p17874 p17127 p17089 p20653 p21727 p17138 p20274 p17060 p20470 p17050 p16778 p17122 p4983 p16729 p20829 p20426 p20126 p17110 p17053 p20096 p17131 p17108 p17294 p16943 p17058 p17064 p17067 p17080 p17072 p17074 p17069 p20461 p20836
theorem n21910 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6454 : (e6454 _v)) : (e4260 _v) := by
  have p15824 := n15824 _v _q 
  have p21904 := n21904 _v _q h51 h4306 h4653 h4813 h6454
  change (e7781 _v) ∨ (e4260 _v) at p15824
  change (¬ (e7781 _v)) at p21904
  rcases p15824 with hlit | hlit
  · exact (False.elim (p21904 hlit))
  · exact hlit
theorem n21912 (_v : Vars) (_q : Query _v)  : (e21911 _v) := by
  by_contra hc
  change ¬ ((¬ (e5145 _v)) ∨ (¬ (e2296 _v)) ∨ (¬ (e2468 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v))) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn)))))))
  have h2296 : (e2296 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h2468 : (e2468 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h5145 : (e5145 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have p21909 := n21909 _v _q h51 h2296 h2468 h4306 h4653 h4813 h5145
  exact p21909
theorem n21913 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2296 : (e2296 _v)) (h2468 : (e2468 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e5148 _v) := by
  have p21912 := n21912 _v _q 
  have p8583 := n8583 _v _q h2296
  have p8438 := n8438 _v _q h2468
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  change (¬ (e5145 _v)) ∨ (¬ (e2296 _v)) ∨ (¬ (e2468 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) at p21912
  rcases p21912 with hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p8583))
  · exact (False.elim (hlit p8438))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p16729))
theorem n21914 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2296 : (e2296 _v)) (h2468 : (e2468 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e5149 _v) := by
  have p15925 := n15925 _v _q 
  have p21913 := n21913 _v _q h51 h2296 h2468 h4306 h4653 h4813
  change (e5149 _v) ∨ (e5145 _v) at p15925
  change (¬ (e5145 _v)) at p21913
  rcases p15925 with hlit | hlit
  · exact hlit
  · exact (False.elim (p21913 hlit))
theorem n21915 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2296 : (e2296 _v)) (h2468 : (e2468 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e79 _v) := by
  have p15115 := n15115 _v _q 
  have p21914 := n21914 _v _q h51 h2296 h2468 h4306 h4653 h4813
  change (e79 _v) ∨ (¬ (e5149 _v)) at p15115
  rcases p15115 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p21914))
theorem n21916 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2296 : (e2296 _v)) (h2468 : (e2468 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e5135 _v) := by
  have p14729 := n14729 _v _q 
  have p21915 := n21915 _v _q h51 h2296 h2468 h4306 h4653 h4813
  change (¬ (e79 _v)) ∨ (¬ (e5134 _v)) at p14729
  rcases p14729 with hlit | hlit
  · exact (False.elim (hlit p21915))
  · exact hlit
theorem n21917 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2296 : (e2296 _v)) (h2468 : (e2468 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e91 _v) := by
  have p16235 := n16235 _v _q 
  have p21916 := n21916 _v _q h51 h2296 h2468 h4306 h4653 h4813
  change (e5134 _v) ∨ (e91 _v) at p16235
  change (¬ (e5134 _v)) at p21916
  rcases p16235 with hlit | hlit
  · exact (False.elim (p21916 hlit))
  · exact hlit
theorem n21918 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2296 : (e2296 _v)) (h2468 : (e2468 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e7489 _v) := by
  have p8583 := n8583 _v _q h2296
  have p5257 := n5257 _v _q 
  have p21900 := n21900 _v _q h51 h4306 h4653 h4813
  have p8438 := n8438 _v _q h2468
  have p13951 := n13951 _v _q 
  have p20836 := n20836 _v _q 
  have p17136 := n17136 _v _q 
  have p21902 := n21902 _v _q h51 h4306 h4653 h4813
  have p17087 := n17087 _v _q 
  have p17055 := n17055 _v _q 
  have p15073 := n15073 _v _q h2468
  have p17098 := n17098 _v _q 
  have p15104 := n15104 _v _q h2468
  have p21907 := n21907 _v _q h51 h2468 h4306 h4653 h4813
  have p17083 := n17083 _v _q 
  have p16074 := n16074 _v _q h2468
  have p17106 := n17106 _v _q 
  have p17020 := n17020 _v _q 
  have p17093 := n17093 _v _q 
  have p21913 := n21913 _v _q h51 h2296 h2468 h4306 h4653 h4813
  have p16859 := n16859 _v _q h2468
  have p17100 := n17100 _v _q 
  have p16067 := n16067 _v _q h2468
  have p17141 := n17141 _v _q 
  have p17102 := n17102 _v _q 
  have p17091 := n17091 _v _q 
  have p15100 := n15100 _v _q h2296
  have p17096 := n17096 _v _q 
  have p21748 := n21748 _v _q h51 h4306 h4653 h4813
  have p16120 := n16120 _v _q h2296 h2468
  have p17758 := n17758 _v _q 
  have p21908 := n21908 _v _q h2468
  have p17124 := n17124 _v _q 
  have p19610 := n19610 _v _q 
  have p17111 := n17111 _v _q 
  have p17115 := n17115 _v _q 
  have p17256 := n17256 _v _q 
  have p17078 := n17078 _v _q 
  have p17113 := n17113 _v _q 
  have p17117 := n17117 _v _q 
  have p20467 := n20467 _v _q 
  have p19665 := n19665 _v _q 
  have p17133 := n17133 _v _q 
  have p17120 := n17120 _v _q 
  have p17104 := n17104 _v _q 
  have p17874 := n17874 _v _q 
  have p17127 := n17127 _v _q 
  have p17089 := n17089 _v _q 
  have p20653 := n20653 _v _q 
  have p21727 := n21727 _v _q h51 h4306 h4653 h4813
  have p17138 := n17138 _v _q h4306
  have p20274 := n20274 _v _q 
  have p17060 := n17060 _v _q h4653
  have p20470 := n20470 _v _q 
  have p17050 := n17050 _v _q 
  have p16778 := n16778 _v _q 
  have p17122 := n17122 _v _q 
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p20829 := n20829 _v _q 
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
  have p258 := n258 _v _q 
  have p21917 := n21917 _v _q h51 h2296 h2468 h4306 h4653 h4813
  exact FloorCertificate.node_21918 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2902 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e4808 _v) p8583 p5257 p21900 p8438 p13951 p20836 p17136 p21902 p17087 p17055 p15073 p17098 p15104 p21907 p17083 p16074 p17106 p17020 p17093 p21913 p16859 p17100 p16067 p17141 p17102 p17091 p15100 p17096 p21748 p16120 p17758 p21908 p17124 p19610 p17111 p17115 p17256 p17078 p17113 p17117 p20467 p19665 p17133 p17120 p17104 p17874 p17127 p17089 p20653 p21727 p17138 p20274 p17060 p20470 p17050 p16778 p17122 p4983 p16729 p20829 p20426 p20126 p17110 p17053 p20096 p17131 p17108 p17294 p16943 p17058 p17064 p17067 p17080 p17072 p17074 p17069 p20461 p258 p21917
theorem n21920 (_v : Vars) (_q : Query _v)  : (e21919 _v) := by
  by_contra hc
  change ¬ ((¬ (e2296 _v)) ∨ (¬ (e2468 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v))) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))
  have h2296 : (e2296 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h2468 : (e2468 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have p21918 := n21918 _v _q h51 h2296 h2468 h4306 h4653 h4813
  exact p21918
theorem n21921 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2468 : (e2468 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e6549 _v) := by
  have p21920 := n21920 _v _q 
  have p8438 := n8438 _v _q h2468
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  change (¬ (e2296 _v)) ∨ (¬ (e2468 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) at p21920
  rcases p21920 with hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p8438))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p16729))
theorem n21922 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2468 : (e2468 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e6879 _v) := by
  have p14643 := n14643 _v _q 
  have p21921 := n21921 _v _q h51 h2468 h4306 h4653 h4813
  change (e2296 _v) ∨ (¬ (e6878 _v)) at p14643
  change (¬ (e2296 _v)) at p21921
  rcases p14643 with hlit | hlit
  · exact (False.elim (p21921 hlit))
  · exact hlit
theorem n21923 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2468 : (e2468 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e3152 _v) := by
  have p15776 := n15776 _v _q 
  have p21922 := n21922 _v _q h51 h2468 h4306 h4653 h4813
  change (e6878 _v) ∨ (e3152 _v) at p15776
  change (¬ (e6878 _v)) at p21922
  rcases p15776 with hlit | hlit
  · exact (False.elim (p21922 hlit))
  · exact hlit
theorem n21924 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) (h5138 : (e5138 _v)) : (e4271 _v) := by
  have p14699 := n14699 _v _q 
  have p12951 := n12951 _v _q h2468 h5138
  change (¬ (e2781 _v)) ∨ (¬ (e4270 _v)) at p14699
  rcases p14699 with hlit | hlit
  · exact (False.elim (hlit p12951))
  · exact hlit
theorem n21925 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) (h5138 : (e5138 _v)) : (e4264 _v) := by
  have p14966 := n14966 _v _q 
  have p21924 := n21924 _v _q h2468 h5138
  change (e4270 _v) ∨ (e4264 _v) at p14966
  change (¬ (e4270 _v)) at p21924
  rcases p14966 with hlit | hlit
  · exact (False.elim (p21924 hlit))
  · exact hlit
theorem n21926 (_v : Vars) (_q : Query _v) (h5138 : (e5138 _v)) : (e7814 _v) := by
  have p15221 := n15221 _v _q 
  have p16123 := n16123 _v _q h5138
  change (e7818 _v) ∨ (e7814 _v) at p15221
  change (¬ (e7818 _v)) at p16123
  rcases p15221 with hlit | hlit
  · exact (False.elim (p16123 hlit))
  · exact hlit
theorem n21927 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2468 : (e2468 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5138 : (e5138 _v)) : (e7489 _v) := by
  have p5391 := n5391 _v _q 
  have p21900 := n21900 _v _q h51 h4306 h4653 h4813
  have p8438 := n8438 _v _q h2468
  have p5255 := n5255 _v _q 
  have p13951 := n13951 _v _q 
  have p17136 := n17136 _v _q 
  have p21902 := n21902 _v _q h51 h4306 h4653 h4813
  have p17087 := n17087 _v _q 
  have p17055 := n17055 _v _q 
  have p15073 := n15073 _v _q h2468
  have p17098 := n17098 _v _q 
  have p15104 := n15104 _v _q h2468
  have p21907 := n21907 _v _q h51 h2468 h4306 h4653 h4813
  have p17083 := n17083 _v _q 
  have p16074 := n16074 _v _q h2468
  have p17106 := n17106 _v _q 
  have p17020 := n17020 _v _q 
  have p17093 := n17093 _v _q 
  have p15927 := n15927 _v _q h5138
  have p21921 := n21921 _v _q h51 h2468 h4306 h4653 h4813
  have p16859 := n16859 _v _q h2468
  have p17100 := n17100 _v _q 
  have p16067 := n16067 _v _q h2468
  have p17141 := n17141 _v _q 
  have p17102 := n17102 _v _q 
  have p17091 := n17091 _v _q 
  have p17096 := n17096 _v _q 
  have p21748 := n21748 _v _q h51 h4306 h4653 h4813
  have p21925 := n21925 _v _q h2468 h5138
  have p17758 := n17758 _v _q 
  have p21908 := n21908 _v _q h2468
  have p17124 := n17124 _v _q 
  have p19610 := n19610 _v _q 
  have p17111 := n17111 _v _q 
  have p17115 := n17115 _v _q 
  have p17256 := n17256 _v _q 
  have p17078 := n17078 _v _q 
  have p17113 := n17113 _v _q 
  have p17117 := n17117 _v _q 
  have p20467 := n20467 _v _q 
  have p19665 := n19665 _v _q 
  have p17133 := n17133 _v _q 
  have p17120 := n17120 _v _q 
  have p17104 := n17104 _v _q 
  have p17874 := n17874 _v _q 
  have p17127 := n17127 _v _q 
  have p17089 := n17089 _v _q 
  have p20653 := n20653 _v _q 
  have p21727 := n21727 _v _q h51 h4306 h4653 h4813
  have p17138 := n17138 _v _q h4306
  have p20274 := n20274 _v _q 
  have p17060 := n17060 _v _q h4653
  have p20470 := n20470 _v _q 
  have p17050 := n17050 _v _q 
  have p16778 := n16778 _v _q 
  have p17122 := n17122 _v _q 
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p20829 := n20829 _v _q 
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
  have p21926 := n21926 _v _q h5138
  have p21923 := n21923 _v _q h51 h2468 h4306 h4653 h4813
  exact FloorCertificate.node_21927 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2902 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4808 _v) p5391 p21900 p8438 p5255 p13951 p17136 p21902 p17087 p17055 p15073 p17098 p15104 p21907 p17083 p16074 p17106 p17020 p17093 p15927 p21921 p16859 p17100 p16067 p17141 p17102 p17091 p17096 p21748 p21925 p17758 p21908 p17124 p19610 p17111 p17115 p17256 p17078 p17113 p17117 p20467 p19665 p17133 p17120 p17104 p17874 p17127 p17089 p20653 p21727 p17138 p20274 p17060 p20470 p17050 p16778 p17122 p4983 p16729 p20829 p20426 p20126 p17110 p17053 p20096 p17131 p17108 p17294 p16943 p17058 p17064 p17067 p17080 p17072 p17074 p17069 p20461 p20836 p21926 p21923
theorem n21929 (_v : Vars) (_q : Query _v)  : (e21928 _v) := by
  by_contra hc
  change ¬ ((e79 _v) ∨ (¬ (e2468 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v))) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))
  have h2468 : (e2468 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h5138 : (e5138 _v) := (fun hn => hc (Or.inl hn))
  have p21927 := n21927 _v _q h51 h2468 h4306 h4653 h4813 h5138
  exact p21927
theorem n21930 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2468 : (e2468 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e79 _v) := by
  have p21929 := n21929 _v _q 
  have p8438 := n8438 _v _q h2468
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  change (e79 _v) ∨ (¬ (e2468 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) at p21929
  rcases p21929 with hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p8438))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p16729))
theorem n21931 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2468 : (e2468 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e5135 _v) := by
  have p14729 := n14729 _v _q 
  have p21930 := n21930 _v _q h51 h2468 h4306 h4653 h4813
  change (¬ (e79 _v)) ∨ (¬ (e5134 _v)) at p14729
  rcases p14729 with hlit | hlit
  · exact (False.elim (hlit p21930))
  · exact hlit
theorem n21932 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2468 : (e2468 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e91 _v) := by
  have p16235 := n16235 _v _q 
  have p21931 := n21931 _v _q h51 h2468 h4306 h4653 h4813
  change (e5134 _v) ∨ (e91 _v) at p16235
  change (¬ (e5134 _v)) at p21931
  rcases p16235 with hlit | hlit
  · exact (False.elim (p21931 hlit))
  · exact hlit
theorem n21933 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2468 : (e2468 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e8310 _v) := by
  have p21178 := n21178 _v _q 
  have p21932 := n21932 _v _q h51 h2468 h4306 h4653 h4813
  have p16729 := n16729 _v _q h51
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4983 := n4983 _v _q h4813
  have p8438 := n8438 _v _q h2468
  change (¬ (e2468 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e2529 _v)) at p21178
  rcases p21178 with hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact (False.elim (hlit p8438))
  · exact (False.elim (hlit p21932))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p4983))
  · exact hlit
theorem n21934 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2468 : (e2468 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e7807 _v) := by
  have p11387 := n11387 _v _q 
  have p21933 := n21933 _v _q h51 h2468 h4306 h4653 h4813
  change (¬ (e2303 _v)) ∨ (e2529 _v) at p11387
  change (¬ (e2529 _v)) at p21933
  rcases p11387 with hlit | hlit
  · exact hlit
  · exact (False.elim (p21933 hlit))
theorem n21935 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2468 : (e2468 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e7819 _v) := by
  have p14994 := n14994 _v _q 
  have p21934 := n21934 _v _q h51 h2468 h4306 h4653 h4813
  change (e2303 _v) ∨ (¬ (e7818 _v)) at p14994
  change (¬ (e2303 _v)) at p21934
  rcases p14994 with hlit | hlit
  · exact (False.elim (p21934 hlit))
  · exact hlit
theorem n21936 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2468 : (e2468 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e7814 _v) := by
  have p15221 := n15221 _v _q 
  have p21935 := n21935 _v _q h51 h2468 h4306 h4653 h4813
  change (e7818 _v) ∨ (e7814 _v) at p15221
  change (¬ (e7818 _v)) at p21935
  rcases p15221 with hlit | hlit
  · exact (False.elim (p21935 hlit))
  · exact hlit
theorem n21937 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2468 : (e2468 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e2781 _v) := by
  have p8438 := n8438 _v _q h2468
  have p21934 := n21934 _v _q h51 h2468 h4306 h4653 h4813
  exact FloorCertificate.node_21937 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8438 p21934
theorem n21938 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2468 : (e2468 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e4271 _v) := by
  have p14699 := n14699 _v _q 
  have p21937 := n21937 _v _q h51 h2468 h4306 h4653 h4813
  change (¬ (e2781 _v)) ∨ (¬ (e4270 _v)) at p14699
  rcases p14699 with hlit | hlit
  · exact (False.elim (hlit p21937))
  · exact hlit
theorem n21939 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2468 : (e2468 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e4264 _v) := by
  have p14966 := n14966 _v _q 
  have p21938 := n21938 _v _q h51 h2468 h4306 h4653 h4813
  change (e4270 _v) ∨ (e4264 _v) at p14966
  change (¬ (e4270 _v)) at p21938
  rcases p14966 with hlit | hlit
  · exact (False.elim (p21938 hlit))
  · exact hlit
theorem n21940 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2468 : (e2468 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e7489 _v) := by
  have p21921 := n21921 _v _q h51 h2468 h4306 h4653 h4813
  have p5257 := n5257 _v _q 
  have p8438 := n8438 _v _q h2468
  have p21934 := n21934 _v _q h51 h2468 h4306 h4653 h4813
  have p21930 := n21930 _v _q h51 h2468 h4306 h4653 h4813
  have p21932 := n21932 _v _q h51 h2468 h4306 h4653 h4813
  have p20836 := n20836 _v _q 
  have p20461 := n20461 _v _q 
  have p21923 := n21923 _v _q h51 h2468 h4306 h4653 h4813
  have p21936 := n21936 _v _q h51 h2468 h4306 h4653 h4813
  have p17136 := n17136 _v _q 
  have p21902 := n21902 _v _q h51 h4306 h4653 h4813
  have p17087 := n17087 _v _q 
  have p17055 := n17055 _v _q 
  have p15073 := n15073 _v _q h2468
  have p17098 := n17098 _v _q 
  have p15104 := n15104 _v _q h2468
  have p21907 := n21907 _v _q h51 h2468 h4306 h4653 h4813
  have p17083 := n17083 _v _q 
  have p16074 := n16074 _v _q h2468
  have p17106 := n17106 _v _q 
  have p17020 := n17020 _v _q 
  have p17093 := n17093 _v _q 
  have p16859 := n16859 _v _q h2468
  have p17100 := n17100 _v _q 
  have p16067 := n16067 _v _q h2468
  have p17141 := n17141 _v _q 
  have p17102 := n17102 _v _q 
  have p17091 := n17091 _v _q 
  have p17096 := n17096 _v _q 
  have p21748 := n21748 _v _q h51 h4306 h4653 h4813
  have p21939 := n21939 _v _q h51 h2468 h4306 h4653 h4813
  have p17758 := n17758 _v _q 
  have p21908 := n21908 _v _q h2468
  have p17124 := n17124 _v _q 
  have p19610 := n19610 _v _q 
  have p17111 := n17111 _v _q 
  have p17115 := n17115 _v _q 
  have p17256 := n17256 _v _q 
  have p17078 := n17078 _v _q 
  have p17113 := n17113 _v _q 
  have p17117 := n17117 _v _q 
  have p20467 := n20467 _v _q 
  have p19665 := n19665 _v _q 
  have p17133 := n17133 _v _q 
  have p17120 := n17120 _v _q 
  have p17104 := n17104 _v _q 
  have p17874 := n17874 _v _q 
  have p17127 := n17127 _v _q 
  have p17089 := n17089 _v _q 
  have p20653 := n20653 _v _q 
  have p21727 := n21727 _v _q h51 h4306 h4653 h4813
  have p17138 := n17138 _v _q h4306
  have p20274 := n20274 _v _q 
  have p17060 := n17060 _v _q h4653
  have p20470 := n20470 _v _q 
  have p17050 := n17050 _v _q 
  have p16778 := n16778 _v _q 
  have p17122 := n17122 _v _q 
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p20829 := n20829 _v _q 
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
  have p13951 := n13951 _v _q 
  have p21900 := n21900 _v _q h51 h4306 h4653 h4813
  exact FloorCertificate.node_21940 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2902 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4808 _v) p21921 p5257 p8438 p21934 p21930 p21932 p20836 p20461 p21923 p21936 p17136 p21902 p17087 p17055 p15073 p17098 p15104 p21907 p17083 p16074 p17106 p17020 p17093 p16859 p17100 p16067 p17141 p17102 p17091 p17096 p21748 p21939 p17758 p21908 p17124 p19610 p17111 p17115 p17256 p17078 p17113 p17117 p20467 p19665 p17133 p17120 p17104 p17874 p17127 p17089 p20653 p21727 p17138 p20274 p17060 p20470 p17050 p16778 p17122 p4983 p16729 p20829 p20426 p20126 p17110 p17053 p20096 p17131 p17108 p17294 p16943 p17058 p17064 p17067 p17080 p17072 p17074 p17069 p13951 p21900
theorem n21942 (_v : Vars) (_q : Query _v)  : (e21941 _v) := by
  by_contra hc
  change ¬ ((¬ (e2468 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v))) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr hn)))))
  have h2468 : (e2468 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have p21940 := n21940 _v _q h51 h2468 h4306 h4653 h4813
  exact p21940
theorem n21943 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e6630 _v) := by
  have p21942 := n21942 _v _q 
  have p16729 := n16729 _v _q h51
  have p17060 := n17060 _v _q h4653
  have p4983 := n4983 _v _q h4813
  have p17138 := n17138 _v _q h4306
  change (¬ (e2468 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) at p21942
  rcases p21942 with hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p16729))
theorem n21944 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e6630 _v) := by
  have p21942 := n21942 _v _q 
  have p17138 := n17138 _v _q h4306
  have p16729 := n16729 _v _q h51
  have p4983 := n4983 _v _q h4813
  have p17060 := n17060 _v _q h4653
  change (¬ (e2468 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) at p21942
  rcases p21942 with hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p16729))
theorem n21945 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e8275 _v) := by
  have p14655 := n14655 _v _q 
  have p21943 := n21943 _v _q h51 h4306 h4653 h4813
  change (e2468 _v) ∨ (¬ (e8267 _v)) at p14655
  change (¬ (e2468 _v)) at p21943
  rcases p14655 with hlit | hlit
  · exact (False.elim (p21943 hlit))
  · exact hlit
theorem n21946 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e4787 _v) := by
  have p15670 := n15670 _v _q 
  have p21945 := n21945 _v _q h51 h4306 h4653 h4813
  change (e8267 _v) ∨ (e4787 _v) at p15670
  change (¬ (e8267 _v)) at p21945
  rcases p15670 with hlit | hlit
  · exact (False.elim (p21945 hlit))
  · exact hlit
theorem n21947 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e8275 _v) := by
  have p14655 := n14655 _v _q 
  have p21944 := n21944 _v _q h51 h4306 h4653 h4813
  change (e2468 _v) ∨ (¬ (e8267 _v)) at p14655
  change (¬ (e2468 _v)) at p21944
  rcases p14655 with hlit | hlit
  · exact (False.elim (p21944 hlit))
  · exact hlit
theorem n21948 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e4787 _v) := by
  have p15670 := n15670 _v _q 
  have p21947 := n21947 _v _q h51 h4306 h4653 h4813
  change (e8267 _v) ∨ (e4787 _v) at p15670
  change (¬ (e8267 _v)) at p21947
  rcases p15670 with hlit | hlit
  · exact (False.elim (p21947 hlit))
  · exact hlit
theorem n21949 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2781 : (e2781 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e7807 _v) := by
  have p8581 := n8581 _v _q 
  have p8421 := n8421 _v _q h2781
  have p21944 := n21944 _v _q h51 h4306 h4653 h4813
  change (e2468 _v) ∨ (¬ (e2781 _v)) ∨ (¬ (e2303 _v)) at p8581
  change (¬ (e2468 _v)) at p21944
  rcases p8581 with hlit | hlit | hlit
  · exact (False.elim (p21944 hlit))
  · exact (False.elim (hlit p8421))
  · exact hlit
theorem n21950 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2781 : (e2781 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e7742 _v) := by
  have p11353 := n11353 _v _q 
  have p21949 := n21949 _v _q h51 h2781 h4306 h4653 h4813
  change (¬ (e2132 _v)) ∨ (e2303 _v) at p11353
  change (¬ (e2303 _v)) at p21949
  rcases p11353 with hlit | hlit
  · exact hlit
  · exact (False.elim (p21949 hlit))
theorem n21951 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2781 : (e2781 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e7754 _v) := by
  have p14942 := n14942 _v _q 
  have p21950 := n21950 _v _q h51 h2781 h4306 h4653 h4813
  change (e2132 _v) ∨ (¬ (e7753 _v)) at p14942
  change (¬ (e2132 _v)) at p21950
  rcases p14942 with hlit | hlit
  · exact (False.elim (p21950 hlit))
  · exact hlit
end
end Assembly
