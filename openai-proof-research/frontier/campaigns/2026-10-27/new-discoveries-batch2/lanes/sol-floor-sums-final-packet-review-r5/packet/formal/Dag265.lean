import Dag264
import generated.th_lemma_35
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n22100 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3158 : (e3158 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e7819 _v) := by
  have p14994 := n14994 _v _q 
  have p22099 := n22099 _v _q h51 h3158 h4101 h4306 h4653 h4813
  change (e2303 _v) ∨ (¬ (e7818 _v)) at p14994
  change (¬ (e2303 _v)) at p22099
  rcases p14994 with hlit | hlit
  · exact (False.elim (p22099 hlit))
  · exact hlit
theorem n22101 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3158 : (e3158 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e7814 _v) := by
  have p15221 := n15221 _v _q 
  have p22100 := n22100 _v _q h51 h3158 h4101 h4306 h4653 h4813
  change (e7818 _v) ∨ (e7814 _v) at p15221
  change (¬ (e7818 _v)) at p22100
  rcases p15221 with hlit | hlit
  · exact (False.elim (p22100 hlit))
  · exact hlit
theorem n22102 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3158 : (e3158 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e7742 _v) := by
  have p11353 := n11353 _v _q 
  have p22099 := n22099 _v _q h51 h3158 h4101 h4306 h4653 h4813
  change (¬ (e2132 _v)) ∨ (e2303 _v) at p11353
  change (¬ (e2303 _v)) at p22099
  rcases p11353 with hlit | hlit
  · exact hlit
  · exact (False.elim (p22099 hlit))
theorem n22103 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3158 : (e3158 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e7754 _v) := by
  have p14942 := n14942 _v _q 
  have p22102 := n22102 _v _q h51 h3158 h4101 h4306 h4653 h4813
  change (e2132 _v) ∨ (¬ (e7753 _v)) at p14942
  change (¬ (e2132 _v)) at p22102
  rcases p14942 with hlit | hlit
  · exact (False.elim (p22102 hlit))
  · exact hlit
theorem n22104 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3158 : (e3158 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e4271 _v) := by
  have p14699 := n14699 _v _q 
  have p22098 := n22098 _v _q h51 h3158 h4101 h4306 h4653 h4813
  change (¬ (e2781 _v)) ∨ (¬ (e4270 _v)) at p14699
  rcases p14699 with hlit | hlit
  · exact (False.elim (hlit p22098))
  · exact hlit
theorem n22105 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3158 : (e3158 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e4264 _v) := by
  have p14966 := n14966 _v _q 
  have p22104 := n22104 _v _q h51 h3158 h4101 h4306 h4653 h4813
  change (e4270 _v) ∨ (e4264 _v) at p14966
  change (¬ (e4270 _v)) at p22104
  rcases p14966 with hlit | hlit
  · exact (False.elim (p22104 hlit))
  · exact hlit
theorem n22106 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3158 : (e3158 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e5093 _v) := by
  have p11468 := n11468 _v _q 
  have p22099 := n22099 _v _q h51 h3158 h4101 h4306 h4653 h4813
  change (¬ (e13 _v)) ∨ (e2303 _v) at p11468
  change (¬ (e2303 _v)) at p22099
  rcases p11468 with hlit | hlit
  · exact hlit
  · exact (False.elim (p22099 hlit))
theorem n22107 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3158 : (e3158 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e5105 _v) := by
  have p15204 := n15204 _v _q 
  have p22106 := n22106 _v _q h51 h3158 h4101 h4306 h4653 h4813
  change (e13 _v) ∨ (¬ (e5104 _v)) at p15204
  change (¬ (e13 _v)) at p22106
  rcases p15204 with hlit | hlit
  · exact (False.elim (p22106 hlit))
  · exact hlit
theorem n22108 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3158 : (e3158 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e7749 _v) := by
  have p14941 := n14941 _v _q 
  have p22103 := n22103 _v _q h51 h3158 h4101 h4306 h4653 h4813
  change (e7753 _v) ∨ (e7749 _v) at p14941
  change (¬ (e7753 _v)) at p22103
  rcases p14941 with hlit | hlit
  · exact (False.elim (p22103 hlit))
  · exact hlit
theorem n22109 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3158 : (e3158 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e5100 _v) := by
  have p15319 := n15319 _v _q 
  have p22107 := n22107 _v _q h51 h3158 h4101 h4306 h4653 h4813
  change (e5104 _v) ∨ (e5100 _v) at p15319
  change (¬ (e5104 _v)) at p22107
  rcases p15319 with hlit | hlit
  · exact (False.elim (p22107 hlit))
  · exact hlit
theorem n22110 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3158 : (e3158 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5145 : (e5145 _v)) (h6525 : (e6525 _v)) (h6600 : (e6600 _v)) : (e7489 _v) := by
  have p16578 := n16578 _v _q 
  have p16858 := n16858 _v _q 
  have p21899 := n21899 _v _q h51 h4306 h4653 h4813
  have p16885 := n16885 _v _q h3158
  have p15907 := n15907 _v _q h6600
  have p17147 := n17147 _v _q 
  have p17245 := n17245 _v _q h5145
  have p20126 := n20126 _v _q 
  have p20426 := n20426 _v _q 
  have p17110 := n17110 _v _q 
  have p20829 := n20829 _v _q 
  have p17009 := n17009 _v _q 
  have p5255 := n5255 _v _q 
  have p22101 := n22101 _v _q h51 h3158 h4101 h4306 h4653 h4813
  have p22108 := n22108 _v _q h51 h3158 h4101 h4306 h4653 h4813
  have p21615 := n21615 _v _q h51 h4306 h4653 h4813 h6525
  have p22105 := n22105 _v _q h51 h3158 h4101 h4306 h4653 h4813
  have p22039 := n22039 _v _q h51 h3158 h4101 h4306 h4653 h4813
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
  have p5257 := n5257 _v _q 
  have p17069 := n17069 _v _q 
  have p20096 := n20096 _v _q 
  have p17065 := n17065 _v _q h4101
  have p20836 := n20836 _v _q 
  have p20461 := n20461 _v _q 
  have p21948 := n21948 _v _q h51 h4306 h4653 h4813
  have p17256 := n17256 _v _q 
  have p17136 := n17136 _v _q 
  have p21906 := n21906 _v _q h51 h4306 h4653 h4813
  have p17087 := n17087 _v _q 
  have p17055 := n17055 _v _q 
  have p17058 := n17058 _v _q 
  have p17098 := n17098 _v _q 
  have p17083 := n17083 _v _q 
  have p17106 := n17106 _v _q 
  have p17020 := n17020 _v _q 
  have p17093 := n17093 _v _q 
  have p21984 := n21984 _v _q h51 h4306 h4653 h4813
  have p17100 := n17100 _v _q 
  have p17141 := n17141 _v _q 
  have p17102 := n17102 _v _q 
  have p17091 := n17091 _v _q 
  have p17096 := n17096 _v _q 
  have p21989 := n21989 _v _q h51 h4306 h4653 h4813
  have p17758 := n17758 _v _q 
  have p17124 := n17124 _v _q 
  have p19610 := n19610 _v _q 
  have p17111 := n17111 _v _q 
  have p17115 := n17115 _v _q 
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
  have p22109 := n22109 _v _q h51 h3158 h4101 h4306 h4653 h4813
  have p17138 := n17138 _v _q h4306
  have p20274 := n20274 _v _q 
  have p17060 := n17060 _v _q h4653
  have p20470 := n20470 _v _q 
  have p17050 := n17050 _v _q 
  have p16778 := n16778 _v _q 
  have p17122 := n17122 _v _q 
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p8463 := n8463 _v _q h6525
  have p13951 := n13951 _v _q 
  have p16058 := n16058 _v _q h6525
  have p21728 := n21728 _v _q h51 h4306 h4653 h4813
  have p8439 := n8439 _v _q h6600
  exact FloorCertificate.node_22110 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2863 _v) (e2877 _v) (e2883 _v) (e2902 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p16578 p16858 p21899 p16885 p15907 p17147 p17245 p20126 p20426 p17110 p20829 p17009 p5255 p22101 p22108 p21615 p22105 p22039 p17131 p17108 p17294 p16943 p17064 p17067 p17080 p17053 p17072 p17074 p5257 p17069 p20096 p17065 p20836 p20461 p21948 p17256 p17136 p21906 p17087 p17055 p17058 p17098 p17083 p17106 p17020 p17093 p21984 p17100 p17141 p17102 p17091 p17096 p21989 p17758 p17124 p19610 p17111 p17115 p17078 p17113 p17117 p20467 p19665 p17133 p17120 p17104 p17874 p17127 p17089 p20653 p22109 p17138 p20274 p17060 p20470 p17050 p16778 p17122 p4983 p16729 p8463 p13951 p16058 p21728 p8439
theorem n22111 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3158 : (e3158 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e4459 _v) := by
  have p16784 := n16784 _v _q 
  have p22108 := n22108 _v _q h51 h3158 h4101 h4306 h4653 h4813
  change (e4459 _v) ∨ (¬ (e7749 _v)) at p16784
  rcases p16784 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p22108))
theorem n22113 (_v : Vars) (_q : Query _v)  : (e22112 _v) := by
  by_contra hc
  change ¬ ((e2402 _v) ∨ (¬ (e3158 _v)) ∨ (¬ (e5145 _v)) ∨ (¬ (e4101 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (e2242 _v)) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h3158 : (e3158 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h4101 : (e4101 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h5145 : (e5145 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h6525 : (e6525 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn)))))))))
  have h6600 : (e6600 _v) := (fun hn => hc (Or.inl hn))
  have p22110 := n22110 _v _q h51 h3158 h4101 h4306 h4653 h4813 h5145 h6525 h6600
  exact p22110
theorem n22114 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3158 : (e3158 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5145 : (e5145 _v)) (h6525 : (e6525 _v)) : (e2402 _v) := by
  have p22113 := n22113 _v _q 
  have p17245 := n17245 _v _q h5145
  have p16885 := n16885 _v _q h3158
  have p17065 := n17065 _v _q h4101
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p8463 := n8463 _v _q h6525
  change (e2402 _v) ∨ (¬ (e3158 _v)) ∨ (¬ (e5145 _v)) ∨ (¬ (e4101 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (e2242 _v) at p22113
  change (¬ (e2242 _v)) at p8463
  rcases p22113 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p16885))
  · exact (False.elim (hlit p17245))
  · exact (False.elim (hlit p17065))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (p8463 hlit))
theorem n22115 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3158 : (e3158 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5145 : (e5145 _v)) (h6525 : (e6525 _v)) : (e3929 _v) := by
  have p14484 := n14484 _v _q 
  have p22114 := n22114 _v _q h51 h3158 h4101 h4306 h4653 h4813 h5145 h6525
  change (¬ (e2402 _v)) ∨ (¬ (e3923 _v)) at p14484
  rcases p14484 with hlit | hlit
  · exact (False.elim (hlit p22114))
  · exact hlit
theorem n22116 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3158 : (e3158 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5145 : (e5145 _v)) (h6525 : (e6525 _v)) : (e3919 _v) := by
  have p14797 := n14797 _v _q 
  have p22115 := n22115 _v _q h51 h3158 h4101 h4306 h4653 h4813 h5145 h6525
  change (e3923 _v) ∨ (e3919 _v) at p14797
  change (¬ (e3923 _v)) at p22115
  rcases p14797 with hlit | hlit
  · exact (False.elim (p22115 hlit))
  · exact hlit
theorem n22117 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3158 : (e3158 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e4679 _v) := by
  have p16058 := n16058 _v _q h6525
  have p22109 := n22109 _v _q h51 h3158 h4101 h4306 h4653 h4813
  have p8463 := n8463 _v _q h6525
  exact FloorCertificate.node_22117 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e2941 _v) p16058 p22109 p8463
theorem n22118 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3158 : (e3158 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e3133 _v) := by
  have p22039 := n22039 _v _q h51 h3158 h4101 h4306 h4653 h4813
  have p5257 := n5257 _v _q 
  have p8463 := n8463 _v _q h6525
  have p22101 := n22101 _v _q h51 h3158 h4101 h4306 h4653 h4813
  exact FloorCertificate.node_22118 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e110 _v) (e2945 _v) (e3141 _v) p22039 p5257 p8463 p22101
theorem n22119 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3158 : (e3158 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5145 : (e5145 _v)) (h6525 : (e6525 _v)) : (e2358 _v) := by
  have p21986 := n21986 _v _q 
  have p22116 := n22116 _v _q h51 h3158 h4101 h4306 h4653 h4813 h5145 h6525
  have p22117 := n22117 _v _q h51 h3158 h4101 h4306 h4653 h4813 h6525
  have p22111 := n22111 _v _q h51 h3158 h4101 h4306 h4653 h4813
  have p22118 := n22118 _v _q h51 h3158 h4101 h4306 h4653 h4813 h6525
  have p17245 := n17245 _v _q h5145
  have p22105 := n22105 _v _q h51 h3158 h4101 h4306 h4653 h4813
  have p17065 := n17065 _v _q h4101
  have p16885 := n16885 _v _q h3158
  have p21615 := n21615 _v _q h51 h4306 h4653 h4813 h6525
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  change (e2358 _v) ∨ (¬ (e4459 _v)) ∨ (¬ (e3919 _v)) ∨ (¬ (e3133 _v)) ∨ (¬ (e5145 _v)) ∨ (¬ (e4679 _v)) ∨ (¬ (e4264 _v)) ∨ (¬ (e4101 _v)) ∨ (¬ (e3158 _v)) ∨ (¬ (e8045 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) at p21986
  rcases p21986 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p22111))
  · exact (False.elim (hlit p22116))
  · exact (False.elim (hlit p22118))
  · exact (False.elim (hlit p17245))
  · exact (False.elim (hlit p22117))
  · exact (False.elim (hlit p22105))
  · exact (False.elim (hlit p17065))
  · exact (False.elim (hlit p16885))
  · exact (False.elim (hlit p21615))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p16729))
theorem n22120 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3158 : (e3158 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5145 : (e5145 _v)) (h6525 : (e6525 _v)) : (e7489 _v) := by
  have p16885 := n16885 _v _q h3158
  have p13951 := n13951 _v _q 
  have p16058 := n16058 _v _q h6525
  have p5391 := n5391 _v _q 
  have p22116 := n22116 _v _q h51 h3158 h4101 h4306 h4653 h4813 h5145 h6525
  have p21728 := n21728 _v _q h51 h4306 h4653 h4813
  have p22119 := n22119 _v _q h51 h3158 h4101 h4306 h4653 h4813 h5145 h6525
  have p17245 := n17245 _v _q h5145
  have p20126 := n20126 _v _q 
  have p20426 := n20426 _v _q 
  have p17110 := n17110 _v _q 
  have p20829 := n20829 _v _q 
  have p17009 := n17009 _v _q 
  have p5255 := n5255 _v _q 
  have p22101 := n22101 _v _q h51 h3158 h4101 h4306 h4653 h4813
  have p22108 := n22108 _v _q h51 h3158 h4101 h4306 h4653 h4813
  have p21615 := n21615 _v _q h51 h4306 h4653 h4813 h6525
  have p22105 := n22105 _v _q h51 h3158 h4101 h4306 h4653 h4813
  have p22039 := n22039 _v _q h51 h3158 h4101 h4306 h4653 h4813
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
  have p5257 := n5257 _v _q 
  have p17069 := n17069 _v _q 
  have p20096 := n20096 _v _q 
  have p17065 := n17065 _v _q h4101
  have p20836 := n20836 _v _q 
  have p20461 := n20461 _v _q 
  have p21948 := n21948 _v _q h51 h4306 h4653 h4813
  have p17256 := n17256 _v _q 
  have p17136 := n17136 _v _q 
  have p21906 := n21906 _v _q h51 h4306 h4653 h4813
  have p17087 := n17087 _v _q 
  have p17055 := n17055 _v _q 
  have p17058 := n17058 _v _q 
  have p17098 := n17098 _v _q 
  have p17083 := n17083 _v _q 
  have p17106 := n17106 _v _q 
  have p17020 := n17020 _v _q 
  have p17093 := n17093 _v _q 
  have p21984 := n21984 _v _q h51 h4306 h4653 h4813
  have p17100 := n17100 _v _q 
  have p17141 := n17141 _v _q 
  have p17102 := n17102 _v _q 
  have p17091 := n17091 _v _q 
  have p17096 := n17096 _v _q 
  have p21989 := n21989 _v _q h51 h4306 h4653 h4813
  have p17758 := n17758 _v _q 
  have p17124 := n17124 _v _q 
  have p19610 := n19610 _v _q 
  have p17111 := n17111 _v _q 
  have p17115 := n17115 _v _q 
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
  have p22109 := n22109 _v _q h51 h3158 h4101 h4306 h4653 h4813
  have p17138 := n17138 _v _q h4306
  have p20274 := n20274 _v _q 
  have p17060 := n17060 _v _q h4653
  have p20470 := n20470 _v _q 
  have p17050 := n17050 _v _q 
  have p16778 := n16778 _v _q 
  have p17122 := n17122 _v _q 
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p8463 := n8463 _v _q h6525
  exact FloorCertificate.node_22120 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2902 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p16885 p13951 p16058 p5391 p22116 p21728 p22119 p17245 p20126 p20426 p17110 p20829 p17009 p5255 p22101 p22108 p21615 p22105 p22039 p17131 p17108 p17294 p16943 p17064 p17067 p17080 p17053 p17072 p17074 p5257 p17069 p20096 p17065 p20836 p20461 p21948 p17256 p17136 p21906 p17087 p17055 p17058 p17098 p17083 p17106 p17020 p17093 p21984 p17100 p17141 p17102 p17091 p17096 p21989 p17758 p17124 p19610 p17111 p17115 p17078 p17113 p17117 p20467 p19665 p17133 p17120 p17104 p17874 p17127 p17089 p20653 p22109 p17138 p20274 p17060 p20470 p17050 p16778 p17122 p4983 p16729 p8463
theorem n22122 (_v : Vars) (_q : Query _v)  : (e22121 _v) := by
  by_contra hc
  change ¬ ((¬ (e5145 _v)) ∨ (¬ (e3158 _v)) ∨ (¬ (e4101 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (e2242 _v)) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h3158 : (e3158 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h4101 : (e4101 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h5145 : (e5145 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h6525 : (e6525 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))))
  have p22120 := n22120 _v _q h51 h3158 h4101 h4306 h4653 h4813 h5145 h6525
  exact p22120
theorem n22123 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3158 : (e3158 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e5148 _v) := by
  have p22122 := n22122 _v _q 
  have p8463 := n8463 _v _q h6525
  have p17065 := n17065 _v _q h4101
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p16885 := n16885 _v _q h3158
  change (¬ (e5145 _v)) ∨ (¬ (e3158 _v)) ∨ (¬ (e4101 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (e2242 _v) at p22122
  change (¬ (e2242 _v)) at p8463
  rcases p22122 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p16885))
  · exact (False.elim (hlit p17065))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (p8463 hlit))
theorem n22124 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3158 : (e3158 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e5149 _v) := by
  have p15925 := n15925 _v _q 
  have p22123 := n22123 _v _q h51 h3158 h4101 h4306 h4653 h4813 h6525
  change (e5149 _v) ∨ (e5145 _v) at p15925
  change (¬ (e5145 _v)) at p22123
  rcases p15925 with hlit | hlit
  · exact hlit
  · exact (False.elim (p22123 hlit))
theorem n22125 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3158 : (e3158 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e79 _v) := by
  have p15115 := n15115 _v _q 
  have p22124 := n22124 _v _q h51 h3158 h4101 h4306 h4653 h4813 h6525
  change (e79 _v) ∨ (¬ (e5149 _v)) at p15115
  rcases p15115 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p22124))
theorem n22126 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3158 : (e3158 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e5135 _v) := by
  have p14729 := n14729 _v _q 
  have p22125 := n22125 _v _q h51 h3158 h4101 h4306 h4653 h4813 h6525
  change (¬ (e79 _v)) ∨ (¬ (e5134 _v)) at p14729
  rcases p14729 with hlit | hlit
  · exact (False.elim (hlit p22125))
  · exact hlit
theorem n22127 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3158 : (e3158 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e91 _v) := by
  have p16235 := n16235 _v _q 
  have p22126 := n22126 _v _q h51 h3158 h4101 h4306 h4653 h4813 h6525
  change (e5134 _v) ∨ (e91 _v) at p16235
  change (¬ (e5134 _v)) at p22126
  rcases p16235 with hlit | hlit
  · exact (False.elim (p22126 hlit))
  · exact hlit
theorem n22128 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3158 : (e3158 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e3942 _v) := by
  have p20869 := n20869 _v _q 
  have p22127 := n22127 _v _q h51 h3158 h4101 h4306 h4653 h4813 h6525
  have p21728 := n21728 _v _q h51 h4306 h4653 h4813
  have p21899 := n21899 _v _q h51 h4306 h4653 h4813
  have p21948 := n21948 _v _q h51 h4306 h4653 h4813
  have p16885 := n16885 _v _q h3158
  have p22039 := n22039 _v _q h51 h3158 h4101 h4306 h4653 h4813
  have p22105 := n22105 _v _q h51 h3158 h4101 h4306 h4653 h4813
  have p22111 := n22111 _v _q h51 h3158 h4101 h4306 h4653 h4813
  have p21989 := n21989 _v _q h51 h4306 h4653 h4813
  have p22101 := n22101 _v _q h51 h3158 h4101 h4306 h4653 h4813
  have p21984 := n21984 _v _q h51 h4306 h4653 h4813
  have p17060 := n17060 _v _q h4653
  have p17138 := n17138 _v _q h4306
  have p22109 := n22109 _v _q h51 h3158 h4101 h4306 h4653 h4813
  have p16729 := n16729 _v _q h51
  have p16058 := n16058 _v _q h6525
  have p21600 := n21600 _v _q h51 h4306 h4653 h4813 h6525
  have p21615 := n21615 _v _q h51 h4306 h4653 h4813 h6525
  have p17065 := n17065 _v _q h4101
  have p4983 := n4983 _v _q h4813
  change (¬ (e8317 _v)) ∨ (¬ (e196 _v)) ∨ (¬ (e4787 _v)) ∨ (e2475 _v) ∨ (¬ (e4459 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e5100 _v)) ∨ (¬ (e7814 _v)) ∨ (¬ (e8045 _v)) ∨ (¬ (e3158 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e4567 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4439 _v)) ∨ (¬ (e4264 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4101 _v)) ∨ (¬ (e4813 _v)) at p20869
  change (¬ (e2475 _v)) at p21600
  rcases p20869 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact (False.elim (hlit p21728))
  · exact (False.elim (hlit p21899))
  · exact (False.elim (hlit p21948))
  · exact (False.elim (p21600 hlit))
  · exact (False.elim (hlit p22111))
  · exact hlit
  · exact (False.elim (hlit p16058))
  · exact (False.elim (hlit p22109))
  · exact (False.elim (hlit p22101))
  · exact (False.elim (hlit p21615))
  · exact (False.elim (hlit p16885))
  · exact (False.elim (hlit p22127))
  · exact (False.elim (hlit p21989))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p21984))
  · exact (False.elim (hlit p22105))
  · exact (False.elim (hlit p22039))
  · exact (False.elim (hlit p17065))
  · exact (False.elim (hlit p4983))
theorem n22129 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3158 : (e3158 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e7415 _v) := by
  have p15012 := n15012 _v _q 
  have p22128 := n22128 _v _q h51 h3158 h4101 h4306 h4653 h4813 h6525
  change (e7415 _v) ∨ (e3937 _v) at p15012
  change (¬ (e3937 _v)) at p22128
  rcases p15012 with hlit | hlit
  · exact hlit
  · exact (False.elim (p22128 hlit))
theorem n22130 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3158 : (e3158 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e2402 _v) := by
  have p14534 := n14534 _v _q 
  have p22129 := n22129 _v _q h51 h3158 h4101 h4306 h4653 h4813 h6525
  change (e2402 _v) ∨ (¬ (e7415 _v)) at p14534
  rcases p14534 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p22129))
theorem n22131 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3158 : (e3158 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e3929 _v) := by
  have p14484 := n14484 _v _q 
  have p22130 := n22130 _v _q h51 h3158 h4101 h4306 h4653 h4813 h6525
  change (¬ (e2402 _v)) ∨ (¬ (e3923 _v)) at p14484
  rcases p14484 with hlit | hlit
  · exact (False.elim (hlit p22130))
  · exact hlit
theorem n22132 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3158 : (e3158 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e3919 _v) := by
  have p14797 := n14797 _v _q 
  have p22131 := n22131 _v _q h51 h3158 h4101 h4306 h4653 h4813 h6525
  change (e3923 _v) ∨ (e3919 _v) at p14797
  change (¬ (e3923 _v)) at p22131
  rcases p14797 with hlit | hlit
  · exact (False.elim (p22131 hlit))
  · exact hlit
theorem n22133 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3158 : (e3158 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e7489 _v) := by
  have p8463 := n8463 _v _q h6525
  have p13951 := n13951 _v _q 
  have p22127 := n22127 _v _q h51 h3158 h4101 h4306 h4653 h4813 h6525
  have p16058 := n16058 _v _q h6525
  have p5391 := n5391 _v _q 
  have p22132 := n22132 _v _q h51 h3158 h4101 h4306 h4653 h4813 h6525
  have p21728 := n21728 _v _q h51 h4306 h4653 h4813
  have p16858 := n16858 _v _q 
  have p16885 := n16885 _v _q h3158
  have p16578 := n16578 _v _q 
  have p20126 := n20126 _v _q 
  have p20426 := n20426 _v _q 
  have p17110 := n17110 _v _q 
  have p20829 := n20829 _v _q 
  have p17009 := n17009 _v _q 
  have p22101 := n22101 _v _q h51 h3158 h4101 h4306 h4653 h4813
  have p22108 := n22108 _v _q h51 h3158 h4101 h4306 h4653 h4813
  have p21615 := n21615 _v _q h51 h4306 h4653 h4813 h6525
  have p22105 := n22105 _v _q h51 h3158 h4101 h4306 h4653 h4813
  have p22039 := n22039 _v _q h51 h3158 h4101 h4306 h4653 h4813
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
  have p5257 := n5257 _v _q 
  have p17069 := n17069 _v _q 
  have p20096 := n20096 _v _q 
  have p17065 := n17065 _v _q h4101
  have p20836 := n20836 _v _q 
  have p20461 := n20461 _v _q 
  have p21948 := n21948 _v _q h51 h4306 h4653 h4813
  have p17256 := n17256 _v _q 
  have p17136 := n17136 _v _q 
  have p21906 := n21906 _v _q h51 h4306 h4653 h4813
  have p17087 := n17087 _v _q 
  have p17055 := n17055 _v _q 
  have p17058 := n17058 _v _q 
  have p17098 := n17098 _v _q 
  have p17083 := n17083 _v _q 
  have p17106 := n17106 _v _q 
  have p17020 := n17020 _v _q 
  have p17093 := n17093 _v _q 
  have p21984 := n21984 _v _q h51 h4306 h4653 h4813
  have p17100 := n17100 _v _q 
  have p17141 := n17141 _v _q 
  have p17102 := n17102 _v _q 
  have p17091 := n17091 _v _q 
  have p17096 := n17096 _v _q 
  have p21989 := n21989 _v _q h51 h4306 h4653 h4813
  have p17758 := n17758 _v _q 
  have p17124 := n17124 _v _q 
  have p19610 := n19610 _v _q 
  have p17111 := n17111 _v _q 
  have p17115 := n17115 _v _q 
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
  have p22109 := n22109 _v _q h51 h3158 h4101 h4306 h4653 h4813
  have p17138 := n17138 _v _q h4306
  have p20274 := n20274 _v _q 
  have p17060 := n17060 _v _q h4653
  have p20470 := n20470 _v _q 
  have p17050 := n17050 _v _q 
  have p16778 := n16778 _v _q 
  have p17122 := n17122 _v _q 
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  exact FloorCertificate.node_22133 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2863 _v) (e2877 _v) (e2902 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p8463 p13951 p22127 p16058 p5391 p22132 p21728 p16858 p16885 p16578 p20126 p20426 p17110 p20829 p17009 p22101 p22108 p21615 p22105 p22039 p17131 p17108 p17294 p16943 p17064 p17067 p17080 p17053 p17072 p17074 p5257 p17069 p20096 p17065 p20836 p20461 p21948 p17256 p17136 p21906 p17087 p17055 p17058 p17098 p17083 p17106 p17020 p17093 p21984 p17100 p17141 p17102 p17091 p17096 p21989 p17758 p17124 p19610 p17111 p17115 p17078 p17113 p17117 p20467 p19665 p17133 p17120 p17104 p17874 p17127 p17089 p20653 p22109 p17138 p20274 p17060 p20470 p17050 p16778 p17122 p4983 p16729
theorem n22135 (_v : Vars) (_q : Query _v)  : (e22134 _v) := by
  by_contra hc
  change ¬ ((e2242 _v) ∨ (¬ (e3158 _v)) ∨ (¬ (e4101 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v))) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn)))))))
  have h3158 : (e3158 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h4101 : (e4101 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h6525 : (e6525 _v) := (fun hn => hc (Or.inl hn))
  have p22133 := n22133 _v _q h51 h3158 h4101 h4306 h4653 h4813 h6525
  exact p22133
theorem n22136 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3158 : (e3158 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e2242 _v) := by
  have p22135 := n22135 _v _q 
  have p16885 := n16885 _v _q h3158
  have p17065 := n17065 _v _q h4101
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  change (e2242 _v) ∨ (¬ (e3158 _v)) ∨ (¬ (e4101 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) at p22135
  rcases p22135 with hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p16885))
  · exact (False.elim (hlit p17065))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p16729))
theorem n22137 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3158 : (e3158 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e4686 _v) := by
  have p14708 := n14708 _v _q 
  have p22136 := n22136 _v _q h51 h3158 h4101 h4306 h4653 h4813
  change (¬ (e2242 _v)) ∨ (¬ (e4685 _v)) at p14708
  rcases p14708 with hlit | hlit
  · exact (False.elim (hlit p22136))
  · exact hlit
theorem n22138 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3158 : (e3158 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e4679 _v) := by
  have p14989 := n14989 _v _q 
  have p22137 := n22137 _v _q h51 h3158 h4101 h4306 h4653 h4813
  change (e4685 _v) ∨ (e4679 _v) at p14989
  change (¬ (e4685 _v)) at p22137
  rcases p14989 with hlit | hlit
  · exact (False.elim (p22137 hlit))
  · exact hlit
theorem n22139 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3158 : (e3158 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e5098 _v) := by
  have p16684 := n16684 _v _q 
  have p22107 := n22107 _v _q h51 h3158 h4101 h4306 h4653 h4813
  change (e5104 _v) ∨ (e5098 _v) at p16684
  change (¬ (e5104 _v)) at p22107
  rcases p16684 with hlit | hlit
  · exact (False.elim (p22107 hlit))
  · exact hlit
theorem n22140 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3158 : (e3158 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e4675 _v) := by
  have p22138 := n22138 _v _q h51 h3158 h4101 h4306 h4653 h4813
  have p22139 := n22139 _v _q h51 h3158 h4101 h4306 h4653 h4813
  have p22136 := n22136 _v _q h51 h3158 h4101 h4306 h4653 h4813
  exact FloorCertificate.node_22140 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e2941 _v) p22138 p22139 p22136
theorem n22141 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3158 : (e3158 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e8038 _v) := by
  have p21996 := n21996 _v _q 
  have p22037 := n22037 _v _q h51 h3158 h4101 h4306 h4653 h4813
  have p17060 := n17060 _v _q h4653
  have p17138 := n17138 _v _q h4306
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p22098 := n22098 _v _q h51 h3158 h4101 h4306 h4653 h4813
  have p16885 := n16885 _v _q h3158
  have p22138 := n22138 _v _q h51 h3158 h4101 h4306 h4653 h4813
  change (¬ (e2475 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (e2296 _v) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e2781 _v)) ∨ (¬ (e3158 _v)) ∨ (¬ (e4679 _v)) at p21996
  change (¬ (e2296 _v)) at p22037
  rcases p21996 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (p22037 hlit))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p22098))
  · exact (False.elim (hlit p16885))
  · exact (False.elim (hlit p22138))
theorem n22142 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3158 : (e3158 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e8050 _v) := by
  have p15207 := n15207 _v _q 
  have p22141 := n22141 _v _q h51 h3158 h4101 h4306 h4653 h4813
  change (e2475 _v) ∨ (¬ (e8049 _v)) at p15207
  change (¬ (e2475 _v)) at p22141
  rcases p15207 with hlit | hlit
  · exact (False.elim (p22141 hlit))
  · exact hlit
theorem n22143 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3158 : (e3158 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e8045 _v) := by
  have p15206 := n15206 _v _q 
  have p22142 := n22142 _v _q h51 h3158 h4101 h4306 h4653 h4813
  change (e8049 _v) ∨ (e8045 _v) at p15206
  change (¬ (e8049 _v)) at p22142
  rcases p15206 with hlit | hlit
  · exact (False.elim (p22142 hlit))
  · exact hlit
theorem n22144 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3158 : (e3158 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6600 : (e6600 _v)) : (e95 _v) := by
  have p20869 := n20869 _v _q 
  have p15907 := n15907 _v _q h6600
  have p21728 := n21728 _v _q h51 h4306 h4653 h4813
  have p21899 := n21899 _v _q h51 h4306 h4653 h4813
  have p21948 := n21948 _v _q h51 h4306 h4653 h4813
  have p16885 := n16885 _v _q h3158
  have p22039 := n22039 _v _q h51 h3158 h4101 h4306 h4653 h4813
  have p22105 := n22105 _v _q h51 h3158 h4101 h4306 h4653 h4813
  have p22111 := n22111 _v _q h51 h3158 h4101 h4306 h4653 h4813
  have p21989 := n21989 _v _q h51 h4306 h4653 h4813
  have p22101 := n22101 _v _q h51 h3158 h4101 h4306 h4653 h4813
  have p21984 := n21984 _v _q h51 h4306 h4653 h4813
  have p17060 := n17060 _v _q h4653
  have p17138 := n17138 _v _q h4306
  have p22109 := n22109 _v _q h51 h3158 h4101 h4306 h4653 h4813
  have p16729 := n16729 _v _q h51
  have p22140 := n22140 _v _q h51 h3158 h4101 h4306 h4653 h4813
  have p22141 := n22141 _v _q h51 h3158 h4101 h4306 h4653 h4813
  have p22143 := n22143 _v _q h51 h3158 h4101 h4306 h4653 h4813
  have p17065 := n17065 _v _q h4101
  have p4983 := n4983 _v _q h4813
  change (¬ (e8317 _v)) ∨ (¬ (e196 _v)) ∨ (¬ (e4787 _v)) ∨ (e2475 _v) ∨ (¬ (e4459 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e5100 _v)) ∨ (¬ (e7814 _v)) ∨ (¬ (e8045 _v)) ∨ (¬ (e3158 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e4567 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4439 _v)) ∨ (¬ (e4264 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4101 _v)) ∨ (¬ (e4813 _v)) at p20869
  change (¬ (e2475 _v)) at p22141
  rcases p20869 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact (False.elim (hlit p21728))
  · exact (False.elim (hlit p21899))
  · exact (False.elim (hlit p21948))
  · exact (False.elim (p22141 hlit))
  · exact (False.elim (hlit p22111))
  · exact (False.elim (hlit p15907))
  · exact (False.elim (hlit p22140))
  · exact (False.elim (hlit p22109))
  · exact (False.elim (hlit p22101))
  · exact (False.elim (hlit p22143))
  · exact (False.elim (hlit p16885))
  · exact hlit
  · exact (False.elim (hlit p21989))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p21984))
  · exact (False.elim (hlit p22105))
  · exact (False.elim (hlit p22039))
  · exact (False.elim (hlit p17065))
  · exact (False.elim (hlit p4983))
theorem n22145 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3158 : (e3158 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6600 : (e6600 _v)) : (e5134 _v) := by
  have p16235 := n16235 _v _q 
  have p22144 := n22144 _v _q h51 h3158 h4101 h4306 h4653 h4813 h6600
  change (e5134 _v) ∨ (e91 _v) at p16235
  change (¬ (e91 _v)) at p22144
  rcases p16235 with hlit | hlit
  · exact hlit
  · exact (False.elim (p22144 hlit))
theorem n22146 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3158 : (e3158 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6600 : (e6600 _v)) : (e5138 _v) := by
  have p14729 := n14729 _v _q 
  have p22145 := n22145 _v _q h51 h3158 h4101 h4306 h4653 h4813 h6600
  change (¬ (e79 _v)) ∨ (¬ (e5134 _v)) at p14729
  rcases p14729 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p22145))
theorem n22147 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3158 : (e3158 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6600 : (e6600 _v)) : (e5150 _v) := by
  have p15115 := n15115 _v _q 
  have p22146 := n22146 _v _q h51 h3158 h4101 h4306 h4653 h4813 h6600
  change (e79 _v) ∨ (¬ (e5149 _v)) at p15115
  change (¬ (e79 _v)) at p22146
  rcases p15115 with hlit | hlit
  · exact (False.elim (p22146 hlit))
  · exact hlit
end
end Assembly
