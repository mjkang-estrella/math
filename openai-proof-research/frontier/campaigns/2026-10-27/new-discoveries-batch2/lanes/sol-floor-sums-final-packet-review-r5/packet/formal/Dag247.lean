import Dag246
import generated.th_lemma_32
import generated.th_lemma_33
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n21210 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e4447 _v) := by
  have p14688 := n14688 _v _q 
  have p21209 := n21209 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  change (¬ (e2061 _v)) ∨ (¬ (e4446 _v)) at p14688
  rcases p14688 with hlit | hlit
  · exact (False.elim (hlit p21209))
  · exact hlit
theorem n21211 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h3152 : (e3152 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) : (e4447 _v) := by
  have p14688 := n14688 _v _q 
  have p21204 := n21204 _v _q h51 h91 h191 h3152 h4260 h4306 h4653 h4675 h4787 h4813 h4838
  change (¬ (e2061 _v)) ∨ (¬ (e4446 _v)) at p14688
  rcases p14688 with hlit | hlit
  · exact (False.elim (hlit p21204))
  · exact hlit
theorem n21212 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h3152 : (e3152 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) : (e4439 _v) := by
  have p14925 := n14925 _v _q 
  have p21211 := n21211 _v _q h51 h91 h191 h3152 h4260 h4306 h4653 h4675 h4787 h4813 h4838
  change (e4446 _v) ∨ (e4439 _v) at p14925
  change (¬ (e4446 _v)) at p21211
  rcases p14925 with hlit | hlit
  · exact (False.elim (p21211 hlit))
  · exact hlit
theorem n21213 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2132 : (e2132 _v)) (h3152 : (e3152 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) : (e2179 _v) := by
  have p20854 := n20854 _v _q 
  have p11349 := n11349 _v _q h2132
  have p5006 := n5006 _v _q h4675
  have p4998 := n4998 _v _q h3152
  have p253 := n253 _v _q h191
  have p4999 := n4999 _v _q h91
  have p4989 := n4989 _v _q h4838
  have p4983 := n4983 _v _q h4813
  have p5008 := n5008 _v _q h4787
  have p4981 := n4981 _v _q h4260
  have p21204 := n21204 _v _q h51 h91 h191 h3152 h4260 h4306 h4653 h4675 h4787 h4813 h4838
  change (e2179 _v) ∨ (¬ (e2061 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e2132 _v)) at p20854
  rcases p20854 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p21204))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p253))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p4989))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p4981))
  · exact (False.elim (hlit p11349))
theorem n21214 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2179 : (e2179 _v)) (h3152 : (e3152 _v)) (h4139 : (e4139 _v)) (h4220 : (e4220 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4306 : (e4306 _v)) (h4419 : (e4419 _v)) (h4546 : (e4546 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6600 : (e6600 _v)) (h6750 : (e6750 _v)) : (e7489 _v) := by
  have p15959 := n15959 _v _q h2179
  have p13951 := n13951 _v _q 
  have p15957 := n15957 _v _q h2179
  have p21212 := n21212 _v _q h51 h91 h191 h3152 h4260 h4306 h4653 h4675 h4787 h4813 h4838
  have p21204 := n21204 _v _q h51 h91 h191 h3152 h4260 h4306 h4653 h4675 h4787 h4813 h4838
  have p8439 := n8439 _v _q h6600
  have p16913 := n16913 _v _q 
  have p4976 := n4976 _v _q h4546
  have p4977 := n4977 _v _q h4285
  have p17100 := n17100 _v _q 
  have p19610 := n19610 _v _q 
  have p4981 := n4981 _v _q h4260
  have p10893 := n10893 _v _q 
  have p17102 := n17102 _v _q 
  have p5008 := n5008 _v _q h4787
  have p8420 := n8420 _v _q h6750
  have p5000 := n5000 _v _q h30
  have p4971 := n4971 _v _q h4419
  have p17009 := n17009 _v _q 
  have p5004 := n5004 _v _q h4220
  have p17147 := n17147 _v _q 
  have p15907 := n15907 _v _q h6600
  have p5006 := n5006 _v _q h4675
  have p4998 := n4998 _v _q h3152
  have p17096 := n17096 _v _q 
  have p17115 := n17115 _v _q 
  have p17758 := n17758 _v _q 
  have p17124 := n17124 _v _q 
  have p17111 := n17111 _v _q 
  have p15940 := n15940 _v _q h6750
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
  have p253 := n253 _v _q h191
  have p17020 := n17020 _v _q 
  have p20274 := n20274 _v _q 
  have p21142 := n21142 _v _q h51 h4260 h4306 h4653 h4813
  have p16729 := n16729 _v _q h51
  have p17050 := n17050 _v _q 
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4989 := n4989 _v _q h4838
  have p4983 := n4983 _v _q h4813
  have p17122 := n17122 _v _q 
  have p16778 := n16778 _v _q 
  have p20829 := n20829 _v _q 
  have p17108 := n17108 _v _q 
  have p20461 := n20461 _v _q 
  have p20426 := n20426 _v _q 
  have p20126 := n20126 _v _q 
  have p17110 := n17110 _v _q 
  have p17053 := n17053 _v _q 
  have p17131 := n17131 _v _q 
  have p20096 := n20096 _v _q 
  have p17058 := n17058 _v _q 
  have p17294 := n17294 _v _q 
  have p16943 := n16943 _v _q 
  have p17064 := n17064 _v _q 
  have p17067 := n17067 _v _q 
  have p17069 := n17069 _v _q 
  have p17080 := n17080 _v _q 
  have p17072 := n17072 _v _q 
  have p17083 := n17083 _v _q 
  have p17074 := n17074 _v _q 
  have p20836 := n20836 _v _q 
  have p17078 := n17078 _v _q 
  have p20653 := n20653 _v _q 
  have p17087 := n17087 _v _q 
  have p17136 := n17136 _v _q 
  have p17055 := n17055 _v _q 
  have p17091 := n17091 _v _q 
  have p17093 := n17093 _v _q 
  have p17141 := n17141 _v _q 
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p4979 := n4979 _v _q h4139
  exact FloorCertificate.node_21214 (e2 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2883 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p15959 p13951 p15957 p21212 p21204 p8439 p16913 p4976 p4977 p17100 p19610 p4981 p10893 p17102 p5008 p8420 p5000 p4971 p17009 p5004 p17147 p15907 p5006 p4998 p17096 p17115 p17758 p17124 p17111 p15940 p19665 p17113 p17117 p20467 p17120 p4999 p17133 p17874 p17104 p17127 p17089 p20470 p253 p17020 p20274 p21142 p16729 p17050 p17138 p17060 p4989 p4983 p17122 p16778 p20829 p17108 p20461 p20426 p20126 p17110 p17053 p17131 p20096 p17058 p17294 p16943 p17064 p17067 p17069 p17080 p17072 p17083 p17074 p20836 p17078 p20653 p17087 p17136 p17055 p17091 p17093 p17141 p17098 p17106 p4979
theorem n21216 (_v : Vars) (_q : Query _v)  : (e21215 _v) := by
  by_contra hc
  change ¬ ((e2402 _v) ∨ (¬ (e2179 _v)) ∨ (¬ (e4546 _v)) ∨ (¬ (e4285 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4787 _v)) ∨ (e2733 _v) ∨ (¬ (e30 _v)) ∨ (¬ (e4419 _v)) ∨ (¬ (e4220 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4139 _v))) at hc
  have h30 : (e30 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h191 : (e191 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h2179 : (e2179 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h4139 : (e4139 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))))))))))))))))
  have h4220 : (e4220 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h4260 : (e4260 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4285 : (e4285 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))
  have h4419 : (e4419 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h4546 : (e4546 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))
  have h4675 : (e4675 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))
  have h4838 : (e4838 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))
  have h6600 : (e6600 _v) := (fun hn => hc (Or.inl hn))
  have h6750 : (e6750 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have p21214 := n21214 _v _q h30 h51 h91 h191 h2179 h3152 h4139 h4220 h4260 h4285 h4306 h4419 h4546 h4653 h4675 h4787 h4813 h4838 h6600 h6750
  exact p21214
theorem n21217 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2179 : (e2179 _v)) (h3152 : (e3152 _v)) (h4139 : (e4139 _v)) (h4220 : (e4220 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4306 : (e4306 _v)) (h4419 : (e4419 _v)) (h4546 : (e4546 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6750 : (e6750 _v)) : (e2402 _v) := by
  have p21216 := n21216 _v _q 
  have p8420 := n8420 _v _q h6750
  have p4976 := n4976 _v _q h4546
  have p4977 := n4977 _v _q h4285
  have p4981 := n4981 _v _q h4260
  have p5008 := n5008 _v _q h4787
  have p15957 := n15957 _v _q h2179
  have p5000 := n5000 _v _q h30
  have p4971 := n4971 _v _q h4419
  have p5004 := n5004 _v _q h4220
  have p5006 := n5006 _v _q h4675
  have p4998 := n4998 _v _q h3152
  have p4999 := n4999 _v _q h91
  have p253 := n253 _v _q h191
  have p16729 := n16729 _v _q h51
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4989 := n4989 _v _q h4838
  have p4983 := n4983 _v _q h4813
  have p4979 := n4979 _v _q h4139
  change (e2402 _v) ∨ (¬ (e2179 _v)) ∨ (¬ (e4546 _v)) ∨ (¬ (e4285 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4787 _v)) ∨ (e2733 _v) ∨ (¬ (e30 _v)) ∨ (¬ (e4419 _v)) ∨ (¬ (e4220 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4139 _v)) at p21216
  change (¬ (e2733 _v)) at p8420
  rcases p21216 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p15957))
  · exact (False.elim (hlit p4976))
  · exact (False.elim (hlit p4977))
  · exact (False.elim (hlit p4981))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (p8420 hlit))
  · exact (False.elim (hlit p5000))
  · exact (False.elim (hlit p4971))
  · exact (False.elim (hlit p5004))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p253))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p4989))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p4979))
theorem n21218 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2179 : (e2179 _v)) (h3152 : (e3152 _v)) (h4139 : (e4139 _v)) (h4220 : (e4220 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4306 : (e4306 _v)) (h4419 : (e4419 _v)) (h4546 : (e4546 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6750 : (e6750 _v)) : (e3929 _v) := by
  have p14484 := n14484 _v _q 
  have p21217 := n21217 _v _q h30 h51 h91 h191 h2179 h3152 h4139 h4220 h4260 h4285 h4306 h4419 h4546 h4653 h4675 h4787 h4813 h4838 h6750
  change (¬ (e2402 _v)) ∨ (¬ (e3923 _v)) at p14484
  rcases p14484 with hlit | hlit
  · exact (False.elim (hlit p21217))
  · exact hlit
theorem n21219 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2179 : (e2179 _v)) (h3152 : (e3152 _v)) (h4139 : (e4139 _v)) (h4220 : (e4220 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4306 : (e4306 _v)) (h4419 : (e4419 _v)) (h4546 : (e4546 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6750 : (e6750 _v)) : (e3919 _v) := by
  have p14797 := n14797 _v _q 
  have p21218 := n21218 _v _q h30 h51 h91 h191 h2179 h3152 h4139 h4220 h4260 h4285 h4306 h4419 h4546 h4653 h4675 h4787 h4813 h4838 h6750
  change (e3923 _v) ∨ (e3919 _v) at p14797
  change (¬ (e3923 _v)) at p21218
  rcases p14797 with hlit | hlit
  · exact (False.elim (p21218 hlit))
  · exact hlit
theorem n21220 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2179 : (e2179 _v)) (h3152 : (e3152 _v)) (h4139 : (e4139 _v)) (h4220 : (e4220 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4306 : (e4306 _v)) (h4419 : (e4419 _v)) (h4546 : (e4546 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6750 : (e6750 _v)) : (e7489 _v) := by
  have p10893 := n10893 _v _q 
  have p258 := n258 _v _q 
  have p21219 := n21219 _v _q h30 h51 h91 h191 h2179 h3152 h4139 h4220 h4260 h4285 h4306 h4419 h4546 h4653 h4675 h4787 h4813 h4838 h6750
  have p4979 := n4979 _v _q h4139
  have p15959 := n15959 _v _q h2179
  have p13951 := n13951 _v _q 
  have p15957 := n15957 _v _q h2179
  have p21212 := n21212 _v _q h51 h91 h191 h3152 h4260 h4306 h4653 h4675 h4787 h4813 h4838
  have p21204 := n21204 _v _q h51 h91 h191 h3152 h4260 h4306 h4653 h4675 h4787 h4813 h4838
  have p16913 := n16913 _v _q 
  have p4976 := n4976 _v _q h4546
  have p4977 := n4977 _v _q h4285
  have p17100 := n17100 _v _q 
  have p19610 := n19610 _v _q 
  have p4981 := n4981 _v _q h4260
  have p17102 := n17102 _v _q 
  have p5008 := n5008 _v _q h4787
  have p8420 := n8420 _v _q h6750
  have p5000 := n5000 _v _q h30
  have p4971 := n4971 _v _q h4419
  have p17009 := n17009 _v _q 
  have p5004 := n5004 _v _q h4220
  have p5006 := n5006 _v _q h4675
  have p4998 := n4998 _v _q h3152
  have p17096 := n17096 _v _q 
  have p17115 := n17115 _v _q 
  have p17758 := n17758 _v _q 
  have p17124 := n17124 _v _q 
  have p17111 := n17111 _v _q 
  have p15940 := n15940 _v _q h6750
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
  have p253 := n253 _v _q h191
  have p17020 := n17020 _v _q 
  have p20274 := n20274 _v _q 
  have p21142 := n21142 _v _q h51 h4260 h4306 h4653 h4813
  have p16729 := n16729 _v _q h51
  have p17050 := n17050 _v _q 
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4989 := n4989 _v _q h4838
  have p4983 := n4983 _v _q h4813
  have p17122 := n17122 _v _q 
  have p16778 := n16778 _v _q 
  have p20829 := n20829 _v _q 
  have p17108 := n17108 _v _q 
  have p20461 := n20461 _v _q 
  have p20426 := n20426 _v _q 
  have p20126 := n20126 _v _q 
  have p17110 := n17110 _v _q 
  have p17053 := n17053 _v _q 
  have p17131 := n17131 _v _q 
  have p20096 := n20096 _v _q 
  have p17058 := n17058 _v _q 
  have p17294 := n17294 _v _q 
  have p16943 := n16943 _v _q 
  have p17064 := n17064 _v _q 
  have p17067 := n17067 _v _q 
  have p17069 := n17069 _v _q 
  have p17080 := n17080 _v _q 
  have p17072 := n17072 _v _q 
  have p17083 := n17083 _v _q 
  have p17074 := n17074 _v _q 
  have p20836 := n20836 _v _q 
  have p17078 := n17078 _v _q 
  have p20653 := n20653 _v _q 
  have p17087 := n17087 _v _q 
  have p17136 := n17136 _v _q 
  have p17055 := n17055 _v _q 
  have p17091 := n17091 _v _q 
  have p17093 := n17093 _v _q 
  have p17141 := n17141 _v _q 
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  exact FloorCertificate.node_21220 (e2 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p10893 p258 p21219 p4979 p15959 p13951 p15957 p21212 p21204 p16913 p4976 p4977 p17100 p19610 p4981 p17102 p5008 p8420 p5000 p4971 p17009 p5004 p5006 p4998 p17096 p17115 p17758 p17124 p17111 p15940 p19665 p17113 p17117 p20467 p17120 p4999 p17133 p17874 p17104 p17127 p17089 p20470 p253 p17020 p20274 p21142 p16729 p17050 p17138 p17060 p4989 p4983 p17122 p16778 p20829 p17108 p20461 p20426 p20126 p17110 p17053 p17131 p20096 p17058 p17294 p16943 p17064 p17067 p17069 p17080 p17072 p17083 p17074 p20836 p17078 p20653 p17087 p17136 p17055 p17091 p17093 p17141 p17098 p17106
theorem n21222 (_v : Vars) (_q : Query _v)  : (e21221 _v) := by
  by_contra hc
  change ¬ ((e2733 _v) ∨ (¬ (e4139 _v)) ∨ (¬ (e2179 _v)) ∨ (¬ (e4546 _v)) ∨ (¬ (e4285 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e30 _v)) ∨ (¬ (e4419 _v)) ∨ (¬ (e4220 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4813 _v))) at hc
  have h30 : (e30 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h191 : (e191 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h2179 : (e2179 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h4139 : (e4139 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h4220 : (e4220 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h4260 : (e4260 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h4285 : (e4285 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))
  have h4419 : (e4419 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h4546 : (e4546 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))
  have h4675 : (e4675 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn)))))))))))))))))))
  have h4838 : (e4838 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))
  have h6750 : (e6750 _v) := (fun hn => hc (Or.inl hn))
  have p21220 := n21220 _v _q h30 h51 h91 h191 h2179 h3152 h4139 h4220 h4260 h4285 h4306 h4419 h4546 h4653 h4675 h4787 h4813 h4838 h6750
  exact p21220
theorem n21223 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2132 : (e2132 _v)) (h3152 : (e3152 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) : (e2733 _v) := by
  have p21222 := n21222 _v _q 
  have p16850 := n16850 _v _q h2132
  have p21213 := n21213 _v _q h51 h91 h191 h2132 h3152 h4260 h4306 h4653 h4675 h4787 h4813 h4838
  have p16873 := n16873 _v _q h2132
  have p16567 := n16567 _v _q h2132
  have p4981 := n4981 _v _q h4260
  have p5008 := n5008 _v _q h4787
  have p16515 := n16515 _v _q h2132
  have p16683 := n16683 _v _q h2132
  have p16336 := n16336 _v _q h2132
  have p5006 := n5006 _v _q h4675
  have p4998 := n4998 _v _q h3152
  have p4999 := n4999 _v _q h91
  have p253 := n253 _v _q h191
  have p16729 := n16729 _v _q h51
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4989 := n4989 _v _q h4838
  have p4983 := n4983 _v _q h4813
  change (e2733 _v) ∨ (¬ (e4139 _v)) ∨ (¬ (e2179 _v)) ∨ (¬ (e4546 _v)) ∨ (¬ (e4285 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e30 _v)) ∨ (¬ (e4419 _v)) ∨ (¬ (e4220 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4813 _v)) at p21222
  rcases p21222 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p16850))
  · exact (False.elim (hlit p21213))
  · exact (False.elim (hlit p16873))
  · exact (False.elim (hlit p16567))
  · exact (False.elim (hlit p4981))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p16515))
  · exact (False.elim (hlit p16683))
  · exact (False.elim (hlit p16336))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p253))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p4989))
  · exact (False.elim (hlit p4983))
theorem n21224 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2132 : (e2132 _v)) (h3152 : (e3152 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) : (e2402 _v) := by
  have p11557 := n11557 _v _q 
  have p21223 := n21223 _v _q h51 h91 h191 h2132 h3152 h4260 h4306 h4653 h4675 h4787 h4813 h4838
  have p11349 := n11349 _v _q h2132
  change (e2402 _v) ∨ (¬ (e2733 _v)) ∨ (¬ (e2132 _v)) at p11557
  rcases p11557 with hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p21223))
  · exact (False.elim (hlit p11349))
theorem n21225 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2132 : (e2132 _v)) (h3152 : (e3152 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) : (e3929 _v) := by
  have p14484 := n14484 _v _q 
  have p21224 := n21224 _v _q h51 h91 h191 h2132 h3152 h4260 h4306 h4653 h4675 h4787 h4813 h4838
  change (¬ (e2402 _v)) ∨ (¬ (e3923 _v)) at p14484
  rcases p14484 with hlit | hlit
  · exact (False.elim (hlit p21224))
  · exact hlit
theorem n21226 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2132 : (e2132 _v)) (h3152 : (e3152 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) : (e3919 _v) := by
  have p14797 := n14797 _v _q 
  have p21225 := n21225 _v _q h51 h91 h191 h2132 h3152 h4260 h4306 h4653 h4675 h4787 h4813 h4838
  change (e3923 _v) ∨ (e3919 _v) at p14797
  change (¬ (e3923 _v)) at p21225
  rcases p14797 with hlit | hlit
  · exact (False.elim (p21225 hlit))
  · exact hlit
theorem n21227 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2132 : (e2132 _v)) (h3152 : (e3152 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) : (e4109 _v) := by
  have p14689 := n14689 _v _q 
  have p21223 := n21223 _v _q h51 h91 h191 h2132 h3152 h4260 h4306 h4653 h4675 h4787 h4813 h4838
  change (¬ (e2733 _v)) ∨ (¬ (e4108 _v)) at p14689
  rcases p14689 with hlit | hlit
  · exact (False.elim (hlit p21223))
  · exact hlit
theorem n21228 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2132 : (e2132 _v)) (h3152 : (e3152 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) : (e4101 _v) := by
  have p14929 := n14929 _v _q 
  have p21227 := n21227 _v _q h51 h91 h191 h2132 h3152 h4260 h4306 h4653 h4675 h4787 h4813 h4838
  change (e4108 _v) ∨ (e4101 _v) at p14929
  change (¬ (e4108 _v)) at p21227
  rcases p14929 with hlit | hlit
  · exact (False.elim (p21227 hlit))
  · exact hlit
theorem n21229 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2132 : (e2132 _v)) (h3152 : (e3152 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) : (e4616 _v) := by
  have p14684 := n14684 _v _q 
  have p21213 := n21213 _v _q h51 h91 h191 h2132 h3152 h4260 h4306 h4653 h4675 h4787 h4813 h4838
  change (¬ (e2179 _v)) ∨ (¬ (e3162 _v)) at p14684
  rcases p14684 with hlit | hlit
  · exact (False.elim (hlit p21213))
  · exact hlit
theorem n21230 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2132 : (e2132 _v)) (h3152 : (e3152 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) : (e3158 _v) := by
  have p15126 := n15126 _v _q 
  have p21229 := n21229 _v _q h51 h91 h191 h2132 h3152 h4260 h4306 h4653 h4675 h4787 h4813 h4838
  change (e3162 _v) ∨ (e3158 _v) at p15126
  change (¬ (e3162 _v)) at p21229
  rcases p15126 with hlit | hlit
  · exact (False.elim (p21229 hlit))
  · exact hlit
theorem n21231 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2132 : (e2132 _v)) (h3152 : (e3152 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) : (e7489 _v) := by
  have p17093 := n17093 _v _q 
  have p258 := n258 _v _q 
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p21228 := n21228 _v _q h51 h91 h191 h2132 h3152 h4260 h4306 h4653 h4675 h4787 h4813 h4838
  have p21226 := n21226 _v _q h51 h91 h191 h2132 h3152 h4260 h4306 h4653 h4675 h4787 h4813 h4838
  have p16850 := n16850 _v _q h2132
  have p21230 := n21230 _v _q h51 h91 h191 h2132 h3152 h4260 h4306 h4653 h4675 h4787 h4813 h4838
  have p13951 := n13951 _v _q 
  have p21212 := n21212 _v _q h51 h91 h191 h3152 h4260 h4306 h4653 h4675 h4787 h4813 h4838
  have p331 := n331 _v _q 
  have p16873 := n16873 _v _q h2132
  have p16567 := n16567 _v _q h2132
  have p17100 := n17100 _v _q 
  have p19610 := n19610 _v _q 
  have p4981 := n4981 _v _q h4260
  have p17102 := n17102 _v _q 
  have p5008 := n5008 _v _q h4787
  have p17141 := n17141 _v _q 
  have p16515 := n16515 _v _q h2132
  have p16683 := n16683 _v _q h2132
  have p17009 := n17009 _v _q 
  have p16336 := n16336 _v _q h2132
  have p5006 := n5006 _v _q h4675
  have p4998 := n4998 _v _q h3152
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
  have p253 := n253 _v _q h191
  have p17020 := n17020 _v _q 
  have p20274 := n20274 _v _q 
  have p21142 := n21142 _v _q h51 h4260 h4306 h4653 h4813
  have p16729 := n16729 _v _q h51
  have p17050 := n17050 _v _q 
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4989 := n4989 _v _q h4838
  have p4983 := n4983 _v _q h4813
  have p17122 := n17122 _v _q 
  have p16778 := n16778 _v _q 
  have p20829 := n20829 _v _q 
  have p17108 := n17108 _v _q 
  have p20461 := n20461 _v _q 
  have p20426 := n20426 _v _q 
  have p20126 := n20126 _v _q 
  have p17110 := n17110 _v _q 
  have p17053 := n17053 _v _q 
  have p17131 := n17131 _v _q 
  have p20096 := n20096 _v _q 
  have p17058 := n17058 _v _q 
  have p17294 := n17294 _v _q 
  have p16943 := n16943 _v _q 
  have p17064 := n17064 _v _q 
  have p17067 := n17067 _v _q 
  have p17069 := n17069 _v _q 
  have p17080 := n17080 _v _q 
  have p17072 := n17072 _v _q 
  have p17083 := n17083 _v _q 
  have p17074 := n17074 _v _q 
  have p20836 := n20836 _v _q 
  have p17078 := n17078 _v _q 
  have p20653 := n20653 _v _q 
  have p17087 := n17087 _v _q 
  have p17136 := n17136 _v _q 
  have p17055 := n17055 _v _q 
  have p17091 := n17091 _v _q 
  exact FloorCertificate.node_21231 (e2 _v) (e16 _v) (e17 _v) (e49 _v) (e80 _v) (e101 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2902 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p17093 p258 p17098 p17106 p21228 p21226 p16850 p21230 p13951 p21212 p331 p16873 p16567 p17100 p19610 p4981 p17102 p5008 p17141 p16515 p16683 p17009 p16336 p5006 p4998 p17096 p17115 p17758 p17124 p17111 p19665 p17113 p17117 p20467 p17120 p4999 p17133 p17874 p17104 p17127 p17089 p20470 p253 p17020 p20274 p21142 p16729 p17050 p17138 p17060 p4989 p4983 p17122 p16778 p20829 p17108 p20461 p20426 p20126 p17110 p17053 p17131 p20096 p17058 p17294 p16943 p17064 p17067 p17069 p17080 p17072 p17083 p17074 p20836 p17078 p20653 p17087 p17136 p17055 p17091
theorem n21233 (_v : Vars) (_q : Query _v)  : (e21232 _v) := by
  by_contra hc
  change ¬ ((¬ (e2132 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4813 _v))) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h191 : (e191 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h2132 : (e2132 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4260 : (e4260 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h4675 : (e4675 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))))))))
  have h4838 : (e4838 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have p21231 := n21231 _v _q h51 h91 h191 h2132 h3152 h4260 h4306 h4653 h4675 h4787 h4813 h4838
  exact p21231
theorem n21234 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h3152 : (e3152 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) : (e7742 _v) := by
  have p21233 := n21233 _v _q 
  have p4981 := n4981 _v _q h4260
  have p5008 := n5008 _v _q h4787
  have p5006 := n5006 _v _q h4675
  have p4998 := n4998 _v _q h3152
  have p4999 := n4999 _v _q h91
  have p253 := n253 _v _q h191
  have p16729 := n16729 _v _q h51
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4989 := n4989 _v _q h4838
  have p4983 := n4983 _v _q h4813
  change (¬ (e2132 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4813 _v)) at p21233
  rcases p21233 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p4981))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p253))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p4989))
  · exact (False.elim (hlit p4983))
theorem n21235 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h3152 : (e3152 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) : (e7754 _v) := by
  have p14942 := n14942 _v _q 
  have p21234 := n21234 _v _q h51 h91 h191 h3152 h4260 h4306 h4653 h4675 h4787 h4813 h4838
  change (e2132 _v) ∨ (¬ (e7753 _v)) at p14942
  change (¬ (e2132 _v)) at p21234
  rcases p14942 with hlit | hlit
  · exact (False.elim (p21234 hlit))
  · exact hlit
theorem n21236 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6525 : (e6525 _v)) : (e7742 _v) := by
  have p21233 := n21233 _v _q 
  have p4981 := n4981 _v _q h4260
  have p5008 := n5008 _v _q h4787
  have p16058 := n16058 _v _q h6525
  have p16689 := n16689 _v _q h6525
  have p4999 := n4999 _v _q h91
  have p253 := n253 _v _q h191
  have p16729 := n16729 _v _q h51
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4989 := n4989 _v _q h4838
  have p4983 := n4983 _v _q h4813
  change (¬ (e2132 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4813 _v)) at p21233
  rcases p21233 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p4981))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p16058))
  · exact (False.elim (hlit p16689))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p253))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p4989))
  · exact (False.elim (hlit p4983))
theorem n21237 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6525 : (e6525 _v)) : (e7754 _v) := by
  have p14942 := n14942 _v _q 
  have p21236 := n21236 _v _q h51 h91 h191 h4260 h4306 h4653 h4787 h4813 h4838 h6525
  change (e2132 _v) ∨ (¬ (e7753 _v)) at p14942
  change (¬ (e2132 _v)) at p21236
  rcases p14942 with hlit | hlit
  · exact (False.elim (p21236 hlit))
  · exact hlit
theorem n21238 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h3152 : (e3152 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4813 : (e4813 _v)) : (e7742 _v) := by
  have p21233 := n21233 _v _q 
  have p4981 := n4981 _v _q h4260
  have p21190 := n21190 _v _q h51 h91 h2529 h4306 h4653 h4813
  have p5006 := n5006 _v _q h4675
  have p4998 := n4998 _v _q h3152
  have p4999 := n4999 _v _q h91
  have p16705 := n16705 _v _q h2529
  have p16729 := n16729 _v _q h51
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p16572 := n16572 _v _q h2529
  have p4983 := n4983 _v _q h4813
  change (¬ (e2132 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4813 _v)) at p21233
  rcases p21233 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p4981))
  · exact (False.elim (hlit p21190))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p16705))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p16572))
  · exact (False.elim (hlit p4983))
theorem n21239 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h3152 : (e3152 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4813 : (e4813 _v)) : (e7754 _v) := by
  have p14942 := n14942 _v _q 
  have p21238 := n21238 _v _q h51 h91 h2529 h3152 h4260 h4306 h4653 h4675 h4813
  change (e2132 _v) ∨ (¬ (e7753 _v)) at p14942
  change (¬ (e2132 _v)) at p21238
  rcases p14942 with hlit | hlit
  · exact (False.elim (p21238 hlit))
  · exact hlit
theorem n21240 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e7742 _v) := by
  have p21233 := n21233 _v _q 
  have p16706 := n16706 _v _q h2529 h6525
  have p21190 := n21190 _v _q h51 h91 h2529 h4306 h4653 h4813
  have p16058 := n16058 _v _q h6525
  have p16689 := n16689 _v _q h6525
  have p4999 := n4999 _v _q h91
  have p16705 := n16705 _v _q h2529
  have p16729 := n16729 _v _q h51
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p16572 := n16572 _v _q h2529
  have p4983 := n4983 _v _q h4813
  change (¬ (e2132 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4813 _v)) at p21233
  rcases p21233 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p16706))
  · exact (False.elim (hlit p21190))
  · exact (False.elim (hlit p16058))
  · exact (False.elim (hlit p16689))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p16705))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p16572))
  · exact (False.elim (hlit p4983))
theorem n21241 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e7754 _v) := by
  have p14942 := n14942 _v _q 
  have p21240 := n21240 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  change (e2132 _v) ∨ (¬ (e7753 _v)) at p14942
  change (¬ (e2132 _v)) at p21240
  rcases p14942 with hlit | hlit
  · exact (False.elim (p21240 hlit))
  · exact hlit
theorem n21242 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h3152 : (e3152 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) : (e7749 _v) := by
  have p14941 := n14941 _v _q 
  have p21235 := n21235 _v _q h51 h91 h191 h3152 h4260 h4306 h4653 h4675 h4787 h4813 h4838
  change (e7753 _v) ∨ (e7749 _v) at p14941
  change (¬ (e7753 _v)) at p21235
  rcases p14941 with hlit | hlit
  · exact (False.elim (p21235 hlit))
  · exact hlit
theorem n21243 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h3152 : (e3152 _v)) (h3158 : (e3158 _v)) (h3937 : (e3937 _v)) (h4139 : (e4139 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4419 : (e4419 _v)) (h4546 : (e4546 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h5100 : (e5100 _v)) (h6750 : (e6750 _v)) (h7814 : (e7814 _v)) : (e7489 _v) := by
  have p4016 := n4016 _v _q 
  have p20126 := n20126 _v _q 
  have p10893 := n10893 _v _q 
  have p17110 := n17110 _v _q 
  have p8420 := n8420 _v _q h6750
  have p17053 := n17053 _v _q 
  have p4976 := n4976 _v _q h4546
  have p20096 := n20096 _v _q 
  have p17172 := n17172 _v _q h7814
  have p17131 := n17131 _v _q 
  have p13951 := n13951 _v _q 
  have p17294 := n17294 _v _q 
  have p16943 := n16943 _v _q 
  have p17058 := n17058 _v _q 
  have p16913 := n16913 _v _q 
  have p4971 := n4971 _v _q h4419
  have p4996 := n4996 _v _q h3937
  have p17064 := n17064 _v _q 
  have p17067 := n17067 _v _q 
  have p17080 := n17080 _v _q 
  have p17147 := n17147 _v _q 
  have p17072 := n17072 _v _q 
  have p17074 := n17074 _v _q 
  have p17069 := n17069 _v _q 
  have p17159 := n17159 _v _q h5100
  have p16885 := n16885 _v _q h3158
  have p20836 := n20836 _v _q 
  have p20653 := n20653 _v _q 
  have p17078 := n17078 _v _q 
  have p17136 := n17136 _v _q 
  have p4979 := n4979 _v _q h4139
  have p17087 := n17087 _v _q 
  have p17083 := n17083 _v _q 
  have p21242 := n21242 _v _q h51 h91 h191 h3152 h4260 h4306 h4653 h4675 h4787 h4813 h4838
  have p17055 := n17055 _v _q 
  have p17093 := n17093 _v _q 
  have p17091 := n17091 _v _q 
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p15940 := n15940 _v _q h6750
  have p21212 := n21212 _v _q h51 h91 h191 h3152 h4260 h4306 h4653 h4675 h4787 h4813 h4838
  have p17141 := n17141 _v _q 
  have p17100 := n17100 _v _q 
  have p19610 := n19610 _v _q 
  have p4981 := n4981 _v _q h4260
  have p17102 := n17102 _v _q 
  have p5008 := n5008 _v _q h4787
  have p17009 := n17009 _v _q 
  have p5006 := n5006 _v _q h4675
  have p4998 := n4998 _v _q h3152
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
  have p253 := n253 _v _q h191
  have p17020 := n17020 _v _q 
  have p20274 := n20274 _v _q 
  have p21142 := n21142 _v _q h51 h4260 h4306 h4653 h4813
  have p16729 := n16729 _v _q h51
  have p17050 := n17050 _v _q 
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4989 := n4989 _v _q h4838
  have p4983 := n4983 _v _q h4813
  have p17122 := n17122 _v _q 
  have p16778 := n16778 _v _q 
  have p20829 := n20829 _v _q 
  have p17108 := n17108 _v _q 
  have p20461 := n20461 _v _q 
  have p20426 := n20426 _v _q 
  exact FloorCertificate.node_21243 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2883 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p4016 p20126 p10893 p17110 p8420 p17053 p4976 p20096 p17172 p17131 p13951 p17294 p16943 p17058 p16913 p4971 p4996 p17064 p17067 p17080 p17147 p17072 p17074 p17069 p17159 p16885 p20836 p20653 p17078 p17136 p4979 p17087 p17083 p21242 p17055 p17093 p17091 p17098 p17106 p15940 p21212 p17141 p17100 p19610 p4981 p17102 p5008 p17009 p5006 p4998 p17096 p17115 p17758 p17124 p17111 p19665 p17113 p17117 p20467 p17120 p4999 p17133 p17874 p17104 p17127 p17089 p20470 p253 p17020 p20274 p21142 p16729 p17050 p17138 p17060 p4989 p4983 p17122 p16778 p20829 p17108 p20461 p20426
theorem n21244 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6525 : (e6525 _v)) : (e7749 _v) := by
  have p14941 := n14941 _v _q 
  have p21237 := n21237 _v _q h51 h91 h191 h4260 h4306 h4653 h4787 h4813 h4838 h6525
  change (e7753 _v) ∨ (e7749 _v) at p14941
  change (¬ (e7753 _v)) at p21237
  rcases p14941 with hlit | hlit
  · exact (False.elim (p21237 hlit))
  · exact hlit
theorem n21245 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6525 : (e6525 _v)) : (e4439 _v) := by
  have p14925 := n14925 _v _q 
  have p21206 := n21206 _v _q h51 h91 h191 h4260 h4306 h4653 h4787 h4813 h4838 h6525
  change (e4446 _v) ∨ (e4439 _v) at p14925
  change (¬ (e4446 _v)) at p21206
  rcases p14925 with hlit | hlit
  · exact (False.elim (p21206 hlit))
  · exact hlit
theorem n21246 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2179 : (e2179 _v)) (h2358 : (e2358 _v)) (h4101 : (e4101 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h5100 : (e5100 _v)) (h6525 : (e6525 _v)) (h6600 : (e6600 _v)) (h7814 : (e7814 _v)) (h7935 : (e7935 _v)) (h8038 : (e8038 _v)) : (e7489 _v) := by
  have p8602 := n8602 _v _q h8038
  have p15209 := n15209 _v _q h8038
  have p15907 := n15907 _v _q h6600
  have p17147 := n17147 _v _q 
  have p17172 := n17172 _v _q h7814
  have p8463 := n8463 _v _q h6525
  have p13951 := n13951 _v _q 
  have p16778 := n16778 _v _q 
  have p17122 := n17122 _v _q 
  have p4983 := n4983 _v _q h4813
  have p17163 := n17163 _v _q h7935
  have p16370 := n16370 _v _q h2358
  have p20829 := n20829 _v _q 
  have p17159 := n17159 _v _q h5100
  have p20426 := n20426 _v _q 
  have p20126 := n20126 _v _q 
  have p17110 := n17110 _v _q 
  have p17065 := n17065 _v _q h4101
  have p17053 := n17053 _v _q 
  have p20096 := n20096 _v _q 
  have p17131 := n17131 _v _q 
  have p17108 := n17108 _v _q 
  have p17294 := n17294 _v _q 
  have p16943 := n16943 _v _q 
  have p17058 := n17058 _v _q 
  have p15957 := n15957 _v _q h2179
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
  have p21244 := n21244 _v _q h51 h91 h191 h4260 h4306 h4653 h4787 h4813 h4838 h6525
  have p17055 := n17055 _v _q 
  have p17093 := n17093 _v _q 
  have p17091 := n17091 _v _q 
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p15959 := n15959 _v _q h2179
  have p21245 := n21245 _v _q h51 h91 h191 h4260 h4306 h4653 h4787 h4813 h4838 h6525
  have p17141 := n17141 _v _q 
  have p17100 := n17100 _v _q 
  have p19610 := n19610 _v _q 
  have p4981 := n4981 _v _q h4260
  have p17102 := n17102 _v _q 
  have p5008 := n5008 _v _q h4787
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
  have p253 := n253 _v _q h191
  have p17020 := n17020 _v _q 
  have p20274 := n20274 _v _q 
  have p21142 := n21142 _v _q h51 h4260 h4306 h4653 h4813
  have p16729 := n16729 _v _q h51
  have p17050 := n17050 _v _q 
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4989 := n4989 _v _q h4838
  have p8439 := n8439 _v _q h6600
  have p11354 := n11354 _v _q h2358
  exact FloorCertificate.node_21246 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2883 _v) (e2902 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p8602 p15209 p15907 p17147 p17172 p8463 p13951 p16778 p17122 p4983 p17163 p16370 p20829 p17159 p20426 p20126 p17110 p17065 p17053 p20096 p17131 p17108 p17294 p16943 p17058 p15957 p17064 p17067 p17080 p17072 p17074 p17069 p20461 p20836 p20653 p17078 p17136 p17087 p17083 p21244 p17055 p17093 p17091 p17098 p17106 p15959 p21245 p17141 p17100 p19610 p4981 p17102 p5008 p17009 p16058 p16689 p17096 p17115 p17758 p17124 p17111 p19665 p17113 p17117 p20467 p17120 p4999 p17133 p17874 p17104 p17127 p17089 p20470 p253 p17020 p20274 p21142 p16729 p17050 p17138 p17060 p4989 p8439 p11354
theorem n21247 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2179 : (e2179 _v)) (h3937 : (e3937 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4419 : (e4419 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h5100 : (e5100 _v)) (h6525 : (e6525 _v)) (h8038 : (e8038 _v)) : (e7489 _v) := by
  have p13951 := n13951 _v _q 
  have p258 := n258 _v _q 
  have p3130 := n3130 _v _q 
  have p17294 := n17294 _v _q 
  have p15957 := n15957 _v _q h2179
  have p16943 := n16943 _v _q 
  have p8463 := n8463 _v _q h6525
  have p17058 := n17058 _v _q 
  have p16913 := n16913 _v _q 
  have p4971 := n4971 _v _q h4419
  have p4996 := n4996 _v _q h3937
  have p15209 := n15209 _v _q h8038
  have p17064 := n17064 _v _q 
  have p17067 := n17067 _v _q 
  have p17080 := n17080 _v _q 
  have p17147 := n17147 _v _q 
  have p16925 := n16925 _v _q h4419 h8038
  have p17072 := n17072 _v _q 
  have p17074 := n17074 _v _q 
  have p17069 := n17069 _v _q 
  have p17159 := n17159 _v _q h5100
  have p15959 := n15959 _v _q h2179
  have p20836 := n20836 _v _q 
  have p20653 := n20653 _v _q 
  have p17078 := n17078 _v _q 
  have p17136 := n17136 _v _q 
  have p4979 := n4979 _v _q h4139
  have p17087 := n17087 _v _q 
  have p17083 := n17083 _v _q 
  have p21244 := n21244 _v _q h51 h91 h191 h4260 h4306 h4653 h4787 h4813 h4838 h6525
  have p17055 := n17055 _v _q 
  have p17093 := n17093 _v _q 
  have p17091 := n17091 _v _q 
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p5001 := n5001 _v _q h4096
  have p21245 := n21245 _v _q h51 h91 h191 h4260 h4306 h4653 h4787 h4813 h4838 h6525
  have p17141 := n17141 _v _q 
  have p17100 := n17100 _v _q 
  have p19610 := n19610 _v _q 
  have p4981 := n4981 _v _q h4260
  have p17102 := n17102 _v _q 
  have p5008 := n5008 _v _q h4787
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
  have p253 := n253 _v _q h191
  have p17020 := n17020 _v _q 
  have p20274 := n20274 _v _q 
  have p21142 := n21142 _v _q h51 h4260 h4306 h4653 h4813
  have p16729 := n16729 _v _q h51
  have p17050 := n17050 _v _q 
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4989 := n4989 _v _q h4838
  have p4983 := n4983 _v _q h4813
  have p17122 := n17122 _v _q 
  have p16778 := n16778 _v _q 
  have p20829 := n20829 _v _q 
  have p17108 := n17108 _v _q 
  have p20461 := n20461 _v _q 
  have p20426 := n20426 _v _q 
  have p20126 := n20126 _v _q 
  have p17110 := n17110 _v _q 
  have p17053 := n17053 _v _q 
  have p17131 := n17131 _v _q 
  have p20096 := n20096 _v _q 
  exact FloorCertificate.node_21247 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2883 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p13951 p258 p3130 p17294 p15957 p16943 p8463 p17058 p16913 p4971 p4996 p15209 p17064 p17067 p17080 p17147 p16925 p17072 p17074 p17069 p17159 p15959 p20836 p20653 p17078 p17136 p4979 p17087 p17083 p21244 p17055 p17093 p17091 p17098 p17106 p5001 p21245 p17141 p17100 p19610 p4981 p17102 p5008 p17009 p16058 p16689 p17096 p17115 p17758 p17124 p17111 p19665 p17113 p17117 p20467 p17120 p4999 p17133 p17874 p17104 p17127 p17089 p20470 p253 p17020 p20274 p21142 p16729 p17050 p17138 p17060 p4989 p4983 p17122 p16778 p20829 p17108 p20461 p20426 p20126 p17110 p17053 p17131 p20096
theorem n21248 (_v : Vars) (_q : Query _v) (h13 : (e13 _v)) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2787 : (e2787 _v)) (h3152 : (e3152 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6501 : (e6501 _v)) : (e7489 _v) := by
  have p16349 := n16349 _v _q h2787
  have p11430 := n11430 _v _q h2787
  have p4977 := n4977 _v _q h4285
  have p17136 := n17136 _v _q 
  have p10893 := n10893 _v _q 
  have p16913 := n16913 _v _q 
  have p16691 := n16691 _v _q h13
  have p13951 := n13951 _v _q 
  have p8554 := n8554 _v _q h6501
  have p10896 := n10896 _v _q 
  have p21242 := n21242 _v _q h51 h91 h191 h3152 h4260 h4306 h4653 h4675 h4787 h4813 h4838
  have p17055 := n17055 _v _q 
  have p17093 := n17093 _v _q 
  have p17091 := n17091 _v _q 
  have p15641 := n15641 _v _q h6501
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p5001 := n5001 _v _q h4096
  have p16576 := n16576 _v _q 
  have p4979 := n4979 _v _q h4139
  have p21212 := n21212 _v _q h51 h91 h191 h3152 h4260 h4306 h4653 h4675 h4787 h4813 h4838
  have p17141 := n17141 _v _q 
  have p16694 := n16694 _v _q h13
  have p17100 := n17100 _v _q 
  have p19610 := n19610 _v _q 
  have p4981 := n4981 _v _q h4260
  have p17102 := n17102 _v _q 
  have p5008 := n5008 _v _q h4787
  have p16325 := n16325 _v _q h6501
  have p17009 := n17009 _v _q 
  have p17147 := n17147 _v _q 
  have p5006 := n5006 _v _q h4675
  have p4998 := n4998 _v _q h3152
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
  have p253 := n253 _v _q h191
  have p17020 := n17020 _v _q 
  have p20274 := n20274 _v _q 
  have p21142 := n21142 _v _q h51 h4260 h4306 h4653 h4813
  have p16729 := n16729 _v _q h51
  have p17050 := n17050 _v _q 
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4989 := n4989 _v _q h4838
  have p4983 := n4983 _v _q h4813
  have p17122 := n17122 _v _q 
  have p16778 := n16778 _v _q 
  have p20829 := n20829 _v _q 
  have p17108 := n17108 _v _q 
  have p20461 := n20461 _v _q 
  have p20426 := n20426 _v _q 
  have p20126 := n20126 _v _q 
  have p17110 := n17110 _v _q 
  have p17053 := n17053 _v _q 
  have p17131 := n17131 _v _q 
  have p20096 := n20096 _v _q 
  have p17058 := n17058 _v _q 
  have p17294 := n17294 _v _q 
  have p16943 := n16943 _v _q 
  have p17064 := n17064 _v _q 
  have p17067 := n17067 _v _q 
  have p17069 := n17069 _v _q 
  have p17080 := n17080 _v _q 
  have p17072 := n17072 _v _q 
  have p17083 := n17083 _v _q 
  have p17074 := n17074 _v _q 
  have p20836 := n20836 _v _q 
  have p17078 := n17078 _v _q 
  have p20653 := n20653 _v _q 
  have p17087 := n17087 _v _q 
  exact FloorCertificate.node_21248 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2863 _v) (e2877 _v) (e2883 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p16349 p11430 p4977 p17136 p10893 p16913 p16691 p13951 p8554 p10896 p21242 p17055 p17093 p17091 p15641 p17098 p17106 p5001 p16576 p4979 p21212 p17141 p16694 p17100 p19610 p4981 p17102 p5008 p16325 p17009 p17147 p5006 p4998 p17096 p17115 p17758 p17124 p17111 p19665 p17113 p17117 p20467 p17120 p4999 p17133 p17874 p17104 p17127 p17089 p20470 p253 p17020 p20274 p21142 p16729 p17050 p17138 p17060 p4989 p4983 p17122 p16778 p20829 p17108 p20461 p20426 p20126 p17110 p17053 p17131 p20096 p17058 p17294 p16943 p17064 p17067 p17069 p17080 p17072 p17083 p17074 p20836 p17078 p20653 p17087
theorem n21249 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h3152 : (e3152 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4813 : (e4813 _v)) : (e4439 _v) := by
  have p14925 := n14925 _v _q 
  have p21208 := n21208 _v _q h51 h91 h2529 h3152 h4260 h4306 h4653 h4675 h4813
  change (e4446 _v) ∨ (e4439 _v) at p14925
  change (¬ (e4446 _v)) at p21208
  rcases p14925 with hlit | hlit
  · exact (False.elim (p21208 hlit))
  · exact hlit
theorem n21250 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h3152 : (e3152 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4813 : (e4813 _v)) : (e7749 _v) := by
  have p14941 := n14941 _v _q 
  have p21239 := n21239 _v _q h51 h91 h2529 h3152 h4260 h4306 h4653 h4675 h4813
  change (e7753 _v) ∨ (e7749 _v) at p14941
  change (¬ (e7753 _v)) at p21239
  rcases p14941 with hlit | hlit
  · exact (False.elim (p21239 hlit))
  · exact hlit
theorem n21251 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4608 : (e4608 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4813 : (e4813 _v)) (h6750 : (e6750 _v)) (h7807 : (e7807 _v)) (h7935 : (e7935 _v)) (h8045 : (e8045 _v)) : (e7489 _v) := by
  have p4016 := n4016 _v _q 
  have p11350 := n11350 _v _q h7807
  have p17157 := n17157 _v _q h8045
  have p10893 := n10893 _v _q 
  have p8548 := n8548 _v _q h2529
  have p17093 := n17093 _v _q 
  have p15373 := n15373 _v _q h7807
  have p17091 := n17091 _v _q 
  have p4991 := n4991 _v _q h4608
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p8420 := n8420 _v _q h6750
  have p15940 := n15940 _v _q h6750
  have p16576 := n16576 _v _q 
  have p13951 := n13951 _v _q 
  have p21249 := n21249 _v _q h51 h91 h2529 h3152 h4260 h4306 h4653 h4675 h4813
  have p17141 := n17141 _v _q 
  have p17100 := n17100 _v _q 
  have p19610 := n19610 _v _q 
  have p4981 := n4981 _v _q h4260
  have p17102 := n17102 _v _q 
  have p21190 := n21190 _v _q h51 h91 h2529 h4306 h4653 h4813
  have p4996 := n4996 _v _q h3937
  have p16977 := n16977 _v _q 
  have p17256 := n17256 _v _q 
  have p17009 := n17009 _v _q 
  have p17147 := n17147 _v _q 
  have p5006 := n5006 _v _q h4675
  have p4998 := n4998 _v _q h3152
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
  have p21142 := n21142 _v _q h51 h4260 h4306 h4653 h4813
  have p16729 := n16729 _v _q h51
  have p17050 := n17050 _v _q 
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p16572 := n16572 _v _q h2529
  have p4983 := n4983 _v _q h4813
  have p17122 := n17122 _v _q 
  have p16778 := n16778 _v _q 
  have p20829 := n20829 _v _q 
  have p17108 := n17108 _v _q 
  have p20461 := n20461 _v _q 
  have p20426 := n20426 _v _q 
  have p20126 := n20126 _v _q 
  have p17110 := n17110 _v _q 
  have p17053 := n17053 _v _q 
  have p17131 := n17131 _v _q 
  have p20096 := n20096 _v _q 
  have p17058 := n17058 _v _q 
  have p17294 := n17294 _v _q 
  have p16943 := n16943 _v _q 
  have p17064 := n17064 _v _q 
  have p17067 := n17067 _v _q 
  have p17069 := n17069 _v _q 
  have p17080 := n17080 _v _q 
  have p17072 := n17072 _v _q 
  have p17083 := n17083 _v _q 
  have p17074 := n17074 _v _q 
  have p20836 := n20836 _v _q 
  have p17078 := n17078 _v _q 
  have p20653 := n20653 _v _q 
  have p17087 := n17087 _v _q 
  have p17136 := n17136 _v _q 
  have p17055 := n17055 _v _q 
  have p18959 := n18959 _v _q h7807
  have p21250 := n21250 _v _q h51 h91 h2529 h3152 h4260 h4306 h4653 h4675 h4813
  have p17163 := n17163 _v _q h7935
  exact FloorCertificate.node_21251 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2863 _v) (e2877 _v) (e2883 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p4016 p11350 p17157 p10893 p8548 p17093 p15373 p17091 p4991 p17098 p17106 p8420 p15940 p16576 p13951 p21249 p17141 p17100 p19610 p4981 p17102 p21190 p4996 p16977 p17256 p17009 p17147 p5006 p4998 p17096 p17115 p17758 p17124 p17111 p19665 p17113 p17117 p20467 p17120 p4999 p17133 p17874 p17104 p17127 p17089 p20470 p16705 p17020 p20274 p21142 p16729 p17050 p17138 p17060 p16572 p4983 p17122 p16778 p20829 p17108 p20461 p20426 p20126 p17110 p17053 p17131 p20096 p17058 p17294 p16943 p17064 p17067 p17069 p17080 p17072 p17083 p17074 p20836 p17078 p20653 p17087 p17136 p17055 p18959 p21250 p17163
theorem n21252 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2787 : (e2787 _v)) (h3152 : (e3152 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4546 : (e4546 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6501 : (e6501 _v)) (h7807 : (e7807 _v)) : (e7489 _v) := by
  have p16349 := n16349 _v _q h2787
  have p8554 := n8554 _v _q h6501
  have p10893 := n10893 _v _q 
  have p17093 := n17093 _v _q 
  have p15373 := n15373 _v _q h7807
  have p17091 := n17091 _v _q 
  have p15641 := n15641 _v _q h6501
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p14109 := n14109 _v _q h7807
  have p5001 := n5001 _v _q h4096
  have p16576 := n16576 _v _q 
  have p13951 := n13951 _v _q 
  have p21212 := n21212 _v _q h51 h91 h191 h3152 h4260 h4306 h4653 h4675 h4787 h4813 h4838
  have p17141 := n17141 _v _q 
  have p4976 := n4976 _v _q h4546
  have p17100 := n17100 _v _q 
  have p19610 := n19610 _v _q 
  have p4981 := n4981 _v _q h4260
  have p17102 := n17102 _v _q 
  have p5008 := n5008 _v _q h4787
  have p16325 := n16325 _v _q h6501
  have p16977 := n16977 _v _q 
  have p11430 := n11430 _v _q h2787
  have p17009 := n17009 _v _q 
  have p17147 := n17147 _v _q 
  have p5006 := n5006 _v _q h4675
  have p4998 := n4998 _v _q h3152
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
  have p253 := n253 _v _q h191
  have p17020 := n17020 _v _q 
  have p20274 := n20274 _v _q 
  have p21142 := n21142 _v _q h51 h4260 h4306 h4653 h4813
  have p16729 := n16729 _v _q h51
  have p17050 := n17050 _v _q 
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4989 := n4989 _v _q h4838
  have p4983 := n4983 _v _q h4813
  have p17122 := n17122 _v _q 
  have p16778 := n16778 _v _q 
  have p20829 := n20829 _v _q 
  have p17108 := n17108 _v _q 
  have p20461 := n20461 _v _q 
  have p20426 := n20426 _v _q 
  have p20126 := n20126 _v _q 
  have p17110 := n17110 _v _q 
  have p17053 := n17053 _v _q 
  have p17131 := n17131 _v _q 
  have p20096 := n20096 _v _q 
  have p17058 := n17058 _v _q 
  have p17294 := n17294 _v _q 
  have p16943 := n16943 _v _q 
  have p17064 := n17064 _v _q 
  have p17067 := n17067 _v _q 
  have p17069 := n17069 _v _q 
  have p17080 := n17080 _v _q 
  have p17072 := n17072 _v _q 
  have p17083 := n17083 _v _q 
  have p17074 := n17074 _v _q 
  have p20836 := n20836 _v _q 
  have p17078 := n17078 _v _q 
  have p20653 := n20653 _v _q 
  have p17087 := n17087 _v _q 
  have p17136 := n17136 _v _q 
  have p17055 := n17055 _v _q 
  have p18959 := n18959 _v _q h7807
  have p21242 := n21242 _v _q h51 h91 h191 h3152 h4260 h4306 h4653 h4675 h4787 h4813 h4838
  have p11350 := n11350 _v _q h7807
  have p4979 := n4979 _v _q h4139
  exact FloorCertificate.node_21252 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2863 _v) (e2877 _v) (e2883 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p16349 p8554 p10893 p17093 p15373 p17091 p15641 p17098 p17106 p14109 p5001 p16576 p13951 p21212 p17141 p4976 p17100 p19610 p4981 p17102 p5008 p16325 p16977 p11430 p17009 p17147 p5006 p4998 p17096 p17115 p17758 p17124 p17111 p19665 p17113 p17117 p20467 p17120 p4999 p17133 p17874 p17104 p17127 p17089 p20470 p253 p17020 p20274 p21142 p16729 p17050 p17138 p17060 p4989 p4983 p17122 p16778 p20829 p17108 p20461 p20426 p20126 p17110 p17053 p17131 p20096 p17058 p17294 p16943 p17064 p17067 p17069 p17080 p17072 p17083 p17074 p20836 p17078 p20653 p17087 p17136 p17055 p18959 p21242 p11350 p4979
theorem n21253 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2179 : (e2179 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4546 : (e4546 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6525 : (e6525 _v)) (h6571 : (e6571 _v)) (h6750 : (e6750 _v)) : (e7489 _v) := by
  have p15959 := n15959 _v _q h2179
  have p15957 := n15957 _v _q h2179
  have p8447 := n8447 _v _q h6571
  have p20653 := n20653 _v _q 
  have p4976 := n4976 _v _q h4546
  have p17078 := n17078 _v _q 
  have p8463 := n8463 _v _q h6525
  have p8420 := n8420 _v _q h6750
  have p17255 := n17255 _v _q h6571
  have p15623 := n15623 _v _q h6571
  have p10893 := n10893 _v _q 
  have p17136 := n17136 _v _q 
  have p17189 := n17189 _v _q h6571
  have p17087 := n17087 _v _q 
  have p13951 := n13951 _v _q 
  have p21244 := n21244 _v _q h51 h91 h191 h4260 h4306 h4653 h4787 h4813 h4838 h6525
  have p17055 := n17055 _v _q 
  have p17093 := n17093 _v _q 
  have p17091 := n17091 _v _q 
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p15940 := n15940 _v _q h6750
  have p17256 := n17256 _v _q 
  have p21245 := n21245 _v _q h51 h91 h191 h4260 h4306 h4653 h4787 h4813 h4838 h6525
  have p17141 := n17141 _v _q 
  have p17100 := n17100 _v _q 
  have p19610 := n19610 _v _q 
  have p4981 := n4981 _v _q h4260
  have p17102 := n17102 _v _q 
  have p5008 := n5008 _v _q h4787
  have p16707 := n16707 _v _q h2179 h6525 h6571 h6750
  have p17009 := n17009 _v _q 
  have p17147 := n17147 _v _q 
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
  have p253 := n253 _v _q h191
  have p17020 := n17020 _v _q 
  have p20274 := n20274 _v _q 
  have p21142 := n21142 _v _q h51 h4260 h4306 h4653 h4813
  have p16729 := n16729 _v _q h51
  have p17050 := n17050 _v _q 
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4989 := n4989 _v _q h4838
  have p4983 := n4983 _v _q h4813
  have p17122 := n17122 _v _q 
  have p16778 := n16778 _v _q 
  have p20829 := n20829 _v _q 
  have p17108 := n17108 _v _q 
  have p20461 := n20461 _v _q 
  have p20426 := n20426 _v _q 
  have p20126 := n20126 _v _q 
  have p17110 := n17110 _v _q 
  have p17053 := n17053 _v _q 
  have p17131 := n17131 _v _q 
  have p20096 := n20096 _v _q 
  have p17058 := n17058 _v _q 
  have p17294 := n17294 _v _q 
  have p16943 := n16943 _v _q 
  have p17064 := n17064 _v _q 
  have p17067 := n17067 _v _q 
  have p17069 := n17069 _v _q 
  have p17080 := n17080 _v _q 
  have p17072 := n17072 _v _q 
  have p17083 := n17083 _v _q 
  have p17074 := n17074 _v _q 
  have p20836 := n20836 _v _q 
  have p16977 := n16977 _v _q 
  exact FloorCertificate.node_21253 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2883 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p15959 p15957 p8447 p20653 p4976 p17078 p8463 p8420 p17255 p15623 p10893 p17136 p17189 p17087 p13951 p21244 p17055 p17093 p17091 p17098 p17106 p15940 p17256 p21245 p17141 p17100 p19610 p4981 p17102 p5008 p16707 p17009 p17147 p16058 p16689 p17096 p17115 p17758 p17124 p17111 p19665 p17113 p17117 p20467 p17120 p4999 p17133 p17874 p17104 p17127 p17089 p20470 p253 p17020 p20274 p21142 p16729 p17050 p17138 p17060 p4989 p4983 p17122 p16778 p20829 p17108 p20461 p20426 p20126 p17110 p17053 p17131 p20096 p17058 p17294 p16943 p17064 p17067 p17069 p17080 p17072 p17083 p17074 p20836 p16977
theorem n21254 (_v : Vars) (_q : Query _v) (h13 : (e13 _v)) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2179 : (e2179 _v)) (h2303 : (e2303 _v)) (h3919 : (e3919 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6525 : (e6525 _v)) : (e7489 _v) := by
  have p13951 := n13951 _v _q 
  have p17072 := n17072 _v _q 
  have p3130 := n3130 _v _q 
  have p15957 := n15957 _v _q h2179
  have p17074 := n17074 _v _q 
  have p8463 := n8463 _v _q h6525
  have p258 := n258 _v _q 
  have p16913 := n16913 _v _q 
  have p16691 := n16691 _v _q h13
  have p16877 := n16877 _v _q h13 h2303
  have p16436 := n16436 _v _q h2303
  have p15959 := n15959 _v _q h2179
  have p20836 := n20836 _v _q 
  have p20653 := n20653 _v _q 
  have p16694 := n16694 _v _q h13
  have p17078 := n17078 _v _q 
  have p17136 := n17136 _v _q 
  have p4979 := n4979 _v _q h4139
  have p17087 := n17087 _v _q 
  have p17083 := n17083 _v _q 
  have p21244 := n21244 _v _q h51 h91 h191 h4260 h4306 h4653 h4787 h4813 h4838 h6525
  have p17055 := n17055 _v _q 
  have p17093 := n17093 _v _q 
  have p17091 := n17091 _v _q 
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p5001 := n5001 _v _q h4096
  have p21245 := n21245 _v _q h51 h91 h191 h4260 h4306 h4653 h4787 h4813 h4838 h6525
  have p17141 := n17141 _v _q 
  have p17100 := n17100 _v _q 
  have p19610 := n19610 _v _q 
  have p4981 := n4981 _v _q h4260
  have p17102 := n17102 _v _q 
  have p5008 := n5008 _v _q h4787
  have p17009 := n17009 _v _q 
  have p17079 := n17079 _v _q h3919
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
  have p253 := n253 _v _q h191
  have p17020 := n17020 _v _q 
  have p20274 := n20274 _v _q 
  have p21142 := n21142 _v _q h51 h4260 h4306 h4653 h4813
  have p16729 := n16729 _v _q h51
  have p17050 := n17050 _v _q 
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4989 := n4989 _v _q h4838
  have p4983 := n4983 _v _q h4813
  have p17122 := n17122 _v _q 
  have p16778 := n16778 _v _q 
  have p20829 := n20829 _v _q 
  have p17108 := n17108 _v _q 
  have p20461 := n20461 _v _q 
  have p20426 := n20426 _v _q 
  have p20126 := n20126 _v _q 
  have p17110 := n17110 _v _q 
  have p17053 := n17053 _v _q 
  have p17131 := n17131 _v _q 
  have p20096 := n20096 _v _q 
  have p17058 := n17058 _v _q 
  have p17294 := n17294 _v _q 
  have p16943 := n16943 _v _q 
  have p17064 := n17064 _v _q 
  have p17067 := n17067 _v _q 
  have p17069 := n17069 _v _q 
  have p17080 := n17080 _v _q 
  exact FloorCertificate.node_21254 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p13951 p17072 p3130 p15957 p17074 p8463 p258 p16913 p16691 p16877 p16436 p15959 p20836 p20653 p16694 p17078 p17136 p4979 p17087 p17083 p21244 p17055 p17093 p17091 p17098 p17106 p5001 p21245 p17141 p17100 p19610 p4981 p17102 p5008 p17009 p17079 p16058 p16689 p17096 p17115 p17758 p17124 p17111 p19665 p17113 p17117 p20467 p17120 p4999 p17133 p17874 p17104 p17127 p17089 p20470 p253 p17020 p20274 p21142 p16729 p17050 p17138 p17060 p4989 p4983 p17122 p16778 p20829 p17108 p20461 p20426 p20126 p17110 p17053 p17131 p20096 p17058 p17294 p16943 p17064 p17067 p17069 p17080
theorem n21255 (_v : Vars) (_q : Query _v) (h13 : (e13 _v)) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2179 : (e2179 _v)) (h3152 : (e3152 _v)) (h4139 : (e4139 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6600 : (e6600 _v)) (h6750 : (e6750 _v)) : (e7489 _v) := by
  have p11396 := n11396 _v _q h13
  have p16691 := n16691 _v _q h13
  have p17064 := n17064 _v _q 
  have p16694 := n16694 _v _q h13
  have p17067 := n17067 _v _q 
  have p8439 := n8439 _v _q h6600
  have p17080 := n17080 _v _q 
  have p17147 := n17147 _v _q 
  have p13951 := n13951 _v _q 
  have p17072 := n17072 _v _q 
  have p17074 := n17074 _v _q 
  have p17069 := n17069 _v _q 
  have p16913 := n16913 _v _q 
  have p16878 := n16878 _v _q h13
  have p16714 := n16714 _v _q h13
  have p15959 := n15959 _v _q h2179
  have p20836 := n20836 _v _q 
  have p20653 := n20653 _v _q 
  have p17078 := n17078 _v _q 
  have p17136 := n17136 _v _q 
  have p4979 := n4979 _v _q h4139
  have p17087 := n17087 _v _q 
  have p17083 := n17083 _v _q 
  have p21242 := n21242 _v _q h51 h91 h191 h3152 h4260 h4306 h4653 h4675 h4787 h4813 h4838
  have p17055 := n17055 _v _q 
  have p17093 := n17093 _v _q 
  have p17091 := n17091 _v _q 
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p15940 := n15940 _v _q h6750
  have p21212 := n21212 _v _q h51 h91 h191 h3152 h4260 h4306 h4653 h4675 h4787 h4813 h4838
  have p17141 := n17141 _v _q 
  have p17100 := n17100 _v _q 
  have p19610 := n19610 _v _q 
  have p4981 := n4981 _v _q h4260
  have p17102 := n17102 _v _q 
  have p5008 := n5008 _v _q h4787
  have p17009 := n17009 _v _q 
  have p8420 := n8420 _v _q h6750
  have p5006 := n5006 _v _q h4675
  have p4998 := n4998 _v _q h3152
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
  have p253 := n253 _v _q h191
  have p17020 := n17020 _v _q 
  have p20274 := n20274 _v _q 
  have p21142 := n21142 _v _q h51 h4260 h4306 h4653 h4813
  have p16729 := n16729 _v _q h51
  have p17050 := n17050 _v _q 
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4989 := n4989 _v _q h4838
  have p4983 := n4983 _v _q h4813
  have p17122 := n17122 _v _q 
  have p16778 := n16778 _v _q 
  have p20829 := n20829 _v _q 
  have p17108 := n17108 _v _q 
  have p20461 := n20461 _v _q 
  have p20426 := n20426 _v _q 
  have p20126 := n20126 _v _q 
  have p17110 := n17110 _v _q 
  have p17053 := n17053 _v _q 
  have p17131 := n17131 _v _q 
  have p20096 := n20096 _v _q 
  have p17058 := n17058 _v _q 
  have p17294 := n17294 _v _q 
  have p16943 := n16943 _v _q 
  have p15907 := n15907 _v _q h6600
  have p15957 := n15957 _v _q h2179
  have p10893 := n10893 _v _q 
  exact FloorCertificate.node_21255 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2883 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p11396 p16691 p17064 p16694 p17067 p8439 p17080 p17147 p13951 p17072 p17074 p17069 p16913 p16878 p16714 p15959 p20836 p20653 p17078 p17136 p4979 p17087 p17083 p21242 p17055 p17093 p17091 p17098 p17106 p15940 p21212 p17141 p17100 p19610 p4981 p17102 p5008 p17009 p8420 p5006 p4998 p17096 p17115 p17758 p17124 p17111 p19665 p17113 p17117 p20467 p17120 p4999 p17133 p17874 p17104 p17127 p17089 p20470 p253 p17020 p20274 p21142 p16729 p17050 p17138 p17060 p4989 p4983 p17122 p16778 p20829 p17108 p20461 p20426 p20126 p17110 p17053 p17131 p20096 p17058 p17294 p16943 p15907 p15957 p10893
theorem n21256 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h3158 : (e3158 _v)) (h3919 : (e3919 _v)) (h4101 : (e4101 _v)) (h4139 : (e4139 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4546 : (e4546 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h5100 : (e5100 _v)) (h6525 : (e6525 _v)) (h7814 : (e7814 _v)) (h7935 : (e7935 _v)) : (e7489 _v) := by
  have p5257 := n5257 _v _q 
  have p3130 := n3130 _v _q 
  have p5391 := n5391 _v _q 
  have p8463 := n8463 _v _q h6525
  have p4976 := n4976 _v _q h4546
  have p13951 := n13951 _v _q 
  have p16778 := n16778 _v _q 
  have p17122 := n17122 _v _q 
  have p4983 := n4983 _v _q h4813
  have p17163 := n17163 _v _q h7935
  have p4979 := n4979 _v _q h4139
  have p20829 := n20829 _v _q 
  have p17159 := n17159 _v _q h5100
  have p20426 := n20426 _v _q 
  have p20126 := n20126 _v _q 
  have p17110 := n17110 _v _q 
  have p17065 := n17065 _v _q h4101
  have p17053 := n17053 _v _q 
  have p20096 := n20096 _v _q 
  have p17131 := n17131 _v _q 
  have p17108 := n17108 _v _q 
  have p17294 := n17294 _v _q 
  have p16943 := n16943 _v _q 
  have p17058 := n17058 _v _q 
  have p17079 := n17079 _v _q h3919
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
  have p21244 := n21244 _v _q h51 h91 h191 h4260 h4306 h4653 h4787 h4813 h4838 h6525
  have p17055 := n17055 _v _q 
  have p17093 := n17093 _v _q 
  have p17091 := n17091 _v _q 
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p16885 := n16885 _v _q h3158
  have p21245 := n21245 _v _q h51 h91 h191 h4260 h4306 h4653 h4787 h4813 h4838 h6525
  have p17141 := n17141 _v _q 
  have p17100 := n17100 _v _q 
  have p19610 := n19610 _v _q 
  have p4981 := n4981 _v _q h4260
  have p17102 := n17102 _v _q 
  have p5008 := n5008 _v _q h4787
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
  have p253 := n253 _v _q h191
  have p17020 := n17020 _v _q 
  have p20274 := n20274 _v _q 
  have p21142 := n21142 _v _q h51 h4260 h4306 h4653 h4813
  have p16729 := n16729 _v _q h51
  have p17050 := n17050 _v _q 
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4989 := n4989 _v _q h4838
  have p17172 := n17172 _v _q h7814
  exact FloorCertificate.node_21256 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2902 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p5257 p3130 p5391 p8463 p4976 p13951 p16778 p17122 p4983 p17163 p4979 p20829 p17159 p20426 p20126 p17110 p17065 p17053 p20096 p17131 p17108 p17294 p16943 p17058 p17079 p17064 p17067 p17080 p17072 p17074 p17069 p20461 p20836 p20653 p17078 p17136 p17087 p17083 p21244 p17055 p17093 p17091 p17098 p17106 p16885 p21245 p17141 p17100 p19610 p4981 p17102 p5008 p17009 p16058 p16689 p17096 p17115 p17758 p17124 p17111 p19665 p17113 p17117 p20467 p17120 p4999 p17133 p17874 p17104 p17127 p17089 p20470 p253 p17020 p20274 p21142 p16729 p17050 p17138 p17060 p4989 p17172
theorem n21258 (_v : Vars) (_q : Query _v)  : (e21257 _v) := by
  by_contra hc
  change ¬ ((¬ (e7814 _v)) ∨ (e2733 _v) ∨ (¬ (e4546 _v)) ∨ (¬ (e4419 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e5100 _v)) ∨ (¬ (e3158 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4813 _v))) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h191 : (e191 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h3158 : (e3158 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4139 : (e4139 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h4260 : (e4260 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))
  have h4419 : (e4419 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4546 : (e4546 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))
  have h4675 : (e4675 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn)))))))))))))))))))
  have h4838 : (e4838 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))
  have h5100 : (e5100 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h6750 : (e6750 _v) := (fun hn => hc (Or.inr (Or.inl hn)))
  have h7814 : (e7814 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have p21243 := n21243 _v _q h51 h91 h191 h3152 h3158 h3937 h4139 h4260 h4306 h4419 h4546 h4653 h4675 h4787 h4813 h4838 h5100 h6750 h7814
  exact p21243
end
end Assembly
