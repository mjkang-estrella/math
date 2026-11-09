import Dag243
import generated.th_lemma_32
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n21064 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2242 : (e2242 _v)) (h3152 : (e3152 _v)) (h4096 : (e4096 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6600 : (e6600 _v)) (h6776 : (e6776 _v)) (h8038 : (e8038 _v)) : (e7489 _v) := by
  have p10893 := n10893 _v _q 
  have p21018 := n21018 _v _q h51 h91 h191 h2242 h3152 h4096 h4306 h4653 h4787 h4813 h4838 h6600 h6776 h8038
  have p21035 := n21035 _v _q h51 h91 h191 h2242 h3152 h4096 h4306 h4653 h4787 h4813 h4838 h6600 h6776 h8038
  have p21047 := n21047 _v _q h51 h91 h191 h2242 h3152 h4096 h4306 h4653 h4787 h4813 h4838 h6600 h6776 h8038
  have p16913 := n16913 _v _q 
  have p17147 := n17147 _v _q 
  have p15907 := n15907 _v _q h6600
  have p15956 := n15956 _v _q h6776
  have p20976 := n20976 _v _q h51 h91 h191 h2242 h3152 h4096 h4306 h4653 h4787 h4813 h4838 h6600 h6776 h8038
  have p17104 := n17104 _v _q 
  have p17874 := n17874 _v _q 
  have p17127 := n17127 _v _q 
  have p17089 := n17089 _v _q 
  have p4998 := n4998 _v _q h3152
  have p8553 := n8553 _v _q h2242
  have p13951 := n13951 _v _q 
  have p15209 := n15209 _v _q h8038
  have p253 := n253 _v _q h191
  have p15946 := n15946 _v _q h2242
  have p17020 := n17020 _v _q 
  have p8439 := n8439 _v _q h6600
  have p17138 := n17138 _v _q h4306
  have p20274 := n20274 _v _q 
  have p17060 := n17060 _v _q h4653
  have p20470 := n20470 _v _q 
  have p4989 := n4989 _v _q h4838
  have p17050 := n17050 _v _q 
  have p16778 := n16778 _v _q 
  have p17122 := n17122 _v _q 
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p20829 := n20829 _v _q 
  have p15775 := n15775 _v _q h2242
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
  have p15949 := n15949 _v _q h2242
  have p20838 := n20838 _v _q h2242
  have p17141 := n17141 _v _q 
  have p17100 := n17100 _v _q 
  have p19610 := n19610 _v _q 
  have p17102 := n17102 _v _q 
  have p5008 := n5008 _v _q h4787
  have p15952 := n15952 _v _q h2242
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
  have p5001 := n5001 _v _q h4096
  have p12927 := n12927 _v _q h2242
  have p20940 := n20940 _v _q h51 h91 h191 h2242 h3152 h4096 h4306 h4653 h4787 h4813 h4838 h6600 h6776 h8038
  exact FloorCertificate.node_21064 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2883 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4541 _v) (e4808 _v) p10893 p21018 p21035 p21047 p16913 p17147 p15907 p15956 p20976 p17104 p17874 p17127 p17089 p4998 p8553 p13951 p15209 p253 p15946 p17020 p8439 p17138 p20274 p17060 p20470 p4989 p17050 p16778 p17122 p4983 p16729 p20829 p15775 p20426 p20126 p17110 p17053 p20096 p17131 p17108 p17294 p16943 p17058 p17064 p17067 p17080 p17072 p17074 p17069 p20461 p20836 p20653 p17078 p17136 p17087 p17083 p17055 p17093 p17091 p17098 p17106 p15949 p20838 p17141 p17100 p19610 p17102 p5008 p15952 p17096 p17115 p17758 p17124 p17111 p19665 p17113 p17117 p20467 p17120 p4999 p17133 p5001 p12927 p20940
theorem n21065 (_v : Vars) (_q : Query _v) (h225 : (e225 _v)) (h4260 : (e4260 _v)) (h4813 : (e4813 _v)) (h6423 : (e6423 _v)) : (e7921 _v) := by
  have p16347 := n16347 _v _q 
  have p21049 := n21049 _v _q h225 h4260 h4813 h6423
  change (e7921 _v) ∨ (e4419 _v) at p16347
  change (¬ (e4419 _v)) at p21049
  rcases p16347 with hlit | hlit
  · exact hlit
  · exact (False.elim (p21049 hlit))
theorem n21066 (_v : Vars) (_q : Query _v) (h225 : (e225 _v)) (h4260 : (e4260 _v)) (h4813 : (e4813 _v)) (h6423 : (e6423 _v)) : (e6772 _v) := by
  have p14855 := n14855 _v _q 
  have p21065 := n21065 _v _q h225 h4260 h4813 h6423
  change (¬ (e2787 _v)) ∨ (¬ (e7921 _v)) at p14855
  rcases p14855 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p21065))
theorem n21067 (_v : Vars) (_q : Query _v) (h225 : (e225 _v)) (h4260 : (e4260 _v)) (h4813 : (e4813 _v)) (h6423 : (e6423 _v)) : (e7945 _v) := by
  have p15228 := n15228 _v _q 
  have p21066 := n21066 _v _q h225 h4260 h4813 h6423
  change (e2787 _v) ∨ (¬ (e7944 _v)) at p15228
  change (¬ (e2787 _v)) at p21066
  rcases p15228 with hlit | hlit
  · exact (False.elim (p21066 hlit))
  · exact hlit
theorem n21068 (_v : Vars) (_q : Query _v) (h4260 : (e4260 _v)) (h6423 : (e6423 _v)) : (e7754 _v) := by
  have p14942 := n14942 _v _q 
  have p21050 := n21050 _v _q h4260 h6423
  change (e2132 _v) ∨ (¬ (e7753 _v)) at p14942
  change (¬ (e2132 _v)) at p21050
  rcases p14942 with hlit | hlit
  · exact (False.elim (p21050 hlit))
  · exact hlit
theorem n21069 (_v : Vars) (_q : Query _v) (h4260 : (e4260 _v)) (h6423 : (e6423 _v)) : (e7749 _v) := by
  have p14941 := n14941 _v _q 
  have p21068 := n21068 _v _q h4260 h6423
  change (e7753 _v) ∨ (e7749 _v) at p14941
  change (¬ (e7753 _v)) at p21068
  rcases p14941 with hlit | hlit
  · exact (False.elim (p21068 hlit))
  · exact hlit
theorem n21070 (_v : Vars) (_q : Query _v) (h4260 : (e4260 _v)) (h6423 : (e6423 _v)) : (e5105 _v) := by
  have p15204 := n15204 _v _q 
  have p21052 := n21052 _v _q h4260 h6423
  change (e13 _v) ∨ (¬ (e5104 _v)) at p15204
  change (¬ (e13 _v)) at p21052
  rcases p15204 with hlit | hlit
  · exact (False.elim (p21052 hlit))
  · exact hlit
theorem n21071 (_v : Vars) (_q : Query _v) (h4260 : (e4260 _v)) (h6423 : (e6423 _v)) : (e5100 _v) := by
  have p15319 := n15319 _v _q 
  have p21070 := n21070 _v _q h4260 h6423
  change (e5104 _v) ∨ (e5100 _v) at p15319
  change (¬ (e5104 _v)) at p21070
  rcases p15319 with hlit | hlit
  · exact (False.elim (p21070 hlit))
  · exact hlit
theorem n21072 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2468 : (e2468 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) : (e2733 _v) := by
  have p21054 := n21054 _v _q 
  have p8438 := n8438 _v _q h2468
  have p4999 := n4999 _v _q h91
  have p253 := n253 _v _q h191
  have p16729 := n16729 _v _q h51
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4989 := n4989 _v _q h4838
  have p4983 := n4983 _v _q h4813
  change (e2733 _v) ∨ (¬ (e2468 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4813 _v)) at p21054
  rcases p21054 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p8438))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p253))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p4989))
  · exact (False.elim (hlit p4983))
theorem n21073 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2468 : (e2468 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e2733 _v) := by
  have p21054 := n21054 _v _q 
  have p8438 := n8438 _v _q h2468
  have p4999 := n4999 _v _q h91
  have p16705 := n16705 _v _q h2529
  have p16729 := n16729 _v _q h51
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p16572 := n16572 _v _q h2529
  have p4983 := n4983 _v _q h4813
  change (e2733 _v) ∨ (¬ (e2468 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4813 _v)) at p21054
  rcases p21054 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p8438))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p16705))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p16572))
  · exact (False.elim (hlit p4983))
theorem n21074 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2468 : (e2468 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e4109 _v) := by
  have p14689 := n14689 _v _q 
  have p21073 := n21073 _v _q h51 h91 h2468 h2529 h4306 h4653 h4813
  change (¬ (e2733 _v)) ∨ (¬ (e4108 _v)) at p14689
  rcases p14689 with hlit | hlit
  · exact (False.elim (hlit p21073))
  · exact hlit
theorem n21076 (_v : Vars) (_q : Query _v)  : (e21075 _v) := by
  by_contra hc
  change ¬ ((¬ (e4419 _v)) ∨ (¬ (e2296 _v)) ∨ (e2781 _v) ∨ (¬ (e191 _v)) ∨ (¬ (e4567 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4679 _v)) ∨ (¬ (e3158 _v)) ∨ (¬ (e4439 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4459 _v)) ∨ (¬ (e91 _v))) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))))))))))))
  have h191 : (e191 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h2296 : (e2296 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h3158 : (e3158 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h4419 : (e4419 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h4439 : (e4439 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h4459 : (e4459 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h4567 : (e4567 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h4679 : (e4679 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h4838 : (e4838 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h6776 : (e6776 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have p21057 := n21057 _v _q h51 h91 h191 h2296 h3158 h4306 h4419 h4439 h4459 h4567 h4653 h4679 h4787 h4813 h4838 h6776
  exact p21057
theorem n21077 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2242 : (e2242 _v)) (h2733 : (e2733 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6549 : (e6549 _v)) (h6600 : (e6600 _v)) (h6776 : (e6776 _v)) : (e7943 _v) := by
  have p21059 := n21059 _v _q 
  have p15907 := n15907 _v _q h6600
  have p15986 := n15986 _v _q h2733
  have p4999 := n4999 _v _q h91
  have p253 := n253 _v _q h191
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4989 := n4989 _v _q h4838
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p5008 := n5008 _v _q h4787
  have p8553 := n8553 _v _q h2242
  have p8601 := n8601 _v _q h6776
  have p8544 := n8544 _v _q h6549
  have p16093 := n16093 _v _q h2733 h6600
  change (¬ (e7935 _v)) ∨ (e2781 _v) ∨ (¬ (e4101 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e2242 _v)) ∨ (¬ (e3937 _v)) ∨ (e2296 _v) ∨ (e2303 _v) at p21059
  change (¬ (e2781 _v)) at p8601
  change (¬ (e2296 _v)) at p8544
  change (¬ (e2303 _v)) at p16093
  rcases p21059 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (p8601 hlit))
  · exact (False.elim (hlit p15986))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p253))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p4989))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p8553))
  · exact (False.elim (hlit p15907))
  · exact (False.elim (p8544 hlit))
  · exact (False.elim (p16093 hlit))
theorem n21078 (_v : Vars) (_q : Query _v) (h4260 : (e4260 _v)) (h5108 : (e5108 _v)) (h6423 : (e6423 _v)) : (e7921 _v) := by
  have p16347 := n16347 _v _q 
  have p21060 := n21060 _v _q h4260 h5108 h6423
  change (e7921 _v) ∨ (e4419 _v) at p16347
  change (¬ (e4419 _v)) at p21060
  rcases p16347 with hlit | hlit
  · exact hlit
  · exact (False.elim (p21060 hlit))
theorem n21079 (_v : Vars) (_q : Query _v) (h4260 : (e4260 _v)) (h5108 : (e5108 _v)) (h6423 : (e6423 _v)) : (e6772 _v) := by
  have p14855 := n14855 _v _q 
  have p21078 := n21078 _v _q h4260 h5108 h6423
  change (¬ (e2787 _v)) ∨ (¬ (e7921 _v)) at p14855
  rcases p14855 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p21078))
theorem n21080 (_v : Vars) (_q : Query _v) (h4260 : (e4260 _v)) (h5108 : (e5108 _v)) (h6423 : (e6423 _v)) : (e7945 _v) := by
  have p15228 := n15228 _v _q 
  have p21079 := n21079 _v _q h4260 h5108 h6423
  change (e2787 _v) ∨ (¬ (e7944 _v)) at p15228
  change (¬ (e2787 _v)) at p21079
  rcases p15228 with hlit | hlit
  · exact (False.elim (p21079 hlit))
  · exact hlit
theorem n21081 (_v : Vars) (_q : Query _v) (h4260 : (e4260 _v)) (h6423 : (e6423 _v)) : (e6724 _v) := by
  have p11461 := n11461 _v _q 
  have p21061 := n21061 _v _q h4260 h6423
  change (¬ (e2691 _v)) ∨ (e2740 _v) at p11461
  change (¬ (e2740 _v)) at p21061
  rcases p11461 with hlit | hlit
  · exact hlit
  · exact (False.elim (p21061 hlit))
theorem n21082 (_v : Vars) (_q : Query _v) (h4260 : (e4260 _v)) (h6423 : (e6423 _v)) : (e7517 _v) := by
  have p15196 := n15196 _v _q 
  have p21081 := n21081 _v _q h4260 h6423
  change (e2691 _v) ∨ (¬ (e7497 _v)) at p15196
  change (¬ (e2691 _v)) at p21081
  rcases p15196 with hlit | hlit
  · exact (False.elim (p21081 hlit))
  · exact hlit
theorem n21083 (_v : Vars) (_q : Query _v) (h4260 : (e4260 _v)) (h6423 : (e6423 _v)) : (e7493 _v) := by
  have p15195 := n15195 _v _q 
  have p21082 := n21082 _v _q h4260 h6423
  change (e7497 _v) ∨ (e7493 _v) at p15195
  change (¬ (e7497 _v)) at p21082
  rcases p15195 with hlit | hlit
  · exact (False.elim (p21082 hlit))
  · exact hlit
theorem n21085 (_v : Vars) (_q : Query _v)  : (e21084 _v) := by
  by_contra hc
  change ¬ ((e2475 _v) ∨ (¬ (e3152 _v)) ∨ (¬ (e2242 _v)) ∨ (¬ (e191 _v)) ∨ (e2402 _v) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e4096 _v)) ∨ (e2781 _v)) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h191 : (e191 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h2242 : (e2242 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h4096 : (e4096 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h4838 : (e4838 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h6600 : (e6600 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h6776 : (e6776 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))))))))))
  have h8038 : (e8038 _v) := (fun hn => hc (Or.inl hn))
  have p21064 := n21064 _v _q h51 h91 h191 h2242 h3152 h4096 h4306 h4653 h4787 h4813 h4838 h6600 h6776 h8038
  exact p21064
theorem n21086 (_v : Vars) (_q : Query _v) (h225 : (e225 _v)) (h4260 : (e4260 _v)) (h4813 : (e4813 _v)) (h6423 : (e6423 _v)) : (e7935 _v) := by
  have p15266 := n15266 _v _q 
  have p21067 := n21067 _v _q h225 h4260 h4813 h6423
  change (e7944 _v) ∨ (e7935 _v) at p15266
  change (¬ (e7944 _v)) at p21067
  rcases p15266 with hlit | hlit
  · exact (False.elim (p21067 hlit))
  · exact hlit
theorem n21087 (_v : Vars) (_q : Query _v) (h225 : (e225 _v)) (h4813 : (e4813 _v)) (h6423 : (e6423 _v)) : (e8045 _v) := by
  have p15206 := n15206 _v _q 
  have p20908 := n20908 _v _q h225 h4813 h6423
  change (e8049 _v) ∨ (e8045 _v) at p15206
  change (¬ (e8049 _v)) at p20908
  rcases p15206 with hlit | hlit
  · exact (False.elim (p20908 hlit))
  · exact hlit
theorem n21088 (_v : Vars) (_q : Query _v) (h4260 : (e4260 _v)) (h6423 : (e6423 _v)) : (e7814 _v) := by
  have p15221 := n15221 _v _q 
  have p21051 := n21051 _v _q h4260 h6423
  change (e7818 _v) ∨ (e7814 _v) at p15221
  change (¬ (e7818 _v)) at p21051
  rcases p15221 with hlit | hlit
  · exact (False.elim (p21051 hlit))
  · exact hlit
theorem n21089 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h225 : (e225 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6423 : (e6423 _v)) : (e2733 _v) := by
  have p21020 := n21020 _v _q 
  have p5007 := n5007 _v _q h225
  have p16396 := n16396 _v _q h6423
  have p16652 := n16652 _v _q h6423
  have p21040 := n21040 _v _q h4260 h6423
  have p16729 := n16729 _v _q h51
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p21086 := n21086 _v _q h225 h4260 h4813 h6423
  have p20906 := n20906 _v _q h225 h4813 h6423
  have p4983 := n4983 _v _q h4813
  have p21069 := n21069 _v _q h4260 h6423
  have p21087 := n21087 _v _q h225 h4813 h6423
  have p21088 := n21088 _v _q h4260 h6423
  have p16669 := n16669 _v _q h6423
  have p4981 := n4981 _v _q h4260
  have p16667 := n16667 _v _q h6423
  have p21071 := n21071 _v _q h4260 h6423
  have p16668 := n16668 _v _q h6423
  have p20910 := n20910 _v _q h225 h4813 h6423
  have p15379 := n15379 _v _q h6423
  have p16666 := n16666 _v _q h6423
  change (e2733 _v) ∨ (¬ (e225 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e2364 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e7935 _v)) ∨ (¬ (e8317 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e7749 _v)) ∨ (¬ (e8045 _v)) ∨ (¬ (e7814 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e5100 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e5145 _v)) ∨ (¬ (e4562 _v)) ∨ (¬ (e4787 _v)) at p21020
  rcases p21020 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p5007))
  · exact (False.elim (hlit p16396))
  · exact (False.elim (hlit p16652))
  · exact (False.elim (hlit p21040))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p21086))
  · exact (False.elim (hlit p20906))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p21069))
  · exact (False.elim (hlit p21087))
  · exact (False.elim (hlit p21088))
  · exact (False.elim (hlit p16669))
  · exact (False.elim (hlit p4981))
  · exact (False.elim (hlit p16667))
  · exact (False.elim (hlit p21071))
  · exact (False.elim (hlit p16668))
  · exact (False.elim (hlit p20910))
  · exact (False.elim (hlit p15379))
  · exact (False.elim (hlit p16666))
theorem n21090 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h225 : (e225 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6423 : (e6423 _v)) : (e4109 _v) := by
  have p14689 := n14689 _v _q 
  have p21089 := n21089 _v _q h51 h225 h4260 h4306 h4653 h4813 h6423
  change (¬ (e2733 _v)) ∨ (¬ (e4108 _v)) at p14689
  rcases p14689 with hlit | hlit
  · exact (False.elim (hlit p21089))
  · exact hlit
theorem n21091 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2468 : (e2468 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) : (e4109 _v) := by
  have p14689 := n14689 _v _q 
  have p21072 := n21072 _v _q h51 h91 h191 h2468 h4306 h4653 h4813 h4838
  change (¬ (e2733 _v)) ∨ (¬ (e4108 _v)) at p14689
  rcases p14689 with hlit | hlit
  · exact (False.elim (hlit p21072))
  · exact hlit
theorem n21092 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2468 : (e2468 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) : (e4101 _v) := by
  have p14929 := n14929 _v _q 
  have p21091 := n21091 _v _q h51 h91 h191 h2468 h4306 h4653 h4813 h4838
  change (e4108 _v) ∨ (e4101 _v) at p14929
  change (¬ (e4108 _v)) at p21091
  rcases p14929 with hlit | hlit
  · exact (False.elim (p21091 hlit))
  · exact hlit
theorem n21093 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2468 : (e2468 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e4101 _v) := by
  have p14929 := n14929 _v _q 
  have p21074 := n21074 _v _q h51 h91 h2468 h2529 h4306 h4653 h4813
  change (e4108 _v) ∨ (e4101 _v) at p14929
  change (¬ (e4108 _v)) at p21074
  rcases p14929 with hlit | hlit
  · exact (False.elim (p21074 hlit))
  · exact hlit
theorem n21094 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2296 : (e2296 _v)) (h2468 : (e2468 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e4269 _v) := by
  have p17758 := n17758 _v _q 
  have p17124 := n17124 _v _q 
  have p17111 := n17111 _v _q 
  have p15073 := n15073 _v _q h2468
  have p19665 := n19665 _v _q 
  have p258 := n258 _v _q 
  have p8438 := n8438 _v _q h2468
  have p17113 := n17113 _v _q 
  have p16067 := n16067 _v _q h2468
  have p17117 := n17117 _v _q 
  have p20467 := n20467 _v _q 
  have p17120 := n17120 _v _q 
  have p21093 := n21093 _v _q h51 h91 h2468 h2529 h4306 h4653 h4813
  have p4999 := n4999 _v _q h91
  have p16074 := n16074 _v _q h2468
  have p17133 := n17133 _v _q 
  have p20827 := n20827 _v _q 
  have p17104 := n17104 _v _q 
  have p17127 := n17127 _v _q 
  have p17089 := n17089 _v _q 
  have p20470 := n20470 _v _q 
  have p16705 := n16705 _v _q h2529
  have p17020 := n17020 _v _q 
  have p20274 := n20274 _v _q 
  have p15104 := n15104 _v _q h2468
  have p20855 := n20855 _v _q h2468
  have p16729 := n16729 _v _q h51
  have p17050 := n17050 _v _q 
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p16572 := n16572 _v _q h2529
  have p4983 := n4983 _v _q h4813
  have p16062 := n16062 _v _q h2468
  have p16859 := n16859 _v _q h2468
  have p16778 := n16778 _v _q 
  have p15100 := n15100 _v _q h2296
  have p20829 := n20829 _v _q 
  have p17108 := n17108 _v _q 
  have p20461 := n20461 _v _q 
  have p20426 := n20426 _v _q 
  have p20126 := n20126 _v _q 
  have p17110 := n17110 _v _q 
  have p17009 := n17009 _v _q 
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
  have p17102 := n17102 _v _q 
  have p17100 := n17100 _v _q 
  have p19610 := n19610 _v _q 
  have p17122 := n17122 _v _q 
  have p17096 := n17096 _v _q 
  have p17115 := n17115 _v _q 
  have p17874 := n17874 _v _q 
  have p17256 := n17256 _v _q 
  have p8583 := n8583 _v _q h2296
  have p13951 := n13951 _v _q 
  have p8548 := n8548 _v _q h2529
  exact FloorCertificate.node_21094 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2902 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e4215 _v) (e4808 _v) p17758 p17124 p17111 p15073 p19665 p258 p8438 p17113 p16067 p17117 p20467 p17120 p21093 p4999 p16074 p17133 p20827 p17104 p17127 p17089 p20470 p16705 p17020 p20274 p15104 p20855 p16729 p17050 p17138 p17060 p16572 p4983 p16062 p16859 p16778 p15100 p20829 p17108 p20461 p20426 p20126 p17110 p17009 p17053 p17131 p20096 p17058 p17294 p16943 p17064 p17067 p17069 p17080 p17072 p17083 p17074 p20836 p17078 p20653 p17087 p17136 p17055 p17091 p17093 p17141 p17098 p17106 p17102 p17100 p19610 p17122 p17096 p17115 p17874 p17256 p8583 p13951 p8548
theorem n21095 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2242 : (e2242 _v)) (h2733 : (e2733 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6549 : (e6549 _v)) (h6600 : (e6600 _v)) (h6776 : (e6776 _v)) : (e7944 _v) := by
  have p15266 := n15266 _v _q 
  have p21077 := n21077 _v _q h51 h91 h191 h2242 h2733 h4306 h4653 h4787 h4813 h4838 h6549 h6600 h6776
  change (e7944 _v) ∨ (e7935 _v) at p15266
  change (¬ (e7935 _v)) at p21077
  rcases p15266 with hlit | hlit
  · exact hlit
  · exact (False.elim (p21077 hlit))
theorem n21096 (_v : Vars) (_q : Query _v) (h4260 : (e4260 _v)) (h5108 : (e5108 _v)) (h6423 : (e6423 _v)) : (e7935 _v) := by
  have p15266 := n15266 _v _q 
  have p21080 := n21080 _v _q h4260 h5108 h6423
  change (e7944 _v) ∨ (e7935 _v) at p15266
  change (¬ (e7944 _v)) at p21080
  rcases p15266 with hlit | hlit
  · exact (False.elim (p21080 hlit))
  · exact hlit
theorem n21097 (_v : Vars) (_q : Query _v) (h4260 : (e4260 _v)) (h5108 : (e5108 _v)) (h6423 : (e6423 _v)) : (e2585 _v) := by
  have p20931 := n20931 _v _q 
  have p21096 := n21096 _v _q h4260 h5108 h6423
  have p21040 := n21040 _v _q h4260 h6423
  have p11366 := n11366 _v _q h5108
  have p16659 := n16659 _v _q h6423
  have p21069 := n21069 _v _q h4260 h6423
  have p21088 := n21088 _v _q h4260 h6423
  have p16660 := n16660 _v _q h6423
  have p4981 := n4981 _v _q h4260
  have p21083 := n21083 _v _q h4260 h6423
  have p15967 := n15967 _v _q h6423
  have p21071 := n21071 _v _q h4260 h6423
  have p16658 := n16658 _v _q h6423
  have p15379 := n15379 _v _q h6423
  have p15964 := n15964 _v _q h6423
  have p16396 := n16396 _v _q h6423
  have p16657 := n16657 _v _q h6423
  have p20932 := n20932 _v _q h5108 h6423
  change (e2585 _v) ∨ (¬ (e2364 _v)) ∨ (¬ (e7935 _v)) ∨ (e48 _v) ∨ (¬ (e4813 _v)) ∨ (¬ (e7749 _v)) ∨ (¬ (e7814 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e7493 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e5100 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e4562 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e3937 _v)) ∨ (e79 _v) at p20931
  change (¬ (e48 _v)) at p11366
  change (¬ (e79 _v)) at p20932
  rcases p20931 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p21040))
  · exact (False.elim (hlit p21096))
  · exact (False.elim (p11366 hlit))
  · exact (False.elim (hlit p16659))
  · exact (False.elim (hlit p21069))
  · exact (False.elim (hlit p21088))
  · exact (False.elim (hlit p16660))
  · exact (False.elim (hlit p4981))
  · exact (False.elim (hlit p21083))
  · exact (False.elim (hlit p15967))
  · exact (False.elim (hlit p21071))
  · exact (False.elim (hlit p16658))
  · exact (False.elim (hlit p15379))
  · exact (False.elim (hlit p15964))
  · exact (False.elim (hlit p16396))
  · exact (False.elim (hlit p16657))
  · exact (False.elim (p20932 hlit))
theorem n21098 (_v : Vars) (_q : Query _v) (h4260 : (e4260 _v)) (h5108 : (e5108 _v)) (h6423 : (e6423 _v)) : (e4314 _v) := by
  have p14704 := n14704 _v _q 
  have p21097 := n21097 _v _q h4260 h5108 h6423
  change (¬ (e2585 _v)) ∨ (¬ (e4313 _v)) at p14704
  rcases p14704 with hlit | hlit
  · exact (False.elim (hlit p21097))
  · exact hlit
theorem n21099 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2242 : (e2242 _v)) (h3152 : (e3152 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6600 : (e6600 _v)) (h6750 : (e6750 _v)) (h6776 : (e6776 _v)) : (e2475 _v) := by
  have p21085 := n21085 _v _q 
  have p8439 := n8439 _v _q h6600
  have p8553 := n8553 _v _q h2242
  have p253 := n253 _v _q h191
  have p4998 := n4998 _v _q h3152
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4989 := n4989 _v _q h4838
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p5008 := n5008 _v _q h4787
  have p4999 := n4999 _v _q h91
  have p15940 := n15940 _v _q h6750
  have p8601 := n8601 _v _q h6776
  change (e2475 _v) ∨ (¬ (e3152 _v)) ∨ (¬ (e2242 _v)) ∨ (¬ (e191 _v)) ∨ (e2402 _v) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e4096 _v)) ∨ (e2781 _v) at p21085
  change (¬ (e2402 _v)) at p8439
  change (¬ (e2781 _v)) at p8601
  rcases p21085 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p8553))
  · exact (False.elim (hlit p253))
  · exact (False.elim (p8439 hlit))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p4989))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p15940))
  · exact (False.elim (p8601 hlit))
theorem n21100 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h225 : (e225 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6423 : (e6423 _v)) : (e4101 _v) := by
  have p14929 := n14929 _v _q 
  have p21090 := n21090 _v _q h51 h225 h4260 h4306 h4653 h4813 h6423
  change (e4108 _v) ∨ (e4101 _v) at p14929
  change (¬ (e4108 _v)) at p21090
  rcases p14929 with hlit | hlit
  · exact (False.elim (p21090 hlit))
  · exact hlit
theorem n21101 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h225 : (e225 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6423 : (e6423 _v)) : (e7489 _v) := by
  have p16992 := n16992 _v _q 
  have p17953 := n17953 _v _q 
  have p8663 := n8663 _v _q 
  have p17133 := n17133 _v _q 
  have p8452 := n8452 _v _q h6423
  have p17089 := n17089 _v _q 
  have p20470 := n20470 _v _q 
  have p21100 := n21100 _v _q h51 h225 h4260 h4306 h4653 h4813 h6423
  have p16396 := n16396 _v _q h6423
  have p16652 := n16652 _v _q h6423
  have p5257 := n5257 _v _q 
  have p16576 := n16576 _v _q 
  have p17147 := n17147 _v _q 
  have p16394 := n16394 _v _q 
  have p16729 := n16729 _v _q h51
  have p17256 := n17256 _v _q 
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p21086 := n21086 _v _q h225 h4260 h4813 h6423
  have p13951 := n13951 _v _q 
  have p20906 := n20906 _v _q h225 h4813 h6423
  have p4983 := n4983 _v _q h4813
  have p21069 := n21069 _v _q h4260 h6423
  have p21087 := n21087 _v _q h225 h4813 h6423
  have p21088 := n21088 _v _q h4260 h6423
  have p16669 := n16669 _v _q h6423
  have p20829 := n20829 _v _q 
  have p17108 := n17108 _v _q 
  have p20461 := n20461 _v _q 
  have p4981 := n4981 _v _q h4260
  have p20426 := n20426 _v _q 
  have p16667 := n16667 _v _q h6423
  have p20126 := n20126 _v _q 
  have p17110 := n17110 _v _q 
  have p17009 := n17009 _v _q 
  have p17053 := n17053 _v _q 
  have p17131 := n17131 _v _q 
  have p21071 := n21071 _v _q h4260 h6423
  have p20096 := n20096 _v _q 
  have p17058 := n17058 _v _q 
  have p17294 := n17294 _v _q 
  have p16943 := n16943 _v _q 
  have p17064 := n17064 _v _q 
  have p16668 := n16668 _v _q h6423
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
  have p17102 := n17102 _v _q 
  have p17100 := n17100 _v _q 
  have p19610 := n19610 _v _q 
  have p16929 := n16929 _v _q 
  have p17122 := n17122 _v _q 
  have p17096 := n17096 _v _q 
  have p20910 := n20910 _v _q h225 h4813 h6423
  have p15379 := n15379 _v _q h6423
  have p17758 := n17758 _v _q 
  have p16666 := n16666 _v _q h6423
  have p19665 := n19665 _v _q 
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
  have p20274 := n20274 _v _q 
  have p5391 := n5391 _v _q 
  have p5255 := n5255 _v _q 
  exact FloorCertificate.node_21101 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2834 _v) (e2849 _v) (e2863 _v) (e2877 _v) (e2883 _v) (e2902 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p16992 p17953 p8663 p17133 p8452 p17089 p20470 p21100 p16396 p16652 p5257 p16576 p17147 p16394 p16729 p17256 p17138 p17060 p21086 p13951 p20906 p4983 p21069 p21087 p21088 p16669 p20829 p17108 p20461 p4981 p20426 p16667 p20126 p17110 p17009 p17053 p17131 p21071 p20096 p17058 p17294 p16943 p17064 p16668 p17067 p17069 p17080 p17072 p17083 p17074 p20836 p17078 p20653 p17087 p17136 p17055 p17091 p17093 p17141 p17098 p17106 p17102 p17100 p19610 p16929 p17122 p17096 p20910 p15379 p17758 p16666 p19665 p17115 p17120 p17111 p17124 p17050 p16778 p17113 p17117 p20467 p17104 p17874 p17127 p20274 p5391 p5255
theorem n21102 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2468 : (e2468 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) : (e6746 _v) := by
  have p258 := n258 _v _q 
  have p21072 := n21072 _v _q h51 h91 h191 h2468 h4306 h4653 h4813 h4838
  exact FloorCertificate.node_21102 (e2 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p258 p21072
theorem n21103 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2468 : (e2468 _v)) (h3152 : (e3152 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6776 : (e6776 _v)) : (e7943 _v) := by
  have p13951 := n13951 _v _q 
  have p19665 := n19665 _v _q 
  have p17124 := n17124 _v _q 
  have p21092 := n21092 _v _q h51 h91 h191 h2468 h4306 h4653 h4813 h4838
  have p8601 := n8601 _v _q h6776
  have p16701 := n16701 _v _q h2468 h6776
  have p17113 := n17113 _v _q 
  have p16067 := n16067 _v _q h2468
  have p17117 := n17117 _v _q 
  have p20467 := n20467 _v _q 
  have p17111 := n17111 _v _q 
  have p15073 := n15073 _v _q h2468
  have p4999 := n4999 _v _q h91
  have p16074 := n16074 _v _q h2468
  have p17133 := n17133 _v _q 
  have p17115 := n17115 _v _q 
  have p17104 := n17104 _v _q 
  have p17127 := n17127 _v _q 
  have p17089 := n17089 _v _q 
  have p20470 := n20470 _v _q 
  have p253 := n253 _v _q h191
  have p17020 := n17020 _v _q 
  have p20274 := n20274 _v _q 
  have p15104 := n15104 _v _q h2468
  have p20855 := n20855 _v _q h2468
  have p16729 := n16729 _v _q h51
  have p17050 := n17050 _v _q 
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4989 := n4989 _v _q h4838
  have p4983 := n4983 _v _q h4813
  have p16062 := n16062 _v _q h2468
  have p16859 := n16859 _v _q h2468
  have p16778 := n16778 _v _q 
  have p8438 := n8438 _v _q h2468
  have p20829 := n20829 _v _q 
  have p17108 := n17108 _v _q 
  have p20461 := n20461 _v _q 
  have p15956 := n15956 _v _q h6776
  have p20426 := n20426 _v _q 
  have p20126 := n20126 _v _q 
  have p17110 := n17110 _v _q 
  have p17009 := n17009 _v _q 
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
  have p17102 := n17102 _v _q 
  have p17100 := n17100 _v _q 
  have p19610 := n19610 _v _q 
  have p17122 := n17122 _v _q 
  have p17096 := n17096 _v _q 
  have p17120 := n17120 _v _q 
  have p17874 := n17874 _v _q 
  have p17758 := n17758 _v _q 
  have p21102 := n21102 _v _q h51 h91 h191 h2468 h4306 h4653 h4813 h4838
  have p5391 := n5391 _v _q 
  have p4998 := n4998 _v _q h3152
  have p16876 := n16876 _v _q h2468 h6776
  exact FloorCertificate.node_21103 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2902 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4808 _v) p13951 p19665 p17124 p21092 p8601 p16701 p17113 p16067 p17117 p20467 p17111 p15073 p4999 p16074 p17133 p17115 p17104 p17127 p17089 p20470 p253 p17020 p20274 p15104 p20855 p16729 p17050 p17138 p17060 p4989 p4983 p16062 p16859 p16778 p8438 p20829 p17108 p20461 p15956 p20426 p20126 p17110 p17009 p17053 p17131 p20096 p17058 p17294 p16943 p17064 p17067 p17069 p17080 p17072 p17083 p17074 p20836 p17078 p20653 p17087 p17136 p17055 p17091 p17093 p17141 p17098 p17106 p17102 p17100 p19610 p17122 p17096 p17120 p17874 p17758 p21102 p5391 p4998 p16876
theorem n21104 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2468 : (e2468 _v)) (h3152 : (e3152 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6776 : (e6776 _v)) : (e4420 _v) := by
  have p17124 := n17124 _v _q 
  have p15073 := n15073 _v _q h2468
  have p21092 := n21092 _v _q h51 h91 h191 h2468 h4306 h4653 h4813 h4838
  have p17120 := n17120 _v _q 
  have p13951 := n13951 _v _q 
  have p17115 := n17115 _v _q 
  have p17113 := n17113 _v _q 
  have p16067 := n16067 _v _q h2468
  have p17117 := n17117 _v _q 
  have p20467 := n20467 _v _q 
  have p8438 := n8438 _v _q h2468
  have p16876 := n16876 _v _q h2468 h6776
  have p4999 := n4999 _v _q h91
  have p16074 := n16074 _v _q h2468
  have p17133 := n17133 _v _q 
  have p258 := n258 _v _q 
  have p17104 := n17104 _v _q 
  have p17127 := n17127 _v _q 
  have p17089 := n17089 _v _q 
  have p20470 := n20470 _v _q 
  have p253 := n253 _v _q h191
  have p17020 := n17020 _v _q 
  have p20274 := n20274 _v _q 
  have p15104 := n15104 _v _q h2468
  have p20855 := n20855 _v _q h2468
  have p16729 := n16729 _v _q h51
  have p17050 := n17050 _v _q 
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4989 := n4989 _v _q h4838
  have p4983 := n4983 _v _q h4813
  have p16062 := n16062 _v _q h2468
  have p16859 := n16859 _v _q h2468
  have p16778 := n16778 _v _q 
  have p17111 := n17111 _v _q 
  have p20829 := n20829 _v _q 
  have p17108 := n17108 _v _q 
  have p20461 := n20461 _v _q 
  have p15956 := n15956 _v _q h6776
  have p20426 := n20426 _v _q 
  have p20126 := n20126 _v _q 
  have p17110 := n17110 _v _q 
  have p17009 := n17009 _v _q 
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
  have p17102 := n17102 _v _q 
  have p17100 := n17100 _v _q 
  have p19610 := n19610 _v _q 
  have p17122 := n17122 _v _q 
  have p17096 := n17096 _v _q 
  have p19665 := n19665 _v _q 
  have p17874 := n17874 _v _q 
  have p17758 := n17758 _v _q 
  have p21102 := n21102 _v _q h51 h91 h191 h2468 h4306 h4653 h4813 h4838
  have p5391 := n5391 _v _q 
  have p8601 := n8601 _v _q h6776
  have p4998 := n4998 _v _q h3152
  have p16701 := n16701 _v _q h2468 h6776
  exact FloorCertificate.node_21104 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2902 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4808 _v) p17124 p15073 p21092 p17120 p13951 p17115 p17113 p16067 p17117 p20467 p8438 p16876 p4999 p16074 p17133 p258 p17104 p17127 p17089 p20470 p253 p17020 p20274 p15104 p20855 p16729 p17050 p17138 p17060 p4989 p4983 p16062 p16859 p16778 p17111 p20829 p17108 p20461 p15956 p20426 p20126 p17110 p17009 p17053 p17131 p20096 p17058 p17294 p16943 p17064 p17067 p17069 p17080 p17072 p17083 p17074 p20836 p17078 p20653 p17087 p17136 p17055 p17091 p17093 p17141 p17098 p17106 p17102 p17100 p19610 p17122 p17096 p19665 p17874 p17758 p21102 p5391 p8601 p4998 p16701
theorem n21105 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2296 : (e2296 _v)) (h2468 : (e2468 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e4270 _v) := by
  have p14966 := n14966 _v _q 
  have p21094 := n21094 _v _q h51 h91 h2296 h2468 h2529 h4306 h4653 h4813
  change (e4270 _v) ∨ (e4264 _v) at p14966
  change (¬ (e4264 _v)) at p21094
  rcases p14966 with hlit | hlit
  · exact hlit
  · exact (False.elim (p21094 hlit))
theorem n21106 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2242 : (e2242 _v)) (h2733 : (e2733 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6549 : (e6549 _v)) (h6600 : (e6600 _v)) (h6776 : (e6776 _v)) : (e2787 _v) := by
  have p15228 := n15228 _v _q 
  have p21095 := n21095 _v _q h51 h91 h191 h2242 h2733 h4306 h4653 h4787 h4813 h4838 h6549 h6600 h6776
  change (e2787 _v) ∨ (¬ (e7944 _v)) at p15228
  rcases p15228 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p21095))
theorem n21107 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2242 : (e2242 _v)) (h2733 : (e2733 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6549 : (e6549 _v)) (h6600 : (e6600 _v)) (h6776 : (e6776 _v)) : (e7927 _v) := by
  have p14855 := n14855 _v _q 
  have p21106 := n21106 _v _q h51 h91 h191 h2242 h2733 h4306 h4653 h4787 h4813 h4838 h6549 h6600 h6776
  change (¬ (e2787 _v)) ∨ (¬ (e7921 _v)) at p14855
  rcases p14855 with hlit | hlit
  · exact (False.elim (hlit p21106))
  · exact hlit
theorem n21108 (_v : Vars) (_q : Query _v) (h4260 : (e4260 _v)) (h5108 : (e5108 _v)) (h6423 : (e6423 _v)) : (e4306 _v) := by
  have p14984 := n14984 _v _q 
  have p21098 := n21098 _v _q h4260 h5108 h6423
  change (e4313 _v) ∨ (e4306 _v) at p14984
  change (¬ (e4313 _v)) at p21098
  rcases p14984 with hlit | hlit
  · exact (False.elim (p21098 hlit))
  · exact hlit
theorem n21109 (_v : Vars) (_q : Query _v) (h5108 : (e5108 _v)) (h6423 : (e6423 _v)) : (e8045 _v) := by
  have p15206 := n15206 _v _q 
  have p20935 := n20935 _v _q h5108 h6423
  change (e8049 _v) ∨ (e8045 _v) at p15206
  change (¬ (e8049 _v)) at p20935
  rcases p15206 with hlit | hlit
  · exact (False.elim (p20935 hlit))
  · exact hlit
theorem n21110 (_v : Vars) (_q : Query _v) (h4260 : (e4260 _v)) (h5108 : (e5108 _v)) (h6423 : (e6423 _v)) : (e192 _v) := by
  have p8663 := n8663 _v _q 
  have p21040 := n21040 _v _q h4260 h6423
  have p17256 := n17256 _v _q 
  have p21108 := n21108 _v _q h4260 h5108 h6423
  have p21063 := n21063 _v _q h4260 h6423
  have p21096 := n21096 _v _q h4260 h5108 h6423
  have p5257 := n5257 _v _q 
  have p15650 := n15650 _v _q h5108
  have p13951 := n13951 _v _q 
  have p20933 := n20933 _v _q h5108 h6423
  have p11366 := n11366 _v _q h5108
  have p16659 := n16659 _v _q h6423
  have p21069 := n21069 _v _q h4260 h6423
  have p21109 := n21109 _v _q h5108 h6423
  have p21088 := n21088 _v _q h4260 h6423
  have p16660 := n16660 _v _q h6423
  have p20829 := n20829 _v _q 
  have p17108 := n17108 _v _q 
  have p20461 := n20461 _v _q 
  have p4981 := n4981 _v _q h4260
  have p21083 := n21083 _v _q h4260 h6423
  have p20426 := n20426 _v _q 
  have p15967 := n15967 _v _q h6423
  have p20126 := n20126 _v _q 
  have p17110 := n17110 _v _q 
  have p17009 := n17009 _v _q 
  have p17053 := n17053 _v _q 
  have p17131 := n17131 _v _q 
  have p21071 := n21071 _v _q h4260 h6423
  have p20096 := n20096 _v _q 
  have p16892 := n16892 _v _q h5108
  have p17058 := n17058 _v _q 
  have p17294 := n17294 _v _q 
  have p16943 := n16943 _v _q 
  have p17064 := n17064 _v _q 
  have p16658 := n16658 _v _q h6423
  have p16748 := n16748 _v _q h5108
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
  have p17102 := n17102 _v _q 
  have p17100 := n17100 _v _q 
  have p19610 := n19610 _v _q 
  have p16929 := n16929 _v _q 
  have p17122 := n17122 _v _q 
  have p17096 := n17096 _v _q 
  have p20937 := n20937 _v _q h5108 h6423
  have p15379 := n15379 _v _q h6423
  have p17758 := n17758 _v _q 
  have p15964 := n15964 _v _q h6423
  have p19665 := n19665 _v _q 
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
  have p20274 := n20274 _v _q 
  have p20470 := n20470 _v _q 
  have p17133 := n17133 _v _q 
  have p17089 := n17089 _v _q 
  have p16394 := n16394 _v _q 
  have p16396 := n16396 _v _q h6423
  have p16576 := n16576 _v _q 
  have p16657 := n16657 _v _q h6423
  have p17147 := n17147 _v _q 
  have p16977 := n16977 _v _q 
  have p20932 := n20932 _v _q h5108 h6423
  exact FloorCertificate.node_21110 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e61 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2834 _v) (e2849 _v) (e2863 _v) (e2877 _v) (e2883 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p8663 p21040 p17256 p21108 p21063 p21096 p5257 p15650 p13951 p20933 p11366 p16659 p21069 p21109 p21088 p16660 p20829 p17108 p20461 p4981 p21083 p20426 p15967 p20126 p17110 p17009 p17053 p17131 p21071 p20096 p16892 p17058 p17294 p16943 p17064 p16658 p16748 p17067 p17069 p17080 p17072 p17083 p17074 p20836 p17078 p20653 p17087 p17136 p17055 p17091 p17093 p17141 p17098 p17106 p17102 p17100 p19610 p16929 p17122 p17096 p20937 p15379 p17758 p15964 p19665 p17115 p17120 p17111 p17124 p17050 p16778 p17113 p17117 p20467 p17104 p17874 p17127 p20274 p20470 p17133 p17089 p16394 p16396 p16576 p16657 p17147 p16977 p20932
end
end Assembly
