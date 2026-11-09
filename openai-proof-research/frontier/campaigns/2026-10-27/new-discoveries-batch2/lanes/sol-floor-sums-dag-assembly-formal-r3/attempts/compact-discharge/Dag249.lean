import Dag248
import generated.th_lemma_33
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n21316 (_v : Vars) (_q : Query _v)  : (e21315 _v) := by
  by_contra hc
  change ¬ ((¬ (e8045 _v)) ∨ (¬ (e2787 _v)) ∨ (¬ (e4285 _v)) ∨ (e2179 _v) ∨ (¬ (e4096 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4813 _v))) at hc
  have h51 : (e51 _v) := by
    tauto
  have h91 : (e91 _v) := by
    tauto
  have h191 : (e191 _v) := by
    tauto
  have h2787 : (e2787 _v) := by
    tauto
  have h3152 : (e3152 _v) := by
    tauto
  have h4096 : (e4096 _v) := by
    tauto
  have h4139 : (e4139 _v) := by
    tauto
  have h4260 : (e4260 _v) := by
    tauto
  have h4285 : (e4285 _v) := by
    tauto
  have h4306 : (e4306 _v) := by
    tauto
  have h4653 : (e4653 _v) := by
    tauto
  have h4675 : (e4675 _v) := by
    tauto
  have h4787 : (e4787 _v) := by
    tauto
  have h4813 : (e4813 _v) := by
    tauto
  have h4838 : (e4838 _v) := by
    tauto
  have h6501 : (e6501 _v) := by
    change (¬ (e2179 _v))
    tauto
  have h8045 : (e8045 _v) := by
    tauto
  have p21305 := n21305 _v _q h51 h91 h191 h2787 h3152 h4096 h4139 h4260 h4285 h4306 h4653 h4675 h4787 h4813 h4838 h6501 h8045
  exact p21305
theorem n21317 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4608 : (e4608 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4813 : (e4813 _v)) (h6571 : (e6571 _v)) (h6750 : (e6750 _v)) : (e4546 _v) := by
  have p16307 := n16307 _v _q 
  have p21309 := n21309 _v _q h51 h91 h2529 h3152 h3937 h4260 h4306 h4608 h4653 h4675 h4813 h6571 h6750
  simp only [e4544, e4545, e4546, e4547, e8029, e8030, e8035] at *
  tauto
theorem n21319 (_v : Vars) (_q : Query _v)  : (e21318 _v) := by
  by_contra hc
  change ¬ ((e2358 _v) ∨ (e2242 _v) ∨ (¬ (e2179 _v)) ∨ (e2733 _v) ∨ (¬ (e4260 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4813 _v))) at hc
  have h51 : (e51 _v) := by
    tauto
  have h91 : (e91 _v) := by
    tauto
  have h191 : (e191 _v) := by
    tauto
  have h2179 : (e2179 _v) := by
    tauto
  have h4260 : (e4260 _v) := by
    tauto
  have h4306 : (e4306 _v) := by
    tauto
  have h4653 : (e4653 _v) := by
    tauto
  have h4787 : (e4787 _v) := by
    tauto
  have h4813 : (e4813 _v) := by
    tauto
  have h4838 : (e4838 _v) := by
    tauto
  have h6525 : (e6525 _v) := by
    change (¬ (e2242 _v))
    tauto
  have h6571 : (e6571 _v) := by
    change (¬ (e2358 _v))
    tauto
  have h6750 : (e6750 _v) := by
    change (¬ (e2733 _v))
    tauto
  have p21310 := n21310 _v _q h51 h91 h191 h2179 h4260 h4306 h4653 h4787 h4813 h4838 h6525 h6571 h6750
  exact p21310
theorem n21320 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2402 : (e2402 _v)) (h3158 : (e3158 _v)) (h4101 : (e4101 _v)) (h4139 : (e4139 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4546 : (e4546 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h5093 : (e5093 _v)) (h6525 : (e6525 _v)) (h7814 : (e7814 _v)) : (e7489 _v) := by
  have p21311 := n21311 _v _q h51 h91 h191 h2402 h3158 h4101 h4139 h4260 h4306 h4546 h4653 h4787 h4813 h4838 h5093 h6525 h7814
  have p4976 := n4976 _v _q h4546
  have p8463 := n8463 _v _q h6525
  have p11440 := n11440 _v _q h5093
  have p13951 := n13951 _v _q 
  have p16778 := n16778 _v _q 
  have p17122 := n17122 _v _q 
  have p17172 := n17172 _v _q h7814
  have p4979 := n4979 _v _q h4139
  have p20829 := n20829 _v _q 
  have p15321 := n15321 _v _q h5093
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
  have p21301 := n21301 _v _q h51 h91 h191 h2402 h3158 h4101 h4139 h4260 h4306 h4546 h4653 h4787 h4813 h4838 h5093 h6525 h7814
  have p8591 := n8591 _v _q h2402
  exact FloorCertificate.node_21320 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2902 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p21311 p4976 p8463 p11440 p13951 p16778 p17122 p17172 p4979 p20829 p15321 p20426 p20126 p17110 p17065 p17053 p20096 p17131 p17108 p17294 p16943 p17058 p4983 p14799 p17064 p17067 p17080 p17072 p17074 p17069 p20461 p20836 p20653 p17078 p17136 p17087 p17083 p21244 p17055 p17093 p17091 p17098 p17106 p16885 p21245 p17141 p17100 p19610 p4981 p17102 p5008 p17009 p16058 p16689 p17096 p17115 p17758 p17124 p17111 p19665 p17113 p17117 p20467 p17120 p4999 p17133 p17874 p17104 p17127 p17089 p20470 p253 p17020 p20274 p21142 p16729 p17050 p17138 p17060 p4989 p21301 p8591
theorem n21322 (_v : Vars) (_q : Query _v)  : (e21321 _v) := by
  by_contra hc
  change ¬ ((e2402 _v) ∨ (e2733 _v) ∨ (¬ (e3152 _v)) ∨ (¬ (e2242 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e91 _v)) ∨ (e2781 _v)) at hc
  have h51 : (e51 _v) := by
    tauto
  have h91 : (e91 _v) := by
    tauto
  have h191 : (e191 _v) := by
    tauto
  have h2242 : (e2242 _v) := by
    tauto
  have h3152 : (e3152 _v) := by
    tauto
  have h4306 : (e4306 _v) := by
    tauto
  have h4653 : (e4653 _v) := by
    tauto
  have h4787 : (e4787 _v) := by
    tauto
  have h4813 : (e4813 _v) := by
    tauto
  have h4838 : (e4838 _v) := by
    tauto
  have h6600 : (e6600 _v) := by
    change (¬ (e2402 _v))
    tauto
  have h6750 : (e6750 _v) := by
    change (¬ (e2733 _v))
    tauto
  have h6776 : (e6776 _v) := by
    change (¬ (e2781 _v))
    tauto
  have p21312 := n21312 _v _q h51 h91 h191 h2242 h3152 h4306 h4653 h4787 h4813 h4838 h6600 h6750 h6776
  exact p21312
theorem n21323 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2787 : (e2787 _v)) (h3152 : (e3152 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6501 : (e6501 _v)) : (e8048 _v) := by
  have p21316 := n21316 _v _q 
  have p11430 := n11430 _v _q h2787
  have p4977 := n4977 _v _q h4285
  have p8554 := n8554 _v _q h6501
  have p5001 := n5001 _v _q h4096
  have p4979 := n4979 _v _q h4139
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
  simp only [e51, e57, e91, e95, e191, e192, e2179, e2787, e3152, e3156, e4096, e4097, e4139, e4140, e4260, e4261, e4285, e4286, e4306, e4311, e4653, e4658, e4675, e4676, e4787, e4788, e4813, e4814, e4838, e4839, e6501, e6772, e8045, e8048, e21315] at *
  tauto
theorem n21324 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2787 : (e2787 _v)) (h3152 : (e3152 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6501 : (e6501 _v)) : (e8049 _v) := by
  have p15206 := n15206 _v _q 
  have p21323 := n21323 _v _q h51 h91 h191 h2787 h3152 h4096 h4139 h4260 h4285 h4306 h4653 h4675 h4787 h4813 h4838 h6501
  simp only [e8043, e8045, e8047, e8048, e8049, e8490] at *
  tauto
theorem n21325 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4608 : (e4608 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4813 : (e4813 _v)) (h6571 : (e6571 _v)) (h6750 : (e6750 _v)) : (e7489 _v) := by
  have p17093 := n17093 _v _q 
  have p17189 := n17189 _v _q h6571
  have p17091 := n17091 _v _q 
  have p4991 := n4991 _v _q h4608
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p8420 := n8420 _v _q h6750
  have p15940 := n15940 _v _q h6750
  have p17255 := n17255 _v _q h6571
  have p16576 := n16576 _v _q 
  have p13951 := n13951 _v _q 
  have p21249 := n21249 _v _q h51 h91 h2529 h3152 h4260 h4306 h4653 h4675 h4813
  have p17141 := n17141 _v _q 
  have p21317 := n21317 _v _q h51 h91 h2529 h3152 h3937 h4260 h4306 h4608 h4653 h4675 h4813 h6571 h6750
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
  have p15623 := n15623 _v _q h6571
  have p21250 := n21250 _v _q h51 h91 h2529 h3152 h4260 h4306 h4653 h4675 h4813
  have p8548 := n8548 _v _q h2529
  have p10893 := n10893 _v _q 
  have p21308 := n21308 _v _q h51 h91 h2529 h3152 h3937 h4260 h4306 h4608 h4653 h4675 h4813 h6571 h6750
  have p8447 := n8447 _v _q h6571
  exact FloorCertificate.node_21325 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2863 _v) (e2877 _v) (e2883 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p17093 p17189 p17091 p4991 p17098 p17106 p8420 p15940 p17255 p16576 p13951 p21249 p17141 p21317 p17100 p19610 p4981 p17102 p21190 p4996 p16977 p17256 p17009 p17147 p5006 p4998 p17096 p17115 p17758 p17124 p17111 p19665 p17113 p17117 p20467 p17120 p4999 p17133 p17874 p17104 p17127 p17089 p20470 p16705 p17020 p20274 p21142 p16729 p17050 p17138 p17060 p16572 p4983 p17122 p16778 p20829 p17108 p20461 p20426 p20126 p17110 p17053 p17131 p20096 p17058 p17294 p16943 p17064 p17067 p17069 p17080 p17072 p17083 p17074 p20836 p17078 p20653 p17087 p17136 p17055 p15623 p21250 p8548 p10893 p21308 p8447
theorem n21326 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2179 : (e2179 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6525 : (e6525 _v)) (h6750 : (e6750 _v)) : (e2358 _v) := by
  have p21319 := n21319 _v _q 
  have p15957 := n15957 _v _q h2179
  have p8463 := n8463 _v _q h6525
  have p8420 := n8420 _v _q h6750
  have p4981 := n4981 _v _q h4260
  have p5008 := n5008 _v _q h4787
  have p4999 := n4999 _v _q h91
  have p253 := n253 _v _q h191
  have p16729 := n16729 _v _q h51
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4989 := n4989 _v _q h4838
  have p4983 := n4983 _v _q h4813
  simp only [e51, e57, e91, e95, e191, e192, e2179, e2242, e2358, e2733, e4260, e4261, e4306, e4311, e4653, e4658, e4787, e4788, e4813, e4814, e4838, e4839, e6501, e6525, e6750, e21318] at *
  tauto
theorem n21327 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2179 : (e2179 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6525 : (e6525 _v)) (h6750 : (e6750 _v)) : (e7640 _v) := by
  have p14828 := n14828 _v _q 
  have p21326 := n21326 _v _q h51 h91 h191 h2179 h4260 h4306 h4653 h4787 h4813 h4838 h6525 h6750
  simp only [e2358, e4139, e4140, e4141, e4142, e6571, e7634, e7640, e7643] at *
  tauto
theorem n21329 (_v : Vars) (_q : Query _v)  : (e21328 _v) := by
  by_contra hc
  change ¬ ((¬ (e7814 _v)) ∨ (¬ (e4546 _v)) ∨ (e2242 _v) ∨ (e13 _v) ∨ (¬ (e4139 _v)) ∨ (¬ (e4101 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e3158 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e2402 _v))) at hc
  have h51 : (e51 _v) := by
    tauto
  have h91 : (e91 _v) := by
    tauto
  have h191 : (e191 _v) := by
    tauto
  have h2402 : (e2402 _v) := by
    tauto
  have h3158 : (e3158 _v) := by
    tauto
  have h4101 : (e4101 _v) := by
    tauto
  have h4139 : (e4139 _v) := by
    tauto
  have h4260 : (e4260 _v) := by
    tauto
  have h4306 : (e4306 _v) := by
    tauto
  have h4546 : (e4546 _v) := by
    tauto
  have h4653 : (e4653 _v) := by
    tauto
  have h4787 : (e4787 _v) := by
    tauto
  have h4813 : (e4813 _v) := by
    tauto
  have h4838 : (e4838 _v) := by
    tauto
  have h5093 : (e5093 _v) := by
    change (¬ (e13 _v))
    tauto
  have h6525 : (e6525 _v) := by
    change (¬ (e2242 _v))
    tauto
  have h7814 : (e7814 _v) := by
    tauto
  have p21320 := n21320 _v _q h51 h91 h191 h2402 h3158 h4101 h4139 h4260 h4306 h4546 h4653 h4787 h4813 h4838 h5093 h6525 h7814
  exact p21320
theorem n21330 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2242 : (e2242 _v)) (h3152 : (e3152 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6630 : (e6630 _v)) (h6750 : (e6750 _v)) (h6776 : (e6776 _v)) : (e2402 _v) := by
  have p21322 := n21322 _v _q 
  have p8420 := n8420 _v _q h6750
  have p4998 := n4998 _v _q h3152
  have p8553 := n8553 _v _q h2242
  have p253 := n253 _v _q h191
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4989 := n4989 _v _q h4838
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p15934 := n15934 _v _q h6630
  have p4999 := n4999 _v _q h91
  have p8601 := n8601 _v _q h6776
  simp only [e51, e57, e91, e95, e191, e192, e2242, e2402, e2733, e2781, e3152, e3156, e4306, e4311, e4653, e4658, e4787, e4788, e4813, e4814, e4838, e4839, e6525, e6750, e6776, e21321] at *
  tauto
theorem n21331 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2787 : (e2787 _v)) (h3152 : (e3152 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6501 : (e6501 _v)) : (e2475 _v) := by
  have p15207 := n15207 _v _q 
  have p21324 := n21324 _v _q h51 h91 h191 h2787 h3152 h4096 h4139 h4260 h4285 h4306 h4653 h4675 h4787 h4813 h4838 h6501
  simp only [e2475, e8043, e8045, e8047, e8048, e8049, e8050, e11165] at *
  tauto
theorem n21332 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2787 : (e2787 _v)) (h3152 : (e3152 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6501 : (e6501 _v)) : (e8035 _v) := by
  have p14871 := n14871 _v _q 
  have p21331 := n21331 _v _q h51 h91 h191 h2787 h3152 h4096 h4139 h4260 h4285 h4306 h4653 h4675 h4787 h4813 h4838 h6501
  simp only [e2475, e4544, e4545, e4546, e4547, e8029, e8035, e8038, e8040] at *
  tauto
theorem n21334 (_v : Vars) (_q : Query _v)  : (e21333 _v) := by
  by_contra hc
  change ¬ ((e2358 _v) ∨ (¬ (e4608 _v)) ∨ (e2733 _v) ∨ (¬ (e4260 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e2529 _v))) at hc
  have h51 : (e51 _v) := by
    tauto
  have h91 : (e91 _v) := by
    tauto
  have h2529 : (e2529 _v) := by
    tauto
  have h3152 : (e3152 _v) := by
    tauto
  have h3937 : (e3937 _v) := by
    tauto
  have h4260 : (e4260 _v) := by
    tauto
  have h4306 : (e4306 _v) := by
    tauto
  have h4608 : (e4608 _v) := by
    tauto
  have h4653 : (e4653 _v) := by
    tauto
  have h4675 : (e4675 _v) := by
    tauto
  have h4813 : (e4813 _v) := by
    tauto
  have h6571 : (e6571 _v) := by
    change (¬ (e2358 _v))
    tauto
  have h6750 : (e6750 _v) := by
    change (¬ (e2733 _v))
    tauto
  have p21325 := n21325 _v _q h51 h91 h2529 h3152 h3937 h4260 h4306 h4608 h4653 h4675 h4813 h6571 h6750
  exact p21325
theorem n21335 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2179 : (e2179 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6525 : (e6525 _v)) (h6750 : (e6750 _v)) : (e4139 _v) := by
  have p16281 := n16281 _v _q 
  have p21327 := n21327 _v _q h51 h91 h191 h2179 h4260 h4306 h4653 h4787 h4813 h4838 h6525 h6750
  simp only [e4139, e4140, e4141, e4142, e7634, e7635, e7640] at *
  tauto
theorem n21336 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2242 : (e2242 _v)) (h3152 : (e3152 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6630 : (e6630 _v)) (h6750 : (e6750 _v)) (h6776 : (e6776 _v)) : (e2787 _v) := by
  have p20880 := n20880 _v _q 
  have p21330 := n21330 _v _q h51 h91 h191 h2242 h3152 h4306 h4653 h4813 h4838 h6630 h6750 h6776
  have p8420 := n8420 _v _q h6750
  have p15956 := n15956 _v _q h6776
  have p4998 := n4998 _v _q h3152
  have p8553 := n8553 _v _q h2242
  have p253 := n253 _v _q h191
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4989 := n4989 _v _q h4838
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p4999 := n4999 _v _q h91
  have p8434 := n8434 _v _q h6630
  simp only [e51, e57, e91, e95, e191, e192, e2242, e2402, e2468, e2733, e2787, e3152, e3156, e4260, e4261, e4306, e4311, e4653, e4658, e4813, e4814, e4838, e4839, e6525, e6600, e6630, e6750, e20879] at *
  tauto
theorem n21337 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2242 : (e2242 _v)) (h3152 : (e3152 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6630 : (e6630 _v)) (h6750 : (e6750 _v)) (h6776 : (e6776 _v)) : (e7927 _v) := by
  have p14855 := n14855 _v _q 
  have p21336 := n21336 _v _q h51 h91 h191 h2242 h3152 h4306 h4653 h4813 h4838 h6630 h6750 h6776
  simp only [e2787, e4417, e4418, e4419, e4420, e6772, e7921, e7927, e7930] at *
  tauto
theorem n21338 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2242 : (e2242 _v)) (h3152 : (e3152 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6630 : (e6630 _v)) (h6750 : (e6750 _v)) (h6776 : (e6776 _v)) : (e3929 _v) := by
  have p14484 := n14484 _v _q 
  have p21330 := n21330 _v _q h51 h91 h191 h2242 h3152 h4306 h4653 h4813 h4838 h6630 h6750 h6776
  simp only [e2402, e3919, e3920, e3921, e3922, e3923, e3929, e6600, e7422] at *
  tauto
theorem n21339 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2242 : (e2242 _v)) (h3152 : (e3152 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6630 : (e6630 _v)) (h6750 : (e6750 _v)) (h6776 : (e6776 _v)) : (e3919 _v) := by
  have p14797 := n14797 _v _q 
  have p21338 := n21338 _v _q h51 h91 h191 h2242 h3152 h4306 h4653 h4813 h4838 h6630 h6750 h6776
  simp only [e3919, e3920, e3921, e3922, e3923, e3924, e3929] at *
  tauto
theorem n21340 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2242 : (e2242 _v)) (h3152 : (e3152 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6630 : (e6630 _v)) (h6750 : (e6750 _v)) (h6776 : (e6776 _v)) : (e2303 _v) := by
  have p8420 := n8420 _v _q h6750
  have p21330 := n21330 _v _q h51 h91 h191 h2242 h3152 h4306 h4653 h4813 h4838 h6630 h6750 h6776
  exact FloorCertificate.node_21340 (e2 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8420 p21330
theorem n21341 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2242 : (e2242 _v)) (h3152 : (e3152 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6630 : (e6630 _v)) (h6750 : (e6750 _v)) (h6776 : (e6776 _v)) : (e7804 _v) := by
  have p14837 := n14837 _v _q 
  have p21340 := n21340 _v _q h51 h91 h191 h2242 h3152 h4306 h4653 h4813 h4838 h6630 h6750 h6776
  simp only [e2303, e4283, e4284, e4285, e4286, e7798, e7804, e7807, e7809] at *
  tauto
theorem n21342 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2242 : (e2242 _v)) (h3152 : (e3152 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6630 : (e6630 _v)) (h6750 : (e6750 _v)) (h6776 : (e6776 _v)) : (e2358 _v) := by
  have p8451 := n8451 _v _q 
  have p21340 := n21340 _v _q h51 h91 h191 h2242 h3152 h4306 h4653 h4813 h4838 h6630 h6750 h6776
  simp only [e2303, e2358, e7807, e8450] at *
  tauto
theorem n21343 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2787 : (e2787 _v)) (h3152 : (e3152 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6501 : (e6501 _v)) : (e4546 _v) := by
  have p16307 := n16307 _v _q 
  have p21332 := n21332 _v _q h51 h91 h191 h2787 h3152 h4096 h4139 h4260 h4285 h4306 h4653 h4675 h4787 h4813 h4838 h6501
  simp only [e4544, e4545, e4546, e4547, e8029, e8030, e8035] at *
  tauto
theorem n21344 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h3152 : (e3152 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4813 : (e4813 _v)) (h6501 : (e6501 _v)) (h6750 : (e6750 _v)) : (e2358 _v) := by
  have p21334 := n21334 _v _q 
  have p15641 := n15641 _v _q h6501
  have p8420 := n8420 _v _q h6750
  have p4981 := n4981 _v _q h4260
  have p16325 := n16325 _v _q h6501
  have p5006 := n5006 _v _q h4675
  have p4998 := n4998 _v _q h3152
  have p4999 := n4999 _v _q h91
  have p16729 := n16729 _v _q h51
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4983 := n4983 _v _q h4813
  have p8548 := n8548 _v _q h2529
  simp only [e51, e57, e91, e95, e2358, e2529, e2733, e3152, e3156, e3937, e3942, e4260, e4261, e4306, e4311, e4608, e4609, e4653, e4658, e4675, e4676, e4813, e4814, e6750, e8310, e21333] at *
  tauto
theorem n21345 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h3152 : (e3152 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4813 : (e4813 _v)) (h6501 : (e6501 _v)) (h6750 : (e6750 _v)) : (e7640 _v) := by
  have p14828 := n14828 _v _q 
  have p21344 := n21344 _v _q h51 h91 h2529 h3152 h4260 h4306 h4653 h4675 h4813 h6501 h6750
  simp only [e2358, e4139, e4140, e4141, e4142, e6571, e7634, e7640, e7643] at *
  tauto
theorem n21346 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2179 : (e2179 _v)) (h3919 : (e3919 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4306 : (e4306 _v)) (h4419 : (e4419 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h5100 : (e5100 _v)) (h6525 : (e6525 _v)) (h6750 : (e6750 _v)) (h8045 : (e8045 _v)) : (e7489 _v) := by
  have p258 := n258 _v _q 
  have p8463 := n8463 _v _q h6525
  have p15957 := n15957 _v _q h2179
  have p8420 := n8420 _v _q h6750
  have p17157 := n17157 _v _q h8045
  have p17080 := n17080 _v _q 
  have p13951 := n13951 _v _q 
  have p17072 := n17072 _v _q 
  have p17074 := n17074 _v _q 
  have p17069 := n17069 _v _q 
  have p16913 := n16913 _v _q 
  have p17159 := n17159 _v _q h5100
  have p4971 := n4971 _v _q h4419
  have p4977 := n4977 _v _q h4285
  have p15959 := n15959 _v _q h2179
  have p20836 := n20836 _v _q 
  have p20653 := n20653 _v _q 
  have p17078 := n17078 _v _q 
  have p17136 := n17136 _v _q 
  have p21335 := n21335 _v _q h51 h91 h191 h2179 h4260 h4306 h4653 h4787 h4813 h4838 h6525 h6750
  have p17087 := n17087 _v _q 
  have p17083 := n17083 _v _q 
  have p21244 := n21244 _v _q h51 h91 h191 h4260 h4306 h4653 h4787 h4813 h4838 h6525
  have p17055 := n17055 _v _q 
  have p17093 := n17093 _v _q 
  have p17091 := n17091 _v _q 
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p15940 := n15940 _v _q h6750
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
  exact FloorCertificate.node_21346 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p258 p8463 p15957 p8420 p17157 p17080 p13951 p17072 p17074 p17069 p16913 p17159 p4971 p4977 p15959 p20836 p20653 p17078 p17136 p21335 p17087 p17083 p21244 p17055 p17093 p17091 p17098 p17106 p15940 p21245 p17141 p17100 p19610 p4981 p17102 p5008 p17009 p17079 p16058 p16689 p17096 p17115 p17758 p17124 p17111 p19665 p17113 p17117 p20467 p17120 p4999 p17133 p17874 p17104 p17127 p17089 p20470 p253 p17020 p20274 p21142 p16729 p17050 p17138 p17060 p4989 p4983 p17122 p16778 p20829 p17108 p20461 p20426 p20126 p17110 p17053 p17131 p20096 p17058 p17294 p16943 p17064 p17067
theorem n21347 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2179 : (e2179 _v)) (h2402 : (e2402 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6525 : (e6525 _v)) (h6750 : (e6750 _v)) : (e5093 _v) := by
  have p21272 := n21272 _v _q 
  have p14799 := n14799 _v _q h2402
  have p8463 := n8463 _v _q h6525
  have p21335 := n21335 _v _q h51 h91 h191 h2179 h4260 h4306 h4653 h4787 h4813 h4838 h6525 h6750
  have p15940 := n15940 _v _q h6750
  have p4981 := n4981 _v _q h4260
  have p5008 := n5008 _v _q h4787
  have p15957 := n15957 _v _q h2179
  have p4999 := n4999 _v _q h91
  have p253 := n253 _v _q h191
  have p16729 := n16729 _v _q h51
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4989 := n4989 _v _q h4838
  have p4983 := n4983 _v _q h4813
  have p11534 := n11534 _v _q h2402 h6750
  simp only [e13, e51, e57, e91, e95, e191, e192, e2179, e2242, e2303, e3919, e3920, e4096, e4097, e4139, e4140, e4260, e4261, e4306, e4311, e4653, e4658, e4787, e4788, e4813, e4814, e4838, e4839, e5093, e6501, e6525, e7807, e21271] at *
  tauto
theorem n21348 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2179 : (e2179 _v)) (h2303 : (e2303 _v)) (h3919 : (e3919 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6525 : (e6525 _v)) (h6750 : (e6750 _v)) : (e5093 _v) := by
  have p21272 := n21272 _v _q 
  have p17079 := n17079 _v _q h3919
  have p8463 := n8463 _v _q h6525
  have p21335 := n21335 _v _q h51 h91 h191 h2179 h4260 h4306 h4653 h4787 h4813 h4838 h6525 h6750
  have p15940 := n15940 _v _q h6750
  have p4981 := n4981 _v _q h4260
  have p5008 := n5008 _v _q h4787
  have p15957 := n15957 _v _q h2179
  have p4999 := n4999 _v _q h91
  have p253 := n253 _v _q h191
  have p16729 := n16729 _v _q h51
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4989 := n4989 _v _q h4838
  have p4983 := n4983 _v _q h4813
  have p8448 := n8448 _v _q h2303
  simp only [e13, e51, e57, e91, e95, e191, e192, e2179, e2242, e2303, e3919, e3920, e4096, e4097, e4139, e4140, e4260, e4261, e4306, e4311, e4653, e4658, e4787, e4788, e4813, e4814, e4838, e4839, e5093, e6501, e6525, e7807, e21271] at *
  tauto
theorem n21349 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2179 : (e2179 _v)) (h2303 : (e2303 _v)) (h3919 : (e3919 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6525 : (e6525 _v)) (h6750 : (e6750 _v)) : (e5105 _v) := by
  have p15204 := n15204 _v _q 
  have p21348 := n21348 _v _q h51 h91 h191 h2179 h2303 h3919 h4260 h4306 h4653 h4787 h4813 h4838 h6525 h6750
  simp only [e13, e5093, e5098, e5100, e5102, e5103, e5104, e5105, e8622] at *
  tauto
theorem n21350 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2242 : (e2242 _v)) (h3152 : (e3152 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6630 : (e6630 _v)) (h6750 : (e6750 _v)) (h6776 : (e6776 _v)) : (e4419 _v) := by
  have p16347 := n16347 _v _q 
  have p21337 := n21337 _v _q h51 h91 h191 h2242 h3152 h4306 h4653 h4813 h4838 h6630 h6750 h6776
  simp only [e4417, e4418, e4419, e4420, e7921, e7922, e7927] at *
  tauto
theorem n21351 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2242 : (e2242 _v)) (h3152 : (e3152 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6630 : (e6630 _v)) (h6750 : (e6750 _v)) (h6776 : (e6776 _v)) : (e4285 _v) := by
  have p16274 := n16274 _v _q 
  have p21341 := n21341 _v _q h51 h91 h191 h2242 h3152 h4306 h4653 h4813 h4838 h6630 h6750 h6776
  simp only [e4283, e4284, e4285, e4286, e7798, e7799, e7804] at *
  tauto
theorem n21352 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2242 : (e2242 _v)) (h3152 : (e3152 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6630 : (e6630 _v)) (h6750 : (e6750 _v)) (h6776 : (e6776 _v)) : (e7640 _v) := by
  have p14828 := n14828 _v _q 
  have p21342 := n21342 _v _q h51 h91 h191 h2242 h3152 h4306 h4653 h4813 h4838 h6630 h6750 h6776
  simp only [e2358, e4139, e4140, e4141, e4142, e6571, e7634, e7640, e7643] at *
  tauto
theorem n21353 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2242 : (e2242 _v)) (h3152 : (e3152 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6630 : (e6630 _v)) (h6750 : (e6750 _v)) (h6776 : (e6776 _v)) : (e4139 _v) := by
  have p16281 := n16281 _v _q 
  have p21352 := n21352 _v _q h51 h91 h191 h2242 h3152 h4306 h4653 h4813 h4838 h6630 h6750 h6776
  simp only [e4139, e4140, e4141, e4142, e7634, e7635, e7640] at *
  tauto
theorem n21354 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2787 : (e2787 _v)) (h3152 : (e3152 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6501 : (e6501 _v)) : (e7489 _v) := by
  have p16349 := n16349 _v _q h2787
  have p11430 := n11430 _v _q h2787
  have p4977 := n4977 _v _q h4285
  have p17136 := n17136 _v _q 
  have p10893 := n10893 _v _q 
  have p16913 := n16913 _v _q 
  have p17087 := n17087 _v _q 
  have p13951 := n13951 _v _q 
  have p8554 := n8554 _v _q h6501
  have p21331 := n21331 _v _q h51 h91 h191 h2787 h3152 h4096 h4139 h4260 h4285 h4306 h4653 h4675 h4787 h4813 h4838 h6501
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
  have p21343 := n21343 _v _q h51 h91 h191 h2787 h3152 h4096 h4139 h4260 h4285 h4306 h4653 h4675 h4787 h4813 h4838 h6501
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
  have p21294 := n21294 _v _q h51 h91 h191 h2787 h3152 h4096 h4139 h4260 h4285 h4306 h4653 h4675 h4787 h4813 h4838 h6501
  have p21282 := n21282 _v _q h51 h91 h191 h2787 h3152 h4096 h4139 h4260 h4285 h4306 h4653 h4675 h4787 h4813 h4838 h6501
  exact FloorCertificate.node_21354 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2863 _v) (e2877 _v) (e2883 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p16349 p11430 p4977 p17136 p10893 p16913 p17087 p13951 p8554 p21331 p21242 p17055 p17093 p17091 p15641 p17098 p17106 p5001 p16576 p4979 p21212 p17141 p21343 p17100 p19610 p4981 p17102 p5008 p16325 p17009 p17147 p5006 p4998 p17096 p17115 p17758 p17124 p17111 p19665 p17113 p17117 p20467 p17120 p4999 p17133 p17874 p17104 p17127 p17089 p20470 p253 p17020 p20274 p21142 p16729 p17050 p17138 p17060 p4989 p4983 p17122 p16778 p20829 p17108 p20461 p20426 p20126 p17110 p17053 p17131 p20096 p17058 p17294 p16943 p17064 p17067 p17069 p17080 p17072 p17083 p17074 p20836 p17078 p20653 p21294 p21282
theorem n21355 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h3152 : (e3152 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4813 : (e4813 _v)) (h6501 : (e6501 _v)) (h6750 : (e6750 _v)) : (e4139 _v) := by
  have p16281 := n16281 _v _q 
  have p21345 := n21345 _v _q h51 h91 h2529 h3152 h4260 h4306 h4653 h4675 h4813 h6501 h6750
  simp only [e4139, e4140, e4141, e4142, e7634, e7635, e7640] at *
  tauto
theorem n21357 (_v : Vars) (_q : Query _v)  : (e21356 _v) := by
  by_contra hc
  change ¬ ((¬ (e8045 _v)) ∨ (e2242 _v) ∨ (¬ (e2179 _v)) ∨ (e2733 _v) ∨ (¬ (e5100 _v)) ∨ (¬ (e4419 _v)) ∨ (¬ (e4285 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e3919 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4813 _v))) at hc
  have h51 : (e51 _v) := by
    tauto
  have h91 : (e91 _v) := by
    tauto
  have h191 : (e191 _v) := by
    tauto
  have h2179 : (e2179 _v) := by
    tauto
  have h3919 : (e3919 _v) := by
    tauto
  have h4260 : (e4260 _v) := by
    tauto
  have h4285 : (e4285 _v) := by
    tauto
  have h4306 : (e4306 _v) := by
    tauto
  have h4419 : (e4419 _v) := by
    tauto
  have h4653 : (e4653 _v) := by
    tauto
  have h4787 : (e4787 _v) := by
    tauto
  have h4813 : (e4813 _v) := by
    tauto
  have h4838 : (e4838 _v) := by
    tauto
  have h5100 : (e5100 _v) := by
    tauto
  have h6525 : (e6525 _v) := by
    change (¬ (e2242 _v))
    tauto
  have h6750 : (e6750 _v) := by
    change (¬ (e2733 _v))
    tauto
  have h8045 : (e8045 _v) := by
    tauto
  have p21346 := n21346 _v _q h51 h91 h191 h2179 h3919 h4260 h4285 h4306 h4419 h4653 h4787 h4813 h4838 h5100 h6525 h6750 h8045
  exact p21346
theorem n21358 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2179 : (e2179 _v)) (h2402 : (e2402 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6525 : (e6525 _v)) (h6750 : (e6750 _v)) : (e5105 _v) := by
  have p15204 := n15204 _v _q 
  have p21347 := n21347 _v _q h51 h91 h191 h2179 h2402 h4260 h4306 h4653 h4787 h4813 h4838 h6525 h6750
  simp only [e13, e5093, e5098, e5100, e5102, e5103, e5104, e5105, e8622] at *
  tauto
theorem n21359 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2179 : (e2179 _v)) (h2402 : (e2402 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6525 : (e6525 _v)) (h6750 : (e6750 _v)) : (e5100 _v) := by
  have p15319 := n15319 _v _q 
  have p21358 := n21358 _v _q h51 h91 h191 h2179 h2402 h4260 h4306 h4653 h4787 h4813 h4838 h6525 h6750
  simp only [e5098, e5100, e5102, e5103, e5104, e5105, e8479] at *
  tauto
theorem n21360 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2179 : (e2179 _v)) (h2303 : (e2303 _v)) (h3919 : (e3919 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6525 : (e6525 _v)) (h6750 : (e6750 _v)) : (e5100 _v) := by
  have p15319 := n15319 _v _q 
  have p21349 := n21349 _v _q h51 h91 h191 h2179 h2303 h3919 h4260 h4306 h4653 h4787 h4813 h4838 h6525 h6750
  simp only [e5098, e5100, e5102, e5103, e5104, e5105, e8479] at *
  tauto
theorem n21361 (_v : Vars) (_q : Query _v) (h2303 : (e2303 _v)) (h6772 : (e6772 _v)) : (e8045 _v) := by
  have p15206 := n15206 _v _q 
  have p16080 := n16080 _v _q h2303 h6772
  simp only [e8043, e8045, e8047, e8048, e8049, e8050, e8490] at *
  tauto
theorem n21362 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2179 : (e2179 _v)) (h2303 : (e2303 _v)) (h3919 : (e3919 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6525 : (e6525 _v)) (h6750 : (e6750 _v)) (h6772 : (e6772 _v)) : (e7489 _v) := by
  have p15957 := n15957 _v _q h2179
  have p21360 := n21360 _v _q h51 h91 h191 h2179 h2303 h3919 h4260 h4306 h4653 h4787 h4813 h4838 h6525 h6750
  have p8420 := n8420 _v _q h6750
  have p15944 := n15944 _v _q h6772
  have p21361 := n21361 _v _q h2303 h6772
  have p17080 := n17080 _v _q 
  have p8463 := n8463 _v _q h6525
  have p13951 := n13951 _v _q 
  have p17072 := n17072 _v _q 
  have p17074 := n17074 _v _q 
  have p17069 := n17069 _v _q 
  have p16913 := n16913 _v _q 
  have p16436 := n16436 _v _q h2303
  have p15959 := n15959 _v _q h2179
  have p20836 := n20836 _v _q 
  have p20653 := n20653 _v _q 
  have p17078 := n17078 _v _q 
  have p17136 := n17136 _v _q 
  have p21335 := n21335 _v _q h51 h91 h191 h2179 h4260 h4306 h4653 h4787 h4813 h4838 h6525 h6750
  have p17087 := n17087 _v _q 
  have p17083 := n17083 _v _q 
  have p21244 := n21244 _v _q h51 h91 h191 h4260 h4306 h4653 h4787 h4813 h4838 h6525
  have p17055 := n17055 _v _q 
  have p17093 := n17093 _v _q 
  have p17091 := n17091 _v _q 
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p15940 := n15940 _v _q h6750
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
  have p8458 := n8458 _v _q h6772
  exact FloorCertificate.node_21362 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p15957 p21360 p8420 p15944 p21361 p17080 p8463 p13951 p17072 p17074 p17069 p16913 p16436 p15959 p20836 p20653 p17078 p17136 p21335 p17087 p17083 p21244 p17055 p17093 p17091 p17098 p17106 p15940 p21245 p17141 p17100 p19610 p4981 p17102 p5008 p17009 p17079 p16058 p16689 p17096 p17115 p17758 p17124 p17111 p19665 p17113 p17117 p20467 p17120 p4999 p17133 p17874 p17104 p17127 p17089 p20470 p253 p17020 p20274 p21142 p16729 p17050 p17138 p17060 p4989 p4983 p17122 p16778 p20829 p17108 p20461 p20426 p20126 p17110 p17053 p17131 p20096 p17058 p17294 p16943 p17064 p17067 p8458
theorem n21363 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2242 : (e2242 _v)) (h3152 : (e3152 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6630 : (e6630 _v)) (h6750 : (e6750 _v)) (h6776 : (e6776 _v)) : (e8048 _v) := by
  have p20878 := n20878 _v _q 
  have p21350 := n21350 _v _q h51 h91 h191 h2242 h3152 h4306 h4653 h4813 h4838 h6630 h6750 h6776
  have p4999 := n4999 _v _q h91
  have p8434 := n8434 _v _q h6630
  have p21339 := n21339 _v _q h51 h91 h191 h2242 h3152 h4306 h4653 h4813 h4838 h6630 h6750 h6776
  have p15940 := n15940 _v _q h6750
  have p21351 := n21351 _v _q h51 h91 h191 h2242 h3152 h4306 h4653 h4813 h4838 h6630 h6750 h6776
  have p15956 := n15956 _v _q h6776
  have p21353 := n21353 _v _q h51 h91 h191 h2242 h3152 h4306 h4653 h4813 h4838 h6630 h6750 h6776
  have p4998 := n4998 _v _q h3152
  have p253 := n253 _v _q h191
  have p15946 := n15946 _v _q h2242
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4989 := n4989 _v _q h4838
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p15775 := n15775 _v _q h2242
  have p15949 := n15949 _v _q h2242
  have p20838 := n20838 _v _q h2242
  have p15952 := n15952 _v _q h2242
  simp only [e51, e57, e91, e95, e191, e192, e2468, e3152, e3156, e3158, e3159, e3919, e3920, e4096, e4097, e4139, e4140, e4260, e4261, e4285, e4286, e4306, e4311, e4419, e4420, e4439, e4444, e4459, e4464, e4567, e4572, e4653, e4658, e4679, e4684, e4813, e4814, e4838, e4839, e6630, e8045, e8048, e20877] at *
  tauto
theorem n21364 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2242 : (e2242 _v)) (h3152 : (e3152 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6630 : (e6630 _v)) (h6750 : (e6750 _v)) (h6776 : (e6776 _v)) : (e8049 _v) := by
  have p15206 := n15206 _v _q 
  have p21363 := n21363 _v _q h51 h91 h191 h2242 h3152 h4306 h4653 h4813 h4838 h6630 h6750 h6776
  simp only [e8043, e8045, e8047, e8048, e8049, e8490] at *
  tauto
theorem n21366 (_v : Vars) (_q : Query _v)  : (e21365 _v) := by
  by_contra hc
  change ¬ ((¬ (e2787 _v)) ∨ (¬ (e4285 _v)) ∨ (e2179 _v) ∨ (¬ (e4096 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4813 _v))) at hc
  have h51 : (e51 _v) := by
    tauto
  have h91 : (e91 _v) := by
    tauto
  have h191 : (e191 _v) := by
    tauto
  have h2787 : (e2787 _v) := by
    tauto
  have h3152 : (e3152 _v) := by
    tauto
  have h4096 : (e4096 _v) := by
    tauto
  have h4139 : (e4139 _v) := by
    tauto
  have h4260 : (e4260 _v) := by
    tauto
  have h4285 : (e4285 _v) := by
    tauto
  have h4306 : (e4306 _v) := by
    tauto
  have h4653 : (e4653 _v) := by
    tauto
  have h4675 : (e4675 _v) := by
    tauto
  have h4787 : (e4787 _v) := by
    tauto
  have h4813 : (e4813 _v) := by
    tauto
  have h4838 : (e4838 _v) := by
    tauto
  have h6501 : (e6501 _v) := by
    change (¬ (e2179 _v))
    tauto
  have p21354 := n21354 _v _q h51 h91 h191 h2787 h3152 h4096 h4139 h4260 h4285 h4306 h4653 h4675 h4787 h4813 h4838 h6501
  exact p21354
end
end Assembly
