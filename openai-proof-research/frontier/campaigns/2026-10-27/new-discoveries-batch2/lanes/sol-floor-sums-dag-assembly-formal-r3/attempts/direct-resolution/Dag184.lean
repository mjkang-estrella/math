import Dag183
import generated.th_lemma_20
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n18116 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2722 : (e2722 _v)) (h3133 : (e3133 _v)) (h3158 : (e3158 _v)) (h3919 : (e3919 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4101 : (e4101 _v)) (h4264 : (e4264 _v)) (h4306 : (e4306 _v)) (h4398 : (e4398 _v)) (h4439 : (e4439 _v)) (h4459 : (e4459 _v)) (h4491 : (e4491 _v)) (h4567 : (e4567 _v)) (h4653 : (e4653 _v)) (h4679 : (e4679 _v)) (h4724 : (e4724 _v)) (h4791 : (e4791 _v)) (h4817 : (e4817 _v)) (h4903 : (e4903 _v)) (h5195 : (e5195 _v)) : (e6575 _v) := by
  have p14695 := n14695 _v _q 
  have p18099 := n18099 _v _q h51 h2722 h3133 h3158 h3919 h3976 h4059 h4101 h4264 h4306 h4398 h4439 h4459 h4491 h4567 h4653 h4679 h4724 h4791 h4817 h4903 h5195
  simp only [e2351, e4161, e4162, e4166, e4167, e4168, e4169, e6575, e7674] at *
  tauto
theorem n18117 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2722 : (e2722 _v)) (h3133 : (e3133 _v)) (h3158 : (e3158 _v)) (h3919 : (e3919 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4101 : (e4101 _v)) (h4264 : (e4264 _v)) (h4306 : (e4306 _v)) (h4398 : (e4398 _v)) (h4439 : (e4439 _v)) (h4459 : (e4459 _v)) (h4491 : (e4491 _v)) (h4567 : (e4567 _v)) (h4653 : (e4653 _v)) (h4679 : (e4679 _v)) (h4724 : (e4724 _v)) (h4791 : (e4791 _v)) (h4817 : (e4817 _v)) (h4903 : (e4903 _v)) (h5195 : (e5195 _v)) : (e7489 _v) := by
  have p5255 := n5255 _v _q 
  have p5391 := n5391 _v _q 
  have p18116 := n18116 _v _q h51 h2722 h3133 h3158 h3919 h3976 h4059 h4101 h4264 h4306 h4398 h4439 h4459 h4491 h4567 h4653 h4679 h4724 h4791 h4817 h4903 h5195
  have p8410 := n8410 _v _q h2722
  have p5257 := n5257 _v _q 
  exact FloorCertificate.node_18117 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p5255 p5391 p18116 p8410 p5257
theorem n18119 (_v : Vars) (_q : Query _v)  : (e18118 _v) := by
  by_contra hc
  change ¬ ((¬ (e2722 _v)) ∨ (¬ (e4459 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e3919 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e3133 _v)) ∨ (¬ (e4491 _v)) ∨ (¬ (e4724 _v)) ∨ (¬ (e4567 _v)) ∨ (¬ (e4791 _v)) ∨ (¬ (e4398 _v)) ∨ (¬ (e4679 _v)) ∨ (¬ (e4817 _v)) ∨ (¬ (e4264 _v)) ∨ (e196 _v) ∨ (¬ (e4101 _v)) ∨ (¬ (e4903 _v)) ∨ (¬ (e4439 _v)) ∨ (¬ (e3976 _v)) ∨ (¬ (e3158 _v)) ∨ (¬ (e4306 _v))) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h2722 : (e2722 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h3133 : (e3133 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h3158 : (e3158 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))
  have h3919 : (e3919 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h3976 : (e3976 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))
  have h4059 : (e4059 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4101 : (e4101 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))
  have h4264 : (e4264 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))))))))))))))))))
  have h4398 : (e4398 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h4439 : (e4439 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))
  have h4459 : (e4459 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h4491 : (e4491 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h4567 : (e4567 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4679 : (e4679 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h4724 : (e4724 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h4791 : (e4791 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h4817 : (e4817 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h4903 : (e4903 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))
  have h5195 : (e5195 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))
  have p18117 := n18117 _v _q h51 h2722 h3133 h3158 h3919 h3976 h4059 h4101 h4264 h4306 h4398 h4439 h4459 h4491 h4567 h4653 h4679 h4724 h4791 h4817 h4903 h5195
  exact p18117
theorem n18120 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) : (e5145 _v) := by
  have p15925 := n15925 _v _q 
  have p15116 := n15116 _v _q h5362
  simp only [e5143, e5145, e5147, e5148, e5149, e5150, e5152] at *
  tauto
theorem n18121 (_v : Vars) (_q : Query _v) (h467 : (e467 _v)) (h2296 : (e2296 _v)) (h2522 : (e2522 _v)) (h3051 : (e3051 _v)) (h4161 : (e4161 _v)) (h4264 : (e4264 _v)) (h5237 : (e5237 _v)) (h5362 : (e5362 _v)) (h6742 : (e6742 _v)) : (e7489 _v) := by
  have p17093 := n17093 _v _q 
  have p4016 := n4016 _v _q 
  have p15083 := n15083 _v _q h2296
  have p18120 := n18120 _v _q h5362
  have p18103 := n18103 _v _q h467 h2296 h2522 h3051 h4161 h4264 h5362 h6742
  have p17246 := n17246 _v _q h5237
  have p15001 := n15001 _v _q h6742
  have p296 := n296 _v _q 
  have p15087 := n15087 _v _q h5362
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p17100 := n17100 _v _q 
  have p17102 := n17102 _v _q 
  have p18084 := n18084 _v _q h467 h2296 h2522 h3051 h4161 h4264 h5362 h6742
  have p17125 := n17125 _v _q h3051
  have p17104 := n17104 _v _q 
  have p17081 := n17081 _v _q h4161
  have p17096 := n17096 _v _q 
  have p17111 := n17111 _v _q 
  have p15094 := n15094 _v _q h2296
  have p17084 := n17084 _v _q h467
  have p17113 := n17113 _v _q 
  have p17946 := n17946 _v _q h2296
  have p17947 := n17947 _v _q h2296
  have p17955 := n17955 _v _q h2522
  have p15097 := n15097 _v _q h2296
  have p15100 := n15100 _v _q h2296
  have p17122 := n17122 _v _q 
  have p17117 := n17117 _v _q 
  have p17124 := n17124 _v _q 
  have p17115 := n17115 _v _q 
  have p17120 := n17120 _v _q 
  have p17948 := n17948 _v _q h2296
  have p17127 := n17127 _v _q 
  have p16778 := n16778 _v _q 
  have p17874 := n17874 _v _q 
  have p17131 := n17131 _v _q 
  have p17110 := n17110 _v _q 
  have p17133 := n17133 _v _q 
  have p17949 := n17949 _v _q h2296
  have p15102 := n15102 _v _q h2296
  have p17050 := n17050 _v _q 
  have p15122 := n15122 _v _q h2522
  have p17294 := n17294 _v _q 
  have p17136 := n17136 _v _q 
  have p17141 := n17141 _v _q 
  have p15107 := n15107 _v _q h2296
  have p15110 := n15110 _v _q h2296
  have p15125 := n15125 _v _q h2522
  have p17118 := n17118 _v _q h4264
  have p15113 := n15113 _v _q h2296
  have p17950 := n17950 _v _q h2296
  have p17053 := n17053 _v _q 
  have p17089 := n17089 _v _q 
  have p17055 := n17055 _v _q 
  have p17108 := n17108 _v _q 
  have p17951 := n17951 _v _q h2296
  have p17058 := n17058 _v _q 
  have p17952 := n17952 _v _q h2296
  have p17064 := n17064 _v _q 
  have p17067 := n17067 _v _q 
  have p17069 := n17069 _v _q 
  have p17072 := n17072 _v _q 
  have p17074 := n17074 _v _q 
  have p17078 := n17078 _v _q 
  have p17080 := n17080 _v _q 
  have p17083 := n17083 _v _q 
  have p15128 := n15128 _v _q h2522
  have p17087 := n17087 _v _q 
  have p17758 := n17758 _v _q 
  have p17091 := n17091 _v _q 
  exact FloorCertificate.node_18121 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) p17093 p4016 p15083 p18120 p18103 p17246 p15001 p296 p15087 p17098 p17106 p17100 p17102 p18084 p17125 p17104 p17081 p17096 p17111 p15094 p17084 p17113 p17946 p17947 p17955 p15097 p15100 p17122 p17117 p17124 p17115 p17120 p17948 p17127 p16778 p17874 p17131 p17110 p17133 p17949 p15102 p17050 p15122 p17294 p17136 p17141 p15107 p15110 p15125 p17118 p15113 p17950 p17053 p17089 p17055 p17108 p17951 p17058 p17952 p17064 p17067 p17069 p17072 p17074 p17078 p17080 p17083 p15128 p17087 p17758 p17091
theorem n18122 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2125 : (e2125 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3976 : (e3976 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h6700 : (e6700 _v)) (h8038 : (e8038 _v)) : (e192 _v) := by
  have p18105 := n18105 _v _q 
  have p8475 := n8475 _v _q h2125
  have p5001 := n5001 _v _q h4096
  have p11027 := n11027 _v _q h6700
  have p17129 := n17129 _v _q h4903
  have p17076 := n17076 _v _q h3976
  have p5007 := n5007 _v _q h225
  have p5008 := n5008 _v _q h4787
  have p4988 := n4988 _v _q h488
  have p4986 := n4986 _v _q h3105
  have p4983 := n4983 _v _q h4813
  have p4994 := n4994 _v _q h3069
  have p4984 := n4984 _v _q h4872
  have p4985 := n4985 _v _q h4156
  have p4998 := n4998 _v _q h3152
  have p4995 := n4995 _v _q h4369
  have p4996 := n4996 _v _q h3937
  have p5003 := n5003 _v _q h4199
  have p5006 := n5006 _v _q h4675
  have p5005 := n5005 _v _q h3169
  have p17143 := n17143 _v _q h4567
  have p5010 := n5010 _v _q h70
  have p4992 := n4992 _v _q h442
  have p4991 := n4991 _v _q h4608
  have p4999 := n4999 _v _q h91
  have p8602 := n8602 _v _q h8038
  have p4981 := n4981 _v _q h4260
  simp only [e70, e75, e91, e95, e191, e192, e225, e230, e442, e443, e488, e493, e2125, e2475, e2634, e3069, e3074, e3105, e3106, e3152, e3156, e3169, e3170, e3937, e3942, e3976, e3981, e4096, e4097, e4156, e4157, e4199, e4200, e4260, e4261, e4369, e4370, e4567, e4572, e4608, e4609, e4675, e4676, e4787, e4788, e4813, e4814, e4872, e4873, e4903, e4908, e6480, e6700, e8038, e18104] at *
  tauto
theorem n18123 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2125 : (e2125 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3976 : (e3976 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h6700 : (e6700 _v)) (h8038 : (e8038 _v)) : (e5193 _v) := by
  have p16442 := n16442 _v _q 
  have p18122 := n18122 _v _q h70 h91 h225 h442 h488 h2125 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4567 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  simp only [e191, e192, e193, e194, e5193, e5194] at *
  tauto
theorem n18124 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3855 : (e3855 _v)) (h3937 : (e3937 _v)) (h3976 : (e3976 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5093 : (e5093 _v)) (h6480 : (e6480 _v)) (h6700 : (e6700 _v)) (h7749 : (e7749 _v)) (h8045 : (e8045 _v)) : (e191 _v) := by
  have p16442 := n16442 _v _q 
  have p18111 := n18111 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3855 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4398 h4567 h4608 h4675 h4724 h4787 h4813 h4872 h4903 h5093 h6480 h6700 h7749 h8045
  simp only [e191, e192, e193, e194, e5193, e5194, e5203] at *
  tauto
theorem n18126 (_v : Vars) (_q : Query _v)  : (e18125 _v) := by
  by_contra hc
  change ¬ ((e2536 _v) ∨ (¬ (e4838 _v)) ∨ (¬ (e4301 _v)) ∨ (¬ (e7935 _v)) ∨ (e4567 _v) ∨ (e2475 _v) ∨ (¬ (e191 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e4903 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e3976 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e3169 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e2358 _v))) at hc
  have h70 : (e70 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h191 : (e191 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h225 : (e225 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))
  have h442 : (e442 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))
  have h488 : (e488 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))
  have h2358 : (e2358 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))))))))))))))))))))))))))
  have h3069 : (e3069 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))
  have h3105 : (e3105 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h3169 : (e3169 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h3976 : (e3976 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))
  have h4096 : (e4096 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h4156 : (e4156 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))
  have h4199 : (e4199 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h4260 : (e4260 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))
  have h4301 : (e4301 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4369 : (e4369 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h4572 : (e4572 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4608 : (e4608 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h4675 : (e4675 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))
  have h4838 : (e4838 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h4872 : (e4872 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))
  have h4903 : (e4903 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h6656 : (e6656 _v) := (fun hn => hc (Or.inl hn))
  have h7935 : (e7935 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h8038 : (e8038 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have p18113 := n18113 _v _q h70 h91 h191 h225 h442 h488 h2358 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4301 h4369 h4572 h4608 h4675 h4787 h4813 h4838 h4872 h4903 h6656 h7935 h8038
  exact p18113
theorem n18127 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2536 : (e2536 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3855 : (e3855 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4026 : (e4026 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4220 : (e4220 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4491 : (e4491 _v)) (h4546 : (e4546 _v)) (h4562 : (e4562 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) : (e2371 _v) := by
  have p18115 := n18115 _v _q 
  have p11132 := n11132 _v _q h2536
  have p4975 := n4975 _v _q h4026
  have p4971 := n4971 _v _q h4419
  have p4976 := n4976 _v _q h4546
  have p4972 := n4972 _v _q h4899
  have p17134 := n17134 _v _q h4398
  have p4978 := n4978 _v _q h4477
  have p4979 := n4979 _v _q h4139
  have p4980 := n4980 _v _q h4301
  have p5005 := n5005 _v _q h3169
  have p4973 := n4973 _v _q h4562
  have p4985 := n4985 _v _q h4156
  have p4987 := n4987 _v _q h4434
  have p4983 := n4983 _v _q h4813
  have p4988 := n4988 _v _q h488
  have p4981 := n4981 _v _q h4260
  have p4989 := n4989 _v _q h4838
  have p4986 := n4986 _v _q h3105
  have p253 := n253 _v _q h191
  have p4990 := n4990 _v _q h4648
  have p4984 := n4984 _v _q h4872
  have p4991 := n4991 _v _q h4608
  have p4992 := n4992 _v _q h442
  have p4977 := n4977 _v _q h4285
  have p4995 := n4995 _v _q h4369
  have p4994 := n4994 _v _q h3069
  have p4996 := n4996 _v _q h3937
  have p4999 := n4999 _v _q h91
  have p4998 := n4998 _v _q h3152
  have p16250 := n16250 _v _q h3855
  have p5001 := n5001 _v _q h4096
  have p5000 := n5000 _v _q h30
  have p17128 := n17128 _v _q h4491
  have p5003 := n5003 _v _q h4199
  have p5004 := n5004 _v _q h4220
  have p17076 := n17076 _v _q h3976
  have p17056 := n17056 _v _q h3946
  have p5007 := n5007 _v _q h225
  have p5008 := n5008 _v _q h4787
  have p17061 := n17061 _v _q h4747
  have p5010 := n5010 _v _q h70
  have p17137 := n17137 _v _q h4059
  have p5006 := n5006 _v _q h4675
  have p17094 := n17094 _v _q h4724
  simp only [e30, e35, e70, e75, e91, e95, e191, e192, e225, e230, e442, e443, e488, e493, e2371, e2536, e3069, e3074, e3105, e3106, e3152, e3156, e3169, e3170, e3855, e3860, e3937, e3942, e3946, e3947, e3976, e3981, e4026, e4031, e4059, e4064, e4096, e4097, e4139, e4140, e4156, e4157, e4199, e4200, e4220, e4221, e4260, e4261, e4285, e4286, e4301, e4302, e4369, e4370, e4398, e4403, e4419, e4420, e4434, e4435, e4477, e4481, e4491, e4496, e4546, e4547, e4562, e4563, e4608, e4609, e4648, e4649, e4675, e4676, e4724, e4729, e4747, e4752, e4787, e4788, e4813, e4814, e4838, e4839, e4872, e4873, e4899, e4900, e6656, e18114] at *
  tauto
theorem n18128 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3133 : (e3133 _v)) (h3158 : (e3158 _v)) (h3919 : (e3919 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4101 : (e4101 _v)) (h4264 : (e4264 _v)) (h4306 : (e4306 _v)) (h4398 : (e4398 _v)) (h4439 : (e4439 _v)) (h4459 : (e4459 _v)) (h4491 : (e4491 _v)) (h4567 : (e4567 _v)) (h4653 : (e4653 _v)) (h4679 : (e4679 _v)) (h4724 : (e4724 _v)) (h4791 : (e4791 _v)) (h4817 : (e4817 _v)) (h4903 : (e4903 _v)) (h5195 : (e5195 _v)) : (e6742 _v) := by
  have p18119 := n18119 _v _q 
  have p17079 := n17079 _v _q h3919
  have p17060 := n17060 _v _q h4653
  have p17137 := n17137 _v _q h4059
  have p17051 := n17051 _v _q h4459
  have p16729 := n16729 _v _q h51
  have p17062 := n17062 _v _q h3133
  have p17128 := n17128 _v _q h4491
  have p17094 := n17094 _v _q h4724
  have p17143 := n17143 _v _q h4567
  have p17059 := n17059 _v _q h4791
  have p17134 := n17134 _v _q h4398
  have p17070 := n17070 _v _q h4679
  have p17088 := n17088 _v _q h4817
  have p17118 := n17118 _v _q h4264
  have p8549 := n8549 _v _q h5195
  have p17065 := n17065 _v _q h4101
  have p17129 := n17129 _v _q h4903
  have p17075 := n17075 _v _q h4439
  have p17076 := n17076 _v _q h3976
  have p16885 := n16885 _v _q h3158
  have p17138 := n17138 _v _q h4306
  simp only [e51, e57, e196, e2722, e3133, e3138, e3158, e3159, e3919, e3920, e3976, e3981, e4059, e4064, e4101, e4106, e4264, e4269, e4306, e4311, e4398, e4403, e4439, e4444, e4459, e4464, e4491, e4496, e4567, e4572, e4653, e4658, e4679, e4684, e4724, e4729, e4791, e4796, e4817, e4822, e4903, e4908, e5195, e6742, e18118] at *
  tauto
theorem n18129 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3133 : (e3133 _v)) (h3158 : (e3158 _v)) (h3919 : (e3919 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4101 : (e4101 _v)) (h4264 : (e4264 _v)) (h4306 : (e4306 _v)) (h4398 : (e4398 _v)) (h4439 : (e4439 _v)) (h4459 : (e4459 _v)) (h4491 : (e4491 _v)) (h4567 : (e4567 _v)) (h4653 : (e4653 _v)) (h4679 : (e4679 _v)) (h4724 : (e4724 _v)) (h4791 : (e4791 _v)) (h4817 : (e4817 _v)) (h4903 : (e4903 _v)) (h5195 : (e5195 _v)) : (e8358 _v) := by
  have p14673 := n14673 _v _q 
  have p18128 := n18128 _v _q h51 h3133 h3158 h3919 h3976 h4059 h4101 h4264 h4306 h4398 h4439 h4459 h4491 h4567 h4653 h4679 h4724 h4791 h4817 h4903 h5195
  simp only [e2722, e4872, e4873, e4874, e4875, e6742, e8350, e8358, e8361] at *
  tauto
theorem n18131 (_v : Vars) (_q : Query _v)  : (e18130 _v) := by
  by_contra hc
  change ¬ ((¬ (e3051 _v)) ∨ (¬ (e5237 _v)) ∨ (¬ (e4161 _v)) ∨ (¬ (e467 _v)) ∨ (¬ (e4264 _v)) ∨ (¬ (e2522 _v)) ∨ (e2722 _v) ∨ (¬ (e2296 _v)) ∨ (e436 _v)) at hc
  have h467 : (e467 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h2296 : (e2296 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h2522 : (e2522 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h3051 : (e3051 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h4161 : (e4161 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4264 : (e4264 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h5237 : (e5237 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h5362 : (e5362 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn)))))))))
  have h6742 : (e6742 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have p18121 := n18121 _v _q h467 h2296 h2522 h3051 h4161 h4264 h5237 h5362 h6742
  exact p18121
theorem n18132 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2125 : (e2125 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3976 : (e3976 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h6700 : (e6700 _v)) (h8038 : (e8038 _v)) : (e5195 _v) := by
  have p14730 := n14730 _v _q 
  have p18123 := n18123 _v _q h70 h91 h225 h442 h488 h2125 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4567 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  simp only [e191, e192, e193, e194, e196, e5193, e5195, e5203, e5206] at *
  tauto
theorem n18133 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2125 : (e2125 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3976 : (e3976 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h6700 : (e6700 _v)) (h8038 : (e8038 _v)) : (e6571 _v) := by
  have p11357 := n11357 _v _q 
  have p18132 := n18132 _v _q h70 h91 h225 h442 h488 h2125 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4567 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  simp only [e196, e2358, e5195, e6571, e11356] at *
  tauto
theorem n18134 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2125 : (e2125 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3976 : (e3976 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h6700 : (e6700 _v)) (h8038 : (e8038 _v)) : (e6746 _v) := by
  have p18133 := n18133 _v _q h70 h91 h225 h442 h488 h2125 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4567 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  have p8602 := n8602 _v _q h8038
  have p4016 := n4016 _v _q 
  exact FloorCertificate.node_18134 (e2 _v) (e7 _v) (e9 _v) (e45 _v) (e110 _v) p18133 p8602 p4016
theorem n18135 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2125 : (e2125 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3976 : (e3976 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h6700 : (e6700 _v)) (h8038 : (e8038 _v)) : (e5221 _v) := by
  have p14732 := n14732 _v _q 
  have p18132 := n18132 _v _q h70 h91 h225 h442 h488 h2125 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4567 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  simp only [e196, e5195, e5208, e5211, e5218, e5219, e5220, e5221, e8668] at *
  tauto
theorem n18136 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2125 : (e2125 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3976 : (e3976 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h6700 : (e6700 _v)) (h8038 : (e8038 _v)) : (e5208 _v) := by
  have p8685 := n8685 _v _q 
  have p18135 := n18135 _v _q h70 h91 h225 h442 h488 h2125 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4567 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  simp only [e5208, e5211, e5218, e5219, e5220, e5221, e5258] at *
  tauto
theorem n18137 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2125 : (e2125 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3976 : (e3976 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h6700 : (e6700 _v)) (h8038 : (e8038 _v)) : (e7658 _v) := by
  have p15249 := n15249 _v _q 
  have p18133 := n18133 _v _q h70 h91 h225 h442 h488 h2125 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4567 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  simp only [e2358, e6571, e7645, e7648, e7655, e7656, e7657, e7658, e10960] at *
  tauto
theorem n18138 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2125 : (e2125 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3976 : (e3976 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h6700 : (e6700 _v)) (h8038 : (e8038 _v)) : (e2364 _v) := by
  have p18133 := n18133 _v _q h70 h91 h225 h442 h488 h2125 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4567 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  have p8663 := n8663 _v _q 
  exact FloorCertificate.node_18138 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e110 _v) p18133 p8663
theorem n18139 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2125 : (e2125 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3976 : (e3976 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h6700 : (e6700 _v)) (h8038 : (e8038 _v)) : (e2310 _v) := by
  have p8663 := n8663 _v _q 
  have p4016 := n4016 _v _q 
  have p18133 := n18133 _v _q h70 h91 h225 h442 h488 h2125 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4567 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  exact FloorCertificate.node_18139 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e110 _v) p8663 p4016 p18133
theorem n18140 (_v : Vars) (_q : Query _v) (h5093 : (e5093 _v)) : (e8335 _v) := by
  have p11421 := n11421 _v _q 
  have p15314 := n15314 _v _q h5093
  simp only [e8335, e8338, e8345, e8346, e8347, e8348, e8482] at *
  tauto
theorem n18141 (_v : Vars) (_q : Query _v) (h5093 : (e5093 _v)) : (e7688 _v) := by
  have p11450 := n11450 _v _q 
  have p15332 := n15332 _v _q h5093
  simp only [e7688, e7691, e7698, e7699, e7700, e7701, e8495] at *
  tauto
theorem n18142 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2740 : (e2740 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3855 : (e3855 _v)) (h3937 : (e3937 _v)) (h3976 : (e3976 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5093 : (e5093 _v)) (h6480 : (e6480 _v)) (h6555 : (e6555 _v)) (h6700 : (e6700 _v)) (h7749 : (e7749 _v)) (h8045 : (e8045 _v)) : (e4302 _v) := by
  have p17310 := n17310 _v _q 
  have p16371 := n16371 _v _q h6555
  have p16806 := n16806 _v _q h5093 h6480 h6555
  have p16378 := n16378 _v _q h2740
  have p16365 := n16365 _v _q h2740
  have p18140 := n18140 _v _q h5093
  have p18124 := n18124 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3855 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4398 h4567 h4608 h4675 h4724 h4787 h4813 h4872 h4903 h5093 h6480 h6700 h7749 h8045
  have p11027 := n11027 _v _q h6700
  have p16368 := n16368 _v _q h2740
  have p16381 := n16381 _v _q h2740
  have p4999 := n4999 _v _q h91
  have p17223 := n17223 _v _q h5093
  have p5001 := n5001 _v _q h4096
  have p18106 := n18106 _v _q h5093
  have p16807 := n16807 _v _q h2740
  have p5003 := n5003 _v _q h4199
  have p15321 := n15321 _v _q h5093
  have p17129 := n17129 _v _q h4903
  have p5006 := n5006 _v _q h4675
  have p17076 := n17076 _v _q h3976
  have p5007 := n5007 _v _q h225
  have p5008 := n5008 _v _q h4787
  have p5005 := n5005 _v _q h3169
  have p17143 := n17143 _v _q h4567
  have p5010 := n5010 _v _q h70
  have p4981 := n4981 _v _q h4260
  have p17157 := n17157 _v _q h8045
  have p18107 := n18107 _v _q h5093
  have p4988 := n4988 _v _q h488
  have p4986 := n4986 _v _q h3105
  have p4983 := n4983 _v _q h4813
  have p17094 := n17094 _v _q h4724
  have p4994 := n4994 _v _q h3069
  have p4992 := n4992 _v _q h442
  have p4984 := n4984 _v _q h4872
  have p4985 := n4985 _v _q h4156
  have p17134 := n17134 _v _q h4398
  have p4991 := n4991 _v _q h4608
  have p16250 := n16250 _v _q h3855
  have p15329 := n15329 _v _q h6555
  have p4998 := n4998 _v _q h3152
  have p4995 := n4995 _v _q h4369
  have p18108 := n18108 _v _q h5093
  have p4996 := n4996 _v _q h3937
  have p18109 := n18109 _v _q h5093
  have p15272 := n15272 _v _q h6480
  have p16269 := n16269 _v _q h7749
  have p18141 := n18141 _v _q h5093
  have p16384 := n16384 _v _q h6555
  simp only [e70, e75, e91, e95, e191, e192, e225, e230, e442, e443, e488, e493, e2634, e3069, e3074, e3105, e3106, e3152, e3156, e3169, e3170, e3267, e3268, e3585, e3589, e3855, e3860, e3937, e3942, e3946, e3947, e3976, e3981, e4059, e4064, e4096, e4097, e4128, e4133, e4139, e4140, e4156, e4157, e4199, e4200, e4260, e4261, e4285, e4286, e4301, e4302, e4369, e4370, e4398, e4403, e4419, e4420, e4434, e4435, e4477, e4481, e4491, e4496, e4567, e4572, e4608, e4609, e4648, e4649, e4675, e4676, e4724, e4729, e4747, e4752, e4787, e4788, e4813, e4814, e4838, e4839, e4872, e4873, e4903, e4908, e5100, e5103, e6700, e7493, e7494, e7688, e7698, e7749, e7752, e8045, e8048, e8335, e8345, e17309] at *
  tauto
theorem n18143 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2740 : (e2740 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3855 : (e3855 _v)) (h3937 : (e3937 _v)) (h3976 : (e3976 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5093 : (e5093 _v)) (h6480 : (e6480 _v)) (h6555 : (e6555 _v)) (h6700 : (e6700 _v)) (h7749 : (e7749 _v)) (h8045 : (e8045 _v)) : (e7822 _v) := by
  have p14840 := n14840 _v _q 
  have p18142 := n18142 _v _q h70 h91 h225 h442 h488 h2740 h3069 h3105 h3152 h3169 h3855 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4398 h4567 h4608 h4675 h4724 h4787 h4813 h4872 h4903 h5093 h6480 h6555 h6700 h7749 h8045
  simp only [e4301, e4302, e4303, e4304, e7822, e7823] at *
  tauto
theorem n18144 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3855 : (e3855 _v)) (h3937 : (e3937 _v)) (h3976 : (e3976 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5093 : (e5093 _v)) (h6480 : (e6480 _v)) (h6555 : (e6555 _v)) (h6700 : (e6700 _v)) (h6746 : (e6746 _v)) (h7749 : (e7749 _v)) (h8045 : (e8045 _v)) : (e2364 _v) := by
  have p17586 := n17586 _v _q 
  have p11362 := n11362 _v _q h6555
  have p11458 := n11458 _v _q h6746
  have p18140 := n18140 _v _q h5093
  have p18141 := n18141 _v _q h5093
  have p16806 := n16806 _v _q h5093 h6480 h6555
  have p4995 := n4995 _v _q h4369
  have p4996 := n4996 _v _q h3937
  have p16269 := n16269 _v _q h7749
  have p4998 := n4998 _v _q h3152
  have p15272 := n15272 _v _q h6480
  have p18124 := n18124 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3855 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4398 h4567 h4608 h4675 h4724 h4787 h4813 h4872 h4903 h5093 h6480 h6700 h7749 h8045
  have p18109 := n18109 _v _q h5093
  have p4999 := n4999 _v _q h91
  have p17223 := n17223 _v _q h5093
  have p5001 := n5001 _v _q h4096
  have p18108 := n18108 _v _q h5093
  have p18106 := n18106 _v _q h5093
  have p5003 := n5003 _v _q h4199
  have p15321 := n15321 _v _q h5093
  have p17129 := n17129 _v _q h4903
  have p5006 := n5006 _v _q h4675
  have p17076 := n17076 _v _q h3976
  have p5007 := n5007 _v _q h225
  have p5008 := n5008 _v _q h4787
  have p5005 := n5005 _v _q h3169
  have p17143 := n17143 _v _q h4567
  have p5010 := n5010 _v _q h70
  have p4981 := n4981 _v _q h4260
  have p17157 := n17157 _v _q h8045
  have p18107 := n18107 _v _q h5093
  have p4988 := n4988 _v _q h488
  have p4986 := n4986 _v _q h3105
  have p4983 := n4983 _v _q h4813
  have p17094 := n17094 _v _q h4724
  have p4994 := n4994 _v _q h3069
  have p4992 := n4992 _v _q h442
  have p4984 := n4984 _v _q h4872
  have p4985 := n4985 _v _q h4156
  have p17134 := n17134 _v _q h4398
  have p4991 := n4991 _v _q h4608
  have p16250 := n16250 _v _q h3855
  have p11027 := n11027 _v _q h6700
  have p4979 := n4979 _v _q h4139
  simp only [e70, e75, e91, e95, e191, e192, e225, e230, e442, e443, e488, e493, e2310, e2364, e2634, e2740, e3069, e3074, e3105, e3106, e3152, e3156, e3169, e3170, e3855, e3860, e3937, e3942, e3946, e3947, e3976, e3981, e4059, e4064, e4096, e4097, e4139, e4140, e4156, e4157, e4199, e4200, e4260, e4261, e4369, e4370, e4398, e4403, e4434, e4435, e4477, e4481, e4491, e4496, e4567, e4572, e4608, e4609, e4675, e4676, e4724, e4729, e4747, e4752, e4787, e4788, e4813, e4814, e4872, e4873, e4903, e4908, e5100, e5103, e6555, e6700, e6746, e7493, e7494, e7688, e7698, e7749, e7752, e8045, e8048, e8335, e8345, e17585] at *
  tauto
theorem n18145 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3855 : (e3855 _v)) (h3937 : (e3937 _v)) (h3976 : (e3976 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5093 : (e5093 _v)) (h6480 : (e6480 _v)) (h6555 : (e6555 _v)) (h6700 : (e6700 _v)) (h6746 : (e6746 _v)) (h7749 : (e7749 _v)) (h8045 : (e8045 _v)) : (e7489 _v) := by
  have p4016 := n4016 _v _q 
  have p18144 := n18144 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3855 h3937 h3976 h4096 h4139 h4156 h4199 h4260 h4369 h4398 h4567 h4608 h4675 h4724 h4787 h4813 h4872 h4903 h5093 h6480 h6555 h6700 h6746 h7749 h8045
  have p11362 := n11362 _v _q h6555
  exact FloorCertificate.node_18145 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e110 _v) p4016 p18144 p11362
theorem n18146 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2536 : (e2536 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3855 : (e3855 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4026 : (e4026 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4220 : (e4220 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4491 : (e4491 _v)) (h4546 : (e4546 _v)) (h4562 : (e4562 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) : (e5018 _v) := by
  have p14714 := n14714 _v _q 
  have p18127 := n18127 _v _q h30 h70 h91 h191 h225 h442 h488 h2536 h3069 h3105 h3152 h3169 h3855 h3937 h3946 h3976 h4026 h4059 h4096 h4139 h4156 h4199 h4220 h4260 h4285 h4301 h4369 h4398 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4724 h4747 h4787 h4813 h4838 h4872 h4899
  simp only [e2371, e5018, e6579, e8500] at *
  tauto
theorem n18147 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3133 : (e3133 _v)) (h3158 : (e3158 _v)) (h3919 : (e3919 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4101 : (e4101 _v)) (h4264 : (e4264 _v)) (h4306 : (e4306 _v)) (h4398 : (e4398 _v)) (h4439 : (e4439 _v)) (h4459 : (e4459 _v)) (h4491 : (e4491 _v)) (h4567 : (e4567 _v)) (h4653 : (e4653 _v)) (h4679 : (e4679 _v)) (h4724 : (e4724 _v)) (h4791 : (e4791 _v)) (h4817 : (e4817 _v)) (h4903 : (e4903 _v)) (h5195 : (e5195 _v)) : (e4872 _v) := by
  have p14999 := n14999 _v _q 
  have p18129 := n18129 _v _q h51 h3133 h3158 h3919 h3976 h4059 h4101 h4264 h4306 h4398 h4439 h4459 h4491 h4567 h4653 h4679 h4724 h4791 h4817 h4903 h5195
  simp only [e4872, e4873, e4874, e4875, e8350, e8351, e8358] at *
  tauto
theorem n18148 (_v : Vars) (_q : Query _v) (h474 : (e474 _v)) (h2296 : (e2296 _v)) (h2522 : (e2522 _v)) (h4264 : (e4264 _v)) (h5237 : (e5237 _v)) (h5362 : (e5362 _v)) (h6742 : (e6742 _v)) : (e3052 _v) := by
  have p18131 := n18131 _v _q 
  have p17246 := n17246 _v _q h5237
  have p15131 := n15131 _v _q h474
  have p15133 := n15133 _v _q h474
  have p17118 := n17118 _v _q h4264
  have p12831 := n12831 _v _q h2522
  have p8416 := n8416 _v _q h6742
  have p8583 := n8583 _v _q h2296
  have p7488 := n7488 _v _q h5362
  simp only [e436, e467, e468, e2296, e2522, e2722, e3051, e3052, e4161, e4166, e4264, e4269, e5237, e5247, e5362, e6549, e6650, e6742, e18130] at *
  tauto
theorem n18149 (_v : Vars) (_q : Query _v) (h474 : (e474 _v)) (h2296 : (e2296 _v)) (h2522 : (e2522 _v)) (h4264 : (e4264 _v)) (h5237 : (e5237 _v)) (h5362 : (e5362 _v)) (h6742 : (e6742 _v)) : (e3055 _v) := by
  have p14764 := n14764 _v _q 
  have p18148 := n18148 _v _q h474 h2296 h2522 h4264 h5237 h5362 h6742
  simp only [e3051, e3052, e3053, e3054, e3055, e3056] at *
  tauto
theorem n18150 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2125 : (e2125 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3976 : (e3976 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h6700 : (e6700 _v)) (h8038 : (e8038 _v)) : (e7630 _v) := by
  have p15152 := n15152 _v _q 
  have p18134 := n18134 _v _q h70 h91 h225 h442 h488 h2125 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4567 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  simp only [e2740, e6746, e7606, e7607, e7608, e7609, e7610, e7630, e10951] at *
  tauto
theorem n18151 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2125 : (e2125 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3976 : (e3976 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h6700 : (e6700 _v)) (h8038 : (e8038 _v)) : (e7606 _v) := by
  have p11418 := n11418 _v _q 
  have p18150 := n18150 _v _q h70 h91 h225 h442 h488 h2125 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4567 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  simp only [e7606, e7607, e7608, e7609, e7610, e7611, e7630] at *
  tauto
theorem n18152 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2740 : (e2740 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3855 : (e3855 _v)) (h3937 : (e3937 _v)) (h3976 : (e3976 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5093 : (e5093 _v)) (h6480 : (e6480 _v)) (h6555 : (e6555 _v)) (h6700 : (e6700 _v)) (h7749 : (e7749 _v)) (h8045 : (e8045 _v)) : (e2585 _v) := by
  have p14579 := n14579 _v _q 
  have p18143 := n18143 _v _q h70 h91 h225 h442 h488 h2740 h3069 h3105 h3152 h3169 h3855 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4398 h4567 h4608 h4675 h4724 h4787 h4813 h4872 h4903 h5093 h6480 h6555 h6700 h7749 h8045
  simp only [e2585, e4301, e4302, e4303, e4304, e7822, e7830, e7833] at *
  tauto
theorem n18153 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2740 : (e2740 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3855 : (e3855 _v)) (h3937 : (e3937 _v)) (h3976 : (e3976 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5093 : (e5093 _v)) (h6480 : (e6480 _v)) (h6555 : (e6555 _v)) (h6700 : (e6700 _v)) (h7749 : (e7749 _v)) (h8045 : (e8045 _v)) : (e4314 _v) := by
  have p14704 := n14704 _v _q 
  have p18152 := n18152 _v _q h70 h91 h225 h442 h488 h2740 h3069 h3105 h3152 h3169 h3855 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4398 h4567 h4608 h4675 h4724 h4787 h4813 h4872 h4903 h5093 h6480 h6555 h6700 h7749 h8045
  simp only [e2585, e4306, e4307, e4311, e4312, e4313, e4314, e6676, e7836] at *
  tauto
theorem n18154 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2740 : (e2740 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3855 : (e3855 _v)) (h3937 : (e3937 _v)) (h3976 : (e3976 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5093 : (e5093 _v)) (h6480 : (e6480 _v)) (h6555 : (e6555 _v)) (h6700 : (e6700 _v)) (h7749 : (e7749 _v)) (h8045 : (e8045 _v)) : (e4306 _v) := by
  have p14984 := n14984 _v _q 
  have p18153 := n18153 _v _q h70 h91 h225 h442 h488 h2740 h3069 h3105 h3152 h3169 h3855 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4398 h4567 h4608 h4675 h4724 h4787 h4813 h4872 h4903 h5093 h6480 h6555 h6700 h7749 h8045
  simp only [e4306, e4307, e4311, e4312, e4313, e4314, e4964] at *
  tauto
theorem n18155 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2740 : (e2740 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3855 : (e3855 _v)) (h3937 : (e3937 _v)) (h3976 : (e3976 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5093 : (e5093 _v)) (h6480 : (e6480 _v)) (h6555 : (e6555 _v)) (h6700 : (e6700 _v)) (h7749 : (e7749 _v)) (h8045 : (e8045 _v)) : (e7489 _v) := by
  have p11027 := n11027 _v _q h6700
  have p11440 := n11440 _v _q h5093
  have p331 := n331 _v _q 
  have p4016 := n4016 _v _q 
  have p11362 := n11362 _v _q h6555
  have p11426 := n11426 _v _q h2740
  have p16181 := n16181 _v _q 
  have p16371 := n16371 _v _q h6555
  have p18154 := n18154 _v _q h70 h91 h225 h442 h488 h2740 h3069 h3105 h3152 h3169 h3855 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4398 h4567 h4608 h4675 h4724 h4787 h4813 h4872 h4903 h5093 h6480 h6555 h6700 h7749 h8045
  have p16269 := n16269 _v _q h7749
  have p16806 := n16806 _v _q h5093 h6480 h6555
  have p16365 := n16365 _v _q h2740
  have p15272 := n15272 _v _q h6480
  have p16384 := n16384 _v _q h6555
  have p16378 := n16378 _v _q h2740
  have p16178 := n16178 _v _q 
  have p18124 := n18124 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3855 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4398 h4567 h4608 h4675 h4724 h4787 h4813 h4872 h4903 h5093 h6480 h6700 h7749 h8045
  have p18141 := n18141 _v _q h5093
  have p16368 := n16368 _v _q h2740
  have p16381 := n16381 _v _q h2740
  have p4999 := n4999 _v _q h91
  have p17055 := n17055 _v _q 
  have p16929 := n16929 _v _q 
  have p17223 := n17223 _v _q h5093
  have p5001 := n5001 _v _q h4096
  have p17136 := n17136 _v _q 
  have p17127 := n17127 _v _q 
  have p18106 := n18106 _v _q h5093
  have p16807 := n16807 _v _q h2740
  have p5003 := n5003 _v _q h4199
  have p15321 := n15321 _v _q h5093
  have p17129 := n17129 _v _q h4903
  have p5006 := n5006 _v _q h4675
  have p17076 := n17076 _v _q h3976
  have p17147 := n17147 _v _q 
  have p5007 := n5007 _v _q h225
  have p5008 := n5008 _v _q h4787
  have p17133 := n17133 _v _q 
  have p5005 := n5005 _v _q h3169
  have p17143 := n17143 _v _q h4567
  have p5010 := n5010 _v _q h70
  have p4981 := n4981 _v _q h4260
  have p17157 := n17157 _v _q h8045
  have p18107 := n18107 _v _q h5093
  have p4988 := n4988 _v _q h488
  have p4986 := n4986 _v _q h3105
  have p16175 := n16175 _v _q 
  have p4983 := n4983 _v _q h4813
  have p17094 := n17094 _v _q h4724
  have p4994 := n4994 _v _q h3069
  have p4992 := n4992 _v _q h442
  have p4984 := n4984 _v _q h4872
  have p4985 := n4985 _v _q h4156
  have p17080 := n17080 _v _q 
  have p17134 := n17134 _v _q h4398
  have p17074 := n17074 _v _q 
  have p17078 := n17078 _v _q 
  have p17072 := n17072 _v _q 
  have p17098 := n17098 _v _q 
  have p17091 := n17091 _v _q 
  have p17087 := n17087 _v _q 
  have p17115 := n17115 _v _q 
  have p17110 := n17110 _v _q 
  have p17067 := n17067 _v _q 
  have p17100 := n17100 _v _q 
  have p4991 := n4991 _v _q h4608
  have p17058 := n17058 _v _q 
  have p17083 := n17083 _v _q 
  have p16576 := n16576 _v _q 
  have p17113 := n17113 _v _q 
  have p17064 := n17064 _v _q 
  have p17102 := n17102 _v _q 
  have p16250 := n16250 _v _q h3855
  have p17096 := n17096 _v _q 
  have p17122 := n17122 _v _q 
  have p17108 := n17108 _v _q 
  have p17124 := n17124 _v _q 
  have p15329 := n15329 _v _q h6555
  have p17117 := n17117 _v _q 
  have p17104 := n17104 _v _q 
  have p17131 := n17131 _v _q 
  have p17106 := n17106 _v _q 
  have p4998 := n4998 _v _q h3152
  have p4995 := n4995 _v _q h4369
  have p17120 := n17120 _v _q 
  have p17069 := n17069 _v _q 
  have p18108 := n18108 _v _q h5093
  have p4996 := n4996 _v _q h3937
  have p17141 := n17141 _v _q 
  have p17093 := n17093 _v _q 
  have p17053 := n17053 _v _q 
  have p18109 := n18109 _v _q h5093
  have p13951 := n13951 _v _q 
  exact FloorCertificate.node_18155 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e61 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2849 _v) (e2863 _v) (e2877 _v) (e2879 _v) (e2883 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e3164 _v) (e3262 _v) (e3574 _v) (e4215 _v) (e4541 _v) (e4808 _v) p11027 p11440 p331 p4016 p11362 p11426 p16181 p16371 p18154 p16269 p16806 p16365 p15272 p16384 p16378 p16178 p18124 p18141 p16368 p16381 p4999 p17055 p16929 p17223 p5001 p17136 p17127 p18106 p16807 p5003 p15321 p17129 p5006 p17076 p17147 p5007 p5008 p17133 p5005 p17143 p5010 p4981 p17157 p18107 p4988 p4986 p16175 p4983 p17094 p4994 p4992 p4984 p4985 p17080 p17134 p17074 p17078 p17072 p17098 p17091 p17087 p17115 p17110 p17067 p17100 p4991 p17058 p17083 p16576 p17113 p17064 p17102 p16250 p17096 p17122 p17108 p17124 p15329 p17117 p17104 p17131 p17106 p4998 p4995 p17120 p17069 p18108 p4996 p17141 p17093 p17053 p18109 p13951
theorem n18157 (_v : Vars) (_q : Query _v)  : (e18156 _v) := by
  by_contra hc
  change ¬ ((e2310 _v) ∨ (e2740 _v) ∨ (¬ (e4369 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e7749 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e4903 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e3976 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e3169 _v)) ∨ (¬ (e4567 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e8045 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4724 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e4398 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e3855 _v)) ∨ (e2634 _v) ∨ (¬ (e4139 _v)) ∨ (e13 _v) ∨ (e2125 _v)) at hc
  have h70 : (e70 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h225 : (e225 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h442 : (e442 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))
  have h488 : (e488 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))
  have h3069 : (e3069 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))
  have h3105 : (e3105 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h3169 : (e3169 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h3855 : (e3855 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h3976 : (e3976 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h4096 : (e4096 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h4139 : (e4139 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))))
  have h4156 : (e4156 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))
  have h4199 : (e4199 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h4260 : (e4260 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))
  have h4369 : (e4369 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4398 : (e4398 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))
  have h4567 : (e4567 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))
  have h4608 : (e4608 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))
  have h4675 : (e4675 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h4724 : (e4724 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))
  have h4872 : (e4872 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))
  have h4903 : (e4903 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h5093 : (e5093 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))))
  have h6480 : (e6480 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))))))))))))))))))))))))))))))
  have h6555 : (e6555 _v) := (fun hn => hc (Or.inl hn))
  have h6700 : (e6700 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))
  have h6746 : (e6746 _v) := (fun hn => hc (Or.inr (Or.inl hn)))
  have h7749 : (e7749 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h8045 : (e8045 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))
  have p18145 := n18145 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3855 h3937 h3976 h4096 h4139 h4156 h4199 h4260 h4369 h4398 h4567 h4608 h4675 h4724 h4787 h4813 h4872 h4903 h5093 h6480 h6555 h6700 h6746 h7749 h8045
  exact p18145
theorem n18158 (_v : Vars) (_q : Query _v) (h2536 : (e2536 _v)) : (e2482 _v) := by
  have p5257 := n5257 _v _q 
  have p11132 := n11132 _v _q h2536
  exact FloorCertificate.node_18158 (e2 _v) (e7 _v) (e17 _v) (e45 _v) (e110 _v) p5257 p11132
theorem n18159 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2536 : (e2536 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3855 : (e3855 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4026 : (e4026 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4220 : (e4220 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4491 : (e4491 _v)) (h4546 : (e4546 _v)) (h4562 : (e4562 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) : (e2634 _v) := by
  have p17424 := n17424 _v _q 
  have p18127 := n18127 _v _q h30 h70 h91 h191 h225 h442 h488 h2536 h3069 h3105 h3152 h3169 h3855 h3937 h3946 h3976 h4026 h4059 h4096 h4139 h4156 h4199 h4220 h4260 h4285 h4301 h4369 h4398 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4724 h4747 h4787 h4813 h4838 h4872 h4899
  have p17831 := n17831 _v _q h30 h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3855 h3937 h3946 h3976 h4026 h4059 h4096 h4139 h4156 h4199 h4220 h4260 h4285 h4301 h4369 h4398 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4724 h4747 h4787 h4813 h4838 h4872 h4899
  have p5005 := n5005 _v _q h3169
  have p15448 := n15448 _v _q h2536
  have p4988 := n4988 _v _q h488
  have p4989 := n4989 _v _q h4838
  have p253 := n253 _v _q h191
  have p4990 := n4990 _v _q h4648
  have p4991 := n4991 _v _q h4608
  have p4992 := n4992 _v _q h442
  have p4975 := n4975 _v _q h4026
  have p4995 := n4995 _v _q h4369
  have p4994 := n4994 _v _q h3069
  have p17134 := n17134 _v _q h4398
  have p4996 := n4996 _v _q h3937
  have p4999 := n4999 _v _q h91
  have p4998 := n4998 _v _q h3152
  have p16250 := n16250 _v _q h3855
  have p5001 := n5001 _v _q h4096
  have p5000 := n5000 _v _q h30
  have p17128 := n17128 _v _q h4491
  have p5003 := n5003 _v _q h4199
  have p5004 := n5004 _v _q h4220
  have p17076 := n17076 _v _q h3976
  have p17056 := n17056 _v _q h3946
  have p5007 := n5007 _v _q h225
  have p5008 := n5008 _v _q h4787
  have p15183 := n15183 _v _q h2536
  have p17061 := n17061 _v _q h4747
  have p5010 := n5010 _v _q h70
  have p17137 := n17137 _v _q h4059
  have p5006 := n5006 _v _q h4675
  have p17094 := n17094 _v _q h4724
  have p4971 := n4971 _v _q h4419
  have p4972 := n4972 _v _q h4899
  have p4973 := n4973 _v _q h4562
  have p4976 := n4976 _v _q h4546
  have p4977 := n4977 _v _q h4285
  have p4978 := n4978 _v _q h4477
  have p4979 := n4979 _v _q h4139
  have p4980 := n4980 _v _q h4301
  have p4981 := n4981 _v _q h4260
  have p4983 := n4983 _v _q h4813
  have p4984 := n4984 _v _q h4872
  have p4985 := n4985 _v _q h4156
  have p4986 := n4986 _v _q h3105
  have p4987 := n4987 _v _q h4434
  have p18158 := n18158 _v _q h2536
  simp only [e30, e35, e70, e75, e91, e95, e191, e192, e225, e230, e442, e443, e488, e493, e2310, e2371, e2482, e2634, e3069, e3074, e3105, e3106, e3152, e3156, e3169, e3170, e3566, e3571, e3855, e3860, e3937, e3942, e3946, e3947, e3976, e3981, e4026, e4031, e4059, e4064, e4096, e4097, e4139, e4140, e4156, e4157, e4199, e4200, e4220, e4221, e4260, e4261, e4285, e4286, e4301, e4302, e4369, e4370, e4398, e4403, e4419, e4420, e4434, e4435, e4477, e4481, e4491, e4496, e4546, e4547, e4562, e4563, e4608, e4609, e4648, e4649, e4675, e4676, e4724, e4729, e4747, e4752, e4787, e4788, e4813, e4814, e4838, e4839, e4872, e4873, e4899, e4900, e6555, e6579, e6636, e8398, e8406, e17423] at *
  tauto
theorem n18160 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2536 : (e2536 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3855 : (e3855 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4026 : (e4026 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4220 : (e4220 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4491 : (e4491 _v)) (h4546 : (e4546 _v)) (h4562 : (e4562 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) : (e7489 _v) := by
  have p17432 := n17432 _v _q 
  have p18146 := n18146 _v _q h30 h70 h91 h191 h225 h442 h488 h2536 h3069 h3105 h3152 h3169 h3855 h3937 h3946 h3976 h4026 h4059 h4096 h4139 h4156 h4199 h4220 h4260 h4285 h4301 h4369 h4398 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4724 h4747 h4787 h4813 h4838 h4872 h4899
  have p18127 := n18127 _v _q h30 h70 h91 h191 h225 h442 h488 h2536 h3069 h3105 h3152 h3169 h3855 h3937 h3946 h3976 h4026 h4059 h4096 h4139 h4156 h4199 h4220 h4260 h4285 h4301 h4369 h4398 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4724 h4747 h4787 h4813 h4838 h4872 h4899
  have p4989 := n4989 _v _q h4838
  have p17831 := n17831 _v _q h30 h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3855 h3937 h3946 h3976 h4026 h4059 h4096 h4139 h4156 h4199 h4220 h4260 h4285 h4301 h4369 h4398 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4724 h4747 h4787 h4813 h4838 h4872 h4899
  have p253 := n253 _v _q h191
  have p4990 := n4990 _v _q h4648
  have p4991 := n4991 _v _q h4608
  have p4992 := n4992 _v _q h442
  have p4975 := n4975 _v _q h4026
  have p15183 := n15183 _v _q h2536
  have p4995 := n4995 _v _q h4369
  have p4994 := n4994 _v _q h3069
  have p17134 := n17134 _v _q h4398
  have p4996 := n4996 _v _q h3937
  have p4999 := n4999 _v _q h91
  have p4998 := n4998 _v _q h3152
  have p16250 := n16250 _v _q h3855
  have p5001 := n5001 _v _q h4096
  have p5000 := n5000 _v _q h30
  have p17128 := n17128 _v _q h4491
  have p5003 := n5003 _v _q h4199
  have p5004 := n5004 _v _q h4220
  have p17076 := n17076 _v _q h3976
  have p17056 := n17056 _v _q h3946
  have p5007 := n5007 _v _q h225
  have p5008 := n5008 _v _q h4787
  have p18158 := n18158 _v _q h2536
  have p17061 := n17061 _v _q h4747
  have p5010 := n5010 _v _q h70
  have p17137 := n17137 _v _q h4059
  have p5006 := n5006 _v _q h4675
  have p17094 := n17094 _v _q h4724
  have p4971 := n4971 _v _q h4419
  have p4972 := n4972 _v _q h4899
  have p4973 := n4973 _v _q h4562
  have p15450 := n15450 _v _q h2536
  have p4976 := n4976 _v _q h4546
  have p4977 := n4977 _v _q h4285
  have p4978 := n4978 _v _q h4477
  have p4979 := n4979 _v _q h4139
  have p4980 := n4980 _v _q h4301
  have p4981 := n4981 _v _q h4260
  have p4983 := n4983 _v _q h4813
  have p4984 := n4984 _v _q h4872
  have p4985 := n4985 _v _q h4156
  have p4986 := n4986 _v _q h3105
  have p4987 := n4987 _v _q h4434
  have p4988 := n4988 _v _q h488
  have p18159 := n18159 _v _q h30 h70 h91 h191 h225 h442 h488 h2536 h3069 h3105 h3152 h3169 h3855 h3937 h3946 h3976 h4026 h4059 h4096 h4139 h4156 h4199 h4220 h4260 h4285 h4301 h4369 h4398 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4724 h4747 h4787 h4813 h4838 h4872 h4899
  simp only [e30, e35, e70, e75, e91, e95, e191, e192, e225, e230, e442, e443, e488, e493, e2371, e2482, e2634, e3069, e3074, e3105, e3106, e3152, e3156, e3271, e3276, e3566, e3571, e3855, e3860, e3937, e3942, e3946, e3947, e3976, e3981, e4026, e4031, e4059, e4064, e4096, e4097, e4139, e4140, e4156, e4157, e4199, e4200, e4220, e4221, e4260, e4261, e4285, e4286, e4301, e4302, e4369, e4370, e4398, e4403, e4419, e4420, e4434, e4435, e4477, e4481, e4491, e4496, e4546, e4547, e4562, e4563, e4608, e4609, e4648, e4649, e4675, e4676, e4724, e4729, e4747, e4752, e4787, e4788, e4813, e4814, e4838, e4839, e4872, e4873, e4899, e4900, e5018, e5020, e6579, e6636, e6700, e8398, e8406, e17431] at *
  tauto
theorem n18161 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h251 : (e251 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3133 : (e3133 _v)) (h3158 : (e3158 _v)) (h3919 : (e3919 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4101 : (e4101 _v)) (h4156 : (e4156 _v)) (h4264 : (e4264 _v)) (h4306 : (e4306 _v)) (h4398 : (e4398 _v)) (h4439 : (e4439 _v)) (h4459 : (e4459 _v)) (h4491 : (e4491 _v)) (h4567 : (e4567 _v)) (h4653 : (e4653 _v)) (h4679 : (e4679 _v)) (h4724 : (e4724 _v)) (h4791 : (e4791 _v)) (h4817 : (e4817 _v)) (h4903 : (e4903 _v)) (h5195 : (e5195 _v)) (h5237 : (e5237 _v)) : (e7724 _v) := by
  have p17256 := n17256 _v _q 
  have p4994 := n4994 _v _q h3069
  have p4985 := n4985 _v _q h4156
  have p5257 := n5257 _v _q 
  have p17246 := n17246 _v _q h5237
  have p5255 := n5255 _v _q 
  have p12839 := n12839 _v _q h5195
  have p17953 := n17953 _v _q 
  have p17075 := n17075 _v _q h4439
  have p4988 := n4988 _v _q h488
  have p17058 := n17058 _v _q 
  have p17076 := n17076 _v _q h3976
  have p17064 := n17064 _v _q 
  have p17067 := n17067 _v _q 
  have p17069 := n17069 _v _q 
  have p17072 := n17072 _v _q 
  have p4992 := n4992 _v _q h442
  have p15119 := n15119 _v _q h251
  have p17078 := n17078 _v _q 
  have p17080 := n17080 _v _q 
  have p17083 := n17083 _v _q 
  have p17074 := n17074 _v _q 
  have p17087 := n17087 _v _q 
  have p17758 := n17758 _v _q 
  have p17091 := n17091 _v _q 
  have p17093 := n17093 _v _q 
  have p18147 := n18147 _v _q h51 h3133 h3158 h3919 h3976 h4059 h4101 h4264 h4306 h4398 h4439 h4459 h4491 h4567 h4653 h4679 h4724 h4791 h4817 h4903 h5195
  have p17138 := n17138 _v _q h4306
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p17100 := n17100 _v _q 
  have p17102 := n17102 _v _q 
  have p16885 := n16885 _v _q h3158
  have p17104 := n17104 _v _q 
  have p17096 := n17096 _v _q 
  have p17111 := n17111 _v _q 
  have p17051 := n17051 _v _q h4459
  have p17113 := n17113 _v _q 
  have p17060 := n17060 _v _q h4653
  have p17137 := n17137 _v _q h4059
  have p17079 := n17079 _v _q h3919
  have p16729 := n16729 _v _q h51
  have p17062 := n17062 _v _q h3133
  have p17122 := n17122 _v _q 
  have p17117 := n17117 _v _q 
  have p17124 := n17124 _v _q 
  have p17115 := n17115 _v _q 
  have p17120 := n17120 _v _q 
  have p17128 := n17128 _v _q h4491
  have p17127 := n17127 _v _q 
  have p16778 := n16778 _v _q 
  have p17874 := n17874 _v _q 
  have p17131 := n17131 _v _q 
  have p17110 := n17110 _v _q 
  have p17133 := n17133 _v _q 
  have p17094 := n17094 _v _q h4724
  have p17143 := n17143 _v _q h4567
  have p17050 := n17050 _v _q 
  have p17059 := n17059 _v _q h4791
  have p17294 := n17294 _v _q 
  have p17136 := n17136 _v _q 
  have p17141 := n17141 _v _q 
  have p17134 := n17134 _v _q h4398
  have p17070 := n17070 _v _q h4679
  have p17088 := n17088 _v _q h4817
  have p17118 := n17118 _v _q h4264
  have p17065 := n17065 _v _q h4101
  have p17129 := n17129 _v _q h4903
  have p17053 := n17053 _v _q 
  have p17089 := n17089 _v _q 
  have p17055 := n17055 _v _q 
  have p17108 := n17108 _v _q 
  have p13951 := n13951 _v _q 
  have p11374 := n11374 _v _q h251
  exact FloorCertificate.node_18161 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2902 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) p17256 p4994 p4985 p5257 p17246 p5255 p12839 p17953 p17075 p4988 p17058 p17076 p17064 p17067 p17069 p17072 p4992 p15119 p17078 p17080 p17083 p17074 p17087 p17758 p17091 p17093 p18147 p17138 p17098 p17106 p17100 p17102 p16885 p17104 p17096 p17111 p17051 p17113 p17060 p17137 p17079 p16729 p17062 p17122 p17117 p17124 p17115 p17120 p17128 p17127 p16778 p17874 p17131 p17110 p17133 p17094 p17143 p17050 p17059 p17294 p17136 p17141 p17134 p17070 p17088 p17118 p17065 p17129 p17053 p17089 p17055 p17108 p13951 p11374
theorem n18162 (_v : Vars) (_q : Query _v) (h474 : (e474 _v)) (h2296 : (e2296 _v)) (h2522 : (e2522 _v)) (h4264 : (e4264 _v)) (h5237 : (e5237 _v)) (h5362 : (e5362 _v)) (h6742 : (e6742 _v)) : (e6720 _v) := by
  have p14350 := n14350 _v _q 
  have p18149 := n18149 _v _q h474 h2296 h2522 h4264 h5237 h5362 h6742
  simp only [e496, e3051, e3052, e3053, e3054, e3055, e3061, e6720, e6836] at *
  tauto
theorem n18163 (_v : Vars) (_q : Query _v) (h474 : (e474 _v)) (h2296 : (e2296 _v)) (h2522 : (e2522 _v)) (h4264 : (e4264 _v)) (h5237 : (e5237 _v)) (h5362 : (e5362 _v)) (h6742 : (e6742 _v)) : (e6830 _v) := by
  have p14629 := n14629 _v _q 
  have p18162 := n18162 _v _q h474 h2296 h2522 h4264 h5237 h5362 h6742
  simp only [e496, e3069, e3071, e3074, e3075, e6720, e6829, e6830, e6833] at *
  tauto
theorem n18164 (_v : Vars) (_q : Query _v) (h474 : (e474 _v)) (h2296 : (e2296 _v)) (h2522 : (e2522 _v)) (h4264 : (e4264 _v)) (h5237 : (e5237 _v)) (h5362 : (e5362 _v)) (h6742 : (e6742 _v)) : (e3069 _v) := by
  have p14878 := n14878 _v _q 
  have p18163 := n18163 _v _q h474 h2296 h2522 h4264 h5237 h5362 h6742
  simp only [e3069, e3071, e3074, e3075, e6829, e6830, e8137] at *
  tauto
end
end Assembly
