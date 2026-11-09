import Dag182
import generated.th_lemma_20
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n18064 (_v : Vars) (_q : Query _v)  : (e18063 _v) := by
  by_contra hc
  change ¬ ((¬ (e4161 _v)) ∨ (¬ (e2722 _v)) ∨ (¬ (e4459 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e3919 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e3133 _v)) ∨ (¬ (e4491 _v)) ∨ (¬ (e4724 _v)) ∨ (¬ (e4567 _v)) ∨ (¬ (e4791 _v)) ∨ (¬ (e4398 _v)) ∨ (¬ (e4679 _v)) ∨ (¬ (e4817 _v)) ∨ (¬ (e4264 _v)) ∨ (e196 _v) ∨ (¬ (e4101 _v)) ∨ (¬ (e4903 _v)) ∨ (¬ (e4439 _v)) ∨ (¬ (e3976 _v)) ∨ (¬ (e3158 _v)) ∨ (¬ (e4306 _v))) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h2722 : (e2722 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h3133 : (e3133 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h3158 : (e3158 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))
  have h3919 : (e3919 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h3976 : (e3976 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))
  have h4059 : (e4059 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4101 : (e4101 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))
  have h4161 : (e4161 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h4264 : (e4264 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn)))))))))))))))))))))))
  have h4398 : (e4398 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h4439 : (e4439 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))
  have h4459 : (e4459 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4491 : (e4491 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h4567 : (e4567 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4679 : (e4679 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h4724 : (e4724 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h4791 : (e4791 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h4817 : (e4817 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h4903 : (e4903 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))
  have h5195 : (e5195 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))
  have p18046 := n18046 _v _q h51 h2722 h3133 h3158 h3919 h3976 h4059 h4101 h4161 h4264 h4306 h4398 h4439 h4459 h4491 h4567 h4653 h4679 h4724 h4791 h4817 h4903 h5195
  exact p18046
theorem n18065 (_v : Vars) (_q : Query _v) (h5195 : (e5195 _v)) : (e8317 _v) := by
  have p11541 := n11541 _v _q 
  have p15220 := n15220 _v _q h5195
  simp only [e8315, e8317, e8319, e8320, e8321, e8322, e8491] at *
  tauto
theorem n18066 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3855 : (e3855 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4491 : (e4491 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5100 : (e5100 _v)) (h5195 : (e5195 _v)) (h6480 : (e6480 _v)) (h6700 : (e6700 _v)) (h7493 : (e7493 _v)) (h7749 : (e7749 _v)) (h8045 : (e8045 _v)) : (e7489 _v) := by
  have p18065 := n18065 _v _q h5195
  have p16269 := n16269 _v _q h7749
  have p8549 := n8549 _v _q h5195
  have p11027 := n11027 _v _q h6700
  have p15223 := n15223 _v _q h5195
  have p17202 := n17202 _v _q h5195
  have p8663 := n8663 _v _q 
  have p4999 := n4999 _v _q h91
  have p17055 := n17055 _v _q 
  have p8575 := n8575 _v _q h6480
  have p18048 := n18048 _v _q h225 h488 h3069 h3105 h3152 h3855 h3937 h3946 h3976 h4059 h4096 h4156 h4260 h4369 h4398 h4491 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h5195 h6700 h7493 h7749 h8045
  have p17155 := n17155 _v _q h7493
  have p5001 := n5001 _v _q h4096
  have p17136 := n17136 _v _q 
  have p17127 := n17127 _v _q 
  have p16929 := n16929 _v _q 
  have p17056 := n17056 _v _q h3946
  have p15263 := n15263 _v _q h5195
  have p5003 := n5003 _v _q h4199
  have p17159 := n17159 _v _q h5100
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
  have p17199 := n17199 _v _q h5195
  have p17157 := n17157 _v _q h8045
  have p17061 := n17061 _v _q h4747
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
  have p15268 := n15268 _v _q h5195 h6480
  have p17096 := n17096 _v _q 
  have p17122 := n17122 _v _q 
  have p15260 := n15260 _v _q h5195
  have p17108 := n17108 _v _q 
  have p17124 := n17124 _v _q 
  have p17203 := n17203 _v _q h5195
  have p17117 := n17117 _v _q 
  have p17104 := n17104 _v _q 
  have p17131 := n17131 _v _q 
  have p17106 := n17106 _v _q 
  have p4998 := n4998 _v _q h3152
  have p4995 := n4995 _v _q h4369
  have p17120 := n17120 _v _q 
  have p17069 := n17069 _v _q 
  have p17128 := n17128 _v _q h4491
  have p4996 := n4996 _v _q h3937
  have p17141 := n17141 _v _q 
  have p17093 := n17093 _v _q 
  have p17053 := n17053 _v _q 
  have p17137 := n17137 _v _q h4059
  have p17204 := n17204 _v _q h5195
  have p13951 := n13951 _v _q 
  have p15272 := n15272 _v _q h6480
  have p12840 := n12840 _v _q h5195
  have p15274 := n15274 _v _q h5195
  exact FloorCertificate.node_18066 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e61 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2849 _v) (e2863 _v) (e2877 _v) (e2883 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e3164 _v) (e4215 _v) (e4541 _v) (e4808 _v) p18065 p16269 p8549 p11027 p15223 p17202 p8663 p4999 p17055 p8575 p18048 p17155 p5001 p17136 p17127 p16929 p17056 p15263 p5003 p17159 p17129 p5006 p17076 p17147 p5007 p5008 p17133 p5005 p17143 p5010 p4981 p17199 p17157 p17061 p4988 p4986 p16175 p4983 p17094 p4994 p4992 p4984 p4985 p17080 p17134 p17074 p17078 p17072 p17098 p17091 p17087 p17115 p17110 p17067 p17100 p4991 p17058 p17083 p16576 p17113 p17064 p17102 p16250 p15268 p17096 p17122 p15260 p17108 p17124 p17203 p17117 p17104 p17131 p17106 p4998 p4995 p17120 p17069 p17128 p4996 p17141 p17093 p17053 p17137 p17204 p13951 p15272 p12840 p15274
theorem n18067 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2125 : (e2125 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3976 : (e3976 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h6700 : (e6700 _v)) (h8038 : (e8038 _v)) : (e7606 _v) := by
  have p11418 := n11418 _v _q 
  have p18009 := n18009 _v _q h70 h91 h191 h225 h442 h488 h2125 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4567 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  simp only [e7606, e7607, e7608, e7609, e7610, e7611, e7630] at *
  tauto
theorem n18068 (_v : Vars) (_q : Query _v) (h2125 : (e2125 _v)) (h8038 : (e8038 _v)) : (e3566 _v) := by
  have p7179 := n7179 _v _q 
  have p15303 := n15303 _v _q h2125 h8038
  simp only [e3565, e3566, e3570, e3571, e3572, e3573, e3590] at *
  tauto
theorem n18069 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2125 : (e2125 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3976 : (e3976 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h6700 : (e6700 _v)) (h8038 : (e8038 _v)) : (e7935 _v) := by
  have p15266 := n15266 _v _q 
  have p18019 := n18019 _v _q h70 h91 h191 h225 h442 h488 h2125 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4567 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  simp only [e7932, e7935, e7942, e7943, e7944, e7945, e8489] at *
  tauto
theorem n18070 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2125 : (e2125 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3976 : (e3976 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h6700 : (e6700 _v)) (h8038 : (e8038 _v)) : (e4839 _v) := by
  have p17628 := n17628 _v _q 
  have p18067 := n18067 _v _q h70 h91 h191 h225 h442 h488 h2125 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4567 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  have p18068 := n18068 _v _q h2125 h8038
  have p18049 := n18049 _v _q h70 h91 h191 h225 h442 h488 h2125 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4567 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  have p16919 := n16919 _v _q h8038
  have p253 := n253 _v _q h191
  have p15198 := n15198 _v _q h8038
  have p5001 := n5001 _v _q h4096
  have p15203 := n15203 _v _q h8038
  have p18014 := n18014 _v _q h70 h91 h191 h225 h442 h488 h2125 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4567 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  have p5003 := n5003 _v _q h4199
  have p17168 := n17168 _v _q h8038
  have p17129 := n17129 _v _q h4903
  have p5006 := n5006 _v _q h4675
  have p17076 := n17076 _v _q h3976
  have p5007 := n5007 _v _q h225
  have p5008 := n5008 _v _q h4787
  have p5005 := n5005 _v _q h3169
  have p17143 := n17143 _v _q h4567
  have p5010 := n5010 _v _q h70
  have p4981 := n4981 _v _q h4260
  have p15246 := n15246 _v _q h2125
  have p15209 := n15209 _v _q h8038
  have p15211 := n15211 _v _q h8038
  have p4988 := n4988 _v _q h488
  have p4986 := n4986 _v _q h3105
  have p4983 := n4983 _v _q h4813
  have p17169 := n17169 _v _q h8038
  have p4994 := n4994 _v _q h3069
  have p4992 := n4992 _v _q h442
  have p4984 := n4984 _v _q h4872
  have p4985 := n4985 _v _q h4156
  have p17170 := n17170 _v _q h8038
  have p4991 := n4991 _v _q h4608
  have p17167 := n17167 _v _q h8038
  have p18017 := n18017 _v _q h70 h91 h191 h225 h442 h488 h2125 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4567 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  have p18069 := n18069 _v _q h70 h91 h191 h225 h442 h488 h2125 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4567 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  have p4998 := n4998 _v _q h3152
  have p4995 := n4995 _v _q h4369
  have p15200 := n15200 _v _q h8038
  have p4996 := n4996 _v _q h3937
  have p15194 := n15194 _v _q h8038
  have p4999 := n4999 _v _q h91
  have p11027 := n11027 _v _q h6700
  have p15301 := n15301 _v _q h2125
  simp only [e70, e75, e91, e95, e191, e192, e225, e230, e442, e443, e488, e493, e2061, e2634, e3069, e3074, e3105, e3106, e3152, e3156, e3169, e3170, e3271, e3276, e3566, e3571, e3855, e3860, e3937, e3942, e3946, e3947, e3976, e3981, e4059, e4064, e4096, e4097, e4139, e4140, e4156, e4157, e4199, e4200, e4260, e4261, e4306, e4311, e4369, e4370, e4398, e4403, e4459, e4464, e4491, e4496, e4567, e4572, e4608, e4609, e4653, e4658, e4675, e4676, e4724, e4729, e4747, e4752, e4787, e4788, e4813, e4814, e4838, e4839, e4872, e4873, e4903, e4908, e5100, e5103, e6454, e6700, e7493, e7494, e7606, e7607, e7935, e7943, e8045, e8048, e17627] at *
  tauto
theorem n18071 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2125 : (e2125 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3976 : (e3976 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h6700 : (e6700 _v)) (h8038 : (e8038 _v)) : (e8301 _v) := by
  have p16285 := n16285 _v _q 
  have p18070 := n18070 _v _q h70 h91 h191 h225 h442 h488 h2125 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4567 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  simp only [e4836, e4837, e4838, e4839, e8301, e8302] at *
  tauto
theorem n18072 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2358 : (e2358 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3976 : (e3976 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4572 : (e4572 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h6656 : (e6656 _v)) (h7935 : (e7935 _v)) (h8038 : (e8038 _v)) : (e8149 _v) := by
  have p15027 := n15027 _v _q 
  have p18051 := n18051 _v _q h70 h91 h191 h225 h442 h488 h2358 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4301 h4369 h4572 h4608 h4675 h4787 h4813 h4838 h4872 h4903 h6656 h7935 h8038
  simp only [e4648, e4649, e4650, e4651, e8149, e8150] at *
  tauto
theorem n18073 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2358 : (e2358 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3976 : (e3976 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4572 : (e4572 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h6656 : (e6656 _v)) (h7935 : (e7935 _v)) (h8038 : (e8038 _v)) : (e2364 _v) := by
  have p14632 := n14632 _v _q 
  have p18072 := n18072 _v _q h70 h91 h191 h225 h442 h488 h2358 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4301 h4369 h4572 h4608 h4675 h4787 h4813 h4838 h4872 h4903 h6656 h7935 h8038
  simp only [e2364, e4648, e4649, e4650, e4651, e8149, e8157, e8160] at *
  tauto
theorem n18074 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2358 : (e2358 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3976 : (e3976 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4572 : (e4572 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h6656 : (e6656 _v)) (h7935 : (e7935 _v)) (h8038 : (e8038 _v)) : (e4661 _v) := by
  have p14686 := n14686 _v _q 
  have p18073 := n18073 _v _q h70 h91 h191 h225 h442 h488 h2358 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4301 h4369 h4572 h4608 h4675 h4787 h4813 h4838 h4872 h4903 h6656 h7935 h8038
  simp only [e2364, e4653, e4654, e4658, e4659, e4660, e4661, e6583, e8163] at *
  tauto
theorem n18076 (_v : Vars) (_q : Query _v)  : (e18075 _v) := by
  by_contra hc
  change ¬ ((¬ (e2592 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e3855 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e30 _v)) ∨ (¬ (e4491 _v)) ∨ (e2371 _v) ∨ (¬ (e4199 _v)) ∨ (¬ (e4220 _v)) ∨ (¬ (e3976 _v)) ∨ (¬ (e3169 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e8398 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4724 _v)) ∨ (¬ (e3585 _v)) ∨ (¬ (e4419 _v)) ∨ (¬ (e4899 _v)) ∨ (¬ (e4562 _v)) ∨ (¬ (e4128 _v)) ∨ (¬ (e4026 _v)) ∨ (¬ (e4546 _v)) ∨ (¬ (e4285 _v)) ∨ (¬ (e4477 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e4301 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e4648 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e4398 _v))) at hc
  have h30 : (e30 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h70 : (e70 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h191 : (e191 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))))))))))))))
  have h225 : (e225 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h442 : (e442 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))))))))))))))))
  have h488 : (e488 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))))))))))))
  have h2592 : (e2592 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h3069 : (e3069 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))))))))))))))))))
  have h3105 : (e3105 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))))))))))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h3169 : (e3169 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h3585 : (e3585 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))
  have h3855 : (e3855 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h3946 : (e3946 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h3976 : (e3976 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h4026 : (e4026 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))
  have h4059 : (e4059 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))
  have h4096 : (e4096 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h4128 : (e4128 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))
  have h4139 : (e4139 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))))
  have h4156 : (e4156 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))))))))
  have h4199 : (e4199 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h4220 : (e4220 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h4260 : (e4260 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))))))
  have h4285 : (e4285 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))
  have h4301 : (e4301 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))))
  have h4369 : (e4369 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))))))))))))))))))
  have h4398 : (e4398 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))))))))))))))))))))))))))))))))))))))))))))
  have h4419 : (e4419 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))
  have h4434 : (e4434 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))))))))))
  have h4477 : (e4477 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))
  have h4491 : (e4491 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h4546 : (e4546 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))
  have h4562 : (e4562 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))
  have h4608 : (e4608 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))))))))))))))))
  have h4648 : (e4648 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))))))))))))))
  have h4675 : (e4675 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))
  have h4724 : (e4724 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))
  have h4747 : (e4747 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))))))
  have h4838 : (e4838 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))))))))))))
  have h4872 : (e4872 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))))))))
  have h4899 : (e4899 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))
  have h6579 : (e6579 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h8398 : (e8398 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))
  have p18053 := n18053 _v _q h30 h70 h91 h191 h225 h442 h488 h2592 h3069 h3105 h3152 h3169 h3585 h3855 h3937 h3946 h3976 h4026 h4059 h4096 h4128 h4139 h4156 h4199 h4220 h4260 h4285 h4301 h4369 h4398 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4724 h4747 h4787 h4813 h4838 h4872 h4899 h6579 h8398
  exact p18053
theorem n18077 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2536 : (e2536 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3855 : (e3855 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4026 : (e4026 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4220 : (e4220 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4491 : (e4491 _v)) (h4546 : (e4546 _v)) (h4562 : (e4562 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) (h6579 : (e6579 _v)) : (e8330 _v) := by
  have p14907 := n14907 _v _q 
  have p18054 := n18054 _v _q h30 h70 h91 h191 h225 h442 h488 h2536 h3069 h3105 h3152 h3169 h3855 h3937 h3946 h3976 h4026 h4059 h4096 h4139 h4156 h4199 h4220 h4260 h4285 h4301 h4369 h4398 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4724 h4747 h4787 h4813 h4838 h4872 h4899 h6579
  simp only [e2592, e4855, e4856, e4857, e4858, e6672, e8324, e8330, e8333] at *
  tauto
theorem n18078 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2536 : (e2536 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3855 : (e3855 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4026 : (e4026 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4220 : (e4220 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4491 : (e4491 _v)) (h4546 : (e4546 _v)) (h4562 : (e4562 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) (h6579 : (e6579 _v)) : (e4855 _v) := by
  have p16317 := n16317 _v _q 
  have p18077 := n18077 _v _q h30 h70 h91 h191 h225 h442 h488 h2536 h3069 h3105 h3152 h3169 h3855 h3937 h3946 h3976 h4026 h4059 h4096 h4139 h4156 h4199 h4220 h4260 h4285 h4301 h4369 h4398 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4724 h4747 h4787 h4813 h4838 h4872 h4899 h6579
  simp only [e4855, e4856, e4857, e4858, e8324, e8325, e8330] at *
  tauto
theorem n18079 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4026 : (e4026 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4220 : (e4220 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4491 : (e4491 _v)) (h4546 : (e4546 _v)) (h4562 : (e4562 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) : (e4731 _v) := by
  have p14698 := n14698 _v _q 
  have p18055 := n18055 _v _q h30 h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h3976 h4026 h4059 h4096 h4139 h4156 h4199 h4220 h4260 h4285 h4301 h4369 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h4899
  simp only [e2254, e4723, e4724, e4728, e4729, e4730, e4731, e6531, e8220] at *
  tauto
theorem n18080 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4026 : (e4026 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4220 : (e4220 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4491 : (e4491 _v)) (h4546 : (e4546 _v)) (h4562 : (e4562 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) : (e4724 _v) := by
  have p15518 := n15518 _v _q 
  have p18079 := n18079 _v _q h30 h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h3976 h4026 h4059 h4096 h4139 h4156 h4199 h4220 h4260 h4285 h4301 h4369 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h4899
  simp only [e4723, e4724, e4728, e4729, e4730, e4731, e4958] at *
  tauto
theorem n18082 (_v : Vars) (_q : Query _v)  : (e18081 _v) := by
  have p18057 := n18057 _v _q 
  have p16913 := n16913 _v _q 
  simp only [e30, e35, e70, e75, e91, e95, e191, e192, e225, e230, e442, e443, e488, e493, e2746, e2799, e3069, e3074, e3105, e3106, e3152, e3156, e3169, e3170, e3267, e3268, e3585, e3589, e3855, e3860, e3937, e3942, e3946, e3947, e4059, e4064, e4096, e4097, e4128, e4133, e4139, e4140, e4156, e4157, e4199, e4200, e4260, e4261, e4285, e4286, e4301, e4302, e4369, e4370, e4398, e4403, e4419, e4420, e4434, e4435, e4477, e4481, e4491, e4496, e4546, e4547, e4562, e4563, e4608, e4609, e4648, e4649, e4675, e4676, e4724, e4729, e4747, e4752, e4787, e4788, e4813, e4814, e4838, e4839, e4855, e4856, e4872, e4873, e4899, e4900, e6780, e18056, e18081] at *
  tauto
theorem n18083 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h436 : (e436 _v)) (h496 : (e496 _v)) (h3133 : (e3133 _v)) (h3158 : (e3158 _v)) (h3919 : (e3919 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4101 : (e4101 _v)) (h4264 : (e4264 _v)) (h4306 : (e4306 _v)) (h4373 : (e4373 _v)) (h4398 : (e4398 _v)) (h4439 : (e4439 _v)) (h4459 : (e4459 _v)) (h4491 : (e4491 _v)) (h4567 : (e4567 _v)) (h4653 : (e4653 _v)) (h4679 : (e4679 _v)) (h4724 : (e4724 _v)) (h4791 : (e4791 _v)) (h4817 : (e4817 _v)) (h4903 : (e4903 _v)) (h6742 : (e6742 _v)) : (e7489 _v) := by
  have p17058 := n17058 _v _q 
  have p296 := n296 _v _q 
  have p17076 := n17076 _v _q h3976
  have p17064 := n17064 _v _q 
  have p17067 := n17067 _v _q 
  have p17069 := n17069 _v _q 
  have p17072 := n17072 _v _q 
  have p18058 := n18058 _v _q h51 h436 h496 h3133 h3158 h3919 h3976 h4059 h4101 h4264 h4306 h4373 h4398 h4439 h4459 h4491 h4567 h4653 h4679 h4724 h4791 h4817 h4903 h6742
  have p16152 := n16152 _v _q h436
  have p14739 := n14739 _v _q h496
  have p17085 := n17085 _v _q h4373
  have p17078 := n17078 _v _q 
  have p17080 := n17080 _v _q 
  have p17083 := n17083 _v _q 
  have p17074 := n17074 _v _q 
  have p14766 := n14766 _v _q h496
  have p17087 := n17087 _v _q 
  have p17758 := n17758 _v _q 
  have p17091 := n17091 _v _q 
  have p17093 := n17093 _v _q 
  have p15001 := n15001 _v _q h6742
  have p17138 := n17138 _v _q h4306
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p17100 := n17100 _v _q 
  have p17102 := n17102 _v _q 
  have p16885 := n16885 _v _q h3158
  have p17104 := n17104 _v _q 
  have p15004 := n15004 _v _q h496
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
  have p17075 := n17075 _v _q h4439
  exact FloorCertificate.node_18083 (e17 _v) (e49 _v) (e101 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) p17058 p296 p17076 p17064 p17067 p17069 p17072 p18058 p16152 p14739 p17085 p17078 p17080 p17083 p17074 p14766 p17087 p17758 p17091 p17093 p15001 p17138 p17098 p17106 p17100 p17102 p16885 p17104 p15004 p17096 p17111 p17051 p17113 p17060 p17137 p17079 p16729 p17062 p17122 p17117 p17124 p17115 p17120 p17128 p17127 p16778 p17874 p17131 p17110 p17133 p17094 p17143 p17050 p17059 p17294 p17136 p17141 p17134 p17070 p17088 p17118 p17065 p17129 p17053 p17089 p17055 p17108 p17075
theorem n18084 (_v : Vars) (_q : Query _v) (h467 : (e467 _v)) (h2296 : (e2296 _v)) (h2522 : (e2522 _v)) (h3051 : (e3051 _v)) (h4161 : (e4161 _v)) (h4264 : (e4264 _v)) (h5362 : (e5362 _v)) (h6742 : (e6742 _v)) : (e6694 _v) := by
  have p18062 := n18062 _v _q 
  have p17125 := n17125 _v _q h3051
  have p17081 := n17081 _v _q h4161
  have p17084 := n17084 _v _q h467
  have p17118 := n17118 _v _q h4264
  have p12831 := n12831 _v _q h2522
  have p8416 := n8416 _v _q h6742
  have p8583 := n8583 _v _q h2296
  have p7488 := n7488 _v _q h5362
  simp only [e251, e436, e467, e468, e2296, e2522, e2722, e3051, e3052, e4161, e4166, e4264, e4269, e5362, e6549, e6650, e6694, e6742, e18061] at *
  tauto
theorem n18086 (_v : Vars) (_q : Query _v)  : (e18085 _v) := by
  by_contra hc
  change ¬ ((e196 _v) ∨ (¬ (e7749 _v)) ∨ (e2634 _v) ∨ (¬ (e91 _v)) ∨ (e2125 _v) ∨ (¬ (e7493 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e5100 _v)) ∨ (¬ (e4903 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e3976 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e3169 _v)) ∨ (¬ (e4567 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e8045 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4724 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e4398 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e3855 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e4491 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e4059 _v))) at hc
  have h70 : (e70 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h225 : (e225 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h442 : (e442 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))
  have h488 : (e488 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))
  have h3069 : (e3069 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))
  have h3105 : (e3105 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))))
  have h3169 : (e3169 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))
  have h3855 : (e3855 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))))
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))))))))
  have h3946 : (e3946 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h3976 : (e3976 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h4059 : (e4059 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn)))))))))))))))))))))))))))))))))))))
  have h4096 : (e4096 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h4156 : (e4156 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))
  have h4199 : (e4199 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h4260 : (e4260 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))
  have h4369 : (e4369 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))))))
  have h4398 : (e4398 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))
  have h4491 : (e4491 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))))))
  have h4567 : (e4567 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))
  have h4608 : (e4608 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))
  have h4675 : (e4675 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h4724 : (e4724 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))
  have h4747 : (e4747 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))
  have h4872 : (e4872 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))
  have h4903 : (e4903 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h5100 : (e5100 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h5195 : (e5195 _v) := (fun hn => hc (Or.inl hn))
  have h6480 : (e6480 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h6700 : (e6700 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h7493 : (e7493 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h7749 : (e7749 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h8045 : (e8045 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))
  have p18066 := n18066 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3855 h3937 h3946 h3976 h4059 h4096 h4156 h4199 h4260 h4369 h4398 h4491 h4567 h4608 h4675 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h5195 h6480 h6700 h7493 h7749 h8045
  exact p18066
theorem n18087 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2125 : (e2125 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3976 : (e3976 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h6700 : (e6700 _v)) (h8038 : (e8038 _v)) : (e2529 _v) := by
  have p17961 := n17961 _v _q 
  have p18017 := n18017 _v _q h70 h91 h191 h225 h442 h488 h2125 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4567 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  have p4981 := n4981 _v _q h4260
  have p5001 := n5001 _v _q h4096
  have p11027 := n11027 _v _q h6700
  have p15203 := n15203 _v _q h8038
  have p15301 := n15301 _v _q h2125
  have p17168 := n17168 _v _q h8038
  have p17129 := n17129 _v _q h4903
  have p17076 := n17076 _v _q h3976
  have p5007 := n5007 _v _q h225
  have p5008 := n5008 _v _q h4787
  have p15198 := n15198 _v _q h8038
  have p15209 := n15209 _v _q h8038
  have p15211 := n15211 _v _q h8038
  have p4988 := n4988 _v _q h488
  have p4986 := n4986 _v _q h3105
  have p4983 := n4983 _v _q h4813
  have p17169 := n17169 _v _q h8038
  have p4994 := n4994 _v _q h3069
  have p4984 := n4984 _v _q h4872
  have p4985 := n4985 _v _q h4156
  have p17170 := n17170 _v _q h8038
  have p17167 := n17167 _v _q h8038
  have p17962 := n17962 _v _q h70 h91 h191 h225 h442 h488 h2125 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4567 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  have p4998 := n4998 _v _q h3152
  have p4995 := n4995 _v _q h4369
  have p15200 := n15200 _v _q h8038
  have p4996 := n4996 _v _q h3937
  have p15194 := n15194 _v _q h8038
  have p16918 := n16918 _v _q h8038
  have p18014 := n18014 _v _q h70 h91 h191 h225 h442 h488 h2125 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4567 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  simp only [e225, e230, e488, e493, e2061, e2358, e2529, e2634, e3069, e3074, e3105, e3106, e3152, e3156, e3271, e3276, e3855, e3860, e3937, e3942, e3946, e3947, e3976, e3981, e4059, e4064, e4096, e4097, e4156, e4157, e4260, e4261, e4369, e4370, e4398, e4403, e4491, e4496, e4653, e4658, e4724, e4729, e4747, e4752, e4787, e4788, e4813, e4814, e4872, e4873, e4903, e4908, e5100, e5103, e6454, e6571, e6700, e7493, e7494, e7749, e7752, e8045, e8048, e17960] at *
  tauto
theorem n18088 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2125 : (e2125 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3976 : (e3976 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h6700 : (e6700 _v)) (h8038 : (e8038 _v)) : (e7489 _v) := by
  have p14906 := n14906 _v _q 
  have p18071 := n18071 _v _q h70 h91 h191 h225 h442 h488 h2125 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4567 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  have p18087 := n18087 _v _q h70 h91 h191 h225 h442 h488 h2125 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4567 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  simp only [e2529, e4836, e4837, e4838, e4839, e8301, e8307, e8310, e8312] at *
  tauto
theorem n18089 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2358 : (e2358 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3976 : (e3976 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4572 : (e4572 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h6656 : (e6656 _v)) (h7935 : (e7935 _v)) (h8038 : (e8038 _v)) : (e4653 _v) := by
  have p15168 := n15168 _v _q 
  have p18074 := n18074 _v _q h70 h91 h191 h225 h442 h488 h2358 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4301 h4369 h4572 h4608 h4675 h4787 h4813 h4838 h4872 h4903 h6656 h7935 h8038
  simp only [e4653, e4654, e4658, e4659, e4660, e4661, e4939] at *
  tauto
theorem n18090 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2358 : (e2358 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3976 : (e3976 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4572 : (e4572 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h6656 : (e6656 _v)) (h7935 : (e7935 _v)) (h8038 : (e8038 _v)) : (e7807 _v) := by
  have p18051 := n18051 _v _q h70 h91 h191 h225 h442 h488 h2358 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4301 h4369 h4572 h4608 h4675 h4787 h4813 h4838 h4872 h4903 h6656 h7935 h8038
  have p18089 := n18089 _v _q h70 h91 h191 h225 h442 h488 h2358 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4301 h4369 h4572 h4608 h4675 h4787 h4813 h4838 h4872 h4903 h6656 h7935 h8038
  have p15371 := n15371 _v _q h8038
  have p16394 := n16394 _v _q 
  have p15181 := n15181 _v _q h4572
  have p8486 := n8486 _v _q h4572
  exact FloorCertificate.node_18090 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e110 _v) (e2834 _v) (e2879 _v) (e2918 _v) (e2951 _v) p18051 p18089 p15371 p16394 p15181 p8486
theorem n18091 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2358 : (e2358 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3976 : (e3976 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4572 : (e4572 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h6656 : (e6656 _v)) (h7935 : (e7935 _v)) (h8038 : (e8038 _v)) : (e7817 _v) := by
  have p5255 := n5255 _v _q 
  have p11499 := n11499 _v _q h6656
  have p18089 := n18089 _v _q h70 h91 h191 h225 h442 h488 h2358 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4301 h4369 h4572 h4608 h4675 h4787 h4813 h4838 h4872 h4903 h6656 h7935 h8038
  have p17074 := n17074 _v _q 
  have p15336 := n15336 _v _q h8038
  have p4989 := n4989 _v _q h4838
  have p4980 := n4980 _v _q h4301
  have p17163 := n17163 _v _q h7935
  have p17170 := n17170 _v _q h8038
  have p16394 := n16394 _v _q 
  have p15181 := n15181 _v _q h4572
  have p8486 := n8486 _v _q h4572
  have p8602 := n8602 _v _q h8038
  have p17072 := n17072 _v _q 
  have p17091 := n17091 _v _q 
  have p17080 := n17080 _v _q 
  have p17098 := n17098 _v _q 
  have p17078 := n17078 _v _q 
  have p253 := n253 _v _q h191
  have p16370 := n16370 _v _q h2358
  have p17825 := n17825 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4572 h4608 h4675 h4787 h4813 h4872 h4903 h8038
  have p17087 := n17087 _v _q 
  have p17067 := n17067 _v _q 
  have p17100 := n17100 _v _q 
  have p4991 := n4991 _v _q h4608
  have p16344 := n16344 _v _q h4572
  have p17110 := n17110 _v _q 
  have p17115 := n17115 _v _q 
  have p17083 := n17083 _v _q 
  have p16576 := n16576 _v _q 
  have p17058 := n17058 _v _q 
  have p17113 := n17113 _v _q 
  have p17064 := n17064 _v _q 
  have p17102 := n17102 _v _q 
  have p13951 := n13951 _v _q 
  have p17167 := n17167 _v _q h8038
  have p17096 := n17096 _v _q 
  have p16929 := n16929 _v _q 
  have p17122 := n17122 _v _q 
  have p15360 := n15360 _v _q h6656
  have p17124 := n17124 _v _q 
  have p17106 := n17106 _v _q 
  have p17108 := n17108 _v _q 
  have p17104 := n17104 _v _q 
  have p4995 := n4995 _v _q h4369
  have p17117 := n17117 _v _q 
  have p17120 := n17120 _v _q 
  have p17069 := n17069 _v _q 
  have p17141 := n17141 _v _q 
  have p17093 := n17093 _v _q 
  have p17131 := n17131 _v _q 
  have p17053 := n17053 _v _q 
  have p4996 := n4996 _v _q h3937
  have p16918 := n16918 _v _q h8038
  have p4998 := n4998 _v _q h3152
  have p16346 := n16346 _v _q h4572
  have p16181 := n16181 _v _q 
  have p15194 := n15194 _v _q h8038
  have p4999 := n4999 _v _q h91
  have p17055 := n17055 _v _q 
  have p15198 := n15198 _v _q h8038
  have p5001 := n5001 _v _q h4096
  have p17136 := n17136 _v _q 
  have p17127 := n17127 _v _q 
  have p15200 := n15200 _v _q h8038
  have p15203 := n15203 _v _q h8038
  have p17798 := n17798 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4572 h4608 h4675 h4787 h4813 h4872 h4903 h8038
  have p5003 := n5003 _v _q h4199
  have p17168 := n17168 _v _q h8038
  have p17129 := n17129 _v _q h4903
  have p5006 := n5006 _v _q h4675
  have p17076 := n17076 _v _q h3976
  have p17147 := n17147 _v _q 
  have p5007 := n5007 _v _q h225
  have p5008 := n5008 _v _q h4787
  have p17133 := n17133 _v _q 
  have p5005 := n5005 _v _q h3169
  have p5010 := n5010 _v _q h70
  have p4981 := n4981 _v _q h4260
  have p15209 := n15209 _v _q h8038
  have p15211 := n15211 _v _q h8038
  have p4988 := n4988 _v _q h488
  have p4986 := n4986 _v _q h3105
  have p16175 := n16175 _v _q 
  have p4983 := n4983 _v _q h4813
  have p17169 := n17169 _v _q h8038
  have p4994 := n4994 _v _q h3069
  have p4992 := n4992 _v _q h442
  have p4984 := n4984 _v _q h4872
  have p4985 := n4985 _v _q h4156
  have p11354 := n11354 _v _q h2358
  have p18051 := n18051 _v _q h70 h91 h191 h225 h442 h488 h2358 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4301 h4369 h4572 h4608 h4675 h4787 h4813 h4838 h4872 h4903 h6656 h7935 h8038
  have p15371 := n15371 _v _q h8038
  exact FloorCertificate.node_18091 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e61 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2834 _v) (e2849 _v) (e2863 _v) (e2877 _v) (e2879 _v) (e2883 _v) (e2898 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e3164 _v) (e3574 _v) (e4215 _v) (e4541 _v) (e4808 _v) p5255 p11499 p18089 p17074 p15336 p4989 p4980 p17163 p17170 p16394 p15181 p8486 p8602 p17072 p17091 p17080 p17098 p17078 p253 p16370 p17825 p17087 p17067 p17100 p4991 p16344 p17110 p17115 p17083 p16576 p17058 p17113 p17064 p17102 p13951 p17167 p17096 p16929 p17122 p15360 p17124 p17106 p17108 p17104 p4995 p17117 p17120 p17069 p17141 p17093 p17131 p17053 p4996 p16918 p4998 p16346 p16181 p15194 p4999 p17055 p15198 p5001 p17136 p17127 p15200 p15203 p17798 p5003 p17168 p17129 p5006 p17076 p17147 p5007 p5008 p17133 p5005 p5010 p4981 p15209 p15211 p4988 p4986 p16175 p4983 p17169 p4994 p4992 p4984 p4985 p11354 p18051 p15371
theorem n18093 (_v : Vars) (_q : Query _v)  : (e18092 _v) := by
  have p18076 := n18076 _v _q 
  have p16913 := n16913 _v _q 
  simp only [e30, e35, e70, e75, e91, e95, e191, e192, e225, e230, e442, e443, e488, e493, e2371, e2592, e3069, e3074, e3105, e3106, e3152, e3156, e3169, e3170, e3585, e3589, e3855, e3860, e3937, e3942, e3946, e3947, e3976, e3981, e4026, e4031, e4059, e4064, e4096, e4097, e4128, e4133, e4139, e4140, e4156, e4157, e4199, e4200, e4220, e4221, e4260, e4261, e4285, e4286, e4301, e4302, e4369, e4370, e4398, e4403, e4419, e4420, e4434, e4435, e4477, e4481, e4491, e4496, e4546, e4547, e4562, e4563, e4608, e4609, e4648, e4649, e4675, e4676, e4724, e4729, e4747, e4752, e4787, e4788, e4813, e4814, e4838, e4839, e4872, e4873, e4899, e4900, e6672, e8398, e8406, e18075, e18092] at *
  tauto
theorem n18094 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2536 : (e2536 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3855 : (e3855 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4026 : (e4026 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4220 : (e4220 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4491 : (e4491 _v)) (h4546 : (e4546 _v)) (h4562 : (e4562 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) (h6579 : (e6579 _v)) : (e7489 _v) := by
  have p5255 := n5255 _v _q 
  have p11132 := n11132 _v _q h2536
  have p18054 := n18054 _v _q h30 h70 h91 h191 h225 h442 h488 h2536 h3069 h3105 h3152 h3169 h3855 h3937 h3946 h3976 h4026 h4059 h4096 h4139 h4156 h4199 h4220 h4260 h4285 h4301 h4369 h4398 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4724 h4747 h4787 h4813 h4838 h4872 h4899 h6579
  have p4975 := n4975 _v _q h4026
  have p13951 := n13951 _v _q 
  have p18078 := n18078 _v _q h30 h70 h91 h191 h225 h442 h488 h2536 h3069 h3105 h3152 h3169 h3855 h3937 h3946 h3976 h4026 h4059 h4096 h4139 h4156 h4199 h4220 h4260 h4285 h4301 h4369 h4398 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4724 h4747 h4787 h4813 h4838 h4872 h4899 h6579
  have p17230 := n17230 _v _q h6579
  have p5257 := n5257 _v _q 
  have p4971 := n4971 _v _q h4419
  have p4976 := n4976 _v _q h4546
  have p4972 := n4972 _v _q h4899
  have p17831 := n17831 _v _q h30 h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3855 h3937 h3946 h3976 h4026 h4059 h4096 h4139 h4156 h4199 h4220 h4260 h4285 h4301 h4369 h4398 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4724 h4747 h4787 h4813 h4838 h4872 h4899
  have p17134 := n17134 _v _q h4398
  have p16929 := n16929 _v _q 
  have p4978 := n4978 _v _q h4477
  have p4979 := n4979 _v _q h4139
  have p4980 := n4980 _v _q h4301
  have p5005 := n5005 _v _q h3169
  have p16394 := n16394 _v _q 
  have p15450 := n15450 _v _q h2536
  have p4973 := n4973 _v _q h4562
  have p4985 := n4985 _v _q h4156
  have p4987 := n4987 _v _q h4434
  have p17221 := n17221 _v _q 
  have p4983 := n4983 _v _q h4813
  have p16175 := n16175 _v _q 
  have p17074 := n17074 _v _q 
  have p4988 := n4988 _v _q h488
  have p4981 := n4981 _v _q h4260
  have p4989 := n4989 _v _q h4838
  have p17072 := n17072 _v _q 
  have p4986 := n4986 _v _q h3105
  have p17080 := n17080 _v _q 
  have p17078 := n17078 _v _q 
  have p17091 := n17091 _v _q 
  have p253 := n253 _v _q h191
  have p17098 := n17098 _v _q 
  have p4990 := n4990 _v _q h4648
  have p17100 := n17100 _v _q 
  have p4984 := n4984 _v _q h4872
  have p17067 := n17067 _v _q 
  have p17087 := n17087 _v _q 
  have p4991 := n4991 _v _q h4608
  have p4992 := n4992 _v _q h442
  have p17115 := n17115 _v _q 
  have p17083 := n17083 _v _q 
  have p17110 := n17110 _v _q 
  have p16576 := n16576 _v _q 
  have p17058 := n17058 _v _q 
  have p17113 := n17113 _v _q 
  have p16913 := n16913 _v _q 
  have p17102 := n17102 _v _q 
  have p17096 := n17096 _v _q 
  have p17106 := n17106 _v _q 
  have p4977 := n4977 _v _q h4285
  have p17122 := n17122 _v _q 
  have p17104 := n17104 _v _q 
  have p4995 := n4995 _v _q h4369
  have p17124 := n17124 _v _q 
  have p17108 := n17108 _v _q 
  have p4994 := n4994 _v _q h3069
  have p17117 := n17117 _v _q 
  have p17120 := n17120 _v _q 
  have p17069 := n17069 _v _q 
  have p15183 := n15183 _v _q h2536
  have p17093 := n17093 _v _q 
  have p17141 := n17141 _v _q 
  have p17131 := n17131 _v _q 
  have p4996 := n4996 _v _q h3937
  have p4999 := n4999 _v _q h91
  have p4998 := n4998 _v _q h3152
  have p16250 := n16250 _v _q h3855
  have p5001 := n5001 _v _q h4096
  have p5000 := n5000 _v _q h30
  have p17136 := n17136 _v _q 
  have p17128 := n17128 _v _q h4491
  have p17127 := n17127 _v _q 
  have p5003 := n5003 _v _q h4199
  have p5004 := n5004 _v _q h4220
  have p17053 := n17053 _v _q 
  have p17076 := n17076 _v _q h3976
  have p17056 := n17056 _v _q h3946
  have p5007 := n5007 _v _q h225
  have p5008 := n5008 _v _q h4787
  have p17055 := n17055 _v _q 
  have p17061 := n17061 _v _q h4747
  have p17147 := n17147 _v _q 
  have p17133 := n17133 _v _q 
  have p5010 := n5010 _v _q h70
  have p17137 := n17137 _v _q h4059
  have p5006 := n5006 _v _q h4675
  have p17094 := n17094 _v _q h4724
  have p17064 := n17064 _v _q 
  exact FloorCertificate.node_18094 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e61 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2834 _v) (e2849 _v) (e2863 _v) (e2877 _v) (e2879 _v) (e2883 _v) (e2898 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2913 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e3164 _v) (e4215 _v) (e4541 _v) (e4808 _v) p5255 p11132 p18054 p4975 p13951 p18078 p17230 p5257 p4971 p4976 p4972 p17831 p17134 p16929 p4978 p4979 p4980 p5005 p16394 p15450 p4973 p4985 p4987 p17221 p4983 p16175 p17074 p4988 p4981 p4989 p17072 p4986 p17080 p17078 p17091 p253 p17098 p4990 p17100 p4984 p17067 p17087 p4991 p4992 p17115 p17083 p17110 p16576 p17058 p17113 p16913 p17102 p17096 p17106 p4977 p17122 p17104 p4995 p17124 p17108 p4994 p17117 p17120 p17069 p15183 p17093 p17141 p17131 p4996 p4999 p4998 p16250 p5001 p5000 p17136 p17128 p17127 p5003 p5004 p17053 p17076 p17056 p5007 p5008 p17055 p17061 p17147 p17133 p5010 p17137 p5006 p17094 p17064
theorem n18095 (_v : Vars) (_q : Query _v)  : (e8501 _v) := by
  simp only [e8183, e8184, e8185, e8186, e8187, e8501] at *
  tauto
theorem n18096 (_v : Vars) (_q : Query _v)  : (e8183 _v) := by
  have p18095 := n18095 _v _q 
  have p14890 := n14890 _v _q 
  simp only [e8183, e8184, e8185, e8186, e8187, e8204, e8501] at *
  tauto
theorem n18097 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4026 : (e4026 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4220 : (e4220 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4491 : (e4491 _v)) (h4546 : (e4546 _v)) (h4562 : (e4562 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) : (e4720 _v) := by
  have p18096 := n18096 _v _q 
  have p18080 := n18080 _v _q h30 h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h3976 h4026 h4059 h4096 h4139 h4156 h4199 h4220 h4260 h4285 h4301 h4369 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h4899
  have p18055 := n18055 _v _q h30 h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h3976 h4026 h4059 h4096 h4139 h4156 h4199 h4220 h4260 h4285 h4301 h4369 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h4899
  exact FloorCertificate.node_18097 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e2942 _v) (e4696 _v) p18096 p18080 p18055
theorem n18098 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2722 : (e2722 _v)) (h3133 : (e3133 _v)) (h3158 : (e3158 _v)) (h3919 : (e3919 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4101 : (e4101 _v)) (h4264 : (e4264 _v)) (h4306 : (e4306 _v)) (h4398 : (e4398 _v)) (h4439 : (e4439 _v)) (h4459 : (e4459 _v)) (h4491 : (e4491 _v)) (h4567 : (e4567 _v)) (h4653 : (e4653 _v)) (h4679 : (e4679 _v)) (h4724 : (e4724 _v)) (h4791 : (e4791 _v)) (h4817 : (e4817 _v)) (h4903 : (e4903 _v)) (h5195 : (e5195 _v)) : (e4166 _v) := by
  have p18064 := n18064 _v _q 
  have p8410 := n8410 _v _q h2722
  have p17051 := n17051 _v _q h4459
  have p17060 := n17060 _v _q h4653
  have p17137 := n17137 _v _q h4059
  have p17079 := n17079 _v _q h3919
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
  simp only [e51, e57, e196, e2722, e3133, e3138, e3158, e3159, e3919, e3920, e3976, e3981, e4059, e4064, e4101, e4106, e4161, e4166, e4264, e4269, e4306, e4311, e4398, e4403, e4439, e4444, e4459, e4464, e4491, e4496, e4567, e4572, e4653, e4658, e4679, e4684, e4724, e4729, e4791, e4796, e4817, e4822, e4903, e4908, e5195, e6742, e18063] at *
  tauto
theorem n18099 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2722 : (e2722 _v)) (h3133 : (e3133 _v)) (h3158 : (e3158 _v)) (h3919 : (e3919 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4101 : (e4101 _v)) (h4264 : (e4264 _v)) (h4306 : (e4306 _v)) (h4398 : (e4398 _v)) (h4439 : (e4439 _v)) (h4459 : (e4459 _v)) (h4491 : (e4491 _v)) (h4567 : (e4567 _v)) (h4653 : (e4653 _v)) (h4679 : (e4679 _v)) (h4724 : (e4724 _v)) (h4791 : (e4791 _v)) (h4817 : (e4817 _v)) (h4903 : (e4903 _v)) (h5195 : (e5195 _v)) : (e4168 _v) := by
  have p14945 := n14945 _v _q 
  have p18098 := n18098 _v _q h51 h2722 h3133 h3158 h3919 h3976 h4059 h4101 h4264 h4306 h4398 h4439 h4459 h4491 h4567 h4653 h4679 h4724 h4791 h4817 h4903 h5195
  simp only [e4161, e4162, e4166, e4167, e4168, e4955] at *
  tauto
theorem n18101 (_v : Vars) (_q : Query _v)  : (e18100 _v) := by
  by_contra hc
  change ¬ ((¬ (e496 _v)) ∨ (¬ (e3976 _v)) ∨ (¬ (e4373 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e3158 _v)) ∨ (¬ (e4459 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e3919 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e3133 _v)) ∨ (¬ (e4491 _v)) ∨ (¬ (e4724 _v)) ∨ (¬ (e4567 _v)) ∨ (¬ (e4791 _v)) ∨ (¬ (e4398 _v)) ∨ (¬ (e4679 _v)) ∨ (¬ (e4817 _v)) ∨ (¬ (e4264 _v)) ∨ (¬ (e4101 _v)) ∨ (¬ (e4903 _v)) ∨ (¬ (e4439 _v)) ∨ (¬ (e436 _v)) ∨ (e2722 _v)) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h436 : (e436 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))
  have h496 : (e496 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h3133 : (e3133 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h3158 : (e3158 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h3919 : (e3919 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h3976 : (e3976 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h4059 : (e4059 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h4101 : (e4101 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))
  have h4264 : (e4264 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4373 : (e4373 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4398 : (e4398 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))
  have h4439 : (e4439 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))
  have h4459 : (e4459 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h4491 : (e4491 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h4567 : (e4567 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h4679 : (e4679 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))
  have h4724 : (e4724 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h4791 : (e4791 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h4817 : (e4817 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))
  have h4903 : (e4903 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))
  have h6742 : (e6742 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))))))))))))))))))))
  have p18083 := n18083 _v _q h51 h436 h496 h3133 h3158 h3919 h3976 h4059 h4101 h4264 h4306 h4373 h4398 h4439 h4459 h4491 h4567 h4653 h4679 h4724 h4791 h4817 h4903 h6742
  exact p18083
theorem n18102 (_v : Vars) (_q : Query _v) (h467 : (e467 _v)) (h2296 : (e2296 _v)) (h2522 : (e2522 _v)) (h3051 : (e3051 _v)) (h4161 : (e4161 _v)) (h4264 : (e4264 _v)) (h5362 : (e5362 _v)) (h6742 : (e6742 _v)) : (e7895 _v) := by
  have p14589 := n14589 _v _q 
  have p18084 := n18084 _v _q h467 h2296 h2522 h3051 h4161 h4264 h5362 h6742
  simp only [e251, e4367, e4368, e4369, e4370, e6694, e7887, e7895, e7898] at *
  tauto
theorem n18103 (_v : Vars) (_q : Query _v) (h467 : (e467 _v)) (h2296 : (e2296 _v)) (h2522 : (e2522 _v)) (h3051 : (e3051 _v)) (h4161 : (e4161 _v)) (h4264 : (e4264 _v)) (h5362 : (e5362 _v)) (h6742 : (e6742 _v)) : (e4369 _v) := by
  have p16222 := n16222 _v _q 
  have p18102 := n18102 _v _q h467 h2296 h2522 h3051 h4161 h4264 h5362 h6742
  simp only [e4367, e4368, e4369, e4370, e7887, e7888, e7895] at *
  tauto
theorem n18105 (_v : Vars) (_q : Query _v)  : (e18104 _v) := by
  by_contra hc
  change ¬ ((¬ (e191 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4096 _v)) ∨ (e2634 _v) ∨ (¬ (e4903 _v)) ∨ (¬ (e3976 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e3169 _v)) ∨ (¬ (e4567 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e91 _v)) ∨ (e2475 _v) ∨ (¬ (e2125 _v))) at hc
  have h70 : (e70 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))
  have h191 : (e191 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h225 : (e225 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h442 : (e442 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))
  have h488 : (e488 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h2125 : (e2125 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn)))))))))))))))))))))))))))
  have h3069 : (e3069 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h3105 : (e3105 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h3169 : (e3169 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))
  have h3976 : (e3976 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h4096 : (e4096 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4156 : (e4156 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h4199 : (e4199 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))
  have h4260 : (e4260 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h4369 : (e4369 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))
  have h4567 : (e4567 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))
  have h4608 : (e4608 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))
  have h4675 : (e4675 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h4872 : (e4872 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h4903 : (e4903 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h6700 : (e6700 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h8038 : (e8038 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))
  have p18088 := n18088 _v _q h70 h91 h191 h225 h442 h488 h2125 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4567 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  exact p18088
theorem n18106 (_v : Vars) (_q : Query _v) (h5093 : (e5093 _v)) : (e3946 _v) := by
  have p15201 := n15201 _v _q 
  have p15318 := n15318 _v _q h5093
  simp only [e3944, e3945, e3946, e3947, e3948, e3949, e3954] at *
  tauto
theorem n18107 (_v : Vars) (_q : Query _v) (h5093 : (e5093 _v)) : (e4747 _v) := by
  have p14920 := n14920 _v _q 
  have p15323 := n15323 _v _q h5093
  simp only [e4747, e4748, e4752, e4753, e4754, e4755, e4940] at *
  tauto
theorem n18108 (_v : Vars) (_q : Query _v) (h5093 : (e5093 _v)) : (e4491 _v) := by
  have p14969 := n14969 _v _q 
  have p15325 := n15325 _v _q h5093
  simp only [e4491, e4492, e4496, e4497, e4498, e4499, e4960] at *
  tauto
theorem n18109 (_v : Vars) (_q : Query _v) (h5093 : (e5093 _v)) : (e4059 _v) := by
  have p14980 := n14980 _v _q 
  have p15327 := n15327 _v _q h5093
  simp only [e4059, e4060, e4064, e4065, e4066, e4067, e4963] at *
  tauto
theorem n18110 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3855 : (e3855 _v)) (h3937 : (e3937 _v)) (h3976 : (e3976 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5093 : (e5093 _v)) (h6480 : (e6480 _v)) (h6700 : (e6700 _v)) (h7749 : (e7749 _v)) (h8045 : (e8045 _v)) : (e196 _v) := by
  have p18086 := n18086 _v _q 
  have p8575 := n8575 _v _q h6480
  have p11027 := n11027 _v _q h6700
  have p4999 := n4999 _v _q h91
  have p16269 := n16269 _v _q h7749
  have p17223 := n17223 _v _q h5093
  have p5001 := n5001 _v _q h4096
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
  have p4998 := n4998 _v _q h3152
  have p4995 := n4995 _v _q h4369
  have p18108 := n18108 _v _q h5093
  have p4996 := n4996 _v _q h3937
  have p18109 := n18109 _v _q h5093
  simp only [e70, e75, e91, e95, e196, e225, e230, e442, e443, e488, e493, e2125, e2634, e3069, e3074, e3105, e3106, e3152, e3156, e3169, e3170, e3855, e3860, e3937, e3942, e3946, e3947, e3976, e3981, e4059, e4064, e4096, e4097, e4156, e4157, e4199, e4200, e4260, e4261, e4369, e4370, e4398, e4403, e4491, e4496, e4567, e4572, e4608, e4609, e4675, e4676, e4724, e4729, e4747, e4752, e4787, e4788, e4813, e4814, e4872, e4873, e4903, e4908, e5100, e5103, e6480, e6700, e7493, e7494, e7749, e7752, e8045, e8048, e18085] at *
  tauto
theorem n18111 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3855 : (e3855 _v)) (h3937 : (e3937 _v)) (h3976 : (e3976 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5093 : (e5093 _v)) (h6480 : (e6480 _v)) (h6700 : (e6700 _v)) (h7749 : (e7749 _v)) (h8045 : (e8045 _v)) : (e5203 _v) := by
  have p14730 := n14730 _v _q 
  have p18110 := n18110 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3855 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4398 h4567 h4608 h4675 h4724 h4787 h4813 h4872 h4903 h5093 h6480 h6700 h7749 h8045
  simp only [e191, e192, e193, e194, e196, e5193, e5195, e5203, e5206] at *
  tauto
theorem n18112 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2358 : (e2358 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3976 : (e3976 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4572 : (e4572 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h6656 : (e6656 _v)) (h7935 : (e7935 _v)) (h8038 : (e8038 _v)) : (e7819 _v) := by
  have p14994 := n14994 _v _q 
  have p18090 := n18090 _v _q h70 h91 h191 h225 h442 h488 h2358 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4301 h4369 h4572 h4608 h4675 h4787 h4813 h4838 h4872 h4903 h6656 h7935 h8038
  simp only [e2303, e7807, e7812, e7814, e7816, e7817, e7818, e7819, e11046] at *
  tauto
theorem n18113 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2358 : (e2358 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3976 : (e3976 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4572 : (e4572 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h6656 : (e6656 _v)) (h7935 : (e7935 _v)) (h8038 : (e8038 _v)) : (e7489 _v) := by
  have p15221 := n15221 _v _q 
  have p18112 := n18112 _v _q h70 h91 h191 h225 h442 h488 h2358 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4301 h4369 h4572 h4608 h4675 h4787 h4813 h4838 h4872 h4903 h6656 h7935 h8038
  have p18091 := n18091 _v _q h70 h91 h191 h225 h442 h488 h2358 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4301 h4369 h4572 h4608 h4675 h4787 h4813 h4838 h4872 h4903 h6656 h7935 h8038
  simp only [e7812, e7814, e7816, e7817, e7818, e7819, e8456] at *
  tauto
theorem n18115 (_v : Vars) (_q : Query _v)  : (e18114 _v) := by
  by_contra hc
  change ¬ ((e2371 _v) ∨ (¬ (e2536 _v)) ∨ (¬ (e4026 _v)) ∨ (¬ (e4419 _v)) ∨ (¬ (e4546 _v)) ∨ (¬ (e4899 _v)) ∨ (¬ (e4398 _v)) ∨ (¬ (e4477 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e4301 _v)) ∨ (¬ (e3169 _v)) ∨ (¬ (e4562 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e4648 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e4285 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e3855 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e30 _v)) ∨ (¬ (e4491 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e4220 _v)) ∨ (¬ (e3976 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4724 _v))) at hc
  have h30 : (e30 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))))
  have h70 : (e70 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))))))))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))
  have h191 : (e191 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))
  have h225 : (e225 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))))))))))
  have h442 : (e442 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))
  have h488 : (e488 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))
  have h2536 : (e2536 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h3069 : (e3069 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))
  have h3105 : (e3105 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))
  have h3169 : (e3169 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h3855 : (e3855 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))
  have h3946 : (e3946 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))))))))))
  have h3976 : (e3976 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))))))))
  have h4026 : (e4026 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4059 : (e4059 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))))))))))))))
  have h4096 : (e4096 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))))
  have h4139 : (e4139 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h4156 : (e4156 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h4199 : (e4199 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))))))
  have h4220 : (e4220 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))))))))
  have h4260 : (e4260 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))
  have h4285 : (e4285 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))
  have h4301 : (e4301 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h4369 : (e4369 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))
  have h4398 : (e4398 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h4419 : (e4419 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4434 : (e4434 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h4477 : (e4477 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h4491 : (e4491 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))))))
  have h4546 : (e4546 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4562 : (e4562 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h4608 : (e4608 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))
  have h4648 : (e4648 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))
  have h4675 : (e4675 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))))))))))))))))
  have h4724 : (e4724 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn)))))))))))))))))))))))))))))))))))))))))))))
  have h4747 : (e4747 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))))))))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))))))))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h4838 : (e4838 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))
  have h4872 : (e4872 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))
  have h4899 : (e4899 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h6579 : (e6579 _v) := (fun hn => hc (Or.inl hn))
  have p18094 := n18094 _v _q h30 h70 h91 h191 h225 h442 h488 h2536 h3069 h3105 h3152 h3169 h3855 h3937 h3946 h3976 h4026 h4059 h4096 h4139 h4156 h4199 h4220 h4260 h4285 h4301 h4369 h4398 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4724 h4747 h4787 h4813 h4838 h4872 h4899 h6579
  exact p18094
end
end Assembly
