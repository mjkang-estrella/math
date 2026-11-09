import Dag180
import generated.th_lemma_19
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n17962 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2125 : (e2125 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3976 : (e3976 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h6700 : (e6700 _v)) (h8038 : (e8038 _v)) : (e6571 _v) := by
  have p17877 := n17877 _v _q 
  have p253 := n253 _v _q h191
  have p8475 := n8475 _v _q h2125
  have p8602 := n8602 _v _q h8038
  have p5001 := n5001 _v _q h4096
  have p5003 := n5003 _v _q h4199
  have p17129 := n17129 _v _q h4903
  have p5006 := n5006 _v _q h4675
  have p17076 := n17076 _v _q h3976
  have p5007 := n5007 _v _q h225
  have p5008 := n5008 _v _q h4787
  have p5005 := n5005 _v _q h3169
  have p17143 := n17143 _v _q h4567
  have p5010 := n5010 _v _q h70
  have p4981 := n4981 _v _q h4260
  have p4988 := n4988 _v _q h488
  have p4986 := n4986 _v _q h3105
  have p4983 := n4983 _v _q h4813
  have p4994 := n4994 _v _q h3069
  have p4992 := n4992 _v _q h442
  have p4984 := n4984 _v _q h4872
  have p4985 := n4985 _v _q h4156
  have p4991 := n4991 _v _q h4608
  have p4998 := n4998 _v _q h3152
  have p4995 := n4995 _v _q h4369
  have p4996 := n4996 _v _q h3937
  have p4999 := n4999 _v _q h91
  have p11027 := n11027 _v _q h6700
  simp only [e70, e75, e91, e95, e191, e192, e225, e230, e442, e443, e488, e493, e2125, e2358, e2475, e2634, e3069, e3074, e3105, e3106, e3152, e3156, e3169, e3170, e3937, e3942, e3976, e3981, e4096, e4097, e4156, e4157, e4199, e4200, e4260, e4261, e4369, e4370, e4567, e4572, e4608, e4609, e4675, e4676, e4787, e4788, e4813, e4814, e4872, e4873, e4903, e4908, e6480, e6571, e6700, e8038, e17876] at *
  tauto
theorem n17963 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3976 : (e3976 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4572 : (e4572 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h6656 : (e6656 _v)) (h7935 : (e7935 _v)) (h8038 : (e8038 _v)) : (e7489 _v) := by
  have p15340 := n15340 _v _q h8038
  have p11499 := n11499 _v _q h6656
  have p4990 := n4990 _v _q h4648
  have p17074 := n17074 _v _q 
  have p15336 := n15336 _v _q h8038
  have p4989 := n4989 _v _q h4838
  have p4980 := n4980 _v _q h4301
  have p17880 := n17880 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4572 h4608 h4648 h4675 h4787 h4813 h4838 h4872 h4903 h6656 h7935 h8038
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
  have p4979 := n4979 _v _q h4139
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
  have p8663 := n8663 _v _q 
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
  have p16181 := n16181 _v _q 
  have p5255 := n5255 _v _q 
  have p17878 := n17878 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4572 h4608 h4648 h4675 h4787 h4813 h4838 h4872 h4903 h6656 h7935 h8038
  exact FloorCertificate.node_17963 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e61 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2834 _v) (e2849 _v) (e2863 _v) (e2877 _v) (e2879 _v) (e2883 _v) (e2898 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e3164 _v) (e3574 _v) (e4215 _v) (e4541 _v) (e4808 _v) p15340 p11499 p4990 p17074 p15336 p4989 p4980 p17880 p17163 p17170 p16394 p15181 p8486 p8602 p17072 p17091 p17080 p17098 p17078 p253 p4979 p17825 p17087 p17067 p17100 p4991 p16344 p17110 p17115 p17083 p16576 p17058 p17113 p17064 p17102 p13951 p17167 p17096 p16929 p17122 p15360 p17124 p17106 p17108 p17104 p4995 p17117 p17120 p17069 p17141 p17093 p17131 p17053 p4996 p16918 p4998 p16346 p8663 p15194 p4999 p17055 p15198 p5001 p17136 p17127 p15200 p15203 p17798 p5003 p17168 p17129 p5006 p17076 p17147 p5007 p5008 p17133 p5005 p5010 p4981 p15209 p15211 p4988 p4986 p16175 p4983 p17169 p4994 p4992 p4984 p4985 p16181 p5255 p17878
theorem n17964 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h225 : (e225 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h4096 : (e4096 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h8038 : (e8038 _v)) : (e2746 _v) := by
  have p8429 := n8429 _v _q 
  have p17881 := n17881 _v _q h91 h225 h488 h3069 h3105 h3152 h3937 h4096 h4369 h4434 h4608 h4787 h4813 h4838 h4872 h8038
  simp only [e2746, e2793, e6784, e8428] at *
  tauto
theorem n17965 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h225 : (e225 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h4096 : (e4096 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h8038 : (e8038 _v)) : (e3984 _v) := by
  have p14691 := n14691 _v _q 
  have p17964 := n17964 _v _q h91 h225 h488 h3069 h3105 h3152 h3937 h4096 h4369 h4434 h4608 h4787 h4813 h4838 h4872 h8038
  simp only [e2746, e3976, e3977, e3981, e3982, e3983, e3984, e6758, e7456] at *
  tauto
theorem n17966 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h225 : (e225 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h4096 : (e4096 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h8038 : (e8038 _v)) : (e3976 _v) := by
  have p14935 := n14935 _v _q 
  have p17965 := n17965 _v _q h91 h225 h488 h3069 h3105 h3152 h3937 h4096 h4369 h4434 h4608 h4787 h4813 h4838 h4872 h8038
  simp only [e3976, e3977, e3981, e3982, e3983, e3984, e4954] at *
  tauto
theorem n17967 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h225 : (e225 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h4096 : (e4096 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h8038 : (e8038 _v)) : (e4910 _v) := by
  have p14701 := n14701 _v _q 
  have p17881 := n17881 _v _q h91 h225 h488 h3069 h3105 h3152 h3937 h4096 h4369 h4434 h4608 h4787 h4813 h4838 h4872 h8038
  simp only [e2793, e4902, e4903, e4907, e4908, e4909, e4910, e6784, e8381] at *
  tauto
theorem n17968 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h225 : (e225 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h4096 : (e4096 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h8038 : (e8038 _v)) : (e4903 _v) := by
  have p14973 := n14973 _v _q 
  have p17967 := n17967 _v _q h91 h225 h488 h3069 h3105 h3152 h3937 h4096 h4369 h4434 h4608 h4787 h4813 h4838 h4872 h8038
  simp only [e4902, e4903, e4907, e4908, e4909, e4910, e4961] at *
  tauto
theorem n17970 (_v : Vars) (_q : Query _v)  : (e17969 _v) := by
  by_contra hc
  change ¬ ((e2482 _v) ∨ (e13 _v) ∨ (¬ (e4899 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4285 _v)) ∨ (¬ (e4491 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e3976 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4419 _v)) ∨ (¬ (e4546 _v)) ∨ (¬ (e4477 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e4301 _v)) ∨ (¬ (e3169 _v)) ∨ (¬ (e4562 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e4648 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e3069 _v))) at hc
  have h70 : (e70 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h191 : (e191 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))))
  have h225 : (e225 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h442 : (e442 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))))))))
  have h488 : (e488 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))
  have h3069 : (e3069 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn)))))))))))))))))))))))))))))))))))))))
  have h3105 : (e3105 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h3169 : (e3169 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h3946 : (e3946 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h3976 : (e3976 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h4059 : (e4059 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))
  have h4096 : (e4096 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4139 : (e4139 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))
  have h4156 : (e4156 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))
  have h4199 : (e4199 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h4260 : (e4260 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))
  have h4285 : (e4285 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h4301 : (e4301 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))
  have h4369 : (e4369 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))))))))))
  have h4419 : (e4419 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))
  have h4434 : (e4434 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))
  have h4477 : (e4477 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))
  have h4491 : (e4491 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h4546 : (e4546 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))
  have h4562 : (e4562 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))
  have h4608 : (e4608 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))))))))
  have h4648 : (e4648 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))))))
  have h4675 : (e4675 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))
  have h4747 : (e4747 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))
  have h4838 : (e4838 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))
  have h4872 : (e4872 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))))))
  have h4899 : (e4899 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h5093 : (e5093 _v) := (fun hn => hc (Or.inr (Or.inl hn)))
  have h6636 : (e6636 _v) := (fun hn => hc (Or.inl hn))
  have p17883 := n17883 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h3976 h4059 h4096 h4139 h4156 h4199 h4260 h4285 h4301 h4369 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h4899 h5093 h6636
  exact p17883
theorem n17971 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2592 : (e2592 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3585 : (e3585 _v)) (h3855 : (e3855 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4026 : (e4026 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4128 : (e4128 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4220 : (e4220 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4491 : (e4491 _v)) (h4546 : (e4546 _v)) (h4562 : (e4562 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4855 : (e4855 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) (h6579 : (e6579 _v)) (h8398 : (e8398 _v)) : (e7489 _v) := by
  have p4997 := n4997 _v _q h4855
  have p8536 := n8536 _v _q h2592
  have p4996 := n4996 _v _q h3937
  have p4999 := n4999 _v _q h91
  have p17803 := n17803 _v _q h70 h91 h191 h225 h442 h488 h2592 h3069 h3105 h3152 h3169 h3855 h3937 h3946 h3976 h4059 h4096 h4128 h4139 h4156 h4199 h4260 h4301 h4369 h4398 h4419 h4491 h4546 h4562 h4608 h4648 h4675 h4724 h4747 h4787 h4813 h4838 h4872 h4899 h6579
  have p16394 := n16394 _v _q 
  have p4998 := n4998 _v _q h3152
  have p13951 := n13951 _v _q 
  have p16250 := n16250 _v _q h3855
  have p5255 := n5255 _v _q 
  have p5257 := n5257 _v _q 
  have p5001 := n5001 _v _q h4096
  have p5000 := n5000 _v _q h30
  have p17136 := n17136 _v _q 
  have p17128 := n17128 _v _q h4491
  have p17127 := n17127 _v _q 
  have p17230 := n17230 _v _q h6579
  have p5003 := n5003 _v _q h4199
  have p17221 := n17221 _v _q 
  have p5004 := n5004 _v _q h4220
  have p17053 := n17053 _v _q 
  have p17076 := n17076 _v _q h3976
  have p5005 := n5005 _v _q h3169
  have p17056 := n17056 _v _q h3946
  have p5007 := n5007 _v _q h225
  have p5008 := n5008 _v _q h4787
  have p17055 := n17055 _v _q 
  have p17208 := n17208 _v _q h8398
  have p17061 := n17061 _v _q h4747
  have p17147 := n17147 _v _q 
  have p17133 := n17133 _v _q 
  have p5010 := n5010 _v _q h70
  have p17137 := n17137 _v _q h4059
  have p5006 := n5006 _v _q h4675
  have p17094 := n17094 _v _q h4724
  have p4970 := n4970 _v _q h3585
  have p4971 := n4971 _v _q h4419
  have p16929 := n16929 _v _q 
  have p4972 := n4972 _v _q h4899
  have p4973 := n4973 _v _q h4562
  have p4974 := n4974 _v _q h4128
  have p4975 := n4975 _v _q h4026
  have p4976 := n4976 _v _q h4546
  have p4977 := n4977 _v _q h4285
  have p4978 := n4978 _v _q h4477
  have p16181 := n16181 _v _q 
  have p4979 := n4979 _v _q h4139
  have p4980 := n4980 _v _q h4301
  have p4981 := n4981 _v _q h4260
  have p16175 := n16175 _v _q 
  have p4983 := n4983 _v _q h4813
  have p4984 := n4984 _v _q h4872
  have p4985 := n4985 _v _q h4156
  have p17884 := n17884 _v _q h30 h70 h91 h191 h225 h442 h488 h2592 h3069 h3105 h3152 h3169 h3585 h3855 h3937 h3946 h3976 h4026 h4059 h4096 h4128 h4139 h4156 h4199 h4220 h4260 h4285 h4301 h4369 h4398 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4724 h4747 h4787 h4813 h4838 h4855 h4872 h4899 h6579 h8398
  have p4986 := n4986 _v _q h3105
  have p4987 := n4987 _v _q h4434
  have p4988 := n4988 _v _q h488
  have p17074 := n17074 _v _q 
  have p4989 := n4989 _v _q h4838
  have p17072 := n17072 _v _q 
  have p17091 := n17091 _v _q 
  have p17080 := n17080 _v _q 
  have p17098 := n17098 _v _q 
  have p17078 := n17078 _v _q 
  have p253 := n253 _v _q h191
  have p4990 := n4990 _v _q h4648
  have p17087 := n17087 _v _q 
  have p17067 := n17067 _v _q 
  have p17100 := n17100 _v _q 
  have p4991 := n4991 _v _q h4608
  have p4992 := n4992 _v _q h442
  have p17110 := n17110 _v _q 
  have p17115 := n17115 _v _q 
  have p17083 := n17083 _v _q 
  have p16576 := n16576 _v _q 
  have p17058 := n17058 _v _q 
  have p17113 := n17113 _v _q 
  have p17064 := n17064 _v _q 
  have p17102 := n17102 _v _q 
  have p17096 := n17096 _v _q 
  have p4994 := n4994 _v _q h3069
  have p17122 := n17122 _v _q 
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
  have p14849 := n14849 _v _q 
  exact FloorCertificate.node_17971 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e61 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2834 _v) (e2849 _v) (e2863 _v) (e2877 _v) (e2879 _v) (e2883 _v) (e2898 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2913 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e3164 _v) (e3574 _v) (e4215 _v) (e4324 _v) (e4541 _v) (e4808 _v) p4997 p8536 p4996 p4999 p17803 p16394 p4998 p13951 p16250 p5255 p5257 p5001 p5000 p17136 p17128 p17127 p17230 p5003 p17221 p5004 p17053 p17076 p5005 p17056 p5007 p5008 p17055 p17208 p17061 p17147 p17133 p5010 p17137 p5006 p17094 p4970 p4971 p16929 p4972 p4973 p4974 p4975 p4976 p4977 p4978 p16181 p4979 p4980 p4981 p16175 p4983 p4984 p4985 p17884 p4986 p4987 p4988 p17074 p4989 p17072 p17091 p17080 p17098 p17078 p253 p4990 p17087 p17067 p17100 p4991 p4992 p17110 p17115 p17083 p16576 p17058 p17113 p17064 p17102 p17096 p4994 p17122 p17124 p17106 p17108 p17104 p4995 p17117 p17120 p17069 p17141 p17093 p17131 p14849
theorem n17972 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2536 : (e2536 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3855 : (e3855 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4026 : (e4026 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4220 : (e4220 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4491 : (e4491 _v)) (h4546 : (e4546 _v)) (h4562 : (e4562 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) (h6672 : (e6672 _v)) : (e7493 _v) := by
  have p15195 := n15195 _v _q 
  have p17886 := n17886 _v _q h30 h70 h91 h191 h225 h442 h488 h2536 h3069 h3105 h3152 h3169 h3855 h3937 h3946 h3976 h4026 h4059 h4096 h4139 h4156 h4199 h4220 h4260 h4285 h4301 h4369 h4398 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4724 h4747 h4787 h4813 h4838 h4872 h4899 h6672
  simp only [e7493, e7494, e7495, e7496, e7497, e7498, e7517] at *
  tauto
theorem n17973 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2536 : (e2536 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3855 : (e3855 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4026 : (e4026 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4220 : (e4220 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4491 : (e4491 _v)) (h4546 : (e4546 _v)) (h4562 : (e4562 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) (h6579 : (e6579 _v)) (h6672 : (e6672 _v)) : (e7489 _v) := by
  have p16977 := n16977 _v _q 
  have p11132 := n11132 _v _q h2536
  have p4971 := n4971 _v _q h4419
  have p15475 := n15475 _v _q h6672
  have p13951 := n13951 _v _q 
  have p17972 := n17972 _v _q h30 h70 h91 h191 h225 h442 h488 h2536 h3069 h3105 h3152 h3169 h3855 h3937 h3946 h3976 h4026 h4059 h4096 h4139 h4156 h4199 h4220 h4260 h4285 h4301 h4369 h4398 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4724 h4747 h4787 h4813 h4838 h4872 h4899 h6672
  have p4976 := n4976 _v _q h4546
  have p4972 := n4972 _v _q h4899
  have p5257 := n5257 _v _q 
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
  have p17230 := n17230 _v _q h6579
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
  exact FloorCertificate.node_17973 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e61 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2834 _v) (e2849 _v) (e2863 _v) (e2877 _v) (e2879 _v) (e2883 _v) (e2898 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2913 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e3164 _v) (e4215 _v) (e4541 _v) (e4808 _v) p16977 p11132 p4971 p15475 p13951 p17972 p4976 p4972 p5257 p17831 p17134 p16929 p4978 p4979 p4980 p5005 p16394 p15450 p4973 p4985 p4987 p17221 p4983 p16175 p17074 p17230 p4988 p4981 p4989 p17072 p4986 p17080 p17078 p17091 p253 p17098 p4990 p17100 p4984 p17067 p17087 p4991 p4992 p17115 p17083 p17110 p16576 p17058 p17113 p17102 p17096 p17106 p4977 p17122 p17104 p4995 p17124 p17108 p4994 p17117 p17120 p17069 p15183 p17093 p17141 p17131 p4996 p4999 p4998 p16250 p5001 p5000 p17136 p17128 p17127 p5003 p5004 p17053 p17076 p17056 p5007 p5008 p17055 p17061 p17147 p17133 p5010 p17137 p5006 p17094 p17064
theorem n17974 (_v : Vars) (_q : Query _v)  : (e5021 _v) := by
  simp only [e3854, e3855, e3859, e3860, e3861, e5021] at *
  tauto
theorem n17975 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4026 : (e4026 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4220 : (e4220 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4491 : (e4491 _v)) (h4546 : (e4546 _v)) (h4562 : (e4562 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) (h6531 : (e6531 _v)) : (e3854 _v) := by
  have p17974 := n17974 _v _q 
  have p17892 := n17892 _v _q h30 h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h3976 h4026 h4059 h4096 h4139 h4156 h4199 h4220 h4260 h4285 h4301 h4369 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h4899 h6531
  simp only [e3854, e3855, e3859, e3860, e3861, e3862, e5021] at *
  tauto
theorem n17976 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4026 : (e4026 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4220 : (e4220 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4491 : (e4491 _v)) (h4546 : (e4546 _v)) (h4562 : (e4562 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) (h6531 : (e6531 _v)) : (e7489 _v) := by
  have p10896 := n10896 _v _q 
  have p5391 := n5391 _v _q 
  have p16452 := n16452 _v _q h6531
  have p13951 := n13951 _v _q 
  have p17975 := n17975 _v _q h30 h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h3976 h4026 h4059 h4096 h4139 h4156 h4199 h4220 h4260 h4285 h4301 h4369 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h4899 h6531
  have p11358 := n11358 _v _q h6531
  have p17860 := n17860 _v _q h30 h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h3976 h4026 h4059 h4096 h4139 h4156 h4199 h4220 h4260 h4285 h4301 h4369 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h4899 h6531
  have p17893 := n17893 _v _q h30 h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h3976 h4026 h4059 h4096 h4139 h4156 h4199 h4220 h4260 h4285 h4301 h4369 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h4899 h6531
  have p4975 := n4975 _v _q h4026
  have p17896 := n17896 _v _q h30 h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h3976 h4026 h4059 h4096 h4139 h4156 h4199 h4220 h4260 h4285 h4301 h4369 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h4899 h6531
  have p17898 := n17898 _v _q h30 h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h3976 h4026 h4059 h4096 h4139 h4156 h4199 h4220 h4260 h4285 h4301 h4369 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h4899 h6531
  have p17137 := n17137 _v _q h4059
  have p5006 := n5006 _v _q h4675
  have p15477 := n15477 _v _q h6531
  have p5010 := n5010 _v _q h70
  have p16487 := n16487 _v _q h6531
  have p17064 := n17064 _v _q 
  have p16181 := n16181 _v _q 
  have p4971 := n4971 _v _q h4419
  have p4976 := n4976 _v _q h4546
  have p4972 := n4972 _v _q h4899
  have p14849 := n14849 _v _q 
  have p16929 := n16929 _v _q 
  have p4978 := n4978 _v _q h4477
  have p4979 := n4979 _v _q h4139
  have p4980 := n4980 _v _q h4301
  have p5005 := n5005 _v _q h3169
  have p16394 := n16394 _v _q 
  have p4973 := n4973 _v _q h4562
  have p4985 := n4985 _v _q h4156
  have p4987 := n4987 _v _q h4434
  have p16913 := n16913 _v _q 
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
  have p16178 := n16178 _v _q 
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
  have p17133 := n17133 _v _q 
  have p17093 := n17093 _v _q 
  have p17141 := n17141 _v _q 
  have p17131 := n17131 _v _q 
  have p4996 := n4996 _v _q h3937
  have p4999 := n4999 _v _q h91
  have p4998 := n4998 _v _q h3152
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
  have p15463 := n15463 _v _q h6531
  have p17151 := n17151 _v _q 
  have p5257 := n5257 _v _q 
  have p17861 := n17861 _v _q h30 h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h3976 h4026 h4059 h4096 h4139 h4156 h4199 h4220 h4260 h4285 h4301 h4369 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h4899 h6531
  have p16184 := n16184 _v _q 
  exact FloorCertificate.node_17976 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e61 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2834 _v) (e2849 _v) (e2863 _v) (e2877 _v) (e2879 _v) (e2883 _v) (e2898 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2913 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e3164 _v) (e3262 _v) (e3574 _v) (e3846 _v) (e4215 _v) (e4324 _v) (e4541 _v) (e4696 _v) (e4808 _v) p10896 p5391 p16452 p13951 p17975 p11358 p17860 p17893 p4975 p17896 p17898 p17137 p5006 p15477 p5010 p16487 p17064 p16181 p4971 p4976 p4972 p14849 p16929 p4978 p4979 p4980 p5005 p16394 p4973 p4985 p4987 p16913 p4983 p16175 p17074 p4988 p4981 p4989 p17072 p4986 p17080 p17078 p17091 p253 p17098 p4990 p17100 p4984 p17067 p17087 p4991 p4992 p17115 p17083 p17110 p16576 p17058 p17113 p16178 p17102 p17096 p17106 p4977 p17122 p17104 p4995 p17124 p17108 p4994 p17117 p17120 p17069 p17133 p17093 p17141 p17131 p4996 p4999 p4998 p5001 p5000 p17136 p17128 p17127 p5003 p5004 p17053 p17076 p17056 p5007 p5008 p17055 p17061 p17147 p15463 p17151 p5257 p17861 p16184
theorem n17978 (_v : Vars) (_q : Query _v)  : (e17977 _v) := by
  by_contra hc
  change ¬ ((e2697 _v) ∨ (¬ (e3855 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e3267 _v)) ∨ (¬ (e3585 _v)) ∨ (¬ (e4419 _v)) ∨ (¬ (e4899 _v)) ∨ (¬ (e4562 _v)) ∨ (¬ (e4128 _v)) ∨ (¬ (e4546 _v)) ∨ (¬ (e4285 _v)) ∨ (¬ (e4477 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e4301 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4398 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e2799 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e4648 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e4855 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e30 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e3971 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e3169 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e70 _v))) at hc
  have h30 : (e30 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))))))))
  have h70 : (e70 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn)))))))))))))))))))))))))))))))))))))))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))))))
  have h191 : (e191 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))
  have h225 : (e225 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))))))))))))))
  have h442 : (e442 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))
  have h488 : (e488 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))
  have h2799 : (e2799 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))
  have h3069 : (e3069 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))
  have h3105 : (e3105 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))))))
  have h3169 : (e3169 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))))))))))))
  have h3267 : (e3267 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h3585 : (e3585 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h3855 : (e3855 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))))
  have h3946 : (e3946 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))))))))))
  have h3971 : (e3971 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))))))))))
  have h4059 : (e4059 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4096 : (e4096 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))))))))
  have h4128 : (e4128 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h4139 : (e4139 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h4156 : (e4156 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))
  have h4199 : (e4199 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))))))))))))
  have h4260 : (e4260 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h4285 : (e4285 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h4301 : (e4301 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h4369 : (e4369 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))
  have h4398 : (e4398 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))
  have h4419 : (e4419 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h4434 : (e4434 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))
  have h4477 : (e4477 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h4546 : (e4546 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h4562 : (e4562 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h4608 : (e4608 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))
  have h4648 : (e4648 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))
  have h4675 : (e4675 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))))))))))))))
  have h4747 : (e4747 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))))))))))))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))
  have h4838 : (e4838 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))
  have h4855 : (e4855 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))))
  have h4872 : (e4872 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))
  have h4899 : (e4899 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h6732 : (e6732 _v) := (fun hn => hc (Or.inl hn))
  have p17899 := n17899 _v _q h30 h70 h91 h191 h225 h442 h488 h2799 h3069 h3105 h3152 h3169 h3267 h3585 h3855 h3937 h3946 h3971 h4059 h4096 h4128 h4139 h4156 h4199 h4260 h4285 h4301 h4369 h4398 h4419 h4434 h4477 h4546 h4562 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4855 h4872 h4899 h6732
  exact p17899
theorem n17979 (_v : Vars) (_q : Query _v) (h6684 : (e6684 _v)) : (e4156 _v) := by
  have p11524 := n11524 _v _q 
  have p17901 := n17901 _v _q h6684
  simp only [e4156, e4157, e4158, e4159, e7660, e7661, e7668] at *
  tauto
theorem n17980 (_v : Vars) (_q : Query _v) (h6684 : (e6684 _v)) : (e4369 _v) := by
  have p16222 := n16222 _v _q 
  have p17903 := n17903 _v _q h6684
  simp only [e4367, e4368, e4369, e4370, e7887, e7888, e7895] at *
  tauto
theorem n17981 (_v : Vars) (_q : Query _v) (h6684 : (e6684 _v)) : (e4260 _v) := by
  have p15824 := n15824 _v _q 
  have p17905 := n17905 _v _q h6684
  simp only [e4258, e4259, e4260, e4261, e7781, e7782, e7789] at *
  tauto
theorem n17982 (_v : Vars) (_q : Query _v) (h6684 : (e6684 _v)) : (e4675 _v) := by
  have p15965 := n15965 _v _q 
  have p17907 := n17907 _v _q h6684
  simp only [e4673, e4674, e4675, e4676, e8166, e8167, e8174] at *
  tauto
theorem n17983 (_v : Vars) (_q : Query _v) (h6684 : (e6684 _v)) : (e4787 _v) := by
  have p15670 := n15670 _v _q 
  have p17909 := n17909 _v _q h6684
  simp only [e4785, e4786, e4787, e4788, e8267, e8268, e8275] at *
  tauto
theorem n17984 (_v : Vars) (_q : Query _v) (h6684 : (e6684 _v)) : (e4199 _v) := by
  have p16212 := n16212 _v _q 
  have p17911 := n17911 _v _q h6684
  simp only [e4199, e4200, e4201, e4202, e7703, e7704, e7709] at *
  tauto
theorem n17985 (_v : Vars) (_q : Query _v) (h6684 : (e6684 _v)) : (e225 _v) := by
  have p16653 := n16653 _v _q 
  have p17913 := n17913 _v _q h6684
  simp only [e225, e227, e230, e231, e5231, e5232, e5253] at *
  tauto
theorem n17986 (_v : Vars) (_q : Query _v) (h6684 : (e6684 _v)) : (e4434 _v) := by
  have p15307 := n15307 _v _q 
  have p17915 := n17915 _v _q h6684
  simp only [e4434, e4435, e4436, e4437, e7947, e7948, e7955] at *
  tauto
theorem n17987 (_v : Vars) (_q : Query _v) (h6684 : (e6684 _v)) : (e70 _v) := by
  have p15648 := n15648 _v _q 
  have p17917 := n17917 _v _q h6684
  simp only [e70, e72, e75, e76, e5118, e5119, e7441] at *
  tauto
theorem n17988 (_v : Vars) (_q : Query _v) (h6684 : (e6684 _v)) : (e4139 _v) := by
  have p16281 := n16281 _v _q 
  have p17919 := n17919 _v _q h6684
  simp only [e4139, e4140, e4141, e4142, e7634, e7635, e7640] at *
  tauto
theorem n17989 (_v : Vars) (_q : Query _v) (h6684 : (e6684 _v)) : (e488 _v) := by
  have p15090 := n15090 _v _q 
  have p17921 := n17921 _v _q h6684
  simp only [e488, e490, e493, e494, e5402, e5403, e7821] at *
  tauto
theorem n17990 (_v : Vars) (_q : Query _v) (h6684 : (e6684 _v)) : (e3152 _v) := by
  have p15776 := n15776 _v _q 
  have p17923 := n17923 _v _q h6684
  simp only [e3150, e3152, e3155, e3156, e6878, e6879, e8223] at *
  tauto
theorem n17991 (_v : Vars) (_q : Query _v) (h6684 : (e6684 _v)) : (e4419 _v) := by
  have p16347 := n16347 _v _q 
  have p17925 := n17925 _v _q h6684
  simp only [e4417, e4418, e4419, e4420, e7921, e7922, e7927] at *
  tauto
theorem n17992 (_v : Vars) (_q : Query _v) (h6684 : (e6684 _v)) : (e4838 _v) := by
  have p16285 := n16285 _v _q 
  have p17927 := n17927 _v _q h6684
  simp only [e4836, e4837, e4838, e4839, e8301, e8302, e8307] at *
  tauto
theorem n17993 (_v : Vars) (_q : Query _v) (h6684 : (e6684 _v)) : (e4813 _v) := by
  have p16259 := n16259 _v _q 
  have p17929 := n17929 _v _q h6684
  simp only [e4811, e4812, e4813, e4814, e8284, e8285, e8292] at *
  tauto
theorem n17994 (_v : Vars) (_q : Query _v) (h6684 : (e6684 _v)) : (e442 _v) := by
  have p16149 := n16149 _v _q 
  have p17931 := n17931 _v _q h6684
  simp only [e440, e441, e442, e443, e5360, e5361, e5370] at *
  tauto
theorem n17995 (_v : Vars) (_q : Query _v) (h6684 : (e6684 _v)) : (e4872 _v) := by
  have p14999 := n14999 _v _q 
  have p17933 := n17933 _v _q h6684
  simp only [e4872, e4873, e4874, e4875, e8350, e8351, e8358] at *
  tauto
theorem n17996 (_v : Vars) (_q : Query _v) (h6684 : (e6684 _v)) : (e4608 _v) := by
  have p15033 := n15033 _v _q 
  have p17935 := n17935 _v _q h6684
  simp only [e4608, e4609, e4610, e4611, e8095, e8096, e8103] at *
  tauto
theorem n17997 (_v : Vars) (_q : Query _v) (h6684 : (e6684 _v)) : (e4096 _v) := by
  have p15703 := n15703 _v _q 
  have p17937 := n17937 _v _q h6684
  simp only [e4096, e4097, e4098, e4099, e7589, e7590, e7597] at *
  tauto
theorem n17998 (_v : Vars) (_q : Query _v) (h6684 : (e6684 _v)) : (e3937 _v) := by
  have p15012 := n15012 _v _q 
  have p17939 := n17939 _v _q h6684
  simp only [e3937, e3939, e3942, e3943, e7415, e7416, e7633] at *
  tauto
theorem n17999 (_v : Vars) (_q : Query _v) (h6684 : (e6684 _v)) : (e91 _v) := by
  have p16235 := n16235 _v _q 
  have p17941 := n17941 _v _q h6684
  simp only [e89, e91, e94, e95, e5134, e5135, e7983] at *
  tauto
theorem n18001 (_v : Vars) (_q : Query _v)  : (e18000 _v) := by
  by_contra hc
  change ¬ ((e214 _v) ∨ (¬ (e436 _v)) ∨ (¬ (e496 _v)) ∨ (¬ (e4373 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e3158 _v)) ∨ (¬ (e4459 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e3919 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e3133 _v)) ∨ (¬ (e4491 _v)) ∨ (¬ (e4724 _v)) ∨ (¬ (e4567 _v)) ∨ (¬ (e4791 _v)) ∨ (¬ (e4398 _v)) ∨ (¬ (e4679 _v)) ∨ (¬ (e4817 _v)) ∨ (¬ (e4264 _v)) ∨ (¬ (e4101 _v)) ∨ (¬ (e4903 _v)) ∨ (¬ (e4439 _v)) ∨ (¬ (e3976 _v)) ∨ (e2722 _v)) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h436 : (e436 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h496 : (e496 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h3133 : (e3133 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h3158 : (e3158 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h3919 : (e3919 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h3976 : (e3976 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))
  have h4059 : (e4059 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h4101 : (e4101 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))
  have h4264 : (e4264 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4373 : (e4373 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4398 : (e4398 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))
  have h4439 : (e4439 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))
  have h4459 : (e4459 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h4491 : (e4491 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h4567 : (e4567 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h4679 : (e4679 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))
  have h4724 : (e4724 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h4791 : (e4791 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))
  have h4817 : (e4817 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))
  have h4903 : (e4903 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))
  have h5223 : (e5223 _v) := (fun hn => hc (Or.inl hn))
  have h6742 : (e6742 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn)))))))))))))))))))))))))
  have p17943 := n17943 _v _q h51 h436 h496 h3133 h3158 h3919 h3976 h4059 h4101 h4264 h4306 h4373 h4398 h4439 h4459 h4491 h4567 h4653 h4679 h4724 h4791 h4817 h4903 h5223 h6742
  exact p17943
theorem n18002 (_v : Vars) (_q : Query _v) (h2296 : (e2296 _v)) (h2468 : (e2468 _v)) (h4264 : (e4264 _v)) (h4373 : (e4373 _v)) (h4817 : (e4817 _v)) (h4872 : (e4872 _v)) (h5362 : (e5362 _v)) (h5392 : (e5392 _v)) : (e7660 _v) := by
  have p11524 := n11524 _v _q 
  have p17954 := n17954 _v _q h2296 h2468 h4264 h4373 h4817 h4872 h5362 h5392
  simp only [e4156, e4157, e4158, e4159, e7660, e7661] at *
  tauto
theorem n18003 (_v : Vars) (_q : Query _v) (h2296 : (e2296 _v)) (h2468 : (e2468 _v)) (h4264 : (e4264 _v)) (h4373 : (e4373 _v)) (h4817 : (e4817 _v)) (h4872 : (e4872 _v)) (h5362 : (e5362 _v)) (h5392 : (e5392 _v)) : (e2351 _v) := by
  have p14544 := n14544 _v _q 
  have p18002 := n18002 _v _q h2296 h2468 h4264 h4373 h4817 h4872 h5362 h5392
  simp only [e2351, e4156, e4157, e4158, e4159, e7660, e7668, e7671] at *
  tauto
theorem n18004 (_v : Vars) (_q : Query _v) (h2296 : (e2296 _v)) (h2468 : (e2468 _v)) (h4264 : (e4264 _v)) (h4373 : (e4373 _v)) (h4817 : (e4817 _v)) (h4872 : (e4872 _v)) (h5362 : (e5362 _v)) (h5392 : (e5392 _v)) : (e4169 _v) := by
  have p14695 := n14695 _v _q 
  have p18003 := n18003 _v _q h2296 h2468 h4264 h4373 h4817 h4872 h5362 h5392
  simp only [e2351, e4161, e4162, e4166, e4167, e4168, e4169, e6575, e7674] at *
  tauto
theorem n18005 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) (h467 : (e467 _v)) (h2296 : (e2296 _v)) (h2522 : (e2522 _v)) (h3051 : (e3051 _v)) (h4161 : (e4161 _v)) (h4264 : (e4264 _v)) (h5362 : (e5362 _v)) (h6742 : (e6742 _v)) : (e5249 _v) := by
  have p8682 := n8682 _v _q 
  have p17956 := n17956 _v _q h251 h467 h2296 h2522 h3051 h4161 h4264 h5362 h6742
  simp only [e5237, e5240, e5247, e5248, e5249, e5252] at *
  tauto
theorem n18006 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2722 : (e2722 _v)) (h3133 : (e3133 _v)) (h3158 : (e3158 _v)) (h3919 : (e3919 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4101 : (e4101 _v)) (h4161 : (e4161 _v)) (h4264 : (e4264 _v)) (h4306 : (e4306 _v)) (h4398 : (e4398 _v)) (h4439 : (e4439 _v)) (h4459 : (e4459 _v)) (h4491 : (e4491 _v)) (h4567 : (e4567 _v)) (h4653 : (e4653 _v)) (h4679 : (e4679 _v)) (h4724 : (e4724 _v)) (h4791 : (e4791 _v)) (h4817 : (e4817 _v)) (h4903 : (e4903 _v)) (h5195 : (e5195 _v)) : (e5387 _v) := by
  have p15084 := n15084 _v _q 
  have p17958 := n17958 _v _q h51 h2722 h3133 h3158 h3919 h3976 h4059 h4101 h4161 h4264 h4306 h4398 h4439 h4459 h4491 h4567 h4653 h4679 h4724 h4791 h4817 h4903 h5195
  simp only [e5375, e5378, e5385, e5386, e5387, e8473] at *
  tauto
theorem n18007 (_v : Vars) (_q : Query _v) (h225 : (e225 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3855 : (e3855 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4491 : (e4491 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5100 : (e5100 _v)) (h5195 : (e5195 _v)) (h6700 : (e6700 _v)) (h7493 : (e7493 _v)) (h7749 : (e7749 _v)) (h8045 : (e8045 _v)) : (e6454 _v) := by
  have p17961 := n17961 _v _q 
  have p15219 := n15219 _v _q h5195
  have p4981 := n4981 _v _q h4260
  have p5001 := n5001 _v _q h4096
  have p11027 := n11027 _v _q h6700
  have p17056 := n17056 _v _q h3946
  have p15260 := n15260 _v _q h5195
  have p17159 := n17159 _v _q h5100
  have p17129 := n17129 _v _q h4903
  have p17076 := n17076 _v _q h3976
  have p5007 := n5007 _v _q h225
  have p5008 := n5008 _v _q h4787
  have p17155 := n17155 _v _q h7493
  have p17157 := n17157 _v _q h8045
  have p17061 := n17061 _v _q h4747
  have p4988 := n4988 _v _q h488
  have p4986 := n4986 _v _q h3105
  have p4983 := n4983 _v _q h4813
  have p17094 := n17094 _v _q h4724
  have p4994 := n4994 _v _q h3069
  have p4984 := n4984 _v _q h4872
  have p4985 := n4985 _v _q h4156
  have p17134 := n17134 _v _q h4398
  have p16250 := n16250 _v _q h3855
  have p12839 := n12839 _v _q h5195
  have p4998 := n4998 _v _q h3152
  have p4995 := n4995 _v _q h4369
  have p17128 := n17128 _v _q h4491
  have p4996 := n4996 _v _q h3937
  have p17137 := n17137 _v _q h4059
  have p16269 := n16269 _v _q h7749
  have p15263 := n15263 _v _q h5195
  simp only [e225, e230, e488, e493, e2061, e2358, e2529, e2634, e3069, e3074, e3105, e3106, e3152, e3156, e3271, e3276, e3855, e3860, e3937, e3942, e3946, e3947, e3976, e3981, e4059, e4064, e4096, e4097, e4156, e4157, e4260, e4261, e4369, e4370, e4398, e4403, e4491, e4496, e4653, e4658, e4724, e4729, e4747, e4752, e4787, e4788, e4813, e4814, e4872, e4873, e4903, e4908, e5100, e5103, e6454, e6571, e6700, e7493, e7494, e7749, e7752, e8045, e8048, e8310, e17960] at *
  tauto
theorem n18008 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2125 : (e2125 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3976 : (e3976 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h6700 : (e6700 _v)) (h8038 : (e8038 _v)) : (e6746 _v) := by
  have p17962 := n17962 _v _q h70 h91 h191 h225 h442 h488 h2125 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4567 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  have p8602 := n8602 _v _q h8038
  have p4016 := n4016 _v _q 
  exact FloorCertificate.node_18008 (e2 _v) (e7 _v) (e9 _v) (e45 _v) (e110 _v) p17962 p8602 p4016
theorem n18009 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2125 : (e2125 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3976 : (e3976 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h6700 : (e6700 _v)) (h8038 : (e8038 _v)) : (e7630 _v) := by
  have p15152 := n15152 _v _q 
  have p18008 := n18008 _v _q h70 h91 h191 h225 h442 h488 h2125 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4567 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  simp only [e2740, e6746, e7606, e7607, e7608, e7609, e7610, e7630, e10951] at *
  tauto
end
end Assembly
