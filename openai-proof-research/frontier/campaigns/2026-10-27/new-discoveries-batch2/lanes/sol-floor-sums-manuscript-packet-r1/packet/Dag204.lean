import Dag203
import generated.th_lemma_24
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n19097 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3271 : (e3271 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h7807 : (e7807 _v)) : (e7170 _v) := by
  have p14427 := n14427 _v _q 
  have p19096 := n19096 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3271 h3937 h3946 h3976 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4653 h4675 h4747 h4787 h4813 h4838 h4872 h4903 h7807
  change (e2536 _v) ∨ (¬ (e7169 _v)) at p14427
  change (¬ (e2536 _v)) at p19096
  rcases p14427 with hlit | hlit
  · exact (False.elim (p19096 hlit))
  · exact hlit
theorem n19098 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3271 : (e3271 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h7807 : (e7807 _v)) : (e3585 _v) := by
  have p14783 := n14783 _v _q 
  have p19097 := n19097 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3271 h3937 h3946 h3976 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4653 h4675 h4747 h4787 h4813 h4838 h4872 h4903 h7807
  change (e7169 _v) ∨ (e3585 _v) at p14783
  change (¬ (e7169 _v)) at p19097
  rcases p14783 with hlit | hlit
  · exact (False.elim (p19097 hlit))
  · exact hlit
theorem n19099 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3271 : (e3271 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h7807 : (e7807 _v)) : (e7489 _v) := by
  have p19098 := n19098 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3271 h3937 h3946 h3976 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4653 h4675 h4747 h4787 h4813 h4838 h4872 h4903 h7807
  have p16181 := n16181 _v _q 
  have p17136 := n17136 _v _q 
  have p16175 := n16175 _v _q 
  have p19082 := n19082 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4653 h4675 h4747 h4787 h4813 h4838 h4872
  have p17053 := n17053 _v _q 
  have p5003 := n5003 _v _q h4199
  have p15485 := n15485 _v _q h7807
  have p10893 := n10893 _v _q 
  have p17127 := n17127 _v _q 
  have p17129 := n17129 _v _q h4903
  have p5005 := n5005 _v _q h3169
  have p13951 := n13951 _v _q 
  have p5008 := n5008 _v _q h4787
  have p17060 := n17060 _v _q h4653
  have p17165 := n17165 _v _q h3271
  have p19073 := n19073 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p17061 := n17061 _v _q h4747
  have p17055 := n17055 _v _q 
  have p17147 := n17147 _v _q 
  have p16977 := n16977 _v _q 
  have p17058 := n17058 _v _q 
  have p17786 := n17786 _v _q h7807
  have p5006 := n5006 _v _q h4675
  have p17137 := n17137 _v _q h4059
  have p4998 := n4998 _v _q h3152
  have p17076 := n17076 _v _q h3976
  have p17056 := n17056 _v _q h3946
  have p15373 := n15373 _v _q h7807
  have p5007 := n5007 _v _q h225
  have p4971 := n4971 _v _q h4419
  have p17064 := n17064 _v _q 
  have p16929 := n16929 _v _q 
  have p4980 := n4980 _v _q h4301
  have p17067 := n17067 _v _q 
  have p4979 := n4979 _v _q h4139
  have p19074 := n19074 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p16994 := n16994 _v _q 
  have p19075 := n19075 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p4985 := n4985 _v _q h4156
  have p17074 := n17074 _v _q 
  have p4987 := n4987 _v _q h4434
  have p5010 := n5010 _v _q h70
  have p4988 := n4988 _v _q h488
  have p4981 := n4981 _v _q h4260
  have p4983 := n4983 _v _q h4813
  have p19066 := n19066 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p17072 := n17072 _v _q 
  have p17080 := n17080 _v _q 
  have p17078 := n17078 _v _q 
  have p4989 := n4989 _v _q h4838
  have p17091 := n17091 _v _q 
  have p4986 := n4986 _v _q h3105
  have p4978 := n4978 _v _q h4477
  have p17100 := n17100 _v _q 
  have p17098 := n17098 _v _q 
  have p4984 := n4984 _v _q h4872
  have p17087 := n17087 _v _q 
  have p4991 := n4991 _v _q h4608
  have p4992 := n4992 _v _q h442
  have p18959 := n18959 _v _q h7807
  have p17083 := n17083 _v _q 
  have p16576 := n16576 _v _q 
  have p16778 := n16778 _v _q 
  have p17110 := n17110 _v _q 
  have p17115 := n17115 _v _q 
  have p253 := n253 _v _q h191
  have p17106 := n17106 _v _q 
  have p17104 := n17104 _v _q 
  have p17096 := n17096 _v _q 
  have p17124 := n17124 _v _q 
  have p17102 := n17102 _v _q 
  have p17108 := n17108 _v _q 
  have p4994 := n4994 _v _q h3069
  have p17117 := n17117 _v _q 
  have p17120 := n17120 _v _q 
  have p17113 := n17113 _v _q 
  have p17122 := n17122 _v _q 
  have p4995 := n4995 _v _q h4369
  have p17133 := n17133 _v _q 
  have p17093 := n17093 _v _q 
  have p17141 := n17141 _v _q 
  have p17069 := n17069 _v _q 
  have p17131 := n17131 _v _q 
  have p4999 := n4999 _v _q h91
  have p5001 := n5001 _v _q h4096
  have p4996 := n4996 _v _q h3937
  have p19041 := n19041 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p16791 := n16791 _v _q 
  have p19080 := n19080 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4653 h4675 h4747 h4787 h4813 h4838 h4872
  have p19096 := n19096 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3271 h3937 h3946 h3976 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4653 h4675 h4747 h4787 h4813 h4838 h4872 h4903 h7807
  have p11350 := n11350 _v _q h7807
  have p5255 := n5255 _v _q 
  exact FloorCertificate.node_19099 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e61 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2834 _v) (e2849 _v) (e2863 _v) (e2877 _v) (e2883 _v) (e2898 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e3164 _v) (e3574 _v) (e4215 _v) (e4541 _v) (e4808 _v) p19098 p16181 p17136 p16175 p19082 p17053 p5003 p15485 p10893 p17127 p17129 p5005 p13951 p5008 p17060 p17165 p19073 p17061 p17055 p17147 p16977 p17058 p17786 p5006 p17137 p4998 p17076 p17056 p15373 p5007 p4971 p17064 p16929 p4980 p17067 p4979 p19074 p16994 p19075 p4985 p17074 p4987 p5010 p4988 p4981 p4983 p19066 p17072 p17080 p17078 p4989 p17091 p4986 p4978 p17100 p17098 p4984 p17087 p4991 p4992 p18959 p17083 p16576 p16778 p17110 p17115 p253 p17106 p17104 p17096 p17124 p17102 p17108 p4994 p17117 p17120 p17113 p17122 p4995 p17133 p17093 p17141 p17069 p17131 p4999 p5001 p4996 p19041 p16791 p19080 p19096 p11350 p5255
theorem n19101 (_v : Vars) (_q : Query _v)  : (e19100 _v) := by
  by_contra hc
  change ¬ ((e2303 _v) ∨ (¬ (e4199 _v)) ∨ (¬ (e4903 _v)) ∨ (¬ (e3169 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e3271 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e3976 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4419 _v)) ∨ (¬ (e4301 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4477 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e3937 _v))) at hc
  have h70 : (e70 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))))
  have h191 : (e191 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))
  have h225 : (e225 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h442 : (e442 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))
  have h488 : (e488 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))
  have h3069 : (e3069 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))
  have h3105 : (e3105 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h3169 : (e3169 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h3271 : (e3271 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn)))))))))))))))))))))))))))))))))))
  have h3946 : (e3946 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h3976 : (e3976 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h4059 : (e4059 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h4096 : (e4096 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))))))
  have h4139 : (e4139 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))
  have h4156 : (e4156 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))
  have h4199 : (e4199 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h4260 : (e4260 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))
  have h4301 : (e4301 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))
  have h4369 : (e4369 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))))
  have h4419 : (e4419 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h4434 : (e4434 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))
  have h4477 : (e4477 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))
  have h4608 : (e4608 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h4675 : (e4675 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h4747 : (e4747 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))
  have h4838 : (e4838 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))
  have h4872 : (e4872 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))
  have h4903 : (e4903 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h7807 : (e7807 _v) := (fun hn => hc (Or.inl hn))
  have p19099 := n19099 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3271 h3937 h3946 h3976 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4653 h4675 h4747 h4787 h4813 h4838 h4872 h4903 h7807
  exact p19099
theorem n19102 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2364 : (e2364 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e2303 _v) := by
  have p19101 := n19101 _v _q 
  have p15167 := n15167 _v _q h2364
  have p5003 := n5003 _v _q h4199
  have p5005 := n5005 _v _q h3169
  have p5008 := n5008 _v _q h4787
  have p15170 := n15170 _v _q h2364
  have p19085 := n19085 _v _q h70 h91 h191 h225 h442 h488 h2364 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p17061 := n17061 _v _q h4747
  have p5006 := n5006 _v _q h4675
  have p17137 := n17137 _v _q h4059
  have p4998 := n4998 _v _q h3152
  have p19088 := n19088 _v _q h70 h91 h191 h225 h442 h488 h2364 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p17056 := n17056 _v _q h3946
  have p5007 := n5007 _v _q h225
  have p4971 := n4971 _v _q h4419
  have p4980 := n4980 _v _q h4301
  have p4979 := n4979 _v _q h4139
  have p4985 := n4985 _v _q h4156
  have p4987 := n4987 _v _q h4434
  have p5010 := n5010 _v _q h70
  have p4988 := n4988 _v _q h488
  have p4981 := n4981 _v _q h4260
  have p4983 := n4983 _v _q h4813
  have p4989 := n4989 _v _q h4838
  have p4986 := n4986 _v _q h3105
  have p4978 := n4978 _v _q h4477
  have p4984 := n4984 _v _q h4872
  have p4991 := n4991 _v _q h4608
  have p4992 := n4992 _v _q h442
  have p253 := n253 _v _q h191
  have p4994 := n4994 _v _q h3069
  have p4995 := n4995 _v _q h4369
  have p4999 := n4999 _v _q h91
  have p5001 := n5001 _v _q h4096
  have p4996 := n4996 _v _q h3937
  change (e2303 _v) ∨ (¬ (e4199 _v)) ∨ (¬ (e4903 _v)) ∨ (¬ (e3169 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e3271 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e3976 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4419 _v)) ∨ (¬ (e4301 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4477 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e3937 _v)) at p19101
  rcases p19101 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p5003))
  · exact (False.elim (hlit p15167))
  · exact (False.elim (hlit p5005))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p15170))
  · exact (False.elim (hlit p19085))
  · exact (False.elim (hlit p17061))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p17137))
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p19088))
  · exact (False.elim (hlit p17056))
  · exact (False.elim (hlit p5007))
  · exact (False.elim (hlit p4971))
  · exact (False.elim (hlit p4980))
  · exact (False.elim (hlit p4979))
  · exact (False.elim (hlit p4985))
  · exact (False.elim (hlit p4987))
  · exact (False.elim (hlit p5010))
  · exact (False.elim (hlit p4988))
  · exact (False.elim (hlit p4981))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p4989))
  · exact (False.elim (hlit p4986))
  · exact (False.elim (hlit p4978))
  · exact (False.elim (hlit p4984))
  · exact (False.elim (hlit p4991))
  · exact (False.elim (hlit p4992))
  · exact (False.elim (hlit p253))
  · exact (False.elim (hlit p4994))
  · exact (False.elim (hlit p4995))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p5001))
  · exact (False.elim (hlit p4996))
theorem n19103 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2364 : (e2364 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e7804 _v) := by
  have p14837 := n14837 _v _q 
  have p19102 := n19102 _v _q h70 h91 h191 h225 h442 h488 h2364 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (¬ (e2303 _v)) ∨ (¬ (e7798 _v)) at p14837
  rcases p14837 with hlit | hlit
  · exact (False.elim (hlit p19102))
  · exact hlit
theorem n19104 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3271 : (e3271 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) : (e2303 _v) := by
  have p19101 := n19101 _v _q 
  have p17129 := n17129 _v _q h4903
  have p5003 := n5003 _v _q h4199
  have p5005 := n5005 _v _q h3169
  have p5008 := n5008 _v _q h4787
  have p17060 := n17060 _v _q h4653
  have p17165 := n17165 _v _q h3271
  have p17061 := n17061 _v _q h4747
  have p5006 := n5006 _v _q h4675
  have p17137 := n17137 _v _q h4059
  have p4998 := n4998 _v _q h3152
  have p17076 := n17076 _v _q h3976
  have p17056 := n17056 _v _q h3946
  have p5007 := n5007 _v _q h225
  have p4971 := n4971 _v _q h4419
  have p4980 := n4980 _v _q h4301
  have p4979 := n4979 _v _q h4139
  have p4985 := n4985 _v _q h4156
  have p4987 := n4987 _v _q h4434
  have p5010 := n5010 _v _q h70
  have p4988 := n4988 _v _q h488
  have p4981 := n4981 _v _q h4260
  have p4983 := n4983 _v _q h4813
  have p4989 := n4989 _v _q h4838
  have p4986 := n4986 _v _q h3105
  have p4978 := n4978 _v _q h4477
  have p4984 := n4984 _v _q h4872
  have p4991 := n4991 _v _q h4608
  have p4992 := n4992 _v _q h442
  have p253 := n253 _v _q h191
  have p4994 := n4994 _v _q h3069
  have p4995 := n4995 _v _q h4369
  have p4999 := n4999 _v _q h91
  have p5001 := n5001 _v _q h4096
  have p4996 := n4996 _v _q h3937
  change (e2303 _v) ∨ (¬ (e4199 _v)) ∨ (¬ (e4903 _v)) ∨ (¬ (e3169 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e3271 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e3976 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4419 _v)) ∨ (¬ (e4301 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4477 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e3937 _v)) at p19101
  rcases p19101 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p5003))
  · exact (False.elim (hlit p17129))
  · exact (False.elim (hlit p5005))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p17165))
  · exact (False.elim (hlit p17061))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p17137))
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p17076))
  · exact (False.elim (hlit p17056))
  · exact (False.elim (hlit p5007))
  · exact (False.elim (hlit p4971))
  · exact (False.elim (hlit p4980))
  · exact (False.elim (hlit p4979))
  · exact (False.elim (hlit p4985))
  · exact (False.elim (hlit p4987))
  · exact (False.elim (hlit p5010))
  · exact (False.elim (hlit p4988))
  · exact (False.elim (hlit p4981))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p4989))
  · exact (False.elim (hlit p4986))
  · exact (False.elim (hlit p4978))
  · exact (False.elim (hlit p4984))
  · exact (False.elim (hlit p4991))
  · exact (False.elim (hlit p4992))
  · exact (False.elim (hlit p253))
  · exact (False.elim (hlit p4994))
  · exact (False.elim (hlit p4995))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p5001))
  · exact (False.elim (hlit p4996))
theorem n19105 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3271 : (e3271 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) : (e7804 _v) := by
  have p14837 := n14837 _v _q 
  have p19104 := n19104 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3271 h3937 h3946 h3976 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4653 h4675 h4747 h4787 h4813 h4838 h4872 h4903
  change (¬ (e2303 _v)) ∨ (¬ (e7798 _v)) at p14837
  rcases p14837 with hlit | hlit
  · exact (False.elim (hlit p19104))
  · exact hlit
theorem n19106 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2364 : (e2364 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e4285 _v) := by
  have p16274 := n16274 _v _q 
  have p19103 := n19103 _v _q h70 h91 h191 h225 h442 h488 h2364 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (e7798 _v) ∨ (e4285 _v) at p16274
  change (¬ (e7798 _v)) at p19103
  rcases p16274 with hlit | hlit
  · exact (False.elim (p19103 hlit))
  · exact hlit
theorem n19107 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3271 : (e3271 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) : (e4285 _v) := by
  have p16274 := n16274 _v _q 
  have p19105 := n19105 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3271 h3937 h3946 h3976 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4653 h4675 h4747 h4787 h4813 h4838 h4872 h4903
  change (e7798 _v) ∨ (e4285 _v) at p16274
  change (¬ (e7798 _v)) at p19105
  rcases p16274 with hlit | hlit
  · exact (False.elim (p19105 hlit))
  · exact hlit
theorem n19108 (_v : Vars) (_q : Query _v)  : (e8483 _v) := by
  by_contra hc
  change ¬ ((¬ (e2132 _v)) ∨ (e4562 _v) ∨ (¬ (e2475 _v)) ∨ (¬ (e2364 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e4285 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4419 _v)) ∨ (¬ (e4301 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4477 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e4096 _v))) at hc
  have h70 : (e70 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))))
  have h191 : (e191 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))
  have h225 : (e225 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h442 : (e442 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))
  have h488 : (e488 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))
  have h2132 : (e2132 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h2364 : (e2364 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h2475 : (e2475 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h3069 : (e3069 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))
  have h3105 : (e3105 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h3946 : (e3946 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h4059 : (e4059 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h4096 : (e4096 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))))))))))))))))))))))))))))))
  have h4139 : (e4139 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))
  have h4156 : (e4156 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))
  have h4199 : (e4199 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h4260 : (e4260 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))
  have h4285 : (e4285 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h4301 : (e4301 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))
  have h4369 : (e4369 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))))
  have h4419 : (e4419 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h4434 : (e4434 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))
  have h4477 : (e4477 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))
  have h4563 : (e4563 _v) := (fun hn => hc (Or.inr (Or.inl hn)))
  have h4608 : (e4608 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))
  have h4675 : (e4675 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h4747 : (e4747 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))
  have h4838 : (e4838 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))
  have h4872 : (e4872 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))
  have p17154 := n17154 _v _q h70 h91 h191 h225 h442 h488 h2132 h2364 h2475 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4285 h4301 h4369 h4419 h4434 h4477 h4563 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  exact p17154
theorem n19109 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2364 : (e2364 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e7742 _v) := by
  have p19108 := n19108 _v _q 
  have p19079 := n19079 _v _q h70 h91 h191 h225 h442 h488 h2364 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p19041 := n19041 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p8527 := n8527 _v _q h2364
  have p4996 := n4996 _v _q h3937
  have p19106 := n19106 _v _q h70 h91 h191 h225 h442 h488 h2364 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p4998 := n4998 _v _q h3152
  have p5003 := n5003 _v _q h4199
  have p5008 := n5008 _v _q h4787
  have p17061 := n17061 _v _q h4747
  have p5006 := n5006 _v _q h4675
  have p17137 := n17137 _v _q h4059
  have p17056 := n17056 _v _q h3946
  have p5007 := n5007 _v _q h225
  have p4971 := n4971 _v _q h4419
  have p4980 := n4980 _v _q h4301
  have p4979 := n4979 _v _q h4139
  have p4985 := n4985 _v _q h4156
  have p4987 := n4987 _v _q h4434
  have p5010 := n5010 _v _q h70
  have p4988 := n4988 _v _q h488
  have p4981 := n4981 _v _q h4260
  have p4983 := n4983 _v _q h4813
  have p4989 := n4989 _v _q h4838
  have p4986 := n4986 _v _q h3105
  have p4978 := n4978 _v _q h4477
  have p4984 := n4984 _v _q h4872
  have p4991 := n4991 _v _q h4608
  have p4992 := n4992 _v _q h442
  have p253 := n253 _v _q h191
  have p4994 := n4994 _v _q h3069
  have p4995 := n4995 _v _q h4369
  have p4999 := n4999 _v _q h91
  have p5001 := n5001 _v _q h4096
  change (¬ (e2132 _v)) ∨ (e4562 _v) ∨ (¬ (e2475 _v)) ∨ (¬ (e2364 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e4285 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4419 _v)) ∨ (¬ (e4301 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4477 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e4096 _v)) at p19108
  change (¬ (e4562 _v)) at p19041
  rcases p19108 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (p19041 hlit))
  · exact (False.elim (hlit p19079))
  · exact (False.elim (hlit p8527))
  · exact (False.elim (hlit p4996))
  · exact (False.elim (hlit p19106))
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p5003))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p17061))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p17137))
  · exact (False.elim (hlit p17056))
  · exact (False.elim (hlit p5007))
  · exact (False.elim (hlit p4971))
  · exact (False.elim (hlit p4980))
  · exact (False.elim (hlit p4979))
  · exact (False.elim (hlit p4985))
  · exact (False.elim (hlit p4987))
  · exact (False.elim (hlit p5010))
  · exact (False.elim (hlit p4988))
  · exact (False.elim (hlit p4981))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p4989))
  · exact (False.elim (hlit p4986))
  · exact (False.elim (hlit p4978))
  · exact (False.elim (hlit p4984))
  · exact (False.elim (hlit p4991))
  · exact (False.elim (hlit p4992))
  · exact (False.elim (hlit p253))
  · exact (False.elim (hlit p4994))
  · exact (False.elim (hlit p4995))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p5001))
theorem n19110 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3271 : (e3271 _v)) (h3566 : (e3566 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5100 : (e5100 _v)) (h7749 : (e7749 _v)) : (e7489 _v) := by
  have p5005 := n5005 _v _q h3169
  have p5255 := n5255 _v _q 
  have p17156 := n17156 _v _q h3566
  have p17159 := n17159 _v _q h5100
  have p17093 := n17093 _v _q 
  have p10893 := n10893 _v _q 
  have p17141 := n17141 _v _q 
  have p17131 := n17131 _v _q 
  have p19080 := n19080 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4653 h4675 h4747 h4787 h4813 h4838 h4872
  have p17069 := n17069 _v _q 
  have p5001 := n5001 _v _q h4096
  have p16269 := n16269 _v _q h7749
  have p4996 := n4996 _v _q h3937
  have p16913 := n16913 _v _q 
  have p4999 := n4999 _v _q h91
  have p19066 := n19066 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p19041 := n19041 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p16791 := n16791 _v _q 
  have p17133 := n17133 _v _q 
  have p16911 := n16911 _v _q 
  have p17136 := n17136 _v _q 
  have p19107 := n19107 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3271 h3937 h3946 h3976 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4653 h4675 h4747 h4787 h4813 h4838 h4872 h4903
  have p4998 := n4998 _v _q h3152
  have p19082 := n19082 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4653 h4675 h4747 h4787 h4813 h4838 h4872
  have p17053 := n17053 _v _q 
  have p5003 := n5003 _v _q h4199
  have p17127 := n17127 _v _q 
  have p17129 := n17129 _v _q h4903
  have p13951 := n13951 _v _q 
  have p5008 := n5008 _v _q h4787
  have p17060 := n17060 _v _q h4653
  have p17165 := n17165 _v _q h3271
  have p19073 := n19073 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p17061 := n17061 _v _q h4747
  have p17055 := n17055 _v _q 
  have p17147 := n17147 _v _q 
  have p17058 := n17058 _v _q 
  have p5006 := n5006 _v _q h4675
  have p17137 := n17137 _v _q h4059
  have p17076 := n17076 _v _q h3976
  have p17056 := n17056 _v _q h3946
  have p5007 := n5007 _v _q h225
  have p4971 := n4971 _v _q h4419
  have p17064 := n17064 _v _q 
  have p16929 := n16929 _v _q 
  have p4980 := n4980 _v _q h4301
  have p17067 := n17067 _v _q 
  have p4979 := n4979 _v _q h4139
  have p19074 := n19074 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p16994 := n16994 _v _q 
  have p19075 := n19075 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p4985 := n4985 _v _q h4156
  have p17074 := n17074 _v _q 
  have p4987 := n4987 _v _q h4434
  have p5010 := n5010 _v _q h70
  have p4988 := n4988 _v _q h488
  have p4981 := n4981 _v _q h4260
  have p4983 := n4983 _v _q h4813
  have p17072 := n17072 _v _q 
  have p17080 := n17080 _v _q 
  have p17078 := n17078 _v _q 
  have p4989 := n4989 _v _q h4838
  have p17091 := n17091 _v _q 
  have p4986 := n4986 _v _q h3105
  have p4978 := n4978 _v _q h4477
  have p17100 := n17100 _v _q 
  have p17098 := n17098 _v _q 
  have p4984 := n4984 _v _q h4872
  have p17087 := n17087 _v _q 
  have p4991 := n4991 _v _q h4608
  have p4992 := n4992 _v _q h442
  have p17083 := n17083 _v _q 
  have p16576 := n16576 _v _q 
  have p16778 := n16778 _v _q 
  have p17110 := n17110 _v _q 
  have p17115 := n17115 _v _q 
  have p253 := n253 _v _q h191
  have p17106 := n17106 _v _q 
  have p17104 := n17104 _v _q 
  have p17096 := n17096 _v _q 
  have p17124 := n17124 _v _q 
  have p17102 := n17102 _v _q 
  have p17108 := n17108 _v _q 
  have p4994 := n4994 _v _q h3069
  have p17117 := n17117 _v _q 
  have p17120 := n17120 _v _q 
  have p17113 := n17113 _v _q 
  have p17122 := n17122 _v _q 
  have p4995 := n4995 _v _q h4369
  have p16175 := n16175 _v _q 
  exact FloorCertificate.node_19110 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e61 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2834 _v) (e2849 _v) (e2863 _v) (e2877 _v) (e2883 _v) (e2898 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e3164 _v) (e4215 _v) (e4541 _v) (e4808 _v) p5005 p5255 p17156 p17159 p17093 p10893 p17141 p17131 p19080 p17069 p5001 p16269 p4996 p16913 p4999 p19066 p19041 p16791 p17133 p16911 p17136 p19107 p4998 p19082 p17053 p5003 p17127 p17129 p13951 p5008 p17060 p17165 p19073 p17061 p17055 p17147 p17058 p5006 p17137 p17076 p17056 p5007 p4971 p17064 p16929 p4980 p17067 p4979 p19074 p16994 p19075 p4985 p17074 p4987 p5010 p4988 p4981 p4983 p17072 p17080 p17078 p4989 p17091 p4986 p4978 p17100 p17098 p4984 p17087 p4991 p4992 p17083 p16576 p16778 p17110 p17115 p253 p17106 p17104 p17096 p17124 p17102 p17108 p4994 p17117 p17120 p17113 p17122 p4995 p16175
theorem n19112 (_v : Vars) (_q : Query _v)  : (e19111 _v) := by
  by_contra hc
  change ¬ ((¬ (e5100 _v)) ∨ (¬ (e3169 _v)) ∨ (¬ (e3566 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e7749 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e4903 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e3271 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e3976 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4419 _v)) ∨ (¬ (e4301 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4477 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4369 _v))) at hc
  have h70 : (e70 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h191 : (e191 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))))))
  have h225 : (e225 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))
  have h442 : (e442 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))))))
  have h488 : (e488 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))
  have h3069 : (e3069 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))))))))
  have h3105 : (e3105 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h3169 : (e3169 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h3271 : (e3271 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h3566 : (e3566 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h3946 : (e3946 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))
  have h3976 : (e3976 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))
  have h4059 : (e4059 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))
  have h4096 : (e4096 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4139 : (e4139 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))
  have h4156 : (e4156 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))
  have h4199 : (e4199 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h4260 : (e4260 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))
  have h4301 : (e4301 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))
  have h4369 : (e4369 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn)))))))))))))))))))))))))))))))))))))
  have h4419 : (e4419 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))
  have h4434 : (e4434 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))
  have h4477 : (e4477 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))
  have h4608 : (e4608 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h4675 : (e4675 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h4747 : (e4747 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))
  have h4838 : (e4838 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))
  have h4872 : (e4872 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))))
  have h4903 : (e4903 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h5100 : (e5100 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h7749 : (e7749 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have p19110 := n19110 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3271 h3566 h3937 h3946 h3976 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4653 h4675 h4747 h4787 h4813 h4838 h4872 h4903 h5100 h7749
  exact p19110
theorem n19113 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2364 : (e2364 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e7754 _v) := by
  have p14942 := n14942 _v _q 
  have p19109 := n19109 _v _q h70 h91 h191 h225 h442 h488 h2364 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (e2132 _v) ∨ (¬ (e7753 _v)) at p14942
  change (¬ (e2132 _v)) at p19109
  rcases p14942 with hlit | hlit
  · exact (False.elim (p19109 hlit))
  · exact hlit
theorem n19114 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2364 : (e2364 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e7749 _v) := by
  have p14941 := n14941 _v _q 
  have p19113 := n19113 _v _q h70 h91 h191 h225 h442 h488 h2364 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (e7753 _v) ∨ (e7749 _v) at p14941
  change (¬ (e7753 _v)) at p19113
  rcases p14941 with hlit | hlit
  · exact (False.elim (p19113 hlit))
  · exact hlit
theorem n19115 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2364 : (e2364 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h6656 : (e6656 _v)) : (e5103 _v) := by
  have p17093 := n17093 _v _q 
  have p10893 := n10893 _v _q 
  have p17141 := n17141 _v _q 
  have p15360 := n15360 _v _q h6656
  have p16181 := n16181 _v _q 
  have p17131 := n17131 _v _q 
  have p19079 := n19079 _v _q h70 h91 h191 h225 h442 h488 h2364 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p17069 := n17069 _v _q 
  have p5001 := n5001 _v _q h4096
  have p19114 := n19114 _v _q h70 h91 h191 h225 h442 h488 h2364 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p4996 := n4996 _v _q h3937
  have p16913 := n16913 _v _q 
  have p4999 := n4999 _v _q h91
  have p19066 := n19066 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p19041 := n19041 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p16791 := n16791 _v _q 
  have p17133 := n17133 _v _q 
  have p16911 := n16911 _v _q 
  have p17136 := n17136 _v _q 
  have p19106 := n19106 _v _q h70 h91 h191 h225 h442 h488 h2364 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p4998 := n4998 _v _q h3152
  have p19090 := n19090 _v _q h70 h91 h191 h225 h442 h488 h2364 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p17053 := n17053 _v _q 
  have p5003 := n5003 _v _q h4199
  have p17127 := n17127 _v _q 
  have p15167 := n15167 _v _q h2364
  have p13951 := n13951 _v _q 
  have p5008 := n5008 _v _q h4787
  have p15170 := n15170 _v _q h2364
  have p19085 := n19085 _v _q h70 h91 h191 h225 h442 h488 h2364 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p19073 := n19073 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p17061 := n17061 _v _q h4747
  have p17055 := n17055 _v _q 
  have p17147 := n17147 _v _q 
  have p17058 := n17058 _v _q 
  have p5006 := n5006 _v _q h4675
  have p17137 := n17137 _v _q h4059
  have p19088 := n19088 _v _q h70 h91 h191 h225 h442 h488 h2364 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p17056 := n17056 _v _q h3946
  have p5007 := n5007 _v _q h225
  have p4971 := n4971 _v _q h4419
  have p17064 := n17064 _v _q 
  have p16929 := n16929 _v _q 
  have p4980 := n4980 _v _q h4301
  have p17067 := n17067 _v _q 
  have p4979 := n4979 _v _q h4139
  have p19074 := n19074 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p16994 := n16994 _v _q 
  have p19075 := n19075 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p4985 := n4985 _v _q h4156
  have p17074 := n17074 _v _q 
  have p4987 := n4987 _v _q h4434
  have p5010 := n5010 _v _q h70
  have p4988 := n4988 _v _q h488
  have p4981 := n4981 _v _q h4260
  have p4983 := n4983 _v _q h4813
  have p17072 := n17072 _v _q 
  have p17080 := n17080 _v _q 
  have p17078 := n17078 _v _q 
  have p4989 := n4989 _v _q h4838
  have p17091 := n17091 _v _q 
  have p4986 := n4986 _v _q h3105
  have p4978 := n4978 _v _q h4477
  have p17100 := n17100 _v _q 
  have p17098 := n17098 _v _q 
  have p4984 := n4984 _v _q h4872
  have p17087 := n17087 _v _q 
  have p4991 := n4991 _v _q h4608
  have p4992 := n4992 _v _q h442
  have p17083 := n17083 _v _q 
  have p16576 := n16576 _v _q 
  have p16778 := n16778 _v _q 
  have p17110 := n17110 _v _q 
  have p17115 := n17115 _v _q 
  have p253 := n253 _v _q h191
  have p17106 := n17106 _v _q 
  have p17104 := n17104 _v _q 
  have p17096 := n17096 _v _q 
  have p17124 := n17124 _v _q 
  have p17102 := n17102 _v _q 
  have p17108 := n17108 _v _q 
  have p4994 := n4994 _v _q h3069
  have p17117 := n17117 _v _q 
  have p17120 := n17120 _v _q 
  have p17113 := n17113 _v _q 
  have p17122 := n17122 _v _q 
  have p4995 := n4995 _v _q h4369
  have p16175 := n16175 _v _q 
  have p5005 := n5005 _v _q h3169
  have p11499 := n11499 _v _q h6656
  have p5255 := n5255 _v _q 
  exact FloorCertificate.node_19115 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e61 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2834 _v) (e2849 _v) (e2863 _v) (e2877 _v) (e2883 _v) (e2898 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e3164 _v) (e3574 _v) (e4215 _v) (e4541 _v) (e4808 _v) p17093 p10893 p17141 p15360 p16181 p17131 p19079 p17069 p5001 p19114 p4996 p16913 p4999 p19066 p19041 p16791 p17133 p16911 p17136 p19106 p4998 p19090 p17053 p5003 p17127 p15167 p13951 p5008 p15170 p19085 p19073 p17061 p17055 p17147 p17058 p5006 p17137 p19088 p17056 p5007 p4971 p17064 p16929 p4980 p17067 p4979 p19074 p16994 p19075 p4985 p17074 p4987 p5010 p4988 p4981 p4983 p17072 p17080 p17078 p4989 p17091 p4986 p4978 p17100 p17098 p4984 p17087 p4991 p4992 p17083 p16576 p16778 p17110 p17115 p253 p17106 p17104 p17096 p17124 p17102 p17108 p4994 p17117 p17120 p17113 p17122 p4995 p16175 p5005 p11499 p5255
theorem n19116 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2364 : (e2364 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h6656 : (e6656 _v)) : (e7489 _v) := by
  have p15319 := n15319 _v _q 
  have p15558 := n15558 _v _q h2364 h6656
  have p19115 := n19115 _v _q h70 h91 h191 h225 h442 h488 h2364 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872 h6656
  change (e5104 _v) ∨ (e5100 _v) at p15319
  change (¬ (e5104 _v)) at p15558
  change (¬ (e5100 _v)) at p19115
  rcases p15319 with hlit | hlit
  · exact (False.elim (p15558 hlit))
  · exact (False.elim (p19115 hlit))
theorem n19118 (_v : Vars) (_q : Query _v)  : (e19117 _v) := by
  by_contra hc
  change ¬ ((e2536 _v) ∨ (¬ (e4096 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4419 _v)) ∨ (¬ (e4301 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4477 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e3169 _v)) ∨ (¬ (e2364 _v))) at hc
  have h70 : (e70 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h191 : (e191 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))
  have h225 : (e225 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h442 : (e442 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))
  have h488 : (e488 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))
  have h2364 : (e2364 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))))))))))))))))))))))))))))
  have h3069 : (e3069 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))
  have h3105 : (e3105 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h3169 : (e3169 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h3946 : (e3946 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h4059 : (e4059 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h4096 : (e4096 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h4139 : (e4139 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h4156 : (e4156 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))
  have h4199 : (e4199 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h4260 : (e4260 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))
  have h4301 : (e4301 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h4369 : (e4369 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))
  have h4419 : (e4419 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h4434 : (e4434 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))
  have h4477 : (e4477 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))
  have h4608 : (e4608 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))
  have h4675 : (e4675 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h4747 : (e4747 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))
  have h4838 : (e4838 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))
  have h4872 : (e4872 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))
  have h6656 : (e6656 _v) := (fun hn => hc (Or.inl hn))
  have p19116 := n19116 _v _q h70 h91 h191 h225 h442 h488 h2364 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872 h6656
  exact p19116
theorem n19119 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2364 : (e2364 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e2536 _v) := by
  have p19118 := n19118 _v _q 
  have p8527 := n8527 _v _q h2364
  have p4996 := n4996 _v _q h3937
  have p4999 := n4999 _v _q h91
  have p4998 := n4998 _v _q h3152
  have p5003 := n5003 _v _q h4199
  have p5008 := n5008 _v _q h4787
  have p17061 := n17061 _v _q h4747
  have p5006 := n5006 _v _q h4675
  have p17137 := n17137 _v _q h4059
  have p17056 := n17056 _v _q h3946
  have p5007 := n5007 _v _q h225
  have p4971 := n4971 _v _q h4419
  have p4980 := n4980 _v _q h4301
  have p4979 := n4979 _v _q h4139
  have p4985 := n4985 _v _q h4156
  have p4987 := n4987 _v _q h4434
  have p5010 := n5010 _v _q h70
  have p4988 := n4988 _v _q h488
  have p4981 := n4981 _v _q h4260
  have p4983 := n4983 _v _q h4813
  have p4989 := n4989 _v _q h4838
  have p4986 := n4986 _v _q h3105
  have p4978 := n4978 _v _q h4477
  have p4984 := n4984 _v _q h4872
  have p4991 := n4991 _v _q h4608
  have p4992 := n4992 _v _q h442
  have p253 := n253 _v _q h191
  have p4994 := n4994 _v _q h3069
  have p4995 := n4995 _v _q h4369
  have p5005 := n5005 _v _q h3169
  have p5001 := n5001 _v _q h4096
  change (e2536 _v) ∨ (¬ (e4096 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4419 _v)) ∨ (¬ (e4301 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4477 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e3169 _v)) ∨ (¬ (e2364 _v)) at p19118
  rcases p19118 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p5001))
  · exact (False.elim (hlit p4996))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p5003))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p17061))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p17137))
  · exact (False.elim (hlit p17056))
  · exact (False.elim (hlit p5007))
  · exact (False.elim (hlit p4971))
  · exact (False.elim (hlit p4980))
  · exact (False.elim (hlit p4979))
  · exact (False.elim (hlit p4985))
  · exact (False.elim (hlit p4987))
  · exact (False.elim (hlit p5010))
  · exact (False.elim (hlit p4988))
  · exact (False.elim (hlit p4981))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p4989))
  · exact (False.elim (hlit p4986))
  · exact (False.elim (hlit p4978))
  · exact (False.elim (hlit p4984))
  · exact (False.elim (hlit p4991))
  · exact (False.elim (hlit p4992))
  · exact (False.elim (hlit p253))
  · exact (False.elim (hlit p4994))
  · exact (False.elim (hlit p4995))
  · exact (False.elim (hlit p5005))
  · exact (False.elim (hlit p8527))
theorem n19120 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2364 : (e2364 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e3573 _v) := by
  have p14426 := n14426 _v _q 
  have p19119 := n19119 _v _q h70 h91 h191 h225 h442 h488 h2364 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (¬ (e2536 _v)) ∨ (¬ (e3572 _v)) at p14426
  rcases p14426 with hlit | hlit
  · exact (False.elim (hlit p19119))
  · exact hlit
theorem n19121 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2364 : (e2364 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e3566 _v) := by
  have p7179 := n7179 _v _q 
  have p19120 := n19120 _v _q h70 h91 h191 h225 h442 h488 h2364 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (e3572 _v) ∨ (e3566 _v) at p7179
  change (¬ (e3572 _v)) at p19120
  rcases p7179 with hlit | hlit
  · exact (False.elim (p19120 hlit))
  · exact hlit
theorem n19122 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2364 : (e2364 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e5103 _v) := by
  have p19112 := n19112 _v _q 
  have p19121 := n19121 _v _q h70 h91 h191 h225 h442 h488 h2364 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p5005 := n5005 _v _q h3169
  have p5001 := n5001 _v _q h4096
  have p19114 := n19114 _v _q h70 h91 h191 h225 h442 h488 h2364 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p4996 := n4996 _v _q h3937
  have p4999 := n4999 _v _q h91
  have p4998 := n4998 _v _q h3152
  have p5003 := n5003 _v _q h4199
  have p15167 := n15167 _v _q h2364
  have p5008 := n5008 _v _q h4787
  have p15170 := n15170 _v _q h2364
  have p19085 := n19085 _v _q h70 h91 h191 h225 h442 h488 h2364 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p17061 := n17061 _v _q h4747
  have p5006 := n5006 _v _q h4675
  have p17137 := n17137 _v _q h4059
  have p19088 := n19088 _v _q h70 h91 h191 h225 h442 h488 h2364 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p17056 := n17056 _v _q h3946
  have p5007 := n5007 _v _q h225
  have p4971 := n4971 _v _q h4419
  have p4980 := n4980 _v _q h4301
  have p4979 := n4979 _v _q h4139
  have p4985 := n4985 _v _q h4156
  have p4987 := n4987 _v _q h4434
  have p5010 := n5010 _v _q h70
  have p4988 := n4988 _v _q h488
  have p4981 := n4981 _v _q h4260
  have p4983 := n4983 _v _q h4813
  have p4989 := n4989 _v _q h4838
  have p4986 := n4986 _v _q h3105
  have p4978 := n4978 _v _q h4477
  have p4984 := n4984 _v _q h4872
  have p4991 := n4991 _v _q h4608
  have p4992 := n4992 _v _q h442
  have p253 := n253 _v _q h191
  have p4994 := n4994 _v _q h3069
  have p4995 := n4995 _v _q h4369
  change (¬ (e5100 _v)) ∨ (¬ (e3169 _v)) ∨ (¬ (e3566 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e7749 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e4903 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e3271 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e3976 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4419 _v)) ∨ (¬ (e4301 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4477 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4369 _v)) at p19112
  rcases p19112 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p5005))
  · exact (False.elim (hlit p19121))
  · exact (False.elim (hlit p5001))
  · exact (False.elim (hlit p19114))
  · exact (False.elim (hlit p4996))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p5003))
  · exact (False.elim (hlit p15167))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p15170))
  · exact (False.elim (hlit p19085))
  · exact (False.elim (hlit p17061))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p17137))
  · exact (False.elim (hlit p19088))
  · exact (False.elim (hlit p17056))
  · exact (False.elim (hlit p5007))
  · exact (False.elim (hlit p4971))
  · exact (False.elim (hlit p4980))
  · exact (False.elim (hlit p4979))
  · exact (False.elim (hlit p4985))
  · exact (False.elim (hlit p4987))
  · exact (False.elim (hlit p5010))
  · exact (False.elim (hlit p4988))
  · exact (False.elim (hlit p4981))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p4989))
  · exact (False.elim (hlit p4986))
  · exact (False.elim (hlit p4978))
  · exact (False.elim (hlit p4984))
  · exact (False.elim (hlit p4991))
  · exact (False.elim (hlit p4992))
  · exact (False.elim (hlit p253))
  · exact (False.elim (hlit p4994))
  · exact (False.elim (hlit p4995))
theorem n19123 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2364 : (e2364 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e5104 _v) := by
  have p15319 := n15319 _v _q 
  have p19122 := n19122 _v _q h70 h91 h191 h225 h442 h488 h2364 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (e5104 _v) ∨ (e5100 _v) at p15319
  change (¬ (e5100 _v)) at p19122
  rcases p15319 with hlit | hlit
  · exact hlit
  · exact (False.elim (p19122 hlit))
theorem n19124 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2364 : (e2364 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e13 _v) := by
  have p15204 := n15204 _v _q 
  have p19123 := n19123 _v _q h70 h91 h191 h225 h442 h488 h2364 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (e13 _v) ∨ (¬ (e5104 _v)) at p15204
  rcases p15204 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p19123))
theorem n19125 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2364 : (e2364 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e5090 _v) := by
  have p14728 := n14728 _v _q 
  have p19124 := n19124 _v _q h70 h91 h191 h225 h442 h488 h2364 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (¬ (e13 _v)) ∨ (¬ (e5089 _v)) at p14728
  rcases p14728 with hlit | hlit
  · exact (False.elim (hlit p19124))
  · exact hlit
theorem n19126 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2364 : (e2364 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e30 _v) := by
  have p16290 := n16290 _v _q 
  have p19125 := n19125 _v _q h70 h91 h191 h225 h442 h488 h2364 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (e5089 _v) ∨ (e30 _v) at p16290
  change (¬ (e5089 _v)) at p19125
  rcases p16290 with hlit | hlit
  · exact (False.elim (p19125 hlit))
  · exact hlit
theorem n19127 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2364 : (e2364 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e7489 _v) := by
  have p19109 := n19109 _v _q h70 h91 h191 h225 h442 h488 h2364 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p19126 := n19126 _v _q h70 h91 h191 h225 h442 h488 h2364 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p16175 := n16175 _v _q 
  have p10893 := n10893 _v _q 
  have p5005 := n5005 _v _q h3169
  have p4995 := n4995 _v _q h4369
  have p19121 := n19121 _v _q h70 h91 h191 h225 h442 h488 h2364 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p17093 := n17093 _v _q 
  have p17141 := n17141 _v _q 
  have p17131 := n17131 _v _q 
  have p19079 := n19079 _v _q h70 h91 h191 h225 h442 h488 h2364 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p17069 := n17069 _v _q 
  have p5001 := n5001 _v _q h4096
  have p19114 := n19114 _v _q h70 h91 h191 h225 h442 h488 h2364 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p4996 := n4996 _v _q h3937
  have p16913 := n16913 _v _q 
  have p4999 := n4999 _v _q h91
  have p19066 := n19066 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p19041 := n19041 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p16791 := n16791 _v _q 
  have p17133 := n17133 _v _q 
  have p16911 := n16911 _v _q 
  have p17136 := n17136 _v _q 
  have p19106 := n19106 _v _q h70 h91 h191 h225 h442 h488 h2364 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p4998 := n4998 _v _q h3152
  have p19090 := n19090 _v _q h70 h91 h191 h225 h442 h488 h2364 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p17053 := n17053 _v _q 
  have p5003 := n5003 _v _q h4199
  have p17127 := n17127 _v _q 
  have p15167 := n15167 _v _q h2364
  have p13951 := n13951 _v _q 
  have p5008 := n5008 _v _q h4787
  have p15170 := n15170 _v _q h2364
  have p19085 := n19085 _v _q h70 h91 h191 h225 h442 h488 h2364 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p19073 := n19073 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p17061 := n17061 _v _q h4747
  have p17055 := n17055 _v _q 
  have p17147 := n17147 _v _q 
  have p17058 := n17058 _v _q 
  have p5006 := n5006 _v _q h4675
  have p17137 := n17137 _v _q h4059
  have p19088 := n19088 _v _q h70 h91 h191 h225 h442 h488 h2364 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p17056 := n17056 _v _q h3946
  have p5007 := n5007 _v _q h225
  have p4971 := n4971 _v _q h4419
  have p17064 := n17064 _v _q 
  have p16929 := n16929 _v _q 
  have p4980 := n4980 _v _q h4301
  have p17067 := n17067 _v _q 
  have p4979 := n4979 _v _q h4139
  have p19074 := n19074 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p16994 := n16994 _v _q 
  have p19075 := n19075 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p4985 := n4985 _v _q h4156
  have p17074 := n17074 _v _q 
  have p4987 := n4987 _v _q h4434
  have p5010 := n5010 _v _q h70
  have p4988 := n4988 _v _q h488
  have p4981 := n4981 _v _q h4260
  have p4983 := n4983 _v _q h4813
  have p17072 := n17072 _v _q 
  have p17080 := n17080 _v _q 
  have p17078 := n17078 _v _q 
  have p4989 := n4989 _v _q h4838
  have p17091 := n17091 _v _q 
  have p4986 := n4986 _v _q h3105
  have p4978 := n4978 _v _q h4477
  have p17100 := n17100 _v _q 
  have p17098 := n17098 _v _q 
  have p4984 := n4984 _v _q h4872
  have p17087 := n17087 _v _q 
  have p4991 := n4991 _v _q h4608
  have p4992 := n4992 _v _q h442
  have p17083 := n17083 _v _q 
  have p16576 := n16576 _v _q 
  have p16778 := n16778 _v _q 
  have p17110 := n17110 _v _q 
  have p17115 := n17115 _v _q 
  have p253 := n253 _v _q h191
  have p17106 := n17106 _v _q 
  have p17104 := n17104 _v _q 
  have p17096 := n17096 _v _q 
  have p17124 := n17124 _v _q 
  have p17102 := n17102 _v _q 
  have p17108 := n17108 _v _q 
  have p4994 := n4994 _v _q h3069
  have p17117 := n17117 _v _q 
  have p17120 := n17120 _v _q 
  have p17113 := n17113 _v _q 
  have p17122 := n17122 _v _q 
  exact FloorCertificate.node_19127 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e61 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2834 _v) (e2849 _v) (e2863 _v) (e2877 _v) (e2883 _v) (e2898 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e3164 _v) (e4215 _v) (e4541 _v) (e4808 _v) p19109 p19126 p16175 p10893 p5005 p4995 p19121 p17093 p17141 p17131 p19079 p17069 p5001 p19114 p4996 p16913 p4999 p19066 p19041 p16791 p17133 p16911 p17136 p19106 p4998 p19090 p17053 p5003 p17127 p15167 p13951 p5008 p15170 p19085 p19073 p17061 p17055 p17147 p17058 p5006 p17137 p19088 p17056 p5007 p4971 p17064 p16929 p4980 p17067 p4979 p19074 p16994 p19075 p4985 p17074 p4987 p5010 p4988 p4981 p4983 p17072 p17080 p17078 p4989 p17091 p4986 p4978 p17100 p17098 p4984 p17087 p4991 p4992 p17083 p16576 p16778 p17110 p17115 p253 p17106 p17104 p17096 p17124 p17102 p17108 p4994 p17117 p17120 p17113 p17122
theorem n19129 (_v : Vars) (_q : Query _v)  : (e19128 _v) := by
  by_contra hc
  change ¬ ((¬ (e2364 _v)) ∨ (¬ (e3169 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4419 _v)) ∨ (¬ (e4301 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4477 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e3069 _v))) at hc
  have h70 : (e70 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h191 : (e191 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))
  have h225 : (e225 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h442 : (e442 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))
  have h488 : (e488 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))
  have h2364 : (e2364 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h3069 : (e3069 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn)))))))))))))))))))))))))))))))
  have h3105 : (e3105 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h3169 : (e3169 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h3946 : (e3946 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h4059 : (e4059 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h4096 : (e4096 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4139 : (e4139 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))
  have h4156 : (e4156 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))
  have h4199 : (e4199 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h4260 : (e4260 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))
  have h4301 : (e4301 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))
  have h4369 : (e4369 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4419 : (e4419 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h4434 : (e4434 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))
  have h4477 : (e4477 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))
  have h4608 : (e4608 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))
  have h4675 : (e4675 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h4747 : (e4747 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))
  have h4838 : (e4838 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))
  have h4872 : (e4872 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))
  have p19127 := n19127 _v _q h70 h91 h191 h225 h442 h488 h2364 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  exact p19127
theorem n19130 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e6583 _v) := by
  have p19129 := n19129 _v _q 
  have p5005 := n5005 _v _q h3169
  have p4995 := n4995 _v _q h4369
  have p5001 := n5001 _v _q h4096
  have p4996 := n4996 _v _q h3937
  have p4999 := n4999 _v _q h91
  have p4998 := n4998 _v _q h3152
  have p5003 := n5003 _v _q h4199
  have p5008 := n5008 _v _q h4787
  have p17061 := n17061 _v _q h4747
  have p5006 := n5006 _v _q h4675
  have p17137 := n17137 _v _q h4059
  have p17056 := n17056 _v _q h3946
  have p5007 := n5007 _v _q h225
  have p4971 := n4971 _v _q h4419
  have p4980 := n4980 _v _q h4301
  have p4979 := n4979 _v _q h4139
  have p4985 := n4985 _v _q h4156
  have p4987 := n4987 _v _q h4434
  have p5010 := n5010 _v _q h70
  have p4988 := n4988 _v _q h488
  have p4981 := n4981 _v _q h4260
  have p4983 := n4983 _v _q h4813
  have p4989 := n4989 _v _q h4838
  have p4986 := n4986 _v _q h3105
  have p4978 := n4978 _v _q h4477
  have p4984 := n4984 _v _q h4872
  have p4991 := n4991 _v _q h4608
  have p4992 := n4992 _v _q h442
  have p253 := n253 _v _q h191
  have p4994 := n4994 _v _q h3069
  change (¬ (e2364 _v)) ∨ (¬ (e3169 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4419 _v)) ∨ (¬ (e4301 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4477 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e3069 _v)) at p19129
  rcases p19129 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p5005))
  · exact (False.elim (hlit p4995))
  · exact (False.elim (hlit p5001))
  · exact (False.elim (hlit p4996))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p5003))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p17061))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p17137))
  · exact (False.elim (hlit p17056))
  · exact (False.elim (hlit p5007))
  · exact (False.elim (hlit p4971))
  · exact (False.elim (hlit p4980))
  · exact (False.elim (hlit p4979))
  · exact (False.elim (hlit p4985))
  · exact (False.elim (hlit p4987))
  · exact (False.elim (hlit p5010))
  · exact (False.elim (hlit p4988))
  · exact (False.elim (hlit p4981))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p4989))
  · exact (False.elim (hlit p4986))
  · exact (False.elim (hlit p4978))
  · exact (False.elim (hlit p4984))
  · exact (False.elim (hlit p4991))
  · exact (False.elim (hlit p4992))
  · exact (False.elim (hlit p253))
  · exact (False.elim (hlit p4994))
theorem n19131 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e6583 _v) := by
  have p19129 := n19129 _v _q 
  have p4980 := n4980 _v _q h4301
  have p4995 := n4995 _v _q h4369
  have p5001 := n5001 _v _q h4096
  have p4996 := n4996 _v _q h3937
  have p4999 := n4999 _v _q h91
  have p4998 := n4998 _v _q h3152
  have p5003 := n5003 _v _q h4199
  have p5008 := n5008 _v _q h4787
  have p17061 := n17061 _v _q h4747
  have p5006 := n5006 _v _q h4675
  have p17137 := n17137 _v _q h4059
  have p17056 := n17056 _v _q h3946
  have p5007 := n5007 _v _q h225
  have p4971 := n4971 _v _q h4419
  have p5005 := n5005 _v _q h3169
  have p4979 := n4979 _v _q h4139
  have p4985 := n4985 _v _q h4156
  have p4987 := n4987 _v _q h4434
  have p5010 := n5010 _v _q h70
  have p4988 := n4988 _v _q h488
  have p4981 := n4981 _v _q h4260
  have p4983 := n4983 _v _q h4813
  have p4989 := n4989 _v _q h4838
  have p4986 := n4986 _v _q h3105
  have p4978 := n4978 _v _q h4477
  have p4984 := n4984 _v _q h4872
  have p4991 := n4991 _v _q h4608
  have p4992 := n4992 _v _q h442
  have p253 := n253 _v _q h191
  have p4994 := n4994 _v _q h3069
  change (¬ (e2364 _v)) ∨ (¬ (e3169 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4419 _v)) ∨ (¬ (e4301 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4477 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e3069 _v)) at p19129
  rcases p19129 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p5005))
  · exact (False.elim (hlit p4995))
  · exact (False.elim (hlit p5001))
  · exact (False.elim (hlit p4996))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p5003))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p17061))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p17137))
  · exact (False.elim (hlit p17056))
  · exact (False.elim (hlit p5007))
  · exact (False.elim (hlit p4971))
  · exact (False.elim (hlit p4980))
  · exact (False.elim (hlit p4979))
  · exact (False.elim (hlit p4985))
  · exact (False.elim (hlit p4987))
  · exact (False.elim (hlit p5010))
  · exact (False.elim (hlit p4988))
  · exact (False.elim (hlit p4981))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p4989))
  · exact (False.elim (hlit p4986))
  · exact (False.elim (hlit p4978))
  · exact (False.elim (hlit p4984))
  · exact (False.elim (hlit p4991))
  · exact (False.elim (hlit p4992))
  · exact (False.elim (hlit p253))
  · exact (False.elim (hlit p4994))
theorem n19132 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e2303 _v) := by
  have p16791 := n16791 _v _q 
  have p19041 := n19041 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p19066 := n19066 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p19131 := n19131 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  exact FloorCertificate.node_19132 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e110 _v) (e2834 _v) (e2918 _v) p16791 p19041 p19066 p19131
theorem n19133 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e7804 _v) := by
  have p14837 := n14837 _v _q 
  have p19132 := n19132 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (¬ (e2303 _v)) ∨ (¬ (e7798 _v)) at p14837
  rcases p14837 with hlit | hlit
  · exact (False.elim (hlit p19132))
  · exact hlit
theorem n19134 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e8157 _v) := by
  have p14632 := n14632 _v _q 
  have p19131 := n19131 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (e2364 _v) ∨ (¬ (e8149 _v)) at p14632
  change (¬ (e2364 _v)) at p19131
  rcases p14632 with hlit | hlit
  · exact (False.elim (p19131 hlit))
  · exact hlit
theorem n19135 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e4648 _v) := by
  have p15027 := n15027 _v _q 
  have p19134 := n19134 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (e8149 _v) ∨ (e4648 _v) at p15027
  change (¬ (e8149 _v)) at p19134
  rcases p15027 with hlit | hlit
  · exact (False.elim (p19134 hlit))
  · exact hlit
theorem n19136 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e8157 _v) := by
  have p14632 := n14632 _v _q 
  have p19130 := n19130 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (e2364 _v) ∨ (¬ (e8149 _v)) at p14632
  change (¬ (e2364 _v)) at p19130
  rcases p14632 with hlit | hlit
  · exact (False.elim (p19130 hlit))
  · exact hlit
theorem n19137 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e4648 _v) := by
  have p15027 := n15027 _v _q 
  have p19136 := n19136 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (e8149 _v) ∨ (e4648 _v) at p15027
  change (¬ (e8149 _v)) at p19136
  rcases p15027 with hlit | hlit
  · exact (False.elim (p19136 hlit))
  · exact hlit
theorem n19138 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e4285 _v) := by
  have p16274 := n16274 _v _q 
  have p19133 := n19133 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (e7798 _v) ∨ (e4285 _v) at p16274
  change (¬ (e7798 _v)) at p19133
  rcases p16274 with hlit | hlit
  · exact (False.elim (p19133 hlit))
  · exact hlit
theorem n19139 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h8038 : (e8038 _v)) : (e3566 _v) := by
  have p7179 := n7179 _v _q 
  have p18605 := n18605 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h4096 h4156 h4199 h4260 h4369 h4434 h4608 h4675 h4787 h4813 h4838 h4872 h8038
  change (e3572 _v) ∨ (e3566 _v) at p7179
  change (¬ (e3572 _v)) at p18605
  rcases p7179 with hlit | hlit
  · exact (False.elim (p18605 hlit))
  · exact hlit
theorem n19140 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h8038 : (e8038 _v)) : (e7489 _v) := by
  have p18599 := n18599 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h4096 h4156 h4199 h4260 h4369 h4434 h4608 h4675 h4787 h4813 h4838 h4872 h8038
  have p19131 := n19131 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p19139 := n19139 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h4096 h4156 h4199 h4260 h4369 h4434 h4608 h4675 h4787 h4813 h4838 h4872 h8038
  have p19045 := n19045 _v _q h8038
  have p17093 := n17093 _v _q 
  have p15209 := n15209 _v _q h8038
  have p17141 := n17141 _v _q 
  have p17131 := n17131 _v _q 
  have p5005 := n5005 _v _q h3169
  have p17069 := n17069 _v _q 
  have p5001 := n5001 _v _q h4096
  have p15555 := n15555 _v _q h8038
  have p4996 := n4996 _v _q h3937
  have p16913 := n16913 _v _q 
  have p4999 := n4999 _v _q h91
  have p19066 := n19066 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p19041 := n19041 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p16791 := n16791 _v _q 
  have p17133 := n17133 _v _q 
  have p16911 := n16911 _v _q 
  have p17136 := n17136 _v _q 
  have p19138 := n19138 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p4998 := n4998 _v _q h3152
  have p17221 := n17221 _v _q 
  have p17053 := n17053 _v _q 
  have p5003 := n5003 _v _q h4199
  have p17127 := n17127 _v _q 
  have p17968 := n17968 _v _q h91 h225 h488 h3069 h3105 h3152 h3937 h4096 h4369 h4434 h4608 h4787 h4813 h4838 h4872 h8038
  have p13951 := n13951 _v _q 
  have p5008 := n5008 _v _q h4787
  have p5255 := n5255 _v _q 
  have p18597 := n18597 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h4096 h4156 h4199 h4260 h4369 h4434 h4608 h4675 h4787 h4813 h4838 h4872 h8038
  have p19073 := n19073 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p17061 := n17061 _v _q h4747
  have p17055 := n17055 _v _q 
  have p17147 := n17147 _v _q 
  have p17058 := n17058 _v _q 
  have p5006 := n5006 _v _q h4675
  have p17137 := n17137 _v _q h4059
  have p17966 := n17966 _v _q h91 h225 h488 h3069 h3105 h3152 h3937 h4096 h4369 h4434 h4608 h4787 h4813 h4838 h4872 h8038
  have p17056 := n17056 _v _q h3946
  have p5007 := n5007 _v _q h225
  have p4971 := n4971 _v _q h4419
  have p17064 := n17064 _v _q 
  have p16929 := n16929 _v _q 
  have p4980 := n4980 _v _q h4301
  have p17067 := n17067 _v _q 
  have p4979 := n4979 _v _q h4139
  have p19074 := n19074 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p16994 := n16994 _v _q 
  have p19075 := n19075 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p4985 := n4985 _v _q h4156
  have p17074 := n17074 _v _q 
  have p4987 := n4987 _v _q h4434
  have p5010 := n5010 _v _q h70
  have p4988 := n4988 _v _q h488
  have p4981 := n4981 _v _q h4260
  have p4983 := n4983 _v _q h4813
  have p17072 := n17072 _v _q 
  have p17080 := n17080 _v _q 
  have p17078 := n17078 _v _q 
  have p4989 := n4989 _v _q h4838
  have p17091 := n17091 _v _q 
  have p4986 := n4986 _v _q h3105
  have p4978 := n4978 _v _q h4477
  have p17100 := n17100 _v _q 
  have p17098 := n17098 _v _q 
  have p4984 := n4984 _v _q h4872
  have p17087 := n17087 _v _q 
  have p4991 := n4991 _v _q h4608
  have p4992 := n4992 _v _q h442
  have p17083 := n17083 _v _q 
  have p16576 := n16576 _v _q 
  have p16778 := n16778 _v _q 
  have p17110 := n17110 _v _q 
  have p17115 := n17115 _v _q 
  have p253 := n253 _v _q h191
  have p17106 := n17106 _v _q 
  have p17104 := n17104 _v _q 
  have p17096 := n17096 _v _q 
  have p17124 := n17124 _v _q 
  have p17102 := n17102 _v _q 
  have p17108 := n17108 _v _q 
  have p4994 := n4994 _v _q h3069
  have p17117 := n17117 _v _q 
  have p17120 := n17120 _v _q 
  have p17113 := n17113 _v _q 
  have p17122 := n17122 _v _q 
  have p4995 := n4995 _v _q h4369
  have p16175 := n16175 _v _q 
  have p5391 := n5391 _v _q 
  have p19135 := n19135 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  exact FloorCertificate.node_19140 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e61 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2834 _v) (e2849 _v) (e2863 _v) (e2877 _v) (e2879 _v) (e2883 _v) (e2898 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e3164 _v) (e4215 _v) (e4541 _v) (e4808 _v) p18599 p19131 p19139 p19045 p17093 p15209 p17141 p17131 p5005 p17069 p5001 p15555 p4996 p16913 p4999 p19066 p19041 p16791 p17133 p16911 p17136 p19138 p4998 p17221 p17053 p5003 p17127 p17968 p13951 p5008 p5255 p18597 p19073 p17061 p17055 p17147 p17058 p5006 p17137 p17966 p17056 p5007 p4971 p17064 p16929 p4980 p17067 p4979 p19074 p16994 p19075 p4985 p17074 p4987 p5010 p4988 p4981 p4983 p17072 p17080 p17078 p4989 p17091 p4986 p4978 p17100 p17098 p4984 p17087 p4991 p4992 p17083 p16576 p16778 p17110 p17115 p253 p17106 p17104 p17096 p17124 p17102 p17108 p4994 p17117 p17120 p17113 p17122 p4995 p16175 p5391 p19135
theorem n19142 (_v : Vars) (_q : Query _v)  : (e19141 _v) := by
  by_contra hc
  change ¬ ((e2475 _v) ∨ (¬ (e3169 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4419 _v)) ∨ (¬ (e4301 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4477 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4369 _v))) at hc
  have h70 : (e70 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h191 : (e191 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))
  have h225 : (e225 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h442 : (e442 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))
  have h488 : (e488 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))
  have h3069 : (e3069 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))
  have h3105 : (e3105 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h3169 : (e3169 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h3946 : (e3946 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h4059 : (e4059 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h4096 : (e4096 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4139 : (e4139 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))
  have h4156 : (e4156 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))
  have h4199 : (e4199 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h4260 : (e4260 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))
  have h4301 : (e4301 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h4369 : (e4369 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn)))))))))))))))))))))))))))))))
  have h4419 : (e4419 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h4434 : (e4434 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))
  have h4477 : (e4477 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))
  have h4608 : (e4608 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))
  have h4675 : (e4675 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h4747 : (e4747 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))
  have h4838 : (e4838 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))
  have h4872 : (e4872 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))
  have h8038 : (e8038 _v) := (fun hn => hc (Or.inl hn))
  have p19140 := n19140 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872 h8038
  exact p19140
theorem n19143 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e2475 _v) := by
  have p19142 := n19142 _v _q 
  have p4980 := n4980 _v _q h4301
  have p5001 := n5001 _v _q h4096
  have p4996 := n4996 _v _q h3937
  have p4999 := n4999 _v _q h91
  have p4998 := n4998 _v _q h3152
  have p5003 := n5003 _v _q h4199
  have p5008 := n5008 _v _q h4787
  have p17061 := n17061 _v _q h4747
  have p5006 := n5006 _v _q h4675
  have p17137 := n17137 _v _q h4059
  have p17056 := n17056 _v _q h3946
  have p5007 := n5007 _v _q h225
  have p4971 := n4971 _v _q h4419
  have p5005 := n5005 _v _q h3169
  have p4979 := n4979 _v _q h4139
  have p4985 := n4985 _v _q h4156
  have p4987 := n4987 _v _q h4434
  have p5010 := n5010 _v _q h70
  have p4988 := n4988 _v _q h488
  have p4981 := n4981 _v _q h4260
  have p4983 := n4983 _v _q h4813
  have p4989 := n4989 _v _q h4838
  have p4986 := n4986 _v _q h3105
  have p4978 := n4978 _v _q h4477
  have p4984 := n4984 _v _q h4872
  have p4991 := n4991 _v _q h4608
  have p4992 := n4992 _v _q h442
  have p253 := n253 _v _q h191
  have p4994 := n4994 _v _q h3069
  have p4995 := n4995 _v _q h4369
  change (e2475 _v) ∨ (¬ (e3169 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4419 _v)) ∨ (¬ (e4301 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4477 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4369 _v)) at p19142
  rcases p19142 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p5005))
  · exact (False.elim (hlit p5001))
  · exact (False.elim (hlit p4996))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p5003))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p17061))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p17137))
  · exact (False.elim (hlit p17056))
  · exact (False.elim (hlit p5007))
  · exact (False.elim (hlit p4971))
  · exact (False.elim (hlit p4980))
  · exact (False.elim (hlit p4979))
  · exact (False.elim (hlit p4985))
  · exact (False.elim (hlit p4987))
  · exact (False.elim (hlit p5010))
  · exact (False.elim (hlit p4988))
  · exact (False.elim (hlit p4981))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p4989))
  · exact (False.elim (hlit p4986))
  · exact (False.elim (hlit p4978))
  · exact (False.elim (hlit p4984))
  · exact (False.elim (hlit p4991))
  · exact (False.elim (hlit p4992))
  · exact (False.elim (hlit p253))
  · exact (False.elim (hlit p4994))
  · exact (False.elim (hlit p4995))
theorem n19144 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e2475 _v) := by
  have p19142 := n19142 _v _q 
  have p5005 := n5005 _v _q h3169
  have p5001 := n5001 _v _q h4096
  have p4996 := n4996 _v _q h3937
  have p4999 := n4999 _v _q h91
  have p4998 := n4998 _v _q h3152
  have p5003 := n5003 _v _q h4199
  have p5008 := n5008 _v _q h4787
  have p17061 := n17061 _v _q h4747
  have p5006 := n5006 _v _q h4675
  have p17137 := n17137 _v _q h4059
  have p17056 := n17056 _v _q h3946
  have p5007 := n5007 _v _q h225
  have p4971 := n4971 _v _q h4419
  have p4980 := n4980 _v _q h4301
  have p4979 := n4979 _v _q h4139
  have p4985 := n4985 _v _q h4156
  have p4987 := n4987 _v _q h4434
  have p5010 := n5010 _v _q h70
  have p4988 := n4988 _v _q h488
  have p4981 := n4981 _v _q h4260
  have p4983 := n4983 _v _q h4813
  have p4989 := n4989 _v _q h4838
  have p4986 := n4986 _v _q h3105
  have p4978 := n4978 _v _q h4477
  have p4984 := n4984 _v _q h4872
  have p4991 := n4991 _v _q h4608
  have p4992 := n4992 _v _q h442
  have p253 := n253 _v _q h191
  have p4994 := n4994 _v _q h3069
  have p4995 := n4995 _v _q h4369
  change (e2475 _v) ∨ (¬ (e3169 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4419 _v)) ∨ (¬ (e4301 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4477 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4369 _v)) at p19142
  rcases p19142 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p5005))
  · exact (False.elim (hlit p5001))
  · exact (False.elim (hlit p4996))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p5003))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p17061))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p17137))
  · exact (False.elim (hlit p17056))
  · exact (False.elim (hlit p5007))
  · exact (False.elim (hlit p4971))
  · exact (False.elim (hlit p4980))
  · exact (False.elim (hlit p4979))
  · exact (False.elim (hlit p4985))
  · exact (False.elim (hlit p4987))
  · exact (False.elim (hlit p5010))
  · exact (False.elim (hlit p4988))
  · exact (False.elim (hlit p4981))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p4989))
  · exact (False.elim (hlit p4986))
  · exact (False.elim (hlit p4978))
  · exact (False.elim (hlit p4984))
  · exact (False.elim (hlit p4991))
  · exact (False.elim (hlit p4992))
  · exact (False.elim (hlit p253))
  · exact (False.elim (hlit p4994))
  · exact (False.elim (hlit p4995))
theorem n19145 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e8035 _v) := by
  have p14871 := n14871 _v _q 
  have p19143 := n19143 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (¬ (e2475 _v)) ∨ (¬ (e8029 _v)) at p14871
  rcases p14871 with hlit | hlit
  · exact (False.elim (hlit p19143))
  · exact hlit
theorem n19146 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e4546 _v) := by
  have p16307 := n16307 _v _q 
  have p19145 := n19145 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (e8029 _v) ∨ (e4546 _v) at p16307
  change (¬ (e8029 _v)) at p19145
  rcases p16307 with hlit | hlit
  · exact (False.elim (p19145 hlit))
  · exact hlit
end
end Assembly
