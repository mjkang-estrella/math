import Dag206
import generated.th_lemma_25
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n19251 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3566 : (e3566 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4491 : (e4491 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) : (e6780 _v) := by
  have p14912 := n14912 _v _q 
  have p19250 := n19250 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3566 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4285 h4301 h4369 h4398 h4419 h4434 h4477 h4491 h4608 h4675 h4724 h4747 h4787 h4813 h4838 h4872 h4899
  change (¬ (e2799 _v)) ∨ (¬ (e8384 _v)) at p14912
  rcases p14912 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p19250))
theorem n19252 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3566 : (e3566 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4491 : (e4491 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) : (e8408 _v) := by
  have p15435 := n15435 _v _q 
  have p19251 := n19251 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3566 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4285 h4301 h4369 h4398 h4419 h4434 h4477 h4491 h4608 h4675 h4724 h4747 h4787 h4813 h4838 h4872 h4899
  change (e2799 _v) ∨ (¬ (e8407 _v)) at p15435
  change (¬ (e2799 _v)) at p19251
  rcases p15435 with hlit | hlit
  · exact (False.elim (p19251 hlit))
  · exact hlit
theorem n19253 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3566 : (e3566 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4491 : (e4491 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) : (e8398 _v) := by
  have p11470 := n11470 _v _q 
  have p19252 := n19252 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3566 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4285 h4301 h4369 h4398 h4419 h4434 h4477 h4491 h4608 h4675 h4724 h4747 h4787 h4813 h4838 h4872 h4899
  change (e8407 _v) ∨ (e8398 _v) at p11470
  change (¬ (e8407 _v)) at p19252
  rcases p11470 with hlit | hlit
  · exact (False.elim (p19252 hlit))
  · exact hlit
theorem n19254 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3566 : (e3566 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4491 : (e4491 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) : (e7489 _v) := by
  have p17115 := n17115 _v _q 
  have p17156 := n17156 _v _q h3566
  have p4972 := n4972 _v _q h4899
  have p19253 := n19253 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3566 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4285 h4301 h4369 h4398 h4419 h4434 h4477 h4491 h4608 h4675 h4724 h4747 h4787 h4813 h4838 h4872 h4899
  have p19242 := n19242 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4285 h4301 h4369 h4398 h4419 h4434 h4477 h4491 h4608 h4675 h4724 h4747 h4787 h4813 h4838 h4872
  have p16778 := n16778 _v _q 
  have p253 := n253 _v _q h191
  have p19189 := n19189 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p19051 := n19051 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p19053 := n19053 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p17104 := n17104 _v _q 
  have p13951 := n13951 _v _q 
  have p17110 := n17110 _v _q 
  have p17096 := n17096 _v _q 
  have p17106 := n17106 _v _q 
  have p17089 := n17089 _v _q 
  have p11375 := n11375 _v _q 
  have p17102 := n17102 _v _q 
  have p17108 := n17108 _v _q 
  have p4994 := n4994 _v _q h3069
  have p17117 := n17117 _v _q 
  have p17120 := n17120 _v _q 
  have p17113 := n17113 _v _q 
  have p17124 := n17124 _v _q 
  have p5005 := n5005 _v _q h3169
  have p16175 := n16175 _v _q 
  have p17122 := n17122 _v _q 
  have p19137 := n19137 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p17093 := n17093 _v _q 
  have p17141 := n17141 _v _q 
  have p17131 := n17131 _v _q 
  have p17069 := n17069 _v _q 
  have p5001 := n5001 _v _q h4096
  have p19148 := n19148 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p4996 := n4996 _v _q h3937
  have p16913 := n16913 _v _q 
  have p4999 := n4999 _v _q h91
  have p17133 := n17133 _v _q 
  have p16911 := n16911 _v _q 
  have p17136 := n17136 _v _q 
  have p4977 := n4977 _v _q h4285
  have p4998 := n4998 _v _q h3152
  have p17221 := n17221 _v _q 
  have p17053 := n17053 _v _q 
  have p5003 := n5003 _v _q h4199
  have p17127 := n17127 _v _q 
  have p4995 := n4995 _v _q h4369
  have p5008 := n5008 _v _q h4787
  have p19239 := n19239 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4285 h4301 h4369 h4398 h4419 h4434 h4477 h4491 h4608 h4675 h4724 h4747 h4787 h4813 h4838 h4872
  have p17134 := n17134 _v _q h4398
  have p17061 := n17061 _v _q h4747
  have p17055 := n17055 _v _q 
  have p17147 := n17147 _v _q 
  have p17058 := n17058 _v _q 
  have p5006 := n5006 _v _q h4675
  have p17137 := n17137 _v _q h4059
  have p17056 := n17056 _v _q h3946
  have p5007 := n5007 _v _q h225
  have p4971 := n4971 _v _q h4419
  have p17064 := n17064 _v _q 
  have p16929 := n16929 _v _q 
  have p4980 := n4980 _v _q h4301
  have p17067 := n17067 _v _q 
  have p4979 := n4979 _v _q h4139
  have p17128 := n17128 _v _q h4491
  have p16994 := n16994 _v _q 
  have p17094 := n17094 _v _q h4724
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
  exact FloorCertificate.node_19254 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e61 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2849 _v) (e2863 _v) (e2877 _v) (e2879 _v) (e2883 _v) (e2898 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2913 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e3164 _v) (e4215 _v) (e4541 _v) (e4808 _v) p17115 p17156 p4972 p19253 p19242 p16778 p253 p19189 p19051 p19053 p17104 p13951 p17110 p17096 p17106 p17089 p11375 p17102 p17108 p4994 p17117 p17120 p17113 p17124 p5005 p16175 p17122 p19137 p17093 p17141 p17131 p17069 p5001 p19148 p4996 p16913 p4999 p17133 p16911 p17136 p4977 p4998 p17221 p17053 p5003 p17127 p4995 p5008 p19239 p17134 p17061 p17055 p17147 p17058 p5006 p17137 p17056 p5007 p4971 p17064 p16929 p4980 p17067 p4979 p17128 p16994 p17094 p4985 p17074 p4987 p5010 p4988 p4981 p4983 p17072 p17080 p17078 p4989 p17091 p4986 p4978 p17100 p17098 p4984 p17087 p4991 p4992 p17083 p16576
theorem n19256 (_v : Vars) (_q : Query _v)  : (e19255 _v) := by
  by_contra hc
  change ¬ ((¬ (e4899 _v)) ∨ (¬ (e3566 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e3169 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e4285 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4398 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4419 _v)) ∨ (¬ (e4301 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e4491 _v)) ∨ (¬ (e4724 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4477 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e442 _v))) at hc
  have h70 : (e70 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h191 : (e191 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h225 : (e225 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))
  have h442 : (e442 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))))))))))))))))))))))))))))))))
  have h488 : (e488 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))
  have h3069 : (e3069 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h3105 : (e3105 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h3169 : (e3169 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h3566 : (e3566 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h3946 : (e3946 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))
  have h4059 : (e4059 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))
  have h4096 : (e4096 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h4139 : (e4139 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))
  have h4156 : (e4156 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))
  have h4199 : (e4199 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h4260 : (e4260 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))
  have h4285 : (e4285 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h4301 : (e4301 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))
  have h4369 : (e4369 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h4398 : (e4398 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h4419 : (e4419 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))
  have h4434 : (e4434 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))
  have h4477 : (e4477 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))))
  have h4491 : (e4491 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))
  have h4608 : (e4608 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))))))
  have h4675 : (e4675 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))
  have h4724 : (e4724 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))
  have h4747 : (e4747 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))
  have h4838 : (e4838 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))
  have h4872 : (e4872 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))))))
  have h4899 : (e4899 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have p19254 := n19254 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3566 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4285 h4301 h4369 h4398 h4419 h4434 h4477 h4491 h4608 h4675 h4724 h4747 h4787 h4813 h4838 h4872 h4899
  exact p19254
theorem n19257 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3566 : (e3566 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4491 : (e4491 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e4900 _v) := by
  have p19256 := n19256 _v _q 
  have p17156 := n17156 _v _q h3566
  have p253 := n253 _v _q h191
  have p4994 := n4994 _v _q h3069
  have p5005 := n5005 _v _q h3169
  have p5001 := n5001 _v _q h4096
  have p4996 := n4996 _v _q h3937
  have p4999 := n4999 _v _q h91
  have p4977 := n4977 _v _q h4285
  have p4998 := n4998 _v _q h3152
  have p5003 := n5003 _v _q h4199
  have p4995 := n4995 _v _q h4369
  have p5008 := n5008 _v _q h4787
  have p17134 := n17134 _v _q h4398
  have p17061 := n17061 _v _q h4747
  have p5006 := n5006 _v _q h4675
  have p17137 := n17137 _v _q h4059
  have p17056 := n17056 _v _q h3946
  have p5007 := n5007 _v _q h225
  have p4971 := n4971 _v _q h4419
  have p4980 := n4980 _v _q h4301
  have p4979 := n4979 _v _q h4139
  have p17128 := n17128 _v _q h4491
  have p17094 := n17094 _v _q h4724
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
  change (¬ (e4899 _v)) ∨ (¬ (e3566 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e3169 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e4285 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4398 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4419 _v)) ∨ (¬ (e4301 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e4491 _v)) ∨ (¬ (e4724 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4477 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e442 _v)) at p19256
  rcases p19256 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p17156))
  · exact (False.elim (hlit p253))
  · exact (False.elim (hlit p4994))
  · exact (False.elim (hlit p5005))
  · exact (False.elim (hlit p5001))
  · exact (False.elim (hlit p4996))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p4977))
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p5003))
  · exact (False.elim (hlit p4995))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p17134))
  · exact (False.elim (hlit p17061))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p17137))
  · exact (False.elim (hlit p17056))
  · exact (False.elim (hlit p5007))
  · exact (False.elim (hlit p4971))
  · exact (False.elim (hlit p4980))
  · exact (False.elim (hlit p4979))
  · exact (False.elim (hlit p17128))
  · exact (False.elim (hlit p17094))
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
theorem n19258 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3566 : (e3566 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4491 : (e4491 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e8367 _v) := by
  have p15064 := n15064 _v _q 
  have p19257 := n19257 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3566 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4285 h4301 h4369 h4398 h4419 h4434 h4477 h4491 h4608 h4675 h4724 h4747 h4787 h4813 h4838 h4872
  change (e8367 _v) ∨ (e4899 _v) at p15064
  change (¬ (e4899 _v)) at p19257
  rcases p15064 with hlit | hlit
  · exact hlit
  · exact (False.elim (p19257 hlit))
theorem n19259 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3566 : (e3566 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4491 : (e4491 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e2793 _v) := by
  have p14675 := n14675 _v _q 
  have p19258 := n19258 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3566 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4285 h4301 h4369 h4398 h4419 h4434 h4477 h4491 h4608 h4675 h4724 h4747 h4787 h4813 h4838 h4872
  change (e2793 _v) ∨ (¬ (e8367 _v)) at p14675
  rcases p14675 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p19258))
theorem n19260 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3566 : (e3566 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4491 : (e4491 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e4910 _v) := by
  have p14701 := n14701 _v _q 
  have p19259 := n19259 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3566 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4285 h4301 h4369 h4398 h4419 h4434 h4477 h4491 h4608 h4675 h4724 h4747 h4787 h4813 h4838 h4872
  change (¬ (e2793 _v)) ∨ (¬ (e4909 _v)) at p14701
  rcases p14701 with hlit | hlit
  · exact (False.elim (hlit p19259))
  · exact hlit
theorem n19261 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3566 : (e3566 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4491 : (e4491 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e4903 _v) := by
  have p14973 := n14973 _v _q 
  have p19260 := n19260 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3566 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4285 h4301 h4369 h4398 h4419 h4434 h4477 h4491 h4608 h4675 h4724 h4747 h4787 h4813 h4838 h4872
  change (e4909 _v) ∨ (e4903 _v) at p14973
  change (¬ (e4909 _v)) at p19260
  rcases p14973 with hlit | hlit
  · exact (False.elim (p19260 hlit))
  · exact hlit
theorem n19262 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3566 : (e3566 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4491 : (e4491 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e7489 _v) := by
  have p19259 := n19259 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3566 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4285 h4301 h4369 h4398 h4419 h4434 h4477 h4491 h4608 h4675 h4724 h4747 h4787 h4813 h4838 h4872
  have p4992 := n4992 _v _q h442
  have p17083 := n17083 _v _q 
  have p19261 := n19261 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3566 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4285 h4301 h4369 h4398 h4419 h4434 h4477 h4491 h4608 h4675 h4724 h4747 h4787 h4813 h4838 h4872
  have p19239 := n19239 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4285 h4301 h4369 h4398 h4419 h4434 h4477 h4491 h4608 h4675 h4724 h4747 h4787 h4813 h4838 h4872
  have p19242 := n19242 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4285 h4301 h4369 h4398 h4419 h4434 h4477 h4491 h4608 h4675 h4724 h4747 h4787 h4813 h4838 h4872
  have p11375 := n11375 _v _q 
  have p16778 := n16778 _v _q 
  have p17115 := n17115 _v _q 
  have p17156 := n17156 _v _q h3566
  have p253 := n253 _v _q h191
  have p19189 := n19189 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p19051 := n19051 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p19053 := n19053 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p17104 := n17104 _v _q 
  have p13951 := n13951 _v _q 
  have p17110 := n17110 _v _q 
  have p17096 := n17096 _v _q 
  have p17106 := n17106 _v _q 
  have p17089 := n17089 _v _q 
  have p17102 := n17102 _v _q 
  have p17108 := n17108 _v _q 
  have p4994 := n4994 _v _q h3069
  have p17117 := n17117 _v _q 
  have p17120 := n17120 _v _q 
  have p17113 := n17113 _v _q 
  have p17124 := n17124 _v _q 
  have p5005 := n5005 _v _q h3169
  have p16175 := n16175 _v _q 
  have p17122 := n17122 _v _q 
  have p19137 := n19137 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p17093 := n17093 _v _q 
  have p17141 := n17141 _v _q 
  have p17131 := n17131 _v _q 
  have p17069 := n17069 _v _q 
  have p5001 := n5001 _v _q h4096
  have p19148 := n19148 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p4996 := n4996 _v _q h3937
  have p16913 := n16913 _v _q 
  have p4999 := n4999 _v _q h91
  have p17133 := n17133 _v _q 
  have p16911 := n16911 _v _q 
  have p17136 := n17136 _v _q 
  have p4977 := n4977 _v _q h4285
  have p4998 := n4998 _v _q h3152
  have p17221 := n17221 _v _q 
  have p17053 := n17053 _v _q 
  have p5003 := n5003 _v _q h4199
  have p17127 := n17127 _v _q 
  have p4995 := n4995 _v _q h4369
  have p5008 := n5008 _v _q h4787
  have p16576 := n16576 _v _q 
  have p17134 := n17134 _v _q h4398
  have p17061 := n17061 _v _q h4747
  have p17055 := n17055 _v _q 
  have p17147 := n17147 _v _q 
  have p17058 := n17058 _v _q 
  have p5006 := n5006 _v _q h4675
  have p17137 := n17137 _v _q h4059
  have p17056 := n17056 _v _q h3946
  have p5007 := n5007 _v _q h225
  have p4971 := n4971 _v _q h4419
  have p17064 := n17064 _v _q 
  have p16929 := n16929 _v _q 
  have p4980 := n4980 _v _q h4301
  have p17067 := n17067 _v _q 
  have p4979 := n4979 _v _q h4139
  have p17128 := n17128 _v _q h4491
  have p16994 := n16994 _v _q 
  have p17094 := n17094 _v _q h4724
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
  exact FloorCertificate.node_19262 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e61 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2849 _v) (e2863 _v) (e2877 _v) (e2879 _v) (e2883 _v) (e2898 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e3164 _v) (e4215 _v) (e4541 _v) (e4808 _v) p19259 p4992 p17083 p19261 p19239 p19242 p11375 p16778 p17115 p17156 p253 p19189 p19051 p19053 p17104 p13951 p17110 p17096 p17106 p17089 p17102 p17108 p4994 p17117 p17120 p17113 p17124 p5005 p16175 p17122 p19137 p17093 p17141 p17131 p17069 p5001 p19148 p4996 p16913 p4999 p17133 p16911 p17136 p4977 p4998 p17221 p17053 p5003 p17127 p4995 p5008 p16576 p17134 p17061 p17055 p17147 p17058 p5006 p17137 p17056 p5007 p4971 p17064 p16929 p4980 p17067 p4979 p17128 p16994 p17094 p4985 p17074 p4987 p5010 p4988 p4981 p4983 p17072 p17080 p17078 p4989 p17091 p4986 p4978 p17100 p17098 p4984 p17087 p4991
theorem n19264 (_v : Vars) (_q : Query _v)  : (e19263 _v) := by
  by_contra hc
  change ¬ ((¬ (e3566 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e3169 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e4285 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4398 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4419 _v)) ∨ (¬ (e4301 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e4491 _v)) ∨ (¬ (e4724 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4477 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v))) at hc
  have h70 : (e70 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h191 : (e191 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h225 : (e225 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))
  have h442 : (e442 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h488 : (e488 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))
  have h3069 : (e3069 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h3105 : (e3105 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h3169 : (e3169 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h3566 : (e3566 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h3946 : (e3946 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))
  have h4059 : (e4059 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))
  have h4096 : (e4096 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h4139 : (e4139 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))
  have h4156 : (e4156 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))
  have h4199 : (e4199 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h4260 : (e4260 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))
  have h4285 : (e4285 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h4301 : (e4301 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))
  have h4369 : (e4369 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h4398 : (e4398 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h4419 : (e4419 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))
  have h4434 : (e4434 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))
  have h4477 : (e4477 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))))
  have h4491 : (e4491 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))
  have h4608 : (e4608 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn)))))))))))))))))))))))))))))))))))
  have h4675 : (e4675 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))
  have h4724 : (e4724 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))
  have h4747 : (e4747 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))
  have h4838 : (e4838 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))
  have h4872 : (e4872 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))))))
  have p19262 := n19262 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3566 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4285 h4301 h4369 h4398 h4419 h4434 h4477 h4491 h4608 h4675 h4724 h4747 h4787 h4813 h4838 h4872
  exact p19262
theorem n19265 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e4286 _v) := by
  have p19264 := n19264 _v _q 
  have p19056 := n19056 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p17111 := n17111 _v _q 
  have p4994 := n4994 _v _q h3069
  have p253 := n253 _v _q h191
  have p5001 := n5001 _v _q h4096
  have p4996 := n4996 _v _q h3937
  have p4999 := n4999 _v _q h91
  have p4992 := n4992 _v _q h442
  have p4998 := n4998 _v _q h3152
  have p5003 := n5003 _v _q h4199
  have p4995 := n4995 _v _q h4369
  have p5008 := n5008 _v _q h4787
  have p5005 := n5005 _v _q h3169
  have p17061 := n17061 _v _q h4747
  have p5006 := n5006 _v _q h4675
  have p17137 := n17137 _v _q h4059
  have p17056 := n17056 _v _q h3946
  have p5007 := n5007 _v _q h225
  have p4971 := n4971 _v _q h4419
  have p4980 := n4980 _v _q h4301
  have p4979 := n4979 _v _q h4139
  have p19059 := n19059 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p19062 := n19062 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
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
  change (¬ (e3566 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e3169 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e4285 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4398 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4419 _v)) ∨ (¬ (e4301 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e4491 _v)) ∨ (¬ (e4724 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4477 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) at p19264
  rcases p19264 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact (False.elim (hlit p17111))
  · exact (False.elim (hlit p4992))
  · exact (False.elim (hlit p253))
  · exact (False.elim (hlit p4994))
  · exact (False.elim (hlit p5005))
  · exact (False.elim (hlit p5001))
  · exact (False.elim (hlit p4996))
  · exact (False.elim (hlit p4999))
  · exact hlit
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p5003))
  · exact (False.elim (hlit p4995))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p19056))
  · exact (False.elim (hlit p17061))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p17137))
  · exact (False.elim (hlit p17056))
  · exact (False.elim (hlit p5007))
  · exact (False.elim (hlit p4971))
  · exact (False.elim (hlit p4980))
  · exact (False.elim (hlit p4979))
  · exact (False.elim (hlit p19059))
  · exact (False.elim (hlit p19062))
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
theorem n19266 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e7798 _v) := by
  have p16274 := n16274 _v _q 
  have p19265 := n19265 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (e7798 _v) ∨ (e4285 _v) at p16274
  change (¬ (e4285 _v)) at p19265
  rcases p16274 with hlit | hlit
  · exact hlit
  · exact (False.elim (p19265 hlit))
theorem n19267 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e7807 _v) := by
  have p14837 := n14837 _v _q 
  have p19266 := n19266 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (¬ (e2303 _v)) ∨ (¬ (e7798 _v)) at p14837
  rcases p14837 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p19266))
theorem n19268 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e7489 _v) := by
  have p19130 := n19130 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p19267 := n19267 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p19051 := n19051 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  exact FloorCertificate.node_19268 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e110 _v) p19130 p19267 p19051
theorem n19270 (_v : Vars) (_q : Query _v)  : (e19269 _v) := by
  by_contra hc
  change ¬ ((¬ (e3169 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4419 _v)) ∨ (¬ (e4301 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4477 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v))) at hc
  have h70 : (e70 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h191 : (e191 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h225 : (e225 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))
  have h442 : (e442 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h488 : (e488 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))
  have h3069 : (e3069 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h3105 : (e3105 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h3169 : (e3169 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h3946 : (e3946 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h4059 : (e4059 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h4096 : (e4096 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4139 : (e4139 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))
  have h4156 : (e4156 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))
  have h4199 : (e4199 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h4260 : (e4260 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))
  have h4301 : (e4301 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))
  have h4369 : (e4369 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h4419 : (e4419 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))
  have h4434 : (e4434 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))
  have h4477 : (e4477 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))
  have h4608 : (e4608 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))))))))))))))))))))))))))
  have h4675 : (e4675 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h4747 : (e4747 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))
  have h4838 : (e4838 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))
  have h4872 : (e4872 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))
  have p19268 := n19268 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  exact p19268
theorem n19271 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e3170 _v) := by
  have p19270 := n19270 _v _q 
  have p4980 := n4980 _v _q h4301
  have p253 := n253 _v _q h191
  have p5001 := n5001 _v _q h4096
  have p4996 := n4996 _v _q h3937
  have p4999 := n4999 _v _q h91
  have p4992 := n4992 _v _q h442
  have p4998 := n4998 _v _q h3152
  have p5003 := n5003 _v _q h4199
  have p4995 := n4995 _v _q h4369
  have p5008 := n5008 _v _q h4787
  have p17061 := n17061 _v _q h4747
  have p5006 := n5006 _v _q h4675
  have p17137 := n17137 _v _q h4059
  have p17056 := n17056 _v _q h3946
  have p5007 := n5007 _v _q h225
  have p4971 := n4971 _v _q h4419
  have p4994 := n4994 _v _q h3069
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
  change (¬ (e3169 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4419 _v)) ∨ (¬ (e4301 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4477 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) at p19270
  rcases p19270 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p4994))
  · exact (False.elim (hlit p253))
  · exact (False.elim (hlit p5001))
  · exact (False.elim (hlit p4996))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p4992))
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p5003))
  · exact (False.elim (hlit p4995))
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
theorem n19272 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e6888 _v) := by
  have p14769 := n14769 _v _q 
  have p19271 := n19271 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (e6888 _v) ∨ (e3169 _v) at p14769
  change (¬ (e3169 _v)) at p19271
  rcases p14769 with hlit | hlit
  · exact hlit
  · exact (False.elim (p19271 hlit))
theorem n19273 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e2634 _v) := by
  have p14360 := n14360 _v _q 
  have p19272 := n19272 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (e2634 _v) ∨ (¬ (e6888 _v)) at p14360
  rcases p14360 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p19272))
theorem n19274 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e3180 _v) := by
  have p14361 := n14361 _v _q 
  have p19273 := n19273 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (¬ (e2634 _v)) ∨ (¬ (e3179 _v)) at p14361
  rcases p14361 with hlit | hlit
  · exact (False.elim (hlit p19273))
  · exact hlit
theorem n19275 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e3173 _v) := by
  have p6907 := n6907 _v _q 
  have p19274 := n19274 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (e3179 _v) ∨ (e3173 _v) at p6907
  change (¬ (e3179 _v)) at p19274
  rcases p6907 with hlit | hlit
  · exact (False.elim (p19274 hlit))
  · exact hlit
theorem n19276 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e2482 _v) := by
  have p11035 := n11035 _v _q 
  have p19273 := n19273 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (¬ (e2634 _v)) ∨ (e2482 _v) at p11035
  rcases p11035 with hlit | hlit
  · exact (False.elim (hlit p19273))
  · exact hlit
theorem n19277 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e4405 _v) := by
  have p14702 := n14702 _v _q 
  have p19276 := n19276 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (¬ (e2482 _v)) ∨ (¬ (e4404 _v)) at p14702
  rcases p14702 with hlit | hlit
  · exact (False.elim (hlit p19276))
  · exact hlit
theorem n19278 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e4398 _v) := by
  have p14976 := n14976 _v _q 
  have p19277 := n19277 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (e4404 _v) ∨ (e4398 _v) at p14976
  change (¬ (e4404 _v)) at p19277
  rcases p14976 with hlit | hlit
  · exact (False.elim (p19277 hlit))
  · exact hlit
theorem n19279 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e2310 _v) := by
  have p11365 := n11365 _v _q 
  have p19273 := n19273 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (e2310 _v) ∨ (¬ (e2634 _v)) at p11365
  rcases p11365 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p19273))
theorem n19280 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e2254 _v) := by
  have p11361 := n11361 _v _q 
  have p19279 := n19279 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (e2254 _v) ∨ (¬ (e2310 _v)) at p11361
  rcases p11361 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p19279))
theorem n19281 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h7807 : (e7807 _v)) : (e2793 _v) := by
  have p11350 := n11350 _v _q h7807
  have p19276 := n19276 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  exact FloorCertificate.node_19281 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p11350 p19276
theorem n19282 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h7807 : (e7807 _v)) : (e4910 _v) := by
  have p14701 := n14701 _v _q 
  have p19281 := n19281 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872 h7807
  change (¬ (e2793 _v)) ∨ (¬ (e4909 _v)) at p14701
  rcases p14701 with hlit | hlit
  · exact (False.elim (hlit p19281))
  · exact hlit
theorem n19283 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e2746 _v) := by
  have p19279 := n19279 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p10893 := n10893 _v _q 
  exact FloorCertificate.node_19283 (e2 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p19279 p10893
theorem n19284 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e3984 _v) := by
  have p14691 := n14691 _v _q 
  have p19283 := n19283 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (¬ (e2746 _v)) ∨ (¬ (e3983 _v)) at p14691
  rcases p14691 with hlit | hlit
  · exact (False.elim (hlit p19283))
  · exact hlit
theorem n19285 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e2697 _v) := by
  have p11391 := n11391 _v _q 
  have p19280 := n19280 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (e2697 _v) ∨ (¬ (e2254 _v)) at p11391
  rcases p11391 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p19280))
theorem n19286 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e4499 _v) := by
  have p14700 := n14700 _v _q 
  have p19285 := n19285 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (¬ (e2697 _v)) ∨ (¬ (e4498 _v)) at p14700
  rcases p14700 with hlit | hlit
  · exact (False.elim (hlit p19285))
  · exact hlit
theorem n19287 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e4491 _v) := by
  have p14969 := n14969 _v _q 
  have p19286 := n19286 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (e4498 _v) ∨ (e4491 _v) at p14969
  change (¬ (e4498 _v)) at p19286
  rcases p14969 with hlit | hlit
  · exact (False.elim (p19286 hlit))
  · exact hlit
theorem n19288 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e4731 _v) := by
  have p14698 := n14698 _v _q 
  have p19280 := n19280 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (¬ (e2254 _v)) ∨ (¬ (e4730 _v)) at p14698
  rcases p14698 with hlit | hlit
  · exact (False.elim (hlit p19280))
  · exact hlit
theorem n19289 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e4724 _v) := by
  have p15518 := n15518 _v _q 
  have p19288 := n19288 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (e4730 _v) ∨ (e4724 _v) at p15518
  change (¬ (e4730 _v)) at p19288
  rcases p15518 with hlit | hlit
  · exact (False.elim (p19288 hlit))
  · exact hlit
theorem n19290 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2364 : (e2364 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4546 : (e4546 _v)) (h4562 : (e4562 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h5100 : (e5100 _v)) (h7493 : (e7493 _v)) (h7749 : (e7749 _v)) (h7814 : (e7814 _v)) : (e7943 _v) := by
  have p17356 := n17356 _v _q 
  have p4973 := n4973 _v _q h4562
  have p4986 := n4986 _v _q h3105
  have p4978 := n4978 _v _q h4477
  have p16269 := n16269 _v _q h7749
  have p4992 := n4992 _v _q h442
  have p17159 := n17159 _v _q h5100
  have p19275 := n19275 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p4984 := n4984 _v _q h4872
  have p15567 := n15567 _v _q h2364
  have p4991 := n4991 _v _q h4608
  have p253 := n253 _v _q h191
  have p17076 := n17076 _v _q h3976
  have p4979 := n4979 _v _q h4139
  have p17172 := n17172 _v _q h7814
  have p4994 := n4994 _v _q h3069
  have p17155 := n17155 _v _q h7493
  have p5001 := n5001 _v _q h4096
  have p4976 := n4976 _v _q h4546
  have p4996 := n4996 _v _q h3937
  have p4999 := n4999 _v _q h91
  have p4998 := n4998 _v _q h3152
  have p15170 := n15170 _v _q h2364
  have p5003 := n5003 _v _q h4199
  have p4995 := n4995 _v _q h4369
  have p5008 := n5008 _v _q h4787
  have p19278 := n19278 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p17061 := n17061 _v _q h4747
  have p5006 := n5006 _v _q h4675
  have p17137 := n17137 _v _q h4059
  have p17056 := n17056 _v _q h3946
  have p5007 := n5007 _v _q h225
  have p4980 := n4980 _v _q h4301
  have p19287 := n19287 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p19289 := n19289 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p4985 := n4985 _v _q h4156
  have p4987 := n4987 _v _q h4434
  have p5010 := n5010 _v _q h70
  have p4988 := n4988 _v _q h488
  have p4981 := n4981 _v _q h4260
  have p4983 := n4983 _v _q h4813
  have p4989 := n4989 _v _q h4838
  change (¬ (e7935 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4477 _v)) ∨ (¬ (e7749 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e5100 _v)) ∨ (¬ (e3173 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4903 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e3976 _v)) ∨ (¬ (e4562 _v)) ∨ (¬ (e7814 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e7493 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e4546 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4398 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4301 _v)) ∨ (¬ (e4491 _v)) ∨ (¬ (e4724 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4838 _v)) at p17356
  rcases p17356 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p4979))
  · exact (False.elim (hlit p4986))
  · exact (False.elim (hlit p4978))
  · exact (False.elim (hlit p16269))
  · exact (False.elim (hlit p4992))
  · exact (False.elim (hlit p17159))
  · exact (False.elim (hlit p19275))
  · exact (False.elim (hlit p4984))
  · exact (False.elim (hlit p15567))
  · exact (False.elim (hlit p4991))
  · exact (False.elim (hlit p253))
  · exact (False.elim (hlit p17076))
  · exact (False.elim (hlit p4973))
  · exact (False.elim (hlit p17172))
  · exact (False.elim (hlit p4994))
  · exact (False.elim (hlit p17155))
  · exact (False.elim (hlit p5001))
  · exact (False.elim (hlit p4976))
  · exact (False.elim (hlit p4996))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p15170))
  · exact (False.elim (hlit p5003))
  · exact (False.elim (hlit p4995))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p19278))
  · exact (False.elim (hlit p17061))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p17137))
  · exact (False.elim (hlit p17056))
  · exact (False.elim (hlit p5007))
  · exact (False.elim (hlit p4980))
  · exact (False.elim (hlit p19287))
  · exact (False.elim (hlit p19289))
  · exact (False.elim (hlit p4985))
  · exact (False.elim (hlit p4987))
  · exact (False.elim (hlit p5010))
  · exact (False.elim (hlit p4988))
  · exact (False.elim (hlit p4981))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p4989))
theorem n19291 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2364 : (e2364 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4546 : (e4546 _v)) (h4562 : (e4562 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h5100 : (e5100 _v)) (h7493 : (e7493 _v)) (h7749 : (e7749 _v)) (h7814 : (e7814 _v)) : (e7944 _v) := by
  have p15266 := n15266 _v _q 
  have p19290 := n19290 _v _q h70 h91 h191 h225 h442 h488 h2364 h3069 h3105 h3152 h3937 h3946 h3976 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4546 h4562 h4608 h4675 h4747 h4787 h4813 h4838 h4872 h5100 h7493 h7749 h7814
  change (e7944 _v) ∨ (e7935 _v) at p15266
  change (¬ (e7935 _v)) at p19290
  rcases p15266 with hlit | hlit
  · exact hlit
  · exact (False.elim (p19290 hlit))
theorem n19292 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2364 : (e2364 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4546 : (e4546 _v)) (h4562 : (e4562 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h5100 : (e5100 _v)) (h7493 : (e7493 _v)) (h7749 : (e7749 _v)) (h7814 : (e7814 _v)) : (e2787 _v) := by
  have p15228 := n15228 _v _q 
  have p19291 := n19291 _v _q h70 h91 h191 h225 h442 h488 h2364 h3069 h3105 h3152 h3937 h3946 h3976 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4546 h4562 h4608 h4675 h4747 h4787 h4813 h4838 h4872 h5100 h7493 h7749 h7814
  change (e2787 _v) ∨ (¬ (e7944 _v)) at p15228
  rcases p15228 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p19291))
theorem n19293 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2364 : (e2364 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4546 : (e4546 _v)) (h4562 : (e4562 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h5100 : (e5100 _v)) (h7493 : (e7493 _v)) (h7749 : (e7749 _v)) (h7814 : (e7814 _v)) : (e7489 _v) := by
  have p10893 := n10893 _v _q 
  have p4989 := n4989 _v _q h4838
  have p4971 := n4971 _v _q h4419
  have p17091 := n17091 _v _q 
  have p4979 := n4979 _v _q h4139
  have p4986 := n4986 _v _q h3105
  have p19292 := n19292 _v _q h70 h91 h191 h225 h442 h488 h2364 h3069 h3105 h3152 h3937 h3946 h3976 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4546 h4562 h4608 h4675 h4747 h4787 h4813 h4838 h4872 h5100 h7493 h7749 h7814
  have p4978 := n4978 _v _q h4477
  have p16269 := n16269 _v _q h7749
  have p4992 := n4992 _v _q h442
  have p17159 := n17159 _v _q h5100
  have p19275 := n19275 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p4984 := n4984 _v _q h4872
  have p17083 := n17083 _v _q 
  have p15567 := n15567 _v _q h2364
  have p4991 := n4991 _v _q h4608
  have p17087 := n17087 _v _q 
  have p16778 := n16778 _v _q 
  have p17115 := n17115 _v _q 
  have p17111 := n17111 _v _q 
  have p253 := n253 _v _q h191
  have p17076 := n17076 _v _q h3976
  have p17098 := n17098 _v _q 
  have p4973 := n4973 _v _q h4562
  have p17104 := n17104 _v _q 
  have p17172 := n17172 _v _q h7814
  have p17110 := n17110 _v _q 
  have p17096 := n17096 _v _q 
  have p17106 := n17106 _v _q 
  have p17089 := n17089 _v _q 
  have p17102 := n17102 _v _q 
  have p17108 := n17108 _v _q 
  have p4994 := n4994 _v _q h3069
  have p17117 := n17117 _v _q 
  have p17120 := n17120 _v _q 
  have p17113 := n17113 _v _q 
  have p17124 := n17124 _v _q 
  have p16394 := n16394 _v _q 
  have p17122 := n17122 _v _q 
  have p17155 := n17155 _v _q h7493
  have p17093 := n17093 _v _q 
  have p17141 := n17141 _v _q 
  have p17131 := n17131 _v _q 
  have p17069 := n17069 _v _q 
  have p5001 := n5001 _v _q h4096
  have p4976 := n4976 _v _q h4546
  have p4996 := n4996 _v _q h3937
  have p17100 := n17100 _v _q 
  have p4999 := n4999 _v _q h91
  have p17133 := n17133 _v _q 
  have p16977 := n16977 _v _q 
  have p17136 := n17136 _v _q 
  have p4998 := n4998 _v _q h3152
  have p15170 := n15170 _v _q h2364
  have p17053 := n17053 _v _q 
  have p5003 := n5003 _v _q h4199
  have p17127 := n17127 _v _q 
  have p4995 := n4995 _v _q h4369
  have p5008 := n5008 _v _q h4787
  have p16576 := n16576 _v _q 
  have p19278 := n19278 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p17061 := n17061 _v _q h4747
  have p17055 := n17055 _v _q 
  have p17147 := n17147 _v _q 
  have p17058 := n17058 _v _q 
  have p5006 := n5006 _v _q h4675
  have p17137 := n17137 _v _q h4059
  have p17056 := n17056 _v _q h3946
  have p5007 := n5007 _v _q h225
  have p17064 := n17064 _v _q 
  have p16929 := n16929 _v _q 
  have p4980 := n4980 _v _q h4301
  have p17067 := n17067 _v _q 
  have p13951 := n13951 _v _q 
  have p19287 := n19287 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p16994 := n16994 _v _q 
  have p19289 := n19289 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
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
  have p8527 := n8527 _v _q h2364
  exact FloorCertificate.node_19293 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e61 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2834 _v) (e2849 _v) (e2863 _v) (e2877 _v) (e2883 _v) (e2898 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p10893 p4989 p4971 p17091 p4979 p4986 p19292 p4978 p16269 p4992 p17159 p19275 p4984 p17083 p15567 p4991 p17087 p16778 p17115 p17111 p253 p17076 p17098 p4973 p17104 p17172 p17110 p17096 p17106 p17089 p17102 p17108 p4994 p17117 p17120 p17113 p17124 p16394 p17122 p17155 p17093 p17141 p17131 p17069 p5001 p4976 p4996 p17100 p4999 p17133 p16977 p17136 p4998 p15170 p17053 p5003 p17127 p4995 p5008 p16576 p19278 p17061 p17055 p17147 p17058 p5006 p17137 p17056 p5007 p17064 p16929 p4980 p17067 p13951 p19287 p16994 p19289 p4985 p17074 p4987 p5010 p4988 p4981 p4983 p17072 p17080 p17078 p8527
theorem n19295 (_v : Vars) (_q : Query _v)  : (e19294 _v) := by
  by_contra hc
  change ¬ ((¬ (e4562 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4419 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4477 _v)) ∨ (¬ (e7749 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e5100 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e3976 _v)) ∨ (¬ (e7814 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e7493 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e4546 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4301 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e2364 _v))) at hc
  have h70 : (e70 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))
  have h191 : (e191 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h225 : (e225 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))
  have h442 : (e442 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h488 : (e488 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))))))
  have h2364 : (e2364 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn)))))))))))))))))))))))))))))))))))))
  have h3069 : (e3069 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h3105 : (e3105 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))
  have h3946 : (e3946 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))
  have h3976 : (e3976 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h4059 : (e4059 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))
  have h4096 : (e4096 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))
  have h4139 : (e4139 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4156 : (e4156 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))
  have h4199 : (e4199 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))
  have h4260 : (e4260 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))))))
  have h4301 : (e4301 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))
  have h4369 : (e4369 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))
  have h4419 : (e4419 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4434 : (e4434 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))))
  have h4477 : (e4477 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h4546 : (e4546 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))
  have h4562 : (e4562 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h4608 : (e4608 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h4675 : (e4675 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))
  have h4747 : (e4747 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))))))))
  have h4838 : (e4838 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h4872 : (e4872 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h5100 : (e5100 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h7493 : (e7493 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))
  have h7749 : (e7749 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h7814 : (e7814 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have p19293 := n19293 _v _q h70 h91 h191 h225 h442 h488 h2364 h3069 h3105 h3152 h3937 h3946 h3976 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4546 h4562 h4608 h4675 h4747 h4787 h4813 h4838 h4872 h5100 h7493 h7749 h7814
  exact p19293
theorem n19296 (_v : Vars) (_q : Query _v) (h7807 : (e7807 _v)) : (e3976 _v) := by
  have p14935 := n14935 _v _q 
  have p15569 := n15569 _v _q h7807
  change (e3983 _v) ∨ (e3976 _v) at p14935
  change (¬ (e3983 _v)) at p15569
  rcases p14935 with hlit | hlit
  · exact (False.elim (p15569 hlit))
  · exact hlit
theorem n19297 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2364 : (e2364 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h7807 : (e7807 _v)) : (e4563 _v) := by
  have p19295 := n19295 _v _q 
  have p8527 := n8527 _v _q h2364
  have p4971 := n4971 _v _q h4419
  have p4979 := n4979 _v _q h4139
  have p4986 := n4986 _v _q h3105
  have p4978 := n4978 _v _q h4477
  have p17786 := n17786 _v _q h7807
  have p4992 := n4992 _v _q h442
  have p18959 := n18959 _v _q h7807
  have p4984 := n4984 _v _q h4872
  have p4991 := n4991 _v _q h4608
  have p253 := n253 _v _q h191
  have p19296 := n19296 _v _q h7807
  have p15373 := n15373 _v _q h7807
  have p4994 := n4994 _v _q h3069
  have p15485 := n15485 _v _q h7807
  have p5001 := n5001 _v _q h4096
  have p16927 := n16927 _v _q h4419 h7807
  have p4996 := n4996 _v _q h3937
  have p4999 := n4999 _v _q h91
  have p4998 := n4998 _v _q h3152
  have p5003 := n5003 _v _q h4199
  have p4995 := n4995 _v _q h4369
  have p5008 := n5008 _v _q h4787
  have p17061 := n17061 _v _q h4747
  have p5006 := n5006 _v _q h4675
  have p17137 := n17137 _v _q h4059
  have p17056 := n17056 _v _q h3946
  have p5007 := n5007 _v _q h225
  have p4980 := n4980 _v _q h4301
  have p4985 := n4985 _v _q h4156
  have p4987 := n4987 _v _q h4434
  have p5010 := n5010 _v _q h70
  have p4988 := n4988 _v _q h488
  have p4981 := n4981 _v _q h4260
  have p4983 := n4983 _v _q h4813
  have p4989 := n4989 _v _q h4838
  change (¬ (e4562 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4419 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4477 _v)) ∨ (¬ (e7749 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e5100 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e3976 _v)) ∨ (¬ (e7814 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e7493 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e4546 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4301 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e2364 _v)) at p19295
  rcases p19295 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p4989))
  · exact (False.elim (hlit p4971))
  · exact (False.elim (hlit p4979))
  · exact (False.elim (hlit p4986))
  · exact (False.elim (hlit p4978))
  · exact (False.elim (hlit p17786))
  · exact (False.elim (hlit p4992))
  · exact (False.elim (hlit p18959))
  · exact (False.elim (hlit p4984))
  · exact (False.elim (hlit p4991))
  · exact (False.elim (hlit p253))
  · exact (False.elim (hlit p19296))
  · exact (False.elim (hlit p15373))
  · exact (False.elim (hlit p4994))
  · exact (False.elim (hlit p15485))
  · exact (False.elim (hlit p5001))
  · exact (False.elim (hlit p16927))
  · exact (False.elim (hlit p4996))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p5003))
  · exact (False.elim (hlit p4995))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p17061))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p17137))
  · exact (False.elim (hlit p17056))
  · exact (False.elim (hlit p5007))
  · exact (False.elim (hlit p4980))
  · exact (False.elim (hlit p4985))
  · exact (False.elim (hlit p4987))
  · exact (False.elim (hlit p5010))
  · exact (False.elim (hlit p4988))
  · exact (False.elim (hlit p4981))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p8527))
theorem n19298 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2364 : (e2364 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h7807 : (e7807 _v)) : (e8052 _v) := by
  have p15155 := n15155 _v _q 
  have p19297 := n19297 _v _q h70 h91 h191 h225 h442 h488 h2364 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872 h7807
  change (e8052 _v) ∨ (e4562 _v) at p15155
  change (¬ (e4562 _v)) at p19297
  rcases p15155 with hlit | hlit
  · exact hlit
  · exact (False.elim (p19297 hlit))
theorem n19299 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2364 : (e2364 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h7807 : (e7807 _v)) : (e1995 _v) := by
  have p14622 := n14622 _v _q 
  have p19298 := n19298 _v _q h70 h91 h191 h225 h442 h488 h2364 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872 h7807
  change (e1995 _v) ∨ (¬ (e8052 _v)) at p14622
  rcases p14622 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p19298))
end
end Assembly
