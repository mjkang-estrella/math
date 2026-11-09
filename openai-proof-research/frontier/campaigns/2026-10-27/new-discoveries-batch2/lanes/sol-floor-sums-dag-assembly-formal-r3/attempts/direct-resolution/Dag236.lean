import Dag235
import generated.th_lemma_30
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n20653 (_v : Vars) (_q : Query _v)  : (e4369 _v) := by
  have p16222 := n16222 _v _q 
  have p20652 := n20652 _v _q 
  simp only [e4367, e4368, e4369, e4370, e7887, e7888, e7895] at *
  tauto
theorem n20654 (_v : Vars) (_q : Query _v) (h474 : (e474 _v)) : (e7742 _v) := by
  have p10896 := n10896 _v _q 
  have p11414 := n11414 _v _q h474
  have p20651 := n20651 _v _q 
  exact FloorCertificate.node_20654 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p10896 p11414 p20651
theorem n20655 (_v : Vars) (_q : Query _v) (h474 : (e474 _v)) : (e7754 _v) := by
  have p14942 := n14942 _v _q 
  have p20654 := n20654 _v _q h474
  simp only [e2132, e7742, e7747, e7749, e7751, e7752, e7753, e7754, e11001] at *
  tauto
theorem n20656 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) : (e7742 _v) := by
  have p20651 := n20651 _v _q 
  have p10893 := n10893 _v _q 
  have p8464 := n8464 _v _q h2351
  exact FloorCertificate.node_20656 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p20651 p10893 p8464
theorem n20657 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) : (e7754 _v) := by
  have p14942 := n14942 _v _q 
  have p20656 := n20656 _v _q h2351
  simp only [e2132, e7742, e7747, e7749, e7751, e7752, e7753, e7754, e11001] at *
  tauto
theorem n20658 (_v : Vars) (_q : Query _v) (h474 : (e474 _v)) : (e4101 _v) := by
  have p14929 := n14929 _v _q 
  have p15895 := n15895 _v _q h474
  simp only [e4101, e4102, e4106, e4107, e4108, e4109, e4952] at *
  tauto
theorem n20659 (_v : Vars) (_q : Query _v) (h474 : (e474 _v)) : (e7749 _v) := by
  have p14941 := n14941 _v _q 
  have p20655 := n20655 _v _q h474
  simp only [e7747, e7749, e7751, e7752, e7753, e7754, e8446] at *
  tauto
theorem n20660 (_v : Vars) (_q : Query _v) (h474 : (e474 _v)) : (e4459 _v) := by
  have p16784 := n16784 _v _q 
  have p20659 := n20659 _v _q h474
  simp only [e4459, e7749, e7752, e16783] at *
  tauto
theorem n20661 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h474 : (e474 _v)) (h3133 : (e3133 _v)) (h3158 : (e3158 _v)) (h4161 : (e4161 _v)) (h4439 : (e4439 _v)) (h4567 : (e4567 _v)) (h4679 : (e4679 _v)) : (e7489 _v) := by
  have p4016 := n4016 _v _q 
  have p258 := n258 _v _q 
  have p20653 := n20653 _v _q 
  have p5257 := n5257 _v _q 
  have p4999 := n4999 _v _q h91
  have p17087 := n17087 _v _q 
  have p16992 := n16992 _v _q 
  have p15133 := n15133 _v _q h474
  have p17081 := n17081 _v _q h4161
  have p17091 := n17091 _v _q 
  have p17093 := n17093 _v _q 
  have p15886 := n15886 _v _q h474
  have p17141 := n17141 _v _q 
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p17102 := n17102 _v _q 
  have p17100 := n17100 _v _q 
  have p15889 := n15889 _v _q h474
  have p19610 := n19610 _v _q 
  have p16885 := n16885 _v _q h3158
  have p17122 := n17122 _v _q 
  have p17096 := n17096 _v _q 
  have p15891 := n15891 _v _q h474
  have p17075 := n17075 _v _q h4439
  have p17758 := n17758 _v _q 
  have p15894 := n15894 _v _q h474
  have p17062 := n17062 _v _q h3133
  have p20658 := n20658 _v _q h474
  have p17070 := n17070 _v _q h4679
  have p17143 := n17143 _v _q h4567
  have p17115 := n17115 _v _q 
  have p17120 := n17120 _v _q 
  have p17111 := n17111 _v _q 
  have p17124 := n17124 _v _q 
  have p17050 := n17050 _v _q 
  have p16778 := n16778 _v _q 
  have p17113 := n17113 _v _q 
  have p17117 := n17117 _v _q 
  have p20467 := n20467 _v _q 
  have p20660 := n20660 _v _q h474
  have p15898 := n15898 _v _q h474
  have p17104 := n17104 _v _q 
  have p17874 := n17874 _v _q 
  have p17127 := n17127 _v _q 
  have p15900 := n15900 _v _q h474
  have p20274 := n20274 _v _q 
  have p20470 := n20470 _v _q 
  have p17133 := n17133 _v _q 
  have p17089 := n17089 _v _q 
  have p19665 := n19665 _v _q 
  have p20426 := n20426 _v _q 
  have p17055 := n17055 _v _q 
  have p17108 := n17108 _v _q 
  have p20461 := n20461 _v _q 
  have p20126 := n20126 _v _q 
  have p17131 := n17131 _v _q 
  have p17110 := n17110 _v _q 
  have p17053 := n17053 _v _q 
  have p15902 := n15902 _v _q h474
  have p20096 := n20096 _v _q 
  have p17294 := n17294 _v _q 
  have p16943 := n16943 _v _q 
  have p17058 := n17058 _v _q 
  have p17064 := n17064 _v _q 
  have p17067 := n17067 _v _q 
  have p17069 := n17069 _v _q 
  have p17072 := n17072 _v _q 
  have p17136 := n17136 _v _q 
  have p17078 := n17078 _v _q 
  have p17080 := n17080 _v _q 
  have p17083 := n17083 _v _q 
  have p17074 := n17074 _v _q 
  have p13951 := n13951 _v _q 
  have p11414 := n11414 _v _q h474
  have p5391 := n5391 _v _q 
  exact FloorCertificate.node_20661 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2902 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) p4016 p258 p20653 p5257 p4999 p17087 p16992 p15133 p17081 p17091 p17093 p15886 p17141 p17098 p17106 p17102 p17100 p15889 p19610 p16885 p17122 p17096 p15891 p17075 p17758 p15894 p17062 p20658 p17070 p17143 p17115 p17120 p17111 p17124 p17050 p16778 p17113 p17117 p20467 p20660 p15898 p17104 p17874 p17127 p15900 p20274 p20470 p17133 p17089 p19665 p20426 p17055 p17108 p20461 p20126 p17131 p17110 p17053 p15902 p20096 p17294 p16943 p17058 p17064 p17067 p17069 p17072 p17136 p17078 p17080 p17083 p17074 p13951 p11414 p5391
theorem n20662 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) : (e7749 _v) := by
  have p14941 := n14941 _v _q 
  have p20657 := n20657 _v _q h2351
  simp only [e7747, e7749, e7751, e7752, e7753, e7754, e8446] at *
  tauto
theorem n20663 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) : (e4459 _v) := by
  have p16784 := n16784 _v _q 
  have p20662 := n20662 _v _q h2351
  simp only [e4459, e7749, e7752, e16783] at *
  tauto
theorem n20665 (_v : Vars) (_q : Query _v)  : (e20664 _v) := by
  by_contra hc
  change ¬ ((¬ (e91 _v)) ∨ (¬ (e4161 _v)) ∨ (¬ (e3158 _v)) ∨ (¬ (e4439 _v)) ∨ (¬ (e3133 _v)) ∨ (¬ (e4679 _v)) ∨ (¬ (e4567 _v)) ∨ (¬ (e474 _v))) at hc
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h474 : (e474 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))))
  have h3133 : (e3133 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h3158 : (e3158 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4161 : (e4161 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h4439 : (e4439 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4567 : (e4567 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h4679 : (e4679 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have p20661 := n20661 _v _q h91 h474 h3133 h3158 h4161 h4439 h4567 h4679
  exact p20661
theorem n20666 (_v : Vars) (_q : Query _v) (h474 : (e474 _v)) (h3133 : (e3133 _v)) (h3158 : (e3158 _v)) (h4161 : (e4161 _v)) (h4439 : (e4439 _v)) (h4567 : (e4567 _v)) (h4679 : (e4679 _v)) : (e95 _v) := by
  have p20665 := n20665 _v _q 
  have p11414 := n11414 _v _q h474
  have p16885 := n16885 _v _q h3158
  have p17075 := n17075 _v _q h4439
  have p17062 := n17062 _v _q h3133
  have p17070 := n17070 _v _q h4679
  have p17143 := n17143 _v _q h4567
  have p17081 := n17081 _v _q h4161
  simp only [e91, e95, e474, e3133, e3138, e3158, e3159, e4161, e4166, e4439, e4444, e4567, e4572, e4679, e4684, e5392, e20664] at *
  tauto
theorem n20667 (_v : Vars) (_q : Query _v) (h474 : (e474 _v)) (h3133 : (e3133 _v)) (h3158 : (e3158 _v)) (h4161 : (e4161 _v)) (h4439 : (e4439 _v)) (h4567 : (e4567 _v)) (h4679 : (e4679 _v)) : (e5134 _v) := by
  have p16235 := n16235 _v _q 
  have p20666 := n20666 _v _q h474 h3133 h3158 h4161 h4439 h4567 h4679
  simp only [e89, e91, e94, e95, e5134, e7983] at *
  tauto
theorem n20668 (_v : Vars) (_q : Query _v) (h474 : (e474 _v)) (h3133 : (e3133 _v)) (h3158 : (e3158 _v)) (h4161 : (e4161 _v)) (h4439 : (e4439 _v)) (h4567 : (e4567 _v)) (h4679 : (e4679 _v)) : (e5138 _v) := by
  have p14729 := n14729 _v _q 
  have p20667 := n20667 _v _q h474 h3133 h3158 h4161 h4439 h4567 h4679
  simp only [e79, e89, e91, e94, e95, e5134, e5135, e5138, e5140] at *
  tauto
theorem n20669 (_v : Vars) (_q : Query _v) (h474 : (e474 _v)) (h3133 : (e3133 _v)) (h3158 : (e3158 _v)) (h4161 : (e4161 _v)) (h4439 : (e4439 _v)) (h4567 : (e4567 _v)) (h4679 : (e4679 _v)) : (e5150 _v) := by
  have p15115 := n15115 _v _q 
  have p20668 := n20668 _v _q h474 h3133 h3158 h4161 h4439 h4567 h4679
  simp only [e79, e5138, e5143, e5145, e5147, e5148, e5149, e5150, e8647] at *
  tauto
theorem n20670 (_v : Vars) (_q : Query _v) (h474 : (e474 _v)) (h3133 : (e3133 _v)) (h3158 : (e3158 _v)) (h4161 : (e4161 _v)) (h4439 : (e4439 _v)) (h4567 : (e4567 _v)) (h4679 : (e4679 _v)) : (e5145 _v) := by
  have p15925 := n15925 _v _q 
  have p20669 := n20669 _v _q h474 h3133 h3158 h4161 h4439 h4567 h4679
  simp only [e5143, e5145, e5147, e5148, e5149, e5150, e5152] at *
  tauto
theorem n20671 (_v : Vars) (_q : Query _v) (h474 : (e474 _v)) (h3133 : (e3133 _v)) (h3158 : (e3158 _v)) (h4161 : (e4161 _v)) (h4439 : (e4439 _v)) (h4567 : (e4567 _v)) (h4679 : (e4679 _v)) : (e7489 _v) := by
  have p20668 := n20668 _v _q h474 h3133 h3158 h4161 h4439 h4567 h4679
  have p20670 := n20670 _v _q h474 h3133 h3158 h4161 h4439 h4567 h4679
  have p17009 := n17009 _v _q 
  have p17080 := n17080 _v _q 
  have p20659 := n20659 _v _q h474
  have p17083 := n17083 _v _q 
  have p17074 := n17074 _v _q 
  have p13951 := n13951 _v _q 
  have p4016 := n4016 _v _q 
  have p17078 := n17078 _v _q 
  have p20653 := n20653 _v _q 
  have p17087 := n17087 _v _q 
  have p16992 := n16992 _v _q 
  have p15133 := n15133 _v _q h474
  have p17081 := n17081 _v _q h4161
  have p17091 := n17091 _v _q 
  have p17093 := n17093 _v _q 
  have p15886 := n15886 _v _q h474
  have p17141 := n17141 _v _q 
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p17102 := n17102 _v _q 
  have p17100 := n17100 _v _q 
  have p15889 := n15889 _v _q h474
  have p19610 := n19610 _v _q 
  have p16885 := n16885 _v _q h3158
  have p17122 := n17122 _v _q 
  have p17096 := n17096 _v _q 
  have p15891 := n15891 _v _q h474
  have p17075 := n17075 _v _q h4439
  have p17758 := n17758 _v _q 
  have p15894 := n15894 _v _q h474
  have p17062 := n17062 _v _q h3133
  have p20658 := n20658 _v _q h474
  have p17070 := n17070 _v _q h4679
  have p17143 := n17143 _v _q h4567
  have p17115 := n17115 _v _q 
  have p17120 := n17120 _v _q 
  have p17111 := n17111 _v _q 
  have p17124 := n17124 _v _q 
  have p17050 := n17050 _v _q 
  have p16778 := n16778 _v _q 
  have p17113 := n17113 _v _q 
  have p17117 := n17117 _v _q 
  have p20467 := n20467 _v _q 
  have p15898 := n15898 _v _q h474
  have p17104 := n17104 _v _q 
  have p17874 := n17874 _v _q 
  have p17127 := n17127 _v _q 
  have p15900 := n15900 _v _q h474
  have p20274 := n20274 _v _q 
  have p20470 := n20470 _v _q 
  have p17133 := n17133 _v _q 
  have p17089 := n17089 _v _q 
  have p19665 := n19665 _v _q 
  have p20426 := n20426 _v _q 
  have p17055 := n17055 _v _q 
  have p17108 := n17108 _v _q 
  have p20461 := n20461 _v _q 
  have p20126 := n20126 _v _q 
  have p17131 := n17131 _v _q 
  have p17110 := n17110 _v _q 
  have p17053 := n17053 _v _q 
  have p15902 := n15902 _v _q h474
  have p20096 := n20096 _v _q 
  have p17294 := n17294 _v _q 
  have p16943 := n16943 _v _q 
  have p17058 := n17058 _v _q 
  have p17064 := n17064 _v _q 
  have p17067 := n17067 _v _q 
  have p17069 := n17069 _v _q 
  have p17072 := n17072 _v _q 
  have p17136 := n17136 _v _q 
  have p20651 := n20651 _v _q 
  exact FloorCertificate.node_20671 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2902 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e4215 _v) p20668 p20670 p17009 p17080 p20659 p17083 p17074 p13951 p4016 p17078 p20653 p17087 p16992 p15133 p17081 p17091 p17093 p15886 p17141 p17098 p17106 p17102 p17100 p15889 p19610 p16885 p17122 p17096 p15891 p17075 p17758 p15894 p17062 p20658 p17070 p17143 p17115 p17120 p17111 p17124 p17050 p16778 p17113 p17117 p20467 p15898 p17104 p17874 p17127 p15900 p20274 p20470 p17133 p17089 p19665 p20426 p17055 p17108 p20461 p20126 p17131 p17110 p17053 p15902 p20096 p17294 p16943 p17058 p17064 p17067 p17069 p17072 p17136 p20651
theorem n20673 (_v : Vars) (_q : Query _v)  : (e20672 _v) := by
  by_contra hc
  change ¬ ((¬ (e474 _v)) ∨ (¬ (e4161 _v)) ∨ (¬ (e3158 _v)) ∨ (¬ (e4439 _v)) ∨ (¬ (e3133 _v)) ∨ (¬ (e4679 _v)) ∨ (¬ (e4567 _v))) at hc
  have h474 : (e474 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h3133 : (e3133 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h3158 : (e3158 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4161 : (e4161 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h4439 : (e4439 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4567 : (e4567 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn)))))))
  have h4679 : (e4679 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have p20671 := n20671 _v _q h474 h3133 h3158 h4161 h4439 h4567 h4679
  exact p20671
theorem n20674 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) : (e5392 _v) := by
  have p20673 := n20673 _v _q 
  have p15793 := n15793 _v _q h2351
  have p15791 := n15791 _v _q h2351
  have p15786 := n15786 _v _q h2351
  have p15783 := n15783 _v _q h2351
  have p15905 := n15905 _v _q h2351
  have p20319 := n20319 _v _q h2351
  simp only [e474, e3133, e3138, e3158, e3159, e4161, e4166, e4439, e4444, e4567, e4572, e4679, e4684, e5392, e20672] at *
  tauto
theorem n20675 (_v : Vars) (_q : Query _v) (h3133 : (e3133 _v)) (h3158 : (e3158 _v)) (h4161 : (e4161 _v)) (h4439 : (e4439 _v)) (h4567 : (e4567 _v)) (h4679 : (e4679 _v)) : (e5392 _v) := by
  have p20673 := n20673 _v _q 
  have p17081 := n17081 _v _q h4161
  have p16885 := n16885 _v _q h3158
  have p17075 := n17075 _v _q h4439
  have p17062 := n17062 _v _q h3133
  have p17070 := n17070 _v _q h4679
  have p17143 := n17143 _v _q h4567
  simp only [e474, e3133, e3138, e3158, e3159, e4161, e4166, e4439, e4444, e4567, e4572, e4679, e4684, e5392, e20672] at *
  tauto
theorem n20676 (_v : Vars) (_q : Query _v) (h3133 : (e3133 _v)) (h3158 : (e3158 _v)) (h4161 : (e4161 _v)) (h4439 : (e4439 _v)) (h4567 : (e4567 _v)) (h4679 : (e4679 _v)) : (e5403 _v) := by
  have p14577 := n14577 _v _q 
  have p20675 := n20675 _v _q h3133 h3158 h4161 h4439 h4567 h4679
  simp only [e474, e488, e490, e493, e494, e5392, e5402, e5403, e5406] at *
  tauto
theorem n20677 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) : (e5403 _v) := by
  have p14577 := n14577 _v _q 
  have p20674 := n20674 _v _q h2351
  simp only [e474, e488, e490, e493, e494, e5392, e5402, e5403, e5406] at *
  tauto
theorem n20678 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) : (e488 _v) := by
  have p15090 := n15090 _v _q 
  have p20677 := n20677 _v _q h2351
  simp only [e488, e490, e493, e494, e5402, e5403, e7821] at *
  tauto
theorem n20679 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) : (e2364 _v) := by
  have p10893 := n10893 _v _q 
  have p8464 := n8464 _v _q h2351
  have p20397 := n20397 _v _q 
  have p20651 := n20651 _v _q 
  have p20674 := n20674 _v _q h2351
  exact FloorCertificate.node_20679 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p10893 p8464 p20397 p20651 p20674
theorem n20680 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) : (e4661 _v) := by
  have p14686 := n14686 _v _q 
  have p20679 := n20679 _v _q h2351
  simp only [e2364, e4653, e4654, e4658, e4659, e4660, e4661, e6583, e8163] at *
  tauto
theorem n20681 (_v : Vars) (_q : Query _v) (h3133 : (e3133 _v)) (h3158 : (e3158 _v)) (h4161 : (e4161 _v)) (h4439 : (e4439 _v)) (h4567 : (e4567 _v)) (h4679 : (e4679 _v)) : (e488 _v) := by
  have p15090 := n15090 _v _q 
  have p20676 := n20676 _v _q h3133 h3158 h4161 h4439 h4567 h4679
  simp only [e488, e490, e493, e494, e5402, e5403, e7821] at *
  tauto
theorem n20682 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) : (e4653 _v) := by
  have p15168 := n15168 _v _q 
  have p20680 := n20680 _v _q h2351
  simp only [e4653, e4654, e4658, e4659, e4660, e4661, e4939] at *
  tauto
theorem n20683 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h2351 : (e2351 _v)) (h4813 : (e4813 _v)) (h6600 : (e6600 _v)) (h8310 : (e8310 _v)) : (e7489 _v) := by
  have p4016 := n4016 _v _q 
  have p10893 := n10893 _v _q 
  have p13951 := n13951 _v _q 
  have p17080 := n17080 _v _q 
  have p8464 := n8464 _v _q h2351
  have p17083 := n17083 _v _q 
  have p17074 := n17074 _v _q 
  have p8439 := n8439 _v _q h6600
  have p20678 := n20678 _v _q h2351
  have p20663 := n20663 _v _q h2351
  have p17078 := n17078 _v _q 
  have p20653 := n20653 _v _q 
  have p4999 := n4999 _v _q h91
  have p17087 := n17087 _v _q 
  have p16992 := n16992 _v _q 
  have p15248 := n15248 _v _q h8310
  have p15793 := n15793 _v _q h2351
  have p17091 := n17091 _v _q 
  have p17093 := n17093 _v _q 
  have p20682 := n20682 _v _q h2351
  have p17141 := n17141 _v _q 
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p17102 := n17102 _v _q 
  have p17100 := n17100 _v _q 
  have p15907 := n15907 _v _q h6600
  have p19610 := n19610 _v _q 
  have p15791 := n15791 _v _q h2351
  have p17122 := n17122 _v _q 
  have p17096 := n17096 _v _q 
  have p15909 := n15909 _v _q h2351
  have p15786 := n15786 _v _q h2351
  have p17758 := n17758 _v _q 
  have p17953 := n17953 _v _q 
  have p15783 := n15783 _v _q h2351
  have p15911 := n15911 _v _q h2351
  have p15905 := n15905 _v _q h2351
  have p20319 := n20319 _v _q h2351
  have p17115 := n17115 _v _q 
  have p17120 := n17120 _v _q 
  have p17111 := n17111 _v _q 
  have p17124 := n17124 _v _q 
  have p17050 := n17050 _v _q 
  have p16778 := n16778 _v _q 
  have p17113 := n17113 _v _q 
  have p17117 := n17117 _v _q 
  have p20467 := n20467 _v _q 
  have p17453 := n17453 _v _q h8310
  have p17104 := n17104 _v _q 
  have p17874 := n17874 _v _q 
  have p17127 := n17127 _v _q 
  have p15914 := n15914 _v _q h2351
  have p20274 := n20274 _v _q 
  have p20470 := n20470 _v _q 
  have p17133 := n17133 _v _q 
  have p17089 := n17089 _v _q 
  have p19665 := n19665 _v _q 
  have p20426 := n20426 _v _q 
  have p17055 := n17055 _v _q 
  have p17108 := n17108 _v _q 
  have p20461 := n20461 _v _q 
  have p20126 := n20126 _v _q 
  have p17131 := n17131 _v _q 
  have p17110 := n17110 _v _q 
  have p17053 := n17053 _v _q 
  have p15917 := n15917 _v _q h2351
  have p20096 := n20096 _v _q 
  have p17294 := n17294 _v _q 
  have p16943 := n16943 _v _q 
  have p17058 := n17058 _v _q 
  have p17064 := n17064 _v _q 
  have p17067 := n17067 _v _q 
  have p17069 := n17069 _v _q 
  have p17072 := n17072 _v _q 
  have p17136 := n17136 _v _q 
  have p16643 := n16643 _v _q h6600
  have p17147 := n17147 _v _q 
  have p4983 := n4983 _v _q h4813
  exact FloorCertificate.node_20683 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2883 _v) (e2902 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e4541 _v) (e4808 _v) p4016 p10893 p13951 p17080 p8464 p17083 p17074 p8439 p20678 p20663 p17078 p20653 p4999 p17087 p16992 p15248 p15793 p17091 p17093 p20682 p17141 p17098 p17106 p17102 p17100 p15907 p19610 p15791 p17122 p17096 p15909 p15786 p17758 p17953 p15783 p15911 p15905 p20319 p17115 p17120 p17111 p17124 p17050 p16778 p17113 p17117 p20467 p17453 p17104 p17874 p17127 p15914 p20274 p20470 p17133 p17089 p19665 p20426 p17055 p17108 p20461 p20126 p17131 p17110 p17053 p15917 p20096 p17294 p16943 p17058 p17064 p17067 p17069 p17072 p17136 p16643 p17147 p4983
theorem n20684 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3133 : (e3133 _v)) (h3158 : (e3158 _v)) (h4101 : (e4101 _v)) (h4161 : (e4161 _v)) (h4264 : (e4264 _v)) (h4306 : (e4306 _v)) (h4439 : (e4439 _v)) (h4567 : (e4567 _v)) (h4653 : (e4653 _v)) (h4679 : (e4679 _v)) (h4813 : (e4813 _v)) (h5223 : (e5223 _v)) (h6600 : (e6600 _v)) (h7749 : (e7749 _v)) : (e5148 _v) := by
  have p17136 := n17136 _v _q 
  have p17009 := n17009 _v _q 
  have p17080 := n17080 _v _q 
  have p16269 := n16269 _v _q h7749
  have p17083 := n17083 _v _q 
  have p17074 := n17074 _v _q 
  have p17072 := n17072 _v _q 
  have p13951 := n13951 _v _q 
  have p17078 := n17078 _v _q 
  have p20653 := n20653 _v _q 
  have p17087 := n17087 _v _q 
  have p16992 := n16992 _v _q 
  have p15921 := n15921 _v _q h5223
  have p17081 := n17081 _v _q h4161
  have p17091 := n17091 _v _q 
  have p17093 := n17093 _v _q 
  have p17060 := n17060 _v _q h4653
  have p17141 := n17141 _v _q 
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p17102 := n17102 _v _q 
  have p17100 := n17100 _v _q 
  have p17147 := n17147 _v _q 
  have p19610 := n19610 _v _q 
  have p16885 := n16885 _v _q h3158
  have p17122 := n17122 _v _q 
  have p17096 := n17096 _v _q 
  have p17118 := n17118 _v _q h4264
  have p17075 := n17075 _v _q h4439
  have p17758 := n17758 _v _q 
  have p20397 := n20397 _v _q 
  have p17062 := n17062 _v _q h3133
  have p17065 := n17065 _v _q h4101
  have p17070 := n17070 _v _q h4679
  have p17143 := n17143 _v _q h4567
  have p17115 := n17115 _v _q 
  have p17120 := n17120 _v _q 
  have p17111 := n17111 _v _q 
  have p17124 := n17124 _v _q 
  have p17050 := n17050 _v _q 
  have p16778 := n16778 _v _q 
  have p17113 := n17113 _v _q 
  have p17117 := n17117 _v _q 
  have p20467 := n20467 _v _q 
  have p8439 := n8439 _v _q h6600
  have p17104 := n17104 _v _q 
  have p17874 := n17874 _v _q 
  have p17127 := n17127 _v _q 
  have p17138 := n17138 _v _q h4306
  have p20274 := n20274 _v _q 
  have p20470 := n20470 _v _q 
  have p17133 := n17133 _v _q 
  have p17089 := n17089 _v _q 
  have p19665 := n19665 _v _q 
  have p20426 := n20426 _v _q 
  have p17055 := n17055 _v _q 
  have p17108 := n17108 _v _q 
  have p20461 := n20461 _v _q 
  have p20126 := n20126 _v _q 
  have p17131 := n17131 _v _q 
  have p17110 := n17110 _v _q 
  have p17053 := n17053 _v _q 
  have p16729 := n16729 _v _q h51
  have p20096 := n20096 _v _q 
  have p17294 := n17294 _v _q 
  have p16943 := n16943 _v _q 
  have p17058 := n17058 _v _q 
  have p17064 := n17064 _v _q 
  have p17067 := n17067 _v _q 
  have p17069 := n17069 _v _q 
  have p15907 := n15907 _v _q h6600
  have p20681 := n20681 _v _q h3133 h3158 h4161 h4439 h4567 h4679
  have p15924 := n15924 _v _q h5223
  have p16643 := n16643 _v _q h6600
  have p4983 := n4983 _v _q h4813
  have p17953 := n17953 _v _q 
  have p11520 := n11520 _v _q h5223
  have p5257 := n5257 _v _q 
  have p5255 := n5255 _v _q 
  exact FloorCertificate.node_20684 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2883 _v) (e2902 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e4215 _v) (e4541 _v) (e4808 _v) p17136 p17009 p17080 p16269 p17083 p17074 p17072 p13951 p17078 p20653 p17087 p16992 p15921 p17081 p17091 p17093 p17060 p17141 p17098 p17106 p17102 p17100 p17147 p19610 p16885 p17122 p17096 p17118 p17075 p17758 p20397 p17062 p17065 p17070 p17143 p17115 p17120 p17111 p17124 p17050 p16778 p17113 p17117 p20467 p8439 p17104 p17874 p17127 p17138 p20274 p20470 p17133 p17089 p19665 p20426 p17055 p17108 p20461 p20126 p17131 p17110 p17053 p16729 p20096 p17294 p16943 p17058 p17064 p17067 p17069 p15907 p20681 p15924 p16643 p4983 p17953 p11520 p5257 p5255
theorem n20686 (_v : Vars) (_q : Query _v)  : (e20685 _v) := by
  by_contra hc
  change ¬ ((e2529 _v) ∨ (¬ (e2351 _v)) ∨ (e2402 _v) ∨ (¬ (e91 _v)) ∨ (¬ (e4813 _v))) at hc
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h2351 : (e2351 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr hn)))))
  have h6600 : (e6600 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h8310 : (e8310 _v) := (fun hn => hc (Or.inl hn))
  have p20683 := n20683 _v _q h91 h2351 h4813 h6600 h8310
  exact p20683
theorem n20687 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h2351 : (e2351 _v)) (h4813 : (e4813 _v)) (h6600 : (e6600 _v)) : (e2529 _v) := by
  have p20686 := n20686 _v _q 
  have p4999 := n4999 _v _q h91
  have p8439 := n8439 _v _q h6600
  have p8464 := n8464 _v _q h2351
  have p4983 := n4983 _v _q h4813
  simp only [e91, e95, e2351, e2402, e2529, e4813, e4814, e6575, e6600, e20685] at *
  tauto
theorem n20688 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3133 : (e3133 _v)) (h3158 : (e3158 _v)) (h4101 : (e4101 _v)) (h4161 : (e4161 _v)) (h4264 : (e4264 _v)) (h4306 : (e4306 _v)) (h4439 : (e4439 _v)) (h4567 : (e4567 _v)) (h4653 : (e4653 _v)) (h4679 : (e4679 _v)) (h4813 : (e4813 _v)) (h5223 : (e5223 _v)) (h6600 : (e6600 _v)) (h7749 : (e7749 _v)) : (e5149 _v) := by
  have p15925 := n15925 _v _q 
  have p20684 := n20684 _v _q h51 h3133 h3158 h4101 h4161 h4264 h4306 h4439 h4567 h4653 h4679 h4813 h5223 h6600 h7749
  simp only [e5143, e5145, e5147, e5148, e5149, e5152] at *
  tauto
theorem n20689 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h2351 : (e2351 _v)) (h4813 : (e4813 _v)) (h6600 : (e6600 _v)) : (e196 _v) := by
  have p8552 := n8552 _v _q 
  have p20687 := n20687 _v _q h91 h2351 h4813 h6600
  simp only [e196, e2529, e8310, e8551] at *
  tauto
theorem n20690 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h2351 : (e2351 _v)) (h4813 : (e4813 _v)) (h6600 : (e6600 _v)) : (e5203 _v) := by
  have p14730 := n14730 _v _q 
  have p20689 := n20689 _v _q h91 h2351 h4813 h6600
  simp only [e191, e192, e193, e194, e196, e5193, e5195, e5203, e5206] at *
  tauto
theorem n20691 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h2351 : (e2351 _v)) (h4813 : (e4813 _v)) (h6600 : (e6600 _v)) : (e191 _v) := by
  have p16442 := n16442 _v _q 
  have p20690 := n20690 _v _q h91 h2351 h4813 h6600
  simp only [e191, e192, e193, e194, e5193, e5194, e5203] at *
  tauto
theorem n20692 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h2351 : (e2351 _v)) (h4813 : (e4813 _v)) (h6600 : (e6600 _v)) : (e8307 _v) := by
  have p14906 := n14906 _v _q 
  have p20687 := n20687 _v _q h91 h2351 h4813 h6600
  simp only [e2529, e4836, e4837, e4838, e4839, e8301, e8307, e8310, e8312] at *
  tauto
theorem n20693 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h2351 : (e2351 _v)) (h4813 : (e4813 _v)) (h6600 : (e6600 _v)) : (e4838 _v) := by
  have p16285 := n16285 _v _q 
  have p20692 := n20692 _v _q h91 h2351 h4813 h6600
  simp only [e4836, e4837, e4838, e4839, e8301, e8302, e8307] at *
  tauto
theorem n20694 (_v : Vars) (_q : Query _v) (h5223 : (e5223 _v)) : (e5138 _v) := by
  have p11520 := n11520 _v _q h5223
  have p20397 := n20397 _v _q 
  have p5257 := n5257 _v _q 
  exact FloorCertificate.node_20694 (e2 _v) (e7 _v) (e9 _v) (e45 _v) (e110 _v) p11520 p20397 p5257
theorem n20695 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3133 : (e3133 _v)) (h3158 : (e3158 _v)) (h4101 : (e4101 _v)) (h4161 : (e4161 _v)) (h4264 : (e4264 _v)) (h4306 : (e4306 _v)) (h4439 : (e4439 _v)) (h4567 : (e4567 _v)) (h4653 : (e4653 _v)) (h4679 : (e4679 _v)) (h4813 : (e4813 _v)) (h5223 : (e5223 _v)) (h6600 : (e6600 _v)) (h7749 : (e7749 _v)) : (e7489 _v) := by
  have p15115 := n15115 _v _q 
  have p20688 := n20688 _v _q h51 h3133 h3158 h4101 h4161 h4264 h4306 h4439 h4567 h4653 h4679 h4813 h5223 h6600 h7749
  have p20694 := n20694 _v _q h5223
  simp only [e79, e5138, e5143, e5145, e5147, e5148, e5149, e5150, e8647] at *
  tauto
theorem n20697 (_v : Vars) (_q : Query _v)  : (e20696 _v) := by
  by_contra hc
  change ¬ ((e214 _v) ∨ (¬ (e7749 _v)) ∨ (¬ (e4161 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e3158 _v)) ∨ (¬ (e4264 _v)) ∨ (¬ (e4439 _v)) ∨ (¬ (e3133 _v)) ∨ (¬ (e4101 _v)) ∨ (¬ (e4679 _v)) ∨ (¬ (e4567 _v)) ∨ (e2402 _v) ∨ (¬ (e4306 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4813 _v))) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h3133 : (e3133 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h3158 : (e3158 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4101 : (e4101 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h4161 : (e4161 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4264 : (e4264 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h4439 : (e4439 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h4567 : (e4567 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4679 : (e4679 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn)))))))))))))))
  have h5223 : (e5223 _v) := (fun hn => hc (Or.inl hn))
  have h6600 : (e6600 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h7749 : (e7749 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have p20695 := n20695 _v _q h51 h3133 h3158 h4101 h4161 h4264 h4306 h4439 h4567 h4653 h4679 h4813 h5223 h6600 h7749
  exact p20695
theorem n20698 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h4813 : (e4813 _v)) (h6600 : (e6600 _v)) : (e214 _v) := by
  have p20697 := n20697 _v _q 
  have p4983 := n4983 _v _q h4813
  have p15793 := n15793 _v _q h2351
  have p20682 := n20682 _v _q h2351
  have p15791 := n15791 _v _q h2351
  have p15909 := n15909 _v _q h2351
  have p15786 := n15786 _v _q h2351
  have p15783 := n15783 _v _q h2351
  have p15911 := n15911 _v _q h2351
  have p15905 := n15905 _v _q h2351
  have p20319 := n20319 _v _q h2351
  have p8439 := n8439 _v _q h6600
  have p15914 := n15914 _v _q h2351
  have p15917 := n15917 _v _q h2351
  have p20662 := n20662 _v _q h2351
  simp only [e51, e57, e214, e2402, e3133, e3138, e3158, e3159, e4101, e4106, e4161, e4166, e4264, e4269, e4306, e4311, e4439, e4444, e4567, e4572, e4653, e4658, e4679, e4684, e4813, e4814, e6600, e7749, e7752, e20696] at *
  tauto
theorem n20699 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h4813 : (e4813 _v)) (h6600 : (e6600 _v)) : (e5232 _v) := by
  have p14731 := n14731 _v _q 
  have p20698 := n20698 _v _q h2351 h4813 h6600
  simp only [e214, e225, e227, e230, e231, e5223, e5231, e5232, e5235] at *
  tauto
theorem n20700 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h4813 : (e4813 _v)) (h6600 : (e6600 _v)) : (e225 _v) := by
  have p16653 := n16653 _v _q 
  have p20699 := n20699 _v _q h2351 h4813 h6600
  simp only [e225, e227, e230, e231, e5231, e5232, e5253] at *
  tauto
theorem n20701 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h2351 : (e2351 _v)) (h2475 : (e2475 _v)) (h4813 : (e4813 _v)) (h6600 : (e6600 _v)) : (e7489 _v) := by
  have p20691 := n20691 _v _q h91 h2351 h4813 h6600
  have p20687 := n20687 _v _q h91 h2351 h4813 h6600
  have p8457 := n8457 _v _q h2475
  have p10893 := n10893 _v _q 
  have p16338 := n16338 _v _q h2475
  have p17147 := n17147 _v _q 
  have p20693 := n20693 _v _q h91 h2351 h4813 h6600
  have p4983 := n4983 _v _q h4813
  have p16643 := n16643 _v _q h6600
  have p13951 := n13951 _v _q 
  have p17080 := n17080 _v _q 
  have p8464 := n8464 _v _q h2351
  have p17083 := n17083 _v _q 
  have p17074 := n17074 _v _q 
  have p8439 := n8439 _v _q h6600
  have p20678 := n20678 _v _q h2351
  have p20663 := n20663 _v _q h2351
  have p17078 := n17078 _v _q 
  have p20653 := n20653 _v _q 
  have p4999 := n4999 _v _q h91
  have p17087 := n17087 _v _q 
  have p17136 := n17136 _v _q 
  have p15793 := n15793 _v _q h2351
  have p17091 := n17091 _v _q 
  have p17093 := n17093 _v _q 
  have p20682 := n20682 _v _q h2351
  have p17141 := n17141 _v _q 
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p17102 := n17102 _v _q 
  have p17100 := n17100 _v _q 
  have p15907 := n15907 _v _q h6600
  have p19610 := n19610 _v _q 
  have p15791 := n15791 _v _q h2351
  have p17122 := n17122 _v _q 
  have p17096 := n17096 _v _q 
  have p15909 := n15909 _v _q h2351
  have p15786 := n15786 _v _q h2351
  have p17758 := n17758 _v _q 
  have p15783 := n15783 _v _q h2351
  have p15911 := n15911 _v _q h2351
  have p15905 := n15905 _v _q h2351
  have p20319 := n20319 _v _q h2351
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
  have p15914 := n15914 _v _q h2351
  have p20274 := n20274 _v _q 
  have p20470 := n20470 _v _q 
  have p17133 := n17133 _v _q 
  have p17089 := n17089 _v _q 
  have p19665 := n19665 _v _q 
  have p20426 := n20426 _v _q 
  have p17055 := n17055 _v _q 
  have p17108 := n17108 _v _q 
  have p20461 := n20461 _v _q 
  have p20126 := n20126 _v _q 
  have p17131 := n17131 _v _q 
  have p17110 := n17110 _v _q 
  have p17053 := n17053 _v _q 
  have p15917 := n15917 _v _q h2351
  have p20096 := n20096 _v _q 
  have p17294 := n17294 _v _q 
  have p16943 := n16943 _v _q 
  have p17058 := n17058 _v _q 
  have p17064 := n17064 _v _q 
  have p17067 := n17067 _v _q 
  have p17069 := n17069 _v _q 
  have p17072 := n17072 _v _q 
  have p20700 := n20700 _v _q h2351 h4813 h6600
  have p5255 := n5255 _v _q 
  exact FloorCertificate.node_20701 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2883 _v) (e2902 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e4541 _v) (e4808 _v) p20691 p20687 p8457 p10893 p16338 p17147 p20693 p4983 p16643 p13951 p17080 p8464 p17083 p17074 p8439 p20678 p20663 p17078 p20653 p4999 p17087 p17136 p15793 p17091 p17093 p20682 p17141 p17098 p17106 p17102 p17100 p15907 p19610 p15791 p17122 p17096 p15909 p15786 p17758 p15783 p15911 p15905 p20319 p17115 p17120 p17111 p17124 p17050 p16778 p17113 p17117 p20467 p17104 p17874 p17127 p15914 p20274 p20470 p17133 p17089 p19665 p20426 p17055 p17108 p20461 p20126 p17131 p17110 p17053 p15917 p20096 p17294 p16943 p17058 p17064 p17067 p17069 p17072 p20700 p5255
end
end Assembly
