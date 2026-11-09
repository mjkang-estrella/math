import Dag216
import generated.th_lemma_27
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n19738 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e5392 _v) := by
  have p11473 := n11473 _v _q h6784
  have p10896 := n10896 _v _q 
  have p19731 := n19731 _v _q h6784
  have p11375 := n11375 _v _q 
  exact FloorCertificate.node_19738 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p11473 p10896 p19731 p11375
theorem n19739 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) : (e4373 _v) := by
  have p19716 := n19716 _v _q h5362
  have p19728 := n19728 _v _q h5362
  have p18120 := n18120 _v _q h5362
  exact FloorCertificate.node_19739 (e2 _v) (e9 _v) (e17 _v) (e45 _v) (e80 _v) (e2976 _v) p19716 p19728 p18120
theorem n19740 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4302 : (e4302 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e4140 _v) := by
  have p4016 := n4016 _v _q 
  have p17098 := n17098 _v _q 
  have p19681 := n19681 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4156 h4199 h4260 h4302 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  have p13951 := n13951 _v _q 
  have p16977 := n16977 _v _q 
  have p10893 := n10893 _v _q 
  have p8663 := n8663 _v _q 
  have p17096 := n17096 _v _q 
  have p17110 := n17110 _v _q 
  have p17013 := n17013 _v _q h4302 h4434
  have p19702 := n19702 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4156 h4199 h4260 h4302 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  have p17102 := n17102 _v _q 
  have p17104 := n17104 _v _q 
  have p17106 := n17106 _v _q 
  have p19705 := n19705 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4156 h4199 h4260 h4302 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  have p17108 := n17108 _v _q 
  have p4994 := n4994 _v _q h3069
  have p17120 := n17120 _v _q 
  have p17113 := n17113 _v _q 
  have p17117 := n17117 _v _q 
  have p17124 := n17124 _v _q 
  have p17122 := n17122 _v _q 
  have p19649 := n19649 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h4096 h4156 h4199 h4260 h4302 h4369 h4434 h4608 h4675 h4787 h4813 h4872
  have p4981 := n4981 _v _q h4260
  have p5001 := n5001 _v _q h4096
  have p4999 := n4999 _v _q h91
  have p17036 := n17036 _v _q h4302 h4434
  have p5010 := n5010 _v _q h70
  have p5003 := n5003 _v _q h4199
  have p5007 := n5007 _v _q h225
  have p4992 := n4992 _v _q h442
  have p19707 := n19707 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4156 h4199 h4260 h4302 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  have p17131 := n17131 _v _q 
  have p4996 := n4996 _v _q h3937
  have p16842 := n16842 _v _q h4302
  have p19721 := n19721 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h4096 h4156 h4199 h4260 h4302 h4369 h4434 h4608 h4675 h4787 h4813 h4872
  have p17133 := n17133 _v _q 
  have p16528 := n16528 _v _q h4302
  have p4987 := n4987 _v _q h4434
  have p17136 := n17136 _v _q 
  have p17137 := n17137 _v _q h4059
  have p16778 := n16778 _v _q 
  have p16517 := n16517 _v _q h4302
  have p18607 := n18607 _v _q h4302
  have p16845 := n16845 _v _q h4302
  have p17017 := n17017 _v _q h4302 h4434
  have p4983 := n4983 _v _q h4813
  have p17053 := n17053 _v _q 
  have p17127 := n17127 _v _q 
  have p4995 := n4995 _v _q h4369
  have p4998 := n4998 _v _q h3152
  have p16576 := n16576 _v _q 
  have p19722 := n19722 _v _q h4302 h4434
  have p5008 := n5008 _v _q h4787
  have p17009 := n17009 _v _q 
  have p17055 := n17055 _v _q 
  have p16540 := n16540 _v _q h4302
  have p17058 := n17058 _v _q 
  have p5006 := n5006 _v _q h4675
  have p17056 := n17056 _v _q h3946
  have p17061 := n17061 _v _q h4747
  have p17147 := n17147 _v _q 
  have p17064 := n17064 _v _q 
  have p17089 := n17089 _v _q 
  have p17067 := n17067 _v _q 
  have p17072 := n17072 _v _q 
  have p17069 := n17069 _v _q 
  have p17074 := n17074 _v _q 
  have p4985 := n4985 _v _q h4156
  have p16538 := n16538 _v _q h4302
  have p16929 := n16929 _v _q 
  have p4988 := n4988 _v _q h488
  have p17080 := n17080 _v _q 
  have p17078 := n17078 _v _q 
  have p17141 := n17141 _v _q 
  have p17091 := n17091 _v _q 
  have p17093 := n17093 _v _q 
  have p4986 := n4986 _v _q h3105
  have p17111 := n17111 _v _q 
  have p4984 := n4984 _v _q h4872
  have p17083 := n17083 _v _q 
  have p4991 := n4991 _v _q h4608
  have p17087 := n17087 _v _q 
  have p17115 := n17115 _v _q 
  have p17100 := n17100 _v _q 
  have p19730 := n19730 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4156 h4199 h4260 h4302 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  exact FloorCertificate.node_19740 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e61 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2849 _v) (e2863 _v) (e2877 _v) (e2883 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p4016 p17098 p19681 p13951 p16977 p10893 p8663 p17096 p17110 p17013 p19702 p17102 p17104 p17106 p19705 p17108 p4994 p17120 p17113 p17117 p17124 p17122 p19649 p4981 p5001 p4999 p17036 p5010 p5003 p5007 p4992 p19707 p17131 p4996 p16842 p19721 p17133 p16528 p4987 p17136 p17137 p16778 p16517 p18607 p16845 p17017 p4983 p17053 p17127 p4995 p4998 p16576 p19722 p5008 p17009 p17055 p16540 p17058 p5006 p17056 p17061 p17147 p17064 p17089 p17067 p17072 p17069 p17074 p4985 p16538 p16929 p4988 p17080 p17078 p17141 p17091 p17093 p4986 p17111 p4984 p17083 p4991 p17087 p17115 p17100 p19730
theorem n19741 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4302 : (e4302 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e7655 _v) := by
  have p17102 := n17102 _v _q 
  have p17098 := n17098 _v _q 
  have p13951 := n13951 _v _q 
  have p10893 := n10893 _v _q 
  have p16977 := n16977 _v _q 
  have p17096 := n17096 _v _q 
  have p17110 := n17110 _v _q 
  have p17013 := n17013 _v _q h4302 h4434
  have p4016 := n4016 _v _q 
  have p19702 := n19702 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4156 h4199 h4260 h4302 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  have p19730 := n19730 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4156 h4199 h4260 h4302 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  have p17104 := n17104 _v _q 
  have p17106 := n17106 _v _q 
  have p19705 := n19705 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4156 h4199 h4260 h4302 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  have p17108 := n17108 _v _q 
  have p4994 := n4994 _v _q h3069
  have p17120 := n17120 _v _q 
  have p17113 := n17113 _v _q 
  have p17117 := n17117 _v _q 
  have p17124 := n17124 _v _q 
  have p17122 := n17122 _v _q 
  have p19649 := n19649 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h4096 h4156 h4199 h4260 h4302 h4369 h4434 h4608 h4675 h4787 h4813 h4872
  have p4981 := n4981 _v _q h4260
  have p5001 := n5001 _v _q h4096
  have p4999 := n4999 _v _q h91
  have p17036 := n17036 _v _q h4302 h4434
  have p5010 := n5010 _v _q h70
  have p5003 := n5003 _v _q h4199
  have p5007 := n5007 _v _q h225
  have p4992 := n4992 _v _q h442
  have p19707 := n19707 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4156 h4199 h4260 h4302 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  have p17131 := n17131 _v _q 
  have p4996 := n4996 _v _q h3937
  have p16842 := n16842 _v _q h4302
  have p19721 := n19721 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h4096 h4156 h4199 h4260 h4302 h4369 h4434 h4608 h4675 h4787 h4813 h4872
  have p17133 := n17133 _v _q 
  have p16528 := n16528 _v _q h4302
  have p4987 := n4987 _v _q h4434
  have p17136 := n17136 _v _q 
  have p17137 := n17137 _v _q h4059
  have p16778 := n16778 _v _q 
  have p16517 := n16517 _v _q h4302
  have p18607 := n18607 _v _q h4302
  have p16845 := n16845 _v _q h4302
  have p17017 := n17017 _v _q h4302 h4434
  have p4983 := n4983 _v _q h4813
  have p17053 := n17053 _v _q 
  have p17127 := n17127 _v _q 
  have p4995 := n4995 _v _q h4369
  have p4998 := n4998 _v _q h3152
  have p16576 := n16576 _v _q 
  have p19722 := n19722 _v _q h4302 h4434
  have p5008 := n5008 _v _q h4787
  have p17009 := n17009 _v _q 
  have p17055 := n17055 _v _q 
  have p16540 := n16540 _v _q h4302
  have p17058 := n17058 _v _q 
  have p5006 := n5006 _v _q h4675
  have p17056 := n17056 _v _q h3946
  have p17061 := n17061 _v _q h4747
  have p17147 := n17147 _v _q 
  have p17064 := n17064 _v _q 
  have p17089 := n17089 _v _q 
  have p17067 := n17067 _v _q 
  have p17072 := n17072 _v _q 
  have p17069 := n17069 _v _q 
  have p17074 := n17074 _v _q 
  have p4985 := n4985 _v _q h4156
  have p16538 := n16538 _v _q h4302
  have p16929 := n16929 _v _q 
  have p4988 := n4988 _v _q h488
  have p17080 := n17080 _v _q 
  have p17078 := n17078 _v _q 
  have p17141 := n17141 _v _q 
  have p17091 := n17091 _v _q 
  have p17093 := n17093 _v _q 
  have p4986 := n4986 _v _q h3105
  have p17111 := n17111 _v _q 
  have p4984 := n4984 _v _q h4872
  have p17083 := n17083 _v _q 
  have p4991 := n4991 _v _q h4608
  have p17087 := n17087 _v _q 
  have p17115 := n17115 _v _q 
  have p17100 := n17100 _v _q 
  have p8663 := n8663 _v _q 
  have p19681 := n19681 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4156 h4199 h4260 h4302 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  have p19723 := n19723 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4156 h4199 h4260 h4302 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  exact FloorCertificate.node_19741 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e61 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2849 _v) (e2863 _v) (e2877 _v) (e2883 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p17102 p17098 p13951 p10893 p16977 p17096 p17110 p17013 p4016 p19702 p19730 p17104 p17106 p19705 p17108 p4994 p17120 p17113 p17117 p17124 p17122 p19649 p4981 p5001 p4999 p17036 p5010 p5003 p5007 p4992 p19707 p17131 p4996 p16842 p19721 p17133 p16528 p4987 p17136 p17137 p16778 p16517 p18607 p16845 p17017 p4983 p17053 p17127 p4995 p4998 p16576 p19722 p5008 p17009 p17055 p16540 p17058 p5006 p17056 p17061 p17147 p17064 p17089 p17067 p17072 p17069 p17074 p4985 p16538 p16929 p4988 p17080 p17078 p17141 p17091 p17093 p4986 p17111 p4984 p17083 p4991 p17087 p17115 p17100 p8663 p19681 p19723
theorem n19743 (_v : Vars) (_q : Query _v)  : (e19742 _v) := by
  by_contra hc
  change ¬ ((¬ (e2296 _v)) ∨ (e2793 _v)) at hc
  have h2296 : (e2296 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h6784 : (e6784 _v) := (fun hn => hc (Or.inr hn))
  have p19732 := n19732 _v _q h2296 h6784
  exact p19732
theorem n19744 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e6549 _v) := by
  have p19743 := n19743 _v _q 
  have p11473 := n11473 _v _q h6784
  change (¬ (e2296 _v)) ∨ (e2793 _v) at p19743
  change (¬ (e2793 _v)) at p11473
  rcases p19743 with hlit | hlit
  · exact hlit
  · exact (False.elim (p11473 hlit))
theorem n19745 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e79 _v) := by
  have p11490 := n11490 _v _q 
  have p19733 := n19733 _v _q h6784
  change (e79 _v) ∨ (¬ (e2303 _v)) at p11490
  rcases p11490 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p19733))
theorem n19746 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e5135 _v) := by
  have p14729 := n14729 _v _q 
  have p19745 := n19745 _v _q h6784
  change (¬ (e79 _v)) ∨ (¬ (e5134 _v)) at p14729
  rcases p14729 with hlit | hlit
  · exact (False.elim (hlit p19745))
  · exact hlit
theorem n19747 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e91 _v) := by
  have p16235 := n16235 _v _q 
  have p19746 := n19746 _v _q h6784
  change (e5134 _v) ∨ (e91 _v) at p16235
  change (¬ (e5134 _v)) at p19746
  rcases p16235 with hlit | hlit
  · exact (False.elim (p19746 hlit))
  · exact hlit
theorem n19748 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e2529 _v) := by
  have p11387 := n11387 _v _q 
  have p19733 := n19733 _v _q h6784
  change (¬ (e2303 _v)) ∨ (e2529 _v) at p11387
  rcases p11387 with hlit | hlit
  · exact (False.elim (hlit p19733))
  · exact hlit
theorem n19749 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e8307 _v) := by
  have p14906 := n14906 _v _q 
  have p19748 := n19748 _v _q h6784
  change (¬ (e2529 _v)) ∨ (¬ (e8301 _v)) at p14906
  rcases p14906 with hlit | hlit
  · exact (False.elim (hlit p19748))
  · exact hlit
theorem n19750 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e4838 _v) := by
  have p16285 := n16285 _v _q 
  have p19749 := n19749 _v _q h6784
  change (e8301 _v) ∨ (e4838 _v) at p16285
  change (¬ (e8301 _v)) at p19749
  rcases p16285 with hlit | hlit
  · exact (False.elim (p19749 hlit))
  · exact hlit
theorem n19751 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e7804 _v) := by
  have p14837 := n14837 _v _q 
  have p19733 := n19733 _v _q h6784
  change (¬ (e2303 _v)) ∨ (¬ (e7798 _v)) at p14837
  rcases p14837 with hlit | hlit
  · exact (False.elim (hlit p19733))
  · exact hlit
theorem n19752 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e4285 _v) := by
  have p16274 := n16274 _v _q 
  have p19751 := n19751 _v _q h6784
  change (e7798 _v) ∨ (e4285 _v) at p16274
  change (¬ (e7798 _v)) at p19751
  rcases p16274 with hlit | hlit
  · exact (False.elim (p19751 hlit))
  · exact hlit
theorem n19754 (_v : Vars) (_q : Query _v)  : (e19753 _v) := by
  by_contra hc
  change ¬ ((e214 _v) ∨ (e2793 _v)) at hc
  have h5223 : (e5223 _v) := (fun hn => hc (Or.inl hn))
  have h6784 : (e6784 _v) := (fun hn => hc (Or.inr hn))
  have p19735 := n19735 _v _q h5223 h6784
  exact p19735
theorem n19755 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e214 _v) := by
  have p19754 := n19754 _v _q 
  have p11473 := n11473 _v _q h6784
  change (e214 _v) ∨ (e2793 _v) at p19754
  change (¬ (e2793 _v)) at p11473
  rcases p19754 with hlit | hlit
  · exact hlit
  · exact (False.elim (p11473 hlit))
theorem n19756 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e5232 _v) := by
  have p14731 := n14731 _v _q 
  have p19755 := n19755 _v _q h6784
  change (¬ (e214 _v)) ∨ (¬ (e5231 _v)) at p14731
  rcases p14731 with hlit | hlit
  · exact (False.elim (hlit p19755))
  · exact hlit
theorem n19757 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e4731 _v) := by
  have p14698 := n14698 _v _q 
  have p19736 := n19736 _v _q h6784
  change (¬ (e2254 _v)) ∨ (¬ (e4730 _v)) at p14698
  rcases p14698 with hlit | hlit
  · exact (False.elim (hlit p19736))
  · exact hlit
theorem n19758 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e4724 _v) := by
  have p15518 := n15518 _v _q 
  have p19757 := n19757 _v _q h6784
  change (e4730 _v) ∨ (e4724 _v) at p15518
  change (¬ (e4730 _v)) at p19757
  rcases p15518 with hlit | hlit
  · exact (False.elim (p19757 hlit))
  · exact hlit
theorem n19759 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e7668 _v) := by
  have p14544 := n14544 _v _q 
  have p19737 := n19737 _v _q h6784
  change (e2351 _v) ∨ (¬ (e7660 _v)) at p14544
  change (¬ (e2351 _v)) at p19737
  rcases p14544 with hlit | hlit
  · exact (False.elim (p19737 hlit))
  · exact hlit
theorem n19760 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e4156 _v) := by
  have p11524 := n11524 _v _q 
  have p19759 := n19759 _v _q h6784
  change (e7660 _v) ∨ (e4156 _v) at p11524
  change (¬ (e7660 _v)) at p19759
  rcases p11524 with hlit | hlit
  · exact (False.elim (p19759 hlit))
  · exact hlit
theorem n19761 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e5403 _v) := by
  have p14577 := n14577 _v _q 
  have p19738 := n19738 _v _q h6784
  change (e474 _v) ∨ (¬ (e5402 _v)) at p14577
  change (¬ (e474 _v)) at p19738
  rcases p14577 with hlit | hlit
  · exact (False.elim (p19738 hlit))
  · exact hlit
theorem n19762 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e488 _v) := by
  have p15090 := n15090 _v _q 
  have p19761 := n19761 _v _q h6784
  change (e5402 _v) ∨ (e488 _v) at p15090
  change (¬ (e5402 _v)) at p19761
  rcases p15090 with hlit | hlit
  · exact (False.elim (p19761 hlit))
  · exact hlit
theorem n19763 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) (h5362 : (e5362 _v)) : (e8317 _v) := by
  have p11541 := n11541 _v _q 
  have p19696 := n19696 _v _q h2468 h5362
  change (e8321 _v) ∨ (e8317 _v) at p11541
  change (¬ (e8321 _v)) at p19696
  rcases p11541 with hlit | hlit
  · exact (False.elim (p19696 hlit))
  · exact hlit
theorem n19764 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) (h5362 : (e5362 _v)) : (e4817 _v) := by
  have p19693 := n19693 _v _q h5362
  have p19763 := n19763 _v _q h2468 h5362
  have p19673 := n19673 _v _q h5362
  exact FloorCertificate.node_19764 (e2 _v) (e17 _v) (e45 _v) (e110 _v) (e2966 _v) (e4808 _v) p19693 p19763 p19673
theorem n19765 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) (h5362 : (e5362 _v)) : (e6549 _v) := by
  have p18060 := n18060 _v _q 
  have p19764 := n19764 _v _q h2468 h5362
  have p7488 := n7488 _v _q h5362
  have p19739 := n19739 _v _q h5362
  have p19674 := n19674 _v _q h5362
  have p19665 := n19665 _v _q 
  have p8438 := n8438 _v _q h2468
  have p17252 := n17252 _v _q h5362
  change (¬ (e4373 _v)) ∨ (¬ (e2468 _v)) ∨ (e474 _v) ∨ (e436 _v) ∨ (¬ (e2296 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4817 _v)) ∨ (¬ (e4264 _v)) at p18060
  change (¬ (e436 _v)) at p7488
  change (¬ (e474 _v)) at p19674
  rcases p18060 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact (False.elim (hlit p19739))
  · exact (False.elim (hlit p8438))
  · exact (False.elim (p19674 hlit))
  · exact (False.elim (p7488 hlit))
  · exact hlit
  · exact (False.elim (hlit p19665))
  · exact (False.elim (hlit p19764))
  · exact (False.elim (hlit p17252))
theorem n19766 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) : (e8317 _v) := by
  have p11541 := n11541 _v _q 
  have p15780 := n15780 _v _q h5362
  change (e8321 _v) ∨ (e8317 _v) at p11541
  change (¬ (e8321 _v)) at p15780
  rcases p11541 with hlit | hlit
  · exact (False.elim (p15780 hlit))
  · exact hlit
theorem n19767 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h5362 : (e5362 _v)) : (e4817 _v) := by
  have p19687 := n19687 _v _q h2351 h5362
  have p19766 := n19766 _v _q h5362
  have p19668 := n19668 _v _q h2351 h5362
  exact FloorCertificate.node_19767 (e2 _v) (e17 _v) (e45 _v) (e110 _v) (e2966 _v) (e4808 _v) p19687 p19766 p19668
theorem n19768 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h5362 : (e5362 _v)) : (e6630 _v) := by
  have p18060 := n18060 _v _q 
  have p19767 := n19767 _v _q h2351 h5362
  have p7488 := n7488 _v _q h5362
  have p19739 := n19739 _v _q h5362
  have p19674 := n19674 _v _q h5362
  have p19665 := n19665 _v _q 
  have p15781 := n15781 _v _q h2351
  have p17252 := n17252 _v _q h5362
  change (¬ (e4373 _v)) ∨ (¬ (e2468 _v)) ∨ (e474 _v) ∨ (e436 _v) ∨ (¬ (e2296 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4817 _v)) ∨ (¬ (e4264 _v)) at p18060
  change (¬ (e436 _v)) at p7488
  change (¬ (e474 _v)) at p19674
  rcases p18060 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact (False.elim (hlit p19739))
  · exact hlit
  · exact (False.elim (p19674 hlit))
  · exact (False.elim (p7488 hlit))
  · exact (False.elim (hlit p15781))
  · exact (False.elim (hlit p19665))
  · exact (False.elim (hlit p19767))
  · exact (False.elim (hlit p17252))
theorem n19769 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4302 : (e4302 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e7657 _v) := by
  have p11406 := n11406 _v _q 
  have p19741 := n19741 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4156 h4199 h4260 h4302 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  change (e7657 _v) ∨ (e7645 _v) at p11406
  change (¬ (e7645 _v)) at p19741
  rcases p11406 with hlit | hlit
  · exact hlit
  · exact (False.elim (p19741 hlit))
theorem n19770 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e6879 _v) := by
  have p14643 := n14643 _v _q 
  have p19744 := n19744 _v _q h6784
  change (e2296 _v) ∨ (¬ (e6878 _v)) at p14643
  change (¬ (e2296 _v)) at p19744
  rcases p14643 with hlit | hlit
  · exact (False.elim (p19744 hlit))
  · exact hlit
theorem n19771 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e3152 _v) := by
  have p15776 := n15776 _v _q 
  have p19770 := n19770 _v _q h6784
  change (e6878 _v) ∨ (e3152 _v) at p15776
  change (¬ (e6878 _v)) at p19770
  rcases p15776 with hlit | hlit
  · exact (False.elim (p19770 hlit))
  · exact hlit
theorem n19772 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e225 _v) := by
  have p16653 := n16653 _v _q 
  have p19756 := n19756 _v _q h6784
  change (e5231 _v) ∨ (e225 _v) at p16653
  change (¬ (e5231 _v)) at p19756
  rcases p16653 with hlit | hlit
  · exact (False.elim (p19756 hlit))
  · exact hlit
theorem n19773 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) (h5362 : (e5362 _v)) : (e6575 _v) := by
  have p8547 := n8547 _v _q 
  have p19765 := n19765 _v _q h2468 h5362
  change (e2296 _v) ∨ (¬ (e2351 _v)) at p8547
  change (¬ (e2296 _v)) at p19765
  rcases p8547 with hlit | hlit
  · exact (False.elim (p19765 hlit))
  · exact hlit
theorem n19774 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) (h5362 : (e5362 _v)) : (e7668 _v) := by
  have p14544 := n14544 _v _q 
  have p19773 := n19773 _v _q h2468 h5362
  change (e2351 _v) ∨ (¬ (e7660 _v)) at p14544
  change (¬ (e2351 _v)) at p19773
  rcases p14544 with hlit | hlit
  · exact (False.elim (p19773 hlit))
  · exact hlit
theorem n19775 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) (h5362 : (e5362 _v)) : (e4156 _v) := by
  have p11524 := n11524 _v _q 
  have p19774 := n19774 _v _q h2468 h5362
  change (e7660 _v) ∨ (e4156 _v) at p11524
  change (¬ (e7660 _v)) at p19774
  rcases p11524 with hlit | hlit
  · exact (False.elim (p19774 hlit))
  · exact hlit
theorem n19776 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) (h5362 : (e5362 _v)) : (e6879 _v) := by
  have p14643 := n14643 _v _q 
  have p19765 := n19765 _v _q h2468 h5362
  change (e2296 _v) ∨ (¬ (e6878 _v)) at p14643
  change (¬ (e2296 _v)) at p19765
  rcases p14643 with hlit | hlit
  · exact (False.elim (p19765 hlit))
  · exact hlit
theorem n19777 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) (h5362 : (e5362 _v)) : (e3152 _v) := by
  have p15776 := n15776 _v _q 
  have p19776 := n19776 _v _q h2468 h5362
  change (e6878 _v) ∨ (e3152 _v) at p15776
  change (¬ (e6878 _v)) at p19776
  rcases p15776 with hlit | hlit
  · exact (False.elim (p19776 hlit))
  · exact hlit
theorem n19778 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h5362 : (e5362 _v)) : (e8275 _v) := by
  have p14655 := n14655 _v _q 
  have p19768 := n19768 _v _q h2351 h5362
  change (e2468 _v) ∨ (¬ (e8267 _v)) at p14655
  change (¬ (e2468 _v)) at p19768
  rcases p14655 with hlit | hlit
  · exact (False.elim (p19768 hlit))
  · exact hlit
theorem n19779 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h5362 : (e5362 _v)) : (e4787 _v) := by
  have p15670 := n15670 _v _q 
  have p19778 := n19778 _v _q h2351 h5362
  change (e8267 _v) ∨ (e4787 _v) at p15670
  change (¬ (e8267 _v)) at p19778
  rcases p15670 with hlit | hlit
  · exact (False.elim (p19778 hlit))
  · exact hlit
theorem n19780 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4302 : (e4302 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e7634 _v) := by
  have p16281 := n16281 _v _q 
  have p19740 := n19740 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4156 h4199 h4260 h4302 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  change (e7634 _v) ∨ (e4139 _v) at p16281
  change (¬ (e4139 _v)) at p19740
  rcases p16281 with hlit | hlit
  · exact hlit
  · exact (False.elim (p19740 hlit))
theorem n19781 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4302 : (e4302 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e6571 _v) := by
  have p14828 := n14828 _v _q 
  have p19780 := n19780 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4156 h4199 h4260 h4302 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  change (¬ (e2358 _v)) ∨ (¬ (e7634 _v)) at p14828
  rcases p14828 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p19780))
theorem n19782 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4302 : (e4302 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e7489 _v) := by
  have p15249 := n15249 _v _q 
  have p19781 := n19781 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4156 h4199 h4260 h4302 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  have p19769 := n19769 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4156 h4199 h4260 h4302 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  change (e2358 _v) ∨ (¬ (e7657 _v)) at p15249
  change (¬ (e2358 _v)) at p19781
  rcases p15249 with hlit | hlit
  · exact (False.elim (p19781 hlit))
  · exact (False.elim (hlit p19769))
theorem n19783 (_v : Vars) (_q : Query _v)  : (e8540 _v) := by
  by_contra hc
  change ¬ ((e4301 _v) ∨ (¬ (e3069 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v))) at hc
  have h70 : (e70 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h225 : (e225 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h442 : (e442 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h488 : (e488 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))
  have h3069 : (e3069 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h3105 : (e3105 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h3946 : (e3946 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))
  have h4059 : (e4059 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h4096 : (e4096 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4156 : (e4156 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))
  have h4199 : (e4199 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h4260 : (e4260 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4302 : (e4302 _v) := (fun hn => hc (Or.inl hn))
  have h4369 : (e4369 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h4434 : (e4434 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h4608 : (e4608 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))))))))))))))))))))
  have h4675 : (e4675 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))
  have h4747 : (e4747 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h4872 : (e4872 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))
  have p19782 := n19782 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4156 h4199 h4260 h4302 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  exact p19782
theorem n19784 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e4301 _v) := by
  have p19783 := n19783 _v _q 
  have p17137 := n17137 _v _q h4059
  have p4981 := n4981 _v _q h4260
  have p5001 := n5001 _v _q h4096
  have p4999 := n4999 _v _q h91
  have p5010 := n5010 _v _q h70
  have p5003 := n5003 _v _q h4199
  have p5007 := n5007 _v _q h225
  have p4992 := n4992 _v _q h442
  have p4996 := n4996 _v _q h3937
  have p4987 := n4987 _v _q h4434
  have p4994 := n4994 _v _q h3069
  have p4983 := n4983 _v _q h4813
  have p4995 := n4995 _v _q h4369
  have p4998 := n4998 _v _q h3152
  have p5008 := n5008 _v _q h4787
  have p5006 := n5006 _v _q h4675
  have p17056 := n17056 _v _q h3946
  have p17061 := n17061 _v _q h4747
  have p4985 := n4985 _v _q h4156
  have p4988 := n4988 _v _q h488
  have p4986 := n4986 _v _q h3105
  have p4984 := n4984 _v _q h4872
  have p4991 := n4991 _v _q h4608
  change (e4301 _v) ∨ (¬ (e3069 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) at p19783
  rcases p19783 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p4994))
  · exact (False.elim (hlit p4981))
  · exact (False.elim (hlit p5001))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p5010))
  · exact (False.elim (hlit p5003))
  · exact (False.elim (hlit p5007))
  · exact (False.elim (hlit p4992))
  · exact (False.elim (hlit p4996))
  · exact (False.elim (hlit p4987))
  · exact (False.elim (hlit p17137))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p4995))
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p17056))
  · exact (False.elim (hlit p17061))
  · exact (False.elim (hlit p4985))
  · exact (False.elim (hlit p4988))
  · exact (False.elim (hlit p4986))
  · exact (False.elim (hlit p4984))
  · exact (False.elim (hlit p4991))
end
end Assembly
