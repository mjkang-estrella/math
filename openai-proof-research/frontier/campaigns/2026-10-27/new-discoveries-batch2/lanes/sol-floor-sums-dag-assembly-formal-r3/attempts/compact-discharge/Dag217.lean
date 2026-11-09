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
  have h2296 : (e2296 _v) := by
    tauto
  have h6784 : (e6784 _v) := by
    change (¬ (e2793 _v))
    tauto
  have p19732 := n19732 _v _q h2296 h6784
  exact p19732
theorem n19744 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e6549 _v) := by
  have p19743 := n19743 _v _q 
  have p11473 := n11473 _v _q h6784
  simp only [e2296, e2793, e6549, e6784, e19742] at *
  tauto
theorem n19745 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e79 _v) := by
  have p11490 := n11490 _v _q 
  have p19733 := n19733 _v _q h6784
  simp only [e79, e2303, e7807, e11489] at *
  tauto
theorem n19746 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e5135 _v) := by
  have p14729 := n14729 _v _q 
  have p19745 := n19745 _v _q h6784
  simp only [e79, e89, e91, e94, e95, e5134, e5135, e5138, e5140] at *
  tauto
theorem n19747 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e91 _v) := by
  have p16235 := n16235 _v _q 
  have p19746 := n19746 _v _q h6784
  simp only [e89, e91, e94, e95, e5134, e5135, e7983] at *
  tauto
theorem n19748 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e2529 _v) := by
  have p11387 := n11387 _v _q 
  have p19733 := n19733 _v _q h6784
  simp only [e2303, e2529, e7807, e11386] at *
  tauto
theorem n19749 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e8307 _v) := by
  have p14906 := n14906 _v _q 
  have p19748 := n19748 _v _q h6784
  simp only [e2529, e4836, e4837, e4838, e4839, e8301, e8307, e8310, e8312] at *
  tauto
theorem n19750 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e4838 _v) := by
  have p16285 := n16285 _v _q 
  have p19749 := n19749 _v _q h6784
  simp only [e4836, e4837, e4838, e4839, e8301, e8302, e8307] at *
  tauto
theorem n19751 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e7804 _v) := by
  have p14837 := n14837 _v _q 
  have p19733 := n19733 _v _q h6784
  simp only [e2303, e4283, e4284, e4285, e4286, e7798, e7804, e7807, e7809] at *
  tauto
theorem n19752 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e4285 _v) := by
  have p16274 := n16274 _v _q 
  have p19751 := n19751 _v _q h6784
  simp only [e4283, e4284, e4285, e4286, e7798, e7799, e7804] at *
  tauto
theorem n19754 (_v : Vars) (_q : Query _v)  : (e19753 _v) := by
  by_contra hc
  change ¬ ((e214 _v) ∨ (e2793 _v)) at hc
  have h5223 : (e5223 _v) := by
    change (¬ (e214 _v))
    tauto
  have h6784 : (e6784 _v) := by
    change (¬ (e2793 _v))
    tauto
  have p19735 := n19735 _v _q h5223 h6784
  exact p19735
theorem n19755 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e214 _v) := by
  have p19754 := n19754 _v _q 
  have p11473 := n11473 _v _q h6784
  simp only [e214, e2793, e6784, e19753] at *
  tauto
theorem n19756 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e5232 _v) := by
  have p14731 := n14731 _v _q 
  have p19755 := n19755 _v _q h6784
  simp only [e214, e225, e227, e230, e231, e5223, e5231, e5232, e5235] at *
  tauto
theorem n19757 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e4731 _v) := by
  have p14698 := n14698 _v _q 
  have p19736 := n19736 _v _q h6784
  simp only [e2254, e4723, e4724, e4728, e4729, e4730, e4731, e6531, e8220] at *
  tauto
theorem n19758 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e4724 _v) := by
  have p15518 := n15518 _v _q 
  have p19757 := n19757 _v _q h6784
  simp only [e4723, e4724, e4728, e4729, e4730, e4731, e4958] at *
  tauto
theorem n19759 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e7668 _v) := by
  have p14544 := n14544 _v _q 
  have p19737 := n19737 _v _q h6784
  simp only [e2351, e4156, e4157, e4158, e4159, e6575, e7660, e7668, e7671] at *
  tauto
theorem n19760 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e4156 _v) := by
  have p11524 := n11524 _v _q 
  have p19759 := n19759 _v _q h6784
  simp only [e4156, e4157, e4158, e4159, e7660, e7661, e7668] at *
  tauto
theorem n19761 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e5403 _v) := by
  have p14577 := n14577 _v _q 
  have p19738 := n19738 _v _q h6784
  simp only [e474, e488, e490, e493, e494, e5392, e5402, e5403, e5406] at *
  tauto
theorem n19762 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e488 _v) := by
  have p15090 := n15090 _v _q 
  have p19761 := n19761 _v _q h6784
  simp only [e488, e490, e493, e494, e5402, e5403, e7821] at *
  tauto
theorem n19763 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) (h5362 : (e5362 _v)) : (e8317 _v) := by
  have p11541 := n11541 _v _q 
  have p19696 := n19696 _v _q h2468 h5362
  simp only [e8315, e8317, e8319, e8320, e8321, e8322, e8491] at *
  tauto
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
  simp only [e436, e474, e2296, e2468, e4264, e4269, e4373, e4378, e4817, e4822, e4872, e4873, e5362, e5392, e6549, e6630, e18059] at *
  tauto
theorem n19766 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) : (e8317 _v) := by
  have p11541 := n11541 _v _q 
  have p15780 := n15780 _v _q h5362
  simp only [e8315, e8317, e8319, e8320, e8321, e8322, e8491] at *
  tauto
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
  simp only [e436, e474, e2296, e2468, e4264, e4269, e4373, e4378, e4817, e4822, e4872, e4873, e5362, e5392, e6549, e6630, e18059] at *
  tauto
theorem n19769 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4302 : (e4302 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e7657 _v) := by
  have p11406 := n11406 _v _q 
  have p19741 := n19741 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4156 h4199 h4260 h4302 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  simp only [e7645, e7648, e7655, e7656, e7657, e8474] at *
  tauto
theorem n19770 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e6879 _v) := by
  have p14643 := n14643 _v _q 
  have p19744 := n19744 _v _q h6784
  simp only [e2296, e3150, e3152, e3155, e3156, e6549, e6878, e6879, e6882] at *
  tauto
theorem n19771 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e3152 _v) := by
  have p15776 := n15776 _v _q 
  have p19770 := n19770 _v _q h6784
  simp only [e3150, e3152, e3155, e3156, e6878, e6879, e8223] at *
  tauto
theorem n19772 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e225 _v) := by
  have p16653 := n16653 _v _q 
  have p19756 := n19756 _v _q h6784
  simp only [e225, e227, e230, e231, e5231, e5232, e5253] at *
  tauto
theorem n19773 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) (h5362 : (e5362 _v)) : (e6575 _v) := by
  have p8547 := n8547 _v _q 
  have p19765 := n19765 _v _q h2468 h5362
  simp only [e2296, e2351, e6549, e6575, e8546] at *
  tauto
theorem n19774 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) (h5362 : (e5362 _v)) : (e7668 _v) := by
  have p14544 := n14544 _v _q 
  have p19773 := n19773 _v _q h2468 h5362
  simp only [e2351, e4156, e4157, e4158, e4159, e6575, e7660, e7668, e7671] at *
  tauto
theorem n19775 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) (h5362 : (e5362 _v)) : (e4156 _v) := by
  have p11524 := n11524 _v _q 
  have p19774 := n19774 _v _q h2468 h5362
  simp only [e4156, e4157, e4158, e4159, e7660, e7661, e7668] at *
  tauto
theorem n19776 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) (h5362 : (e5362 _v)) : (e6879 _v) := by
  have p14643 := n14643 _v _q 
  have p19765 := n19765 _v _q h2468 h5362
  simp only [e2296, e3150, e3152, e3155, e3156, e6549, e6878, e6879, e6882] at *
  tauto
theorem n19777 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) (h5362 : (e5362 _v)) : (e3152 _v) := by
  have p15776 := n15776 _v _q 
  have p19776 := n19776 _v _q h2468 h5362
  simp only [e3150, e3152, e3155, e3156, e6878, e6879, e8223] at *
  tauto
theorem n19778 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h5362 : (e5362 _v)) : (e8275 _v) := by
  have p14655 := n14655 _v _q 
  have p19768 := n19768 _v _q h2351 h5362
  simp only [e2468, e4785, e4786, e4787, e4788, e6630, e8267, e8275, e8278] at *
  tauto
theorem n19779 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h5362 : (e5362 _v)) : (e4787 _v) := by
  have p15670 := n15670 _v _q 
  have p19778 := n19778 _v _q h2351 h5362
  simp only [e4785, e4786, e4787, e4788, e8267, e8268, e8275] at *
  tauto
theorem n19780 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4302 : (e4302 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e7634 _v) := by
  have p16281 := n16281 _v _q 
  have p19740 := n19740 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4156 h4199 h4260 h4302 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  simp only [e4139, e4140, e4141, e4142, e7634, e7635] at *
  tauto
theorem n19781 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4302 : (e4302 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e6571 _v) := by
  have p14828 := n14828 _v _q 
  have p19780 := n19780 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4156 h4199 h4260 h4302 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  simp only [e2358, e4139, e4140, e4141, e4142, e6571, e7634, e7640, e7643] at *
  tauto
theorem n19782 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4302 : (e4302 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e7489 _v) := by
  have p15249 := n15249 _v _q 
  have p19781 := n19781 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4156 h4199 h4260 h4302 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  have p19769 := n19769 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4156 h4199 h4260 h4302 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  simp only [e2358, e6571, e7645, e7648, e7655, e7656, e7657, e7658, e10960] at *
  tauto
theorem n19783 (_v : Vars) (_q : Query _v)  : (e8540 _v) := by
  by_contra hc
  change ¬ ((e4301 _v) ∨ (¬ (e3069 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v))) at hc
  have h70 : (e70 _v) := by
    tauto
  have h91 : (e91 _v) := by
    tauto
  have h225 : (e225 _v) := by
    tauto
  have h442 : (e442 _v) := by
    tauto
  have h488 : (e488 _v) := by
    tauto
  have h3069 : (e3069 _v) := by
    tauto
  have h3105 : (e3105 _v) := by
    tauto
  have h3152 : (e3152 _v) := by
    tauto
  have h3937 : (e3937 _v) := by
    tauto
  have h3946 : (e3946 _v) := by
    tauto
  have h4059 : (e4059 _v) := by
    tauto
  have h4096 : (e4096 _v) := by
    tauto
  have h4156 : (e4156 _v) := by
    tauto
  have h4199 : (e4199 _v) := by
    tauto
  have h4260 : (e4260 _v) := by
    tauto
  have h4302 : (e4302 _v) := by
    change (¬ (e4301 _v))
    tauto
  have h4369 : (e4369 _v) := by
    tauto
  have h4434 : (e4434 _v) := by
    tauto
  have h4608 : (e4608 _v) := by
    tauto
  have h4675 : (e4675 _v) := by
    tauto
  have h4747 : (e4747 _v) := by
    tauto
  have h4787 : (e4787 _v) := by
    tauto
  have h4813 : (e4813 _v) := by
    tauto
  have h4872 : (e4872 _v) := by
    tauto
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
  simp only [e70, e75, e91, e95, e225, e230, e442, e443, e488, e493, e3069, e3074, e3105, e3106, e3152, e3156, e3937, e3942, e3946, e3947, e4059, e4064, e4096, e4097, e4156, e4157, e4199, e4200, e4260, e4261, e4301, e4369, e4370, e4434, e4435, e4608, e4609, e4675, e4676, e4747, e4752, e4787, e4788, e4813, e4814, e4872, e4873, e8540] at *
  tauto
end
end Assembly
