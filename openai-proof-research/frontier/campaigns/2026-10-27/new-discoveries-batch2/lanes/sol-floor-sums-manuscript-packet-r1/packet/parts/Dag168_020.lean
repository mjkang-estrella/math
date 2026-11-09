import parts.Dag168_019
import generated.th_lemma_16
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n17283 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h196 : (e196 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3158 : (e3158 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4101 : (e4101 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4264 : (e4264 _v)) (h4306 : (e4306 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4439 : (e4439 _v)) (h4459 : (e4459 _v)) (h4491 : (e4491 _v)) (h4567 : (e4567 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5100 : (e5100 _v)) (h7645 : (e7645 _v)) (h7814 : (e7814 _v)) (h8038 : (e8038 _v)) (h8045 : (e8045 _v)) (h8317 : (e8317 _v)) : (e7489 _v) := by
  have p17174 := n17174 _v _q h8317
  have p5255 := n5255 _v _q 
  have p8140 := n8140 _v _q h196
  have p17128 := n17128 _v _q h4491
  have p258 := n258 _v _q 
  have p5008 := n5008 _v _q h4787
  have p17176 := n17176 _v _q h7645
  have p17129 := n17129 _v _q h4903
  have p8602 := n8602 _v _q h8038
  have p17051 := n17051 _v _q h4459
  have p4996 := n4996 _v _q h3937
  have p5006 := n5006 _v _q h4675
  have p17159 := n17159 _v _q h5100
  have p17131 := n17131 _v _q 
  have p17172 := n17172 _v _q h7814
  have p16679 := n16679 _v _q h196
  have p17133 := n17133 _v _q 
  have p13951 := n13951 _v _q 
  have p17134 := n17134 _v _q h4398
  have p17136 := n17136 _v _q 
  have p17157 := n17157 _v _q h8045
  have p16885 := n16885 _v _q h3158
  have p17137 := n17137 _v _q h4059
  have p4999 := n4999 _v _q h91
  have p5007 := n5007 _v _q h225
  have p16778 := n16778 _v _q 
  have p17141 := n17141 _v _q 
  have p4992 := n4992 _v _q h442
  have p17143 := n17143 _v _q h4567
  have p17050 := n17050 _v _q 
  have p17053 := n17053 _v _q 
  have p17055 := n17055 _v _q 
  have p17056 := n17056 _v _q h3946
  have p17147 := n17147 _v _q 
  have p17058 := n17058 _v _q 
  have p17060 := n17060 _v _q h4653
  have p17061 := n17061 _v _q h4747
  have p17064 := n17064 _v _q 
  have p4995 := n4995 _v _q h4369
  have p17067 := n17067 _v _q 
  have p17069 := n17069 _v _q 
  have p17138 := n17138 _v _q h4306
  have p17072 := n17072 _v _q 
  have p17074 := n17074 _v _q 
  have p17076 := n17076 _v _q h3976
  have p4985 := n4985 _v _q h4156
  have p16729 := n16729 _v _q h51
  have p4988 := n4988 _v _q h488
  have p17078 := n17078 _v _q 
  have p4986 := n4986 _v _q h3105
  have p17080 := n17080 _v _q 
  have p17083 := n17083 _v _q 
  have p4984 := n4984 _v _q h4872
  have p17087 := n17087 _v _q 
  have p17091 := n17091 _v _q 
  have p17094 := n17094 _v _q h4724
  have p17093 := n17093 _v _q 
  have p17111 := n17111 _v _q 
  have p17075 := n17075 _v _q h4439
  have p17115 := n17115 _v _q 
  have p17089 := n17089 _v _q 
  have p17100 := n17100 _v _q 
  have p17098 := n17098 _v _q 
  have p17096 := n17096 _v _q 
  have p17110 := n17110 _v _q 
  have p17102 := n17102 _v _q 
  have p17104 := n17104 _v _q 
  have p17106 := n17106 _v _q 
  have p17108 := n17108 _v _q 
  have p4994 := n4994 _v _q h3069
  have p17120 := n17120 _v _q 
  have p17113 := n17113 _v _q 
  have p17117 := n17117 _v _q 
  have p17124 := n17124 _v _q 
  have p17122 := n17122 _v _q 
  have p17118 := n17118 _v _q h4264
  have p4998 := n4998 _v _q h3152
  have p17065 := n17065 _v _q h4101
  have p5003 := n5003 _v _q h4199
  have p17127 := n17127 _v _q 
  have p4983 := n4983 _v _q h4813
  exact FloorCertificate.node_17283 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2883 _v) (e2902 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4541 _v) (e4808 _v) p17174 p5255 p8140 p17128 p258 p5008 p17176 p17129 p8602 p17051 p4996 p5006 p17159 p17131 p17172 p16679 p17133 p13951 p17134 p17136 p17157 p16885 p17137 p4999 p5007 p16778 p17141 p4992 p17143 p17050 p17053 p17055 p17056 p17147 p17058 p17060 p17061 p17064 p4995 p17067 p17069 p17138 p17072 p17074 p17076 p4985 p16729 p4988 p17078 p4986 p17080 p17083 p4984 p17087 p17091 p17094 p17093 p17111 p17075 p17115 p17089 p17100 p17098 p17096 p17110 p17102 p17104 p17106 p17108 p4994 p17120 p17113 p17117 p17124 p17122 p17118 p4998 p17065 p5003 p17127 p4983
end
end Assembly
