import Dag241
import generated.th_lemma_32
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n20963 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2296 : (e2296 _v)) (h3158 : (e3158 _v)) (h4306 : (e4306 _v)) (h4439 : (e4439 _v)) (h4459 : (e4459 _v)) (h4567 : (e4567 _v)) (h4653 : (e4653 _v)) (h4679 : (e4679 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6600 : (e6600 _v)) (h6776 : (e6776 _v)) : (e2787 _v) := by
  have p15228 := n15228 _v _q 
  have p20924 := n20924 _v _q h51 h91 h191 h2296 h3158 h4306 h4439 h4459 h4567 h4653 h4679 h4787 h4813 h4838 h6600 h6776
  change (e2787 _v) ∨ (¬ (e7944 _v)) at p15228
  rcases p15228 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p20924))
theorem n20964 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2296 : (e2296 _v)) (h3158 : (e3158 _v)) (h4306 : (e4306 _v)) (h4439 : (e4439 _v)) (h4459 : (e4459 _v)) (h4567 : (e4567 _v)) (h4653 : (e4653 _v)) (h4679 : (e4679 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6600 : (e6600 _v)) (h6776 : (e6776 _v)) : (e7921 _v) := by
  have p16347 := n16347 _v _q 
  have p20862 := n20862 _v _q h51 h91 h191 h2296 h3158 h4306 h4439 h4459 h4567 h4653 h4679 h4787 h4813 h4838 h6600 h6776
  change (e7921 _v) ∨ (e4419 _v) at p16347
  change (¬ (e4419 _v)) at p20862
  rcases p16347 with hlit | hlit
  · exact hlit
  · exact (False.elim (p20862 hlit))
theorem n20965 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2296 : (e2296 _v)) (h3158 : (e3158 _v)) (h4306 : (e4306 _v)) (h4439 : (e4439 _v)) (h4459 : (e4459 _v)) (h4567 : (e4567 _v)) (h4653 : (e4653 _v)) (h4679 : (e4679 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6600 : (e6600 _v)) (h6776 : (e6776 _v)) : (e7489 _v) := by
  have p14855 := n14855 _v _q 
  have p20963 := n20963 _v _q h51 h91 h191 h2296 h3158 h4306 h4439 h4459 h4567 h4653 h4679 h4787 h4813 h4838 h6600 h6776
  have p20964 := n20964 _v _q h51 h91 h191 h2296 h3158 h4306 h4439 h4459 h4567 h4653 h4679 h4787 h4813 h4838 h6600 h6776
  change (¬ (e2787 _v)) ∨ (¬ (e7921 _v)) at p14855
  rcases p14855 with hlit | hlit
  · exact (False.elim (hlit p20963))
  · exact (False.elim (hlit p20964))
theorem n20966 (_v : Vars) (_q : Query _v) (h2781 : (e2781 _v)) (h6549 : (e6549 _v)) : (e8045 _v) := by
  have p15206 := n15206 _v _q 
  have p16090 := n16090 _v _q h2781 h6549
  change (e8049 _v) ∨ (e8045 _v) at p15206
  change (¬ (e8049 _v)) at p16090
  rcases p15206 with hlit | hlit
  · exact (False.elim (p16090 hlit))
  · exact hlit
theorem n20967 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2781 : (e2781 _v)) (h3158 : (e3158 _v)) (h4306 : (e4306 _v)) (h4439 : (e4439 _v)) (h4459 : (e4459 _v)) (h4567 : (e4567 _v)) (h4653 : (e4653 _v)) (h4679 : (e4679 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6549 : (e6549 _v)) (h6630 : (e6630 _v)) : (e3942 _v) := by
  have p20926 := n20926 _v _q 
  have p16091 := n16091 _v _q h2781 h6630
  have p8544 := n8544 _v _q h6549
  have p16003 := n16003 _v _q h2781
  have p20966 := n20966 _v _q h2781 h6549
  have p253 := n253 _v _q h191
  have p17143 := n17143 _v _q h4567
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4989 := n4989 _v _q h4838
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p17070 := n17070 _v _q h4679
  have p16011 := n16011 _v _q h2781
  have p16885 := n16885 _v _q h3158
  have p17075 := n17075 _v _q h4439
  have p15934 := n15934 _v _q h6630
  have p17051 := n17051 _v _q h4459
  have p4999 := n4999 _v _q h91
  change (¬ (e3937 _v)) ∨ (e2296 _v) ∨ (e2303 _v) ∨ (¬ (e4264 _v)) ∨ (¬ (e8045 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e4567 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4679 _v)) ∨ (¬ (e4101 _v)) ∨ (¬ (e3158 _v)) ∨ (¬ (e4439 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4459 _v)) ∨ (¬ (e91 _v)) at p20926
  change (¬ (e2303 _v)) at p16091
  change (¬ (e2296 _v)) at p8544
  rcases p20926 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (p8544 hlit))
  · exact (False.elim (p16091 hlit))
  · exact (False.elim (hlit p16003))
  · exact (False.elim (hlit p20966))
  · exact (False.elim (hlit p253))
  · exact (False.elim (hlit p17143))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p4989))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p17070))
  · exact (False.elim (hlit p16011))
  · exact (False.elim (hlit p16885))
  · exact (False.elim (hlit p17075))
  · exact (False.elim (hlit p15934))
  · exact (False.elim (hlit p17051))
  · exact (False.elim (hlit p4999))
theorem n20968 (_v : Vars) (_q : Query _v) (h6776 : (e6776 _v)) (h7935 : (e7935 _v)) : (e4264 _v) := by
  have p15956 := n15956 _v _q h6776
  have p8601 := n8601 _v _q h6776
  have p17163 := n17163 _v _q h7935
  exact FloorCertificate.node_20968 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) (e2911 _v) (e2995 _v) p15956 p8601 p17163
theorem n20969 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2242 : (e2242 _v)) (h3937 : (e3937 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6549 : (e6549 _v)) (h6776 : (e6776 _v)) (h7807 : (e7807 _v)) (h7935 : (e7935 _v)) : (e8048 _v) := by
  have p20926 := n20926 _v _q 
  have p20968 := n20968 _v _q h6776 h7935
  have p8544 := n8544 _v _q h6549
  have p17065 := n17065 _v _q h4101
  have p4996 := n4996 _v _q h3937
  have p253 := n253 _v _q h191
  have p15946 := n15946 _v _q h2242
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4989 := n4989 _v _q h4838
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p15775 := n15775 _v _q h2242
  have p11350 := n11350 _v _q h7807
  have p15949 := n15949 _v _q h2242
  have p20838 := n20838 _v _q h2242
  have p5008 := n5008 _v _q h4787
  have p15952 := n15952 _v _q h2242
  have p4999 := n4999 _v _q h91
  change (¬ (e3937 _v)) ∨ (e2296 _v) ∨ (e2303 _v) ∨ (¬ (e4264 _v)) ∨ (¬ (e8045 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e4567 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4679 _v)) ∨ (¬ (e4101 _v)) ∨ (¬ (e3158 _v)) ∨ (¬ (e4439 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4459 _v)) ∨ (¬ (e91 _v)) at p20926
  change (¬ (e2296 _v)) at p8544
  change (¬ (e2303 _v)) at p11350
  rcases p20926 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact (False.elim (hlit p4996))
  · exact (False.elim (p8544 hlit))
  · exact (False.elim (p11350 hlit))
  · exact (False.elim (hlit p20968))
  · exact hlit
  · exact (False.elim (hlit p253))
  · exact (False.elim (hlit p15946))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p4989))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p15775))
  · exact (False.elim (hlit p17065))
  · exact (False.elim (hlit p15949))
  · exact (False.elim (hlit p20838))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p15952))
  · exact (False.elim (hlit p4999))
theorem n20970 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2242 : (e2242 _v)) (h2733 : (e2733 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6571 : (e6571 _v)) (h6776 : (e6776 _v)) (h7814 : (e7814 _v)) : (e8029 _v) := by
  have p16307 := n16307 _v _q 
  have p20864 := n20864 _v _q h51 h91 h191 h2242 h2733 h3152 h3937 h4306 h4653 h4787 h4813 h4838 h6571 h6776 h7814
  change (e8029 _v) ∨ (e4546 _v) at p16307
  change (¬ (e4546 _v)) at p20864
  rcases p16307 with hlit | hlit
  · exact hlit
  · exact (False.elim (p20864 hlit))
theorem n20971 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2242 : (e2242 _v)) (h2733 : (e2733 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6571 : (e6571 _v)) (h6776 : (e6776 _v)) (h7814 : (e7814 _v)) : (e8038 _v) := by
  have p14871 := n14871 _v _q 
  have p20970 := n20970 _v _q h51 h91 h191 h2242 h2733 h3152 h3937 h4306 h4653 h4787 h4813 h4838 h6571 h6776 h7814
  change (¬ (e2475 _v)) ∨ (¬ (e8029 _v)) at p14871
  rcases p14871 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p20970))
theorem n20972 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2242 : (e2242 _v)) (h2733 : (e2733 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6571 : (e6571 _v)) (h6776 : (e6776 _v)) (h7814 : (e7814 _v)) : (e7489 _v) := by
  have p15207 := n15207 _v _q 
  have p20971 := n20971 _v _q h51 h91 h191 h2242 h2733 h3152 h3937 h4306 h4653 h4787 h4813 h4838 h6571 h6776 h7814
  have p20927 := n20927 _v _q h51 h91 h191 h2242 h2733 h3152 h3937 h4306 h4653 h4787 h4813 h4838 h6571 h6776 h7814
  change (e2475 _v) ∨ (¬ (e8049 _v)) at p15207
  change (¬ (e2475 _v)) at p20971
  rcases p15207 with hlit | hlit
  · exact (False.elim (p20971 hlit))
  · exact (False.elim (hlit p20927))
theorem n20973 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2242 : (e2242 _v)) (h2303 : (e2303 _v)) (h3152 : (e3152 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6600 : (e6600 _v)) (h8045 : (e8045 _v)) : (e7935 _v) := by
  have p15266 := n15266 _v _q 
  have p20939 := n20939 _v _q h51 h91 h191 h2242 h2303 h3152 h4096 h4139 h4260 h4306 h4653 h4787 h4813 h4838 h6600 h8045
  change (e7944 _v) ∨ (e7935 _v) at p15266
  change (¬ (e7944 _v)) at p20939
  rcases p15266 with hlit | hlit
  · exact (False.elim (p20939 hlit))
  · exact hlit
theorem n20974 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2242 : (e2242 _v)) (h2303 : (e2303 _v)) (h3152 : (e3152 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6600 : (e6600 _v)) (h8045 : (e8045 _v)) : (e7489 _v) := by
  have p10893 := n10893 _v _q 
  have p8448 := n8448 _v _q h2303
  have p4016 := n4016 _v _q 
  have p20973 := n20973 _v _q h51 h91 h191 h2242 h2303 h3152 h4096 h4139 h4260 h4306 h4653 h4787 h4813 h4838 h6600 h8045
  have p16913 := n16913 _v _q 
  have p17147 := n17147 _v _q 
  have p15907 := n15907 _v _q h6600
  have p4981 := n4981 _v _q h4260
  have p4979 := n4979 _v _q h4139
  have p17104 := n17104 _v _q 
  have p17874 := n17874 _v _q 
  have p17127 := n17127 _v _q 
  have p17089 := n17089 _v _q 
  have p4998 := n4998 _v _q h3152
  have p16436 := n16436 _v _q h2303
  have p13951 := n13951 _v _q 
  have p17157 := n17157 _v _q h8045
  have p253 := n253 _v _q h191
  have p15946 := n15946 _v _q h2242
  have p17020 := n17020 _v _q 
  have p8439 := n8439 _v _q h6600
  have p17138 := n17138 _v _q h4306
  have p20274 := n20274 _v _q 
  have p17060 := n17060 _v _q h4653
  have p20470 := n20470 _v _q 
  have p4989 := n4989 _v _q h4838
  have p17050 := n17050 _v _q 
  have p16778 := n16778 _v _q 
  have p17122 := n17122 _v _q 
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p20829 := n20829 _v _q 
  have p15775 := n15775 _v _q h2242
  have p20426 := n20426 _v _q 
  have p20126 := n20126 _v _q 
  have p17110 := n17110 _v _q 
  have p17053 := n17053 _v _q 
  have p20096 := n20096 _v _q 
  have p17131 := n17131 _v _q 
  have p17108 := n17108 _v _q 
  have p17294 := n17294 _v _q 
  have p16943 := n16943 _v _q 
  have p17058 := n17058 _v _q 
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
  have p17055 := n17055 _v _q 
  have p17093 := n17093 _v _q 
  have p17091 := n17091 _v _q 
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p15949 := n15949 _v _q h2242
  have p20838 := n20838 _v _q h2242
  have p17141 := n17141 _v _q 
  have p17100 := n17100 _v _q 
  have p19610 := n19610 _v _q 
  have p17102 := n17102 _v _q 
  have p5008 := n5008 _v _q h4787
  have p15952 := n15952 _v _q h2242
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
  have p5001 := n5001 _v _q h4096
  have p12927 := n12927 _v _q h2242
  have p8553 := n8553 _v _q h2242
  exact FloorCertificate.node_20974 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2883 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4541 _v) (e4808 _v) p10893 p8448 p4016 p20973 p16913 p17147 p15907 p4981 p4979 p17104 p17874 p17127 p17089 p4998 p16436 p13951 p17157 p253 p15946 p17020 p8439 p17138 p20274 p17060 p20470 p4989 p17050 p16778 p17122 p4983 p16729 p20829 p15775 p20426 p20126 p17110 p17053 p20096 p17131 p17108 p17294 p16943 p17058 p17064 p17067 p17080 p17072 p17074 p17069 p20461 p20836 p20653 p17078 p17136 p17087 p17083 p17055 p17093 p17091 p17098 p17106 p15949 p20838 p17141 p17100 p19610 p17102 p5008 p15952 p17096 p17115 p17758 p17124 p17111 p19665 p17113 p17117 p20467 p17120 p4999 p17133 p5001 p12927 p8553
theorem n20975 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2242 : (e2242 _v)) (h3152 : (e3152 _v)) (h4096 : (e4096 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6600 : (e6600 _v)) (h6776 : (e6776 _v)) (h8038 : (e8038 _v)) : (e7640 _v) := by
  have p14828 := n14828 _v _q 
  have p20940 := n20940 _v _q h51 h91 h191 h2242 h3152 h4096 h4306 h4653 h4787 h4813 h4838 h6600 h6776 h8038
  change (¬ (e2358 _v)) ∨ (¬ (e7634 _v)) at p14828
  rcases p14828 with hlit | hlit
  · exact (False.elim (hlit p20940))
  · exact hlit
theorem n20976 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2242 : (e2242 _v)) (h3152 : (e3152 _v)) (h4096 : (e4096 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6600 : (e6600 _v)) (h6776 : (e6776 _v)) (h8038 : (e8038 _v)) : (e4139 _v) := by
  have p16281 := n16281 _v _q 
  have p20975 := n20975 _v _q h51 h91 h191 h2242 h3152 h4096 h4306 h4653 h4787 h4813 h4838 h6600 h6776 h8038
  change (e7634 _v) ∨ (e4139 _v) at p16281
  change (¬ (e7634 _v)) at p20975
  rcases p16281 with hlit | hlit
  · exact (False.elim (p20975 hlit))
  · exact hlit
theorem n20977 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4434 : (e4434 _v)) (h4562 : (e4562 _v)) (h4608 : (e4608 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h5100 : (e5100 _v)) (h5145 : (e5145 _v)) (h6750 : (e6750 _v)) (h7749 : (e7749 _v)) (h7814 : (e7814 _v)) (h7935 : (e7935 _v)) (h8045 : (e8045 _v)) (h8317 : (e8317 _v)) : (e191 _v) := by
  have p16442 := n16442 _v _q 
  have p20942 := n20942 _v _q h51 h3152 h3937 h4260 h4306 h4434 h4562 h4608 h4653 h4675 h4787 h4813 h5100 h5145 h6750 h7749 h7814 h7935 h8045 h8317
  change (e5193 _v) ∨ (e191 _v) at p16442
  change (¬ (e5193 _v)) at p20942
  rcases p16442 with hlit | hlit
  · exact (False.elim (p20942 hlit))
  · exact hlit
theorem n20978 (_v : Vars) (_q : Query _v) (h6423 : (e6423 _v)) (h6583 : (e6583 _v)) : (e8045 _v) := by
  have p15206 := n15206 _v _q 
  have p20898 := n20898 _v _q h6423 h6583
  change (e8049 _v) ∨ (e8045 _v) at p15206
  change (¬ (e8049 _v)) at p20898
  rcases p15206 with hlit | hlit
  · exact (False.elim (p20898 hlit))
  · exact hlit
theorem n20979 (_v : Vars) (_q : Query _v) (h6423 : (e6423 _v)) (h6583 : (e6583 _v)) : (e7935 _v) := by
  have p15266 := n15266 _v _q 
  have p20945 := n20945 _v _q h6423 h6583
  change (e7944 _v) ∨ (e7935 _v) at p15266
  change (¬ (e7944 _v)) at p20945
  rcases p15266 with hlit | hlit
  · exact (False.elim (p20945 hlit))
  · exact hlit
theorem n20980 (_v : Vars) (_q : Query _v) (h4260 : (e4260 _v)) (h6423 : (e6423 _v)) (h6583 : (e6583 _v)) : (e75 _v) := by
  have p20897 := n20897 _v _q 
  have p20895 := n20895 _v _q h6423 h6583
  have p20978 := n20978 _v _q h6423 h6583
  have p15967 := n15967 _v _q h6423
  have p20947 := n20947 _v _q h6423 h6583
  have p16658 := n16658 _v _q h6423
  have p16660 := n16660 _v _q h6423
  have p20893 := n20893 _v _q h6423 h6583
  have p15379 := n15379 _v _q h6423
  have p20979 := n20979 _v _q h6423 h6583
  have p15964 := n15964 _v _q h6423
  have p20901 := n20901 _v _q h6423 h6583
  have p16396 := n16396 _v _q h6423
  have p4981 := n4981 _v _q h4260
  have p16657 := n16657 _v _q h6423
  have p20902 := n20902 _v _q h6423 h6583
  have p11340 := n11340 _v _q h6583
  have p16659 := n16659 _v _q h6423
  change (¬ (e8317 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e8045 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e7493 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e70 _v)) ∨ (e2303 _v) ∨ (¬ (e4562 _v)) ∨ (¬ (e7935 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e5145 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e3937 _v)) ∨ (e13 _v) ∨ (e2364 _v) ∨ (¬ (e4813 _v)) at p20897
  change (¬ (e2303 _v)) at p20893
  change (¬ (e13 _v)) at p20902
  change (¬ (e2364 _v)) at p11340
  rcases p20897 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact (False.elim (hlit p20895))
  · exact (False.elim (hlit p16660))
  · exact (False.elim (hlit p20978))
  · exact (False.elim (hlit p15967))
  · exact (False.elim (hlit p20947))
  · exact (False.elim (hlit p16658))
  · exact hlit
  · exact (False.elim (p20893 hlit))
  · exact (False.elim (hlit p15379))
  · exact (False.elim (hlit p20979))
  · exact (False.elim (hlit p15964))
  · exact (False.elim (hlit p20901))
  · exact (False.elim (hlit p16396))
  · exact (False.elim (hlit p4981))
  · exact (False.elim (hlit p16657))
  · exact (False.elim (p20902 hlit))
  · exact (False.elim (p11340 hlit))
  · exact (False.elim (hlit p16659))
theorem n20981 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h3152 : (e3152 _v)) (h4260 : (e4260 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h6454 : (e6454 _v)) : (e7754 _v) := by
  have p14942 := n14942 _v _q 
  have p20953 := n20953 _v _q h91 h3152 h4260 h4675 h4787 h4813 h6454
  change (e2132 _v) ∨ (¬ (e7753 _v)) at p14942
  change (¬ (e2132 _v)) at p20953
  rcases p14942 with hlit | hlit
  · exact (False.elim (p20953 hlit))
  · exact hlit
theorem n20982 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h3152 : (e3152 _v)) (h4260 : (e4260 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h6454 : (e6454 _v)) : (e7749 _v) := by
  have p14941 := n14941 _v _q 
  have p20981 := n20981 _v _q h91 h3152 h4260 h4675 h4787 h4813 h6454
  change (e7753 _v) ∨ (e7749 _v) at p14941
  change (¬ (e7753 _v)) at p20981
  rcases p14941 with hlit | hlit
  · exact (False.elim (p20981 hlit))
  · exact hlit
theorem n20983 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h3152 : (e3152 _v)) (h4260 : (e4260 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h6454 : (e6454 _v)) : (e5105 _v) := by
  have p15204 := n15204 _v _q 
  have p20956 := n20956 _v _q h91 h3152 h4260 h4675 h4787 h4813 h6454
  change (e13 _v) ∨ (¬ (e5104 _v)) at p15204
  change (¬ (e13 _v)) at p20956
  rcases p15204 with hlit | hlit
  · exact (False.elim (p20956 hlit))
  · exact hlit
theorem n20984 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h3152 : (e3152 _v)) (h4260 : (e4260 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h6454 : (e6454 _v)) : (e5100 _v) := by
  have p15319 := n15319 _v _q 
  have p20983 := n20983 _v _q h91 h3152 h4260 h4675 h4787 h4813 h6454
  change (e5104 _v) ∨ (e5100 _v) at p15319
  change (¬ (e5104 _v)) at p20983
  rcases p15319 with hlit | hlit
  · exact (False.elim (p20983 hlit))
  · exact hlit
theorem n20985 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2468 : (e2468 _v)) (h3152 : (e3152 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4679 : (e4679 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6750 : (e6750 _v)) : (e6772 _v) := by
  have p14855 := n14855 _v _q 
  have p20958 := n20958 _v _q h51 h91 h191 h2468 h3152 h4306 h4653 h4679 h4813 h4838 h6750
  change (¬ (e2787 _v)) ∨ (¬ (e7921 _v)) at p14855
  rcases p14855 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p20958))
theorem n20986 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2468 : (e2468 _v)) (h3152 : (e3152 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4679 : (e4679 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6750 : (e6750 _v)) : (e7945 _v) := by
  have p15228 := n15228 _v _q 
  have p20985 := n20985 _v _q h51 h91 h191 h2468 h3152 h4306 h4653 h4679 h4813 h4838 h6750
  change (e2787 _v) ∨ (¬ (e7944 _v)) at p15228
  change (¬ (e2787 _v)) at p20985
  rcases p15228 with hlit | hlit
  · exact (False.elim (p20985 hlit))
  · exact hlit
theorem n20987 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2468 : (e2468 _v)) (h3152 : (e3152 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4679 : (e4679 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6750 : (e6750 _v)) : (e7935 _v) := by
  have p15266 := n15266 _v _q 
  have p20986 := n20986 _v _q h51 h91 h191 h2468 h3152 h4306 h4653 h4679 h4813 h4838 h6750
  change (e7944 _v) ∨ (e7935 _v) at p15266
  change (¬ (e7944 _v)) at p20986
  rcases p15266 with hlit | hlit
  · exact (False.elim (p20986 hlit))
  · exact hlit
theorem n20988 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2242 : (e2242 _v)) (h2402 : (e2402 _v)) (h4101 : (e4101 _v)) (h4139 : (e4139 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4546 : (e4546 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6549 : (e6549 _v)) (h7807 : (e7807 _v)) : (e7935 _v) := by
  have p15266 := n15266 _v _q 
  have p20960 := n20960 _v _q h51 h91 h191 h2242 h2402 h4101 h4139 h4260 h4306 h4546 h4653 h4787 h4813 h4838 h6549 h7807
  change (e7944 _v) ∨ (e7935 _v) at p15266
  change (¬ (e7944 _v)) at p20960
  rcases p15266 with hlit | hlit
  · exact (False.elim (p20960 hlit))
  · exact hlit
theorem n20989 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2242 : (e2242 _v)) (h2402 : (e2402 _v)) (h4101 : (e4101 _v)) (h4139 : (e4139 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4546 : (e4546 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6549 : (e6549 _v)) (h7807 : (e7807 _v)) : (e7489 _v) := by
  have p4946 := n4946 _v _q 
  have p13951 := n13951 _v _q 
  have p4016 := n4016 _v _q 
  have p4976 := n4976 _v _q h4546
  have p8544 := n8544 _v _q h6549
  have p17111 := n17111 _v _q 
  have p20988 := n20988 _v _q h51 h91 h191 h2242 h2402 h4101 h4139 h4260 h4306 h4546 h4653 h4787 h4813 h4838 h6549 h7807
  have p17124 := n17124 _v _q 
  have p4979 := n4979 _v _q h4139
  have p15373 := n15373 _v _q h7807
  have p17113 := n17113 _v _q 
  have p17117 := n17117 _v _q 
  have p20467 := n20467 _v _q 
  have p14799 := n14799 _v _q h2402
  have p17065 := n17065 _v _q h4101
  have p19665 := n19665 _v _q 
  have p17133 := n17133 _v _q 
  have p17120 := n17120 _v _q 
  have p4981 := n4981 _v _q h4260
  have p17104 := n17104 _v _q 
  have p17874 := n17874 _v _q 
  have p17127 := n17127 _v _q 
  have p17089 := n17089 _v _q 
  have p15778 := n15778 _v _q h6549
  have p4999 := n4999 _v _q h91
  have p253 := n253 _v _q h191
  have p15946 := n15946 _v _q h2242
  have p17020 := n17020 _v _q 
  have p17138 := n17138 _v _q h4306
  have p20274 := n20274 _v _q 
  have p17060 := n17060 _v _q h4653
  have p20470 := n20470 _v _q 
  have p4989 := n4989 _v _q h4838
  have p17050 := n17050 _v _q 
  have p16778 := n16778 _v _q 
  have p17122 := n17122 _v _q 
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p20829 := n20829 _v _q 
  have p15775 := n15775 _v _q h2242
  have p20426 := n20426 _v _q 
  have p20126 := n20126 _v _q 
  have p17110 := n17110 _v _q 
  have p17053 := n17053 _v _q 
  have p20096 := n20096 _v _q 
  have p17131 := n17131 _v _q 
  have p17108 := n17108 _v _q 
  have p17294 := n17294 _v _q 
  have p16943 := n16943 _v _q 
  have p17058 := n17058 _v _q 
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
  have p17055 := n17055 _v _q 
  have p17093 := n17093 _v _q 
  have p17091 := n17091 _v _q 
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p15949 := n15949 _v _q h2242
  have p20838 := n20838 _v _q h2242
  have p17141 := n17141 _v _q 
  have p17100 := n17100 _v _q 
  have p19610 := n19610 _v _q 
  have p17102 := n17102 _v _q 
  have p5008 := n5008 _v _q h4787
  have p15952 := n15952 _v _q h2242
  have p17096 := n17096 _v _q 
  have p17115 := n17115 _v _q 
  have p17758 := n17758 _v _q 
  exact FloorCertificate.node_20989 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2902 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4541 _v) (e4808 _v) p4946 p13951 p4016 p4976 p8544 p17111 p20988 p17124 p4979 p15373 p17113 p17117 p20467 p14799 p17065 p19665 p17133 p17120 p4981 p17104 p17874 p17127 p17089 p15778 p4999 p253 p15946 p17020 p17138 p20274 p17060 p20470 p4989 p17050 p16778 p17122 p4983 p16729 p20829 p15775 p20426 p20126 p17110 p17053 p20096 p17131 p17108 p17294 p16943 p17058 p17064 p17067 p17080 p17072 p17074 p17069 p20461 p20836 p20653 p17078 p17136 p17087 p17083 p17055 p17093 p17091 p17098 p17106 p15949 p20838 p17141 p17100 p19610 p17102 p5008 p15952 p17096 p17115 p17758
theorem n20990 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2242 : (e2242 _v)) (h2402 : (e2402 _v)) (h3152 : (e3152 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6776 : (e6776 _v)) (h7935 : (e7935 _v)) (h8038 : (e8038 _v)) : (e4285 _v) := by
  have p16274 := n16274 _v _q 
  have p20962 := n20962 _v _q h51 h91 h191 h2242 h2402 h3152 h4101 h4306 h4653 h4787 h4813 h4838 h6776 h7935 h8038
  change (e7798 _v) ∨ (e4285 _v) at p16274
  change (¬ (e7798 _v)) at p20962
  rcases p16274 with hlit | hlit
  · exact (False.elim (p20962 hlit))
  · exact hlit
theorem n20992 (_v : Vars) (_q : Query _v)  : (e20991 _v) := by
  by_contra hc
  change ¬ ((e2402 _v) ∨ (¬ (e2296 _v)) ∨ (e2781 _v) ∨ (¬ (e191 _v)) ∨ (¬ (e4567 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4679 _v)) ∨ (¬ (e3158 _v)) ∨ (¬ (e4439 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4459 _v)) ∨ (¬ (e91 _v))) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))))))))))))
  have h191 : (e191 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h2296 : (e2296 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h3158 : (e3158 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h4439 : (e4439 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h4459 : (e4459 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h4567 : (e4567 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h4679 : (e4679 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h4838 : (e4838 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h6600 : (e6600 _v) := (fun hn => hc (Or.inl hn))
  have h6776 : (e6776 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have p20965 := n20965 _v _q h51 h91 h191 h2296 h3158 h4306 h4439 h4459 h4567 h4653 h4679 h4787 h4813 h4838 h6600 h6776
  exact p20965
theorem n20993 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2781 : (e2781 _v)) (h3158 : (e3158 _v)) (h4306 : (e4306 _v)) (h4439 : (e4439 _v)) (h4459 : (e4459 _v)) (h4567 : (e4567 _v)) (h4653 : (e4653 _v)) (h4679 : (e4679 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6549 : (e6549 _v)) (h6630 : (e6630 _v)) : (e7415 _v) := by
  have p15012 := n15012 _v _q 
  have p20967 := n20967 _v _q h51 h91 h191 h2781 h3158 h4306 h4439 h4459 h4567 h4653 h4679 h4813 h4838 h6549 h6630
  change (e7415 _v) ∨ (e3937 _v) at p15012
  change (¬ (e3937 _v)) at p20967
  rcases p15012 with hlit | hlit
  · exact hlit
  · exact (False.elim (p20967 hlit))
theorem n20994 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2781 : (e2781 _v)) (h3158 : (e3158 _v)) (h4306 : (e4306 _v)) (h4439 : (e4439 _v)) (h4459 : (e4459 _v)) (h4567 : (e4567 _v)) (h4653 : (e4653 _v)) (h4679 : (e4679 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6549 : (e6549 _v)) (h6630 : (e6630 _v)) : (e2402 _v) := by
  have p14534 := n14534 _v _q 
  have p20993 := n20993 _v _q h51 h91 h191 h2781 h3158 h4306 h4439 h4459 h4567 h4653 h4679 h4813 h4838 h6549 h6630
  change (e2402 _v) ∨ (¬ (e7415 _v)) at p14534
  rcases p14534 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p20993))
theorem n20995 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2781 : (e2781 _v)) (h3158 : (e3158 _v)) (h4306 : (e4306 _v)) (h4439 : (e4439 _v)) (h4459 : (e4459 _v)) (h4567 : (e4567 _v)) (h4653 : (e4653 _v)) (h4679 : (e4679 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6549 : (e6549 _v)) (h6630 : (e6630 _v)) : (e3929 _v) := by
  have p14484 := n14484 _v _q 
  have p20994 := n20994 _v _q h51 h91 h191 h2781 h3158 h4306 h4439 h4459 h4567 h4653 h4679 h4813 h4838 h6549 h6630
  change (¬ (e2402 _v)) ∨ (¬ (e3923 _v)) at p14484
  rcases p14484 with hlit | hlit
  · exact (False.elim (hlit p20994))
  · exact hlit
theorem n20996 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2242 : (e2242 _v)) (h3937 : (e3937 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6549 : (e6549 _v)) (h6776 : (e6776 _v)) (h7807 : (e7807 _v)) (h7935 : (e7935 _v)) : (e8049 _v) := by
  have p15206 := n15206 _v _q 
  have p20969 := n20969 _v _q h51 h91 h191 h2242 h3937 h4101 h4306 h4653 h4787 h4813 h4838 h6549 h6776 h7807 h7935
  change (e8049 _v) ∨ (e8045 _v) at p15206
  change (¬ (e8045 _v)) at p20969
  rcases p15206 with hlit | hlit
  · exact hlit
  · exact (False.elim (p20969 hlit))
theorem n20998 (_v : Vars) (_q : Query _v)  : (e20997 _v) := by
  by_contra hc
  change ¬ ((e2358 _v) ∨ (¬ (e91 _v)) ∨ (e2781 _v) ∨ (¬ (e3152 _v)) ∨ (¬ (e7814 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e2242 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e2733 _v))) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h191 : (e191 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h2242 : (e2242 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h2733 : (e2733 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn)))))))))))))))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h4838 : (e4838 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h6571 : (e6571 _v) := (fun hn => hc (Or.inl hn))
  have h6776 : (e6776 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h7814 : (e7814 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have p20972 := n20972 _v _q h51 h91 h191 h2242 h2733 h3152 h3937 h4306 h4653 h4787 h4813 h4838 h6571 h6776 h7814
  exact p20972
theorem n21000 (_v : Vars) (_q : Query _v)  : (e20999 _v) := by
  by_contra hc
  change ¬ ((¬ (e2303 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e8045 _v)) ∨ (¬ (e191 _v)) ∨ (e2402 _v) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e2242 _v))) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h191 : (e191 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h2242 : (e2242 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))))))))))))
  have h2303 : (e2303 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4096 : (e4096 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h4139 : (e4139 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4260 : (e4260 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h4838 : (e4838 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h6600 : (e6600 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h8045 : (e8045 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have p20974 := n20974 _v _q h51 h91 h191 h2242 h2303 h3152 h4096 h4139 h4260 h4306 h4653 h4787 h4813 h4838 h6600 h8045
  exact p20974
theorem n21001 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h225 : (e225 _v)) (h2364 : (e2364 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4434 : (e4434 _v)) (h4562 : (e4562 _v)) (h4608 : (e4608 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h5100 : (e5100 _v)) (h5145 : (e5145 _v)) (h6750 : (e6750 _v)) (h7749 : (e7749 _v)) (h7814 : (e7814 _v)) (h7935 : (e7935 _v)) (h8045 : (e8045 _v)) (h8317 : (e8317 _v)) : (e7489 _v) := by
  have p8663 := n8663 _v _q 
  have p4016 := n4016 _v _q 
  have p5007 := n5007 _v _q h225
  have p4987 := n4987 _v _q h4434
  have p4996 := n4996 _v _q h3937
  have p20977 := n20977 _v _q h51 h3152 h3937 h4260 h4306 h4434 h4562 h4608 h4653 h4675 h4787 h4813 h5100 h5145 h6750 h7749 h7814 h7935 h8045 h8317
  have p16576 := n16576 _v _q 
  have p17147 := n17147 _v _q 
  have p16394 := n16394 _v _q 
  have p16977 := n16977 _v _q 
  have p8527 := n8527 _v _q h2364
  have p16729 := n16729 _v _q h51
  have p17256 := n17256 _v _q 
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p17163 := n17163 _v _q h7935
  have p13951 := n13951 _v _q 
  have p17174 := n17174 _v _q h8317
  have p4983 := n4983 _v _q h4813
  have p16269 := n16269 _v _q h7749
  have p17157 := n17157 _v _q h8045
  have p17172 := n17172 _v _q h7814
  have p4998 := n4998 _v _q h3152
  have p20829 := n20829 _v _q 
  have p17108 := n17108 _v _q 
  have p20461 := n20461 _v _q 
  have p4981 := n4981 _v _q h4260
  have p20426 := n20426 _v _q 
  have p5006 := n5006 _v _q h4675
  have p20126 := n20126 _v _q 
  have p17110 := n17110 _v _q 
  have p17009 := n17009 _v _q 
  have p17053 := n17053 _v _q 
  have p17131 := n17131 _v _q 
  have p17159 := n17159 _v _q h5100
  have p20096 := n20096 _v _q 
  have p17058 := n17058 _v _q 
  have p17294 := n17294 _v _q 
  have p16943 := n16943 _v _q 
  have p17064 := n17064 _v _q 
  have p4991 := n4991 _v _q h4608
  have p15940 := n15940 _v _q h6750
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
  have p17091 := n17091 _v _q 
  have p17093 := n17093 _v _q 
  have p17141 := n17141 _v _q 
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p17102 := n17102 _v _q 
  have p17100 := n17100 _v _q 
  have p19610 := n19610 _v _q 
  have p16929 := n16929 _v _q 
  have p17122 := n17122 _v _q 
  have p17096 := n17096 _v _q 
  have p17245 := n17245 _v _q h5145
  have p4973 := n4973 _v _q h4562
  have p17758 := n17758 _v _q 
  have p5008 := n5008 _v _q h4787
  have p19665 := n19665 _v _q 
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
  have p20274 := n20274 _v _q 
  have p20470 := n20470 _v _q 
  have p17133 := n17133 _v _q 
  have p17089 := n17089 _v _q 
  have p8420 := n8420 _v _q h6750
  exact FloorCertificate.node_21001 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2834 _v) (e2849 _v) (e2863 _v) (e2877 _v) (e2883 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p8663 p4016 p5007 p4987 p4996 p20977 p16576 p17147 p16394 p16977 p8527 p16729 p17256 p17138 p17060 p17163 p13951 p17174 p4983 p16269 p17157 p17172 p4998 p20829 p17108 p20461 p4981 p20426 p5006 p20126 p17110 p17009 p17053 p17131 p17159 p20096 p17058 p17294 p16943 p17064 p4991 p15940 p17067 p17069 p17080 p17072 p17083 p17074 p20836 p17078 p20653 p17087 p17136 p17055 p17091 p17093 p17141 p17098 p17106 p17102 p17100 p19610 p16929 p17122 p17096 p17245 p4973 p17758 p5008 p19665 p17115 p17120 p17111 p17124 p17050 p16778 p17113 p17117 p20467 p17104 p17874 p17127 p20274 p20470 p17133 p17089 p8420
theorem n21002 (_v : Vars) (_q : Query _v) (h4260 : (e4260 _v)) (h6423 : (e6423 _v)) (h6583 : (e6583 _v)) : (e5118 _v) := by
  have p15648 := n15648 _v _q 
  have p20980 := n20980 _v _q h4260 h6423 h6583
  change (e5118 _v) ∨ (e70 _v) at p15648
  change (¬ (e70 _v)) at p20980
  rcases p15648 with hlit | hlit
  · exact hlit
  · exact (False.elim (p20980 hlit))
theorem n21003 (_v : Vars) (_q : Query _v) (h4260 : (e4260 _v)) (h6423 : (e6423 _v)) (h6583 : (e6583 _v)) : (e48 _v) := by
  have p14487 := n14487 _v _q 
  have p21002 := n21002 _v _q h4260 h6423 h6583
  change (e48 _v) ∨ (¬ (e5118 _v)) at p14487
  rcases p14487 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p21002))
theorem n21004 (_v : Vars) (_q : Query _v) (h4260 : (e4260 _v)) (h6423 : (e6423 _v)) (h6583 : (e6583 _v)) : (e60 _v) := by
  have p14152 := n14152 _v _q 
  have p21003 := n21003 _v _q h4260 h6423 h6583
  change (¬ (e48 _v)) ∨ (¬ (e59 _v)) at p14152
  rcases p14152 with hlit | hlit
  · exact (False.elim (hlit p21003))
  · exact hlit
theorem n21005 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2468 : (e2468 _v)) (h3152 : (e3152 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4679 : (e4679 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6750 : (e6750 _v)) : (e7489 _v) := by
  have p16874 := n16874 _v _q h2468 h6750
  have p4016 := n4016 _v _q 
  have p20987 := n20987 _v _q h51 h91 h191 h2468 h3152 h4306 h4653 h4679 h4813 h4838 h6750
  have p17124 := n17124 _v _q 
  have p8420 := n8420 _v _q h6750
  have p16913 := n16913 _v _q 
  have p8438 := n8438 _v _q h2468
  have p17113 := n17113 _v _q 
  have p16067 := n16067 _v _q h2468
  have p17117 := n17117 _v _q 
  have p20467 := n20467 _v _q 
  have p16875 := n16875 _v _q h2468 h6750
  have p5391 := n5391 _v _q 
  have p4999 := n4999 _v _q h91
  have p17070 := n17070 _v _q h4679
  have p17133 := n17133 _v _q 
  have p15940 := n15940 _v _q h6750
  have p17104 := n17104 _v _q 
  have p17127 := n17127 _v _q 
  have p17089 := n17089 _v _q 
  have p20470 := n20470 _v _q 
  have p253 := n253 _v _q h191
  have p17020 := n17020 _v _q 
  have p20274 := n20274 _v _q 
  have p15104 := n15104 _v _q h2468
  have p20855 := n20855 _v _q h2468
  have p16729 := n16729 _v _q h51
  have p17050 := n17050 _v _q 
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4989 := n4989 _v _q h4838
  have p4983 := n4983 _v _q h4813
  have p16062 := n16062 _v _q h2468
  have p16859 := n16859 _v _q h2468
  have p16778 := n16778 _v _q 
  have p4998 := n4998 _v _q h3152
  have p20829 := n20829 _v _q 
  have p17108 := n17108 _v _q 
  have p20461 := n20461 _v _q 
  have p16699 := n16699 _v _q h6750
  have p20426 := n20426 _v _q 
  have p20126 := n20126 _v _q 
  have p17110 := n17110 _v _q 
  have p17009 := n17009 _v _q 
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
  have p17091 := n17091 _v _q 
  have p17093 := n17093 _v _q 
  have p17141 := n17141 _v _q 
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p17102 := n17102 _v _q 
  have p17100 := n17100 _v _q 
  have p19610 := n19610 _v _q 
  have p17122 := n17122 _v _q 
  have p17096 := n17096 _v _q 
  have p13951 := n13951 _v _q 
  have p17874 := n17874 _v _q 
  have p17758 := n17758 _v _q 
  have p15073 := n15073 _v _q h2468
  have p19665 := n19665 _v _q 
  have p17115 := n17115 _v _q 
  have p17120 := n17120 _v _q 
  have p17111 := n17111 _v _q 
  have p20985 := n20985 _v _q h51 h91 h191 h2468 h3152 h4306 h4653 h4679 h4813 h4838 h6750
  exact FloorCertificate.node_21005 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4808 _v) p16874 p4016 p20987 p17124 p8420 p16913 p8438 p17113 p16067 p17117 p20467 p16875 p5391 p4999 p17070 p17133 p15940 p17104 p17127 p17089 p20470 p253 p17020 p20274 p15104 p20855 p16729 p17050 p17138 p17060 p4989 p4983 p16062 p16859 p16778 p4998 p20829 p17108 p20461 p16699 p20426 p20126 p17110 p17009 p17053 p17131 p20096 p17058 p17294 p16943 p17064 p17067 p17069 p17080 p17072 p17083 p17074 p20836 p17078 p20653 p17087 p17136 p17055 p17091 p17093 p17141 p17098 p17106 p17102 p17100 p19610 p17122 p17096 p13951 p17874 p17758 p15073 p19665 p17115 p17120 p17111 p20985
theorem n21007 (_v : Vars) (_q : Query _v)  : (e21006 _v) := by
  by_contra hc
  change ¬ ((e2303 _v) ∨ (¬ (e4546 _v)) ∨ (e2296 _v) ∨ (¬ (e4139 _v)) ∨ (¬ (e4101 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e2402 _v)) ∨ (¬ (e2242 _v))) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h191 : (e191 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h2242 : (e2242 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))))))))))))
  have h2402 : (e2402 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h4101 : (e4101 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4139 : (e4139 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4260 : (e4260 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h4546 : (e4546 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h4838 : (e4838 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h6549 : (e6549 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h7807 : (e7807 _v) := (fun hn => hc (Or.inl hn))
  have p20989 := n20989 _v _q h51 h91 h191 h2242 h2402 h4101 h4139 h4260 h4306 h4546 h4653 h4787 h4813 h4838 h6549 h7807
  exact p20989
theorem n21008 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2242 : (e2242 _v)) (h2402 : (e2402 _v)) (h3152 : (e3152 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6776 : (e6776 _v)) (h7935 : (e7935 _v)) (h8038 : (e8038 _v)) : (e7489 _v) := by
  have p13951 := n13951 _v _q 
  have p12927 := n12927 _v _q h2242
  have p4016 := n4016 _v _q 
  have p8553 := n8553 _v _q h2242
  have p8601 := n8601 _v _q h6776
  have p20990 := n20990 _v _q h51 h91 h191 h2242 h2402 h3152 h4101 h4306 h4653 h4787 h4813 h4838 h6776 h7935 h8038
  have p16882 := n16882 _v _q h2402 h6776
  have p15209 := n15209 _v _q h8038
  have p258 := n258 _v _q 
  have p17113 := n17113 _v _q 
  have p17117 := n17117 _v _q 
  have p20467 := n20467 _v _q 
  have p14799 := n14799 _v _q h2402
  have p17065 := n17065 _v _q h4101
  have p19665 := n19665 _v _q 
  have p17133 := n17133 _v _q 
  have p17120 := n17120 _v _q 
  have p15956 := n15956 _v _q h6776
  have p17104 := n17104 _v _q 
  have p17874 := n17874 _v _q 
  have p17127 := n17127 _v _q 
  have p17089 := n17089 _v _q 
  have p4998 := n4998 _v _q h3152
  have p4999 := n4999 _v _q h91
  have p253 := n253 _v _q h191
  have p15946 := n15946 _v _q h2242
  have p17020 := n17020 _v _q 
  have p17138 := n17138 _v _q h4306
  have p20274 := n20274 _v _q 
  have p17060 := n17060 _v _q h4653
  have p20470 := n20470 _v _q 
  have p4989 := n4989 _v _q h4838
  have p17050 := n17050 _v _q 
  have p16778 := n16778 _v _q 
  have p17122 := n17122 _v _q 
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p20829 := n20829 _v _q 
  have p15775 := n15775 _v _q h2242
  have p20426 := n20426 _v _q 
  have p20126 := n20126 _v _q 
  have p17110 := n17110 _v _q 
  have p17053 := n17053 _v _q 
  have p20096 := n20096 _v _q 
  have p17131 := n17131 _v _q 
  have p17108 := n17108 _v _q 
  have p17294 := n17294 _v _q 
  have p16943 := n16943 _v _q 
  have p17058 := n17058 _v _q 
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
  have p17055 := n17055 _v _q 
  have p17093 := n17093 _v _q 
  have p17091 := n17091 _v _q 
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p15949 := n15949 _v _q h2242
  have p20838 := n20838 _v _q h2242
  have p17141 := n17141 _v _q 
  have p17100 := n17100 _v _q 
  have p19610 := n19610 _v _q 
  have p17102 := n17102 _v _q 
  have p5008 := n5008 _v _q h4787
  have p15952 := n15952 _v _q h2242
  have p17096 := n17096 _v _q 
  have p17115 := n17115 _v _q 
  have p17758 := n17758 _v _q 
  have p17124 := n17124 _v _q 
  have p17111 := n17111 _v _q 
  have p17163 := n17163 _v _q h7935
  exact FloorCertificate.node_21008 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2902 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4541 _v) (e4808 _v) p13951 p12927 p4016 p8553 p8601 p20990 p16882 p15209 p258 p17113 p17117 p20467 p14799 p17065 p19665 p17133 p17120 p15956 p17104 p17874 p17127 p17089 p4998 p4999 p253 p15946 p17020 p17138 p20274 p17060 p20470 p4989 p17050 p16778 p17122 p4983 p16729 p20829 p15775 p20426 p20126 p17110 p17053 p20096 p17131 p17108 p17294 p16943 p17058 p17064 p17067 p17080 p17072 p17074 p17069 p20461 p20836 p20653 p17078 p17136 p17087 p17083 p17055 p17093 p17091 p17098 p17106 p15949 p20838 p17141 p17100 p19610 p17102 p5008 p15952 p17096 p17115 p17758 p17124 p17111 p17163
theorem n21009 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2296 : (e2296 _v)) (h3158 : (e3158 _v)) (h4306 : (e4306 _v)) (h4439 : (e4439 _v)) (h4459 : (e4459 _v)) (h4567 : (e4567 _v)) (h4653 : (e4653 _v)) (h4679 : (e4679 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6776 : (e6776 _v)) : (e2402 _v) := by
  have p20992 := n20992 _v _q 
  have p8583 := n8583 _v _q h2296
  have p8601 := n8601 _v _q h6776
  have p253 := n253 _v _q h191
  have p17143 := n17143 _v _q h4567
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4989 := n4989 _v _q h4838
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p17070 := n17070 _v _q h4679
  have p16885 := n16885 _v _q h3158
  have p17075 := n17075 _v _q h4439
  have p5008 := n5008 _v _q h4787
  have p17051 := n17051 _v _q h4459
  have p4999 := n4999 _v _q h91
  change (e2402 _v) ∨ (¬ (e2296 _v)) ∨ (e2781 _v) ∨ (¬ (e191 _v)) ∨ (¬ (e4567 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4679 _v)) ∨ (¬ (e3158 _v)) ∨ (¬ (e4439 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4459 _v)) ∨ (¬ (e91 _v)) at p20992
  change (¬ (e2781 _v)) at p8601
  rcases p20992 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p8583))
  · exact (False.elim (p8601 hlit))
  · exact (False.elim (hlit p253))
  · exact (False.elim (hlit p17143))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p4989))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p17070))
  · exact (False.elim (hlit p16885))
  · exact (False.elim (hlit p17075))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p17051))
  · exact (False.elim (hlit p4999))
theorem n21010 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2781 : (e2781 _v)) (h3158 : (e3158 _v)) (h4306 : (e4306 _v)) (h4439 : (e4439 _v)) (h4459 : (e4459 _v)) (h4567 : (e4567 _v)) (h4653 : (e4653 _v)) (h4679 : (e4679 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6549 : (e6549 _v)) (h6630 : (e6630 _v)) : (e3919 _v) := by
  have p14797 := n14797 _v _q 
  have p20995 := n20995 _v _q h51 h91 h191 h2781 h3158 h4306 h4439 h4459 h4567 h4653 h4679 h4813 h4838 h6549 h6630
  change (e3923 _v) ∨ (e3919 _v) at p14797
  change (¬ (e3923 _v)) at p20995
  rcases p14797 with hlit | hlit
  · exact (False.elim (p20995 hlit))
  · exact hlit
theorem n21011 (_v : Vars) (_q : Query _v) (h2781 : (e2781 _v)) (h6630 : (e6630 _v)) : (e7814 _v) := by
  have p15221 := n15221 _v _q 
  have p16092 := n16092 _v _q h2781 h6630
  change (e7818 _v) ∨ (e7814 _v) at p15221
  change (¬ (e7818 _v)) at p16092
  rcases p15221 with hlit | hlit
  · exact (False.elim (p16092 hlit))
  · exact hlit
end
end Assembly
