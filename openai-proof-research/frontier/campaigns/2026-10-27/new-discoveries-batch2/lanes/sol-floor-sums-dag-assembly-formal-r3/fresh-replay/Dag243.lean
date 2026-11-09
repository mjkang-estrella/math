import Dag242
import generated.th_lemma_32
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n21012 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2781 : (e2781 _v)) (h3158 : (e3158 _v)) (h4306 : (e4306 _v)) (h4439 : (e4439 _v)) (h4459 : (e4459 _v)) (h4567 : (e4567 _v)) (h4653 : (e4653 _v)) (h4679 : (e4679 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6549 : (e6549 _v)) (h6630 : (e6630 _v)) : (e7489 _v) := by
  have p17104 := n17104 _v _q 
  have p4946 := n4946 _v _q 
  have p17127 := n17127 _v _q 
  have p17089 := n17089 _v _q 
  have p8544 := n8544 _v _q h6549
  have p21010 := n21010 _v _q h51 h91 h191 h2781 h3158 h4306 h4439 h4459 h4567 h4653 h4679 h4813 h4838 h6549 h6630
  have p15778 := n15778 _v _q h6549
  have p16091 := n16091 _v _q h2781 h6630
  have p17256 := n17256 _v _q 
  have p16003 := n16003 _v _q h2781
  have p13951 := n13951 _v _q 
  have p20966 := n20966 _v _q h2781 h6549
  have p253 := n253 _v _q h191
  have p17143 := n17143 _v _q h4567
  have p17020 := n17020 _v _q 
  have p21011 := n21011 _v _q h2781 h6630
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
  have p17070 := n17070 _v _q h4679
  have p20426 := n20426 _v _q 
  have p20126 := n20126 _v _q 
  have p17110 := n17110 _v _q 
  have p16011 := n16011 _v _q h2781
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
  have p16885 := n16885 _v _q h3158
  have p17075 := n17075 _v _q h4439
  have p17141 := n17141 _v _q 
  have p17100 := n17100 _v _q 
  have p19610 := n19610 _v _q 
  have p17102 := n17102 _v _q 
  have p15934 := n15934 _v _q h6630
  have p17051 := n17051 _v _q h4459
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
  have p17874 := n17874 _v _q 
  exact FloorCertificate.node_21012 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2902 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4541 _v) (e4808 _v) p17104 p4946 p17127 p17089 p8544 p21010 p15778 p16091 p17256 p16003 p13951 p20966 p253 p17143 p17020 p21011 p17138 p20274 p17060 p20470 p4989 p17050 p16778 p17122 p4983 p16729 p20829 p17070 p20426 p20126 p17110 p16011 p17053 p20096 p17131 p17108 p17294 p16943 p17058 p17064 p17067 p17080 p17072 p17074 p17069 p20461 p20836 p20653 p17078 p17136 p17087 p17083 p17055 p17093 p17091 p17098 p17106 p16885 p17075 p17141 p17100 p19610 p17102 p15934 p17051 p17096 p17115 p17758 p17124 p17111 p19665 p17113 p17117 p20467 p17120 p4999 p17133 p17874
theorem n21013 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2242 : (e2242 _v)) (h3937 : (e3937 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6549 : (e6549 _v)) (h6776 : (e6776 _v)) (h7807 : (e7807 _v)) (h7935 : (e7935 _v)) : (e2475 _v) := by
  have p15207 := n15207 _v _q 
  have p20996 := n20996 _v _q h51 h91 h191 h2242 h3937 h4101 h4306 h4653 h4787 h4813 h4838 h6549 h6776 h7807 h7935
  change (e2475 _v) ∨ (¬ (e8049 _v)) at p15207
  rcases p15207 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p20996))
theorem n21014 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2242 : (e2242 _v)) (h3937 : (e3937 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6549 : (e6549 _v)) (h6776 : (e6776 _v)) (h7807 : (e7807 _v)) (h7935 : (e7935 _v)) : (e8035 _v) := by
  have p14871 := n14871 _v _q 
  have p21013 := n21013 _v _q h51 h91 h191 h2242 h3937 h4101 h4306 h4653 h4787 h4813 h4838 h6549 h6776 h7807 h7935
  change (¬ (e2475 _v)) ∨ (¬ (e8029 _v)) at p14871
  rcases p14871 with hlit | hlit
  · exact (False.elim (hlit p21013))
  · exact hlit
theorem n21015 (_v : Vars) (_q : Query _v) (h2733 : (e2733 _v)) (h6600 : (e6600 _v)) : (e7814 _v) := by
  have p15221 := n15221 _v _q 
  have p16094 := n16094 _v _q h2733 h6600
  change (e7818 _v) ∨ (e7814 _v) at p15221
  change (¬ (e7818 _v)) at p16094
  rcases p15221 with hlit | hlit
  · exact (False.elim (p16094 hlit))
  · exact hlit
theorem n21016 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2242 : (e2242 _v)) (h2733 : (e2733 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6549 : (e6549 _v)) (h6600 : (e6600 _v)) (h6776 : (e6776 _v)) : (e2358 _v) := by
  have p20998 := n20998 _v _q 
  have p21015 := n21015 _v _q h2733 h6600
  have p8601 := n8601 _v _q h6776
  have p15778 := n15778 _v _q h6549
  have p4999 := n4999 _v _q h91
  have p253 := n253 _v _q h191
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4989 := n4989 _v _q h4838
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p5008 := n5008 _v _q h4787
  have p8553 := n8553 _v _q h2242
  have p15907 := n15907 _v _q h6600
  have p8587 := n8587 _v _q h2733
  change (e2358 _v) ∨ (¬ (e91 _v)) ∨ (e2781 _v) ∨ (¬ (e3152 _v)) ∨ (¬ (e7814 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e2242 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e2733 _v)) at p20998
  change (¬ (e2781 _v)) at p8601
  rcases p20998 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p4999))
  · exact (False.elim (p8601 hlit))
  · exact (False.elim (hlit p15778))
  · exact (False.elim (hlit p21015))
  · exact (False.elim (hlit p253))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p4989))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p8553))
  · exact (False.elim (hlit p15907))
  · exact (False.elim (hlit p8587))
theorem n21017 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2242 : (e2242 _v)) (h2733 : (e2733 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6549 : (e6549 _v)) (h6600 : (e6600 _v)) (h6776 : (e6776 _v)) : (e7640 _v) := by
  have p14828 := n14828 _v _q 
  have p21016 := n21016 _v _q h51 h91 h191 h2242 h2733 h4306 h4653 h4787 h4813 h4838 h6549 h6600 h6776
  change (¬ (e2358 _v)) ∨ (¬ (e7634 _v)) at p14828
  rcases p14828 with hlit | hlit
  · exact (False.elim (hlit p21016))
  · exact hlit
theorem n21018 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2242 : (e2242 _v)) (h3152 : (e3152 _v)) (h4096 : (e4096 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6600 : (e6600 _v)) (h6776 : (e6776 _v)) (h8038 : (e8038 _v)) : (e7807 _v) := by
  have p21000 := n21000 _v _q 
  have p20976 := n20976 _v _q h51 h91 h191 h2242 h3152 h4096 h4306 h4653 h4787 h4813 h4838 h6600 h6776 h8038
  have p15956 := n15956 _v _q h6776
  have p4998 := n4998 _v _q h3152
  have p15209 := n15209 _v _q h8038
  have p253 := n253 _v _q h191
  have p8439 := n8439 _v _q h6600
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4989 := n4989 _v _q h4838
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p5008 := n5008 _v _q h4787
  have p4999 := n4999 _v _q h91
  have p5001 := n5001 _v _q h4096
  have p8553 := n8553 _v _q h2242
  change (¬ (e2303 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e8045 _v)) ∨ (¬ (e191 _v)) ∨ (e2402 _v) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e2242 _v)) at p21000
  change (¬ (e2402 _v)) at p8439
  rcases p21000 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p15956))
  · exact (False.elim (hlit p20976))
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p15209))
  · exact (False.elim (hlit p253))
  · exact (False.elim (p8439 hlit))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p4989))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p5001))
  · exact (False.elim (hlit p8553))
theorem n21020 (_v : Vars) (_q : Query _v)  : (e21019 _v) := by
  by_contra hc
  change ¬ ((e2733 _v) ∨ (¬ (e225 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e2364 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e7935 _v)) ∨ (¬ (e8317 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e7749 _v)) ∨ (¬ (e8045 _v)) ∨ (¬ (e7814 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e5100 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e5145 _v)) ∨ (¬ (e4562 _v)) ∨ (¬ (e4787 _v))) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h225 : (e225 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h2364 : (e2364 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4260 : (e4260 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h4434 : (e4434 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4562 : (e4562 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))
  have h4608 : (e4608 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h4675 : (e4675 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))))))))))))))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h5100 : (e5100 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))
  have h5145 : (e5145 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))
  have h6750 : (e6750 _v) := (fun hn => hc (Or.inl hn))
  have h7749 : (e7749 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h7814 : (e7814 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h7935 : (e7935 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h8045 : (e8045 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h8317 : (e8317 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have p21001 := n21001 _v _q h51 h225 h2364 h3152 h3937 h4260 h4306 h4434 h4562 h4608 h4653 h4675 h4787 h4813 h5100 h5145 h6750 h7749 h7814 h7935 h8045 h8317
  exact p21001
theorem n21021 (_v : Vars) (_q : Query _v) (h4260 : (e4260 _v)) (h6423 : (e6423 _v)) (h6583 : (e6583 _v)) : (e51 _v) := by
  have p14962 := n14962 _v _q 
  have p21004 := n21004 _v _q h4260 h6423 h6583
  change (e59 _v) ∨ (e51 _v) at p14962
  change (¬ (e59 _v)) at p21004
  rcases p14962 with hlit | hlit
  · exact (False.elim (p21004 hlit))
  · exact hlit
theorem n21022 (_v : Vars) (_q : Query _v) (h6423 : (e6423 _v)) (h6583 : (e6583 _v)) : (e7814 _v) := by
  have p15221 := n15221 _v _q 
  have p20904 := n20904 _v _q h6423 h6583
  change (e7818 _v) ∨ (e7814 _v) at p15221
  change (¬ (e7818 _v)) at p20904
  rcases p15221 with hlit | hlit
  · exact (False.elim (p20904 hlit))
  · exact hlit
theorem n21023 (_v : Vars) (_q : Query _v) (h4260 : (e4260 _v)) (h6423 : (e6423 _v)) (h6583 : (e6583 _v)) : (e7489 _v) := by
  have p13951 := n13951 _v _q 
  have p296 := n296 _v _q 
  have p20979 := n20979 _v _q h6423 h6583
  have p8663 := n8663 _v _q 
  have p5255 := n5255 _v _q 
  have p20893 := n20893 _v _q h6423 h6583
  have p15338 := n15338 _v _q h6583
  have p20895 := n20895 _v _q h6423 h6583
  have p21021 := n21021 _v _q h4260 h6423 h6583
  have p16659 := n16659 _v _q h6423
  have p20949 := n20949 _v _q h6423 h6583
  have p20978 := n20978 _v _q h6423 h6583
  have p21022 := n21022 _v _q h6423 h6583
  have p16660 := n16660 _v _q h6423
  have p20829 := n20829 _v _q 
  have p17108 := n17108 _v _q 
  have p20461 := n20461 _v _q 
  have p16663 := n16663 _v _q h6583
  have p4981 := n4981 _v _q h4260
  have p17221 := n17221 _v _q 
  have p20426 := n20426 _v _q 
  have p15967 := n15967 _v _q h6423
  have p20126 := n20126 _v _q 
  have p17110 := n17110 _v _q 
  have p17009 := n17009 _v _q 
  have p17053 := n17053 _v _q 
  have p17131 := n17131 _v _q 
  have p20951 := n20951 _v _q h6423 h6583
  have p20096 := n20096 _v _q 
  have p16656 := n16656 _v _q h6583
  have p17058 := n17058 _v _q 
  have p17294 := n17294 _v _q 
  have p16943 := n16943 _v _q 
  have p17064 := n17064 _v _q 
  have p16658 := n16658 _v _q h6423
  have p15974 := n15974 _v _q h6583
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
  have p20901 := n20901 _v _q h6423 h6583
  have p15379 := n15379 _v _q h6423
  have p17758 := n17758 _v _q 
  have p15964 := n15964 _v _q h6423
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
  have p16869 := n16869 _v _q h6583
  have p20274 := n20274 _v _q 
  have p20470 := n20470 _v _q 
  have p17133 := n17133 _v _q 
  have p17089 := n17089 _v _q 
  have p16394 := n16394 _v _q 
  have p16396 := n16396 _v _q h6423
  have p16576 := n16576 _v _q 
  have p16657 := n16657 _v _q h6423
  have p17147 := n17147 _v _q 
  have p16977 := n16977 _v _q 
  have p16388 := n16388 _v _q h6583
  have p16994 := n16994 _v _q 
  have p4946 := n4946 _v _q 
  have p11340 := n11340 _v _q h6583
  exact FloorCertificate.node_21023 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2834 _v) (e2849 _v) (e2863 _v) (e2877 _v) (e2879 _v) (e2883 _v) (e2898 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p13951 p296 p20979 p8663 p5255 p20893 p15338 p20895 p21021 p16659 p20949 p20978 p21022 p16660 p20829 p17108 p20461 p16663 p4981 p17221 p20426 p15967 p20126 p17110 p17009 p17053 p17131 p20951 p20096 p16656 p17058 p17294 p16943 p17064 p16658 p15974 p17067 p17069 p17080 p17072 p17083 p17074 p20836 p17078 p20653 p17087 p17136 p17055 p17091 p17093 p17141 p17098 p17106 p17102 p17100 p19610 p16929 p17122 p17096 p20901 p15379 p17758 p15964 p19665 p17115 p17120 p17111 p17124 p17050 p16778 p17113 p17117 p20467 p17104 p17874 p17127 p16869 p20274 p20470 p17133 p17089 p16394 p16396 p16576 p16657 p17147 p16977 p16388 p16994 p4946 p11340
theorem n21025 (_v : Vars) (_q : Query _v)  : (e21024 _v) := by
  by_contra hc
  change ¬ ((¬ (e3152 _v)) ∨ (e2733 _v) ∨ (¬ (e2468 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e4679 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4813 _v))) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h191 : (e191 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h2468 : (e2468 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h4679 : (e4679 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn)))))))))))
  have h4838 : (e4838 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h6750 : (e6750 _v) := (fun hn => hc (Or.inr (Or.inl hn)))
  have p21005 := n21005 _v _q h51 h91 h191 h2468 h3152 h4306 h4653 h4679 h4813 h4838 h6750
  exact p21005
theorem n21027 (_v : Vars) (_q : Query _v)  : (e21026 _v) := by
  by_contra hc
  change ¬ ((¬ (e7935 _v)) ∨ (¬ (e2242 _v)) ∨ (e2781 _v) ∨ (¬ (e4101 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e2402 _v)) ∨ (e2475 _v)) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h191 : (e191 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h2242 : (e2242 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h2402 : (e2402 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4101 : (e4101 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h4838 : (e4838 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h6776 : (e6776 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h7935 : (e7935 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h8038 : (e8038 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn)))))))))))))))
  have p21008 := n21008 _v _q h51 h91 h191 h2242 h2402 h3152 h4101 h4306 h4653 h4787 h4813 h4838 h6776 h7935 h8038
  exact p21008
theorem n21028 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2296 : (e2296 _v)) (h3158 : (e3158 _v)) (h4306 : (e4306 _v)) (h4439 : (e4439 _v)) (h4459 : (e4459 _v)) (h4567 : (e4567 _v)) (h4653 : (e4653 _v)) (h4679 : (e4679 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6776 : (e6776 _v)) : (e2358 _v) := by
  have p21009 := n21009 _v _q h51 h91 h191 h2296 h3158 h4306 h4439 h4459 h4567 h4653 h4679 h4787 h4813 h4838 h6776
  have p8601 := n8601 _v _q h6776
  exact FloorCertificate.node_21028 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p21009 p8601
theorem n21029 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2296 : (e2296 _v)) (h3158 : (e3158 _v)) (h4306 : (e4306 _v)) (h4439 : (e4439 _v)) (h4459 : (e4459 _v)) (h4567 : (e4567 _v)) (h4653 : (e4653 _v)) (h4679 : (e4679 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6776 : (e6776 _v)) : (e7640 _v) := by
  have p14828 := n14828 _v _q 
  have p21028 := n21028 _v _q h51 h91 h191 h2296 h3158 h4306 h4439 h4459 h4567 h4653 h4679 h4787 h4813 h4838 h6776
  change (¬ (e2358 _v)) ∨ (¬ (e7634 _v)) at p14828
  rcases p14828 with hlit | hlit
  · exact (False.elim (hlit p21028))
  · exact hlit
theorem n21031 (_v : Vars) (_q : Query _v)  : (e21030 _v) := by
  by_contra hc
  change ¬ ((¬ (e2781 _v)) ∨ (e2296 _v) ∨ (¬ (e191 _v)) ∨ (¬ (e4567 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4679 _v)) ∨ (¬ (e3158 _v)) ∨ (¬ (e4439 _v)) ∨ (¬ (e4459 _v)) ∨ (¬ (e91 _v)) ∨ (e2468 _v)) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h191 : (e191 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h2781 : (e2781 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h3158 : (e3158 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4439 : (e4439 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h4459 : (e4459 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h4567 : (e4567 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h4679 : (e4679 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h4838 : (e4838 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h6549 : (e6549 _v) := (fun hn => hc (Or.inr (Or.inl hn)))
  have h6630 : (e6630 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn)))))))))))))))
  have p21012 := n21012 _v _q h51 h91 h191 h2781 h3158 h4306 h4439 h4459 h4567 h4653 h4679 h4813 h4838 h6549 h6630
  exact p21012
theorem n21032 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2242 : (e2242 _v)) (h3937 : (e3937 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6549 : (e6549 _v)) (h6776 : (e6776 _v)) (h7807 : (e7807 _v)) (h7935 : (e7935 _v)) : (e4546 _v) := by
  have p16307 := n16307 _v _q 
  have p21014 := n21014 _v _q h51 h91 h191 h2242 h3937 h4101 h4306 h4653 h4787 h4813 h4838 h6549 h6776 h7807 h7935
  change (e8029 _v) ∨ (e4546 _v) at p16307
  change (¬ (e8029 _v)) at p21014
  rcases p16307 with hlit | hlit
  · exact (False.elim (p21014 hlit))
  · exact hlit
theorem n21033 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2242 : (e2242 _v)) (h2733 : (e2733 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6549 : (e6549 _v)) (h6600 : (e6600 _v)) (h6776 : (e6776 _v)) : (e4139 _v) := by
  have p16281 := n16281 _v _q 
  have p21017 := n21017 _v _q h51 h91 h191 h2242 h2733 h4306 h4653 h4787 h4813 h4838 h6549 h6600 h6776
  change (e7634 _v) ∨ (e4139 _v) at p16281
  change (¬ (e7634 _v)) at p21017
  rcases p16281 with hlit | hlit
  · exact (False.elim (p21017 hlit))
  · exact hlit
theorem n21034 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2242 : (e2242 _v)) (h3152 : (e3152 _v)) (h4096 : (e4096 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6600 : (e6600 _v)) (h6776 : (e6776 _v)) (h8038 : (e8038 _v)) : (e7819 _v) := by
  have p14994 := n14994 _v _q 
  have p21018 := n21018 _v _q h51 h91 h191 h2242 h3152 h4096 h4306 h4653 h4787 h4813 h4838 h6600 h6776 h8038
  change (e2303 _v) ∨ (¬ (e7818 _v)) at p14994
  change (¬ (e2303 _v)) at p21018
  rcases p14994 with hlit | hlit
  · exact (False.elim (p21018 hlit))
  · exact hlit
theorem n21035 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2242 : (e2242 _v)) (h3152 : (e3152 _v)) (h4096 : (e4096 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6600 : (e6600 _v)) (h6776 : (e6776 _v)) (h8038 : (e8038 _v)) : (e7814 _v) := by
  have p15221 := n15221 _v _q 
  have p21034 := n21034 _v _q h51 h91 h191 h2242 h3152 h4096 h4306 h4653 h4787 h4813 h4838 h6600 h6776 h8038
  change (e7818 _v) ∨ (e7814 _v) at p15221
  change (¬ (e7818 _v)) at p21034
  rcases p15221 with hlit | hlit
  · exact (False.elim (p21034 hlit))
  · exact hlit
theorem n21036 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2242 : (e2242 _v)) (h3152 : (e3152 _v)) (h4096 : (e4096 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6600 : (e6600 _v)) (h6776 : (e6776 _v)) (h8038 : (e8038 _v)) : (e4420 _v) := by
  have p16832 := n16832 _v _q 
  have p21018 := n21018 _v _q h51 h91 h191 h2242 h3152 h4096 h4306 h4653 h4787 h4813 h4838 h6600 h6776 h8038
  have p8602 := n8602 _v _q h8038
  change (e2303 _v) ∨ (¬ (e4419 _v)) ∨ (e2475 _v) at p16832
  change (¬ (e2303 _v)) at p21018
  change (¬ (e2475 _v)) at p8602
  rcases p16832 with hlit | hlit | hlit
  · exact (False.elim (p21018 hlit))
  · exact hlit
  · exact (False.elim (p8602 hlit))
theorem n21037 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2242 : (e2242 _v)) (h3152 : (e3152 _v)) (h4096 : (e4096 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6600 : (e6600 _v)) (h6776 : (e6776 _v)) (h8038 : (e8038 _v)) : (e7921 _v) := by
  have p16347 := n16347 _v _q 
  have p21036 := n21036 _v _q h51 h91 h191 h2242 h3152 h4096 h4306 h4653 h4787 h4813 h4838 h6600 h6776 h8038
  change (e7921 _v) ∨ (e4419 _v) at p16347
  change (¬ (e4419 _v)) at p21036
  rcases p16347 with hlit | hlit
  · exact hlit
  · exact (False.elim (p21036 hlit))
theorem n21039 (_v : Vars) (_q : Query _v)  : (e21038 _v) := by
  by_contra hc
  change ¬ ((e2364 _v) ∨ (¬ (e4260 _v)) ∨ (e1995 _v)) at hc
  have h4260 : (e4260 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h6423 : (e6423 _v) := (fun hn => hc (Or.inr (Or.inr hn)))
  have h6583 : (e6583 _v) := (fun hn => hc (Or.inl hn))
  have p21023 := n21023 _v _q h4260 h6423 h6583
  exact p21023
theorem n21040 (_v : Vars) (_q : Query _v) (h4260 : (e4260 _v)) (h6423 : (e6423 _v)) : (e2364 _v) := by
  have p21039 := n21039 _v _q 
  have p4981 := n4981 _v _q h4260
  have p8452 := n8452 _v _q h6423
  change (e2364 _v) ∨ (¬ (e4260 _v)) ∨ (e1995 _v) at p21039
  change (¬ (e1995 _v)) at p8452
  rcases p21039 with hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p4981))
  · exact (False.elim (p8452 hlit))
theorem n21041 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2468 : (e2468 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6750 : (e6750 _v)) : (e3156 _v) := by
  have p21025 := n21025 _v _q 
  have p8420 := n8420 _v _q h6750
  have p8438 := n8438 _v _q h2468
  have p4999 := n4999 _v _q h91
  have p16074 := n16074 _v _q h2468
  have p253 := n253 _v _q h191
  have p16729 := n16729 _v _q h51
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4989 := n4989 _v _q h4838
  have p4983 := n4983 _v _q h4813
  change (¬ (e3152 _v)) ∨ (e2733 _v) ∨ (¬ (e2468 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e4679 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4813 _v)) at p21025
  change (¬ (e2733 _v)) at p8420
  rcases p21025 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (p8420 hlit))
  · exact (False.elim (hlit p8438))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p16074))
  · exact (False.elim (hlit p253))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p4989))
  · exact (False.elim (hlit p4983))
theorem n21042 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2468 : (e2468 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6750 : (e6750 _v)) : (e7489 _v) := by
  have p15776 := n15776 _v _q 
  have p16064 := n16064 _v _q h2468 h6750
  have p21041 := n21041 _v _q h51 h91 h191 h2468 h4306 h4653 h4813 h4838 h6750
  change (e6878 _v) ∨ (e3152 _v) at p15776
  change (¬ (e6878 _v)) at p16064
  change (¬ (e3152 _v)) at p21041
  rcases p15776 with hlit | hlit
  · exact (False.elim (p16064 hlit))
  · exact (False.elim (p21041 hlit))
theorem n21043 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2296 : (e2296 _v)) (h3158 : (e3158 _v)) (h4306 : (e4306 _v)) (h4439 : (e4439 _v)) (h4459 : (e4459 _v)) (h4567 : (e4567 _v)) (h4653 : (e4653 _v)) (h4679 : (e4679 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6776 : (e6776 _v)) : (e4139 _v) := by
  have p16281 := n16281 _v _q 
  have p21029 := n21029 _v _q h51 h91 h191 h2296 h3158 h4306 h4439 h4459 h4567 h4653 h4679 h4787 h4813 h4838 h6776
  change (e7634 _v) ∨ (e4139 _v) at p16281
  change (¬ (e7634 _v)) at p21029
  rcases p16281 with hlit | hlit
  · exact (False.elim (p21029 hlit))
  · exact hlit
theorem n21044 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2242 : (e2242 _v)) (h3937 : (e3937 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6549 : (e6549 _v)) (h6776 : (e6776 _v)) (h7807 : (e7807 _v)) (h7935 : (e7935 _v)) : (e7489 _v) := by
  have p258 := n258 _v _q 
  have p10893 := n10893 _v _q 
  have p8601 := n8601 _v _q h6776
  have p21032 := n21032 _v _q h51 h91 h191 h2242 h3937 h4101 h4306 h4653 h4787 h4813 h4838 h6549 h6776 h7807 h7935
  have p17113 := n17113 _v _q 
  have p17117 := n17117 _v _q 
  have p20467 := n20467 _v _q 
  have p17147 := n17147 _v _q 
  have p17065 := n17065 _v _q h4101
  have p19665 := n19665 _v _q 
  have p17133 := n17133 _v _q 
  have p17120 := n17120 _v _q 
  have p15956 := n15956 _v _q h6776
  have p17256 := n17256 _v _q 
  have p17104 := n17104 _v _q 
  have p17874 := n17874 _v _q 
  have p17127 := n17127 _v _q 
  have p17089 := n17089 _v _q 
  have p15778 := n15778 _v _q h6549
  have p15373 := n15373 _v _q h7807
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
  have p12927 := n12927 _v _q h2242
  have p8553 := n8553 _v _q h2242
  have p13951 := n13951 _v _q 
  have p4996 := n4996 _v _q h3937
  have p17163 := n17163 _v _q h7935
  exact FloorCertificate.node_21044 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2883 _v) (e2902 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4541 _v) (e4808 _v) p258 p10893 p8601 p21032 p17113 p17117 p20467 p17147 p17065 p19665 p17133 p17120 p15956 p17256 p17104 p17874 p17127 p17089 p15778 p15373 p4999 p253 p15946 p17020 p17138 p20274 p17060 p20470 p4989 p17050 p16778 p17122 p4983 p16729 p20829 p15775 p20426 p20126 p17110 p17053 p20096 p17131 p17108 p17294 p16943 p17058 p17064 p17067 p17080 p17072 p17074 p17069 p20461 p20836 p20653 p17078 p17136 p17087 p17083 p17055 p17093 p17091 p17098 p17106 p15949 p20838 p17141 p17100 p19610 p17102 p5008 p15952 p17096 p17115 p17758 p17124 p17111 p12927 p8553 p13951 p4996 p17163
theorem n21045 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2242 : (e2242 _v)) (h3152 : (e3152 _v)) (h4096 : (e4096 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6600 : (e6600 _v)) (h6776 : (e6776 _v)) (h8038 : (e8038 _v)) : (e6772 _v) := by
  have p14855 := n14855 _v _q 
  have p21037 := n21037 _v _q h51 h91 h191 h2242 h3152 h4096 h4306 h4653 h4787 h4813 h4838 h6600 h6776 h8038
  change (¬ (e2787 _v)) ∨ (¬ (e7921 _v)) at p14855
  rcases p14855 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p21037))
theorem n21046 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2242 : (e2242 _v)) (h3152 : (e3152 _v)) (h4096 : (e4096 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6600 : (e6600 _v)) (h6776 : (e6776 _v)) (h8038 : (e8038 _v)) : (e7945 _v) := by
  have p15228 := n15228 _v _q 
  have p21045 := n21045 _v _q h51 h91 h191 h2242 h3152 h4096 h4306 h4653 h4787 h4813 h4838 h6600 h6776 h8038
  change (e2787 _v) ∨ (¬ (e7944 _v)) at p15228
  change (¬ (e2787 _v)) at p21045
  rcases p15228 with hlit | hlit
  · exact (False.elim (p21045 hlit))
  · exact hlit
theorem n21047 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2242 : (e2242 _v)) (h3152 : (e3152 _v)) (h4096 : (e4096 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6600 : (e6600 _v)) (h6776 : (e6776 _v)) (h8038 : (e8038 _v)) : (e7935 _v) := by
  have p15266 := n15266 _v _q 
  have p21046 := n21046 _v _q h51 h91 h191 h2242 h3152 h4096 h4306 h4653 h4787 h4813 h4838 h6600 h6776 h8038
  change (e7944 _v) ∨ (e7935 _v) at p15266
  change (¬ (e7944 _v)) at p21046
  rcases p15266 with hlit | hlit
  · exact (False.elim (p21046 hlit))
  · exact hlit
theorem n21048 (_v : Vars) (_q : Query _v) (h4260 : (e4260 _v)) (h6423 : (e6423 _v)) : (e7807 _v) := by
  have p8530 := n8530 _v _q 
  have p21040 := n21040 _v _q h4260 h6423
  have p8452 := n8452 _v _q h6423
  change (¬ (e2303 _v)) ∨ (e1995 _v) ∨ (¬ (e2364 _v)) at p8530
  change (¬ (e1995 _v)) at p8452
  rcases p8530 with hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (p8452 hlit))
  · exact (False.elim (hlit p21040))
theorem n21049 (_v : Vars) (_q : Query _v) (h225 : (e225 _v)) (h4260 : (e4260 _v)) (h4813 : (e4813 _v)) (h6423 : (e6423 _v)) : (e4420 _v) := by
  have p16832 := n16832 _v _q 
  have p20907 := n20907 _v _q h225 h4813 h6423
  have p21048 := n21048 _v _q h4260 h6423
  change (e2303 _v) ∨ (¬ (e4419 _v)) ∨ (e2475 _v) at p16832
  change (¬ (e2475 _v)) at p20907
  change (¬ (e2303 _v)) at p21048
  rcases p16832 with hlit | hlit | hlit
  · exact (False.elim (p21048 hlit))
  · exact hlit
  · exact (False.elim (p20907 hlit))
theorem n21050 (_v : Vars) (_q : Query _v) (h4260 : (e4260 _v)) (h6423 : (e6423 _v)) : (e7742 _v) := by
  have p11353 := n11353 _v _q 
  have p21048 := n21048 _v _q h4260 h6423
  change (¬ (e2132 _v)) ∨ (e2303 _v) at p11353
  change (¬ (e2303 _v)) at p21048
  rcases p11353 with hlit | hlit
  · exact hlit
  · exact (False.elim (p21048 hlit))
theorem n21051 (_v : Vars) (_q : Query _v) (h4260 : (e4260 _v)) (h6423 : (e6423 _v)) : (e7819 _v) := by
  have p14994 := n14994 _v _q 
  have p21048 := n21048 _v _q h4260 h6423
  change (e2303 _v) ∨ (¬ (e7818 _v)) at p14994
  change (¬ (e2303 _v)) at p21048
  rcases p14994 with hlit | hlit
  · exact (False.elim (p21048 hlit))
  · exact hlit
theorem n21052 (_v : Vars) (_q : Query _v) (h4260 : (e4260 _v)) (h6423 : (e6423 _v)) : (e5093 _v) := by
  have p11468 := n11468 _v _q 
  have p21048 := n21048 _v _q h4260 h6423
  change (¬ (e13 _v)) ∨ (e2303 _v) at p11468
  change (¬ (e2303 _v)) at p21048
  rcases p11468 with hlit | hlit
  · exact hlit
  · exact (False.elim (p21048 hlit))
theorem n21054 (_v : Vars) (_q : Query _v)  : (e21053 _v) := by
  by_contra hc
  change ¬ ((e2733 _v) ∨ (¬ (e2468 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4813 _v))) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h191 : (e191 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h2468 : (e2468 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn)))))))))
  have h4838 : (e4838 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h6750 : (e6750 _v) := (fun hn => hc (Or.inl hn))
  have p21042 := n21042 _v _q h51 h91 h191 h2468 h4306 h4653 h4813 h4838 h6750
  exact p21042
theorem n21055 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2296 : (e2296 _v)) (h3158 : (e3158 _v)) (h4306 : (e4306 _v)) (h4439 : (e4439 _v)) (h4459 : (e4459 _v)) (h4567 : (e4567 _v)) (h4653 : (e4653 _v)) (h4679 : (e4679 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6776 : (e6776 _v)) : (e3929 _v) := by
  have p14484 := n14484 _v _q 
  have p21009 := n21009 _v _q h51 h91 h191 h2296 h3158 h4306 h4439 h4459 h4567 h4653 h4679 h4787 h4813 h4838 h6776
  change (¬ (e2402 _v)) ∨ (¬ (e3923 _v)) at p14484
  rcases p14484 with hlit | hlit
  · exact (False.elim (hlit p21009))
  · exact hlit
theorem n21056 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2296 : (e2296 _v)) (h3158 : (e3158 _v)) (h4306 : (e4306 _v)) (h4439 : (e4439 _v)) (h4459 : (e4459 _v)) (h4567 : (e4567 _v)) (h4653 : (e4653 _v)) (h4679 : (e4679 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6776 : (e6776 _v)) : (e3919 _v) := by
  have p14797 := n14797 _v _q 
  have p21055 := n21055 _v _q h51 h91 h191 h2296 h3158 h4306 h4439 h4459 h4567 h4653 h4679 h4787 h4813 h4838 h6776
  change (e3923 _v) ∨ (e3919 _v) at p14797
  change (¬ (e3923 _v)) at p21055
  rcases p14797 with hlit | hlit
  · exact (False.elim (p21055 hlit))
  · exact hlit
theorem n21057 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2296 : (e2296 _v)) (h3158 : (e3158 _v)) (h4306 : (e4306 _v)) (h4419 : (e4419 _v)) (h4439 : (e4439 _v)) (h4459 : (e4459 _v)) (h4567 : (e4567 _v)) (h4653 : (e4653 _v)) (h4679 : (e4679 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6776 : (e6776 _v)) : (e7489 _v) := by
  have p10893 := n10893 _v _q 
  have p258 := n258 _v _q 
  have p21056 := n21056 _v _q h51 h91 h191 h2296 h3158 h4306 h4439 h4459 h4567 h4653 h4679 h4787 h4813 h4838 h6776
  have p21043 := n21043 _v _q h51 h91 h191 h2296 h3158 h4306 h4439 h4459 h4567 h4653 h4679 h4787 h4813 h4838 h6776
  have p4971 := n4971 _v _q h4419
  have p8583 := n8583 _v _q h2296
  have p8601 := n8601 _v _q h6776
  have p15956 := n15956 _v _q h6776
  have p253 := n253 _v _q h191
  have p17143 := n17143 _v _q h4567
  have p17020 := n17020 _v _q 
  have p16883 := n16883 _v _q h2296 h6776
  have p17138 := n17138 _v _q h4306
  have p20274 := n20274 _v _q 
  have p17060 := n17060 _v _q h4653
  have p20470 := n20470 _v _q 
  have p4989 := n4989 _v _q h4838
  have p15100 := n15100 _v _q h2296
  have p17050 := n17050 _v _q 
  have p16778 := n16778 _v _q 
  have p17122 := n17122 _v _q 
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p20829 := n20829 _v _q 
  have p17070 := n17070 _v _q h4679
  have p20426 := n20426 _v _q 
  have p20126 := n20126 _v _q 
  have p17110 := n17110 _v _q 
  have p15113 := n15113 _v _q h2296
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
  have p16885 := n16885 _v _q h3158
  have p17075 := n17075 _v _q h4439
  have p17141 := n17141 _v _q 
  have p17100 := n17100 _v _q 
  have p19610 := n19610 _v _q 
  have p17102 := n17102 _v _q 
  have p5008 := n5008 _v _q h4787
  have p17051 := n17051 _v _q h4459
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
  have p17874 := n17874 _v _q 
  have p17104 := n17104 _v _q 
  have p17127 := n17127 _v _q 
  have p17089 := n17089 _v _q 
  have p5257 := n5257 _v _q 
  have p13951 := n13951 _v _q 
  have p5255 := n5255 _v _q 
  exact FloorCertificate.node_21057 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2902 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e4541 _v) (e4808 _v) p10893 p258 p21056 p21043 p4971 p8583 p8601 p15956 p253 p17143 p17020 p16883 p17138 p20274 p17060 p20470 p4989 p15100 p17050 p16778 p17122 p4983 p16729 p20829 p17070 p20426 p20126 p17110 p15113 p17053 p20096 p17131 p17108 p17294 p16943 p17058 p17064 p17067 p17080 p17072 p17074 p17069 p20461 p20836 p20653 p17078 p17136 p17087 p17083 p17055 p17093 p17091 p17098 p17106 p16885 p17075 p17141 p17100 p19610 p17102 p5008 p17051 p17096 p17115 p17758 p17124 p17111 p19665 p17113 p17117 p20467 p17120 p4999 p17133 p17874 p17104 p17127 p17089 p5257 p13951 p5255
theorem n21059 (_v : Vars) (_q : Query _v)  : (e21058 _v) := by
  by_contra hc
  change ¬ ((¬ (e7935 _v)) ∨ (e2781 _v) ∨ (¬ (e4101 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e2242 _v)) ∨ (¬ (e3937 _v)) ∨ (e2296 _v) ∨ (e2303 _v)) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h191 : (e191 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h2242 : (e2242 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h4101 : (e4101 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h4838 : (e4838 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h6549 : (e6549 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h6776 : (e6776 _v) := (fun hn => hc (Or.inr (Or.inl hn)))
  have h7807 : (e7807 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn)))))))))))))))
  have h7935 : (e7935 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have p21044 := n21044 _v _q h51 h91 h191 h2242 h3937 h4101 h4306 h4653 h4787 h4813 h4838 h6549 h6776 h7807 h7935
  exact p21044
theorem n21060 (_v : Vars) (_q : Query _v) (h4260 : (e4260 _v)) (h5108 : (e5108 _v)) (h6423 : (e6423 _v)) : (e4420 _v) := by
  have p16832 := n16832 _v _q 
  have p20934 := n20934 _v _q h5108 h6423
  have p21048 := n21048 _v _q h4260 h6423
  change (e2303 _v) ∨ (¬ (e4419 _v)) ∨ (e2475 _v) at p16832
  change (¬ (e2475 _v)) at p20934
  change (¬ (e2303 _v)) at p21048
  rcases p16832 with hlit | hlit | hlit
  · exact (False.elim (p21048 hlit))
  · exact hlit
  · exact (False.elim (p20934 hlit))
theorem n21061 (_v : Vars) (_q : Query _v) (h4260 : (e4260 _v)) (h6423 : (e6423 _v)) : (e6746 _v) := by
  have p11429 := n11429 _v _q 
  have p21048 := n21048 _v _q h4260 h6423
  change (¬ (e2740 _v)) ∨ (e2303 _v) at p11429
  change (¬ (e2303 _v)) at p21048
  rcases p11429 with hlit | hlit
  · exact hlit
  · exact (False.elim (p21048 hlit))
theorem n21062 (_v : Vars) (_q : Query _v) (h4260 : (e4260 _v)) (h6423 : (e6423 _v)) : (e4661 _v) := by
  have p14686 := n14686 _v _q 
  have p21040 := n21040 _v _q h4260 h6423
  change (¬ (e2364 _v)) ∨ (¬ (e4660 _v)) at p14686
  rcases p14686 with hlit | hlit
  · exact (False.elim (hlit p21040))
  · exact hlit
theorem n21063 (_v : Vars) (_q : Query _v) (h4260 : (e4260 _v)) (h6423 : (e6423 _v)) : (e4653 _v) := by
  have p15168 := n15168 _v _q 
  have p21062 := n21062 _v _q h4260 h6423
  change (e4660 _v) ∨ (e4653 _v) at p15168
  change (¬ (e4660 _v)) at p21062
  rcases p15168 with hlit | hlit
  · exact (False.elim (p21062 hlit))
  · exact hlit
end
end Assembly
