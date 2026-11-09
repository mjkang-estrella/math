import Dag261
import generated.th_lemma_35
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n21952 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4813 : (e4813 _v)) (h5138 : (e5138 _v)) (h6750 : (e6750 _v)) (h7807 : (e7807 _v)) (h7935 : (e7935 _v)) (h8045 : (e8045 _v)) : (e7489 _v) := by
  have p16576 := n16576 _v _q 
  have p15927 := n15927 _v _q h5138
  have p15940 := n15940 _v _q h6750
  have p18959 := n18959 _v _q h7807
  have p4991 := n4991 _v _q h4608
  have p21742 := n21742 _v _q h51 h4306 h4653 h4813
  have p20836 := n20836 _v _q 
  have p20461 := n20461 _v _q 
  have p4998 := n4998 _v _q h3152
  have p15373 := n15373 _v _q h7807
  have p17136 := n17136 _v _q 
  have p21902 := n21902 _v _q h51 h4306 h4653 h4813
  have p17087 := n17087 _v _q 
  have p17055 := n17055 _v _q 
  have p4987 := n4987 _v _q h4434
  have p17098 := n17098 _v _q 
  have p5006 := n5006 _v _q h4675
  have p17147 := n17147 _v _q 
  have p17083 := n17083 _v _q 
  have p17786 := n17786 _v _q h7807
  have p17106 := n17106 _v _q 
  have p17020 := n17020 _v _q 
  have p17093 := n17093 _v _q 
  have p16929 := n16929 _v _q 
  have p17100 := n17100 _v _q 
  have p11487 := n11487 _v _q h5138
  have p17141 := n17141 _v _q 
  have p17102 := n17102 _v _q 
  have p17091 := n17091 _v _q 
  have p17096 := n17096 _v _q 
  have p21748 := n21748 _v _q h51 h4306 h4653 h4813
  have p17157 := n17157 _v _q h8045
  have p17758 := n17758 _v _q 
  have p11350 := n11350 _v _q h7807
  have p17124 := n17124 _v _q 
  have p19610 := n19610 _v _q 
  have p17111 := n17111 _v _q 
  have p17115 := n17115 _v _q 
  have p17256 := n17256 _v _q 
  have p17078 := n17078 _v _q 
  have p17113 := n17113 _v _q 
  have p17117 := n17117 _v _q 
  have p20467 := n20467 _v _q 
  have p19665 := n19665 _v _q 
  have p17133 := n17133 _v _q 
  have p17120 := n17120 _v _q 
  have p17104 := n17104 _v _q 
  have p17874 := n17874 _v _q 
  have p17127 := n17127 _v _q 
  have p17089 := n17089 _v _q 
  have p20653 := n20653 _v _q 
  have p21727 := n21727 _v _q h51 h4306 h4653 h4813
  have p17138 := n17138 _v _q h4306
  have p20274 := n20274 _v _q 
  have p17060 := n17060 _v _q h4653
  have p20470 := n20470 _v _q 
  have p17050 := n17050 _v _q 
  have p16778 := n16778 _v _q 
  have p17122 := n17122 _v _q 
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p20829 := n20829 _v _q 
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
  have p13951 := n13951 _v _q 
  have p4996 := n4996 _v _q h3937
  have p16977 := n16977 _v _q 
  have p17009 := n17009 _v _q 
  have p5255 := n5255 _v _q 
  have p21946 := n21946 _v _q h51 h4306 h4653 h4813
  have p21900 := n21900 _v _q h51 h4306 h4653 h4813
  have p4981 := n4981 _v _q h4260
  have p17163 := n17163 _v _q h7935
  have p8420 := n8420 _v _q h6750
  exact FloorCertificate.node_21952 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2849 _v) (e2863 _v) (e2877 _v) (e2883 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p16576 p15927 p15940 p18959 p4991 p21742 p20836 p20461 p4998 p15373 p17136 p21902 p17087 p17055 p4987 p17098 p5006 p17147 p17083 p17786 p17106 p17020 p17093 p16929 p17100 p11487 p17141 p17102 p17091 p17096 p21748 p17157 p17758 p11350 p17124 p19610 p17111 p17115 p17256 p17078 p17113 p17117 p20467 p19665 p17133 p17120 p17104 p17874 p17127 p17089 p20653 p21727 p17138 p20274 p17060 p20470 p17050 p16778 p17122 p4983 p16729 p20829 p20426 p20126 p17110 p17053 p20096 p17131 p17108 p17294 p16943 p17058 p17064 p17067 p17080 p17072 p17074 p17069 p13951 p4996 p16977 p17009 p5255 p21946 p21900 p4981 p17163 p8420
theorem n21954 (_v : Vars) (_q : Query _v)  : (e21953 _v) := by
  by_contra hc
  change ¬ ((e79 _v) ∨ (¬ (e4608 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e8045 _v)) ∨ (e2303 _v) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e7935 _v)) ∨ (e2733 _v)) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h4260 : (e4260 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h4434 : (e4434 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4608 : (e4608 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h4675 : (e4675 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h5138 : (e5138 _v) := (fun hn => hc (Or.inl hn))
  have h6750 : (e6750 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn)))))))))))))))
  have h7807 : (e7807 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h7935 : (e7935 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h8045 : (e8045 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have p21952 := n21952 _v _q h51 h3152 h3937 h4260 h4306 h4434 h4608 h4653 h4675 h4813 h5138 h6750 h7807 h7935 h8045
  exact p21952
theorem n21955 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4813 : (e4813 _v)) (h6750 : (e6750 _v)) (h7807 : (e7807 _v)) (h8038 : (e8038 _v)) : (e79 _v) := by
  have p21954 := n21954 _v _q 
  have p8420 := n8420 _v _q h6750
  have p4998 := n4998 _v _q h3152
  have p4987 := n4987 _v _q h4434
  have p5006 := n5006 _v _q h4675
  have p15209 := n15209 _v _q h8038
  have p11350 := n11350 _v _q h7807
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p4996 := n4996 _v _q h3937
  have p4981 := n4981 _v _q h4260
  have p16966 := n16966 _v _q h7807 h8038
  have p4991 := n4991 _v _q h4608
  change (e79 _v) ∨ (¬ (e4608 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e8045 _v)) ∨ (e2303 _v) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e7935 _v)) ∨ (e2733 _v) at p21954
  change (¬ (e2733 _v)) at p8420
  change (¬ (e2303 _v)) at p11350
  rcases p21954 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p4991))
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p4987))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p15209))
  · exact (False.elim (p11350 hlit))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p4996))
  · exact (False.elim (hlit p4981))
  · exact (False.elim (hlit p16966))
  · exact (False.elim (p8420 hlit))
theorem n21956 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4813 : (e4813 _v)) (h6750 : (e6750 _v)) (h7807 : (e7807 _v)) (h8038 : (e8038 _v)) : (e5135 _v) := by
  have p14729 := n14729 _v _q 
  have p21955 := n21955 _v _q h51 h3152 h3937 h4260 h4306 h4434 h4608 h4653 h4675 h4813 h6750 h7807 h8038
  change (¬ (e79 _v)) ∨ (¬ (e5134 _v)) at p14729
  rcases p14729 with hlit | hlit
  · exact (False.elim (hlit p21955))
  · exact hlit
theorem n21957 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4813 : (e4813 _v)) (h6750 : (e6750 _v)) (h7807 : (e7807 _v)) (h8038 : (e8038 _v)) : (e91 _v) := by
  have p16235 := n16235 _v _q 
  have p21956 := n21956 _v _q h51 h3152 h3937 h4260 h4306 h4434 h4608 h4653 h4675 h4813 h6750 h7807 h8038
  change (e5134 _v) ∨ (e91 _v) at p16235
  change (¬ (e5134 _v)) at p21956
  rcases p16235 with hlit | hlit
  · exact (False.elim (p21956 hlit))
  · exact hlit
theorem n21958 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4813 : (e4813 _v)) (h6750 : (e6750 _v)) (h7807 : (e7807 _v)) (h8038 : (e8038 _v)) : (e2358 _v) := by
  have p20260 := n20260 _v _q 
  have p21957 := n21957 _v _q h51 h3152 h3937 h4260 h4306 h4434 h4608 h4653 h4675 h4813 h6750 h7807 h8038
  have p17953 := n17953 _v _q 
  have p20274 := n20274 _v _q 
  have p20426 := n20426 _v _q 
  have p20461 := n20461 _v _q 
  have p17020 := n17020 _v _q 
  have p16943 := n16943 _v _q 
  have p4987 := n4987 _v _q h4434
  have p4983 := n4983 _v _q h4813
  have p21946 := n21946 _v _q h51 h4306 h4653 h4813
  have p20096 := n20096 _v _q 
  have p4998 := n4998 _v _q h3152
  have p5006 := n5006 _v _q h4675
  have p4996 := n4996 _v _q h3937
  have p20467 := n20467 _v _q 
  have p15209 := n15209 _v _q h8038
  have p19610 := n19610 _v _q 
  have p17138 := n17138 _v _q h4306
  have p4991 := n4991 _v _q h4608
  have p11350 := n11350 _v _q h7807
  have p17294 := n17294 _v _q 
  have p17060 := n17060 _v _q h4653
  have p17874 := n17874 _v _q 
  have p20653 := n20653 _v _q 
  have p20126 := n20126 _v _q 
  have p20829 := n20829 _v _q 
  have p20836 := n20836 _v _q 
  have p17758 := n17758 _v _q 
  have p19665 := n19665 _v _q 
  have p20470 := n20470 _v _q 
  have p8602 := n8602 _v _q h8038
  have p21748 := n21748 _v _q h51 h4306 h4653 h4813
  have p18959 := n18959 _v _q h7807
  change (¬ (e4567 _v)) ∨ (e2358 _v) ∨ (¬ (e3069 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4491 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4903 _v)) ∨ (¬ (e5208 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e5100 _v)) ∨ (¬ (e4398 _v)) ∨ (¬ (e8045 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e3976 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4724 _v)) ∨ (¬ (e4434 _v)) ∨ (e2475 _v) ∨ (e2303 _v) at p20260
  change (¬ (e2303 _v)) at p11350
  change (¬ (e2475 _v)) at p8602
  rcases p20260 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact (False.elim (hlit p21748))
  · exact hlit
  · exact (False.elim (hlit p20461))
  · exact (False.elim (hlit p4991))
  · exact (False.elim (hlit p21957))
  · exact (False.elim (hlit p4996))
  · exact (False.elim (hlit p16943))
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p20096))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p21946))
  · exact (False.elim (hlit p20274))
  · exact (False.elim (hlit p17953))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p18959))
  · exact (False.elim (hlit p20467))
  · exact (False.elim (hlit p15209))
  · exact (False.elim (hlit p19610))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17020))
  · exact (False.elim (hlit p20426))
  · exact (False.elim (hlit p17294))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p17874))
  · exact (False.elim (hlit p20653))
  · exact (False.elim (hlit p20126))
  · exact (False.elim (hlit p20829))
  · exact (False.elim (hlit p20836))
  · exact (False.elim (hlit p17758))
  · exact (False.elim (hlit p19665))
  · exact (False.elim (hlit p20470))
  · exact (False.elim (hlit p4987))
  · exact (False.elim (p8602 hlit))
  · exact (False.elim (p11350 hlit))
theorem n21959 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4813 : (e4813 _v)) (h6750 : (e6750 _v)) (h7807 : (e7807 _v)) (h8038 : (e8038 _v)) : (e7489 _v) := by
  have p3130 := n3130 _v _q 
  have p21958 := n21958 _v _q h51 h3152 h3937 h4260 h4306 h4434 h4608 h4653 h4675 h4813 h6750 h7807 h8038
  have p21742 := n21742 _v _q h51 h4306 h4653 h4813
  have p11350 := n11350 _v _q h7807
  have p8420 := n8420 _v _q h6750
  have p21957 := n21957 _v _q h51 h3152 h3937 h4260 h4306 h4434 h4608 h4653 h4675 h4813 h6750 h7807 h8038
  have p16576 := n16576 _v _q 
  have p15940 := n15940 _v _q h6750
  have p18959 := n18959 _v _q h7807
  have p4991 := n4991 _v _q h4608
  have p20836 := n20836 _v _q 
  have p20461 := n20461 _v _q 
  have p4998 := n4998 _v _q h3152
  have p15373 := n15373 _v _q h7807
  have p17136 := n17136 _v _q 
  have p21902 := n21902 _v _q h51 h4306 h4653 h4813
  have p17087 := n17087 _v _q 
  have p17055 := n17055 _v _q 
  have p4987 := n4987 _v _q h4434
  have p17098 := n17098 _v _q 
  have p5006 := n5006 _v _q h4675
  have p17147 := n17147 _v _q 
  have p17083 := n17083 _v _q 
  have p17786 := n17786 _v _q h7807
  have p17106 := n17106 _v _q 
  have p17020 := n17020 _v _q 
  have p17093 := n17093 _v _q 
  have p16929 := n16929 _v _q 
  have p17100 := n17100 _v _q 
  have p16966 := n16966 _v _q h7807 h8038
  have p17141 := n17141 _v _q 
  have p17102 := n17102 _v _q 
  have p17091 := n17091 _v _q 
  have p17096 := n17096 _v _q 
  have p21748 := n21748 _v _q h51 h4306 h4653 h4813
  have p15209 := n15209 _v _q h8038
  have p17758 := n17758 _v _q 
  have p17124 := n17124 _v _q 
  have p19610 := n19610 _v _q 
  have p17111 := n17111 _v _q 
  have p17115 := n17115 _v _q 
  have p17256 := n17256 _v _q 
  have p17078 := n17078 _v _q 
  have p17113 := n17113 _v _q 
  have p17117 := n17117 _v _q 
  have p20467 := n20467 _v _q 
  have p19665 := n19665 _v _q 
  have p17133 := n17133 _v _q 
  have p17120 := n17120 _v _q 
  have p17104 := n17104 _v _q 
  have p17874 := n17874 _v _q 
  have p17127 := n17127 _v _q 
  have p17089 := n17089 _v _q 
  have p20653 := n20653 _v _q 
  have p21727 := n21727 _v _q h51 h4306 h4653 h4813
  have p17138 := n17138 _v _q h4306
  have p20274 := n20274 _v _q 
  have p17060 := n17060 _v _q h4653
  have p20470 := n20470 _v _q 
  have p17050 := n17050 _v _q 
  have p16778 := n16778 _v _q 
  have p17122 := n17122 _v _q 
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p20829 := n20829 _v _q 
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
  have p13951 := n13951 _v _q 
  have p4996 := n4996 _v _q h3937
  have p16977 := n16977 _v _q 
  have p17009 := n17009 _v _q 
  have p21946 := n21946 _v _q h51 h4306 h4653 h4813
  have p4981 := n4981 _v _q h4260
  exact FloorCertificate.node_21959 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2849 _v) (e2863 _v) (e2877 _v) (e2883 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p3130 p21958 p21742 p11350 p8420 p21957 p16576 p15940 p18959 p4991 p20836 p20461 p4998 p15373 p17136 p21902 p17087 p17055 p4987 p17098 p5006 p17147 p17083 p17786 p17106 p17020 p17093 p16929 p17100 p16966 p17141 p17102 p17091 p17096 p21748 p15209 p17758 p17124 p19610 p17111 p17115 p17256 p17078 p17113 p17117 p20467 p19665 p17133 p17120 p17104 p17874 p17127 p17089 p20653 p21727 p17138 p20274 p17060 p20470 p17050 p16778 p17122 p4983 p16729 p20829 p20426 p20126 p17110 p17053 p20096 p17131 p17108 p17294 p16943 p17058 p17064 p17067 p17080 p17072 p17074 p17069 p13951 p4996 p16977 p17009 p21946 p4981
theorem n21961 (_v : Vars) (_q : Query _v)  : (e21960 _v) := by
  by_contra hc
  change ¬ ((e2733 _v) ∨ (e2303 _v) ∨ (¬ (e4608 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e4260 _v)) ∨ (e2475 _v)) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h4260 : (e4260 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h4434 : (e4434 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4608 : (e4608 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h4675 : (e4675 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h6750 : (e6750 _v) := (fun hn => hc (Or.inl hn))
  have h7807 : (e7807 _v) := (fun hn => hc (Or.inr (Or.inl hn)))
  have h8038 : (e8038 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn)))))))))))))
  have p21959 := n21959 _v _q h51 h3152 h3937 h4260 h4306 h4434 h4608 h4653 h4675 h4813 h6750 h7807 h8038
  exact p21959
theorem n21962 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6454 : (e6454 _v)) : (e2733 _v) := by
  have p21961 := n21961 _v _q 
  have p21599 := n21599 _v _q h51 h4306 h4653 h4813 h6454
  have p16735 := n16735 _v _q h6454
  have p16631 := n16631 _v _q h6454
  have p15764 := n15764 _v _q h6454
  have p16736 := n16736 _v _q h6454
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p16128 := n16128 _v _q h6454
  have p21910 := n21910 _v _q h51 h4306 h4653 h4813 h6454
  have p21649 := n21649 _v _q h51 h4306 h4653 h4813 h6454
  change (e2733 _v) ∨ (e2303 _v) ∨ (¬ (e4608 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e4260 _v)) ∨ (e2475 _v) at p21961
  change (¬ (e2303 _v)) at p21599
  change (¬ (e2475 _v)) at p21649
  rcases p21961 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (p21599 hlit))
  · exact (False.elim (hlit p16735))
  · exact (False.elim (hlit p16631))
  · exact (False.elim (hlit p15764))
  · exact (False.elim (hlit p16736))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p16128))
  · exact (False.elim (hlit p21910))
  · exact (False.elim (p21649 hlit))
theorem n21963 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6454 : (e6454 _v)) : (e8310 _v) := by
  have p8590 := n8590 _v _q 
  have p21962 := n21962 _v _q h51 h4306 h4653 h4813 h6454
  have p12952 := n12952 _v _q h6454
  change (e2179 _v) ∨ (¬ (e2529 _v)) ∨ (¬ (e2733 _v)) at p8590
  change (¬ (e2179 _v)) at p12952
  rcases p8590 with hlit | hlit | hlit
  · exact (False.elim (p12952 hlit))
  · exact hlit
  · exact (False.elim (hlit p21962))
theorem n21964 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6454 : (e6454 _v)) : (e95 _v) := by
  have p16871 := n16871 _v _q 
  have p21962 := n21962 _v _q h51 h4306 h4653 h4813 h6454
  have p8430 := n8430 _v _q h6454
  change (¬ (e2733 _v)) ∨ (¬ (e91 _v)) ∨ (e2061 _v) at p16871
  change (¬ (e2061 _v)) at p8430
  rcases p16871 with hlit | hlit | hlit
  · exact (False.elim (hlit p21962))
  · exact hlit
  · exact (False.elim (p8430 hlit))
theorem n21965 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6454 : (e6454 _v)) : (e4109 _v) := by
  have p14689 := n14689 _v _q 
  have p21962 := n21962 _v _q h51 h4306 h4653 h4813 h6454
  change (¬ (e2733 _v)) ∨ (¬ (e4108 _v)) at p14689
  rcases p14689 with hlit | hlit
  · exact (False.elim (hlit p21962))
  · exact hlit
theorem n21966 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6454 : (e6454 _v)) : (e4101 _v) := by
  have p14929 := n14929 _v _q 
  have p21965 := n21965 _v _q h51 h4306 h4653 h4813 h6454
  change (e4108 _v) ∨ (e4101 _v) at p14929
  change (¬ (e4108 _v)) at p21965
  rcases p14929 with hlit | hlit
  · exact (False.elim (p21965 hlit))
  · exact hlit
theorem n21967 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6454 : (e6454 _v)) : (e7935 _v) := by
  have p15266 := n15266 _v _q 
  have p21655 := n21655 _v _q h51 h4306 h4653 h4813 h6454
  change (e7944 _v) ∨ (e7935 _v) at p15266
  change (¬ (e7944 _v)) at p21655
  rcases p15266 with hlit | hlit
  · exact (False.elim (p21655 hlit))
  · exact hlit
theorem n21968 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6454 : (e6454 _v)) : (e4264 _v) := by
  have p21900 := n21900 _v _q h51 h4306 h4653 h4813
  have p21910 := n21910 _v _q h51 h4306 h4653 h4813 h6454
  have p21967 := n21967 _v _q h51 h4306 h4653 h4813 h6454
  have p5255 := n5255 _v _q 
  have p8430 := n8430 _v _q h6454
  exact FloorCertificate.node_21968 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) (e2911 _v) (e2995 _v) p21900 p21910 p21967 p5255 p8430
theorem n21969 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6454 : (e6454 _v)) : (e5148 _v) := by
  have p17621 := n17621 _v _q 
  have p21966 := n21966 _v _q h51 h4306 h4653 h4813 h6454
  have p20426 := n20426 _v _q 
  have p16729 := n16729 _v _q h51
  have p21742 := n21742 _v _q h51 h4306 h4653 h4813
  have p8430 := n8430 _v _q h6454
  have p16943 := n16943 _v _q 
  have p20470 := n20470 _v _q 
  have p20467 := n20467 _v _q 
  have p15764 := n15764 _v _q h6454
  have p19610 := n19610 _v _q 
  have p17020 := n17020 _v _q 
  have p20126 := n20126 _v _q 
  have p20096 := n20096 _v _q 
  have p4983 := n4983 _v _q h4813
  have p20653 := n20653 _v _q 
  have p16128 := n16128 _v _q h6454
  have p21968 := n21968 _v _q h51 h4306 h4653 h4813 h6454
  have p21599 := n21599 _v _q h51 h4306 h4653 h4813 h6454
  have p21946 := n21946 _v _q h51 h4306 h4653 h4813
  have p17060 := n17060 _v _q h4653
  have p16736 := n16736 _v _q h6454
  have p17294 := n17294 _v _q 
  have p17874 := n17874 _v _q 
  have p17138 := n17138 _v _q h4306
  have p20829 := n20829 _v _q 
  have p20274 := n20274 _v _q 
  have p20836 := n20836 _v _q 
  have p17953 := n17953 _v _q 
  have p17758 := n17758 _v _q 
  have p19665 := n19665 _v _q 
  have p16735 := n16735 _v _q h6454
  have p20461 := n20461 _v _q 
  have p21963 := n21963 _v _q h51 h4306 h4653 h4813 h6454
  have p16631 := n16631 _v _q h6454
  change (¬ (e5145 _v)) ∨ (e2061 _v) ∨ (e2303 _v) ∨ (¬ (e4199 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e4724 _v)) ∨ (¬ (e4398 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e3976 _v)) ∨ (¬ (e4491 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e4264 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4101 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e4903 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e5208 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e3069 _v)) ∨ (e2529 _v) ∨ (¬ (e1995 _v)) at p17621
  change (¬ (e2061 _v)) at p8430
  change (¬ (e2303 _v)) at p21599
  change (¬ (e2529 _v)) at p21963
  rcases p17621 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (p8430 hlit))
  · exact (False.elim (p21599 hlit))
  · exact (False.elim (hlit p16943))
  · exact (False.elim (hlit p17020))
  · exact (False.elim (hlit p20426))
  · exact (False.elim (hlit p16128))
  · exact (False.elim (hlit p20470))
  · exact (False.elim (hlit p20467))
  · exact (False.elim (hlit p15764))
  · exact (False.elim (hlit p19610))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p20126))
  · exact (False.elim (hlit p20096))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p20653))
  · exact (False.elim (hlit p21968))
  · exact (False.elim (hlit p16631))
  · exact (False.elim (hlit p21966))
  · exact (False.elim (hlit p21946))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p16736))
  · exact (False.elim (hlit p17294))
  · exact (False.elim (hlit p17874))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p20829))
  · exact (False.elim (hlit p20274))
  · exact (False.elim (hlit p20836))
  · exact (False.elim (hlit p17953))
  · exact (False.elim (hlit p17758))
  · exact (False.elim (hlit p19665))
  · exact (False.elim (hlit p16735))
  · exact (False.elim (hlit p20461))
  · exact (False.elim (p21963 hlit))
  · exact (False.elim (hlit p21742))
theorem n21970 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6454 : (e6454 _v)) : (e5149 _v) := by
  have p15925 := n15925 _v _q 
  have p21969 := n21969 _v _q h51 h4306 h4653 h4813 h6454
  change (e5149 _v) ∨ (e5145 _v) at p15925
  change (¬ (e5145 _v)) at p21969
  rcases p15925 with hlit | hlit
  · exact hlit
  · exact (False.elim (p21969 hlit))
theorem n21971 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6454 : (e6454 _v)) : (e5134 _v) := by
  have p16235 := n16235 _v _q 
  have p21964 := n21964 _v _q h51 h4306 h4653 h4813 h6454
  change (e5134 _v) ∨ (e91 _v) at p16235
  change (¬ (e91 _v)) at p21964
  rcases p16235 with hlit | hlit
  · exact hlit
  · exact (False.elim (p21964 hlit))
theorem n21972 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6454 : (e6454 _v)) : (e5138 _v) := by
  have p14729 := n14729 _v _q 
  have p21971 := n21971 _v _q h51 h4306 h4653 h4813 h6454
  change (¬ (e79 _v)) ∨ (¬ (e5134 _v)) at p14729
  rcases p14729 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p21971))
theorem n21973 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6454 : (e6454 _v)) : (e7489 _v) := by
  have p15115 := n15115 _v _q 
  have p21970 := n21970 _v _q h51 h4306 h4653 h4813 h6454
  have p21972 := n21972 _v _q h51 h4306 h4653 h4813 h6454
  change (e79 _v) ∨ (¬ (e5149 _v)) at p15115
  change (¬ (e79 _v)) at p21972
  rcases p15115 with hlit | hlit
  · exact (False.elim (p21972 hlit))
  · exact (False.elim (hlit p21970))
theorem n21975 (_v : Vars) (_q : Query _v)  : (e21974 _v) := by
  by_contra hc
  change ¬ ((e2061 _v) ∨ (¬ (e51 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4306 _v))) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr hn)))))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h6454 : (e6454 _v) := (fun hn => hc (Or.inl hn))
  have p21973 := n21973 _v _q h51 h4306 h4653 h4813 h6454
  exact p21973
theorem n21976 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e2061 _v) := by
  have p21975 := n21975 _v _q 
  have p16729 := n16729 _v _q h51
  have p4983 := n4983 _v _q h4813
  have p17060 := n17060 _v _q h4653
  have p17138 := n17138 _v _q h4306
  change (e2061 _v) ∨ (¬ (e51 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4306 _v)) at p21975
  rcases p21975 with hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p17138))
theorem n21977 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e4447 _v) := by
  have p14688 := n14688 _v _q 
  have p21976 := n21976 _v _q h51 h4306 h4653 h4813
  change (¬ (e2061 _v)) ∨ (¬ (e4446 _v)) at p14688
  rcases p14688 with hlit | hlit
  · exact (False.elim (hlit p21976))
  · exact hlit
theorem n21978 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e2061 _v) := by
  have p21975 := n21975 _v _q 
  have p17138 := n17138 _v _q h4306
  have p16729 := n16729 _v _q h51
  have p4983 := n4983 _v _q h4813
  have p17060 := n17060 _v _q h4653
  change (e2061 _v) ∨ (¬ (e51 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4306 _v)) at p21975
  rcases p21975 with hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p17138))
theorem n21979 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e4439 _v) := by
  have p14925 := n14925 _v _q 
  have p21977 := n21977 _v _q h51 h4306 h4653 h4813
  change (e4446 _v) ∨ (e4439 _v) at p14925
  change (¬ (e4446 _v)) at p21977
  rcases p14925 with hlit | hlit
  · exact (False.elim (p21977 hlit))
  · exact hlit
theorem n21980 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3133 : (e3133 _v)) (h3158 : (e3158 _v)) (h3919 : (e3919 _v)) (h4101 : (e4101 _v)) (h4264 : (e4264 _v)) (h4306 : (e4306 _v)) (h4459 : (e4459 _v)) (h4653 : (e4653 _v)) (h4679 : (e4679 _v)) (h4813 : (e4813 _v)) (h5145 : (e5145 _v)) (h6571 : (e6571 _v)) (h8045 : (e8045 _v)) : (e7489 _v) := by
  have p17064 := n17064 _v _q 
  have p17051 := n17051 _v _q h4459
  have p17067 := n17067 _v _q 
  have p5255 := n5255 _v _q 
  have p5257 := n5257 _v _q 
  have p8447 := n8447 _v _q h6571
  have p17080 := n17080 _v _q 
  have p21900 := n21900 _v _q h51 h4306 h4653 h4813
  have p17072 := n17072 _v _q 
  have p17079 := n17079 _v _q h3919
  have p17074 := n17074 _v _q 
  have p17062 := n17062 _v _q h3133
  have p17245 := n17245 _v _q h5145
  have p17070 := n17070 _v _q h4679
  have p17118 := n17118 _v _q h4264
  have p17069 := n17069 _v _q 
  have p17065 := n17065 _v _q h4101
  have p20836 := n20836 _v _q 
  have p20461 := n20461 _v _q 
  have p21946 := n21946 _v _q h51 h4306 h4653 h4813
  have p16885 := n16885 _v _q h3158
  have p17136 := n17136 _v _q 
  have p21902 := n21902 _v _q h51 h4306 h4653 h4813
  have p17087 := n17087 _v _q 
  have p17055 := n17055 _v _q 
  have p13951 := n13951 _v _q 
  have p17098 := n17098 _v _q 
  have p17083 := n17083 _v _q 
  have p17106 := n17106 _v _q 
  have p17020 := n17020 _v _q 
  have p17093 := n17093 _v _q 
  have p21979 := n21979 _v _q h51 h4306 h4653 h4813
  have p17100 := n17100 _v _q 
  have p17141 := n17141 _v _q 
  have p17102 := n17102 _v _q 
  have p17091 := n17091 _v _q 
  have p17096 := n17096 _v _q 
  have p21748 := n21748 _v _q h51 h4306 h4653 h4813
  have p17157 := n17157 _v _q h8045
  have p17758 := n17758 _v _q 
  have p17124 := n17124 _v _q 
  have p19610 := n19610 _v _q 
  have p17111 := n17111 _v _q 
  have p17115 := n17115 _v _q 
  have p17256 := n17256 _v _q 
  have p17078 := n17078 _v _q 
  have p17113 := n17113 _v _q 
  have p17117 := n17117 _v _q 
  have p20467 := n20467 _v _q 
  have p19665 := n19665 _v _q 
  have p17133 := n17133 _v _q 
  have p17120 := n17120 _v _q 
  have p17104 := n17104 _v _q 
  have p17874 := n17874 _v _q 
  have p17127 := n17127 _v _q 
  have p17089 := n17089 _v _q 
  have p20653 := n20653 _v _q 
  have p21727 := n21727 _v _q h51 h4306 h4653 h4813
  have p17138 := n17138 _v _q h4306
  have p20274 := n20274 _v _q 
  have p17060 := n17060 _v _q h4653
  have p20470 := n20470 _v _q 
  have p17050 := n17050 _v _q 
  have p16778 := n16778 _v _q 
  have p17122 := n17122 _v _q 
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p20829 := n20829 _v _q 
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
  exact FloorCertificate.node_21980 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2902 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e4541 _v) (e4808 _v) p17064 p17051 p17067 p5255 p5257 p8447 p17080 p21900 p17072 p17079 p17074 p17062 p17245 p17070 p17118 p17069 p17065 p20836 p20461 p21946 p16885 p17136 p21902 p17087 p17055 p13951 p17098 p17083 p17106 p17020 p17093 p21979 p17100 p17141 p17102 p17091 p17096 p21748 p17157 p17758 p17124 p19610 p17111 p17115 p17256 p17078 p17113 p17117 p20467 p19665 p17133 p17120 p17104 p17874 p17127 p17089 p20653 p21727 p17138 p20274 p17060 p20470 p17050 p16778 p17122 p4983 p16729 p20829 p20426 p20126 p17110 p17053 p20096 p17131 p17108 p17294 p16943 p17058
theorem n21981 (_v : Vars) (_q : Query _v) (h2296 : (e2296 _v)) : (e7749 _v) := by
  have p14941 := n14941 _v _q 
  have p16134 := n16134 _v _q h2296
  change (e7753 _v) ∨ (e7749 _v) at p14941
  change (¬ (e7753 _v)) at p16134
  rcases p14941 with hlit | hlit
  · exact (False.elim (p16134 hlit))
  · exact hlit
theorem n21982 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2296 : (e2296 _v)) (h4264 : (e4264 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5145 : (e5145 _v)) (h6600 : (e6600 _v)) (h8045 : (e8045 _v)) : (e7489 _v) := by
  have p16102 := n16102 _v _q h2296
  have p20827 := n20827 _v _q 
  have p21900 := n21900 _v _q h51 h4306 h4653 h4813
  have p15100 := n15100 _v _q h2296
  have p17245 := n17245 _v _q h5145
  have p16115 := n16115 _v _q h2296
  have p5255 := n5255 _v _q 
  have p17118 := n17118 _v _q h4264
  have p17069 := n17069 _v _q 
  have p15907 := n15907 _v _q h6600
  have p8583 := n8583 _v _q h2296
  have p17009 := n17009 _v _q 
  have p16131 := n16131 _v _q h2296
  have p20836 := n20836 _v _q 
  have p20461 := n20461 _v _q 
  have p21946 := n21946 _v _q h51 h4306 h4653 h4813
  have p21793 := n21793 _v _q h2296
  have p17136 := n17136 _v _q 
  have p21902 := n21902 _v _q h51 h4306 h4653 h4813
  have p17087 := n17087 _v _q 
  have p17055 := n17055 _v _q 
  have p13951 := n13951 _v _q 
  have p17098 := n17098 _v _q 
  have p17147 := n17147 _v _q 
  have p17083 := n17083 _v _q 
  have p21981 := n21981 _v _q h2296
  have p17106 := n17106 _v _q 
  have p17020 := n17020 _v _q 
  have p17093 := n17093 _v _q 
  have p21979 := n21979 _v _q h51 h4306 h4653 h4813
  have p17100 := n17100 _v _q 
  have p17141 := n17141 _v _q 
  have p17102 := n17102 _v _q 
  have p17091 := n17091 _v _q 
  have p17096 := n17096 _v _q 
  have p21748 := n21748 _v _q h51 h4306 h4653 h4813
  have p17157 := n17157 _v _q h8045
  have p17758 := n17758 _v _q 
  have p17124 := n17124 _v _q 
  have p19610 := n19610 _v _q 
  have p17111 := n17111 _v _q 
  have p17115 := n17115 _v _q 
  have p17256 := n17256 _v _q 
  have p17078 := n17078 _v _q 
  have p17113 := n17113 _v _q 
  have p17117 := n17117 _v _q 
  have p20467 := n20467 _v _q 
  have p19665 := n19665 _v _q 
  have p17133 := n17133 _v _q 
  have p17120 := n17120 _v _q 
  have p17104 := n17104 _v _q 
  have p17874 := n17874 _v _q 
  have p17127 := n17127 _v _q 
  have p17089 := n17089 _v _q 
  have p20653 := n20653 _v _q 
  have p21727 := n21727 _v _q h51 h4306 h4653 h4813
  have p17138 := n17138 _v _q h4306
  have p20274 := n20274 _v _q 
  have p17060 := n17060 _v _q h4653
  have p20470 := n20470 _v _q 
  have p17050 := n17050 _v _q 
  have p16778 := n16778 _v _q 
  have p17122 := n17122 _v _q 
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p20829 := n20829 _v _q 
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
  have p8439 := n8439 _v _q h6600
  exact FloorCertificate.node_21982 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2883 _v) (e2902 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e4215 _v) (e4541 _v) (e4808 _v) p16102 p20827 p21900 p15100 p17245 p16115 p5255 p17118 p17069 p15907 p8583 p17009 p16131 p20836 p20461 p21946 p21793 p17136 p21902 p17087 p17055 p13951 p17098 p17147 p17083 p21981 p17106 p17020 p17093 p21979 p17100 p17141 p17102 p17091 p17096 p21748 p17157 p17758 p17124 p19610 p17111 p17115 p17256 p17078 p17113 p17117 p20467 p19665 p17133 p17120 p17104 p17874 p17127 p17089 p20653 p21727 p17138 p20274 p17060 p20470 p17050 p16778 p17122 p4983 p16729 p20829 p20426 p20126 p17110 p17053 p20096 p17131 p17108 p17294 p16943 p17058 p17064 p17067 p17080 p17072 p17074 p8439
theorem n21983 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e4447 _v) := by
  have p14688 := n14688 _v _q 
  have p21978 := n21978 _v _q h51 h4306 h4653 h4813
  change (¬ (e2061 _v)) ∨ (¬ (e4446 _v)) at p14688
  rcases p14688 with hlit | hlit
  · exact (False.elim (hlit p21978))
  · exact hlit
theorem n21984 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e4439 _v) := by
  have p14925 := n14925 _v _q 
  have p21983 := n21983 _v _q h51 h4306 h4653 h4813
  change (e4446 _v) ∨ (e4439 _v) at p14925
  change (¬ (e4446 _v)) at p21983
  rcases p14925 with hlit | hlit
  · exact (False.elim (p21983 hlit))
  · exact hlit
theorem n21986 (_v : Vars) (_q : Query _v)  : (e21985 _v) := by
  by_contra hc
  change ¬ ((e2358 _v) ∨ (¬ (e4459 _v)) ∨ (¬ (e3919 _v)) ∨ (¬ (e3133 _v)) ∨ (¬ (e5145 _v)) ∨ (¬ (e4679 _v)) ∨ (¬ (e4264 _v)) ∨ (¬ (e4101 _v)) ∨ (¬ (e3158 _v)) ∨ (¬ (e8045 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v))) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))))))))))
  have h3133 : (e3133 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h3158 : (e3158 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h3919 : (e3919 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4101 : (e4101 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h4264 : (e4264 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h4459 : (e4459 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h4679 : (e4679 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h5145 : (e5145 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h6571 : (e6571 _v) := (fun hn => hc (Or.inl hn))
  have h8045 : (e8045 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have p21980 := n21980 _v _q h51 h3133 h3158 h3919 h4101 h4264 h4306 h4459 h4653 h4679 h4813 h5145 h6571 h8045
  exact p21980
theorem n21988 (_v : Vars) (_q : Query _v)  : (e21987 _v) := by
  by_contra hc
  change ¬ ((e2402 _v) ∨ (¬ (e5145 _v)) ∨ (¬ (e4264 _v)) ∨ (¬ (e2296 _v)) ∨ (¬ (e8045 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v))) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn)))))))))
  have h2296 : (e2296 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4264 : (e4264 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h5145 : (e5145 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h6600 : (e6600 _v) := (fun hn => hc (Or.inl hn))
  have h8045 : (e8045 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have p21982 := n21982 _v _q h51 h2296 h4264 h4306 h4653 h4813 h5145 h6600 h8045
  exact p21982
theorem n21989 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e4567 _v) := by
  have p8485 := n8485 _v _q 
  have p21744 := n21744 _v _q h51 h4306 h4653 h4813
  change (e4574 _v) ∨ (e4567 _v) at p8485
  change (¬ (e4574 _v)) at p21744
  rcases p8485 with hlit | hlit
  · exact (False.elim (p21744 hlit))
  · exact hlit
theorem n21990 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2781 : (e2781 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e7749 _v) := by
  have p14941 := n14941 _v _q 
  have p21951 := n21951 _v _q h51 h2781 h4306 h4653 h4813
  change (e7753 _v) ∨ (e7749 _v) at p14941
  change (¬ (e7753 _v)) at p21951
  rcases p14941 with hlit | hlit
  · exact (False.elim (p21951 hlit))
  · exact hlit
theorem n21991 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2781 : (e2781 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e4459 _v) := by
  have p16784 := n16784 _v _q 
  have p21990 := n21990 _v _q h51 h2781 h4306 h4653 h4813
  change (e4459 _v) ∨ (¬ (e7749 _v)) at p16784
  rcases p16784 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p21990))
theorem n21992 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2475 : (e2475 _v)) (h2781 : (e2781 _v)) (h3158 : (e3158 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4679 : (e4679 _v)) (h4813 : (e4813 _v)) (h6549 : (e6549 _v)) : (e7489 _v) := by
  have p21031 := n21031 _v _q 
  have p16889 := n16889 _v _q h2475
  have p16739 := n16739 _v _q h2475
  have p21906 := n21906 _v _q h51 h4306 h4653 h4813
  have p21989 := n21989 _v _q h51 h4306 h4653 h4813
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p8544 := n8544 _v _q h6549
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p8421 := n8421 _v _q h2781
  have p16885 := n16885 _v _q h3158
  have p21984 := n21984 _v _q h51 h4306 h4653 h4813
  have p21991 := n21991 _v _q h51 h2781 h4306 h4653 h4813
  have p17070 := n17070 _v _q h4679
  have p21944 := n21944 _v _q h51 h4306 h4653 h4813
  change (¬ (e2781 _v)) ∨ (e2296 _v) ∨ (¬ (e191 _v)) ∨ (¬ (e4567 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4679 _v)) ∨ (¬ (e3158 _v)) ∨ (¬ (e4439 _v)) ∨ (¬ (e4459 _v)) ∨ (¬ (e91 _v)) ∨ (e2468 _v) at p21031
  change (¬ (e2296 _v)) at p8544
  change (¬ (e2468 _v)) at p21944
  rcases p21031 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact (False.elim (hlit p8421))
  · exact (False.elim (p8544 hlit))
  · exact (False.elim (hlit p21906))
  · exact (False.elim (hlit p21989))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p16739))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p17070))
  · exact (False.elim (hlit p16885))
  · exact (False.elim (hlit p21984))
  · exact (False.elim (hlit p21991))
  · exact (False.elim (hlit p16889))
  · exact (False.elim (p21944 hlit))
theorem n21993 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2296 : (e2296 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5138 : (e5138 _v)) : (e2402 _v) := by
  have p21988 := n21988 _v _q 
  have p15927 := n15927 _v _q h5138
  have p16136 := n16136 _v _q h2296 h5138
  have p8583 := n8583 _v _q h2296
  have p20757 := n20757 _v _q h5138
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  change (e2402 _v) ∨ (¬ (e5145 _v)) ∨ (¬ (e4264 _v)) ∨ (¬ (e2296 _v)) ∨ (¬ (e8045 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) at p21988
  rcases p21988 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p15927))
  · exact (False.elim (hlit p16136))
  · exact (False.elim (hlit p8583))
  · exact (False.elim (hlit p20757))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p16729))
theorem n21994 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2296 : (e2296 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5138 : (e5138 _v)) : (e3929 _v) := by
  have p14484 := n14484 _v _q 
  have p21993 := n21993 _v _q h51 h2296 h4306 h4653 h4813 h5138
  change (¬ (e2402 _v)) ∨ (¬ (e3923 _v)) at p14484
  rcases p14484 with hlit | hlit
  · exact (False.elim (hlit p21993))
  · exact hlit
theorem n21996 (_v : Vars) (_q : Query _v)  : (e21995 _v) := by
  by_contra hc
  change ¬ ((¬ (e2475 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (e2296 _v) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e2781 _v)) ∨ (¬ (e3158 _v)) ∨ (¬ (e4679 _v))) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h2475 : (e2475 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h2781 : (e2781 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h3158 : (e3158 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4679 : (e4679 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn)))))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h6549 : (e6549 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have p21992 := n21992 _v _q h51 h2475 h2781 h3158 h4306 h4653 h4679 h4813 h6549
  exact p21992
theorem n21997 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2296 : (e2296 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5138 : (e5138 _v)) : (e3919 _v) := by
  have p14797 := n14797 _v _q 
  have p21994 := n21994 _v _q h51 h2296 h4306 h4653 h4813 h5138
  change (e3923 _v) ∨ (e3919 _v) at p14797
  change (¬ (e3923 _v)) at p21994
  rcases p14797 with hlit | hlit
  · exact (False.elim (p21994 hlit))
  · exact hlit
theorem n21998 (_v : Vars) (_q : Query _v) (h2296 : (e2296 _v)) : (e4459 _v) := by
  have p8443 := n8443 _v _q 
  have p16138 := n16138 _v _q h2296
  change (e4465 _v) ∨ (e4459 _v) at p8443
  change (¬ (e4465 _v)) at p16138
  rcases p8443 with hlit | hlit
  · exact (False.elim (p16138 hlit))
  · exact hlit
theorem n21999 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2296 : (e2296 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5138 : (e5138 _v)) : (e2358 _v) := by
  have p21986 := n21986 _v _q 
  have p21997 := n21997 _v _q h51 h2296 h4306 h4653 h4813 h5138
  have p21998 := n21998 _v _q h2296
  have p15100 := n15100 _v _q h2296
  have p15927 := n15927 _v _q h5138
  have p16115 := n16115 _v _q h2296
  have p16136 := n16136 _v _q h2296 h5138
  have p16131 := n16131 _v _q h2296
  have p21793 := n21793 _v _q h2296
  have p20757 := n20757 _v _q h5138
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  change (e2358 _v) ∨ (¬ (e4459 _v)) ∨ (¬ (e3919 _v)) ∨ (¬ (e3133 _v)) ∨ (¬ (e5145 _v)) ∨ (¬ (e4679 _v)) ∨ (¬ (e4264 _v)) ∨ (¬ (e4101 _v)) ∨ (¬ (e3158 _v)) ∨ (¬ (e8045 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) at p21986
  rcases p21986 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p21998))
  · exact (False.elim (hlit p21997))
  · exact (False.elim (hlit p15100))
  · exact (False.elim (hlit p15927))
  · exact (False.elim (hlit p16115))
  · exact (False.elim (hlit p16136))
  · exact (False.elim (hlit p16131))
  · exact (False.elim (hlit p21793))
  · exact (False.elim (hlit p20757))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p16729))
theorem n22000 (_v : Vars) (_q : Query _v) (h2296 : (e2296 _v)) : (e4458 _v) := by
  have p20594 := n20594 _v _q 
  have p16138 := n16138 _v _q h2296
  change (e4465 _v) ∨ (e4458 _v) at p20594
  change (¬ (e4465 _v)) at p16138
  rcases p20594 with hlit | hlit
  · exact (False.elim (p16138 hlit))
  · exact hlit
theorem n22001 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2296 : (e2296 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5138 : (e5138 _v)) : (e7489 _v) := by
  have p16102 := n16102 _v _q h2296
  have p5257 := n5257 _v _q 
  have p21943 := n21943 _v _q h51 h4306 h4653 h4813
  have p17064 := n17064 _v _q 
  have p21999 := n21999 _v _q h51 h2296 h4306 h4653 h4813 h5138
  have p17067 := n17067 _v _q 
  have p17080 := n17080 _v _q 
  have p22000 := n22000 _v _q h2296
  have p17072 := n17072 _v _q 
  have p21997 := n21997 _v _q h51 h2296 h4306 h4653 h4813 h5138
  have p17074 := n17074 _v _q 
  have p15100 := n15100 _v _q h2296
  have p15927 := n15927 _v _q h5138
  have p16115 := n16115 _v _q h2296
  have p16136 := n16136 _v _q h2296 h5138
  have p17069 := n17069 _v _q 
  have p17009 := n17009 _v _q 
  have p16131 := n16131 _v _q h2296
  have p20836 := n20836 _v _q 
  have p20461 := n20461 _v _q 
  have p21946 := n21946 _v _q h51 h4306 h4653 h4813
  have p21793 := n21793 _v _q h2296
  have p17136 := n17136 _v _q 
  have p21902 := n21902 _v _q h51 h4306 h4653 h4813
  have p17087 := n17087 _v _q 
  have p17055 := n17055 _v _q 
  have p17058 := n17058 _v _q 
  have p17098 := n17098 _v _q 
  have p17083 := n17083 _v _q 
  have p21981 := n21981 _v _q h2296
  have p17106 := n17106 _v _q 
  have p17020 := n17020 _v _q 
  have p17093 := n17093 _v _q 
  have p21979 := n21979 _v _q h51 h4306 h4653 h4813
  have p17100 := n17100 _v _q 
  have p17141 := n17141 _v _q 
  have p17102 := n17102 _v _q 
  have p17091 := n17091 _v _q 
  have p17096 := n17096 _v _q 
  have p21748 := n21748 _v _q h51 h4306 h4653 h4813
  have p20757 := n20757 _v _q h5138
  have p17758 := n17758 _v _q 
  have p17124 := n17124 _v _q 
  have p19610 := n19610 _v _q 
  have p17111 := n17111 _v _q 
  have p17115 := n17115 _v _q 
  have p17256 := n17256 _v _q 
  have p17078 := n17078 _v _q 
  have p17113 := n17113 _v _q 
  have p17117 := n17117 _v _q 
  have p20467 := n20467 _v _q 
  have p19665 := n19665 _v _q 
  have p17133 := n17133 _v _q 
  have p17120 := n17120 _v _q 
  have p17104 := n17104 _v _q 
  have p17874 := n17874 _v _q 
  have p17127 := n17127 _v _q 
  have p17089 := n17089 _v _q 
  have p20653 := n20653 _v _q 
  have p21727 := n21727 _v _q h51 h4306 h4653 h4813
  have p17138 := n17138 _v _q h4306
  have p20274 := n20274 _v _q 
  have p17060 := n17060 _v _q h4653
  have p20470 := n20470 _v _q 
  have p17050 := n17050 _v _q 
  have p16778 := n16778 _v _q 
  have p17122 := n17122 _v _q 
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p20829 := n20829 _v _q 
  have p20426 := n20426 _v _q 
  have p20126 := n20126 _v _q 
  have p17110 := n17110 _v _q 
  have p17053 := n17053 _v _q 
  have p20096 := n20096 _v _q 
  have p17131 := n17131 _v _q 
  have p17108 := n17108 _v _q 
  have p17294 := n17294 _v _q 
  have p16943 := n16943 _v _q 
  have p13951 := n13951 _v _q 
  exact FloorCertificate.node_22001 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2902 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e4215 _v) (e4541 _v) (e4808 _v) p16102 p5257 p21943 p17064 p21999 p17067 p17080 p22000 p17072 p21997 p17074 p15100 p15927 p16115 p16136 p17069 p17009 p16131 p20836 p20461 p21946 p21793 p17136 p21902 p17087 p17055 p17058 p17098 p17083 p21981 p17106 p17020 p17093 p21979 p17100 p17141 p17102 p17091 p17096 p21748 p20757 p17758 p17124 p19610 p17111 p17115 p17256 p17078 p17113 p17117 p20467 p19665 p17133 p17120 p17104 p17874 p17127 p17089 p20653 p21727 p17138 p20274 p17060 p20470 p17050 p16778 p17122 p4983 p16729 p20829 p20426 p20126 p17110 p17053 p20096 p17131 p17108 p17294 p16943 p13951
theorem n22003 (_v : Vars) (_q : Query _v)  : (e22002 _v) := by
  by_contra hc
  change ¬ ((e79 _v) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e2296 _v))) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h2296 : (e2296 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h5138 : (e5138 _v) := (fun hn => hc (Or.inl hn))
  have p22001 := n22001 _v _q h51 h2296 h4306 h4653 h4813 h5138
  exact p22001
end
end Assembly
