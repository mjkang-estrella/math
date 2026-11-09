import Dag265
import generated.th_lemma_35
import generated.th_lemma_36
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n22148 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3158 : (e3158 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6600 : (e6600 _v)) : (e5145 _v) := by
  have p15925 := n15925 _v _q 
  have p22147 := n22147 _v _q h51 h3158 h4101 h4306 h4653 h4813 h6600
  change (e5149 _v) ∨ (e5145 _v) at p15925
  change (¬ (e5149 _v)) at p22147
  rcases p15925 with hlit | hlit
  · exact (False.elim (p22147 hlit))
  · exact hlit
theorem n22149 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3158 : (e3158 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6600 : (e6600 _v)) : (e7489 _v) := by
  have p22138 := n22138 _v _q h51 h3158 h4101 h4306 h4653 h4813
  have p22136 := n22136 _v _q h51 h3158 h4101 h4306 h4653 h4813
  have p8439 := n8439 _v _q h6600
  have p17147 := n17147 _v _q 
  have p15907 := n15907 _v _q h6600
  have p21899 := n21899 _v _q h51 h4306 h4653 h4813
  have p21728 := n21728 _v _q h51 h4306 h4653 h4813
  have p16729 := n16729 _v _q h51
  have p22148 := n22148 _v _q h51 h3158 h4101 h4306 h4653 h4813 h6600
  have p20126 := n20126 _v _q 
  have p20426 := n20426 _v _q 
  have p17110 := n17110 _v _q 
  have p20829 := n20829 _v _q 
  have p17009 := n17009 _v _q 
  have p22146 := n22146 _v _q h51 h3158 h4101 h4306 h4653 h4813 h6600
  have p22101 := n22101 _v _q h51 h3158 h4101 h4306 h4653 h4813
  have p22108 := n22108 _v _q h51 h3158 h4101 h4306 h4653 h4813
  have p22143 := n22143 _v _q h51 h3158 h4101 h4306 h4653 h4813
  have p22105 := n22105 _v _q h51 h3158 h4101 h4306 h4653 h4813
  have p22039 := n22039 _v _q h51 h3158 h4101 h4306 h4653 h4813
  have p17131 := n17131 _v _q 
  have p17108 := n17108 _v _q 
  have p17294 := n17294 _v _q 
  have p16943 := n16943 _v _q 
  have p17064 := n17064 _v _q 
  have p17067 := n17067 _v _q 
  have p17080 := n17080 _v _q 
  have p17053 := n17053 _v _q 
  have p17072 := n17072 _v _q 
  have p17074 := n17074 _v _q 
  have p5255 := n5255 _v _q 
  have p17069 := n17069 _v _q 
  have p20096 := n20096 _v _q 
  have p17065 := n17065 _v _q h4101
  have p20836 := n20836 _v _q 
  have p20461 := n20461 _v _q 
  have p21948 := n21948 _v _q h51 h4306 h4653 h4813
  have p17256 := n17256 _v _q 
  have p17136 := n17136 _v _q 
  have p21906 := n21906 _v _q h51 h4306 h4653 h4813
  have p17087 := n17087 _v _q 
  have p17055 := n17055 _v _q 
  have p17058 := n17058 _v _q 
  have p17098 := n17098 _v _q 
  have p17083 := n17083 _v _q 
  have p17106 := n17106 _v _q 
  have p17020 := n17020 _v _q 
  have p17093 := n17093 _v _q 
  have p21984 := n21984 _v _q h51 h4306 h4653 h4813
  have p17100 := n17100 _v _q 
  have p17141 := n17141 _v _q 
  have p17102 := n17102 _v _q 
  have p17091 := n17091 _v _q 
  have p17096 := n17096 _v _q 
  have p21989 := n21989 _v _q h51 h4306 h4653 h4813
  have p17758 := n17758 _v _q 
  have p17124 := n17124 _v _q 
  have p19610 := n19610 _v _q 
  have p17111 := n17111 _v _q 
  have p17115 := n17115 _v _q 
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
  have p17138 := n17138 _v _q h4306
  have p20274 := n20274 _v _q 
  have p17060 := n17060 _v _q h4653
  have p20470 := n20470 _v _q 
  have p17050 := n17050 _v _q 
  have p16778 := n16778 _v _q 
  have p17122 := n17122 _v _q 
  have p4983 := n4983 _v _q h4813
  have p13951 := n13951 _v _q 
  have p22037 := n22037 _v _q h51 h3158 h4101 h4306 h4653 h4813
  have p16885 := n16885 _v _q h3158
  exact FloorCertificate.node_22149 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2883 _v) (e2902 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p22138 p22136 p8439 p17147 p15907 p21899 p21728 p16729 p22148 p20126 p20426 p17110 p20829 p17009 p22146 p22101 p22108 p22143 p22105 p22039 p17131 p17108 p17294 p16943 p17064 p17067 p17080 p17053 p17072 p17074 p5255 p17069 p20096 p17065 p20836 p20461 p21948 p17256 p17136 p21906 p17087 p17055 p17058 p17098 p17083 p17106 p17020 p17093 p21984 p17100 p17141 p17102 p17091 p17096 p21989 p17758 p17124 p19610 p17111 p17115 p17078 p17113 p17117 p20467 p19665 p17133 p17120 p17104 p17874 p17127 p17089 p20653 p17138 p20274 p17060 p20470 p17050 p16778 p17122 p4983 p13951 p22037 p16885
theorem n22151 (_v : Vars) (_q : Query _v)  : (e22150 _v) := by
  by_contra hc
  change ¬ ((e2402 _v) ∨ (¬ (e51 _v)) ∨ (¬ (e4101 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e3158 _v))) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h3158 : (e3158 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn)))))))
  have h4101 : (e4101 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h6600 : (e6600 _v) := (fun hn => hc (Or.inl hn))
  have p22149 := n22149 _v _q h51 h3158 h4101 h4306 h4653 h4813 h6600
  exact p22149
theorem n22152 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3158 : (e3158 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e2402 _v) := by
  have p22151 := n22151 _v _q 
  have p16885 := n16885 _v _q h3158
  have p17065 := n17065 _v _q h4101
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  change (e2402 _v) ∨ (¬ (e51 _v)) ∨ (¬ (e4101 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e3158 _v)) at p22151
  rcases p22151 with hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p17065))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p16885))
theorem n22153 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3158 : (e3158 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e3929 _v) := by
  have p14484 := n14484 _v _q 
  have p22152 := n22152 _v _q h51 h3158 h4101 h4306 h4653 h4813
  change (¬ (e2402 _v)) ∨ (¬ (e3923 _v)) at p14484
  rcases p14484 with hlit | hlit
  · exact (False.elim (hlit p22152))
  · exact hlit
theorem n22154 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3158 : (e3158 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e3133 _v) := by
  have p22039 := n22039 _v _q h51 h3158 h4101 h4306 h4653 h4813
  have p22101 := n22101 _v _q h51 h3158 h4101 h4306 h4653 h4813
  have p22037 := n22037 _v _q h51 h3158 h4101 h4306 h4653 h4813
  exact FloorCertificate.node_22154 (e2 _v) (e9 _v) (e17 _v) (e110 _v) (e2945 _v) (e3141 _v) p22039 p22101 p22037
theorem n22155 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3158 : (e3158 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e3919 _v) := by
  have p14797 := n14797 _v _q 
  have p22153 := n22153 _v _q h51 h3158 h4101 h4306 h4653 h4813
  change (e3923 _v) ∨ (e3919 _v) at p14797
  change (¬ (e3923 _v)) at p22153
  rcases p14797 with hlit | hlit
  · exact (False.elim (p22153 hlit))
  · exact hlit
theorem n22156 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3158 : (e3158 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5145 : (e5145 _v)) : (e2358 _v) := by
  have p21986 := n21986 _v _q 
  have p17245 := n17245 _v _q h5145
  have p22138 := n22138 _v _q h51 h3158 h4101 h4306 h4653 h4813
  have p22111 := n22111 _v _q h51 h3158 h4101 h4306 h4653 h4813
  have p22154 := n22154 _v _q h51 h3158 h4101 h4306 h4653 h4813
  have p22155 := n22155 _v _q h51 h3158 h4101 h4306 h4653 h4813
  have p22105 := n22105 _v _q h51 h3158 h4101 h4306 h4653 h4813
  have p17065 := n17065 _v _q h4101
  have p16885 := n16885 _v _q h3158
  have p22143 := n22143 _v _q h51 h3158 h4101 h4306 h4653 h4813
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  change (e2358 _v) ∨ (¬ (e4459 _v)) ∨ (¬ (e3919 _v)) ∨ (¬ (e3133 _v)) ∨ (¬ (e5145 _v)) ∨ (¬ (e4679 _v)) ∨ (¬ (e4264 _v)) ∨ (¬ (e4101 _v)) ∨ (¬ (e3158 _v)) ∨ (¬ (e8045 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) at p21986
  rcases p21986 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p22111))
  · exact (False.elim (hlit p22155))
  · exact (False.elim (hlit p22154))
  · exact (False.elim (hlit p17245))
  · exact (False.elim (hlit p22138))
  · exact (False.elim (hlit p22105))
  · exact (False.elim (hlit p17065))
  · exact (False.elim (hlit p16885))
  · exact (False.elim (hlit p22143))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p16729))
theorem n22157 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3158 : (e3158 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5145 : (e5145 _v)) : (e7489 _v) := by
  have p22138 := n22138 _v _q h51 h3158 h4101 h4306 h4653 h4813
  have p13951 := n13951 _v _q 
  have p16885 := n16885 _v _q h3158
  have p22037 := n22037 _v _q h51 h3158 h4101 h4306 h4653 h4813
  have p22156 := n22156 _v _q h51 h3158 h4101 h4306 h4653 h4813 h5145
  have p4983 := n4983 _v _q h4813
  have p21728 := n21728 _v _q h51 h4306 h4653 h4813
  have p16729 := n16729 _v _q h51
  have p17245 := n17245 _v _q h5145
  have p20126 := n20126 _v _q 
  have p20426 := n20426 _v _q 
  have p17110 := n17110 _v _q 
  have p20829 := n20829 _v _q 
  have p17009 := n17009 _v _q 
  have p22155 := n22155 _v _q h51 h3158 h4101 h4306 h4653 h4813
  have p22101 := n22101 _v _q h51 h3158 h4101 h4306 h4653 h4813
  have p22108 := n22108 _v _q h51 h3158 h4101 h4306 h4653 h4813
  have p22143 := n22143 _v _q h51 h3158 h4101 h4306 h4653 h4813
  have p22105 := n22105 _v _q h51 h3158 h4101 h4306 h4653 h4813
  have p22039 := n22039 _v _q h51 h3158 h4101 h4306 h4653 h4813
  have p17131 := n17131 _v _q 
  have p17108 := n17108 _v _q 
  have p17294 := n17294 _v _q 
  have p16943 := n16943 _v _q 
  have p17064 := n17064 _v _q 
  have p17067 := n17067 _v _q 
  have p17080 := n17080 _v _q 
  have p17053 := n17053 _v _q 
  have p17072 := n17072 _v _q 
  have p17074 := n17074 _v _q 
  have p5255 := n5255 _v _q 
  have p17069 := n17069 _v _q 
  have p20096 := n20096 _v _q 
  have p17065 := n17065 _v _q h4101
  have p20836 := n20836 _v _q 
  have p20461 := n20461 _v _q 
  have p21948 := n21948 _v _q h51 h4306 h4653 h4813
  have p17256 := n17256 _v _q 
  have p17136 := n17136 _v _q 
  have p21906 := n21906 _v _q h51 h4306 h4653 h4813
  have p17087 := n17087 _v _q 
  have p17055 := n17055 _v _q 
  have p17058 := n17058 _v _q 
  have p17098 := n17098 _v _q 
  have p17083 := n17083 _v _q 
  have p17106 := n17106 _v _q 
  have p17020 := n17020 _v _q 
  have p17093 := n17093 _v _q 
  have p21984 := n21984 _v _q h51 h4306 h4653 h4813
  have p17100 := n17100 _v _q 
  have p17141 := n17141 _v _q 
  have p17102 := n17102 _v _q 
  have p17091 := n17091 _v _q 
  have p17096 := n17096 _v _q 
  have p21989 := n21989 _v _q h51 h4306 h4653 h4813
  have p17758 := n17758 _v _q 
  have p17124 := n17124 _v _q 
  have p19610 := n19610 _v _q 
  have p17111 := n17111 _v _q 
  have p17115 := n17115 _v _q 
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
  have p17138 := n17138 _v _q h4306
  have p20274 := n20274 _v _q 
  have p17060 := n17060 _v _q h4653
  have p20470 := n20470 _v _q 
  have p17050 := n17050 _v _q 
  have p16778 := n16778 _v _q 
  have p17122 := n17122 _v _q 
  have p22136 := n22136 _v _q h51 h3158 h4101 h4306 h4653 h4813
  have p21944 := n21944 _v _q h51 h4306 h4653 h4813
  exact FloorCertificate.node_22157 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2902 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p22138 p13951 p16885 p22037 p22156 p4983 p21728 p16729 p17245 p20126 p20426 p17110 p20829 p17009 p22155 p22101 p22108 p22143 p22105 p22039 p17131 p17108 p17294 p16943 p17064 p17067 p17080 p17053 p17072 p17074 p5255 p17069 p20096 p17065 p20836 p20461 p21948 p17256 p17136 p21906 p17087 p17055 p17058 p17098 p17083 p17106 p17020 p17093 p21984 p17100 p17141 p17102 p17091 p17096 p21989 p17758 p17124 p19610 p17111 p17115 p17078 p17113 p17117 p20467 p19665 p17133 p17120 p17104 p17874 p17127 p17089 p20653 p17138 p20274 p17060 p20470 p17050 p16778 p17122 p22136 p21944
theorem n22159 (_v : Vars) (_q : Query _v)  : (e22158 _v) := by
  by_contra hc
  change ¬ ((¬ (e5145 _v)) ∨ (¬ (e3158 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4101 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v))) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h3158 : (e3158 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h4101 : (e4101 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn)))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h5145 : (e5145 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have p22157 := n22157 _v _q h51 h3158 h4101 h4306 h4653 h4813 h5145
  exact p22157
theorem n22160 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3158 : (e3158 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e5148 _v) := by
  have p22159 := n22159 _v _q 
  have p16885 := n16885 _v _q h3158
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p17065 := n17065 _v _q h4101
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  change (¬ (e5145 _v)) ∨ (¬ (e3158 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4101 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) at p22159
  rcases p22159 with hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p16885))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p17065))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
theorem n22161 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3158 : (e3158 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e5149 _v) := by
  have p15925 := n15925 _v _q 
  have p22160 := n22160 _v _q h51 h3158 h4101 h4306 h4653 h4813
  change (e5149 _v) ∨ (e5145 _v) at p15925
  change (¬ (e5145 _v)) at p22160
  rcases p15925 with hlit | hlit
  · exact hlit
  · exact (False.elim (p22160 hlit))
theorem n22162 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3158 : (e3158 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e79 _v) := by
  have p15115 := n15115 _v _q 
  have p22161 := n22161 _v _q h51 h3158 h4101 h4306 h4653 h4813
  change (e79 _v) ∨ (¬ (e5149 _v)) at p15115
  rcases p15115 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p22161))
theorem n22163 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3158 : (e3158 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e5135 _v) := by
  have p14729 := n14729 _v _q 
  have p22162 := n22162 _v _q h51 h3158 h4101 h4306 h4653 h4813
  change (¬ (e79 _v)) ∨ (¬ (e5134 _v)) at p14729
  rcases p14729 with hlit | hlit
  · exact (False.elim (hlit p22162))
  · exact hlit
theorem n22164 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3158 : (e3158 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e91 _v) := by
  have p16235 := n16235 _v _q 
  have p22163 := n22163 _v _q h51 h3158 h4101 h4306 h4653 h4813
  change (e5134 _v) ∨ (e91 _v) at p16235
  change (¬ (e5134 _v)) at p22163
  rcases p16235 with hlit | hlit
  · exact (False.elim (p22163 hlit))
  · exact hlit
theorem n22165 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3158 : (e3158 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e7489 _v) := by
  have p22162 := n22162 _v _q h51 h3158 h4101 h4306 h4653 h4813
  have p331 := n331 _v _q 
  have p22037 := n22037 _v _q h51 h3158 h4101 h4306 h4653 h4813
  have p17122 := n17122 _v _q 
  have p22136 := n22136 _v _q h51 h3158 h4101 h4306 h4653 h4813
  have p21944 := n21944 _v _q h51 h4306 h4653 h4813
  have p22164 := n22164 _v _q h51 h3158 h4101 h4306 h4653 h4813
  have p22138 := n22138 _v _q h51 h3158 h4101 h4306 h4653 h4813
  have p13951 := n13951 _v _q 
  have p16885 := n16885 _v _q h3158
  have p4983 := n4983 _v _q h4813
  have p21728 := n21728 _v _q h51 h4306 h4653 h4813
  have p16729 := n16729 _v _q h51
  have p20126 := n20126 _v _q 
  have p20426 := n20426 _v _q 
  have p17110 := n17110 _v _q 
  have p20829 := n20829 _v _q 
  have p22155 := n22155 _v _q h51 h3158 h4101 h4306 h4653 h4813
  have p22101 := n22101 _v _q h51 h3158 h4101 h4306 h4653 h4813
  have p22111 := n22111 _v _q h51 h3158 h4101 h4306 h4653 h4813
  have p22143 := n22143 _v _q h51 h3158 h4101 h4306 h4653 h4813
  have p22105 := n22105 _v _q h51 h3158 h4101 h4306 h4653 h4813
  have p22039 := n22039 _v _q h51 h3158 h4101 h4306 h4653 h4813
  have p17131 := n17131 _v _q 
  have p17108 := n17108 _v _q 
  have p17294 := n17294 _v _q 
  have p16943 := n16943 _v _q 
  have p17064 := n17064 _v _q 
  have p17067 := n17067 _v _q 
  have p17080 := n17080 _v _q 
  have p17053 := n17053 _v _q 
  have p17072 := n17072 _v _q 
  have p17074 := n17074 _v _q 
  have p17069 := n17069 _v _q 
  have p20096 := n20096 _v _q 
  have p17065 := n17065 _v _q h4101
  have p20836 := n20836 _v _q 
  have p20461 := n20461 _v _q 
  have p21948 := n21948 _v _q h51 h4306 h4653 h4813
  have p17256 := n17256 _v _q 
  have p17136 := n17136 _v _q 
  have p21906 := n21906 _v _q h51 h4306 h4653 h4813
  have p17087 := n17087 _v _q 
  have p17055 := n17055 _v _q 
  have p17058 := n17058 _v _q 
  have p17098 := n17098 _v _q 
  have p17083 := n17083 _v _q 
  have p17106 := n17106 _v _q 
  have p17020 := n17020 _v _q 
  have p17093 := n17093 _v _q 
  have p21984 := n21984 _v _q h51 h4306 h4653 h4813
  have p17100 := n17100 _v _q 
  have p17141 := n17141 _v _q 
  have p17102 := n17102 _v _q 
  have p17091 := n17091 _v _q 
  have p17096 := n17096 _v _q 
  have p21989 := n21989 _v _q h51 h4306 h4653 h4813
  have p17758 := n17758 _v _q 
  have p17124 := n17124 _v _q 
  have p19610 := n19610 _v _q 
  have p17111 := n17111 _v _q 
  have p17115 := n17115 _v _q 
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
  have p17138 := n17138 _v _q h4306
  have p20274 := n20274 _v _q 
  have p17060 := n17060 _v _q h4653
  have p20470 := n20470 _v _q 
  have p17050 := n17050 _v _q 
  have p16778 := n16778 _v _q 
  exact FloorCertificate.node_22165 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2902 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4541 _v) (e4808 _v) p22162 p331 p22037 p17122 p22136 p21944 p22164 p22138 p13951 p16885 p4983 p21728 p16729 p20126 p20426 p17110 p20829 p22155 p22101 p22111 p22143 p22105 p22039 p17131 p17108 p17294 p16943 p17064 p17067 p17080 p17053 p17072 p17074 p17069 p20096 p17065 p20836 p20461 p21948 p17256 p17136 p21906 p17087 p17055 p17058 p17098 p17083 p17106 p17020 p17093 p21984 p17100 p17141 p17102 p17091 p17096 p21989 p17758 p17124 p19610 p17111 p17115 p17078 p17113 p17117 p20467 p19665 p17133 p17120 p17104 p17874 p17127 p17089 p20653 p17138 p20274 p17060 p20470 p17050 p16778
theorem n22167 (_v : Vars) (_q : Query _v)  : (e22166 _v) := by
  by_contra hc
  change ¬ ((¬ (e3158 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4101 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v))) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h3158 : (e3158 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h4101 : (e4101 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have p22165 := n22165 _v _q h51 h3158 h4101 h4306 h4653 h4813
  exact p22165
theorem n22168 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e3159 _v) := by
  have p22167 := n22167 _v _q 
  have p17065 := n17065 _v _q h4101
  have p16729 := n16729 _v _q h51
  have p4983 := n4983 _v _q h4813
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  change (¬ (e3158 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4101 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) at p22167
  rcases p22167 with hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p17065))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
theorem n22169 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e3162 _v) := by
  have p15126 := n15126 _v _q 
  have p22168 := n22168 _v _q h51 h4101 h4306 h4653 h4813
  change (e3162 _v) ∨ (e3158 _v) at p15126
  change (¬ (e3158 _v)) at p22168
  rcases p15126 with hlit | hlit
  · exact hlit
  · exact (False.elim (p22168 hlit))
theorem n22170 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e6501 _v) := by
  have p14684 := n14684 _v _q 
  have p22169 := n22169 _v _q h51 h4101 h4306 h4653 h4813
  change (¬ (e2179 _v)) ∨ (¬ (e3162 _v)) at p14684
  rcases p14684 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p22169))
theorem n22171 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e6525 _v) := by
  have p8557 := n8557 _v _q 
  have p22170 := n22170 _v _q h51 h4101 h4306 h4653 h4813
  change (¬ (e2242 _v)) ∨ (e2179 _v) at p8557
  change (¬ (e2179 _v)) at p22170
  rcases p8557 with hlit | hlit
  · exact hlit
  · exact (False.elim (p22170 hlit))
theorem n22172 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e8038 _v) := by
  have p21568 := n21568 _v _q 
  have p22171 := n22171 _v _q h51 h4101 h4306 h4653 h4813
  have p17060 := n17060 _v _q h4653
  have p16729 := n16729 _v _q h51
  have p17138 := n17138 _v _q h4306
  have p4983 := n4983 _v _q h4813
  change (¬ (e2475 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4306 _v)) ∨ (e2242 _v) at p21568
  change (¬ (e2242 _v)) at p22171
  rcases p21568 with hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (p22171 hlit))
theorem n22173 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e7807 _v) := by
  have p21596 := n21596 _v _q 
  have p22171 := n22171 _v _q h51 h4101 h4306 h4653 h4813
  have p17060 := n17060 _v _q h4653
  have p16729 := n16729 _v _q h51
  have p17138 := n17138 _v _q h4306
  have p4983 := n4983 _v _q h4813
  change (¬ (e2303 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4306 _v)) ∨ (e2242 _v) at p21596
  change (¬ (e2242 _v)) at p22171
  rcases p21596 with hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (p22171 hlit))
theorem n22174 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e8103 _v) := by
  have p14626 := n14626 _v _q 
  have p22170 := n22170 _v _q h51 h4101 h4306 h4653 h4813
  change (e2179 _v) ∨ (¬ (e8095 _v)) at p14626
  change (¬ (e2179 _v)) at p22170
  rcases p14626 with hlit | hlit
  · exact (False.elim (p22170 hlit))
  · exact hlit
theorem n22175 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e4608 _v) := by
  have p15033 := n15033 _v _q 
  have p22174 := n22174 _v _q h51 h4101 h4306 h4653 h4813
  change (e8095 _v) ∨ (e4608 _v) at p15033
  change (¬ (e8095 _v)) at p22174
  rcases p15033 with hlit | hlit
  · exact (False.elim (p22174 hlit))
  · exact hlit
theorem n22176 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e6776 _v) := by
  have p22170 := n22170 _v _q h51 h4101 h4306 h4653 h4813
  have p21899 := n21899 _v _q h51 h4306 h4653 h4813
  exact FloorCertificate.node_22176 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p22170 p21899
theorem n22177 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e7789 _v) := by
  have p14570 := n14570 _v _q 
  have p22176 := n22176 _v _q h51 h4101 h4306 h4653 h4813
  change (e2781 _v) ∨ (¬ (e7781 _v)) at p14570
  change (¬ (e2781 _v)) at p22176
  rcases p14570 with hlit | hlit
  · exact (False.elim (p22176 hlit))
  · exact hlit
theorem n22178 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e6600 _v) := by
  have p11339 := n11339 _v _q 
  have p22170 := n22170 _v _q h51 h4101 h4306 h4653 h4813
  change (e2179 _v) ∨ (¬ (e2402 _v)) at p11339
  change (¬ (e2179 _v)) at p22170
  rcases p11339 with hlit | hlit
  · exact (False.elim (p22170 hlit))
  · exact hlit
theorem n22179 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e7416 _v) := by
  have p14534 := n14534 _v _q 
  have p22178 := n22178 _v _q h51 h4101 h4306 h4653 h4813
  change (e2402 _v) ∨ (¬ (e7415 _v)) at p14534
  change (¬ (e2402 _v)) at p22178
  rcases p14534 with hlit | hlit
  · exact (False.elim (p22178 hlit))
  · exact hlit
theorem n22180 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e8174 _v) := by
  have p14634 := n14634 _v _q 
  have p22171 := n22171 _v _q h51 h4101 h4306 h4653 h4813
  change (e2242 _v) ∨ (¬ (e8166 _v)) at p14634
  change (¬ (e2242 _v)) at p22171
  rcases p14634 with hlit | hlit
  · exact (False.elim (p22171 hlit))
  · exact hlit
theorem n22181 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e6549 _v) := by
  have p11560 := n11560 _v _q 
  have p22171 := n22171 _v _q h51 h4101 h4306 h4653 h4813
  change (¬ (e2296 _v)) ∨ (e2242 _v) at p11560
  change (¬ (e2242 _v)) at p22171
  rcases p11560 with hlit | hlit
  · exact hlit
  · exact (False.elim (p22171 hlit))
theorem n22182 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e4260 _v) := by
  have p15824 := n15824 _v _q 
  have p22177 := n22177 _v _q h51 h4101 h4306 h4653 h4813
  change (e7781 _v) ∨ (e4260 _v) at p15824
  change (¬ (e7781 _v)) at p22177
  rcases p15824 with hlit | hlit
  · exact (False.elim (p22177 hlit))
  · exact hlit
theorem n22183 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e4420 _v) := by
  have p16832 := n16832 _v _q 
  have p22172 := n22172 _v _q h51 h4101 h4306 h4653 h4813
  have p22173 := n22173 _v _q h51 h4101 h4306 h4653 h4813
  change (e2303 _v) ∨ (¬ (e4419 _v)) ∨ (e2475 _v) at p16832
  change (¬ (e2475 _v)) at p22172
  change (¬ (e2303 _v)) at p22173
  rcases p16832 with hlit | hlit | hlit
  · exact (False.elim (p22173 hlit))
  · exact hlit
  · exact (False.elim (p22172 hlit))
theorem n22184 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e7921 _v) := by
  have p16347 := n16347 _v _q 
  have p22183 := n22183 _v _q h51 h4101 h4306 h4653 h4813
  change (e7921 _v) ∨ (e4419 _v) at p16347
  change (¬ (e4419 _v)) at p22183
  rcases p16347 with hlit | hlit
  · exact hlit
  · exact (False.elim (p22183 hlit))
theorem n22185 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e3937 _v) := by
  have p15012 := n15012 _v _q 
  have p22179 := n22179 _v _q h51 h4101 h4306 h4653 h4813
  change (e7415 _v) ∨ (e3937 _v) at p15012
  change (¬ (e7415 _v)) at p22179
  rcases p15012 with hlit | hlit
  · exact (False.elim (p22179 hlit))
  · exact hlit
theorem n22186 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e4675 _v) := by
  have p15965 := n15965 _v _q 
  have p22180 := n22180 _v _q h51 h4101 h4306 h4653 h4813
  change (e8166 _v) ∨ (e4675 _v) at p15965
  change (¬ (e8166 _v)) at p22180
  rcases p15965 with hlit | hlit
  · exact (False.elim (p22180 hlit))
  · exact hlit
theorem n22187 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e5093 _v) := by
  have p11468 := n11468 _v _q 
  have p22173 := n22173 _v _q h51 h4101 h4306 h4653 h4813
  change (¬ (e13 _v)) ∨ (e2303 _v) at p11468
  change (¬ (e2303 _v)) at p22173
  rcases p11468 with hlit | hlit
  · exact hlit
  · exact (False.elim (p22173 hlit))
theorem n22188 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e5105 _v) := by
  have p15204 := n15204 _v _q 
  have p22187 := n22187 _v _q h51 h4101 h4306 h4653 h4813
  change (e13 _v) ∨ (¬ (e5104 _v)) at p15204
  change (¬ (e13 _v)) at p22187
  rcases p15204 with hlit | hlit
  · exact (False.elim (p22187 hlit))
  · exact hlit
theorem n22189 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e5100 _v) := by
  have p15319 := n15319 _v _q 
  have p22188 := n22188 _v _q h51 h4101 h4306 h4653 h4813
  change (e5104 _v) ∨ (e5100 _v) at p15319
  change (¬ (e5104 _v)) at p22188
  rcases p15319 with hlit | hlit
  · exact (False.elim (p22188 hlit))
  · exact hlit
theorem n22190 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e7819 _v) := by
  have p14994 := n14994 _v _q 
  have p22173 := n22173 _v _q h51 h4101 h4306 h4653 h4813
  change (e2303 _v) ∨ (¬ (e7818 _v)) at p14994
  change (¬ (e2303 _v)) at p22173
  rcases p14994 with hlit | hlit
  · exact (False.elim (p22173 hlit))
  · exact hlit
theorem n22191 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e7814 _v) := by
  have p15221 := n15221 _v _q 
  have p22190 := n22190 _v _q h51 h4101 h4306 h4653 h4813
  change (e7818 _v) ∨ (e7814 _v) at p15221
  change (¬ (e7818 _v)) at p22190
  rcases p15221 with hlit | hlit
  · exact (False.elim (p22190 hlit))
  · exact hlit
theorem n22192 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e8050 _v) := by
  have p15207 := n15207 _v _q 
  have p22172 := n22172 _v _q h51 h4101 h4306 h4653 h4813
  change (e2475 _v) ∨ (¬ (e8049 _v)) at p15207
  change (¬ (e2475 _v)) at p22172
  rcases p15207 with hlit | hlit
  · exact (False.elim (p22172 hlit))
  · exact hlit
theorem n22193 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e8045 _v) := by
  have p15206 := n15206 _v _q 
  have p22192 := n22192 _v _q h51 h4101 h4306 h4653 h4813
  change (e8049 _v) ∨ (e8045 _v) at p15206
  change (¬ (e8049 _v)) at p22192
  rcases p15206 with hlit | hlit
  · exact (False.elim (p22192 hlit))
  · exact hlit
theorem n22194 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e6879 _v) := by
  have p14643 := n14643 _v _q 
  have p22181 := n22181 _v _q h51 h4101 h4306 h4653 h4813
  change (e2296 _v) ∨ (¬ (e6878 _v)) at p14643
  change (¬ (e2296 _v)) at p22181
  rcases p14643 with hlit | hlit
  · exact (False.elim (p22181 hlit))
  · exact hlit
theorem n22195 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e3152 _v) := by
  have p15776 := n15776 _v _q 
  have p22194 := n22194 _v _q h51 h4101 h4306 h4653 h4813
  change (e6878 _v) ∨ (e3152 _v) at p15776
  change (¬ (e6878 _v)) at p22194
  rcases p15776 with hlit | hlit
  · exact (False.elim (p22194 hlit))
  · exact hlit
end
end Assembly
