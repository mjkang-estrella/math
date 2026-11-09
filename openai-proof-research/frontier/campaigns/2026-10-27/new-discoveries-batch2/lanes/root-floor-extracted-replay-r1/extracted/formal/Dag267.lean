import Dag266
import generated.th_lemma_36
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n22196 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e7742 _v) := by
  have p11353 := n11353 _v _q 
  have p22173 := n22173 _v _q h51 h4101 h4306 h4653 h4813
  change (¬ (e2132 _v)) ∨ (e2303 _v) at p11353
  change (¬ (e2303 _v)) at p22173
  rcases p11353 with hlit | hlit
  · exact hlit
  · exact (False.elim (p22173 hlit))
theorem n22197 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e7754 _v) := by
  have p14942 := n14942 _v _q 
  have p22196 := n22196 _v _q h51 h4101 h4306 h4653 h4813
  change (e2132 _v) ∨ (¬ (e7753 _v)) at p14942
  change (¬ (e2132 _v)) at p22196
  rcases p14942 with hlit | hlit
  · exact (False.elim (p22196 hlit))
  · exact hlit
theorem n22198 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e7749 _v) := by
  have p14941 := n14941 _v _q 
  have p22197 := n22197 _v _q h51 h4101 h4306 h4653 h4813
  change (e7753 _v) ∨ (e7749 _v) at p14941
  change (¬ (e7753 _v)) at p22197
  rcases p14941 with hlit | hlit
  · exact (False.elim (p22197 hlit))
  · exact hlit
theorem n22199 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e6772 _v) := by
  have p14855 := n14855 _v _q 
  have p22184 := n22184 _v _q h51 h4101 h4306 h4653 h4813
  change (¬ (e2787 _v)) ∨ (¬ (e7921 _v)) at p14855
  rcases p14855 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p22184))
theorem n22200 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e7945 _v) := by
  have p15228 := n15228 _v _q 
  have p22199 := n22199 _v _q h51 h4101 h4306 h4653 h4813
  change (e2787 _v) ∨ (¬ (e7944 _v)) at p15228
  change (¬ (e2787 _v)) at p22199
  rcases p15228 with hlit | hlit
  · exact (False.elim (p22199 hlit))
  · exact hlit
theorem n22201 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e7935 _v) := by
  have p15266 := n15266 _v _q 
  have p22200 := n22200 _v _q h51 h4101 h4306 h4653 h4813
  change (e7944 _v) ∨ (e7935 _v) at p15266
  change (¬ (e7944 _v)) at p22200
  rcases p15266 with hlit | hlit
  · exact (False.elim (p22200 hlit))
  · exact hlit
theorem n22202 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e7489 _v) := by
  have p22172 := n22172 _v _q h51 h4101 h4306 h4653 h4813
  have p4016 := n4016 _v _q 
  have p22173 := n22173 _v _q h51 h4101 h4306 h4653 h4813
  have p21899 := n21899 _v _q h51 h4306 h4653 h4813
  have p16576 := n16576 _v _q 
  have p22175 := n22175 _v _q h51 h4101 h4306 h4653 h4813
  have p22170 := n22170 _v _q h51 h4101 h4306 h4653 h4813
  have p22182 := n22182 _v _q h51 h4101 h4306 h4653 h4813
  have p22201 := n22201 _v _q h51 h4101 h4306 h4653 h4813
  have p16778 := n16778 _v _q 
  have p17147 := n17147 _v _q 
  have p22185 := n22185 _v _q h51 h4101 h4306 h4653 h4813
  have p17050 := n17050 _v _q 
  have p22186 := n22186 _v _q h51 h4101 h4306 h4653 h4813
  have p4999 := n4999 _v _q h91
  have p17122 := n17122 _v _q 
  have p13951 := n13951 _v _q 
  have p22189 := n22189 _v _q h51 h4101 h4306 h4653 h4813
  have p4983 := n4983 _v _q h4813
  have p21728 := n21728 _v _q h51 h4306 h4653 h4813
  have p16729 := n16729 _v _q h51
  have p20126 := n20126 _v _q 
  have p20426 := n20426 _v _q 
  have p17110 := n17110 _v _q 
  have p20829 := n20829 _v _q 
  have p22191 := n22191 _v _q h51 h4101 h4306 h4653 h4813
  have p17009 := n17009 _v _q 
  have p22193 := n22193 _v _q h51 h4101 h4306 h4653 h4813
  have p22195 := n22195 _v _q h51 h4101 h4306 h4653 h4813
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
  have p22198 := n22198 _v _q h51 h4101 h4306 h4653 h4813
  exact FloorCertificate.node_22202 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2863 _v) (e2877 _v) (e2883 _v) (e2902 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p22172 p4016 p22173 p21899 p16576 p22175 p22170 p22182 p22201 p16778 p17147 p22185 p17050 p22186 p4999 p17122 p13951 p22189 p4983 p21728 p16729 p20126 p20426 p17110 p20829 p22191 p17009 p22193 p22195 p17131 p17108 p17294 p16943 p17064 p17067 p17080 p17053 p17072 p17074 p17069 p20096 p17065 p20836 p20461 p21948 p17256 p17136 p21906 p17087 p17055 p17058 p17098 p17083 p17106 p17020 p17093 p21984 p17100 p17141 p17102 p17091 p17096 p21989 p17758 p17124 p19610 p17111 p17115 p17078 p17113 p17117 p20467 p19665 p17133 p17120 p17104 p17874 p17127 p17089 p20653 p17138 p20274 p17060 p20470 p22198
theorem n22204 (_v : Vars) (_q : Query _v)  : (e22203 _v) := by
  by_contra hc
  change ¬ ((¬ (e91 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4101 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v))) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h4101 : (e4101 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have p22202 := n22202 _v _q h51 h91 h4101 h4306 h4653 h4813
  exact p22202
theorem n22205 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e95 _v) := by
  have p22204 := n22204 _v _q 
  have p17065 := n17065 _v _q h4101
  have p16729 := n16729 _v _q h51
  have p4983 := n4983 _v _q h4813
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  change (¬ (e91 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4101 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) at p22204
  rcases p22204 with hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p17065))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
theorem n22206 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e5134 _v) := by
  have p16235 := n16235 _v _q 
  have p22205 := n22205 _v _q h51 h4101 h4306 h4653 h4813
  change (e5134 _v) ∨ (e91 _v) at p16235
  change (¬ (e91 _v)) at p22205
  rcases p16235 with hlit | hlit
  · exact hlit
  · exact (False.elim (p22205 hlit))
theorem n22207 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e5138 _v) := by
  have p14729 := n14729 _v _q 
  have p22206 := n22206 _v _q h51 h4101 h4306 h4653 h4813
  change (¬ (e79 _v)) ∨ (¬ (e5134 _v)) at p14729
  rcases p14729 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p22206))
theorem n22208 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e5150 _v) := by
  have p15115 := n15115 _v _q 
  have p22207 := n22207 _v _q h51 h4101 h4306 h4653 h4813
  change (e79 _v) ∨ (¬ (e5149 _v)) at p15115
  change (¬ (e79 _v)) at p22207
  rcases p15115 with hlit | hlit
  · exact (False.elim (p22207 hlit))
  · exact hlit
theorem n22209 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e5145 _v) := by
  have p15925 := n15925 _v _q 
  have p22208 := n22208 _v _q h51 h4101 h4306 h4653 h4813
  change (e5149 _v) ∨ (e5145 _v) at p15925
  change (¬ (e5149 _v)) at p22208
  rcases p15925 with hlit | hlit
  · exact (False.elim (p22208 hlit))
  · exact hlit
theorem n22210 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e7489 _v) := by
  have p22209 := n22209 _v _q h51 h4101 h4306 h4653 h4813
  have p22198 := n22198 _v _q h51 h4101 h4306 h4653 h4813
  have p20470 := n20470 _v _q 
  have p21978 := n21978 _v _q h51 h4306 h4653 h4813
  have p22207 := n22207 _v _q h51 h4101 h4306 h4653 h4813
  have p22170 := n22170 _v _q h51 h4101 h4306 h4653 h4813
  have p16576 := n16576 _v _q 
  have p22175 := n22175 _v _q h51 h4101 h4306 h4653 h4813
  have p21899 := n21899 _v _q h51 h4306 h4653 h4813
  have p22182 := n22182 _v _q h51 h4101 h4306 h4653 h4813
  have p22201 := n22201 _v _q h51 h4101 h4306 h4653 h4813
  have p16778 := n16778 _v _q 
  have p17147 := n17147 _v _q 
  have p22185 := n22185 _v _q h51 h4101 h4306 h4653 h4813
  have p17050 := n17050 _v _q 
  have p22186 := n22186 _v _q h51 h4101 h4306 h4653 h4813
  have p17122 := n17122 _v _q 
  have p13951 := n13951 _v _q 
  have p22189 := n22189 _v _q h51 h4101 h4306 h4653 h4813
  have p4983 := n4983 _v _q h4813
  have p21728 := n21728 _v _q h51 h4306 h4653 h4813
  have p16729 := n16729 _v _q h51
  have p20126 := n20126 _v _q 
  have p20426 := n20426 _v _q 
  have p17110 := n17110 _v _q 
  have p20829 := n20829 _v _q 
  have p22191 := n22191 _v _q h51 h4101 h4306 h4653 h4813
  have p17009 := n17009 _v _q 
  have p22193 := n22193 _v _q h51 h4101 h4306 h4653 h4813
  have p22195 := n22195 _v _q h51 h4101 h4306 h4653 h4813
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
  have p5257 := n5257 _v _q 
  have p5391 := n5391 _v _q 
  exact FloorCertificate.node_22210 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2863 _v) (e2877 _v) (e2883 _v) (e2902 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p22209 p22198 p20470 p21978 p22207 p22170 p16576 p22175 p21899 p22182 p22201 p16778 p17147 p22185 p17050 p22186 p17122 p13951 p22189 p4983 p21728 p16729 p20126 p20426 p17110 p20829 p22191 p17009 p22193 p22195 p17131 p17108 p17294 p16943 p17064 p17067 p17080 p17053 p17072 p17074 p17069 p20096 p17065 p20836 p20461 p21948 p17256 p17136 p21906 p17087 p17055 p17058 p17098 p17083 p17106 p17020 p17093 p21984 p17100 p17141 p17102 p17091 p17096 p21989 p17758 p17124 p19610 p17111 p17115 p17078 p17113 p17117 p20467 p19665 p17133 p17120 p17104 p17874 p17127 p17089 p20653 p17138 p20274 p17060 p5257 p5391
theorem n22212 (_v : Vars) (_q : Query _v)  : (e22211 _v) := by
  by_contra hc
  change ¬ ((¬ (e4101 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v))) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4101 : (e4101 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr hn)))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have p22210 := n22210 _v _q h51 h4101 h4306 h4653 h4813
  exact p22210
theorem n22213 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e4106 _v) := by
  have p22212 := n22212 _v _q 
  have p17138 := n17138 _v _q h4306
  have p16729 := n16729 _v _q h51
  have p4983 := n4983 _v _q h4813
  have p17060 := n17060 _v _q h4653
  change (¬ (e4101 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) at p22212
  rcases p22212 with hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
theorem n22214 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e4108 _v) := by
  have p14929 := n14929 _v _q 
  have p22213 := n22213 _v _q h51 h4306 h4653 h4813
  change (e4108 _v) ∨ (e4101 _v) at p14929
  change (¬ (e4101 _v)) at p22213
  rcases p14929 with hlit | hlit
  · exact hlit
  · exact (False.elim (p22213 hlit))
theorem n22215 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e6750 _v) := by
  have p14689 := n14689 _v _q 
  have p22214 := n22214 _v _q h51 h4306 h4653 h4813
  change (¬ (e2733 _v)) ∨ (¬ (e4108 _v)) at p14689
  rcases p14689 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p22214))
theorem n22216 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e7597 _v) := by
  have p14525 := n14525 _v _q 
  have p22215 := n22215 _v _q h51 h4306 h4653 h4813
  change (e2733 _v) ∨ (¬ (e7589 _v)) at p14525
  change (¬ (e2733 _v)) at p22215
  rcases p14525 with hlit | hlit
  · exact (False.elim (p22215 hlit))
  · exact hlit
theorem n22217 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e4096 _v) := by
  have p15703 := n15703 _v _q 
  have p22216 := n22216 _v _q h51 h4306 h4653 h4813
  change (e7589 _v) ∨ (e4096 _v) at p15703
  change (¬ (e7589 _v)) at p22216
  rcases p15703 with hlit | hlit
  · exact (False.elim (p22216 hlit))
  · exact hlit
theorem n22218 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e6776 _v) := by
  have p8424 := n8424 _v _q 
  have p22215 := n22215 _v _q h51 h4306 h4653 h4813
  change (e2733 _v) ∨ (¬ (e2781 _v)) at p8424
  change (¬ (e2733 _v)) at p22215
  rcases p8424 with hlit | hlit
  · exact (False.elim (p22215 hlit))
  · exact hlit
theorem n22219 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e7789 _v) := by
  have p14570 := n14570 _v _q 
  have p22218 := n22218 _v _q h51 h4306 h4653 h4813
  change (e2781 _v) ∨ (¬ (e7781 _v)) at p14570
  change (¬ (e2781 _v)) at p22218
  rcases p14570 with hlit | hlit
  · exact (False.elim (p22218 hlit))
  · exact hlit
theorem n22220 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e6549 _v) := by
  have p11571 := n11571 _v _q 
  have p22215 := n22215 _v _q h51 h4306 h4653 h4813
  change (e2733 _v) ∨ (¬ (e2296 _v)) at p11571
  change (¬ (e2733 _v)) at p22215
  rcases p11571 with hlit | hlit
  · exact (False.elim (p22215 hlit))
  · exact hlit
theorem n22221 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e6879 _v) := by
  have p14643 := n14643 _v _q 
  have p22220 := n22220 _v _q h51 h4306 h4653 h4813
  change (e2296 _v) ∨ (¬ (e6878 _v)) at p14643
  change (¬ (e2296 _v)) at p22220
  rcases p14643 with hlit | hlit
  · exact (False.elim (p22220 hlit))
  · exact hlit
theorem n22222 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e79 _v) := by
  have p22215 := n22215 _v _q h51 h4306 h4653 h4813
  have p21978 := n21978 _v _q h51 h4306 h4653 h4813
  exact FloorCertificate.node_22222 (e2 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p22215 p21978
theorem n22223 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e5135 _v) := by
  have p14729 := n14729 _v _q 
  have p22222 := n22222 _v _q h51 h4306 h4653 h4813
  change (¬ (e79 _v)) ∨ (¬ (e5134 _v)) at p14729
  rcases p14729 with hlit | hlit
  · exact (False.elim (hlit p22222))
  · exact hlit
theorem n22224 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e4260 _v) := by
  have p15824 := n15824 _v _q 
  have p22219 := n22219 _v _q h51 h4306 h4653 h4813
  change (e7781 _v) ∨ (e4260 _v) at p15824
  change (¬ (e7781 _v)) at p22219
  rcases p15824 with hlit | hlit
  · exact (False.elim (p22219 hlit))
  · exact hlit
theorem n22225 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e3152 _v) := by
  have p15776 := n15776 _v _q 
  have p22221 := n22221 _v _q h51 h4306 h4653 h4813
  change (e6878 _v) ∨ (e3152 _v) at p15776
  change (¬ (e6878 _v)) at p22221
  rcases p15776 with hlit | hlit
  · exact (False.elim (p22221 hlit))
  · exact hlit
theorem n22226 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e91 _v) := by
  have p16235 := n16235 _v _q 
  have p22223 := n22223 _v _q h51 h4306 h4653 h4813
  change (e5134 _v) ∨ (e91 _v) at p16235
  change (¬ (e5134 _v)) at p22223
  rcases p16235 with hlit | hlit
  · exact (False.elim (p22223 hlit))
  · exact hlit
theorem n22227 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6501 : (e6501 _v)) : (e8310 _v) := by
  have p21481 := n21481 _v _q 
  have p15772 := n15772 _v _q h6501
  have p16729 := n16729 _v _q h51
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4983 := n4983 _v _q h4813
  have p22215 := n22215 _v _q h51 h4306 h4653 h4813
  have p22226 := n22226 _v _q h51 h4306 h4653 h4813
  change (e2733 _v) ∨ (¬ (e91 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (e2242 _v) ∨ (¬ (e2529 _v)) at p21481
  change (¬ (e2242 _v)) at p15772
  change (¬ (e2733 _v)) at p22215
  rcases p21481 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact (False.elim (p22215 hlit))
  · exact (False.elim (hlit p22226))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (p15772 hlit))
  · exact hlit
theorem n22228 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6501 : (e6501 _v)) : (e48 _v) := by
  have p16732 := n16732 _v _q 
  have p21646 := n21646 _v _q h51 h4306 h4653 h4813 h6501
  have p16729 := n16729 _v _q h51
  change (e48 _v) ∨ (¬ (e7495 _v)) ∨ (¬ (e51 _v)) at p16732
  rcases p16732 with hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p21646))
  · exact (False.elim (hlit p16729))
theorem n22229 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6501 : (e6501 _v)) : (e7489 _v) := by
  have p16977 := n16977 _v _q 
  have p22215 := n22215 _v _q h51 h4306 h4653 h4813
  have p22217 := n22217 _v _q h51 h4306 h4653 h4813
  have p13951 := n13951 _v _q 
  have p21623 := n21623 _v _q h51 h4306 h4653 h4813 h6501
  have p20470 := n20470 _v _q 
  have p20274 := n20274 _v _q 
  have p17060 := n17060 _v _q h4653
  have p21899 := n21899 _v _q h51 h4306 h4653 h4813
  have p16576 := n16576 _v _q 
  have p15641 := n15641 _v _q h6501
  have p17138 := n17138 _v _q h4306
  have p22224 := n22224 _v _q h51 h4306 h4653 h4813
  have p21644 := n21644 _v _q h51 h4306 h4653 h4813 h6501
  have p16778 := n16778 _v _q 
  have p17147 := n17147 _v _q 
  have p16325 := n16325 _v _q h6501
  have p17050 := n17050 _v _q 
  have p16633 := n16633 _v _q h6501
  have p17122 := n17122 _v _q 
  have p21628 := n21628 _v _q h51 h4306 h4653 h4813 h6501
  have p4983 := n4983 _v _q h4813
  have p21728 := n21728 _v _q h51 h4306 h4653 h4813
  have p16729 := n16729 _v _q h51
  have p20126 := n20126 _v _q 
  have p20426 := n20426 _v _q 
  have p17110 := n17110 _v _q 
  have p20829 := n20829 _v _q 
  have p21630 := n21630 _v _q h51 h4306 h4653 h4813 h6501
  have p17009 := n17009 _v _q 
  have p21632 := n21632 _v _q h51 h4306 h4653 h4813 h6501
  have p22225 := n22225 _v _q h51 h4306 h4653 h4813
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
  have p21602 := n21602 _v _q h51 h4306 h4653 h4813 h6501
  have p22226 := n22226 _v _q h51 h4306 h4653 h4813
  have p22227 := n22227 _v _q h51 h4306 h4653 h4813 h6501
  have p22228 := n22228 _v _q h51 h4306 h4653 h4813 h6501
  exact FloorCertificate.node_22229 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2863 _v) (e2877 _v) (e2883 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p16977 p22215 p22217 p13951 p21623 p20470 p20274 p17060 p21899 p16576 p15641 p17138 p22224 p21644 p16778 p17147 p16325 p17050 p16633 p17122 p21628 p4983 p21728 p16729 p20126 p20426 p17110 p20829 p21630 p17009 p21632 p22225 p17131 p17108 p17294 p16943 p17064 p17067 p17080 p17053 p17072 p17074 p17069 p20096 p20836 p20461 p21948 p17256 p17136 p21906 p17087 p17055 p17058 p17098 p17083 p17106 p17020 p17093 p21984 p17100 p17141 p17102 p17091 p17096 p21989 p17758 p17124 p19610 p17111 p17115 p17078 p17113 p17117 p20467 p19665 p17133 p17120 p17104 p17874 p17127 p17089 p20653 p21602 p22226 p22227 p22228
theorem n22231 (_v : Vars) (_q : Query _v)  : (e22230 _v) := by
  by_contra hc
  change ¬ ((e2179 _v) ∨ (¬ (e4653 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v))) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr hn)))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h6501 : (e6501 _v) := (fun hn => hc (Or.inl hn))
  have p22229 := n22229 _v _q h51 h4306 h4653 h4813 h6501
  exact p22229
theorem n22232 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e2179 _v) := by
  have p22231 := n22231 _v _q 
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  change (e2179 _v) ∨ (¬ (e4653 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) at p22231
  rcases p22231 with hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p16729))
theorem n22233 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e4616 _v) := by
  have p14684 := n14684 _v _q 
  have p22232 := n22232 _v _q h51 h4306 h4653 h4813
  change (¬ (e2179 _v)) ∨ (¬ (e3162 _v)) at p14684
  rcases p14684 with hlit | hlit
  · exact (False.elim (hlit p22232))
  · exact hlit
theorem n22234 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e3158 _v) := by
  have p15126 := n15126 _v _q 
  have p22233 := n22233 _v _q h51 h4306 h4653 h4813
  change (e3162 _v) ∨ (e3158 _v) at p15126
  change (¬ (e3162 _v)) at p22233
  rcases p15126 with hlit | hlit
  · exact (False.elim (p22233 hlit))
  · exact hlit
theorem n22235 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e2529 _v) := by
  have p22234 := n22234 _v _q h51 h4306 h4653 h4813
  have p16578 := n16578 _v _q 
  have p16858 := n16858 _v _q 
  have p22215 := n22215 _v _q h51 h4306 h4653 h4813
  exact FloorCertificate.node_22235 (e2 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) (e2863 _v) (e2935 _v) p22234 p16578 p16858 p22215
theorem n22236 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e8307 _v) := by
  have p14906 := n14906 _v _q 
  have p22235 := n22235 _v _q h51 h4306 h4653 h4813
  change (¬ (e2529 _v)) ∨ (¬ (e8301 _v)) at p14906
  rcases p14906 with hlit | hlit
  · exact (False.elim (hlit p22235))
  · exact hlit
theorem n22237 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e4838 _v) := by
  have p16285 := n16285 _v _q 
  have p22236 := n22236 _v _q h51 h4306 h4653 h4813
  change (e8301 _v) ∨ (e4838 _v) at p16285
  change (¬ (e8301 _v)) at p22236
  rcases p16285 with hlit | hlit
  · exact (False.elim (p22236 hlit))
  · exact hlit
theorem n22238 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e2242 _v) := by
  have p21481 := n21481 _v _q 
  have p22235 := n22235 _v _q h51 h4306 h4653 h4813
  have p16729 := n16729 _v _q h51
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4983 := n4983 _v _q h4813
  have p22215 := n22215 _v _q h51 h4306 h4653 h4813
  have p22226 := n22226 _v _q h51 h4306 h4653 h4813
  change (e2733 _v) ∨ (¬ (e91 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (e2242 _v) ∨ (¬ (e2529 _v)) at p21481
  change (¬ (e2733 _v)) at p22215
  rcases p21481 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact (False.elim (p22215 hlit))
  · exact (False.elim (hlit p22226))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p4983))
  · exact hlit
  · exact (False.elim (hlit p22235))
theorem n22239 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e7489 _v) := by
  have p21392 := n21392 _v _q 
  have p22237 := n22237 _v _q h51 h4306 h4653 h4813
  have p22238 := n22238 _v _q h51 h4306 h4653 h4813
  have p21944 := n21944 _v _q h51 h4306 h4653 h4813
  have p22215 := n22215 _v _q h51 h4306 h4653 h4813
  have p21906 := n21906 _v _q h51 h4306 h4653 h4813
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p22225 := n22225 _v _q h51 h4306 h4653 h4813
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p22226 := n22226 _v _q h51 h4306 h4653 h4813
  have p22218 := n22218 _v _q h51 h4306 h4653 h4813
  change (e2733 _v) ∨ (e2468 _v) ∨ (¬ (e3152 _v)) ∨ (¬ (e2242 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e91 _v)) ∨ (e2781 _v) at p21392
  change (¬ (e2468 _v)) at p21944
  change (¬ (e2733 _v)) at p22215
  change (¬ (e2781 _v)) at p22218
  rcases p21392 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact (False.elim (p22215 hlit))
  · exact (False.elim (p21944 hlit))
  · exact (False.elim (hlit p22225))
  · exact (False.elim (hlit p22238))
  · exact (False.elim (hlit p21906))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p22237))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p22226))
  · exact (False.elim (p22218 hlit))
theorem n22241 (_v : Vars) (_q : Query _v)  : (e22240 _v) := by
  by_contra hc
  change ¬ ((¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v))) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr hn))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have p22239 := n22239 _v _q h51 h4306 h4653 h4813
  exact p22239
theorem n22242 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) : (e4814 _v) := by
  have p22241 := n22241 _v _q 
  have p17286 := n17286 _v _q h51
  have p17288 := n17288 _v _q h51
  have p16729 := n16729 _v _q h51
  change (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) at p22241
  rcases p22241 with hlit | hlit | hlit | hlit
  · exact (False.elim (hlit p17288))
  · exact (False.elim (hlit p17286))
  · exact hlit
  · exact (False.elim (hlit p16729))
theorem n22243 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) : (e8284 _v) := by
  have p16259 := n16259 _v _q 
  have p22242 := n22242 _v _q h51
  change (e8284 _v) ∨ (e4813 _v) at p16259
  change (¬ (e4813 _v)) at p22242
  rcases p16259 with hlit | hlit
  · exact hlit
  · exact (False.elim (p22242 hlit))
theorem n22244 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) : (e2522 _v) := by
  have p14657 := n14657 _v _q 
  have p22243 := n22243 _v _q h51
  change (e2522 _v) ∨ (¬ (e8284 _v)) at p14657
  rcases p14657 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p22243))
end
end Assembly
