import Dag258
import generated.th_lemma_34
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n21804 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2296 : (e2296 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5195 : (e5195 _v)) : (e5148 _v) := by
  have p21803 := n21803 _v _q 
  have p8583 := n8583 _v _q h2296
  have p17060 := n17060 _v _q h4653
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p17138 := n17138 _v _q h4306
  have p8549 := n8549 _v _q h5195
  change (¬ (e5145 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e2296 _v)) ∨ (e196 _v) at p21803
  change (¬ (e196 _v)) at p8549
  rcases p21803 with hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p8583))
  · exact (False.elim (p8549 hlit))
theorem n21805 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2296 : (e2296 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5195 : (e5195 _v)) : (e5149 _v) := by
  have p15925 := n15925 _v _q 
  have p21804 := n21804 _v _q h51 h2296 h4306 h4653 h4813 h5195
  change (e5149 _v) ∨ (e5145 _v) at p15925
  change (¬ (e5145 _v)) at p21804
  rcases p15925 with hlit | hlit
  · exact hlit
  · exact (False.elim (p21804 hlit))
theorem n21806 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2296 : (e2296 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5195 : (e5195 _v)) : (e79 _v) := by
  have p15115 := n15115 _v _q 
  have p21805 := n21805 _v _q h51 h2296 h4306 h4653 h4813 h5195
  change (e79 _v) ∨ (¬ (e5149 _v)) at p15115
  rcases p15115 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p21805))
theorem n21807 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2296 : (e2296 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5195 : (e5195 _v)) : (e5135 _v) := by
  have p14729 := n14729 _v _q 
  have p21806 := n21806 _v _q h51 h2296 h4306 h4653 h4813 h5195
  change (¬ (e79 _v)) ∨ (¬ (e5134 _v)) at p14729
  rcases p14729 with hlit | hlit
  · exact (False.elim (hlit p21806))
  · exact hlit
theorem n21808 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2296 : (e2296 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5195 : (e5195 _v)) : (e91 _v) := by
  have p16235 := n16235 _v _q 
  have p21807 := n21807 _v _q h51 h2296 h4306 h4653 h4813 h5195
  change (e5134 _v) ∨ (e91 _v) at p16235
  change (¬ (e5134 _v)) at p21807
  rcases p16235 with hlit | hlit
  · exact (False.elim (p21807 hlit))
  · exact hlit
theorem n21809 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2296 : (e2296 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5195 : (e5195 _v)) (h6600 : (e6600 _v)) : (e7489 _v) := by
  have p17758 := n17758 _v _q 
  have p21737 := n21737 _v _q h51 h4306 h4653 h4813 h5195
  have p21793 := n21793 _v _q h2296
  have p17124 := n17124 _v _q 
  have p15100 := n15100 _v _q h2296
  have p17111 := n17111 _v _q 
  have p17115 := n17115 _v _q 
  have p21789 := n21789 _v _q h51 h4306 h4653 h4813 h5195
  have p17256 := n17256 _v _q 
  have p13951 := n13951 _v _q 
  have p17113 := n17113 _v _q 
  have p17117 := n17117 _v _q 
  have p20467 := n20467 _v _q 
  have p16115 := n16115 _v _q h2296
  have p21799 := n21799 _v _q h2296 h5195
  have p19665 := n19665 _v _q 
  have p17133 := n17133 _v _q 
  have p17120 := n17120 _v _q 
  have p21808 := n21808 _v _q h51 h2296 h4306 h4653 h4813 h5195
  have p17104 := n17104 _v _q 
  have p17874 := n17874 _v _q 
  have p17127 := n17127 _v _q 
  have p17089 := n17089 _v _q 
  have p21740 := n21740 _v _q h5195
  have p21770 := n21770 _v _q h51 h4306 h4653 h4813 h5195
  have p21727 := n21727 _v _q h51 h4306 h4653 h4813
  have p16102 := n16102 _v _q h2296
  have p15907 := n15907 _v _q h6600
  have p17138 := n17138 _v _q h4306
  have p20274 := n20274 _v _q 
  have p17060 := n17060 _v _q h4653
  have p20470 := n20470 _v _q 
  have p17953 := n17953 _v _q 
  have p17050 := n17050 _v _q 
  have p16778 := n16778 _v _q 
  have p17122 := n17122 _v _q 
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p20829 := n20829 _v _q 
  have p8439 := n8439 _v _q h6600
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
  have p8583 := n8583 _v _q h2296
  have p8549 := n8549 _v _q h5195
  have p17141 := n17141 _v _q 
  have p17100 := n17100 _v _q 
  have p19610 := n19610 _v _q 
  have p17102 := n17102 _v _q 
  have p17096 := n17096 _v _q 
  have p17147 := n17147 _v _q 
  have p15938 := n15938 _v _q h5195
  have p21800 := n21800 _v _q h2296 h5195
  have p20827 := n20827 _v _q 
  have p17020 := n17020 _v _q 
  have p21804 := n21804 _v _q h51 h2296 h4306 h4653 h4813 h5195
  exact FloorCertificate.node_21809 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2883 _v) (e2902 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e4541 _v) (e4808 _v) p17758 p21737 p21793 p17124 p15100 p17111 p17115 p21789 p17256 p13951 p17113 p17117 p20467 p16115 p21799 p19665 p17133 p17120 p21808 p17104 p17874 p17127 p17089 p21740 p21770 p21727 p16102 p15907 p17138 p20274 p17060 p20470 p17953 p17050 p16778 p17122 p4983 p16729 p20829 p8439 p20426 p20126 p17110 p17053 p20096 p17131 p17108 p17294 p16943 p17058 p17064 p17067 p17080 p17072 p17074 p17069 p20461 p20836 p20653 p17078 p17136 p17087 p17083 p17055 p17093 p17091 p17098 p17106 p8583 p8549 p17141 p17100 p19610 p17102 p17096 p17147 p15938 p21800 p20827 p17020 p21804
theorem n21811 (_v : Vars) (_q : Query _v)  : (e21810 _v) := by
  by_contra hc
  change ¬ ((e2402 _v) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e2296 _v)) ∨ (e196 _v)) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h2296 : (e2296 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h5195 : (e5195 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn)))))))
  have h6600 : (e6600 _v) := (fun hn => hc (Or.inl hn))
  have p21809 := n21809 _v _q h51 h2296 h4306 h4653 h4813 h5195 h6600
  exact p21809
theorem n21812 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2296 : (e2296 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5195 : (e5195 _v)) : (e2402 _v) := by
  have p21811 := n21811 _v _q 
  have p8583 := n8583 _v _q h2296
  have p17060 := n17060 _v _q h4653
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p17138 := n17138 _v _q h4306
  have p8549 := n8549 _v _q h5195
  change (e2402 _v) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e2296 _v)) ∨ (e196 _v) at p21811
  change (¬ (e196 _v)) at p8549
  rcases p21811 with hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p8583))
  · exact (False.elim (p8549 hlit))
theorem n21813 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2296 : (e2296 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5195 : (e5195 _v)) : (e3929 _v) := by
  have p14484 := n14484 _v _q 
  have p21812 := n21812 _v _q h51 h2296 h4306 h4653 h4813 h5195
  change (¬ (e2402 _v)) ∨ (¬ (e3923 _v)) at p14484
  rcases p14484 with hlit | hlit
  · exact (False.elim (hlit p21812))
  · exact hlit
theorem n21814 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2296 : (e2296 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5195 : (e5195 _v)) : (e3919 _v) := by
  have p14797 := n14797 _v _q 
  have p21813 := n21813 _v _q h51 h2296 h4306 h4653 h4813 h5195
  change (e3923 _v) ∨ (e3919 _v) at p14797
  change (¬ (e3923 _v)) at p21813
  rcases p14797 with hlit | hlit
  · exact (False.elim (p21813 hlit))
  · exact hlit
theorem n21815 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2296 : (e2296 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5195 : (e5195 _v)) : (e7489 _v) := by
  have p17020 := n17020 _v _q 
  have p258 := n258 _v _q 
  have p21804 := n21804 _v _q h51 h2296 h4306 h4653 h4813 h5195
  have p16102 := n16102 _v _q h2296
  have p8583 := n8583 _v _q h2296
  have p15938 := n15938 _v _q h5195
  have p21814 := n21814 _v _q h51 h2296 h4306 h4653 h4813 h5195
  have p21800 := n21800 _v _q h2296 h5195
  have p17758 := n17758 _v _q 
  have p21737 := n21737 _v _q h51 h4306 h4653 h4813 h5195
  have p21793 := n21793 _v _q h2296
  have p17124 := n17124 _v _q 
  have p15100 := n15100 _v _q h2296
  have p17111 := n17111 _v _q 
  have p17115 := n17115 _v _q 
  have p21789 := n21789 _v _q h51 h4306 h4653 h4813 h5195
  have p17256 := n17256 _v _q 
  have p13951 := n13951 _v _q 
  have p17113 := n17113 _v _q 
  have p17117 := n17117 _v _q 
  have p20467 := n20467 _v _q 
  have p16115 := n16115 _v _q h2296
  have p21799 := n21799 _v _q h2296 h5195
  have p19665 := n19665 _v _q 
  have p17133 := n17133 _v _q 
  have p17120 := n17120 _v _q 
  have p21808 := n21808 _v _q h51 h2296 h4306 h4653 h4813 h5195
  have p17104 := n17104 _v _q 
  have p17874 := n17874 _v _q 
  have p17127 := n17127 _v _q 
  have p17089 := n17089 _v _q 
  have p21740 := n21740 _v _q h5195
  have p21770 := n21770 _v _q h51 h4306 h4653 h4813 h5195
  have p21727 := n21727 _v _q h51 h4306 h4653 h4813
  have p17138 := n17138 _v _q h4306
  have p20274 := n20274 _v _q 
  have p17060 := n17060 _v _q h4653
  have p20470 := n20470 _v _q 
  have p17953 := n17953 _v _q 
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
  have p17141 := n17141 _v _q 
  have p17100 := n17100 _v _q 
  have p19610 := n19610 _v _q 
  have p17102 := n17102 _v _q 
  have p17096 := n17096 _v _q 
  exact FloorCertificate.node_21815 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2902 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e4541 _v) (e4808 _v) p17020 p258 p21804 p16102 p8583 p15938 p21814 p21800 p17758 p21737 p21793 p17124 p15100 p17111 p17115 p21789 p17256 p13951 p17113 p17117 p20467 p16115 p21799 p19665 p17133 p17120 p21808 p17104 p17874 p17127 p17089 p21740 p21770 p21727 p17138 p20274 p17060 p20470 p17953 p17050 p16778 p17122 p4983 p16729 p20829 p20426 p20126 p17110 p17053 p20096 p17131 p17108 p17294 p16943 p17058 p17064 p17067 p17080 p17072 p17074 p17069 p20461 p20836 p20653 p17078 p17136 p17087 p17083 p17055 p17093 p17091 p17098 p17106 p17141 p17100 p19610 p17102 p17096
theorem n21817 (_v : Vars) (_q : Query _v)  : (e21816 _v) := by
  by_contra hc
  change ¬ ((¬ (e2296 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (e196 _v)) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h2296 : (e2296 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h5195 : (e5195 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))
  have p21815 := n21815 _v _q h51 h2296 h4306 h4653 h4813 h5195
  exact p21815
theorem n21818 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5195 : (e5195 _v)) : (e6549 _v) := by
  have p21817 := n21817 _v _q 
  have p8549 := n8549 _v _q h5195
  have p17060 := n17060 _v _q h4653
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p17138 := n17138 _v _q h4306
  change (¬ (e2296 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (e196 _v) at p21817
  change (¬ (e196 _v)) at p8549
  rcases p21817 with hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (p8549 hlit))
theorem n21819 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5195 : (e5195 _v)) : (e6879 _v) := by
  have p14643 := n14643 _v _q 
  have p21818 := n21818 _v _q h51 h4306 h4653 h4813 h5195
  change (e2296 _v) ∨ (¬ (e6878 _v)) at p14643
  change (¬ (e2296 _v)) at p21818
  rcases p14643 with hlit | hlit
  · exact (False.elim (p21818 hlit))
  · exact hlit
theorem n21820 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5195 : (e5195 _v)) : (e3152 _v) := by
  have p15776 := n15776 _v _q 
  have p21819 := n21819 _v _q h51 h4306 h4653 h4813 h5195
  change (e6878 _v) ∨ (e3152 _v) at p15776
  change (¬ (e6878 _v)) at p21819
  rcases p15776 with hlit | hlit
  · exact (False.elim (p21819 hlit))
  · exact hlit
theorem n21821 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5138 : (e5138 _v)) (h5195 : (e5195 _v)) : (e4101 _v) := by
  have p14929 := n14929 _v _q 
  have p21791 := n21791 _v _q h51 h4306 h4653 h4813 h5138 h5195
  change (e4108 _v) ∨ (e4101 _v) at p14929
  change (¬ (e4108 _v)) at p21791
  rcases p14929 with hlit | hlit
  · exact (False.elim (p21791 hlit))
  · exact hlit
theorem n21822 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5138 : (e5138 _v)) (h5195 : (e5195 _v)) (h6501 : (e6501 _v)) : (e4269 _v) := by
  have p17009 := n17009 _v _q 
  have p16101 := n16101 _v _q h5195
  have p20397 := n20397 _v _q 
  have p16992 := n16992 _v _q 
  have p17102 := n17102 _v _q 
  have p5391 := n5391 _v _q 
  have p15223 := n15223 _v _q h5195
  have p15927 := n15927 _v _q h5138
  have p17147 := n17147 _v _q 
  have p17096 := n17096 _v _q 
  have p15938 := n15938 _v _q h5195
  have p16109 := n16109 _v _q h5195
  have p17758 := n17758 _v _q 
  have p21737 := n21737 _v _q h51 h4306 h4653 h4813 h5195
  have p16325 := n16325 _v _q h6501
  have p17124 := n17124 _v _q 
  have p19610 := n19610 _v _q 
  have p17111 := n17111 _v _q 
  have p17115 := n17115 _v _q 
  have p21789 := n21789 _v _q h51 h4306 h4653 h4813 h5195
  have p17256 := n17256 _v _q 
  have p13951 := n13951 _v _q 
  have p17113 := n17113 _v _q 
  have p17117 := n17117 _v _q 
  have p20467 := n20467 _v _q 
  have p16633 := n16633 _v _q h6501
  have p21821 := n21821 _v _q h51 h4306 h4653 h4813 h5138 h5195
  have p19665 := n19665 _v _q 
  have p17133 := n17133 _v _q 
  have p17120 := n17120 _v _q 
  have p17104 := n17104 _v _q 
  have p17874 := n17874 _v _q 
  have p17127 := n17127 _v _q 
  have p17089 := n17089 _v _q 
  have p21770 := n21770 _v _q h51 h4306 h4653 h4813 h5195
  have p21727 := n21727 _v _q h51 h4306 h4653 h4813
  have p17138 := n17138 _v _q h4306
  have p20274 := n20274 _v _q 
  have p17060 := n17060 _v _q h4653
  have p20470 := n20470 _v _q 
  have p17953 := n17953 _v _q 
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
  have p17141 := n17141 _v _q 
  have p17100 := n17100 _v _q 
  have p21820 := n21820 _v _q h51 h4306 h4653 h4813 h5195
  have p16576 := n16576 _v _q 
  have p15641 := n15641 _v _q h6501
  have p11487 := n11487 _v _q h5138
  have p21787 := n21787 _v _q h51 h4306 h4653 h4813 h5195
  have p8554 := n8554 _v _q h6501
  exact FloorCertificate.node_21822 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2863 _v) (e2877 _v) (e2883 _v) (e2902 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p17009 p16101 p20397 p16992 p17102 p5391 p15223 p15927 p17147 p17096 p15938 p16109 p17758 p21737 p16325 p17124 p19610 p17111 p17115 p21789 p17256 p13951 p17113 p17117 p20467 p16633 p21821 p19665 p17133 p17120 p17104 p17874 p17127 p17089 p21770 p21727 p17138 p20274 p17060 p20470 p17953 p17050 p16778 p17122 p4983 p16729 p20829 p20426 p20126 p17110 p17053 p20096 p17131 p17108 p17294 p16943 p17058 p17064 p17067 p17080 p17072 p17074 p17069 p20461 p20836 p20653 p17078 p17136 p17087 p17083 p17055 p17093 p17091 p17098 p17106 p17141 p17100 p21820 p16576 p15641 p11487 p21787 p8554
theorem n21823 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5138 : (e5138 _v)) (h5195 : (e5195 _v)) (h6501 : (e6501 _v)) : (e4270 _v) := by
  have p14966 := n14966 _v _q 
  have p21822 := n21822 _v _q h51 h4306 h4653 h4813 h5138 h5195 h6501
  change (e4270 _v) ∨ (e4264 _v) at p14966
  change (¬ (e4264 _v)) at p21822
  rcases p14966 with hlit | hlit
  · exact hlit
  · exact (False.elim (p21822 hlit))
theorem n21824 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5138 : (e5138 _v)) (h5195 : (e5195 _v)) (h6501 : (e6501 _v)) : (e6776 _v) := by
  have p14699 := n14699 _v _q 
  have p21823 := n21823 _v _q h51 h4306 h4653 h4813 h5138 h5195 h6501
  change (¬ (e2781 _v)) ∨ (¬ (e4270 _v)) at p14699
  rcases p14699 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p21823))
theorem n21825 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5138 : (e5138 _v)) (h5195 : (e5195 _v)) (h6501 : (e6501 _v)) : (e7789 _v) := by
  have p14570 := n14570 _v _q 
  have p21824 := n21824 _v _q h51 h4306 h4653 h4813 h5138 h5195 h6501
  change (e2781 _v) ∨ (¬ (e7781 _v)) at p14570
  change (¬ (e2781 _v)) at p21824
  rcases p14570 with hlit | hlit
  · exact (False.elim (p21824 hlit))
  · exact hlit
theorem n21826 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5138 : (e5138 _v)) (h5195 : (e5195 _v)) (h6501 : (e6501 _v)) : (e4260 _v) := by
  have p15824 := n15824 _v _q 
  have p21825 := n21825 _v _q h51 h4306 h4653 h4813 h5138 h5195 h6501
  change (e7781 _v) ∨ (e4260 _v) at p15824
  change (¬ (e7781 _v)) at p21825
  rcases p15824 with hlit | hlit
  · exact (False.elim (p21825 hlit))
  · exact hlit
theorem n21827 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5138 : (e5138 _v)) (h5195 : (e5195 _v)) (h6501 : (e6501 _v)) : (e7489 _v) := by
  have p17147 := n17147 _v _q 
  have p21826 := n21826 _v _q h51 h4306 h4653 h4813 h5138 h5195 h6501
  have p16113 := n16113 _v _q h5195
  have p21820 := n21820 _v _q h51 h4306 h4653 h4813 h5195
  have p15641 := n15641 _v _q h6501
  have p16325 := n16325 _v _q h6501
  have p17009 := n17009 _v _q 
  have p16101 := n16101 _v _q h5195
  have p12839 := n12839 _v _q h5195
  have p17102 := n17102 _v _q 
  have p15223 := n15223 _v _q h5195
  have p15927 := n15927 _v _q h5138
  have p16633 := n16633 _v _q h6501
  have p17096 := n17096 _v _q 
  have p15938 := n15938 _v _q h5195
  have p16109 := n16109 _v _q h5195
  have p17758 := n17758 _v _q 
  have p21737 := n21737 _v _q h51 h4306 h4653 h4813 h5195
  have p8549 := n8549 _v _q h5195
  have p17124 := n17124 _v _q 
  have p19610 := n19610 _v _q 
  have p17111 := n17111 _v _q 
  have p17115 := n17115 _v _q 
  have p21789 := n21789 _v _q h51 h4306 h4653 h4813 h5195
  have p17256 := n17256 _v _q 
  have p13951 := n13951 _v _q 
  have p17113 := n17113 _v _q 
  have p17117 := n17117 _v _q 
  have p20467 := n20467 _v _q 
  have p16576 := n16576 _v _q 
  have p21821 := n21821 _v _q h51 h4306 h4653 h4813 h5138 h5195
  have p19665 := n19665 _v _q 
  have p17133 := n17133 _v _q 
  have p17120 := n17120 _v _q 
  have p17104 := n17104 _v _q 
  have p17874 := n17874 _v _q 
  have p17127 := n17127 _v _q 
  have p17089 := n17089 _v _q 
  have p21770 := n21770 _v _q h51 h4306 h4653 h4813 h5195
  have p21727 := n21727 _v _q h51 h4306 h4653 h4813
  have p17138 := n17138 _v _q h4306
  have p20274 := n20274 _v _q 
  have p17060 := n17060 _v _q h4653
  have p20470 := n20470 _v _q 
  have p17953 := n17953 _v _q 
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
  have p17141 := n17141 _v _q 
  have p17100 := n17100 _v _q 
  have p21732 := n21732 _v _q h51 h4306 h4653 h4813 h5195
  have p11487 := n11487 _v _q h5138
  have p21824 := n21824 _v _q h51 h4306 h4653 h4813 h5138 h5195 h6501
  have p21787 := n21787 _v _q h51 h4306 h4653 h4813 h5195
  have p17020 := n17020 _v _q 
  exact FloorCertificate.node_21827 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2863 _v) (e2877 _v) (e2883 _v) (e2902 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p17147 p21826 p16113 p21820 p15641 p16325 p17009 p16101 p12839 p17102 p15223 p15927 p16633 p17096 p15938 p16109 p17758 p21737 p8549 p17124 p19610 p17111 p17115 p21789 p17256 p13951 p17113 p17117 p20467 p16576 p21821 p19665 p17133 p17120 p17104 p17874 p17127 p17089 p21770 p21727 p17138 p20274 p17060 p20470 p17953 p17050 p16778 p17122 p4983 p16729 p20829 p20426 p20126 p17110 p17053 p20096 p17131 p17108 p17294 p16943 p17058 p17064 p17067 p17080 p17072 p17074 p17069 p20461 p20836 p20653 p17078 p17136 p17087 p17083 p17055 p17093 p17091 p17098 p17106 p17141 p17100 p21732 p11487 p21824 p21787 p17020
theorem n21829 (_v : Vars) (_q : Query _v)  : (e21828 _v) := by
  by_contra hc
  change ¬ ((e79 _v) ∨ (e196 _v) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (e2179 _v)) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h5138 : (e5138 _v) := (fun hn => hc (Or.inl hn))
  have h5195 : (e5195 _v) := (fun hn => hc (Or.inr (Or.inl hn)))
  have h6501 : (e6501 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn)))))))
  have p21827 := n21827 _v _q h51 h4306 h4653 h4813 h5138 h5195 h6501
  exact p21827
theorem n21830 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5195 : (e5195 _v)) (h6501 : (e6501 _v)) : (e79 _v) := by
  have p21829 := n21829 _v _q 
  have p8554 := n8554 _v _q h6501
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p8549 := n8549 _v _q h5195
  change (e79 _v) ∨ (e196 _v) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (e2179 _v) at p21829
  change (¬ (e2179 _v)) at p8554
  change (¬ (e196 _v)) at p8549
  rcases p21829 with hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (p8549 hlit))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (p8554 hlit))
theorem n21831 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5195 : (e5195 _v)) (h6501 : (e6501 _v)) : (e5135 _v) := by
  have p14729 := n14729 _v _q 
  have p21830 := n21830 _v _q h51 h4306 h4653 h4813 h5195 h6501
  change (¬ (e79 _v)) ∨ (¬ (e5134 _v)) at p14729
  rcases p14729 with hlit | hlit
  · exact (False.elim (hlit p21830))
  · exact hlit
theorem n21832 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5195 : (e5195 _v)) (h6501 : (e6501 _v)) : (e91 _v) := by
  have p16235 := n16235 _v _q 
  have p21831 := n21831 _v _q h51 h4306 h4653 h4813 h5195 h6501
  change (e5134 _v) ∨ (e91 _v) at p16235
  change (¬ (e5134 _v)) at p21831
  rcases p16235 with hlit | hlit
  · exact (False.elim (p21831 hlit))
  · exact hlit
theorem n21833 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h5195 : (e5195 _v)) : (e48 _v) := by
  have p16732 := n16732 _v _q 
  have p16734 := n16734 _v _q h5195
  have p16729 := n16729 _v _q h51
  change (e48 _v) ∨ (¬ (e7495 _v)) ∨ (¬ (e51 _v)) at p16732
  rcases p16732 with hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p16734))
  · exact (False.elim (hlit p16729))
theorem n21834 (_v : Vars) (_q : Query _v) (h5195 : (e5195 _v)) : (e7608 _v) := by
  have p18879 := n18879 _v _q 
  have p15225 := n15225 _v _q h5195
  change (e7610 _v) ∨ (e7608 _v) at p18879
  change (¬ (e7610 _v)) at p15225
  rcases p18879 with hlit | hlit
  · exact (False.elim (p15225 hlit))
  · exact hlit
theorem n21835 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5195 : (e5195 _v)) (h6501 : (e6501 _v)) : (e2781 _v) := by
  have p17617 := n17617 _v _q 
  have p16325 := n16325 _v _q h6501
  have p17953 := n17953 _v _q 
  have p8549 := n8549 _v _q h5195
  have p16101 := n16101 _v _q h5195
  have p21737 := n21737 _v _q h51 h4306 h4653 h4813 h5195
  have p16943 := n16943 _v _q 
  have p21770 := n21770 _v _q h51 h4306 h4653 h4813 h5195
  have p20096 := n20096 _v _q 
  have p4983 := n4983 _v _q h4813
  have p21820 := n21820 _v _q h51 h4306 h4653 h4813 h5195
  have p20274 := n20274 _v _q 
  have p21833 := n21833 _v _q h51 h5195
  have p15641 := n15641 _v _q h6501
  have p16109 := n16109 _v _q h5195
  have p15223 := n15223 _v _q h5195
  have p20467 := n20467 _v _q 
  have p15938 := n15938 _v _q h5195
  have p19610 := n19610 _v _q 
  have p17138 := n17138 _v _q h4306
  have p17020 := n17020 _v _q 
  have p20426 := n20426 _v _q 
  have p16633 := n16633 _v _q h6501
  have p17294 := n17294 _v _q 
  have p17060 := n17060 _v _q h4653
  have p17874 := n17874 _v _q 
  have p20653 := n20653 _v _q 
  have p20126 := n20126 _v _q 
  have p20829 := n20829 _v _q 
  have p21834 := n21834 _v _q h5195
  have p20836 := n20836 _v _q 
  have p17758 := n17758 _v _q 
  have p19665 := n19665 _v _q 
  have p20470 := n20470 _v _q 
  have p20461 := n20461 _v _q 
  have p16113 := n16113 _v _q h5195
  have p21789 := n21789 _v _q h51 h4306 h4653 h4813 h5195
  have p21832 := n21832 _v _q h51 h4306 h4653 h4813 h5195 h6501
  change (¬ (e4439 _v)) ∨ (¬ (e7749 _v)) ∨ (e2781 _v) ∨ (¬ (e4608 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4491 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4903 _v)) ∨ (¬ (e5208 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e5100 _v)) ∨ (¬ (e7814 _v)) ∨ (¬ (e4398 _v)) ∨ (¬ (e8045 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e4567 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e3976 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e7608 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4724 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e7935 _v)) ∨ (e196 _v) ∨ (¬ (e48 _v)) at p17617
  change (¬ (e196 _v)) at p8549
  rcases p17617 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact (False.elim (hlit p21789))
  · exact (False.elim (hlit p16101))
  · exact hlit
  · exact (False.elim (hlit p15641))
  · exact (False.elim (hlit p21832))
  · exact (False.elim (hlit p16325))
  · exact (False.elim (hlit p16943))
  · exact (False.elim (hlit p21820))
  · exact (False.elim (hlit p20096))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p21770))
  · exact (False.elim (hlit p20274))
  · exact (False.elim (hlit p17953))
  · exact (False.elim (hlit p16633))
  · exact (False.elim (hlit p16109))
  · exact (False.elim (hlit p15223))
  · exact (False.elim (hlit p20467))
  · exact (False.elim (hlit p15938))
  · exact (False.elim (hlit p19610))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17020))
  · exact (False.elim (hlit p20426))
  · exact (False.elim (hlit p21737))
  · exact (False.elim (hlit p17294))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p17874))
  · exact (False.elim (hlit p20653))
  · exact (False.elim (hlit p20126))
  · exact (False.elim (hlit p20829))
  · exact (False.elim (hlit p21834))
  · exact (False.elim (hlit p20836))
  · exact (False.elim (hlit p17758))
  · exact (False.elim (hlit p19665))
  · exact (False.elim (hlit p20470))
  · exact (False.elim (hlit p20461))
  · exact (False.elim (hlit p16113))
  · exact (False.elim (p8549 hlit))
  · exact (False.elim (hlit p21833))
theorem n21836 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5195 : (e5195 _v)) (h6501 : (e6501 _v)) : (e4271 _v) := by
  have p14699 := n14699 _v _q 
  have p21835 := n21835 _v _q h51 h4306 h4653 h4813 h5195 h6501
  change (¬ (e2781 _v)) ∨ (¬ (e4270 _v)) at p14699
  rcases p14699 with hlit | hlit
  · exact (False.elim (hlit p21835))
  · exact hlit
theorem n21837 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5195 : (e5195 _v)) (h6501 : (e6501 _v)) : (e4264 _v) := by
  have p14966 := n14966 _v _q 
  have p21836 := n21836 _v _q h51 h4306 h4653 h4813 h5195 h6501
  change (e4270 _v) ∨ (e4264 _v) at p14966
  change (¬ (e4270 _v)) at p21836
  rcases p14966 with hlit | hlit
  · exact (False.elim (p21836 hlit))
  · exact hlit
theorem n21838 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5195 : (e5195 _v)) (h6501 : (e6501 _v)) : (e2733 _v) := by
  have p8424 := n8424 _v _q 
  have p21835 := n21835 _v _q h51 h4306 h4653 h4813 h5195 h6501
  change (e2733 _v) ∨ (¬ (e2781 _v)) at p8424
  rcases p8424 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p21835))
theorem n21839 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5195 : (e5195 _v)) (h6501 : (e6501 _v)) : (e4109 _v) := by
  have p14689 := n14689 _v _q 
  have p21838 := n21838 _v _q h51 h4306 h4653 h4813 h5195 h6501
  change (¬ (e2733 _v)) ∨ (¬ (e4108 _v)) at p14689
  rcases p14689 with hlit | hlit
  · exact (False.elim (hlit p21838))
  · exact hlit
theorem n21840 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5195 : (e5195 _v)) (h6501 : (e6501 _v)) : (e4101 _v) := by
  have p14929 := n14929 _v _q 
  have p21839 := n21839 _v _q h51 h4306 h4653 h4813 h5195 h6501
  change (e4108 _v) ∨ (e4101 _v) at p14929
  change (¬ (e4108 _v)) at p21839
  rcases p14929 with hlit | hlit
  · exact (False.elim (p21839 hlit))
  · exact hlit
theorem n21841 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5195 : (e5195 _v)) (h6501 : (e6501 _v)) : (e7489 _v) := by
  have p17106 := n17106 _v _q 
  have p21740 := n21740 _v _q h5195
  have p17141 := n17141 _v _q 
  have p17020 := n17020 _v _q 
  have p17100 := n17100 _v _q 
  have p15641 := n15641 _v _q h6501
  have p21820 := n21820 _v _q h51 h4306 h4653 h4813 h5195
  have p16576 := n16576 _v _q 
  have p17102 := n17102 _v _q 
  have p21832 := n21832 _v _q h51 h4306 h4653 h4813 h5195 h6501
  have p15223 := n15223 _v _q h5195
  have p17147 := n17147 _v _q 
  have p17096 := n17096 _v _q 
  have p15938 := n15938 _v _q h5195
  have p16109 := n16109 _v _q h5195
  have p21837 := n21837 _v _q h51 h4306 h4653 h4813 h5195 h6501
  have p17758 := n17758 _v _q 
  have p21737 := n21737 _v _q h51 h4306 h4653 h4813 h5195
  have p16325 := n16325 _v _q h6501
  have p17124 := n17124 _v _q 
  have p19610 := n19610 _v _q 
  have p17111 := n17111 _v _q 
  have p17115 := n17115 _v _q 
  have p21789 := n21789 _v _q h51 h4306 h4653 h4813 h5195
  have p17256 := n17256 _v _q 
  have p296 := n296 _v _q 
  have p17113 := n17113 _v _q 
  have p17117 := n17117 _v _q 
  have p20467 := n20467 _v _q 
  have p16633 := n16633 _v _q h6501
  have p21840 := n21840 _v _q h51 h4306 h4653 h4813 h5195 h6501
  have p19665 := n19665 _v _q 
  have p17133 := n17133 _v _q 
  have p17120 := n17120 _v _q 
  have p17104 := n17104 _v _q 
  have p17874 := n17874 _v _q 
  have p17127 := n17127 _v _q 
  have p17089 := n17089 _v _q 
  have p21770 := n21770 _v _q h51 h4306 h4653 h4813 h5195
  have p21727 := n21727 _v _q h51 h4306 h4653 h4813
  have p17138 := n17138 _v _q h4306
  have p20274 := n20274 _v _q 
  have p17060 := n17060 _v _q h4653
  have p20470 := n20470 _v _q 
  have p17953 := n17953 _v _q 
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
  exact FloorCertificate.node_21841 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2863 _v) (e2877 _v) (e2883 _v) (e2902 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4541 _v) (e4808 _v) p17106 p21740 p17141 p17020 p17100 p15641 p21820 p16576 p17102 p21832 p15223 p17147 p17096 p15938 p16109 p21837 p17758 p21737 p16325 p17124 p19610 p17111 p17115 p21789 p17256 p296 p17113 p17117 p20467 p16633 p21840 p19665 p17133 p17120 p17104 p17874 p17127 p17089 p21770 p21727 p17138 p20274 p17060 p20470 p17953 p17050 p16778 p17122 p4983 p16729 p20829 p20426 p20126 p17110 p17053 p20096 p17131 p17108 p17294 p16943 p17058 p17064 p17067 p17080 p17072 p17074 p17069 p20461 p20836 p20653 p17078 p17136 p17087 p17083 p17055 p17093 p17091 p17098
theorem n21843 (_v : Vars) (_q : Query _v)  : (e21842 _v) := by
  by_contra hc
  change ¬ ((e2179 _v) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (e196 _v)) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h5195 : (e5195 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))
  have h6501 : (e6501 _v) := (fun hn => hc (Or.inl hn))
  have p21841 := n21841 _v _q h51 h4306 h4653 h4813 h5195 h6501
  exact p21841
theorem n21844 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5195 : (e5195 _v)) : (e2179 _v) := by
  have p21843 := n21843 _v _q 
  have p8549 := n8549 _v _q h5195
  have p17060 := n17060 _v _q h4653
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p17138 := n17138 _v _q h4306
  change (e2179 _v) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (e196 _v) at p21843
  change (¬ (e196 _v)) at p8549
  rcases p21843 with hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (p8549 hlit))
theorem n21845 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5195 : (e5195 _v)) : (e4616 _v) := by
  have p14684 := n14684 _v _q 
  have p21844 := n21844 _v _q h51 h4306 h4653 h4813 h5195
  change (¬ (e2179 _v)) ∨ (¬ (e3162 _v)) at p14684
  rcases p14684 with hlit | hlit
  · exact (False.elim (hlit p21844))
  · exact hlit
theorem n21846 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5195 : (e5195 _v)) : (e3158 _v) := by
  have p15126 := n15126 _v _q 
  have p21845 := n21845 _v _q h51 h4306 h4653 h4813 h5195
  change (e3162 _v) ∨ (e3158 _v) at p15126
  change (¬ (e3162 _v)) at p21845
  rcases p15126 with hlit | hlit
  · exact (False.elim (p21845 hlit))
  · exact hlit
theorem n21847 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5195 : (e5195 _v)) : (e2781 _v) := by
  have p16578 := n16578 _v _q 
  have p8549 := n8549 _v _q h5195
  have p16858 := n16858 _v _q 
  have p21846 := n21846 _v _q h51 h4306 h4653 h4813 h5195
  exact FloorCertificate.node_21847 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) (e2863 _v) (e2935 _v) p16578 p8549 p16858 p21846
theorem n21848 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5195 : (e5195 _v)) : (e4271 _v) := by
  have p14699 := n14699 _v _q 
  have p21847 := n21847 _v _q h51 h4306 h4653 h4813 h5195
  change (¬ (e2781 _v)) ∨ (¬ (e4270 _v)) at p14699
  rcases p14699 with hlit | hlit
  · exact (False.elim (hlit p21847))
  · exact hlit
theorem n21849 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5195 : (e5195 _v)) : (e4264 _v) := by
  have p14966 := n14966 _v _q 
  have p21848 := n21848 _v _q h51 h4306 h4653 h4813 h5195
  change (e4270 _v) ∨ (e4264 _v) at p14966
  change (¬ (e4270 _v)) at p21848
  rcases p14966 with hlit | hlit
  · exact (False.elim (p21848 hlit))
  · exact hlit
theorem n21850 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5195 : (e5195 _v)) : (e2733 _v) := by
  have p8424 := n8424 _v _q 
  have p21847 := n21847 _v _q h51 h4306 h4653 h4813 h5195
  change (e2733 _v) ∨ (¬ (e2781 _v)) at p8424
  rcases p8424 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p21847))
theorem n21851 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5195 : (e5195 _v)) : (e4109 _v) := by
  have p14689 := n14689 _v _q 
  have p21850 := n21850 _v _q h51 h4306 h4653 h4813 h5195
  change (¬ (e2733 _v)) ∨ (¬ (e4108 _v)) at p14689
  rcases p14689 with hlit | hlit
  · exact (False.elim (hlit p21850))
  · exact hlit
theorem n21852 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5195 : (e5195 _v)) : (e4101 _v) := by
  have p14929 := n14929 _v _q 
  have p21851 := n21851 _v _q h51 h4306 h4653 h4813 h5195
  change (e4108 _v) ∨ (e4101 _v) at p14929
  change (¬ (e4108 _v)) at p21851
  rcases p14929 with hlit | hlit
  · exact (False.elim (p21851 hlit))
  · exact hlit
end
end Assembly
