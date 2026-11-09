import Dag238
import generated.th_lemma_31
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n20806 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h5138 : (e5138 _v)) : (e5232 _v) := by
  have p14731 := n14731 _v _q 
  have p20805 := n20805 _v _q h2351 h5138
  change (¬ (e214 _v)) ∨ (¬ (e5231 _v)) at p14731
  rcases p14731 with hlit | hlit
  · exact (False.elim (hlit p20805))
  · exact hlit
theorem n20807 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h5138 : (e5138 _v)) : (e225 _v) := by
  have p16653 := n16653 _v _q 
  have p20806 := n20806 _v _q h2351 h5138
  change (e5231 _v) ∨ (e225 _v) at p16653
  change (¬ (e5231 _v)) at p20806
  rcases p16653 with hlit | hlit
  · exact (False.elim (p20806 hlit))
  · exact hlit
theorem n20808 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h5138 : (e5138 _v)) : (e7489 _v) := by
  have p20730 := n20730 _v _q h2351
  have p13951 := n13951 _v _q 
  have p15927 := n15927 _v _q h5138
  have p17953 := n17953 _v _q 
  have p5255 := n5255 _v _q 
  have p17110 := n17110 _v _q 
  have p20804 := n20804 _v _q h5138
  have p20800 := n20800 _v _q h2351
  have p17053 := n17053 _v _q 
  have p17131 := n17131 _v _q 
  have p20751 := n20751 _v _q h2351
  have p20096 := n20096 _v _q 
  have p20807 := n20807 _v _q h2351 h5138
  have p8464 := n8464 _v _q h2351
  have p20753 := n20753 _v _q h2351
  have p17058 := n17058 _v _q 
  have p17294 := n17294 _v _q 
  have p16943 := n16943 _v _q 
  have p17064 := n17064 _v _q 
  have p20732 := n20732 _v _q h2351
  have p15917 := n15917 _v _q h2351
  have p17067 := n17067 _v _q 
  have p17069 := n17069 _v _q 
  have p17080 := n17080 _v _q 
  have p17072 := n17072 _v _q 
  have p17083 := n17083 _v _q 
  have p17074 := n17074 _v _q 
  have p20678 := n20678 _v _q h2351
  have p20663 := n20663 _v _q h2351
  have p17078 := n17078 _v _q 
  have p20653 := n20653 _v _q 
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
  exact FloorCertificate.node_20808 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2902 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e4808 _v) p20730 p13951 p15927 p17953 p5255 p17110 p20804 p20800 p17053 p17131 p20751 p20096 p20807 p8464 p20753 p17058 p17294 p16943 p17064 p20732 p15917 p17067 p17069 p17080 p17072 p17083 p17074 p20678 p20663 p17078 p20653 p17087 p17136 p15793 p17091 p17093 p20682 p17141 p17098 p17106 p17102 p17100 p19610 p15791 p17122 p17096 p15909 p15786 p17758 p15783 p15911 p15905 p20319 p17115 p17120 p17111 p17124 p17050 p16778 p17113 p17117 p20467 p17104 p17874 p17127 p15914 p20274 p20470 p17133 p17089 p19665 p20426 p17055 p17108 p20461 p20126
theorem n20810 (_v : Vars) (_q : Query _v)  : (e20809 _v) := by
  by_contra hc
  change ¬ ((e79 _v) ∨ (¬ (e2351 _v))) at hc
  have h2351 : (e2351 _v) := Classical.byContradiction (fun hn => hc (Or.inr hn))
  have h5138 : (e5138 _v) := (fun hn => hc (Or.inl hn))
  have p20808 := n20808 _v _q h2351 h5138
  exact p20808
theorem n20811 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) : (e79 _v) := by
  have p20810 := n20810 _v _q 
  have p8464 := n8464 _v _q h2351
  change (e79 _v) ∨ (¬ (e2351 _v)) at p20810
  rcases p20810 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p8464))
theorem n20812 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) : (e5135 _v) := by
  have p14729 := n14729 _v _q 
  have p20811 := n20811 _v _q h2351
  change (¬ (e79 _v)) ∨ (¬ (e5134 _v)) at p14729
  rcases p14729 with hlit | hlit
  · exact (False.elim (hlit p20811))
  · exact hlit
theorem n20813 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) : (e91 _v) := by
  have p16235 := n16235 _v _q 
  have p20812 := n20812 _v _q h2351
  change (e5134 _v) ∨ (e91 _v) at p16235
  change (¬ (e5134 _v)) at p20812
  rcases p16235 with hlit | hlit
  · exact (False.elim (p20812 hlit))
  · exact hlit
theorem n20814 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) : (e214 _v) := by
  have p20751 := n20751 _v _q h2351
  have p20730 := n20730 _v _q h2351
  have p20811 := n20811 _v _q h2351
  exact FloorCertificate.node_20814 (e2 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p20751 p20730 p20811
theorem n20815 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) : (e5232 _v) := by
  have p14731 := n14731 _v _q 
  have p20814 := n20814 _v _q h2351
  change (¬ (e214 _v)) ∨ (¬ (e5231 _v)) at p14731
  rcases p14731 with hlit | hlit
  · exact (False.elim (hlit p20814))
  · exact hlit
theorem n20816 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) : (e225 _v) := by
  have p16653 := n16653 _v _q 
  have p20815 := n20815 _v _q h2351
  change (e5231 _v) ∨ (e225 _v) at p16653
  change (¬ (e5231 _v)) at p20815
  rcases p16653 with hlit | hlit
  · exact (False.elim (p20815 hlit))
  · exact hlit
theorem n20817 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h8310 : (e8310 _v)) : (e7489 _v) := by
  have p20813 := n20813 _v _q h2351
  have p20811 := n20811 _v _q h2351
  have p20730 := n20730 _v _q h2351
  have p13951 := n13951 _v _q 
  have p17953 := n17953 _v _q 
  have p20126 := n20126 _v _q 
  have p17110 := n17110 _v _q 
  have p15248 := n15248 _v _q h8310
  have p20800 := n20800 _v _q h2351
  have p17053 := n17053 _v _q 
  have p17131 := n17131 _v _q 
  have p20751 := n20751 _v _q h2351
  have p20096 := n20096 _v _q 
  have p20816 := n20816 _v _q h2351
  have p8464 := n8464 _v _q h2351
  have p20753 := n20753 _v _q h2351
  have p17058 := n17058 _v _q 
  have p17294 := n17294 _v _q 
  have p16943 := n16943 _v _q 
  have p17064 := n17064 _v _q 
  have p20732 := n20732 _v _q h2351
  have p15917 := n15917 _v _q h2351
  have p17067 := n17067 _v _q 
  have p17069 := n17069 _v _q 
  have p17080 := n17080 _v _q 
  have p17072 := n17072 _v _q 
  have p17083 := n17083 _v _q 
  have p17074 := n17074 _v _q 
  have p20678 := n20678 _v _q h2351
  have p20663 := n20663 _v _q h2351
  have p17078 := n17078 _v _q 
  have p20653 := n20653 _v _q 
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
  have p11384 := n11384 _v _q h8310
  exact FloorCertificate.node_20817 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2902 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e4808 _v) p20813 p20811 p20730 p13951 p17953 p20126 p17110 p15248 p20800 p17053 p17131 p20751 p20096 p20816 p8464 p20753 p17058 p17294 p16943 p17064 p20732 p15917 p17067 p17069 p17080 p17072 p17083 p17074 p20678 p20663 p17078 p20653 p17087 p17136 p15793 p17091 p17093 p20682 p17141 p17098 p17106 p17102 p17100 p19610 p15791 p17122 p17096 p15909 p15786 p17758 p15783 p15911 p15905 p20319 p17115 p17120 p17111 p17124 p17050 p16778 p17113 p17117 p20467 p17104 p17874 p17127 p15914 p20274 p20470 p17133 p17089 p19665 p20426 p17055 p17108 p20461 p11384
theorem n20819 (_v : Vars) (_q : Query _v)  : (e20818 _v) := by
  by_contra hc
  change ¬ ((e2529 _v) ∨ (¬ (e2351 _v))) at hc
  have h2351 : (e2351 _v) := Classical.byContradiction (fun hn => hc (Or.inr hn))
  have h8310 : (e8310 _v) := (fun hn => hc (Or.inl hn))
  have p20817 := n20817 _v _q h2351 h8310
  exact p20817
theorem n20820 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) : (e2529 _v) := by
  have p20819 := n20819 _v _q 
  have p8464 := n8464 _v _q h2351
  change (e2529 _v) ∨ (¬ (e2351 _v)) at p20819
  rcases p20819 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p8464))
theorem n20821 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) : (e196 _v) := by
  have p8552 := n8552 _v _q 
  have p20820 := n20820 _v _q h2351
  change (¬ (e2529 _v)) ∨ (e196 _v) at p8552
  rcases p8552 with hlit | hlit
  · exact (False.elim (hlit p20820))
  · exact hlit
theorem n20822 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) : (e5203 _v) := by
  have p14730 := n14730 _v _q 
  have p20821 := n20821 _v _q h2351
  change (¬ (e196 _v)) ∨ (¬ (e5193 _v)) at p14730
  rcases p14730 with hlit | hlit
  · exact (False.elim (hlit p20821))
  · exact hlit
theorem n20823 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) : (e191 _v) := by
  have p16442 := n16442 _v _q 
  have p20822 := n20822 _v _q h2351
  change (e5193 _v) ∨ (e191 _v) at p16442
  change (¬ (e5193 _v)) at p20822
  rcases p16442 with hlit | hlit
  · exact (False.elim (p20822 hlit))
  · exact hlit
theorem n20824 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) : (e8307 _v) := by
  have p14906 := n14906 _v _q 
  have p20820 := n20820 _v _q h2351
  change (¬ (e2529 _v)) ∨ (¬ (e8301 _v)) at p14906
  rcases p14906 with hlit | hlit
  · exact (False.elim (hlit p20820))
  · exact hlit
theorem n20825 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) : (e4838 _v) := by
  have p16285 := n16285 _v _q 
  have p20824 := n20824 _v _q h2351
  change (e8301 _v) ∨ (e4838 _v) at p16285
  change (¬ (e8301 _v)) at p20824
  rcases p16285 with hlit | hlit
  · exact (False.elim (p20824 hlit))
  · exact hlit
theorem n20826 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) : (e7489 _v) := by
  have p17089 := n17089 _v _q 
  have p296 := n296 _v _q 
  have p19665 := n19665 _v _q 
  have p20426 := n20426 _v _q 
  have p17055 := n17055 _v _q 
  have p17108 := n17108 _v _q 
  have p20461 := n20461 _v _q 
  have p20823 := n20823 _v _q h2351
  have p20825 := n20825 _v _q h2351
  have p20813 := n20813 _v _q h2351
  have p20126 := n20126 _v _q 
  have p17110 := n17110 _v _q 
  have p20800 := n20800 _v _q h2351
  have p17053 := n17053 _v _q 
  have p17131 := n17131 _v _q 
  have p20096 := n20096 _v _q 
  have p20816 := n20816 _v _q h2351
  have p20753 := n20753 _v _q h2351
  have p17058 := n17058 _v _q 
  have p17294 := n17294 _v _q 
  have p16943 := n16943 _v _q 
  have p17064 := n17064 _v _q 
  have p20732 := n20732 _v _q h2351
  have p15917 := n15917 _v _q h2351
  have p17067 := n17067 _v _q 
  have p17069 := n17069 _v _q 
  have p17080 := n17080 _v _q 
  have p17072 := n17072 _v _q 
  have p17083 := n17083 _v _q 
  have p17074 := n17074 _v _q 
  have p20678 := n20678 _v _q h2351
  have p20663 := n20663 _v _q h2351
  have p17078 := n17078 _v _q 
  have p20653 := n20653 _v _q 
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
  exact FloorCertificate.node_20826 (e17 _v) (e49 _v) (e80 _v) (e101 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2902 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e4808 _v) p17089 p296 p19665 p20426 p17055 p17108 p20461 p20823 p20825 p20813 p20126 p17110 p20800 p17053 p17131 p20096 p20816 p20753 p17058 p17294 p16943 p17064 p20732 p15917 p17067 p17069 p17080 p17072 p17083 p17074 p20678 p20663 p17078 p20653 p17087 p17136 p15793 p17091 p17093 p20682 p17141 p17098 p17106 p17102 p17100 p19610 p15791 p17122 p17096 p15909 p15786 p17758 p15783 p15911 p15905 p20319 p17115 p17120 p17111 p17124 p17050 p16778 p17113 p17117 p20467 p17104 p17874 p17127 p15914 p20274 p20470 p17133
theorem n20827 (_v : Vars) (_q : Query _v)  : (e6575 _v) := by
  by_contra hc
  change ¬ (¬ (e2351 _v)) at hc
  have h2351 : (e2351 _v) := Classical.byContradiction (fun hn => hc hn)
  have p20826 := n20826 _v _q h2351
  exact p20826
theorem n20828 (_v : Vars) (_q : Query _v)  : (e7668 _v) := by
  have p14544 := n14544 _v _q 
  have p20827 := n20827 _v _q 
  change (e2351 _v) ∨ (¬ (e7660 _v)) at p14544
  change (¬ (e2351 _v)) at p20827
  rcases p14544 with hlit | hlit
  · exact (False.elim (p20827 hlit))
  · exact hlit
theorem n20829 (_v : Vars) (_q : Query _v)  : (e4156 _v) := by
  have p11524 := n11524 _v _q 
  have p20828 := n20828 _v _q 
  change (e7660 _v) ∨ (e4156 _v) at p11524
  change (¬ (e7660 _v)) at p20828
  rcases p11524 with hlit | hlit
  · exact (False.elim (p20828 hlit))
  · exact hlit
theorem n20830 (_v : Vars) (_q : Query _v)  : (e5392 _v) := by
  have p11417 := n11417 _v _q 
  have p20827 := n20827 _v _q 
  change (e2351 _v) ∨ (¬ (e474 _v)) at p11417
  change (¬ (e2351 _v)) at p20827
  rcases p11417 with hlit | hlit
  · exact (False.elim (p20827 hlit))
  · exact hlit
theorem n20831 (_v : Vars) (_q : Query _v)  : (e5403 _v) := by
  have p14577 := n14577 _v _q 
  have p20830 := n20830 _v _q 
  change (e474 _v) ∨ (¬ (e5402 _v)) at p14577
  change (¬ (e474 _v)) at p20830
  rcases p14577 with hlit | hlit
  · exact (False.elim (p20830 hlit))
  · exact hlit
theorem n20832 (_v : Vars) (_q : Query _v) (h2296 : (e2296 _v)) (h5195 : (e5195 _v)) : (e2733 _v) := by
  have p16102 := n16102 _v _q h2296
  have p8549 := n8549 _v _q h5195
  have p8583 := n8583 _v _q h2296
  have p20827 := n20827 _v _q 
  exact FloorCertificate.node_20832 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p16102 p8549 p8583 p20827
theorem n20833 (_v : Vars) (_q : Query _v) (h2296 : (e2296 _v)) (h5195 : (e5195 _v)) : (e4109 _v) := by
  have p14689 := n14689 _v _q 
  have p20832 := n20832 _v _q h2296 h5195
  change (¬ (e2733 _v)) ∨ (¬ (e4108 _v)) at p14689
  rcases p14689 with hlit | hlit
  · exact (False.elim (hlit p20832))
  · exact hlit
theorem n20834 (_v : Vars) (_q : Query _v) (h2296 : (e2296 _v)) (h5195 : (e5195 _v)) : (e2781 _v) := by
  have p20827 := n20827 _v _q 
  have p8549 := n8549 _v _q h5195
  have p16102 := n16102 _v _q h2296
  have p8583 := n8583 _v _q h2296
  exact FloorCertificate.node_20834 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p20827 p8549 p16102 p8583
theorem n20835 (_v : Vars) (_q : Query _v) (h2296 : (e2296 _v)) (h5195 : (e5195 _v)) : (e4271 _v) := by
  have p14699 := n14699 _v _q 
  have p20834 := n20834 _v _q h2296 h5195
  change (¬ (e2781 _v)) ∨ (¬ (e4270 _v)) at p14699
  rcases p14699 with hlit | hlit
  · exact (False.elim (hlit p20834))
  · exact hlit
theorem n20836 (_v : Vars) (_q : Query _v)  : (e488 _v) := by
  have p15090 := n15090 _v _q 
  have p20831 := n20831 _v _q 
  change (e5402 _v) ∨ (e488 _v) at p15090
  change (¬ (e5402 _v)) at p20831
  rcases p15090 with hlit | hlit
  · exact (False.elim (p20831 hlit))
  · exact hlit
theorem n20837 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h3152 : (e3152 _v)) (h3158 : (e3158 _v)) (h3919 : (e3919 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4306 : (e4306 _v)) (h4419 : (e4419 _v)) (h4439 : (e4439 _v)) (h4459 : (e4459 _v)) (h4567 : (e4567 _v)) (h4653 : (e4653 _v)) (h4679 : (e4679 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6630 : (e6630 _v)) (h8045 : (e8045 _v)) : (e7489 _v) := by
  have p17117 := n17117 _v _q 
  have p20467 := n20467 _v _q 
  have p17120 := n17120 _v _q 
  have p8434 := n8434 _v _q h6630
  have p4999 := n4999 _v _q h91
  have p331 := n331 _v _q 
  have p4971 := n4971 _v _q h4419
  have p17079 := n17079 _v _q h3919
  have p16913 := n16913 _v _q 
  have p5001 := n5001 _v _q h4096
  have p17157 := n17157 _v _q h8045
  have p4977 := n4977 _v _q h4285
  have p17133 := n17133 _v _q 
  have p4981 := n4981 _v _q h4260
  have p4979 := n4979 _v _q h4139
  have p17104 := n17104 _v _q 
  have p17874 := n17874 _v _q 
  have p17127 := n17127 _v _q 
  have p17089 := n17089 _v _q 
  have p4998 := n4998 _v _q h3152
  have p13951 := n13951 _v _q 
  have p253 := n253 _v _q h191
  have p17143 := n17143 _v _q h4567
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
  have p17070 := n17070 _v _q h4679
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
  exact FloorCertificate.node_20837 (e2 _v) (e7 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4541 _v) (e4808 _v) p17117 p20467 p17120 p8434 p4999 p331 p4971 p17079 p16913 p5001 p17157 p4977 p17133 p4981 p4979 p17104 p17874 p17127 p17089 p4998 p13951 p253 p17143 p17020 p17138 p20274 p17060 p20470 p4989 p17050 p16778 p17122 p4983 p16729 p20829 p17070 p20426 p20126 p17110 p17053 p20096 p17131 p17108 p17294 p16943 p17058 p17064 p17067 p17080 p17072 p17074 p17069 p20461 p20836 p20653 p17078 p17136 p17087 p17083 p17055 p17093 p17091 p17098 p17106 p16885 p17075 p17141 p17100 p19610 p17102 p15934 p17051 p17096 p17115 p17758 p17124 p17111 p19665 p17113
theorem n20838 (_v : Vars) (_q : Query _v) (h2242 : (e2242 _v)) : (e4439 _v) := by
  have p14925 := n14925 _v _q 
  have p15950 := n15950 _v _q h2242
  change (e4446 _v) ∨ (e4439 _v) at p14925
  change (¬ (e4446 _v)) at p15950
  rcases p14925 with hlit | hlit
  · exact (False.elim (p15950 hlit))
  · exact hlit
theorem n20839 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2242 : (e2242 _v)) (h2402 : (e2402 _v)) (h3152 : (e3152 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6630 : (e6630 _v)) (h6750 : (e6750 _v)) (h6772 : (e6772 _v)) : (e7489 _v) := by
  have p14799 := n14799 _v _q h2402
  have p8458 := n8458 _v _q h6772
  have p8591 := n8591 _v _q h2402
  have p16913 := n16913 _v _q 
  have p15940 := n15940 _v _q h6750
  have p15942 := n15942 _v _q h2402 h6750 h6772
  have p16864 := n16864 _v _q h2402 h6750
  have p8420 := n8420 _v _q h6750
  have p17133 := n17133 _v _q 
  have p15944 := n15944 _v _q h6772
  have p12927 := n12927 _v _q h2242
  have p4981 := n4981 _v _q h4260
  have p16646 := n16646 _v _q h2402 h6750
  have p17104 := n17104 _v _q 
  have p17874 := n17874 _v _q 
  have p17127 := n17127 _v _q 
  have p17089 := n17089 _v _q 
  have p4998 := n4998 _v _q h3152
  have p8553 := n8553 _v _q h2242
  have p13951 := n13951 _v _q 
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
  have p15934 := n15934 _v _q h6630
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
  have p8434 := n8434 _v _q h6630
  exact FloorCertificate.node_20839 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4541 _v) (e4808 _v) p14799 p8458 p8591 p16913 p15940 p15942 p16864 p8420 p17133 p15944 p12927 p4981 p16646 p17104 p17874 p17127 p17089 p4998 p8553 p13951 p253 p15946 p17020 p17138 p20274 p17060 p20470 p4989 p17050 p16778 p17122 p4983 p16729 p20829 p15775 p20426 p20126 p17110 p17053 p20096 p17131 p17108 p17294 p16943 p17058 p17064 p17067 p17080 p17072 p17074 p17069 p20461 p20836 p20653 p17078 p17136 p17087 p17083 p17055 p17093 p17091 p17098 p17106 p15949 p20838 p17141 p17100 p19610 p17102 p15934 p15952 p17096 p17115 p17758 p17124 p17111 p19665 p17113 p17117 p20467 p17120 p4999 p8434
theorem n20840 (_v : Vars) (_q : Query _v) (h2475 : (e2475 _v)) (h6772 : (e6772 _v)) : (e7814 _v) := by
  have p15221 := n15221 _v _q 
  have p15954 := n15954 _v _q h2475 h6772
  change (e7818 _v) ∨ (e7814 _v) at p15221
  change (¬ (e7818 _v)) at p15954
  rcases p15221 with hlit | hlit
  · exact (False.elim (p15954 hlit))
  · exact hlit
theorem n20841 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2475 : (e2475 _v)) (h3152 : (e3152 _v)) (h3158 : (e3158 _v)) (h3937 : (e3937 _v)) (h4096 : (e4096 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4439 : (e4439 _v)) (h4459 : (e4459 _v)) (h4567 : (e4567 _v)) (h4653 : (e4653 _v)) (h4679 : (e4679 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6772 : (e6772 _v)) : (e7489 _v) := by
  have p331 := n331 _v _q 
  have p10893 := n10893 _v _q 
  have p4999 := n4999 _v _q h91
  have p17133 := n17133 _v _q 
  have p5001 := n5001 _v _q h4096
  have p16977 := n16977 _v _q 
  have p16338 := n16338 _v _q h2475
  have p20840 := n20840 _v _q h2475 h6772
  have p15944 := n15944 _v _q h6772
  have p17147 := n17147 _v _q 
  have p4996 := n4996 _v _q h3937
  have p4981 := n4981 _v _q h4260
  have p17256 := n17256 _v _q 
  have p17104 := n17104 _v _q 
  have p17874 := n17874 _v _q 
  have p17127 := n17127 _v _q 
  have p17089 := n17089 _v _q 
  have p4998 := n4998 _v _q h3152
  have p13951 := n13951 _v _q 
  have p253 := n253 _v _q h191
  have p17143 := n17143 _v _q h4567
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
  have p17070 := n17070 _v _q h4679
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
  exact FloorCertificate.node_20841 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2883 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4541 _v) (e4808 _v) p331 p10893 p4999 p17133 p5001 p16977 p16338 p20840 p15944 p17147 p4996 p4981 p17256 p17104 p17874 p17127 p17089 p4998 p13951 p253 p17143 p17020 p17138 p20274 p17060 p20470 p4989 p17050 p16778 p17122 p4983 p16729 p20829 p17070 p20426 p20126 p17110 p17053 p20096 p17131 p17108 p17294 p16943 p17058 p17064 p17067 p17080 p17072 p17074 p17069 p20461 p20836 p20653 p17078 p17136 p17087 p17083 p17055 p17093 p17091 p17098 p17106 p16885 p17075 p17141 p17100 p19610 p17102 p5008 p17051 p17096 p17115 p17758 p17124 p17111 p19665 p17113 p17117 p20467 p17120
theorem n20842 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2242 : (e2242 _v)) (h2787 : (e2787 _v)) (h3152 : (e3152 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6600 : (e6600 _v)) (h8045 : (e8045 _v)) : (e7489 _v) := by
  have p4016 := n4016 _v _q 
  have p10893 := n10893 _v _q 
  have p16913 := n16913 _v _q 
  have p11430 := n11430 _v _q h2787
  have p16349 := n16349 _v _q h2787
  have p17147 := n17147 _v _q 
  have p15907 := n15907 _v _q h6600
  have p4981 := n4981 _v _q h4260
  have p4979 := n4979 _v _q h4139
  have p17104 := n17104 _v _q 
  have p17874 := n17874 _v _q 
  have p17127 := n17127 _v _q 
  have p17089 := n17089 _v _q 
  have p4998 := n4998 _v _q h3152
  have p4977 := n4977 _v _q h4285
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
  exact FloorCertificate.node_20842 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2883 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4541 _v) (e4808 _v) p4016 p10893 p16913 p11430 p16349 p17147 p15907 p4981 p4979 p17104 p17874 p17127 p17089 p4998 p4977 p13951 p17157 p253 p15946 p17020 p8439 p17138 p20274 p17060 p20470 p4989 p17050 p16778 p17122 p4983 p16729 p20829 p15775 p20426 p20126 p17110 p17053 p20096 p17131 p17108 p17294 p16943 p17058 p17064 p17067 p17080 p17072 p17074 p17069 p20461 p20836 p20653 p17078 p17136 p17087 p17083 p17055 p17093 p17091 p17098 p17106 p15949 p20838 p17141 p17100 p19610 p17102 p5008 p15952 p17096 p17115 p17758 p17124 p17111 p19665 p17113 p17117 p20467 p17120 p4999 p17133 p5001 p12927 p8553
theorem n20843 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2242 : (e2242 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h4096 : (e4096 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6571 : (e6571 _v)) (h6776 : (e6776 _v)) (h8045 : (e8045 _v)) : (e7489 _v) := by
  have p15956 := n15956 _v _q h6776
  have p17255 := n17255 _v _q h6571
  have p8601 := n8601 _v _q h6776
  have p17104 := n17104 _v _q 
  have p17874 := n17874 _v _q 
  have p17127 := n17127 _v _q 
  have p17089 := n17089 _v _q 
  have p16977 := n16977 _v _q 
  have p4998 := n4998 _v _q h3152
  have p11445 := n11445 _v _q h6571
  have p17256 := n17256 _v _q 
  have p13951 := n13951 _v _q 
  have p17157 := n17157 _v _q h8045
  have p253 := n253 _v _q h191
  have p15946 := n15946 _v _q h2242
  have p17020 := n17020 _v _q 
  have p17189 := n17189 _v _q h6571
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
  have p10893 := n10893 _v _q 
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
  have p4016 := n4016 _v _q 
  have p4996 := n4996 _v _q h3937
  have p17147 := n17147 _v _q 
  exact FloorCertificate.node_20843 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2883 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4541 _v) (e4808 _v) p15956 p17255 p8601 p17104 p17874 p17127 p17089 p16977 p4998 p11445 p17256 p13951 p17157 p253 p15946 p17020 p17189 p17138 p20274 p17060 p20470 p4989 p17050 p16778 p17122 p4983 p16729 p20829 p15775 p20426 p20126 p17110 p10893 p17053 p20096 p17131 p17108 p17294 p16943 p17058 p17064 p17067 p17080 p17072 p17074 p17069 p20461 p20836 p20653 p17078 p17136 p17087 p17083 p17055 p17093 p17091 p17098 p17106 p15949 p20838 p17141 p17100 p19610 p17102 p5008 p15952 p17096 p17115 p17758 p17124 p17111 p19665 p17113 p17117 p20467 p17120 p4999 p17133 p5001 p12927 p8553 p4016 p4996 p17147
theorem n20844 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2242 : (e2242 _v)) (h2475 : (e2475 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6571 : (e6571 _v)) (h6750 : (e6750 _v)) : (e7489 _v) := by
  have p16338 := n16338 _v _q h2475
  have p8457 := n8457 _v _q h2475
  have p10893 := n10893 _v _q 
  have p8420 := n8420 _v _q h6750
  have p17189 := n17189 _v _q h6571
  have p17255 := n17255 _v _q h6571
  have p16913 := n16913 _v _q 
  have p17147 := n17147 _v _q 
  have p4996 := n4996 _v _q h3937
  have p4981 := n4981 _v _q h4260
  have p17256 := n17256 _v _q 
  have p17104 := n17104 _v _q 
  have p17874 := n17874 _v _q 
  have p17127 := n17127 _v _q 
  have p17089 := n17089 _v _q 
  have p4998 := n4998 _v _q h3152
  have p8553 := n8553 _v _q h2242
  have p13951 := n13951 _v _q 
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
  have p19665 := n19665 _v _q 
  have p17113 := n17113 _v _q 
  have p17117 := n17117 _v _q 
  have p20467 := n20467 _v _q 
  have p17120 := n17120 _v _q 
  have p4999 := n4999 _v _q h91
  have p17133 := n17133 _v _q 
  have p15940 := n15940 _v _q h6750
  have p12927 := n12927 _v _q h2242
  exact FloorCertificate.node_20844 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2883 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4541 _v) (e4808 _v) p16338 p8457 p10893 p8420 p17189 p17255 p16913 p17147 p4996 p4981 p17256 p17104 p17874 p17127 p17089 p4998 p8553 p13951 p253 p15946 p17020 p17138 p20274 p17060 p20470 p4989 p17050 p16778 p17122 p4983 p16729 p20829 p15775 p20426 p20126 p17110 p17053 p20096 p17131 p17108 p17294 p16943 p17058 p17064 p17067 p17080 p17072 p17074 p17069 p20461 p20836 p20653 p17078 p17136 p17087 p17083 p17055 p17093 p17091 p17098 p17106 p15949 p20838 p17141 p17100 p19610 p17102 p5008 p15952 p17096 p17115 p17758 p17124 p17111 p19665 p17113 p17117 p20467 p17120 p4999 p17133 p15940 p12927
theorem n20845 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4434 : (e4434 _v)) (h4562 : (e4562 _v)) (h4608 : (e4608 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h5100 : (e5100 _v)) (h5145 : (e5145 _v)) (h5195 : (e5195 _v)) (h6750 : (e6750 _v)) (h7749 : (e7749 _v)) (h7814 : (e7814 _v)) (h7935 : (e7935 _v)) (h8045 : (e8045 _v)) (h8317 : (e8317 _v)) : (e7489 _v) := by
  have p8663 := n8663 _v _q 
  have p4016 := n4016 _v _q 
  have p8549 := n8549 _v _q h5195
  have p16977 := n16977 _v _q 
  have p17953 := n17953 _v _q 
  have p16729 := n16729 _v _q h51
  have p8420 := n8420 _v _q h6750
  have p17256 := n17256 _v _q 
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p17163 := n17163 _v _q h7935
  have p12839 := n12839 _v _q h5195
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
  have p16867 := n16867 _v _q h6750
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
  have p16394 := n16394 _v _q 
  have p4987 := n4987 _v _q h4434
  have p16576 := n16576 _v _q 
  have p4996 := n4996 _v _q h3937
  have p17147 := n17147 _v _q 
  exact FloorCertificate.node_20845 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2834 _v) (e2849 _v) (e2863 _v) (e2877 _v) (e2883 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p8663 p4016 p8549 p16977 p17953 p16729 p8420 p17256 p17138 p17060 p17163 p12839 p13951 p17174 p4983 p16269 p17157 p17172 p4998 p20829 p17108 p20461 p4981 p20426 p5006 p20126 p17110 p17009 p17053 p17131 p17159 p20096 p16867 p17058 p17294 p16943 p17064 p4991 p15940 p17067 p17069 p17080 p17072 p17083 p17074 p20836 p17078 p20653 p17087 p17136 p17055 p17091 p17093 p17141 p17098 p17106 p17102 p17100 p19610 p16929 p17122 p17096 p17245 p4973 p17758 p5008 p19665 p17115 p17120 p17111 p17124 p17050 p16778 p17113 p17117 p20467 p17104 p17874 p17127 p20274 p20470 p17133 p17089 p16394 p4987 p16576 p4996 p17147
theorem n20846 (_v : Vars) (_q : Query _v) (h6423 : (e6423 _v)) (h6583 : (e6583 _v)) : (e95 _v) := by
  have p20113 := n20113 _v _q 
  have p16656 := n16656 _v _q h6583
  have p17874 := n17874 _v _q 
  have p19610 := n19610 _v _q 
  have p8452 := n8452 _v _q h6423
  have p17758 := n17758 _v _q 
  have p19665 := n19665 _v _q 
  have p20829 := n20829 _v _q 
  have p16657 := n16657 _v _q h6423
  have p20461 := n20461 _v _q 
  have p20836 := n20836 _v _q 
  have p15964 := n15964 _v _q h6423
  have p16943 := n16943 _v _q 
  have p15967 := n15967 _v _q h6423
  have p20426 := n20426 _v _q 
  have p16658 := n16658 _v _q h6423
  have p16396 := n16396 _v _q h6423
  have p16659 := n16659 _v _q h6423
  have p20653 := n20653 _v _q 
  have p16660 := n16660 _v _q h6423
  have p17294 := n17294 _v _q 
  change (e1995 _v) ∨ (¬ (e91 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e3946 _v)) at p20113
  change (¬ (e1995 _v)) at p8452
  rcases p20113 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact (False.elim (p8452 hlit))
  · exact hlit
  · exact (False.elim (hlit p17874))
  · exact (False.elim (hlit p20829))
  · exact (False.elim (hlit p20836))
  · exact (False.elim (hlit p17758))
  · exact (False.elim (hlit p19665))
  · exact (False.elim (hlit p19610))
  · exact (False.elim (hlit p15964))
  · exact (False.elim (hlit p20461))
  · exact (False.elim (hlit p15967))
  · exact (False.elim (hlit p16658))
  · exact (False.elim (hlit p16943))
  · exact (False.elim (hlit p16656))
  · exact (False.elim (hlit p20426))
  · exact (False.elim (hlit p16657))
  · exact (False.elim (hlit p16396))
  · exact (False.elim (hlit p16659))
  · exact (False.elim (hlit p20653))
  · exact (False.elim (hlit p16660))
  · exact (False.elim (hlit p17294))
theorem n20847 (_v : Vars) (_q : Query _v) (h6423 : (e6423 _v)) (h6583 : (e6583 _v)) : (e5134 _v) := by
  have p16235 := n16235 _v _q 
  have p20846 := n20846 _v _q h6423 h6583
  change (e5134 _v) ∨ (e91 _v) at p16235
  change (¬ (e91 _v)) at p20846
  rcases p16235 with hlit | hlit
  · exact hlit
  · exact (False.elim (p20846 hlit))
theorem n20848 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h4260 : (e4260 _v)) (h4434 : (e4434 _v)) (h4562 : (e4562 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h5093 : (e5093 _v)) (h5145 : (e5145 _v)) (h6583 : (e6583 _v)) (h7493 : (e7493 _v)) (h7807 : (e7807 _v)) (h7935 : (e7935 _v)) (h8045 : (e8045 _v)) (h8317 : (e8317 _v)) : (e7489 _v) := by
  have p15373 := n15373 _v _q h7807
  have p4998 := n4998 _v _q h3152
  have p20829 := n20829 _v _q 
  have p17108 := n17108 _v _q 
  have p20461 := n20461 _v _q 
  have p12869 := n12869 _v _q h7807
  have p16663 := n16663 _v _q h6583
  have p8663 := n8663 _v _q 
  have p17157 := n17157 _v _q h8045
  have p20426 := n20426 _v _q 
  have p5006 := n5006 _v _q h4675
  have p20126 := n20126 _v _q 
  have p17110 := n17110 _v _q 
  have p17009 := n17009 _v _q 
  have p17053 := n17053 _v _q 
  have p17131 := n17131 _v _q 
  have p15321 := n15321 _v _q h5093
  have p20096 := n20096 _v _q 
  have p16656 := n16656 _v _q h6583
  have p17155 := n17155 _v _q h7493
  have p17058 := n17058 _v _q 
  have p17294 := n17294 _v _q 
  have p16943 := n16943 _v _q 
  have p17064 := n17064 _v _q 
  have p4991 := n4991 _v _q h4608
  have p15974 := n15974 _v _q h6583
  have p17067 := n17067 _v _q 
  have p17069 := n17069 _v _q 
  have p17080 := n17080 _v _q 
  have p17072 := n17072 _v _q 
  have p17083 := n17083 _v _q 
  have p17074 := n17074 _v _q 
  have p20836 := n20836 _v _q 
  have p5010 := n5010 _v _q h70
  have p17078 := n17078 _v _q 
  have p20653 := n20653 _v _q 
  have p17087 := n17087 _v _q 
  have p17136 := n17136 _v _q 
  have p17055 := n17055 _v _q 
  have p17091 := n17091 _v _q 
  have p17093 := n17093 _v _q 
  have p11350 := n11350 _v _q h7807
  have p17141 := n17141 _v _q 
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p17102 := n17102 _v _q 
  have p17100 := n17100 _v _q 
  have p19610 := n19610 _v _q 
  have p16929 := n16929 _v _q 
  have p17122 := n17122 _v _q 
  have p17096 := n17096 _v _q 
  have p15338 := n15338 _v _q h6583
  have p4973 := n4973 _v _q h4562
  have p17758 := n17758 _v _q 
  have p17163 := n17163 _v _q h7935
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
  have p16869 := n16869 _v _q h6583
  have p20274 := n20274 _v _q 
  have p20470 := n20470 _v _q 
  have p17133 := n17133 _v _q 
  have p17089 := n17089 _v _q 
  have p17245 := n17245 _v _q h5145
  have p16394 := n16394 _v _q 
  have p4987 := n4987 _v _q h4434
  have p4981 := n4981 _v _q h4260
  have p16576 := n16576 _v _q 
  have p4996 := n4996 _v _q h3937
  have p17147 := n17147 _v _q 
  have p16977 := n16977 _v _q 
  have p16388 := n16388 _v _q h6583
  have p16994 := n16994 _v _q 
  have p17786 := n17786 _v _q h7807
  have p13951 := n13951 _v _q 
  have p17221 := n17221 _v _q 
  have p17174 := n17174 _v _q h8317
  have p11440 := n11440 _v _q h5093
  have p11340 := n11340 _v _q h6583
  have p4983 := n4983 _v _q h4813
  exact FloorCertificate.node_20848 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e61 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2834 _v) (e2849 _v) (e2863 _v) (e2877 _v) (e2879 _v) (e2883 _v) (e2898 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p15373 p4998 p20829 p17108 p20461 p12869 p16663 p8663 p17157 p20426 p5006 p20126 p17110 p17009 p17053 p17131 p15321 p20096 p16656 p17155 p17058 p17294 p16943 p17064 p4991 p15974 p17067 p17069 p17080 p17072 p17083 p17074 p20836 p5010 p17078 p20653 p17087 p17136 p17055 p17091 p17093 p11350 p17141 p17098 p17106 p17102 p17100 p19610 p16929 p17122 p17096 p15338 p4973 p17758 p17163 p5008 p19665 p17115 p17120 p17111 p17124 p17050 p16778 p17113 p17117 p20467 p17104 p17874 p17127 p16869 p20274 p20470 p17133 p17089 p17245 p16394 p4987 p4981 p16576 p4996 p17147 p16977 p16388 p16994 p17786 p13951 p17221 p17174 p11440 p11340 p4983
theorem n20849 (_v : Vars) (_q : Query _v) (h225 : (e225 _v)) (h4813 : (e4813 _v)) (h6423 : (e6423 _v)) : (e95 _v) := by
  have p20113 := n20113 _v _q 
  have p5007 := n5007 _v _q h225
  have p17874 := n17874 _v _q 
  have p19610 := n19610 _v _q 
  have p8452 := n8452 _v _q h6423
  have p17758 := n17758 _v _q 
  have p19665 := n19665 _v _q 
  have p20829 := n20829 _v _q 
  have p16652 := n16652 _v _q h6423
  have p20461 := n20461 _v _q 
  have p20836 := n20836 _v _q 
  have p16666 := n16666 _v _q h6423
  have p16943 := n16943 _v _q 
  have p16667 := n16667 _v _q h6423
  have p20426 := n20426 _v _q 
  have p16668 := n16668 _v _q h6423
  have p16396 := n16396 _v _q h6423
  have p4983 := n4983 _v _q h4813
  have p20653 := n20653 _v _q 
  have p16669 := n16669 _v _q h6423
  have p17294 := n17294 _v _q 
  change (e1995 _v) ∨ (¬ (e91 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e3946 _v)) at p20113
  change (¬ (e1995 _v)) at p8452
  rcases p20113 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact (False.elim (p8452 hlit))
  · exact hlit
  · exact (False.elim (hlit p17874))
  · exact (False.elim (hlit p20829))
  · exact (False.elim (hlit p20836))
  · exact (False.elim (hlit p17758))
  · exact (False.elim (hlit p19665))
  · exact (False.elim (hlit p19610))
  · exact (False.elim (hlit p16666))
  · exact (False.elim (hlit p20461))
  · exact (False.elim (hlit p16667))
  · exact (False.elim (hlit p16668))
  · exact (False.elim (hlit p16943))
  · exact (False.elim (hlit p5007))
  · exact (False.elim (hlit p20426))
  · exact (False.elim (hlit p16652))
  · exact (False.elim (hlit p16396))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p20653))
  · exact (False.elim (hlit p16669))
  · exact (False.elim (hlit p17294))
theorem n20850 (_v : Vars) (_q : Query _v) (h225 : (e225 _v)) (h4813 : (e4813 _v)) (h6423 : (e6423 _v)) : (e5134 _v) := by
  have p16235 := n16235 _v _q 
  have p20849 := n20849 _v _q h225 h4813 h6423
  change (e5134 _v) ∨ (e91 _v) at p16235
  change (¬ (e91 _v)) at p20849
  rcases p16235 with hlit | hlit
  · exact hlit
  · exact (False.elim (p20849 hlit))
theorem n20851 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h3152 : (e3152 _v)) (h4260 : (e4260 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h6454 : (e6454 _v)) : (e75 _v) := by
  have p20056 := n20056 _v _q 
  have p12905 := n12905 _v _q h6454
  have p17020 := n17020 _v _q 
  have p4999 := n4999 _v _q h91
  have p20461 := n20461 _v _q 
  have p20829 := n20829 _v _q 
  have p20836 := n20836 _v _q 
  have p5006 := n5006 _v _q h4675
  have p5008 := n5008 _v _q h4787
  have p16943 := n16943 _v _q 
  have p4983 := n4983 _v _q h4813
  have p20426 := n20426 _v _q 
  have p4998 := n4998 _v _q h3152
  have p4981 := n4981 _v _q h4260
  have p15764 := n15764 _v _q h6454
  have p20653 := n20653 _v _q 
  have p16947 := n16947 _v _q h91 h6454
  change (e2179 _v) ∨ (¬ (e4260 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e3152 _v)) at p20056
  change (¬ (e2179 _v)) at p12905
  rcases p20056 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact (False.elim (p12905 hlit))
  · exact (False.elim (hlit p4981))
  · exact hlit
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p20461))
  · exact (False.elim (hlit p20829))
  · exact (False.elim (hlit p20836))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p16947))
  · exact (False.elim (hlit p16943))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p20426))
  · exact (False.elim (hlit p17020))
  · exact (False.elim (hlit p15764))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p20653))
  · exact (False.elim (hlit p4998))
theorem n20852 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2061 : (e2061 _v)) (h2132 : (e2132 _v)) (h3152 : (e3152 _v)) (h4260 : (e4260 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6501 : (e6501 _v)) : (e7489 _v) := by
  have p20166 := n20166 _v _q 
  have p16048 := n16048 _v _q h2132 h6501
  have p16051 := n16051 _v _q h2132 h6501
  have p11409 := n11409 _v _q h2061
  have p20306 := n20306 _v _q 
  have p5006 := n5006 _v _q h4675
  have p16873 := n16873 _v _q h2132
  have p16850 := n16850 _v _q h2132
  have p4998 := n4998 _v _q h3152
  have p253 := n253 _v _q h191
  have p8554 := n8554 _v _q h6501
  have p20653 := n20653 _v _q 
  have p16943 := n16943 _v _q 
  have p16681 := n16681 _v _q h2132 h6501
  have p4999 := n4999 _v _q h91
  have p4989 := n4989 _v _q h4838
  have p20461 := n20461 _v _q 
  have p16515 := n16515 _v _q h2132
  have p16567 := n16567 _v _q h2132
  have p20467 := n20467 _v _q 
  have p20426 := n20426 _v _q 
  have p17020 := n17020 _v _q 
  have p16054 := n16054 _v _q h2132 h6501
  have p4983 := n4983 _v _q h4813
  have p5008 := n5008 _v _q h4787
  have p20470 := n20470 _v _q 
  have p20829 := n20829 _v _q 
  have p4981 := n4981 _v _q h4260
  have p16683 := n16683 _v _q h2132
  have p20836 := n20836 _v _q 
  have p16336 := n16336 _v _q h2132
  change (¬ (e4220 _v)) ∨ (¬ (e2061 _v)) ∨ (¬ (e4648 _v)) ∨ (¬ (e4899 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e4546 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e30 _v)) ∨ (¬ (e4285 _v)) ∨ (¬ (e4398 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4301 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4724 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4419 _v)) ∨ (¬ (e488 _v)) ∨ (e2179 _v) at p20166
  change (¬ (e2179 _v)) at p8554
  rcases p20166 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact (False.elim (hlit p16336))
  · exact (False.elim (hlit p11409))
  · exact (False.elim (hlit p16681))
  · exact (False.elim (hlit p20306))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p16850))
  · exact (False.elim (hlit p16873))
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p253))
  · exact (False.elim (hlit p16048))
  · exact (False.elim (hlit p20653))
  · exact (False.elim (hlit p16943))
  · exact (False.elim (hlit p16051))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p4989))
  · exact (False.elim (hlit p20461))
  · exact (False.elim (hlit p16515))
  · exact (False.elim (hlit p16567))
  · exact (False.elim (hlit p20467))
  · exact (False.elim (hlit p20426))
  · exact (False.elim (hlit p17020))
  · exact (False.elim (hlit p16054))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p20470))
  · exact (False.elim (hlit p20829))
  · exact (False.elim (hlit p4981))
  · exact (False.elim (hlit p16683))
  · exact (False.elim (hlit p20836))
  · exact (False.elim (p8554 hlit))
end
end Assembly
