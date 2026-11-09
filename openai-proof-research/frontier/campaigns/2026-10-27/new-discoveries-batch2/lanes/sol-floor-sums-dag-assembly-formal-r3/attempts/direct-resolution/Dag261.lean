import Dag260
import generated.th_lemma_35
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n21903 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6454 : (e6454 _v)) : (e6776 _v) := by
  have p21900 := n21900 _v _q h51 h4306 h4653 h4813
  have p5255 := n5255 _v _q 
  have p8430 := n8430 _v _q h6454
  exact FloorCertificate.node_21903 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p21900 p5255 p8430
theorem n21904 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6454 : (e6454 _v)) : (e7789 _v) := by
  have p14570 := n14570 _v _q 
  have p21903 := n21903 _v _q h51 h4306 h4653 h4813 h6454
  simp only [e2781, e4258, e4259, e4260, e4261, e6776, e7781, e7789, e7792] at *
  tauto
theorem n21905 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e5203 _v) := by
  have p14730 := n14730 _v _q 
  have p21899 := n21899 _v _q h51 h4306 h4653 h4813
  simp only [e191, e192, e193, e194, e196, e5193, e5195, e5203, e5206] at *
  tauto
theorem n21906 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e191 _v) := by
  have p16442 := n16442 _v _q 
  have p21905 := n21905 _v _q h51 h4306 h4653 h4813
  simp only [e191, e192, e193, e194, e5193, e5194, e5203] at *
  tauto
theorem n21907 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2468 : (e2468 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e4101 _v) := by
  have p14929 := n14929 _v _q 
  have p21203 := n21203 _v _q h51 h2468 h4306 h4653 h4813
  simp only [e4101, e4102, e4106, e4107, e4108, e4109, e4952] at *
  tauto
theorem n21908 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) : (e4459 _v) := by
  have p8443 := n8443 _v _q 
  have p16122 := n16122 _v _q h2468
  simp only [e4458, e4459, e4463, e4464, e4465, e4466, e4482] at *
  tauto
theorem n21909 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2296 : (e2296 _v)) (h2468 : (e2468 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5145 : (e5145 _v)) : (e7489 _v) := by
  have p8583 := n8583 _v _q h2296
  have p5257 := n5257 _v _q 
  have p21900 := n21900 _v _q h51 h4306 h4653 h4813
  have p8438 := n8438 _v _q h2468
  have p13951 := n13951 _v _q 
  have p20651 := n20651 _v _q 
  have p17136 := n17136 _v _q 
  have p21902 := n21902 _v _q h51 h4306 h4653 h4813
  have p17087 := n17087 _v _q 
  have p17055 := n17055 _v _q 
  have p15073 := n15073 _v _q h2468
  have p17098 := n17098 _v _q 
  have p15104 := n15104 _v _q h2468
  have p21907 := n21907 _v _q h51 h2468 h4306 h4653 h4813
  have p17083 := n17083 _v _q 
  have p16074 := n16074 _v _q h2468
  have p17106 := n17106 _v _q 
  have p17020 := n17020 _v _q 
  have p17093 := n17093 _v _q 
  have p17245 := n17245 _v _q h5145
  have p16859 := n16859 _v _q h2468
  have p17100 := n17100 _v _q 
  have p16067 := n16067 _v _q h2468
  have p17141 := n17141 _v _q 
  have p17102 := n17102 _v _q 
  have p17091 := n17091 _v _q 
  have p15100 := n15100 _v _q h2296
  have p17096 := n17096 _v _q 
  have p21748 := n21748 _v _q h51 h4306 h4653 h4813
  have p16120 := n16120 _v _q h2296 h2468
  have p17758 := n17758 _v _q 
  have p21908 := n21908 _v _q h2468
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
  have p20461 := n20461 _v _q 
  have p20836 := n20836 _v _q 
  exact FloorCertificate.node_21909 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2902 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e4808 _v) p8583 p5257 p21900 p8438 p13951 p20651 p17136 p21902 p17087 p17055 p15073 p17098 p15104 p21907 p17083 p16074 p17106 p17020 p17093 p17245 p16859 p17100 p16067 p17141 p17102 p17091 p15100 p17096 p21748 p16120 p17758 p21908 p17124 p19610 p17111 p17115 p17256 p17078 p17113 p17117 p20467 p19665 p17133 p17120 p17104 p17874 p17127 p17089 p20653 p21727 p17138 p20274 p17060 p20470 p17050 p16778 p17122 p4983 p16729 p20829 p20426 p20126 p17110 p17053 p20096 p17131 p17108 p17294 p16943 p17058 p17064 p17067 p17080 p17072 p17074 p17069 p20461 p20836
theorem n21910 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6454 : (e6454 _v)) : (e4260 _v) := by
  have p15824 := n15824 _v _q 
  have p21904 := n21904 _v _q h51 h4306 h4653 h4813 h6454
  simp only [e4258, e4259, e4260, e4261, e7781, e7782, e7789] at *
  tauto
theorem n21912 (_v : Vars) (_q : Query _v)  : (e21911 _v) := by
  by_contra hc
  change ¬ ((¬ (e5145 _v)) ∨ (¬ (e2296 _v)) ∨ (¬ (e2468 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v))) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn)))))))
  have h2296 : (e2296 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h2468 : (e2468 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h5145 : (e5145 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have p21909 := n21909 _v _q h51 h2296 h2468 h4306 h4653 h4813 h5145
  exact p21909
theorem n21913 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2296 : (e2296 _v)) (h2468 : (e2468 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e5148 _v) := by
  have p21912 := n21912 _v _q 
  have p8583 := n8583 _v _q h2296
  have p8438 := n8438 _v _q h2468
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  simp only [e51, e57, e2296, e2468, e4306, e4311, e4653, e4658, e4813, e4814, e5145, e5148, e6549, e6630, e21911] at *
  tauto
theorem n21914 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2296 : (e2296 _v)) (h2468 : (e2468 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e5149 _v) := by
  have p15925 := n15925 _v _q 
  have p21913 := n21913 _v _q h51 h2296 h2468 h4306 h4653 h4813
  simp only [e5143, e5145, e5147, e5148, e5149, e5152] at *
  tauto
theorem n21915 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2296 : (e2296 _v)) (h2468 : (e2468 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e79 _v) := by
  have p15115 := n15115 _v _q 
  have p21914 := n21914 _v _q h51 h2296 h2468 h4306 h4653 h4813
  simp only [e79, e5143, e5145, e5147, e5148, e5149, e5150, e8647] at *
  tauto
theorem n21916 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2296 : (e2296 _v)) (h2468 : (e2468 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e5135 _v) := by
  have p14729 := n14729 _v _q 
  have p21915 := n21915 _v _q h51 h2296 h2468 h4306 h4653 h4813
  simp only [e79, e89, e91, e94, e95, e5134, e5135, e5138, e5140] at *
  tauto
theorem n21917 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2296 : (e2296 _v)) (h2468 : (e2468 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e91 _v) := by
  have p16235 := n16235 _v _q 
  have p21916 := n21916 _v _q h51 h2296 h2468 h4306 h4653 h4813
  simp only [e89, e91, e94, e95, e5134, e5135, e7983] at *
  tauto
theorem n21918 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2296 : (e2296 _v)) (h2468 : (e2468 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e7489 _v) := by
  have p8583 := n8583 _v _q h2296
  have p5257 := n5257 _v _q 
  have p21900 := n21900 _v _q h51 h4306 h4653 h4813
  have p8438 := n8438 _v _q h2468
  have p13951 := n13951 _v _q 
  have p20836 := n20836 _v _q 
  have p17136 := n17136 _v _q 
  have p21902 := n21902 _v _q h51 h4306 h4653 h4813
  have p17087 := n17087 _v _q 
  have p17055 := n17055 _v _q 
  have p15073 := n15073 _v _q h2468
  have p17098 := n17098 _v _q 
  have p15104 := n15104 _v _q h2468
  have p21907 := n21907 _v _q h51 h2468 h4306 h4653 h4813
  have p17083 := n17083 _v _q 
  have p16074 := n16074 _v _q h2468
  have p17106 := n17106 _v _q 
  have p17020 := n17020 _v _q 
  have p17093 := n17093 _v _q 
  have p21913 := n21913 _v _q h51 h2296 h2468 h4306 h4653 h4813
  have p16859 := n16859 _v _q h2468
  have p17100 := n17100 _v _q 
  have p16067 := n16067 _v _q h2468
  have p17141 := n17141 _v _q 
  have p17102 := n17102 _v _q 
  have p17091 := n17091 _v _q 
  have p15100 := n15100 _v _q h2296
  have p17096 := n17096 _v _q 
  have p21748 := n21748 _v _q h51 h4306 h4653 h4813
  have p16120 := n16120 _v _q h2296 h2468
  have p17758 := n17758 _v _q 
  have p21908 := n21908 _v _q h2468
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
  have p20461 := n20461 _v _q 
  have p258 := n258 _v _q 
  have p21917 := n21917 _v _q h51 h2296 h2468 h4306 h4653 h4813
  exact FloorCertificate.node_21918 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2902 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e4808 _v) p8583 p5257 p21900 p8438 p13951 p20836 p17136 p21902 p17087 p17055 p15073 p17098 p15104 p21907 p17083 p16074 p17106 p17020 p17093 p21913 p16859 p17100 p16067 p17141 p17102 p17091 p15100 p17096 p21748 p16120 p17758 p21908 p17124 p19610 p17111 p17115 p17256 p17078 p17113 p17117 p20467 p19665 p17133 p17120 p17104 p17874 p17127 p17089 p20653 p21727 p17138 p20274 p17060 p20470 p17050 p16778 p17122 p4983 p16729 p20829 p20426 p20126 p17110 p17053 p20096 p17131 p17108 p17294 p16943 p17058 p17064 p17067 p17080 p17072 p17074 p17069 p20461 p258 p21917
theorem n21920 (_v : Vars) (_q : Query _v)  : (e21919 _v) := by
  by_contra hc
  change ¬ ((¬ (e2296 _v)) ∨ (¬ (e2468 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v))) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))
  have h2296 : (e2296 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h2468 : (e2468 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have p21918 := n21918 _v _q h51 h2296 h2468 h4306 h4653 h4813
  exact p21918
theorem n21921 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2468 : (e2468 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e6549 _v) := by
  have p21920 := n21920 _v _q 
  have p8438 := n8438 _v _q h2468
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  simp only [e51, e57, e2296, e2468, e4306, e4311, e4653, e4658, e4813, e4814, e6549, e6630, e21919] at *
  tauto
theorem n21922 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2468 : (e2468 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e6879 _v) := by
  have p14643 := n14643 _v _q 
  have p21921 := n21921 _v _q h51 h2468 h4306 h4653 h4813
  simp only [e2296, e3150, e3152, e3155, e3156, e6549, e6878, e6879, e6882] at *
  tauto
theorem n21923 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2468 : (e2468 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e3152 _v) := by
  have p15776 := n15776 _v _q 
  have p21922 := n21922 _v _q h51 h2468 h4306 h4653 h4813
  simp only [e3150, e3152, e3155, e3156, e6878, e6879, e8223] at *
  tauto
theorem n21924 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) (h5138 : (e5138 _v)) : (e4271 _v) := by
  have p14699 := n14699 _v _q 
  have p12951 := n12951 _v _q h2468 h5138
  simp only [e2781, e4263, e4264, e4268, e4269, e4270, e4271, e6776, e7795] at *
  tauto
theorem n21925 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) (h5138 : (e5138 _v)) : (e4264 _v) := by
  have p14966 := n14966 _v _q 
  have p21924 := n21924 _v _q h2468 h5138
  simp only [e4263, e4264, e4268, e4269, e4270, e4271, e4959] at *
  tauto
theorem n21926 (_v : Vars) (_q : Query _v) (h5138 : (e5138 _v)) : (e7814 _v) := by
  have p15221 := n15221 _v _q 
  have p16123 := n16123 _v _q h5138
  simp only [e7812, e7814, e7816, e7817, e7818, e7819, e8456] at *
  tauto
theorem n21927 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2468 : (e2468 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5138 : (e5138 _v)) : (e7489 _v) := by
  have p5391 := n5391 _v _q 
  have p21900 := n21900 _v _q h51 h4306 h4653 h4813
  have p8438 := n8438 _v _q h2468
  have p5255 := n5255 _v _q 
  have p13951 := n13951 _v _q 
  have p17136 := n17136 _v _q 
  have p21902 := n21902 _v _q h51 h4306 h4653 h4813
  have p17087 := n17087 _v _q 
  have p17055 := n17055 _v _q 
  have p15073 := n15073 _v _q h2468
  have p17098 := n17098 _v _q 
  have p15104 := n15104 _v _q h2468
  have p21907 := n21907 _v _q h51 h2468 h4306 h4653 h4813
  have p17083 := n17083 _v _q 
  have p16074 := n16074 _v _q h2468
  have p17106 := n17106 _v _q 
  have p17020 := n17020 _v _q 
  have p17093 := n17093 _v _q 
  have p15927 := n15927 _v _q h5138
  have p21921 := n21921 _v _q h51 h2468 h4306 h4653 h4813
  have p16859 := n16859 _v _q h2468
  have p17100 := n17100 _v _q 
  have p16067 := n16067 _v _q h2468
  have p17141 := n17141 _v _q 
  have p17102 := n17102 _v _q 
  have p17091 := n17091 _v _q 
  have p17096 := n17096 _v _q 
  have p21748 := n21748 _v _q h51 h4306 h4653 h4813
  have p21925 := n21925 _v _q h2468 h5138
  have p17758 := n17758 _v _q 
  have p21908 := n21908 _v _q h2468
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
  have p20461 := n20461 _v _q 
  have p20836 := n20836 _v _q 
  have p21926 := n21926 _v _q h5138
  have p21923 := n21923 _v _q h51 h2468 h4306 h4653 h4813
  exact FloorCertificate.node_21927 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2902 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4808 _v) p5391 p21900 p8438 p5255 p13951 p17136 p21902 p17087 p17055 p15073 p17098 p15104 p21907 p17083 p16074 p17106 p17020 p17093 p15927 p21921 p16859 p17100 p16067 p17141 p17102 p17091 p17096 p21748 p21925 p17758 p21908 p17124 p19610 p17111 p17115 p17256 p17078 p17113 p17117 p20467 p19665 p17133 p17120 p17104 p17874 p17127 p17089 p20653 p21727 p17138 p20274 p17060 p20470 p17050 p16778 p17122 p4983 p16729 p20829 p20426 p20126 p17110 p17053 p20096 p17131 p17108 p17294 p16943 p17058 p17064 p17067 p17080 p17072 p17074 p17069 p20461 p20836 p21926 p21923
theorem n21929 (_v : Vars) (_q : Query _v)  : (e21928 _v) := by
  by_contra hc
  change ¬ ((e79 _v) ∨ (¬ (e2468 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v))) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))
  have h2468 : (e2468 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h5138 : (e5138 _v) := (fun hn => hc (Or.inl hn))
  have p21927 := n21927 _v _q h51 h2468 h4306 h4653 h4813 h5138
  exact p21927
theorem n21930 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2468 : (e2468 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e79 _v) := by
  have p21929 := n21929 _v _q 
  have p8438 := n8438 _v _q h2468
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  simp only [e51, e57, e79, e2468, e4306, e4311, e4653, e4658, e4813, e4814, e6630, e21928] at *
  tauto
theorem n21931 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2468 : (e2468 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e5135 _v) := by
  have p14729 := n14729 _v _q 
  have p21930 := n21930 _v _q h51 h2468 h4306 h4653 h4813
  simp only [e79, e89, e91, e94, e95, e5134, e5135, e5138, e5140] at *
  tauto
theorem n21932 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2468 : (e2468 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e91 _v) := by
  have p16235 := n16235 _v _q 
  have p21931 := n21931 _v _q h51 h2468 h4306 h4653 h4813
  simp only [e89, e91, e94, e95, e5134, e5135, e7983] at *
  tauto
theorem n21933 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2468 : (e2468 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e8310 _v) := by
  have p21178 := n21178 _v _q 
  have p21932 := n21932 _v _q h51 h2468 h4306 h4653 h4813
  have p16729 := n16729 _v _q h51
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4983 := n4983 _v _q h4813
  have p8438 := n8438 _v _q h2468
  simp only [e51, e57, e91, e95, e2468, e2529, e4306, e4311, e4653, e4658, e4813, e4814, e6630, e8310, e21177] at *
  tauto
theorem n21934 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2468 : (e2468 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e7807 _v) := by
  have p11387 := n11387 _v _q 
  have p21933 := n21933 _v _q h51 h2468 h4306 h4653 h4813
  simp only [e2303, e2529, e7807, e8310, e11386] at *
  tauto
theorem n21935 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2468 : (e2468 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e7819 _v) := by
  have p14994 := n14994 _v _q 
  have p21934 := n21934 _v _q h51 h2468 h4306 h4653 h4813
  simp only [e2303, e7807, e7812, e7814, e7816, e7817, e7818, e7819, e11046] at *
  tauto
theorem n21936 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2468 : (e2468 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e7814 _v) := by
  have p15221 := n15221 _v _q 
  have p21935 := n21935 _v _q h51 h2468 h4306 h4653 h4813
  simp only [e7812, e7814, e7816, e7817, e7818, e7819, e8456] at *
  tauto
theorem n21937 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2468 : (e2468 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e2781 _v) := by
  have p8438 := n8438 _v _q h2468
  have p21934 := n21934 _v _q h51 h2468 h4306 h4653 h4813
  exact FloorCertificate.node_21937 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8438 p21934
theorem n21938 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2468 : (e2468 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e4271 _v) := by
  have p14699 := n14699 _v _q 
  have p21937 := n21937 _v _q h51 h2468 h4306 h4653 h4813
  simp only [e2781, e4263, e4264, e4268, e4269, e4270, e4271, e6776, e7795] at *
  tauto
theorem n21939 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2468 : (e2468 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e4264 _v) := by
  have p14966 := n14966 _v _q 
  have p21938 := n21938 _v _q h51 h2468 h4306 h4653 h4813
  simp only [e4263, e4264, e4268, e4269, e4270, e4271, e4959] at *
  tauto
theorem n21940 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2468 : (e2468 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e7489 _v) := by
  have p21921 := n21921 _v _q h51 h2468 h4306 h4653 h4813
  have p5257 := n5257 _v _q 
  have p8438 := n8438 _v _q h2468
  have p21934 := n21934 _v _q h51 h2468 h4306 h4653 h4813
  have p21930 := n21930 _v _q h51 h2468 h4306 h4653 h4813
  have p21932 := n21932 _v _q h51 h2468 h4306 h4653 h4813
  have p20836 := n20836 _v _q 
  have p20461 := n20461 _v _q 
  have p21923 := n21923 _v _q h51 h2468 h4306 h4653 h4813
  have p21936 := n21936 _v _q h51 h2468 h4306 h4653 h4813
  have p17136 := n17136 _v _q 
  have p21902 := n21902 _v _q h51 h4306 h4653 h4813
  have p17087 := n17087 _v _q 
  have p17055 := n17055 _v _q 
  have p15073 := n15073 _v _q h2468
  have p17098 := n17098 _v _q 
  have p15104 := n15104 _v _q h2468
  have p21907 := n21907 _v _q h51 h2468 h4306 h4653 h4813
  have p17083 := n17083 _v _q 
  have p16074 := n16074 _v _q h2468
  have p17106 := n17106 _v _q 
  have p17020 := n17020 _v _q 
  have p17093 := n17093 _v _q 
  have p16859 := n16859 _v _q h2468
  have p17100 := n17100 _v _q 
  have p16067 := n16067 _v _q h2468
  have p17141 := n17141 _v _q 
  have p17102 := n17102 _v _q 
  have p17091 := n17091 _v _q 
  have p17096 := n17096 _v _q 
  have p21748 := n21748 _v _q h51 h4306 h4653 h4813
  have p21939 := n21939 _v _q h51 h2468 h4306 h4653 h4813
  have p17758 := n17758 _v _q 
  have p21908 := n21908 _v _q h2468
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
  have p21900 := n21900 _v _q h51 h4306 h4653 h4813
  exact FloorCertificate.node_21940 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2902 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4808 _v) p21921 p5257 p8438 p21934 p21930 p21932 p20836 p20461 p21923 p21936 p17136 p21902 p17087 p17055 p15073 p17098 p15104 p21907 p17083 p16074 p17106 p17020 p17093 p16859 p17100 p16067 p17141 p17102 p17091 p17096 p21748 p21939 p17758 p21908 p17124 p19610 p17111 p17115 p17256 p17078 p17113 p17117 p20467 p19665 p17133 p17120 p17104 p17874 p17127 p17089 p20653 p21727 p17138 p20274 p17060 p20470 p17050 p16778 p17122 p4983 p16729 p20829 p20426 p20126 p17110 p17053 p20096 p17131 p17108 p17294 p16943 p17058 p17064 p17067 p17080 p17072 p17074 p17069 p13951 p21900
theorem n21942 (_v : Vars) (_q : Query _v)  : (e21941 _v) := by
  by_contra hc
  change ¬ ((¬ (e2468 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v))) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr hn)))))
  have h2468 : (e2468 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have p21940 := n21940 _v _q h51 h2468 h4306 h4653 h4813
  exact p21940
theorem n21943 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e6630 _v) := by
  have p21942 := n21942 _v _q 
  have p16729 := n16729 _v _q h51
  have p17060 := n17060 _v _q h4653
  have p4983 := n4983 _v _q h4813
  have p17138 := n17138 _v _q h4306
  simp only [e51, e57, e2468, e4306, e4311, e4653, e4658, e4813, e4814, e6630, e21941] at *
  tauto
theorem n21944 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e6630 _v) := by
  have p21942 := n21942 _v _q 
  have p17138 := n17138 _v _q h4306
  have p16729 := n16729 _v _q h51
  have p4983 := n4983 _v _q h4813
  have p17060 := n17060 _v _q h4653
  simp only [e51, e57, e2468, e4306, e4311, e4653, e4658, e4813, e4814, e6630, e21941] at *
  tauto
theorem n21945 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e8275 _v) := by
  have p14655 := n14655 _v _q 
  have p21943 := n21943 _v _q h51 h4306 h4653 h4813
  simp only [e2468, e4785, e4786, e4787, e4788, e6630, e8267, e8275, e8278] at *
  tauto
theorem n21946 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e4787 _v) := by
  have p15670 := n15670 _v _q 
  have p21945 := n21945 _v _q h51 h4306 h4653 h4813
  simp only [e4785, e4786, e4787, e4788, e8267, e8268, e8275] at *
  tauto
theorem n21947 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e8275 _v) := by
  have p14655 := n14655 _v _q 
  have p21944 := n21944 _v _q h51 h4306 h4653 h4813
  simp only [e2468, e4785, e4786, e4787, e4788, e6630, e8267, e8275, e8278] at *
  tauto
theorem n21948 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e4787 _v) := by
  have p15670 := n15670 _v _q 
  have p21947 := n21947 _v _q h51 h4306 h4653 h4813
  simp only [e4785, e4786, e4787, e4788, e8267, e8268, e8275] at *
  tauto
theorem n21949 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2781 : (e2781 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e7807 _v) := by
  have p8581 := n8581 _v _q 
  have p8421 := n8421 _v _q h2781
  have p21944 := n21944 _v _q h51 h4306 h4653 h4813
  simp only [e2303, e2468, e2781, e6630, e6776, e7807, e8580] at *
  tauto
theorem n21950 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2781 : (e2781 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e7742 _v) := by
  have p11353 := n11353 _v _q 
  have p21949 := n21949 _v _q h51 h2781 h4306 h4653 h4813
  simp only [e2132, e2303, e7742, e7807, e11352] at *
  tauto
theorem n21951 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2781 : (e2781 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e7754 _v) := by
  have p14942 := n14942 _v _q 
  have p21950 := n21950 _v _q h51 h2781 h4306 h4653 h4813
  simp only [e2132, e7742, e7747, e7749, e7751, e7752, e7753, e7754, e11001] at *
  tauto
end
end Assembly
