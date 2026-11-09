import Dag236
import generated.th_lemma_31
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n20703 (_v : Vars) (_q : Query _v)  : (e20702 _v) := by
  by_contra hc
  change ¬ ((¬ (e2475 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e2351 _v)) ∨ (e2402 _v) ∨ (¬ (e91 _v))) at hc
  have h91 : (e91 _v) := by
    tauto
  have h2351 : (e2351 _v) := by
    tauto
  have h2475 : (e2475 _v) := by
    tauto
  have h4813 : (e4813 _v) := by
    tauto
  have h6600 : (e6600 _v) := by
    change (¬ (e2402 _v))
    tauto
  have p20701 := n20701 _v _q h91 h2351 h2475 h4813 h6600
  exact p20701
theorem n20704 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h2351 : (e2351 _v)) (h4813 : (e4813 _v)) (h6600 : (e6600 _v)) : (e8038 _v) := by
  have p20703 := n20703 _v _q 
  have p4999 := n4999 _v _q h91
  have p8464 := n8464 _v _q h2351
  have p8439 := n8439 _v _q h6600
  have p4983 := n4983 _v _q h4813
  simp only [e91, e95, e2351, e2402, e2475, e4813, e4814, e6575, e6600, e8038, e20702] at *
  tauto
theorem n20705 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h2351 : (e2351 _v)) (h4813 : (e4813 _v)) (h6600 : (e6600 _v)) : (e8050 _v) := by
  have p15207 := n15207 _v _q 
  have p20704 := n20704 _v _q h91 h2351 h4813 h6600
  simp only [e2475, e8038, e8043, e8045, e8047, e8048, e8049, e8050, e11165] at *
  tauto
theorem n20706 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h2351 : (e2351 _v)) (h4813 : (e4813 _v)) (h6600 : (e6600 _v)) : (e8045 _v) := by
  have p15206 := n15206 _v _q 
  have p20705 := n20705 _v _q h91 h2351 h4813 h6600
  simp only [e8043, e8045, e8047, e8048, e8049, e8050, e8490] at *
  tauto
theorem n20707 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h2351 : (e2351 _v)) (h4813 : (e4813 _v)) (h6600 : (e6600 _v)) : (e7489 _v) := by
  have p10893 := n10893 _v _q 
  have p4016 := n4016 _v _q 
  have p20691 := n20691 _v _q h91 h2351 h4813 h6600
  have p20687 := n20687 _v _q h91 h2351 h4813 h6600
  have p5255 := n5255 _v _q 
  have p17147 := n17147 _v _q 
  have p20693 := n20693 _v _q h91 h2351 h4813 h6600
  have p4983 := n4983 _v _q h4813
  have p16643 := n16643 _v _q h6600
  have p13951 := n13951 _v _q 
  have p17080 := n17080 _v _q 
  have p8464 := n8464 _v _q h2351
  have p17083 := n17083 _v _q 
  have p17074 := n17074 _v _q 
  have p8439 := n8439 _v _q h6600
  have p20678 := n20678 _v _q h2351
  have p20663 := n20663 _v _q h2351
  have p17078 := n17078 _v _q 
  have p20653 := n20653 _v _q 
  have p4999 := n4999 _v _q h91
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
  have p15907 := n15907 _v _q h6600
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
  have p17131 := n17131 _v _q 
  have p17110 := n17110 _v _q 
  have p17053 := n17053 _v _q 
  have p15917 := n15917 _v _q h2351
  have p20096 := n20096 _v _q 
  have p17294 := n17294 _v _q 
  have p16943 := n16943 _v _q 
  have p17058 := n17058 _v _q 
  have p17064 := n17064 _v _q 
  have p17067 := n17067 _v _q 
  have p17069 := n17069 _v _q 
  have p17072 := n17072 _v _q 
  have p20700 := n20700 _v _q h2351 h4813 h6600
  have p20706 := n20706 _v _q h91 h2351 h4813 h6600
  exact FloorCertificate.node_20707 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2883 _v) (e2902 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e4541 _v) (e4808 _v) p10893 p4016 p20691 p20687 p5255 p17147 p20693 p4983 p16643 p13951 p17080 p8464 p17083 p17074 p8439 p20678 p20663 p17078 p20653 p4999 p17087 p17136 p15793 p17091 p17093 p20682 p17141 p17098 p17106 p17102 p17100 p15907 p19610 p15791 p17122 p17096 p15909 p15786 p17758 p15783 p15911 p15905 p20319 p17115 p17120 p17111 p17124 p17050 p16778 p17113 p17117 p20467 p17104 p17874 p17127 p15914 p20274 p20470 p17133 p17089 p19665 p20426 p17055 p17108 p20461 p20126 p17131 p17110 p17053 p15917 p20096 p17294 p16943 p17058 p17064 p17067 p17069 p17072 p20700 p20706
theorem n20709 (_v : Vars) (_q : Query _v)  : (e20708 _v) := by
  by_contra hc
  change ¬ ((¬ (e91 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e2351 _v)) ∨ (e2402 _v)) at hc
  have h91 : (e91 _v) := by
    tauto
  have h2351 : (e2351 _v) := by
    tauto
  have h4813 : (e4813 _v) := by
    tauto
  have h6600 : (e6600 _v) := by
    change (¬ (e2402 _v))
    tauto
  have p20707 := n20707 _v _q h91 h2351 h4813 h6600
  exact p20707
theorem n20710 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h4813 : (e4813 _v)) (h6600 : (e6600 _v)) : (e95 _v) := by
  have p20709 := n20709 _v _q 
  have p4983 := n4983 _v _q h4813
  have p8464 := n8464 _v _q h2351
  have p8439 := n8439 _v _q h6600
  simp only [e91, e95, e2351, e2402, e4813, e4814, e6575, e6600, e20708] at *
  tauto
theorem n20711 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h4813 : (e4813 _v)) (h6600 : (e6600 _v)) : (e5134 _v) := by
  have p16235 := n16235 _v _q 
  have p20710 := n20710 _v _q h2351 h4813 h6600
  simp only [e89, e91, e94, e95, e5134, e7983] at *
  tauto
theorem n20712 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h4813 : (e4813 _v)) (h6600 : (e6600 _v)) : (e5138 _v) := by
  have p14729 := n14729 _v _q 
  have p20711 := n20711 _v _q h2351 h4813 h6600
  simp only [e79, e89, e91, e94, e95, e5134, e5135, e5138, e5140] at *
  tauto
theorem n20713 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h4813 : (e4813 _v)) (h6600 : (e6600 _v)) : (e5150 _v) := by
  have p15115 := n15115 _v _q 
  have p20712 := n20712 _v _q h2351 h4813 h6600
  simp only [e79, e5138, e5143, e5145, e5147, e5148, e5149, e5150, e8647] at *
  tauto
theorem n20714 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h4813 : (e4813 _v)) (h6600 : (e6600 _v)) : (e5145 _v) := by
  have p15925 := n15925 _v _q 
  have p20713 := n20713 _v _q h2351 h4813 h6600
  simp only [e5143, e5145, e5147, e5148, e5149, e5150, e5152] at *
  tauto
theorem n20715 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h4813 : (e4813 _v)) (h6600 : (e6600 _v)) : (e8038 _v) := by
  have p11510 := n11510 _v _q 
  have p20712 := n20712 _v _q h2351 h4813 h6600
  simp only [e79, e2475, e5138, e8038, e11509] at *
  tauto
theorem n20716 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h4813 : (e4813 _v)) (h6600 : (e6600 _v)) : (e8050 _v) := by
  have p15207 := n15207 _v _q 
  have p20715 := n20715 _v _q h2351 h4813 h6600
  simp only [e2475, e8038, e8043, e8045, e8047, e8048, e8049, e8050, e11165] at *
  tauto
theorem n20717 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h4813 : (e4813 _v)) (h6600 : (e6600 _v)) : (e8045 _v) := by
  have p15206 := n15206 _v _q 
  have p20716 := n20716 _v _q h2351 h4813 h6600
  simp only [e8043, e8045, e8047, e8048, e8049, e8050, e8490] at *
  tauto
theorem n20718 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h4813 : (e4813 _v)) (h6600 : (e6600 _v)) : (e8310 _v) := by
  have p20712 := n20712 _v _q h2351 h4813 h6600
  have p5255 := n5255 _v _q 
  exact FloorCertificate.node_20718 (e2 _v) (e9 _v) (e45 _v) (e110 _v) p20712 p5255
theorem n20719 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h4813 : (e4813 _v)) (h6600 : (e6600 _v)) : (e8322 _v) := by
  have p15218 := n15218 _v _q 
  have p20718 := n20718 _v _q h2351 h4813 h6600
  simp only [e2529, e8310, e8315, e8317, e8319, e8320, e8321, e8322, e11298] at *
  tauto
theorem n20720 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h4813 : (e4813 _v)) (h6600 : (e6600 _v)) : (e8317 _v) := by
  have p11541 := n11541 _v _q 
  have p20719 := n20719 _v _q h2351 h4813 h6600
  simp only [e8315, e8317, e8319, e8320, e8321, e8322, e8491] at *
  tauto
theorem n20721 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h4813 : (e4813 _v)) (h6600 : (e6600 _v)) : (e7489 _v) := by
  have p20712 := n20712 _v _q h2351 h4813 h6600
  have p20714 := n20714 _v _q h2351 h4813 h6600
  have p4016 := n4016 _v _q 
  have p20717 := n20717 _v _q h2351 h4813 h6600
  have p17147 := n17147 _v _q 
  have p20698 := n20698 _v _q h2351 h4813 h6600
  have p4983 := n4983 _v _q h4813
  have p16643 := n16643 _v _q h6600
  have p13951 := n13951 _v _q 
  have p17080 := n17080 _v _q 
  have p8464 := n8464 _v _q h2351
  have p17083 := n17083 _v _q 
  have p17074 := n17074 _v _q 
  have p8439 := n8439 _v _q h6600
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
  have p15907 := n15907 _v _q h6600
  have p19610 := n19610 _v _q 
  have p15791 := n15791 _v _q h2351
  have p17122 := n17122 _v _q 
  have p17096 := n17096 _v _q 
  have p15909 := n15909 _v _q h2351
  have p15786 := n15786 _v _q h2351
  have p17758 := n17758 _v _q 
  have p17953 := n17953 _v _q 
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
  have p17131 := n17131 _v _q 
  have p17110 := n17110 _v _q 
  have p17053 := n17053 _v _q 
  have p15917 := n15917 _v _q h2351
  have p20096 := n20096 _v _q 
  have p17294 := n17294 _v _q 
  have p16943 := n16943 _v _q 
  have p17058 := n17058 _v _q 
  have p17064 := n17064 _v _q 
  have p17067 := n17067 _v _q 
  have p17069 := n17069 _v _q 
  have p17072 := n17072 _v _q 
  have p20700 := n20700 _v _q h2351 h4813 h6600
  have p5255 := n5255 _v _q 
  have p20720 := n20720 _v _q h2351 h4813 h6600
  exact FloorCertificate.node_20721 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2883 _v) (e2902 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e4541 _v) (e4808 _v) p20712 p20714 p4016 p20717 p17147 p20698 p4983 p16643 p13951 p17080 p8464 p17083 p17074 p8439 p20678 p20663 p17078 p20653 p17087 p17136 p15793 p17091 p17093 p20682 p17141 p17098 p17106 p17102 p17100 p15907 p19610 p15791 p17122 p17096 p15909 p15786 p17758 p17953 p15783 p15911 p15905 p20319 p17115 p17120 p17111 p17124 p17050 p16778 p17113 p17117 p20467 p17104 p17874 p17127 p15914 p20274 p20470 p17133 p17089 p19665 p20426 p17055 p17108 p20461 p20126 p17131 p17110 p17053 p15917 p20096 p17294 p16943 p17058 p17064 p17067 p17069 p17072 p20700 p5255 p20720
theorem n20723 (_v : Vars) (_q : Query _v)  : (e20722 _v) := by
  by_contra hc
  change ¬ ((¬ (e4813 _v)) ∨ (¬ (e2351 _v)) ∨ (e2402 _v)) at hc
  have h2351 : (e2351 _v) := by
    tauto
  have h4813 : (e4813 _v) := by
    tauto
  have h6600 : (e6600 _v) := by
    change (¬ (e2402 _v))
    tauto
  have p20721 := n20721 _v _q h2351 h4813 h6600
  exact p20721
theorem n20724 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h6600 : (e6600 _v)) : (e4814 _v) := by
  have p20723 := n20723 _v _q 
  have p8439 := n8439 _v _q h6600
  have p8464 := n8464 _v _q h2351
  simp only [e2351, e2402, e4813, e4814, e6575, e6600, e20722] at *
  tauto
theorem n20725 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h6600 : (e6600 _v)) : (e8284 _v) := by
  have p16259 := n16259 _v _q 
  have p20724 := n20724 _v _q h2351 h6600
  simp only [e4811, e4812, e4813, e4814, e8284, e8285] at *
  tauto
theorem n20726 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h6600 : (e6600 _v)) : (e2522 _v) := by
  have p14657 := n14657 _v _q 
  have p20725 := n20725 _v _q h2351 h6600
  simp only [e2522, e4811, e4812, e4813, e4814, e8284, e8292, e8295] at *
  tauto
theorem n20727 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h6600 : (e6600 _v)) : (e7489 _v) := by
  have p8439 := n8439 _v _q h6600
  have p3130 := n3130 _v _q 
  have p20726 := n20726 _v _q h2351 h6600
  exact FloorCertificate.node_20727 (e2 _v) (e17 _v) (e45 _v) (e110 _v) p8439 p3130 p20726
theorem n20729 (_v : Vars) (_q : Query _v)  : (e20728 _v) := by
  by_contra hc
  change ¬ ((e2402 _v) ∨ (¬ (e2351 _v))) at hc
  have h2351 : (e2351 _v) := by
    tauto
  have h6600 : (e6600 _v) := by
    change (¬ (e2402 _v))
    tauto
  have p20727 := n20727 _v _q h2351 h6600
  exact p20727
theorem n20730 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) : (e2402 _v) := by
  have p20729 := n20729 _v _q 
  have p8464 := n8464 _v _q h2351
  simp only [e2351, e2402, e6575, e20728] at *
  tauto
theorem n20731 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) : (e3929 _v) := by
  have p14484 := n14484 _v _q 
  have p20730 := n20730 _v _q h2351
  simp only [e2402, e3919, e3920, e3921, e3922, e3923, e3929, e6600, e7422] at *
  tauto
theorem n20732 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) : (e3919 _v) := by
  have p14797 := n14797 _v _q 
  have p20731 := n20731 _v _q h2351
  simp only [e3919, e3920, e3921, e3922, e3923, e3924, e3929] at *
  tauto
theorem n20733 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h2522 : (e2522 _v)) (h5138 : (e5138 _v)) : (e7489 _v) := by
  have p16992 := n16992 _v _q 
  have p11487 := n11487 _v _q h5138
  have p20674 := n20674 _v _q h2351
  have p12831 := n12831 _v _q h2522
  have p5257 := n5257 _v _q 
  have p15932 := n15932 _v _q h2522
  have p15927 := n15927 _v _q h5138
  have p20732 := n20732 _v _q h2351
  have p8464 := n8464 _v _q h2351
  have p17067 := n17067 _v _q 
  have p17069 := n17069 _v _q 
  have p17080 := n17080 _v _q 
  have p17072 := n17072 _v _q 
  have p17083 := n17083 _v _q 
  have p17074 := n17074 _v _q 
  have p15125 := n15125 _v _q h2522
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
  have p17953 := n17953 _v _q 
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
  have p17131 := n17131 _v _q 
  have p17110 := n17110 _v _q 
  have p17053 := n17053 _v _q 
  have p15917 := n15917 _v _q h2351
  have p20096 := n20096 _v _q 
  have p17294 := n17294 _v _q 
  have p16943 := n16943 _v _q 
  have p17058 := n17058 _v _q 
  have p17064 := n17064 _v _q 
  have p13951 := n13951 _v _q 
  have p20651 := n20651 _v _q 
  exact FloorCertificate.node_20733 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2902 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) p16992 p11487 p20674 p12831 p5257 p15932 p15927 p20732 p8464 p17067 p17069 p17080 p17072 p17083 p17074 p15125 p20678 p20663 p17078 p20653 p17087 p17136 p15793 p17091 p17093 p20682 p17141 p17098 p17106 p17102 p17100 p19610 p15791 p17122 p17096 p15909 p15786 p17758 p17953 p15783 p15911 p15905 p20319 p17115 p17120 p17111 p17124 p17050 p16778 p17113 p17117 p20467 p17104 p17874 p17127 p15914 p20274 p20470 p17133 p17089 p19665 p20426 p17055 p17108 p20461 p20126 p17131 p17110 p17053 p15917 p20096 p17294 p16943 p17058 p17064 p13951 p20651
theorem n20735 (_v : Vars) (_q : Query _v)  : (e20734 _v) := by
  by_contra hc
  change ¬ ((e79 _v) ∨ (¬ (e2522 _v)) ∨ (¬ (e2351 _v))) at hc
  have h2351 : (e2351 _v) := by
    tauto
  have h2522 : (e2522 _v) := by
    tauto
  have h5138 : (e5138 _v) := by
    change (¬ (e79 _v))
    tauto
  have p20733 := n20733 _v _q h2351 h2522 h5138
  exact p20733
theorem n20736 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h2522 : (e2522 _v)) : (e79 _v) := by
  have p20735 := n20735 _v _q 
  have p12831 := n12831 _v _q h2522
  have p8464 := n8464 _v _q h2351
  simp only [e79, e2351, e2522, e6575, e6650, e20734] at *
  tauto
theorem n20737 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h2522 : (e2522 _v)) : (e5135 _v) := by
  have p14729 := n14729 _v _q 
  have p20736 := n20736 _v _q h2351 h2522
  simp only [e79, e89, e91, e94, e95, e5134, e5135, e5138, e5140] at *
  tauto
theorem n20738 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h2522 : (e2522 _v)) : (e91 _v) := by
  have p16235 := n16235 _v _q 
  have p20737 := n20737 _v _q h2351 h2522
  simp only [e89, e91, e94, e95, e5134, e5135, e7983] at *
  tauto
theorem n20739 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h2522 : (e2522 _v)) : (e214 _v) := by
  have p20674 := n20674 _v _q h2351
  have p12831 := n12831 _v _q h2522
  have p5257 := n5257 _v _q 
  have p20736 := n20736 _v _q h2351 h2522
  exact FloorCertificate.node_20739 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p20674 p12831 p5257 p20736
theorem n20740 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h2522 : (e2522 _v)) : (e5232 _v) := by
  have p14731 := n14731 _v _q 
  have p20739 := n20739 _v _q h2351 h2522
  simp only [e214, e225, e227, e230, e231, e5223, e5231, e5232, e5235] at *
  tauto
theorem n20741 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h2522 : (e2522 _v)) : (e225 _v) := by
  have p16653 := n16653 _v _q 
  have p20740 := n20740 _v _q h2351 h2522
  simp only [e225, e227, e230, e231, e5231, e5232, e5253] at *
  tauto
theorem n20742 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h2522 : (e2522 _v)) (h5195 : (e5195 _v)) : (e7489 _v) := by
  have p20738 := n20738 _v _q h2351 h2522
  have p20736 := n20736 _v _q h2351 h2522
  have p13951 := n13951 _v _q 
  have p20741 := n20741 _v _q h2351 h2522
  have p20674 := n20674 _v _q h2351
  have p12831 := n12831 _v _q h2522
  have p5257 := n5257 _v _q 
  have p15932 := n15932 _v _q h2522
  have p20732 := n20732 _v _q h2351
  have p8464 := n8464 _v _q h2351
  have p17067 := n17067 _v _q 
  have p17069 := n17069 _v _q 
  have p17080 := n17080 _v _q 
  have p17072 := n17072 _v _q 
  have p17083 := n17083 _v _q 
  have p17074 := n17074 _v _q 
  have p15125 := n15125 _v _q h2522
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
  have p17953 := n17953 _v _q 
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
  have p17131 := n17131 _v _q 
  have p17110 := n17110 _v _q 
  have p17053 := n17053 _v _q 
  have p15917 := n15917 _v _q h2351
  have p20096 := n20096 _v _q 
  have p17294 := n17294 _v _q 
  have p16943 := n16943 _v _q 
  have p17058 := n17058 _v _q 
  have p17064 := n17064 _v _q 
  have p8549 := n8549 _v _q h5195
  exact FloorCertificate.node_20742 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2902 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) p20738 p20736 p13951 p20741 p20674 p12831 p5257 p15932 p20732 p8464 p17067 p17069 p17080 p17072 p17083 p17074 p15125 p20678 p20663 p17078 p20653 p17087 p17136 p15793 p17091 p17093 p20682 p17141 p17098 p17106 p17102 p17100 p19610 p15791 p17122 p17096 p15909 p15786 p17758 p17953 p15783 p15911 p15905 p20319 p17115 p17120 p17111 p17124 p17050 p16778 p17113 p17117 p20467 p17104 p17874 p17127 p15914 p20274 p20470 p17133 p17089 p19665 p20426 p17055 p17108 p20461 p20126 p17131 p17110 p17053 p15917 p20096 p17294 p16943 p17058 p17064 p8549
theorem n20744 (_v : Vars) (_q : Query _v)  : (e20743 _v) := by
  by_contra hc
  change ¬ ((e196 _v) ∨ (¬ (e2522 _v)) ∨ (¬ (e2351 _v))) at hc
  have h2351 : (e2351 _v) := by
    tauto
  have h2522 : (e2522 _v) := by
    tauto
  have h5195 : (e5195 _v) := by
    change (¬ (e196 _v))
    tauto
  have p20742 := n20742 _v _q h2351 h2522 h5195
  exact p20742
theorem n20745 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h2522 : (e2522 _v)) : (e196 _v) := by
  have p20744 := n20744 _v _q 
  have p12831 := n12831 _v _q h2522
  have p8464 := n8464 _v _q h2351
  simp only [e196, e2351, e2522, e6575, e6650, e20743] at *
  tauto
theorem n20746 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h2522 : (e2522 _v)) : (e5203 _v) := by
  have p14730 := n14730 _v _q 
  have p20745 := n20745 _v _q h2351 h2522
  simp only [e191, e192, e193, e194, e196, e5193, e5195, e5203, e5206] at *
  tauto
theorem n20747 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h2522 : (e2522 _v)) : (e191 _v) := by
  have p16442 := n16442 _v _q 
  have p20746 := n20746 _v _q h2351 h2522
  simp only [e191, e192, e193, e194, e5193, e5194, e5203] at *
  tauto
theorem n20748 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h2522 : (e2522 _v)) : (e7489 _v) := by
  have p8464 := n8464 _v _q h2351
  have p5257 := n5257 _v _q 
  have p20674 := n20674 _v _q h2351
  have p331 := n331 _v _q 
  have p20736 := n20736 _v _q h2351 h2522
  have p12831 := n12831 _v _q h2522
  have p20747 := n20747 _v _q h2351 h2522
  have p20738 := n20738 _v _q h2351 h2522
  have p13951 := n13951 _v _q 
  have p20741 := n20741 _v _q h2351 h2522
  have p15932 := n15932 _v _q h2522
  have p20732 := n20732 _v _q h2351
  have p17067 := n17067 _v _q 
  have p17069 := n17069 _v _q 
  have p17080 := n17080 _v _q 
  have p17072 := n17072 _v _q 
  have p17083 := n17083 _v _q 
  have p17074 := n17074 _v _q 
  have p15125 := n15125 _v _q h2522
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
  have p17131 := n17131 _v _q 
  have p17110 := n17110 _v _q 
  have p17053 := n17053 _v _q 
  have p15917 := n15917 _v _q h2351
  have p20096 := n20096 _v _q 
  have p17294 := n17294 _v _q 
  have p16943 := n16943 _v _q 
  have p17058 := n17058 _v _q 
  have p17064 := n17064 _v _q 
  exact FloorCertificate.node_20748 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2902 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) p8464 p5257 p20674 p331 p20736 p12831 p20747 p20738 p13951 p20741 p15932 p20732 p17067 p17069 p17080 p17072 p17083 p17074 p15125 p20678 p20663 p17078 p20653 p17087 p17136 p15793 p17091 p17093 p20682 p17141 p17098 p17106 p17102 p17100 p19610 p15791 p17122 p17096 p15909 p15786 p17758 p15783 p15911 p15905 p20319 p17115 p17120 p17111 p17124 p17050 p16778 p17113 p17117 p20467 p17104 p17874 p17127 p15914 p20274 p20470 p17133 p17089 p19665 p20426 p17055 p17108 p20461 p20126 p17131 p17110 p17053 p15917 p20096 p17294 p16943 p17058 p17064
theorem n20750 (_v : Vars) (_q : Query _v)  : (e20749 _v) := by
  by_contra hc
  change ¬ ((¬ (e2522 _v)) ∨ (¬ (e2351 _v))) at hc
  have h2351 : (e2351 _v) := by
    tauto
  have h2522 : (e2522 _v) := by
    tauto
  have p20748 := n20748 _v _q h2351 h2522
  exact p20748
theorem n20751 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) : (e6650 _v) := by
  have p20750 := n20750 _v _q 
  have p8464 := n8464 _v _q h2351
  simp only [e2351, e2522, e6575, e6650, e20749] at *
  tauto
theorem n20752 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) : (e8292 _v) := by
  have p14657 := n14657 _v _q 
  have p20751 := n20751 _v _q h2351
  simp only [e2522, e4811, e4812, e4813, e4814, e6650, e8284, e8292, e8295] at *
  tauto
theorem n20753 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) : (e4813 _v) := by
  have p16259 := n16259 _v _q 
  have p20752 := n20752 _v _q h2351
  simp only [e4811, e4812, e4813, e4814, e8284, e8285, e8292] at *
  tauto
end
end Assembly
