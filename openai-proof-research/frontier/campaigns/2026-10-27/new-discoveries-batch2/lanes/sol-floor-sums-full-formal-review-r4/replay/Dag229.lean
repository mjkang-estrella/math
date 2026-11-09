import Dag228
import generated.th_lemma_29
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n20326 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) (h6423 : (e6423 _v)) : (e8317 _v) := by
  have p11541 := n11541 _v _q 
  have p15740 := n15740 _v _q h5362 h6423
  change (e8321 _v) ∨ (e8317 _v) at p11541
  change (¬ (e8321 _v)) at p15740
  rcases p11541 with hlit | hlit
  · exact (False.elim (p15740 hlit))
  · exact hlit
theorem n20327 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) (h6423 : (e6423 _v)) : (e7489 _v) := by
  have p17450 := n17450 _v _q 
  have p16627 := n16627 _v _q h6423
  have p20326 := n20326 _v _q h5362 h6423
  have p17953 := n17953 _v _q 
  have p7488 := n7488 _v _q h5362
  have p8452 := n8452 _v _q h6423
  have p17294 := n17294 _v _q 
  have p15728 := n15728 _v _q h5362
  have p17874 := n17874 _v _q 
  have p20323 := n20323 _v _q h5362
  have p15595 := n15595 _v _q h5362
  have p19728 := n19728 _v _q h5362
  have p15742 := n15742 _v _q h5362
  have p20126 := n20126 _v _q 
  have p15744 := n15744 _v _q h6423
  have p15733 := n15733 _v _q h5362
  have p15723 := n15723 _v _q h5362
  have p18120 := n18120 _v _q h5362
  have p19694 := n19694 _v _q h5362
  have p17758 := n17758 _v _q 
  have p19665 := n19665 _v _q 
  have p16628 := n16628 _v _q h6423
  have p15591 := n15591 _v _q h5362
  have p15736 := n15736 _v _q h5362
  have p15731 := n15731 _v _q h5362
  have p16992 := n16992 _v _q 
  have p19720 := n19720 _v _q h5362
  have p17252 := n17252 _v _q h5362
  have p16629 := n16629 _v _q h6423
  have p17253 := n17253 _v _q h5362
  have p20274 := n20274 _v _q 
  have p16630 := n16630 _v _q h6423
  have p15725 := n15725 _v _q h5362
  have p16396 := n16396 _v _q h6423
  have p19610 := n19610 _v _q 
  have p20096 := n20096 _v _q 
  have p19693 := n19693 _v _q h5362
  have p20286 := n20286 _v _q h5362
  change (e436 _v) ∨ (¬ (e7814 _v)) ∨ (¬ (e5208 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e8317 _v)) ∨ (¬ (e8045 _v)) ∨ (¬ (e3976 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e5145 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e5237 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e7749 _v)) ∨ (¬ (e5100 _v)) ∨ (¬ (e4724 _v)) ∨ (e1995 _v) ∨ (¬ (e3069 _v)) ∨ (¬ (e4264 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4101 _v)) ∨ (¬ (e4903 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e4398 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e4491 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e7714 _v)) at p17450
  change (¬ (e436 _v)) at p7488
  change (¬ (e1995 _v)) at p8452
  rcases p17450 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact (False.elim (p7488 hlit))
  · exact (False.elim (hlit p15733))
  · exact (False.elim (hlit p17953))
  · exact (False.elim (hlit p20323))
  · exact (False.elim (hlit p16627))
  · exact (False.elim (hlit p17294))
  · exact (False.elim (hlit p15728))
  · exact (False.elim (hlit p17874))
  · exact (False.elim (hlit p19728))
  · exact (False.elim (hlit p15595))
  · exact (False.elim (hlit p20326))
  · exact (False.elim (hlit p15742))
  · exact (False.elim (hlit p20126))
  · exact (False.elim (hlit p15744))
  · exact (False.elim (hlit p18120))
  · exact (False.elim (hlit p15723))
  · exact (False.elim (hlit p16992))
  · exact (False.elim (hlit p19694))
  · exact (False.elim (hlit p17758))
  · exact (False.elim (hlit p19665))
  · exact (False.elim (hlit p16628))
  · exact (False.elim (hlit p15591))
  · exact (False.elim (hlit p15736))
  · exact (False.elim (hlit p15731))
  · exact (False.elim (p8452 hlit))
  · exact (False.elim (hlit p19720))
  · exact (False.elim (hlit p17252))
  · exact (False.elim (hlit p16629))
  · exact (False.elim (hlit p17253))
  · exact (False.elim (hlit p20274))
  · exact (False.elim (hlit p16630))
  · exact (False.elim (hlit p15725))
  · exact (False.elim (hlit p16396))
  · exact (False.elim (hlit p19610))
  · exact (False.elim (hlit p20096))
  · exact (False.elim (hlit p19693))
  · exact (False.elim (hlit p20286))
theorem n20329 (_v : Vars) (_q : Query _v)  : (e20328 _v) := by
  by_contra hc
  change ¬ ((e1995 _v) ∨ (e436 _v)) at hc
  have h5362 : (e5362 _v) := (fun hn => hc (Or.inr hn))
  have h6423 : (e6423 _v) := (fun hn => hc (Or.inl hn))
  have p20327 := n20327 _v _q h5362 h6423
  exact p20327
theorem n20330 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h4679 : (e4679 _v)) (h5362 : (e5362 _v)) (h7714 : (e7714 _v)) : (e6600 _v) := by
  have p20325 := n20325 _v _q 
  have p17070 := n17070 _v _q h4679
  have p17247 := n17247 _v _q h7714
  have p8464 := n8464 _v _q h2351
  have p7488 := n7488 _v _q h5362
  change (¬ (e2402 _v)) ∨ (¬ (e4679 _v)) ∨ (¬ (e7714 _v)) ∨ (¬ (e2351 _v)) ∨ (e436 _v) at p20325
  change (¬ (e436 _v)) at p7488
  rcases p20325 with hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p17070))
  · exact (False.elim (hlit p17247))
  · exact (False.elim (hlit p8464))
  · exact (False.elim (p7488 hlit))
theorem n20331 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h4679 : (e4679 _v)) (h5362 : (e5362 _v)) (h7714 : (e7714 _v)) : (e7416 _v) := by
  have p14534 := n14534 _v _q 
  have p20330 := n20330 _v _q h2351 h4679 h5362 h7714
  change (e2402 _v) ∨ (¬ (e7415 _v)) at p14534
  change (¬ (e2402 _v)) at p20330
  rcases p14534 with hlit | hlit
  · exact (False.elim (p20330 hlit))
  · exact hlit
theorem n20332 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) : (e1995 _v) := by
  have p20329 := n20329 _v _q 
  have p7488 := n7488 _v _q h5362
  change (e1995 _v) ∨ (e436 _v) at p20329
  change (¬ (e436 _v)) at p7488
  rcases p20329 with hlit | hlit
  · exact hlit
  · exact (False.elim (p7488 hlit))
theorem n20333 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) : (e4575 _v) := by
  have p14696 := n14696 _v _q 
  have p20332 := n20332 _v _q h5362
  change (¬ (e1995 _v)) ∨ (¬ (e4574 _v)) at p14696
  rcases p14696 with hlit | hlit
  · exact (False.elim (hlit p20332))
  · exact hlit
theorem n20334 (_v : Vars) (_q : Query _v) (h6454 : (e6454 _v)) : (e6480 _v) := by
  have p8478 := n8478 _v _q 
  have p8430 := n8430 _v _q h6454
  change (e2061 _v) ∨ (¬ (e2125 _v)) at p8478
  change (¬ (e2061 _v)) at p8430
  rcases p8478 with hlit | hlit
  · exact (False.elim (p8430 hlit))
  · exact hlit
theorem n20335 (_v : Vars) (_q : Query _v) (h4156 : (e4156 _v)) (h5362 : (e5362 _v)) (h6454 : (e6454 _v)) : (e4676 _v) := by
  have p17452 := n17452 _v _q 
  have p15762 := n15762 _v _q h6454
  have p7488 := n7488 _v _q h5362
  have p15736 := n15736 _v _q h5362
  have p15731 := n15731 _v _q h5362
  have p15725 := n15725 _v _q h5362
  have p20332 := n20332 _v _q h5362
  have p15595 := n15595 _v _q h5362
  have p19610 := n19610 _v _q 
  have p15742 := n15742 _v _q h5362
  have p20126 := n20126 _v _q 
  have p20096 := n20096 _v _q 
  have p20334 := n20334 _v _q h6454
  have p19693 := n19693 _v _q h5362
  have p19728 := n19728 _v _q h5362
  have p15764 := n15764 _v _q h6454
  have p15733 := n15733 _v _q h5362
  have p15591 := n15591 _v _q h5362
  have p20323 := n20323 _v _q h5362
  have p15728 := n15728 _v _q h5362
  have p16631 := n16631 _v _q h6454
  have p17294 := n17294 _v _q 
  have p17874 := n17874 _v _q 
  have p4985 := n4985 _v _q h4156
  have p20274 := n20274 _v _q 
  have p15768 := n15768 _v _q h5362 h6454
  have p19694 := n19694 _v _q h5362
  have p17953 := n17953 _v _q 
  have p17758 := n17758 _v _q 
  have p19665 := n19665 _v _q 
  have p16632 := n16632 _v _q h6454
  have p19720 := n19720 _v _q h5362
  have p18120 := n18120 _v _q h5362
  change (e436 _v) ∨ (e2125 _v) ∨ (¬ (e5100 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e4724 _v)) ∨ (¬ (e4398 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e8045 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e3976 _v)) ∨ (¬ (e4491 _v)) ∨ (¬ (e8317 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e7814 _v)) ∨ (¬ (e7749 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e4903 _v)) ∨ (¬ (e5145 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e5208 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e1995 _v)) at p17452
  change (¬ (e436 _v)) at p7488
  change (¬ (e2125 _v)) at p20334
  rcases p17452 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact (False.elim (p7488 hlit))
  · exact (False.elim (p20334 hlit))
  · exact (False.elim (hlit p15736))
  · exact (False.elim (hlit p15762))
  · exact (False.elim (hlit p15731))
  · exact (False.elim (hlit p15725))
  · exact (False.elim (hlit p15764))
  · exact (False.elim (hlit p15742))
  · exact (False.elim (hlit p19610))
  · exact (False.elim (hlit p15595))
  · exact (False.elim (hlit p20126))
  · exact (False.elim (hlit p20096))
  · exact (False.elim (hlit p15768))
  · exact (False.elim (hlit p19693))
  · exact (False.elim (hlit p19728))
  · exact (False.elim (hlit p16631))
  · exact (False.elim (hlit p15733))
  · exact (False.elim (hlit p15591))
  · exact (False.elim (hlit p20323))
  · exact (False.elim (hlit p15728))
  · exact hlit
  · exact (False.elim (hlit p17294))
  · exact (False.elim (hlit p17874))
  · exact (False.elim (hlit p4985))
  · exact (False.elim (hlit p20274))
  · exact (False.elim (hlit p18120))
  · exact (False.elim (hlit p19694))
  · exact (False.elim (hlit p17953))
  · exact (False.elim (hlit p17758))
  · exact (False.elim (hlit p19665))
  · exact (False.elim (hlit p16632))
  · exact (False.elim (hlit p19720))
  · exact (False.elim (hlit p20332))
theorem n20336 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h4679 : (e4679 _v)) (h5362 : (e5362 _v)) (h7714 : (e7714 _v)) : (e3937 _v) := by
  have p15012 := n15012 _v _q 
  have p20331 := n20331 _v _q h2351 h4679 h5362 h7714
  change (e7415 _v) ∨ (e3937 _v) at p15012
  change (¬ (e7415 _v)) at p20331
  rcases p15012 with hlit | hlit
  · exact (False.elim (p20331 hlit))
  · exact hlit
theorem n20337 (_v : Vars) (_q : Query _v) (h4156 : (e4156 _v)) (h5362 : (e5362 _v)) (h6454 : (e6454 _v)) : (e8166 _v) := by
  have p15965 := n15965 _v _q 
  have p20335 := n20335 _v _q h4156 h5362 h6454
  change (e8166 _v) ∨ (e4675 _v) at p15965
  change (¬ (e4675 _v)) at p20335
  rcases p15965 with hlit | hlit
  · exact hlit
  · exact (False.elim (p20335 hlit))
theorem n20338 (_v : Vars) (_q : Query _v) (h4156 : (e4156 _v)) (h5362 : (e5362 _v)) (h6454 : (e6454 _v)) : (e2242 _v) := by
  have p14634 := n14634 _v _q 
  have p20337 := n20337 _v _q h4156 h5362 h6454
  change (e2242 _v) ∨ (¬ (e8166 _v)) at p14634
  rcases p14634 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p20337))
theorem n20339 (_v : Vars) (_q : Query _v) (h4156 : (e4156 _v)) (h5362 : (e5362 _v)) (h6454 : (e6454 _v)) : (e7489 _v) := by
  have p4016 := n4016 _v _q 
  have p5255 := n5255 _v _q 
  have p8430 := n8430 _v _q h6454
  have p20338 := n20338 _v _q h4156 h5362 h6454
  exact FloorCertificate.node_20339 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e110 _v) p4016 p5255 p8430 p20338
theorem n20340 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h4679 : (e4679 _v)) (h5362 : (e5362 _v)) (h7714 : (e7714 _v)) : (e7489 _v) := by
  have p17953 := n17953 _v _q 
  have p15742 := n15742 _v _q h5362
  have p19694 := n19694 _v _q h5362
  have p17070 := n17070 _v _q h4679
  have p16778 := n16778 _v _q 
  have p19779 := n19779 _v _q h2351 h5362
  have p17247 := n17247 _v _q h7714
  have p19766 := n19766 _v _q h5362
  have p17111 := n17111 _v _q 
  have p20294 := n20294 _v _q h5362
  have p17252 := n17252 _v _q h5362
  have p19720 := n19720 _v _q h5362
  have p17874 := n17874 _v _q 
  have p17127 := n17127 _v _q 
  have p15595 := n15595 _v _q h5362
  have p20274 := n20274 _v _q 
  have p18120 := n18120 _v _q h5362
  have p17253 := n17253 _v _q h5362
  have p17050 := n17050 _v _q 
  have p15783 := n15783 _v _q h2351
  have p17133 := n17133 _v _q 
  have p17089 := n17089 _v _q 
  have p19665 := n19665 _v _q 
  have p16992 := n16992 _v _q 
  have p17055 := n17055 _v _q 
  have p15786 := n15786 _v _q h2351
  have p20319 := n20319 _v _q h2351
  have p17108 := n17108 _v _q 
  have p15791 := n15791 _v _q h2351
  have p15793 := n15793 _v _q h2351
  have p20126 := n20126 _v _q 
  have p15087 := n15087 _v _q h5362
  have p17131 := n17131 _v _q 
  have p17110 := n17110 _v _q 
  have p17053 := n17053 _v _q 
  have p15723 := n15723 _v _q h5362
  have p20096 := n20096 _v _q 
  have p17294 := n17294 _v _q 
  have p20336 := n20336 _v _q h2351 h4679 h5362 h7714
  have p15725 := n15725 _v _q h5362
  have p17058 := n17058 _v _q 
  have p17064 := n17064 _v _q 
  have p17067 := n17067 _v _q 
  have p17069 := n17069 _v _q 
  have p17072 := n17072 _v _q 
  have p17136 := n17136 _v _q 
  have p19728 := n19728 _v _q h5362
  have p17078 := n17078 _v _q 
  have p17080 := n17080 _v _q 
  have p17083 := n17083 _v _q 
  have p17074 := n17074 _v _q 
  have p17087 := n17087 _v _q 
  have p17758 := n17758 _v _q 
  have p17091 := n17091 _v _q 
  have p17093 := n17093 _v _q 
  have p15728 := n15728 _v _q h5362
  have p17141 := n17141 _v _q 
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p17100 := n17100 _v _q 
  have p17102 := n17102 _v _q 
  have p19610 := n19610 _v _q 
  have p17104 := n17104 _v _q 
  have p17096 := n17096 _v _q 
  have p296 := n296 _v _q 
  have p17113 := n17113 _v _q 
  have p15731 := n15731 _v _q h5362
  have p17122 := n17122 _v _q 
  have p17117 := n17117 _v _q 
  have p17124 := n17124 _v _q 
  have p17115 := n17115 _v _q 
  have p17120 := n17120 _v _q 
  have p19687 := n19687 _v _q h2351 h5362
  have p17147 := n17147 _v _q 
  exact FloorCertificate.node_20340 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2883 _v) (e2902 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e4541 _v) (e4808 _v) p17953 p15742 p19694 p17070 p16778 p19779 p17247 p19766 p17111 p20294 p17252 p19720 p17874 p17127 p15595 p20274 p18120 p17253 p17050 p15783 p17133 p17089 p19665 p16992 p17055 p15786 p20319 p17108 p15791 p15793 p20126 p15087 p17131 p17110 p17053 p15723 p20096 p17294 p20336 p15725 p17058 p17064 p17067 p17069 p17072 p17136 p19728 p17078 p17080 p17083 p17074 p17087 p17758 p17091 p17093 p15728 p17141 p17098 p17106 p17100 p17102 p19610 p17104 p17096 p296 p17113 p15731 p17122 p17117 p17124 p17115 p17120 p19687 p17147
theorem n20342 (_v : Vars) (_q : Query _v)  : (e20341 _v) := by
  by_contra hc
  change ¬ ((e2061 _v) ∨ (e436 _v) ∨ (¬ (e4156 _v))) at hc
  have h4156 : (e4156 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr hn)))
  have h5362 : (e5362 _v) := (fun hn => hc (Or.inr (Or.inl hn)))
  have h6454 : (e6454 _v) := (fun hn => hc (Or.inl hn))
  have p20339 := n20339 _v _q h4156 h5362 h6454
  exact p20339
theorem n20343 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) (h6575 : (e6575 _v)) : (e2061 _v) := by
  have p20342 := n20342 _v _q 
  have p15771 := n15771 _v _q h6575
  have p7488 := n7488 _v _q h5362
  change (e2061 _v) ∨ (e436 _v) ∨ (¬ (e4156 _v)) at p20342
  change (¬ (e436 _v)) at p7488
  rcases p20342 with hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (p7488 hlit))
  · exact (False.elim (hlit p15771))
theorem n20344 (_v : Vars) (_q : Query _v) (h4156 : (e4156 _v)) (h5362 : (e5362 _v)) : (e2061 _v) := by
  have p20342 := n20342 _v _q 
  have p4985 := n4985 _v _q h4156
  have p7488 := n7488 _v _q h5362
  change (e2061 _v) ∨ (e436 _v) ∨ (¬ (e4156 _v)) at p20342
  change (¬ (e436 _v)) at p7488
  rcases p20342 with hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (p7488 hlit))
  · exact (False.elim (hlit p4985))
theorem n20345 (_v : Vars) (_q : Query _v) (h4156 : (e4156 _v)) (h5362 : (e5362 _v)) : (e4447 _v) := by
  have p14688 := n14688 _v _q 
  have p20344 := n20344 _v _q h4156 h5362
  change (¬ (e2061 _v)) ∨ (¬ (e4446 _v)) at p14688
  rcases p14688 with hlit | hlit
  · exact (False.elim (hlit p20344))
  · exact hlit
theorem n20347 (_v : Vars) (_q : Query _v)  : (e20346 _v) := by
  by_contra hc
  change ¬ ((¬ (e4679 _v)) ∨ (¬ (e7714 _v)) ∨ (¬ (e2351 _v)) ∨ (e436 _v)) at hc
  have h2351 : (e2351 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4679 : (e4679 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h5362 : (e5362 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr hn))))
  have h7714 : (e7714 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have p20340 := n20340 _v _q h2351 h4679 h5362 h7714
  exact p20340
theorem n20348 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) (h6575 : (e6575 _v)) : (e8310 _v) := by
  have p20343 := n20343 _v _q h5362 h6575
  have p7488 := n7488 _v _q h5362
  have p11413 := n11413 _v _q h6575
  exact FloorCertificate.node_20348 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p20343 p7488 p11413
theorem n20349 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) (h6575 : (e6575 _v)) : (e8322 _v) := by
  have p15218 := n15218 _v _q 
  have p20348 := n20348 _v _q h5362 h6575
  change (e2529 _v) ∨ (¬ (e8321 _v)) at p15218
  change (¬ (e2529 _v)) at p20348
  rcases p15218 with hlit | hlit
  · exact (False.elim (p20348 hlit))
  · exact hlit
theorem n20350 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) (h6575 : (e6575 _v)) : (e4447 _v) := by
  have p14688 := n14688 _v _q 
  have p20343 := n20343 _v _q h5362 h6575
  change (¬ (e2061 _v)) ∨ (¬ (e4446 _v)) at p14688
  rcases p14688 with hlit | hlit
  · exact (False.elim (hlit p20343))
  · exact hlit
theorem n20351 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) (h6575 : (e6575 _v)) : (e4439 _v) := by
  have p14925 := n14925 _v _q 
  have p20350 := n20350 _v _q h5362 h6575
  change (e4446 _v) ∨ (e4439 _v) at p14925
  change (¬ (e4446 _v)) at p20350
  rcases p14925 with hlit | hlit
  · exact (False.elim (p20350 hlit))
  · exact hlit
theorem n20352 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) : (e4567 _v) := by
  have p8485 := n8485 _v _q 
  have p20333 := n20333 _v _q h5362
  change (e4574 _v) ∨ (e4567 _v) at p8485
  change (¬ (e4574 _v)) at p20333
  rcases p8485 with hlit | hlit
  · exact (False.elim (p20333 hlit))
  · exact hlit
theorem n20353 (_v : Vars) (_q : Query _v) (h4156 : (e4156 _v)) (h5362 : (e5362 _v)) : (e4439 _v) := by
  have p14925 := n14925 _v _q 
  have p20345 := n20345 _v _q h4156 h5362
  change (e4446 _v) ∨ (e4439 _v) at p14925
  change (¬ (e4446 _v)) at p20345
  rcases p14925 with hlit | hlit
  · exact (False.elim (p20345 hlit))
  · exact hlit
theorem n20354 (_v : Vars) (_q : Query _v) (h2242 : (e2242 _v)) (h3158 : (e3158 _v)) (h4156 : (e4156 _v)) (h5362 : (e5362 _v)) (h6549 : (e6549 _v)) (h8317 : (e8317 _v)) : (e3920 _v) := by
  have p20318 := n20318 _v _q h5362
  have p8544 := n8544 _v _q h6549
  have p15775 := n15775 _v _q h2242
  have p16858 := n16858 _v _q 
  have p16885 := n16885 _v _q h3158
  have p13951 := n13951 _v _q 
  have p15778 := n15778 _v _q h6549
  have p20352 := n20352 _v _q h5362
  have p19693 := n19693 _v _q h5362
  have p15733 := n15733 _v _q h5362
  have p17120 := n17120 _v _q 
  have p17953 := n17953 _v _q 
  have p17256 := n17256 _v _q 
  have p19694 := n19694 _v _q h5362
  have p16578 := n16578 _v _q 
  have p16778 := n16778 _v _q 
  have p15591 := n15591 _v _q h5362
  have p20286 := n20286 _v _q h5362
  have p17174 := n17174 _v _q h8317
  have p17111 := n17111 _v _q 
  have p15742 := n15742 _v _q h5362
  have p17252 := n17252 _v _q h5362
  have p19720 := n19720 _v _q h5362
  have p17874 := n17874 _v _q 
  have p17127 := n17127 _v _q 
  have p15595 := n15595 _v _q h5362
  have p20274 := n20274 _v _q 
  have p18120 := n18120 _v _q h5362
  have p17253 := n17253 _v _q h5362
  have p17050 := n17050 _v _q 
  have p17009 := n17009 _v _q 
  have p17133 := n17133 _v _q 
  have p17089 := n17089 _v _q 
  have p19665 := n19665 _v _q 
  have p16992 := n16992 _v _q 
  have p17055 := n17055 _v _q 
  have p17108 := n17108 _v _q 
  have p7488 := n7488 _v _q h5362
  have p4985 := n4985 _v _q h4156
  have p20126 := n20126 _v _q 
  have p15087 := n15087 _v _q h5362
  have p17131 := n17131 _v _q 
  have p17110 := n17110 _v _q 
  have p17053 := n17053 _v _q 
  have p15723 := n15723 _v _q h5362
  have p20096 := n20096 _v _q 
  have p17294 := n17294 _v _q 
  have p15725 := n15725 _v _q h5362
  have p17058 := n17058 _v _q 
  have p17064 := n17064 _v _q 
  have p17067 := n17067 _v _q 
  have p17069 := n17069 _v _q 
  have p17072 := n17072 _v _q 
  have p17136 := n17136 _v _q 
  have p19728 := n19728 _v _q h5362
  have p17078 := n17078 _v _q 
  have p17080 := n17080 _v _q 
  have p17083 := n17083 _v _q 
  have p17074 := n17074 _v _q 
  have p17087 := n17087 _v _q 
  have p17758 := n17758 _v _q 
  have p17091 := n17091 _v _q 
  have p17093 := n17093 _v _q 
  have p15728 := n15728 _v _q h5362
  have p17141 := n17141 _v _q 
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p17100 := n17100 _v _q 
  have p17102 := n17102 _v _q 
  have p19610 := n19610 _v _q 
  have p17104 := n17104 _v _q 
  have p17096 := n17096 _v _q 
  have p17113 := n17113 _v _q 
  have p15731 := n15731 _v _q h5362
  have p17122 := n17122 _v _q 
  have p17117 := n17117 _v _q 
  have p17124 := n17124 _v _q 
  have p17115 := n17115 _v _q 
  have p20353 := n20353 _v _q h4156 h5362
  have p20323 := n20323 _v _q h5362
  have p5255 := n5255 _v _q 
  have p8553 := n8553 _v _q h2242
  exact FloorCertificate.node_20354 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2863 _v) (e2877 _v) (e2902 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p20318 p8544 p15775 p16858 p16885 p13951 p15778 p20352 p19693 p15733 p17120 p17953 p17256 p19694 p16578 p16778 p15591 p20286 p17174 p17111 p15742 p17252 p19720 p17874 p17127 p15595 p20274 p18120 p17253 p17050 p17009 p17133 p17089 p19665 p16992 p17055 p17108 p7488 p4985 p20126 p15087 p17131 p17110 p17053 p15723 p20096 p17294 p15725 p17058 p17064 p17067 p17069 p17072 p17136 p19728 p17078 p17080 p17083 p17074 p17087 p17758 p17091 p17093 p15728 p17141 p17098 p17106 p17100 p17102 p19610 p17104 p17096 p17113 p15731 p17122 p17117 p17124 p17115 p20353 p20323 p5255 p8553
theorem n20355 (_v : Vars) (_q : Query _v) (h2242 : (e2242 _v)) (h3158 : (e3158 _v)) (h4156 : (e4156 _v)) (h5362 : (e5362 _v)) (h6549 : (e6549 _v)) (h8317 : (e8317 _v)) : (e3942 _v) := by
  have p16885 := n16885 _v _q h3158
  have p16578 := n16578 _v _q 
  have p15775 := n15775 _v _q h2242
  have p13951 := n13951 _v _q 
  have p17147 := n17147 _v _q 
  have p20318 := n20318 _v _q h5362
  have p15778 := n15778 _v _q h6549
  have p20352 := n20352 _v _q h5362
  have p19693 := n19693 _v _q h5362
  have p15733 := n15733 _v _q h5362
  have p17120 := n17120 _v _q 
  have p17953 := n17953 _v _q 
  have p17256 := n17256 _v _q 
  have p19694 := n19694 _v _q h5362
  have p16858 := n16858 _v _q 
  have p16778 := n16778 _v _q 
  have p15591 := n15591 _v _q h5362
  have p20286 := n20286 _v _q h5362
  have p17174 := n17174 _v _q h8317
  have p17111 := n17111 _v _q 
  have p15742 := n15742 _v _q h5362
  have p17252 := n17252 _v _q h5362
  have p19720 := n19720 _v _q h5362
  have p17874 := n17874 _v _q 
  have p17127 := n17127 _v _q 
  have p15595 := n15595 _v _q h5362
  have p20274 := n20274 _v _q 
  have p18120 := n18120 _v _q h5362
  have p17253 := n17253 _v _q h5362
  have p17050 := n17050 _v _q 
  have p17009 := n17009 _v _q 
  have p17133 := n17133 _v _q 
  have p17089 := n17089 _v _q 
  have p19665 := n19665 _v _q 
  have p16992 := n16992 _v _q 
  have p17055 := n17055 _v _q 
  have p17108 := n17108 _v _q 
  have p8544 := n8544 _v _q h6549
  have p4985 := n4985 _v _q h4156
  have p20126 := n20126 _v _q 
  have p15087 := n15087 _v _q h5362
  have p17131 := n17131 _v _q 
  have p17110 := n17110 _v _q 
  have p17053 := n17053 _v _q 
  have p15723 := n15723 _v _q h5362
  have p20096 := n20096 _v _q 
  have p17294 := n17294 _v _q 
  have p15725 := n15725 _v _q h5362
  have p17058 := n17058 _v _q 
  have p17064 := n17064 _v _q 
  have p17067 := n17067 _v _q 
  have p17069 := n17069 _v _q 
  have p17072 := n17072 _v _q 
  have p17136 := n17136 _v _q 
  have p19728 := n19728 _v _q h5362
  have p17078 := n17078 _v _q 
  have p17080 := n17080 _v _q 
  have p17083 := n17083 _v _q 
  have p17074 := n17074 _v _q 
  have p17087 := n17087 _v _q 
  have p17758 := n17758 _v _q 
  have p17091 := n17091 _v _q 
  have p17093 := n17093 _v _q 
  have p15728 := n15728 _v _q h5362
  have p17141 := n17141 _v _q 
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p17100 := n17100 _v _q 
  have p17102 := n17102 _v _q 
  have p19610 := n19610 _v _q 
  have p17104 := n17104 _v _q 
  have p17096 := n17096 _v _q 
  have p17113 := n17113 _v _q 
  have p15731 := n15731 _v _q h5362
  have p17122 := n17122 _v _q 
  have p17117 := n17117 _v _q 
  have p17124 := n17124 _v _q 
  have p17115 := n17115 _v _q 
  have p20353 := n20353 _v _q h4156 h5362
  have p20323 := n20323 _v _q h5362
  have p7488 := n7488 _v _q h5362
  have p5255 := n5255 _v _q 
  exact FloorCertificate.node_20355 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2863 _v) (e2877 _v) (e2883 _v) (e2902 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p16885 p16578 p15775 p13951 p17147 p20318 p15778 p20352 p19693 p15733 p17120 p17953 p17256 p19694 p16858 p16778 p15591 p20286 p17174 p17111 p15742 p17252 p19720 p17874 p17127 p15595 p20274 p18120 p17253 p17050 p17009 p17133 p17089 p19665 p16992 p17055 p17108 p8544 p4985 p20126 p15087 p17131 p17110 p17053 p15723 p20096 p17294 p15725 p17058 p17064 p17067 p17069 p17072 p17136 p19728 p17078 p17080 p17083 p17074 p17087 p17758 p17091 p17093 p15728 p17141 p17098 p17106 p17100 p17102 p19610 p17104 p17096 p17113 p15731 p17122 p17117 p17124 p17115 p20353 p20323 p7488 p5255
theorem n20356 (_v : Vars) (_q : Query _v) (h2296 : (e2296 _v)) (h6575 : (e6575 _v)) : (e3158 _v) := by
  have p15126 := n15126 _v _q 
  have p15751 := n15751 _v _q h2296 h6575
  change (e3162 _v) ∨ (e3158 _v) at p15126
  change (¬ (e3162 _v)) at p15751
  rcases p15126 with hlit | hlit
  · exact (False.elim (p15751 hlit))
  · exact hlit
theorem n20357 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) (h6575 : (e6575 _v)) : (e8317 _v) := by
  have p11541 := n11541 _v _q 
  have p20349 := n20349 _v _q h5362 h6575
  change (e8321 _v) ∨ (e8317 _v) at p11541
  change (¬ (e8321 _v)) at p20349
  rcases p11541 with hlit | hlit
  · exact (False.elim (p20349 hlit))
  · exact hlit
theorem n20358 (_v : Vars) (_q : Query _v) (h2296 : (e2296 _v)) (h5362 : (e5362 _v)) (h6575 : (e6575 _v)) : (e3942 _v) := by
  have p13951 := n13951 _v _q 
  have p17147 := n17147 _v _q 
  have p20318 := n20318 _v _q h5362
  have p5257 := n5257 _v _q 
  have p8583 := n8583 _v _q h2296
  have p20352 := n20352 _v _q h5362
  have p19693 := n19693 _v _q h5362
  have p20356 := n20356 _v _q h2296 h6575
  have p17120 := n17120 _v _q 
  have p17953 := n17953 _v _q 
  have p17256 := n17256 _v _q 
  have p19694 := n19694 _v _q h5362
  have p15754 := n15754 _v _q h2296
  have p16778 := n16778 _v _q 
  have p15591 := n15591 _v _q h5362
  have p20286 := n20286 _v _q h5362
  have p20357 := n20357 _v _q h5362 h6575
  have p17111 := n17111 _v _q 
  have p15742 := n15742 _v _q h5362
  have p17252 := n17252 _v _q h5362
  have p19720 := n19720 _v _q h5362
  have p17874 := n17874 _v _q 
  have p17127 := n17127 _v _q 
  have p15595 := n15595 _v _q h5362
  have p20274 := n20274 _v _q 
  have p18120 := n18120 _v _q h5362
  have p17253 := n17253 _v _q h5362
  have p17050 := n17050 _v _q 
  have p17009 := n17009 _v _q 
  have p17133 := n17133 _v _q 
  have p17089 := n17089 _v _q 
  have p19665 := n19665 _v _q 
  have p16992 := n16992 _v _q 
  have p17055 := n17055 _v _q 
  have p17108 := n17108 _v _q 
  have p15100 := n15100 _v _q h2296
  have p15771 := n15771 _v _q h6575
  have p20126 := n20126 _v _q 
  have p15087 := n15087 _v _q h5362
  have p17131 := n17131 _v _q 
  have p17110 := n17110 _v _q 
  have p17053 := n17053 _v _q 
  have p15723 := n15723 _v _q h5362
  have p20096 := n20096 _v _q 
  have p17294 := n17294 _v _q 
  have p15725 := n15725 _v _q h5362
  have p17058 := n17058 _v _q 
  have p17064 := n17064 _v _q 
  have p17067 := n17067 _v _q 
  have p17069 := n17069 _v _q 
  have p17072 := n17072 _v _q 
  have p17136 := n17136 _v _q 
  have p19728 := n19728 _v _q h5362
  have p17078 := n17078 _v _q 
  have p17080 := n17080 _v _q 
  have p17083 := n17083 _v _q 
  have p17074 := n17074 _v _q 
  have p17087 := n17087 _v _q 
  have p17758 := n17758 _v _q 
  have p17091 := n17091 _v _q 
  have p17093 := n17093 _v _q 
  have p15728 := n15728 _v _q h5362
  have p17141 := n17141 _v _q 
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p17100 := n17100 _v _q 
  have p17102 := n17102 _v _q 
  have p19610 := n19610 _v _q 
  have p17104 := n17104 _v _q 
  have p17096 := n17096 _v _q 
  have p17113 := n17113 _v _q 
  have p15731 := n15731 _v _q h5362
  have p17122 := n17122 _v _q 
  have p17117 := n17117 _v _q 
  have p17124 := n17124 _v _q 
  have p17115 := n17115 _v _q 
  have p20351 := n20351 _v _q h5362 h6575
  have p5255 := n5255 _v _q 
  have p7488 := n7488 _v _q h5362
  have p11413 := n11413 _v _q h6575
  have p20323 := n20323 _v _q h5362
  exact FloorCertificate.node_20358 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2883 _v) (e2902 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e4215 _v) (e4541 _v) (e4808 _v) p13951 p17147 p20318 p5257 p8583 p20352 p19693 p20356 p17120 p17953 p17256 p19694 p15754 p16778 p15591 p20286 p20357 p17111 p15742 p17252 p19720 p17874 p17127 p15595 p20274 p18120 p17253 p17050 p17009 p17133 p17089 p19665 p16992 p17055 p17108 p15100 p15771 p20126 p15087 p17131 p17110 p17053 p15723 p20096 p17294 p15725 p17058 p17064 p17067 p17069 p17072 p17136 p19728 p17078 p17080 p17083 p17074 p17087 p17758 p17091 p17093 p15728 p17141 p17098 p17106 p17100 p17102 p19610 p17104 p17096 p17113 p15731 p17122 p17117 p17124 p17115 p20351 p5255 p7488 p11413 p20323
theorem n20359 (_v : Vars) (_q : Query _v) (h2296 : (e2296 _v)) (h5362 : (e5362 _v)) (h6575 : (e6575 _v)) : (e3920 _v) := by
  have p13951 := n13951 _v _q 
  have p5257 := n5257 _v _q 
  have p20352 := n20352 _v _q h5362
  have p19693 := n19693 _v _q h5362
  have p15100 := n15100 _v _q h2296
  have p20356 := n20356 _v _q h2296 h6575
  have p17120 := n17120 _v _q 
  have p17953 := n17953 _v _q 
  have p17256 := n17256 _v _q 
  have p19694 := n19694 _v _q h5362
  have p15754 := n15754 _v _q h2296
  have p16778 := n16778 _v _q 
  have p15591 := n15591 _v _q h5362
  have p20286 := n20286 _v _q h5362
  have p20357 := n20357 _v _q h5362 h6575
  have p17111 := n17111 _v _q 
  have p20318 := n20318 _v _q h5362
  have p17252 := n17252 _v _q h5362
  have p19720 := n19720 _v _q h5362
  have p17874 := n17874 _v _q 
  have p17127 := n17127 _v _q 
  have p15595 := n15595 _v _q h5362
  have p20274 := n20274 _v _q 
  have p18120 := n18120 _v _q h5362
  have p17253 := n17253 _v _q h5362
  have p17050 := n17050 _v _q 
  have p17009 := n17009 _v _q 
  have p17133 := n17133 _v _q 
  have p17089 := n17089 _v _q 
  have p19665 := n19665 _v _q 
  have p16992 := n16992 _v _q 
  have p17055 := n17055 _v _q 
  have p17108 := n17108 _v _q 
  have p8583 := n8583 _v _q h2296
  have p15771 := n15771 _v _q h6575
  have p20126 := n20126 _v _q 
  have p15087 := n15087 _v _q h5362
  have p17131 := n17131 _v _q 
  have p17110 := n17110 _v _q 
  have p17053 := n17053 _v _q 
  have p15723 := n15723 _v _q h5362
  have p20096 := n20096 _v _q 
  have p17294 := n17294 _v _q 
  have p15725 := n15725 _v _q h5362
  have p17058 := n17058 _v _q 
  have p17064 := n17064 _v _q 
  have p17067 := n17067 _v _q 
  have p17069 := n17069 _v _q 
  have p17072 := n17072 _v _q 
  have p17136 := n17136 _v _q 
  have p19728 := n19728 _v _q h5362
  have p17078 := n17078 _v _q 
  have p17080 := n17080 _v _q 
  have p17083 := n17083 _v _q 
  have p17074 := n17074 _v _q 
  have p17087 := n17087 _v _q 
  have p17758 := n17758 _v _q 
  have p17091 := n17091 _v _q 
  have p17093 := n17093 _v _q 
  have p15728 := n15728 _v _q h5362
  have p17141 := n17141 _v _q 
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p17100 := n17100 _v _q 
  have p17102 := n17102 _v _q 
  have p19610 := n19610 _v _q 
  have p17104 := n17104 _v _q 
  have p17096 := n17096 _v _q 
  have p17113 := n17113 _v _q 
  have p15731 := n15731 _v _q h5362
  have p17122 := n17122 _v _q 
  have p17117 := n17117 _v _q 
  have p17124 := n17124 _v _q 
  have p17115 := n17115 _v _q 
  have p20351 := n20351 _v _q h5362 h6575
  have p5255 := n5255 _v _q 
  have p7488 := n7488 _v _q h5362
  have p11413 := n11413 _v _q h6575
  have p20323 := n20323 _v _q h5362
  have p15742 := n15742 _v _q h5362
  exact FloorCertificate.node_20359 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2902 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e4215 _v) (e4541 _v) (e4808 _v) p13951 p5257 p20352 p19693 p15100 p20356 p17120 p17953 p17256 p19694 p15754 p16778 p15591 p20286 p20357 p17111 p20318 p17252 p19720 p17874 p17127 p15595 p20274 p18120 p17253 p17050 p17009 p17133 p17089 p19665 p16992 p17055 p17108 p8583 p15771 p20126 p15087 p17131 p17110 p17053 p15723 p20096 p17294 p15725 p17058 p17064 p17067 p17069 p17072 p17136 p19728 p17078 p17080 p17083 p17074 p17087 p17758 p17091 p17093 p15728 p17141 p17098 p17106 p17100 p17102 p19610 p17104 p17096 p17113 p15731 p17122 p17117 p17124 p17115 p20351 p5255 p7488 p11413 p20323 p15742
theorem n20360 (_v : Vars) (_q : Query _v) (h2242 : (e2242 _v)) (h3158 : (e3158 _v)) (h4156 : (e4156 _v)) (h5362 : (e5362 _v)) (h6549 : (e6549 _v)) (h8317 : (e8317 _v)) : (e3923 _v) := by
  have p14797 := n14797 _v _q 
  have p20354 := n20354 _v _q h2242 h3158 h4156 h5362 h6549 h8317
  change (e3923 _v) ∨ (e3919 _v) at p14797
  change (¬ (e3919 _v)) at p20354
  rcases p14797 with hlit | hlit
  · exact hlit
  · exact (False.elim (p20354 hlit))
theorem n20361 (_v : Vars) (_q : Query _v) (h2296 : (e2296 _v)) (h5362 : (e5362 _v)) (h6575 : (e6575 _v)) : (e3923 _v) := by
  have p14797 := n14797 _v _q 
  have p20359 := n20359 _v _q h2296 h5362 h6575
  change (e3923 _v) ∨ (e3919 _v) at p14797
  change (¬ (e3919 _v)) at p20359
  rcases p14797 with hlit | hlit
  · exact hlit
  · exact (False.elim (p20359 hlit))
theorem n20362 (_v : Vars) (_q : Query _v) (h2242 : (e2242 _v)) (h3158 : (e3158 _v)) (h4156 : (e4156 _v)) (h5362 : (e5362 _v)) (h6549 : (e6549 _v)) (h8317 : (e8317 _v)) : (e6600 _v) := by
  have p14484 := n14484 _v _q 
  have p20360 := n20360 _v _q h2242 h3158 h4156 h5362 h6549 h8317
  change (¬ (e2402 _v)) ∨ (¬ (e3923 _v)) at p14484
  rcases p14484 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p20360))
theorem n20363 (_v : Vars) (_q : Query _v) (h2242 : (e2242 _v)) (h3158 : (e3158 _v)) (h4156 : (e4156 _v)) (h5362 : (e5362 _v)) (h6549 : (e6549 _v)) (h8317 : (e8317 _v)) : (e7415 _v) := by
  have p15012 := n15012 _v _q 
  have p20355 := n20355 _v _q h2242 h3158 h4156 h5362 h6549 h8317
  change (e7415 _v) ∨ (e3937 _v) at p15012
  change (¬ (e3937 _v)) at p20355
  rcases p15012 with hlit | hlit
  · exact hlit
  · exact (False.elim (p20355 hlit))
theorem n20364 (_v : Vars) (_q : Query _v) (h2242 : (e2242 _v)) (h3158 : (e3158 _v)) (h4156 : (e4156 _v)) (h5362 : (e5362 _v)) (h6549 : (e6549 _v)) (h8317 : (e8317 _v)) : (e7489 _v) := by
  have p14534 := n14534 _v _q 
  have p20362 := n20362 _v _q h2242 h3158 h4156 h5362 h6549 h8317
  have p20363 := n20363 _v _q h2242 h3158 h4156 h5362 h6549 h8317
  change (e2402 _v) ∨ (¬ (e7415 _v)) at p14534
  change (¬ (e2402 _v)) at p20362
  rcases p14534 with hlit | hlit
  · exact (False.elim (p20362 hlit))
  · exact (False.elim (hlit p20363))
theorem n20366 (_v : Vars) (_q : Query _v)  : (e20365 _v) := by
  by_contra hc
  change ¬ ((¬ (e2242 _v)) ∨ (¬ (e3158 _v)) ∨ (¬ (e8317 _v)) ∨ (e2296 _v) ∨ (¬ (e4156 _v)) ∨ (e436 _v)) at hc
  have h2242 : (e2242 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h3158 : (e3158 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h4156 : (e4156 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h5362 : (e5362 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))
  have h6549 : (e6549 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h8317 : (e8317 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have p20364 := n20364 _v _q h2242 h3158 h4156 h5362 h6549 h8317
  exact p20364
theorem n20367 (_v : Vars) (_q : Query _v) (h2296 : (e2296 _v)) (h5362 : (e5362 _v)) (h6575 : (e6575 _v)) : (e7415 _v) := by
  have p15012 := n15012 _v _q 
  have p20358 := n20358 _v _q h2296 h5362 h6575
  change (e7415 _v) ∨ (e3937 _v) at p15012
  change (¬ (e3937 _v)) at p20358
  rcases p15012 with hlit | hlit
  · exact hlit
  · exact (False.elim (p20358 hlit))
theorem n20368 (_v : Vars) (_q : Query _v) (h2296 : (e2296 _v)) (h5362 : (e5362 _v)) (h6575 : (e6575 _v)) : (e2402 _v) := by
  have p14534 := n14534 _v _q 
  have p20367 := n20367 _v _q h2296 h5362 h6575
  change (e2402 _v) ∨ (¬ (e7415 _v)) at p14534
  rcases p14534 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p20367))
theorem n20369 (_v : Vars) (_q : Query _v) (h2296 : (e2296 _v)) (h5362 : (e5362 _v)) (h6575 : (e6575 _v)) : (e7489 _v) := by
  have p14484 := n14484 _v _q 
  have p20368 := n20368 _v _q h2296 h5362 h6575
  have p20361 := n20361 _v _q h2296 h5362 h6575
  change (¬ (e2402 _v)) ∨ (¬ (e3923 _v)) at p14484
  rcases p14484 with hlit | hlit
  · exact (False.elim (hlit p20368))
  · exact (False.elim (hlit p20361))
theorem n20371 (_v : Vars) (_q : Query _v)  : (e20370 _v) := by
  by_contra hc
  change ¬ ((¬ (e2296 _v)) ∨ (e436 _v) ∨ (e2351 _v)) at hc
  have h2296 : (e2296 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h5362 : (e5362 _v) := (fun hn => hc (Or.inr (Or.inl hn)))
  have h6575 : (e6575 _v) := (fun hn => hc (Or.inr (Or.inr hn)))
  have p20369 := n20369 _v _q h2296 h5362 h6575
  exact p20369
theorem n20372 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) (h6575 : (e6575 _v)) : (e6549 _v) := by
  have p20371 := n20371 _v _q 
  have p11413 := n11413 _v _q h6575
  have p7488 := n7488 _v _q h5362
  change (¬ (e2296 _v)) ∨ (e436 _v) ∨ (e2351 _v) at p20371
  change (¬ (e2351 _v)) at p11413
  change (¬ (e436 _v)) at p7488
  rcases p20371 with hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (p7488 hlit))
  · exact (False.elim (p11413 hlit))
theorem n20373 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) (h6575 : (e6575 _v)) : (e6879 _v) := by
  have p14643 := n14643 _v _q 
  have p20372 := n20372 _v _q h5362 h6575
  change (e2296 _v) ∨ (¬ (e6878 _v)) at p14643
  change (¬ (e2296 _v)) at p20372
  rcases p14643 with hlit | hlit
  · exact (False.elim (p20372 hlit))
  · exact hlit
theorem n20374 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) (h6575 : (e6575 _v)) : (e3152 _v) := by
  have p15776 := n15776 _v _q 
  have p20373 := n20373 _v _q h5362 h6575
  change (e6878 _v) ∨ (e3152 _v) at p15776
  change (¬ (e6878 _v)) at p20373
  rcases p15776 with hlit | hlit
  · exact (False.elim (p20373 hlit))
  · exact hlit
theorem n20375 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) (h6501 : (e6501 _v)) (h6575 : (e6575 _v)) : (e7489 _v) := by
  have p4016 := n4016 _v _q 
  have p11413 := n11413 _v _q h6575
  have p5257 := n5257 _v _q 
  have p16325 := n16325 _v _q h6501
  have p13951 := n13951 _v _q 
  have p17147 := n17147 _v _q 
  have p20318 := n20318 _v _q h5362
  have p20374 := n20374 _v _q h5362 h6575
  have p20352 := n20352 _v _q h5362
  have p19693 := n19693 _v _q h5362
  have p15733 := n15733 _v _q h5362
  have p17120 := n17120 _v _q 
  have p17953 := n17953 _v _q 
  have p17256 := n17256 _v _q 
  have p19694 := n19694 _v _q h5362
  have p8663 := n8663 _v _q 
  have p16778 := n16778 _v _q 
  have p15591 := n15591 _v _q h5362
  have p20286 := n20286 _v _q h5362
  have p20357 := n20357 _v _q h5362 h6575
  have p17111 := n17111 _v _q 
  have p15742 := n15742 _v _q h5362
  have p17252 := n17252 _v _q h5362
  have p19720 := n19720 _v _q h5362
  have p17874 := n17874 _v _q 
  have p17127 := n17127 _v _q 
  have p15595 := n15595 _v _q h5362
  have p20274 := n20274 _v _q 
  have p18120 := n18120 _v _q h5362
  have p17253 := n17253 _v _q h5362
  have p17050 := n17050 _v _q 
  have p17009 := n17009 _v _q 
  have p17133 := n17133 _v _q 
  have p17089 := n17089 _v _q 
  have p19665 := n19665 _v _q 
  have p16992 := n16992 _v _q 
  have p17055 := n17055 _v _q 
  have p17108 := n17108 _v _q 
  have p16576 := n16576 _v _q 
  have p15771 := n15771 _v _q h6575
  have p20126 := n20126 _v _q 
  have p15087 := n15087 _v _q h5362
  have p17131 := n17131 _v _q 
  have p17110 := n17110 _v _q 
  have p17053 := n17053 _v _q 
  have p15723 := n15723 _v _q h5362
  have p20096 := n20096 _v _q 
  have p17294 := n17294 _v _q 
  have p15725 := n15725 _v _q h5362
  have p17058 := n17058 _v _q 
  have p17064 := n17064 _v _q 
  have p17067 := n17067 _v _q 
  have p17069 := n17069 _v _q 
  have p17072 := n17072 _v _q 
  have p17136 := n17136 _v _q 
  have p19728 := n19728 _v _q h5362
  have p17078 := n17078 _v _q 
  have p17080 := n17080 _v _q 
  have p17083 := n17083 _v _q 
  have p17074 := n17074 _v _q 
  have p17087 := n17087 _v _q 
  have p17758 := n17758 _v _q 
  have p17091 := n17091 _v _q 
  have p17093 := n17093 _v _q 
  have p15728 := n15728 _v _q h5362
  have p17141 := n17141 _v _q 
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p17100 := n17100 _v _q 
  have p17102 := n17102 _v _q 
  have p19610 := n19610 _v _q 
  have p17104 := n17104 _v _q 
  have p17096 := n17096 _v _q 
  have p17113 := n17113 _v _q 
  have p15731 := n15731 _v _q h5362
  have p17122 := n17122 _v _q 
  have p17117 := n17117 _v _q 
  have p17124 := n17124 _v _q 
  have p17115 := n17115 _v _q 
  have p20351 := n20351 _v _q h5362 h6575
  have p20323 := n20323 _v _q h5362
  have p7488 := n7488 _v _q h5362
  have p15641 := n15641 _v _q h6501
  have p16633 := n16633 _v _q h6501
  have p15736 := n15736 _v _q h5362
  exact FloorCertificate.node_20375 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2863 _v) (e2877 _v) (e2883 _v) (e2902 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p4016 p11413 p5257 p16325 p13951 p17147 p20318 p20374 p20352 p19693 p15733 p17120 p17953 p17256 p19694 p8663 p16778 p15591 p20286 p20357 p17111 p15742 p17252 p19720 p17874 p17127 p15595 p20274 p18120 p17253 p17050 p17009 p17133 p17089 p19665 p16992 p17055 p17108 p16576 p15771 p20126 p15087 p17131 p17110 p17053 p15723 p20096 p17294 p15725 p17058 p17064 p17067 p17069 p17072 p17136 p19728 p17078 p17080 p17083 p17074 p17087 p17758 p17091 p17093 p15728 p17141 p17098 p17106 p17100 p17102 p19610 p17104 p17096 p17113 p15731 p17122 p17117 p17124 p17115 p20351 p20323 p7488 p15641 p16633 p15736
end
end Assembly
