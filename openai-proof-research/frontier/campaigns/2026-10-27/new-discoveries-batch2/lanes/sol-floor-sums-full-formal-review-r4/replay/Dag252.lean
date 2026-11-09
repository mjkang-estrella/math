import Dag251
import generated.th_lemma_33
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n21465 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) (h6750 : (e6750 _v)) : (e7927 _v) := by
  have p14855 := n14855 _v _q 
  have p21464 := n21464 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525 h6750
  change (¬ (e2787 _v)) ∨ (¬ (e7921 _v)) at p14855
  rcases p14855 with hlit | hlit
  · exact (False.elim (hlit p21464))
  · exact hlit
theorem n21466 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) (h6750 : (e6750 _v)) : (e4419 _v) := by
  have p16347 := n16347 _v _q 
  have p21465 := n21465 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525 h6750
  change (e7921 _v) ∨ (e4419 _v) at p16347
  change (¬ (e7921 _v)) at p21465
  rcases p16347 with hlit | hlit
  · exact (False.elim (p21465 hlit))
  · exact hlit
theorem n21467 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) (h6750 : (e6750 _v)) : (e5100 _v) := by
  have p15319 := n15319 _v _q 
  have p21453 := n21453 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525 h6750
  change (e5104 _v) ∨ (e5100 _v) at p15319
  change (¬ (e5104 _v)) at p21453
  rcases p15319 with hlit | hlit
  · exact (False.elim (p21453 hlit))
  · exact hlit
theorem n21468 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) (h6750 : (e6750 _v)) : (e2475 _v) := by
  have p21262 := n21262 _v _q 
  have p21432 := n21432 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525 h6750
  have p8463 := n8463 _v _q h6525
  have p21466 := n21466 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525 h6750
  have p21447 := n21447 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525 h6750
  have p21467 := n21467 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525 h6750
  have p21448 := n21448 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525 h6750
  have p15940 := n15940 _v _q h6750
  have p16706 := n16706 _v _q h2529 h6525
  have p21190 := n21190 _v _q h51 h91 h2529 h4306 h4653 h4813
  have p4999 := n4999 _v _q h91
  have p16705 := n16705 _v _q h2529
  have p16729 := n16729 _v _q h51
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p16572 := n16572 _v _q h2529
  have p4983 := n4983 _v _q h4813
  change (e2475 _v) ∨ (¬ (e2179 _v)) ∨ (e2242 _v) ∨ (¬ (e4419 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e5100 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4813 _v)) at p21262
  change (¬ (e2242 _v)) at p8463
  rcases p21262 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p21432))
  · exact (False.elim (p8463 hlit))
  · exact (False.elim (hlit p21466))
  · exact (False.elim (hlit p21447))
  · exact (False.elim (hlit p21467))
  · exact (False.elim (hlit p21448))
  · exact (False.elim (hlit p15940))
  · exact (False.elim (hlit p16706))
  · exact (False.elim (hlit p21190))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p16705))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p16572))
  · exact (False.elim (hlit p4983))
theorem n21469 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) (h6750 : (e6750 _v)) : (e8035 _v) := by
  have p14871 := n14871 _v _q 
  have p21468 := n21468 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525 h6750
  change (¬ (e2475 _v)) ∨ (¬ (e8029 _v)) at p14871
  rcases p14871 with hlit | hlit
  · exact (False.elim (hlit p21468))
  · exact hlit
theorem n21470 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) (h6750 : (e6750 _v)) : (e4546 _v) := by
  have p16307 := n16307 _v _q 
  have p21469 := n21469 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525 h6750
  change (e8029 _v) ∨ (e4546 _v) at p16307
  change (¬ (e8029 _v)) at p21469
  rcases p16307 with hlit | hlit
  · exact (False.elim (p21469 hlit))
  · exact hlit
theorem n21471 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) (h6750 : (e6750 _v)) : (e7817 _v) := by
  have p21258 := n21258 _v _q 
  have p8420 := n8420 _v _q h6750
  have p21470 := n21470 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525 h6750
  have p21466 := n21466 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525 h6750
  have p21447 := n21447 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525 h6750
  have p21467 := n21467 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525 h6750
  have p21442 := n21442 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525 h6750
  have p21448 := n21448 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525 h6750
  have p16706 := n16706 _v _q h2529 h6525
  have p21190 := n21190 _v _q h51 h91 h2529 h4306 h4653 h4813
  have p16058 := n16058 _v _q h6525
  have p16689 := n16689 _v _q h6525
  have p4999 := n4999 _v _q h91
  have p16705 := n16705 _v _q h2529
  have p16729 := n16729 _v _q h51
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p16572 := n16572 _v _q h2529
  have p4983 := n4983 _v _q h4813
  change (¬ (e7814 _v)) ∨ (e2733 _v) ∨ (¬ (e4546 _v)) ∨ (¬ (e4419 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e5100 _v)) ∨ (¬ (e3158 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4813 _v)) at p21258
  change (¬ (e2733 _v)) at p8420
  rcases p21258 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (p8420 hlit))
  · exact (False.elim (hlit p21470))
  · exact (False.elim (hlit p21466))
  · exact (False.elim (hlit p21447))
  · exact (False.elim (hlit p21467))
  · exact (False.elim (hlit p21442))
  · exact (False.elim (hlit p21448))
  · exact (False.elim (hlit p16706))
  · exact (False.elim (hlit p21190))
  · exact (False.elim (hlit p16058))
  · exact (False.elim (hlit p16689))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p16705))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p16572))
  · exact (False.elim (hlit p4983))
theorem n21472 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) (h6750 : (e6750 _v)) : (e7818 _v) := by
  have p15221 := n15221 _v _q 
  have p21471 := n21471 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525 h6750
  change (e7818 _v) ∨ (e7814 _v) at p15221
  change (¬ (e7814 _v)) at p21471
  rcases p15221 with hlit | hlit
  · exact hlit
  · exact (False.elim (p21471 hlit))
theorem n21473 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) (h6750 : (e6750 _v)) : (e2303 _v) := by
  have p14994 := n14994 _v _q 
  have p21472 := n21472 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525 h6750
  change (e2303 _v) ∨ (¬ (e7818 _v)) at p14994
  rcases p14994 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p21472))
theorem n21474 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) (h6750 : (e6750 _v)) : (e7804 _v) := by
  have p14837 := n14837 _v _q 
  have p21473 := n21473 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525 h6750
  change (¬ (e2303 _v)) ∨ (¬ (e7798 _v)) at p14837
  rcases p14837 with hlit | hlit
  · exact (False.elim (hlit p21473))
  · exact hlit
theorem n21475 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) (h6750 : (e6750 _v)) : (e4285 _v) := by
  have p16274 := n16274 _v _q 
  have p21474 := n21474 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525 h6750
  change (e7798 _v) ∨ (e4285 _v) at p16274
  change (¬ (e7798 _v)) at p21474
  rcases p16274 with hlit | hlit
  · exact (False.elim (p21474 hlit))
  · exact hlit
theorem n21476 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e7749 _v) := by
  have p14941 := n14941 _v _q 
  have p21241 := n21241 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  change (e7753 _v) ∨ (e7749 _v) at p14941
  change (¬ (e7753 _v)) at p21241
  rcases p14941 with hlit | hlit
  · exact (False.elim (p21241 hlit))
  · exact hlit
theorem n21477 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e4439 _v) := by
  have p14925 := n14925 _v _q 
  have p21210 := n21210 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  change (e4446 _v) ∨ (e4439 _v) at p14925
  change (¬ (e4446 _v)) at p21210
  rcases p14925 with hlit | hlit
  · exact (False.elim (p21210 hlit))
  · exact hlit
theorem n21478 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e4567 _v) := by
  have p8485 := n8485 _v _q 
  have p21136 := n21136 _v _q h51 h2529 h4306 h4653 h4813 h6525
  change (e4574 _v) ∨ (e4567 _v) at p8485
  change (¬ (e4574 _v)) at p21136
  rcases p8485 with hlit | hlit
  · exact (False.elim (p21136 hlit))
  · exact hlit
theorem n21479 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) (h6750 : (e6750 _v)) : (e7489 _v) := by
  have p10893 := n10893 _v _q 
  have p258 := n258 _v _q 
  have p8420 := n8420 _v _q h6750
  have p21475 := n21475 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525 h6750
  have p20426 := n20426 _v _q 
  have p20126 := n20126 _v _q 
  have p17110 := n17110 _v _q 
  have p17053 := n17053 _v _q 
  have p21470 := n21470 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525 h6750
  have p20096 := n20096 _v _q 
  have p17131 := n17131 _v _q 
  have p13951 := n13951 _v _q 
  have p17294 := n17294 _v _q 
  have p16943 := n16943 _v _q 
  have p17058 := n17058 _v _q 
  have p16913 := n16913 _v _q 
  have p21466 := n21466 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525 h6750
  have p21447 := n21447 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525 h6750
  have p17064 := n17064 _v _q 
  have p17067 := n17067 _v _q 
  have p17080 := n17080 _v _q 
  have p17147 := n17147 _v _q 
  have p17072 := n17072 _v _q 
  have p17074 := n17074 _v _q 
  have p17069 := n17069 _v _q 
  have p21467 := n21467 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525 h6750
  have p21442 := n21442 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525 h6750
  have p20836 := n20836 _v _q 
  have p20653 := n20653 _v _q 
  have p17078 := n17078 _v _q 
  have p17136 := n17136 _v _q 
  have p21448 := n21448 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525 h6750
  have p17087 := n17087 _v _q 
  have p17083 := n17083 _v _q 
  have p21476 := n21476 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  have p17055 := n17055 _v _q 
  have p17093 := n17093 _v _q 
  have p17091 := n17091 _v _q 
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p15940 := n15940 _v _q h6750
  have p21477 := n21477 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  have p17141 := n17141 _v _q 
  have p17100 := n17100 _v _q 
  have p19610 := n19610 _v _q 
  have p16706 := n16706 _v _q h2529 h6525
  have p17102 := n17102 _v _q 
  have p21190 := n21190 _v _q h51 h91 h2529 h4306 h4653 h4813
  have p17009 := n17009 _v _q 
  have p16058 := n16058 _v _q h6525
  have p16689 := n16689 _v _q h6525
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
  have p20470 := n20470 _v _q 
  have p16705 := n16705 _v _q h2529
  have p17020 := n17020 _v _q 
  have p20274 := n20274 _v _q 
  have p21478 := n21478 _v _q h51 h2529 h4306 h4653 h4813 h6525
  have p16729 := n16729 _v _q h51
  have p17050 := n17050 _v _q 
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p16572 := n16572 _v _q h2529
  have p4983 := n4983 _v _q h4813
  have p17122 := n17122 _v _q 
  have p16778 := n16778 _v _q 
  have p20829 := n20829 _v _q 
  have p17108 := n17108 _v _q 
  have p20461 := n20461 _v _q 
  have p21432 := n21432 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525 h6750
  have p8463 := n8463 _v _q h6525
  exact FloorCertificate.node_21479 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2883 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p10893 p258 p8420 p21475 p20426 p20126 p17110 p17053 p21470 p20096 p17131 p13951 p17294 p16943 p17058 p16913 p21466 p21447 p17064 p17067 p17080 p17147 p17072 p17074 p17069 p21467 p21442 p20836 p20653 p17078 p17136 p21448 p17087 p17083 p21476 p17055 p17093 p17091 p17098 p17106 p15940 p21477 p17141 p17100 p19610 p16706 p17102 p21190 p17009 p16058 p16689 p17096 p17115 p17758 p17124 p17111 p19665 p17113 p17117 p20467 p17120 p4999 p17133 p17874 p17104 p17127 p17089 p20470 p16705 p17020 p20274 p21478 p16729 p17050 p17138 p17060 p16572 p4983 p17122 p16778 p20829 p17108 p20461 p21432 p8463
theorem n21481 (_v : Vars) (_q : Query _v)  : (e21480 _v) := by
  by_contra hc
  change ¬ ((e2733 _v) ∨ (¬ (e91 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (e2242 _v) ∨ (¬ (e2529 _v))) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h2529 : (e2529 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h6525 : (e6525 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h6750 : (e6750 _v) := (fun hn => hc (Or.inl hn))
  have p21479 := n21479 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525 h6750
  exact p21479
theorem n21482 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e2733 _v) := by
  have p21481 := n21481 _v _q 
  have p8463 := n8463 _v _q h6525
  have p16729 := n16729 _v _q h51
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4983 := n4983 _v _q h4813
  have p4999 := n4999 _v _q h91
  have p8548 := n8548 _v _q h2529
  change (e2733 _v) ∨ (¬ (e91 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (e2242 _v) ∨ (¬ (e2529 _v)) at p21481
  change (¬ (e2242 _v)) at p8463
  rcases p21481 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (p8463 hlit))
  · exact (False.elim (hlit p8548))
theorem n21483 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e4109 _v) := by
  have p14689 := n14689 _v _q 
  have p21482 := n21482 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  change (¬ (e2733 _v)) ∨ (¬ (e4108 _v)) at p14689
  rcases p14689 with hlit | hlit
  · exact (False.elim (hlit p21482))
  · exact hlit
theorem n21484 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e4101 _v) := by
  have p14929 := n14929 _v _q 
  have p21483 := n21483 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  change (e4108 _v) ∨ (e4101 _v) at p14929
  change (¬ (e4108 _v)) at p21483
  rcases p14929 with hlit | hlit
  · exact (False.elim (p21483 hlit))
  · exact hlit
theorem n21485 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e2179 _v) := by
  have p8590 := n8590 _v _q 
  have p21482 := n21482 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  have p8548 := n8548 _v _q h2529
  change (e2179 _v) ∨ (¬ (e2529 _v)) ∨ (¬ (e2733 _v)) at p8590
  rcases p8590 with hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p8548))
  · exact (False.elim (hlit p21482))
theorem n21486 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e4616 _v) := by
  have p14684 := n14684 _v _q 
  have p21485 := n21485 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  change (¬ (e2179 _v)) ∨ (¬ (e3162 _v)) at p14684
  rcases p14684 with hlit | hlit
  · exact (False.elim (hlit p21485))
  · exact hlit
theorem n21487 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e3158 _v) := by
  have p15126 := n15126 _v _q 
  have p21486 := n21486 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  change (e3162 _v) ∨ (e3158 _v) at p15126
  change (¬ (e3162 _v)) at p21486
  rcases p15126 with hlit | hlit
  · exact (False.elim (p21486 hlit))
  · exact hlit
theorem n21488 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) (h6571 : (e6571 _v)) : (e8048 _v) := by
  have p20461 := n20461 _v _q 
  have p13951 := n13951 _v _q 
  have p17108 := n17108 _v _q 
  have p20426 := n20426 _v _q 
  have p20126 := n20126 _v _q 
  have p10893 := n10893 _v _q 
  have p17110 := n17110 _v _q 
  have p21484 := n21484 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  have p17053 := n17053 _v _q 
  have p20096 := n20096 _v _q 
  have p17189 := n17189 _v _q h6571
  have p17131 := n17131 _v _q 
  have p17294 := n17294 _v _q 
  have p16943 := n16943 _v _q 
  have p17058 := n17058 _v _q 
  have p17256 := n17256 _v _q 
  have p8447 := n8447 _v _q h6571
  have p17064 := n17064 _v _q 
  have p17067 := n17067 _v _q 
  have p17080 := n17080 _v _q 
  have p21485 := n21485 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  have p17072 := n17072 _v _q 
  have p17074 := n17074 _v _q 
  have p17069 := n17069 _v _q 
  have p15623 := n15623 _v _q h6571
  have p21487 := n21487 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  have p20836 := n20836 _v _q 
  have p20653 := n20653 _v _q 
  have p17078 := n17078 _v _q 
  have p17136 := n17136 _v _q 
  have p17255 := n17255 _v _q h6571
  have p17087 := n17087 _v _q 
  have p17083 := n17083 _v _q 
  have p21476 := n21476 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  have p17055 := n17055 _v _q 
  have p17093 := n17093 _v _q 
  have p17091 := n17091 _v _q 
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p8548 := n8548 _v _q h2529
  have p21477 := n21477 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  have p17141 := n17141 _v _q 
  have p17100 := n17100 _v _q 
  have p19610 := n19610 _v _q 
  have p16706 := n16706 _v _q h2529 h6525
  have p17102 := n17102 _v _q 
  have p21190 := n21190 _v _q h51 h91 h2529 h4306 h4653 h4813
  have p17009 := n17009 _v _q 
  have p16058 := n16058 _v _q h6525
  have p16689 := n16689 _v _q h6525
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
  have p20470 := n20470 _v _q 
  have p16705 := n16705 _v _q h2529
  have p17020 := n17020 _v _q 
  have p20274 := n20274 _v _q 
  have p21478 := n21478 _v _q h51 h2529 h4306 h4653 h4813 h6525
  have p16729 := n16729 _v _q h51
  have p17050 := n17050 _v _q 
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p16572 := n16572 _v _q h2529
  have p4983 := n4983 _v _q h4813
  have p17122 := n17122 _v _q 
  have p16778 := n16778 _v _q 
  have p20829 := n20829 _v _q 
  have p8463 := n8463 _v _q h6525
  have p17147 := n17147 _v _q 
  have p16715 := n16715 _v _q h2529 h6525 h6571
  exact FloorCertificate.node_21488 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2883 _v) (e2902 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p20461 p13951 p17108 p20426 p20126 p10893 p17110 p21484 p17053 p20096 p17189 p17131 p17294 p16943 p17058 p17256 p8447 p17064 p17067 p17080 p21485 p17072 p17074 p17069 p15623 p21487 p20836 p20653 p17078 p17136 p17255 p17087 p17083 p21476 p17055 p17093 p17091 p17098 p17106 p8548 p21477 p17141 p17100 p19610 p16706 p17102 p21190 p17009 p16058 p16689 p17096 p17115 p17758 p17124 p17111 p19665 p17113 p17117 p20467 p17120 p4999 p17133 p17874 p17104 p17127 p17089 p20470 p16705 p17020 p20274 p21478 p16729 p17050 p17138 p17060 p16572 p4983 p17122 p16778 p20829 p8463 p17147 p16715
theorem n21489 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) (h6571 : (e6571 _v)) : (e4547 _v) := by
  have p20426 := n20426 _v _q 
  have p20126 := n20126 _v _q 
  have p10893 := n10893 _v _q 
  have p17110 := n17110 _v _q 
  have p21484 := n21484 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  have p17053 := n17053 _v _q 
  have p20096 := n20096 _v _q 
  have p17189 := n17189 _v _q h6571
  have p17131 := n17131 _v _q 
  have p17108 := n17108 _v _q 
  have p17294 := n17294 _v _q 
  have p16943 := n16943 _v _q 
  have p17058 := n17058 _v _q 
  have p13951 := n13951 _v _q 
  have p17256 := n17256 _v _q 
  have p8447 := n8447 _v _q h6571
  have p17064 := n17064 _v _q 
  have p17067 := n17067 _v _q 
  have p17080 := n17080 _v _q 
  have p8548 := n8548 _v _q h2529
  have p17072 := n17072 _v _q 
  have p17074 := n17074 _v _q 
  have p17069 := n17069 _v _q 
  have p15623 := n15623 _v _q h6571
  have p20461 := n20461 _v _q 
  have p20836 := n20836 _v _q 
  have p20653 := n20653 _v _q 
  have p17078 := n17078 _v _q 
  have p17136 := n17136 _v _q 
  have p17255 := n17255 _v _q h6571
  have p17087 := n17087 _v _q 
  have p17083 := n17083 _v _q 
  have p21476 := n21476 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  have p17055 := n17055 _v _q 
  have p17093 := n17093 _v _q 
  have p17091 := n17091 _v _q 
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p21487 := n21487 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  have p21477 := n21477 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  have p17141 := n17141 _v _q 
  have p17100 := n17100 _v _q 
  have p19610 := n19610 _v _q 
  have p16706 := n16706 _v _q h2529 h6525
  have p17102 := n17102 _v _q 
  have p21190 := n21190 _v _q h51 h91 h2529 h4306 h4653 h4813
  have p17009 := n17009 _v _q 
  have p16058 := n16058 _v _q h6525
  have p16689 := n16689 _v _q h6525
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
  have p20470 := n20470 _v _q 
  have p16705 := n16705 _v _q h2529
  have p17020 := n17020 _v _q 
  have p20274 := n20274 _v _q 
  have p21478 := n21478 _v _q h51 h2529 h4306 h4653 h4813 h6525
  have p16729 := n16729 _v _q h51
  have p17050 := n17050 _v _q 
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p16572 := n16572 _v _q h2529
  have p4983 := n4983 _v _q h4813
  have p17122 := n17122 _v _q 
  have p16778 := n16778 _v _q 
  have p20829 := n20829 _v _q 
  have p8463 := n8463 _v _q h6525
  have p17147 := n17147 _v _q 
  have p16715 := n16715 _v _q h2529 h6525 h6571
  exact FloorCertificate.node_21489 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2883 _v) (e2902 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p20426 p20126 p10893 p17110 p21484 p17053 p20096 p17189 p17131 p17108 p17294 p16943 p17058 p13951 p17256 p8447 p17064 p17067 p17080 p8548 p17072 p17074 p17069 p15623 p20461 p20836 p20653 p17078 p17136 p17255 p17087 p17083 p21476 p17055 p17093 p17091 p17098 p17106 p21487 p21477 p17141 p17100 p19610 p16706 p17102 p21190 p17009 p16058 p16689 p17096 p17115 p17758 p17124 p17111 p19665 p17113 p17117 p20467 p17120 p4999 p17133 p17874 p17104 p17127 p17089 p20470 p16705 p17020 p20274 p21478 p16729 p17050 p17138 p17060 p16572 p4983 p17122 p16778 p20829 p8463 p17147 p16715
theorem n21490 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) (h6571 : (e6571 _v)) : (e8049 _v) := by
  have p15206 := n15206 _v _q 
  have p21488 := n21488 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525 h6571
  change (e8049 _v) ∨ (e8045 _v) at p15206
  change (¬ (e8045 _v)) at p21488
  rcases p15206 with hlit | hlit
  · exact hlit
  · exact (False.elim (p21488 hlit))
theorem n21491 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) (h6571 : (e6571 _v)) : (e2475 _v) := by
  have p15207 := n15207 _v _q 
  have p21490 := n21490 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525 h6571
  change (e2475 _v) ∨ (¬ (e8049 _v)) at p15207
  rcases p15207 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p21490))
theorem n21492 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) (h6571 : (e6571 _v)) : (e8029 _v) := by
  have p16307 := n16307 _v _q 
  have p21489 := n21489 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525 h6571
  change (e8029 _v) ∨ (e4546 _v) at p16307
  change (¬ (e4546 _v)) at p21489
  rcases p16307 with hlit | hlit
  · exact hlit
  · exact (False.elim (p21489 hlit))
theorem n21493 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) (h6571 : (e6571 _v)) : (e7489 _v) := by
  have p14871 := n14871 _v _q 
  have p21491 := n21491 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525 h6571
  have p21492 := n21492 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525 h6571
  change (¬ (e2475 _v)) ∨ (¬ (e8029 _v)) at p14871
  rcases p14871 with hlit | hlit
  · exact (False.elim (hlit p21491))
  · exact (False.elim (hlit p21492))
theorem n21495 (_v : Vars) (_q : Query _v)  : (e21494 _v) := by
  by_contra hc
  change ¬ ((e2358 _v) ∨ (¬ (e2529 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (e2242 _v)) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h2529 : (e2529 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h6525 : (e6525 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))))
  have h6571 : (e6571 _v) := (fun hn => hc (Or.inl hn))
  have p21493 := n21493 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525 h6571
  exact p21493
theorem n21496 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e2358 _v) := by
  have p21495 := n21495 _v _q 
  have p8463 := n8463 _v _q h6525
  have p4999 := n4999 _v _q h91
  have p16729 := n16729 _v _q h51
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4983 := n4983 _v _q h4813
  have p8548 := n8548 _v _q h2529
  change (e2358 _v) ∨ (¬ (e2529 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (e2242 _v) at p21495
  change (¬ (e2242 _v)) at p8463
  rcases p21495 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p8548))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (p8463 hlit))
theorem n21497 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e7640 _v) := by
  have p14828 := n14828 _v _q 
  have p21496 := n21496 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  change (¬ (e2358 _v)) ∨ (¬ (e7634 _v)) at p14828
  rcases p14828 with hlit | hlit
  · exact (False.elim (hlit p21496))
  · exact hlit
theorem n21498 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e4139 _v) := by
  have p16281 := n16281 _v _q 
  have p21497 := n21497 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  change (e7634 _v) ∨ (e4139 _v) at p16281
  change (¬ (e7634 _v)) at p21497
  rcases p16281 with hlit | hlit
  · exact (False.elim (p21497 hlit))
  · exact hlit
theorem n21499 (_v : Vars) (_q : Query _v) (h13 : (e13 _v)) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h3919 : (e3919 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e7489 _v) := by
  have p258 := n258 _v _q 
  have p10893 := n10893 _v _q 
  have p8463 := n8463 _v _q h6525
  have p16691 := n16691 _v _q h13
  have p21485 := n21485 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  have p8548 := n8548 _v _q h2529
  have p16714 := n16714 _v _q h13
  have p16879 := n16879 _v _q h13
  have p20426 := n20426 _v _q 
  have p20126 := n20126 _v _q 
  have p17110 := n17110 _v _q 
  have p21484 := n21484 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  have p17053 := n17053 _v _q 
  have p16694 := n16694 _v _q h13
  have p20096 := n20096 _v _q 
  have p17131 := n17131 _v _q 
  have p17108 := n17108 _v _q 
  have p17294 := n17294 _v _q 
  have p16943 := n16943 _v _q 
  have p17058 := n17058 _v _q 
  have p13951 := n13951 _v _q 
  have p17079 := n17079 _v _q h3919
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
  have p21476 := n21476 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  have p17055 := n17055 _v _q 
  have p17093 := n17093 _v _q 
  have p17091 := n17091 _v _q 
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p21487 := n21487 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  have p21477 := n21477 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  have p17141 := n17141 _v _q 
  have p17100 := n17100 _v _q 
  have p19610 := n19610 _v _q 
  have p16706 := n16706 _v _q h2529 h6525
  have p17102 := n17102 _v _q 
  have p21190 := n21190 _v _q h51 h91 h2529 h4306 h4653 h4813
  have p17009 := n17009 _v _q 
  have p16058 := n16058 _v _q h6525
  have p16689 := n16689 _v _q h6525
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
  have p20470 := n20470 _v _q 
  have p16705 := n16705 _v _q h2529
  have p17020 := n17020 _v _q 
  have p20274 := n20274 _v _q 
  have p21478 := n21478 _v _q h51 h2529 h4306 h4653 h4813 h6525
  have p16729 := n16729 _v _q h51
  have p17050 := n17050 _v _q 
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p16572 := n16572 _v _q h2529
  have p4983 := n4983 _v _q h4813
  have p17122 := n17122 _v _q 
  have p16778 := n16778 _v _q 
  have p20829 := n20829 _v _q 
  have p21498 := n21498 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  exact FloorCertificate.node_21499 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2902 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p258 p10893 p8463 p16691 p21485 p8548 p16714 p16879 p20426 p20126 p17110 p21484 p17053 p16694 p20096 p17131 p17108 p17294 p16943 p17058 p13951 p17079 p17064 p17067 p17080 p17072 p17074 p17069 p20461 p20836 p20653 p17078 p17136 p17087 p17083 p21476 p17055 p17093 p17091 p17098 p17106 p21487 p21477 p17141 p17100 p19610 p16706 p17102 p21190 p17009 p16058 p16689 p17096 p17115 p17758 p17124 p17111 p19665 p17113 p17117 p20467 p17120 p4999 p17133 p17874 p17104 p17127 p17089 p20470 p16705 p17020 p20274 p21478 p16729 p17050 p17138 p17060 p16572 p4983 p17122 p16778 p20829 p21498
theorem n21501 (_v : Vars) (_q : Query _v)  : (e21500 _v) := by
  by_contra hc
  change ¬ ((¬ (e13 _v)) ∨ (e2242 _v) ∨ (¬ (e2529 _v)) ∨ (¬ (e3919 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v))) at hc
  have h13 : (e13 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h2529 : (e2529 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h3919 : (e3919 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn)))))))))
  have h6525 : (e6525 _v) := (fun hn => hc (Or.inr (Or.inl hn)))
  have p21499 := n21499 _v _q h13 h51 h91 h2529 h3919 h4306 h4653 h4813 h6525
  exact p21499
theorem n21502 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h3919 : (e3919 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e5093 _v) := by
  have p21501 := n21501 _v _q 
  have p17079 := n17079 _v _q h3919
  have p8548 := n8548 _v _q h2529
  have p8463 := n8463 _v _q h6525
  have p4999 := n4999 _v _q h91
  have p16729 := n16729 _v _q h51
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4983 := n4983 _v _q h4813
  change (¬ (e13 _v)) ∨ (e2242 _v) ∨ (¬ (e2529 _v)) ∨ (¬ (e3919 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) at p21501
  change (¬ (e2242 _v)) at p8463
  rcases p21501 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (p8463 hlit))
  · exact (False.elim (hlit p8548))
  · exact (False.elim (hlit p17079))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p4983))
theorem n21503 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h3919 : (e3919 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e5105 _v) := by
  have p15204 := n15204 _v _q 
  have p21502 := n21502 _v _q h51 h91 h2529 h3919 h4306 h4653 h4813 h6525
  change (e13 _v) ∨ (¬ (e5104 _v)) at p15204
  change (¬ (e13 _v)) at p21502
  rcases p15204 with hlit | hlit
  · exact (False.elim (p21502 hlit))
  · exact hlit
theorem n21504 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2402 : (e2402 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e5093 _v) := by
  have p21501 := n21501 _v _q 
  have p14799 := n14799 _v _q h2402
  have p8548 := n8548 _v _q h2529
  have p8463 := n8463 _v _q h6525
  have p4999 := n4999 _v _q h91
  have p16729 := n16729 _v _q h51
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4983 := n4983 _v _q h4813
  change (¬ (e13 _v)) ∨ (e2242 _v) ∨ (¬ (e2529 _v)) ∨ (¬ (e3919 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) at p21501
  change (¬ (e2242 _v)) at p8463
  rcases p21501 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (p8463 hlit))
  · exact (False.elim (hlit p8548))
  · exact (False.elim (hlit p14799))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p4983))
theorem n21505 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h3919 : (e3919 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e5100 _v) := by
  have p15319 := n15319 _v _q 
  have p21503 := n21503 _v _q h51 h91 h2529 h3919 h4306 h4653 h4813 h6525
  change (e5104 _v) ∨ (e5100 _v) at p15319
  change (¬ (e5104 _v)) at p21503
  rcases p15319 with hlit | hlit
  · exact (False.elim (p21503 hlit))
  · exact hlit
theorem n21506 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h3919 : (e3919 _v)) (h4285 : (e4285 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) (h7935 : (e7935 _v)) (h8045 : (e8045 _v)) : (e7489 _v) := by
  have p13951 := n13951 _v _q 
  have p16778 := n16778 _v _q 
  have p8463 := n8463 _v _q h6525
  have p4016 := n4016 _v _q 
  have p258 := n258 _v _q 
  have p8548 := n8548 _v _q h2529
  have p4977 := n4977 _v _q h4285
  have p17163 := n17163 _v _q h7935
  have p21498 := n21498 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  have p20829 := n20829 _v _q 
  have p21505 := n21505 _v _q h51 h91 h2529 h3919 h4306 h4653 h4813 h6525
  have p20426 := n20426 _v _q 
  have p20126 := n20126 _v _q 
  have p17110 := n17110 _v _q 
  have p21484 := n21484 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  have p17053 := n17053 _v _q 
  have p20096 := n20096 _v _q 
  have p17131 := n17131 _v _q 
  have p17108 := n17108 _v _q 
  have p17294 := n17294 _v _q 
  have p16943 := n16943 _v _q 
  have p17058 := n17058 _v _q 
  have p17157 := n17157 _v _q h8045
  have p17079 := n17079 _v _q h3919
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
  have p21476 := n21476 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  have p17055 := n17055 _v _q 
  have p17093 := n17093 _v _q 
  have p17091 := n17091 _v _q 
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p21487 := n21487 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  have p21477 := n21477 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  have p17141 := n17141 _v _q 
  have p17100 := n17100 _v _q 
  have p19610 := n19610 _v _q 
  have p16706 := n16706 _v _q h2529 h6525
  have p17102 := n17102 _v _q 
  have p21190 := n21190 _v _q h51 h91 h2529 h4306 h4653 h4813
  have p17009 := n17009 _v _q 
  have p16058 := n16058 _v _q h6525
  have p16689 := n16689 _v _q h6525
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
  have p20470 := n20470 _v _q 
  have p16705 := n16705 _v _q h2529
  have p17020 := n17020 _v _q 
  have p20274 := n20274 _v _q 
  have p21478 := n21478 _v _q h51 h2529 h4306 h4653 h4813 h6525
  have p16729 := n16729 _v _q h51
  have p17050 := n17050 _v _q 
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p16572 := n16572 _v _q h2529
  have p4983 := n4983 _v _q h4813
  have p17122 := n17122 _v _q 
  exact FloorCertificate.node_21506 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2902 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p13951 p16778 p8463 p4016 p258 p8548 p4977 p17163 p21498 p20829 p21505 p20426 p20126 p17110 p21484 p17053 p20096 p17131 p17108 p17294 p16943 p17058 p17157 p17079 p17064 p17067 p17080 p17072 p17074 p17069 p20461 p20836 p20653 p17078 p17136 p17087 p17083 p21476 p17055 p17093 p17091 p17098 p17106 p21487 p21477 p17141 p17100 p19610 p16706 p17102 p21190 p17009 p16058 p16689 p17096 p17115 p17758 p17124 p17111 p19665 p17113 p17117 p20467 p17120 p4999 p17133 p17874 p17104 p17127 p17089 p20470 p16705 p17020 p20274 p21478 p16729 p17050 p17138 p17060 p16572 p4983 p17122
theorem n21507 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2402 : (e2402 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e5105 _v) := by
  have p15204 := n15204 _v _q 
  have p21504 := n21504 _v _q h51 h91 h2402 h2529 h4306 h4653 h4813 h6525
  change (e13 _v) ∨ (¬ (e5104 _v)) at p15204
  change (¬ (e13 _v)) at p21504
  rcases p15204 with hlit | hlit
  · exact (False.elim (p21504 hlit))
  · exact hlit
theorem n21508 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2402 : (e2402 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e5100 _v) := by
  have p15319 := n15319 _v _q 
  have p21507 := n21507 _v _q h51 h91 h2402 h2529 h4306 h4653 h4813 h6525
  change (e5104 _v) ∨ (e5100 _v) at p15319
  change (¬ (e5104 _v)) at p21507
  rcases p15319 with hlit | hlit
  · exact (False.elim (p21507 hlit))
  · exact hlit
theorem n21510 (_v : Vars) (_q : Query _v)  : (e21509 _v) := by
  by_contra hc
  change ¬ ((¬ (e7935 _v)) ∨ (e2242 _v) ∨ (¬ (e2529 _v)) ∨ (¬ (e4285 _v)) ∨ (¬ (e8045 _v)) ∨ (¬ (e3919 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v))) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h2529 : (e2529 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h3919 : (e3919 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h4285 : (e4285 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn)))))))))))
  have h6525 : (e6525 _v) := (fun hn => hc (Or.inr (Or.inl hn)))
  have h7935 : (e7935 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h8045 : (e8045 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have p21506 := n21506 _v _q h51 h91 h2529 h3919 h4285 h4306 h4653 h4813 h6525 h7935 h8045
  exact p21506
theorem n21511 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2402 : (e2402 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) (h7807 : (e7807 _v)) (h8038 : (e8038 _v)) : (e7489 _v) := by
  have p8548 := n8548 _v _q h2529
  have p16953 := n16953 _v _q h7807 h8038
  have p11350 := n11350 _v _q h7807
  have p21498 := n21498 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  have p15373 := n15373 _v _q h7807
  have p20829 := n20829 _v _q 
  have p8463 := n8463 _v _q h6525
  have p21508 := n21508 _v _q h51 h91 h2402 h2529 h4306 h4653 h4813 h6525
  have p20426 := n20426 _v _q 
  have p20126 := n20126 _v _q 
  have p17110 := n17110 _v _q 
  have p21484 := n21484 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  have p17053 := n17053 _v _q 
  have p8591 := n8591 _v _q h2402
  have p20096 := n20096 _v _q 
  have p17131 := n17131 _v _q 
  have p17108 := n17108 _v _q 
  have p17294 := n17294 _v _q 
  have p16943 := n16943 _v _q 
  have p17058 := n17058 _v _q 
  have p13951 := n13951 _v _q 
  have p14799 := n14799 _v _q h2402
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
  have p21476 := n21476 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  have p17055 := n17055 _v _q 
  have p17093 := n17093 _v _q 
  have p17091 := n17091 _v _q 
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p21487 := n21487 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  have p21477 := n21477 _v _q h51 h91 h2529 h4306 h4653 h4813 h6525
  have p17141 := n17141 _v _q 
  have p17100 := n17100 _v _q 
  have p19610 := n19610 _v _q 
  have p16706 := n16706 _v _q h2529 h6525
  have p17102 := n17102 _v _q 
  have p21190 := n21190 _v _q h51 h91 h2529 h4306 h4653 h4813
  have p17009 := n17009 _v _q 
  have p16058 := n16058 _v _q h6525
  have p16689 := n16689 _v _q h6525
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
  have p20470 := n20470 _v _q 
  have p16705 := n16705 _v _q h2529
  have p17020 := n17020 _v _q 
  have p20274 := n20274 _v _q 
  have p21478 := n21478 _v _q h51 h2529 h4306 h4653 h4813 h6525
  have p16729 := n16729 _v _q h51
  have p17050 := n17050 _v _q 
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p16572 := n16572 _v _q h2529
  have p4983 := n4983 _v _q h4813
  have p17122 := n17122 _v _q 
  have p16778 := n16778 _v _q 
  have p15209 := n15209 _v _q h8038
  have p8602 := n8602 _v _q h8038
  exact FloorCertificate.node_21511 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2902 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p8548 p16953 p11350 p21498 p15373 p20829 p8463 p21508 p20426 p20126 p17110 p21484 p17053 p8591 p20096 p17131 p17108 p17294 p16943 p17058 p13951 p14799 p17064 p17067 p17080 p17072 p17074 p17069 p20461 p20836 p20653 p17078 p17136 p17087 p17083 p21476 p17055 p17093 p17091 p17098 p17106 p21487 p21477 p17141 p17100 p19610 p16706 p17102 p21190 p17009 p16058 p16689 p17096 p17115 p17758 p17124 p17111 p19665 p17113 p17117 p20467 p17120 p4999 p17133 p17874 p17104 p17127 p17089 p20470 p16705 p17020 p20274 p21478 p16729 p17050 p17138 p17060 p16572 p4983 p17122 p16778 p15209 p8602
theorem n21513 (_v : Vars) (_q : Query _v)  : (e21512 _v) := by
  by_contra hc
  change ¬ ((e2303 _v) ∨ (¬ (e2529 _v)) ∨ (e2242 _v) ∨ (¬ (e2402 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (e2475 _v)) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h2402 : (e2402 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h2529 : (e2529 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h6525 : (e6525 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h7807 : (e7807 _v) := (fun hn => hc (Or.inl hn))
  have h8038 : (e8038 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))))))
  have p21511 := n21511 _v _q h51 h91 h2402 h2529 h4306 h4653 h4813 h6525 h7807 h8038
  exact p21511
theorem n21514 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2402 : (e2402 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) (h8038 : (e8038 _v)) : (e2303 _v) := by
  have p21513 := n21513 _v _q 
  have p8602 := n8602 _v _q h8038
  have p8463 := n8463 _v _q h6525
  have p8591 := n8591 _v _q h2402
  have p4999 := n4999 _v _q h91
  have p16729 := n16729 _v _q h51
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4983 := n4983 _v _q h4813
  have p8548 := n8548 _v _q h2529
  change (e2303 _v) ∨ (¬ (e2529 _v)) ∨ (e2242 _v) ∨ (¬ (e2402 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (e2475 _v) at p21513
  change (¬ (e2475 _v)) at p8602
  change (¬ (e2242 _v)) at p8463
  rcases p21513 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p8548))
  · exact (False.elim (p8463 hlit))
  · exact (False.elim (hlit p8591))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (p8602 hlit))
end
end Assembly
