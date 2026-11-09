import Dag254
import generated.th_lemma_34
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n21611 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e5093 _v) := by
  have p11468 := n11468 _v _q 
  have p21601 := n21601 _v _q h51 h4306 h4653 h4813 h6525
  change (¬ (e13 _v)) ∨ (e2303 _v) at p11468
  change (¬ (e2303 _v)) at p21601
  rcases p11468 with hlit | hlit
  · exact hlit
  · exact (False.elim (p21601 hlit))
theorem n21612 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e5105 _v) := by
  have p15204 := n15204 _v _q 
  have p21611 := n21611 _v _q h51 h4306 h4653 h4813 h6525
  change (e13 _v) ∨ (¬ (e5104 _v)) at p15204
  change (¬ (e13 _v)) at p21611
  rcases p15204 with hlit | hlit
  · exact (False.elim (p21611 hlit))
  · exact hlit
theorem n21613 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e5100 _v) := by
  have p15319 := n15319 _v _q 
  have p21612 := n21612 _v _q h51 h4306 h4653 h4813 h6525
  change (e5104 _v) ∨ (e5100 _v) at p15319
  change (¬ (e5104 _v)) at p21612
  rcases p15319 with hlit | hlit
  · exact (False.elim (p21612 hlit))
  · exact hlit
theorem n21614 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e8050 _v) := by
  have p15207 := n15207 _v _q 
  have p21600 := n21600 _v _q h51 h4306 h4653 h4813 h6525
  change (e2475 _v) ∨ (¬ (e8049 _v)) at p15207
  change (¬ (e2475 _v)) at p21600
  rcases p15207 with hlit | hlit
  · exact (False.elim (p21600 hlit))
  · exact hlit
theorem n21615 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e8045 _v) := by
  have p15206 := n15206 _v _q 
  have p21614 := n21614 _v _q h51 h4306 h4653 h4813 h6525
  change (e8049 _v) ∨ (e8045 _v) at p15206
  change (¬ (e8049 _v)) at p21614
  rcases p15206 with hlit | hlit
  · exact (False.elim (p21614 hlit))
  · exact hlit
theorem n21616 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e7742 _v) := by
  have p11353 := n11353 _v _q 
  have p21601 := n21601 _v _q h51 h4306 h4653 h4813 h6525
  change (¬ (e2132 _v)) ∨ (e2303 _v) at p11353
  change (¬ (e2303 _v)) at p21601
  rcases p11353 with hlit | hlit
  · exact hlit
  · exact (False.elim (p21601 hlit))
theorem n21617 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e7754 _v) := by
  have p14942 := n14942 _v _q 
  have p21616 := n21616 _v _q h51 h4306 h4653 h4813 h6525
  change (e2132 _v) ∨ (¬ (e7753 _v)) at p14942
  change (¬ (e2132 _v)) at p21616
  rcases p14942 with hlit | hlit
  · exact (False.elim (p21616 hlit))
  · exact hlit
theorem n21618 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e7749 _v) := by
  have p14941 := n14941 _v _q 
  have p21617 := n21617 _v _q h51 h4306 h4653 h4813 h6525
  change (e7753 _v) ∨ (e7749 _v) at p14941
  change (¬ (e7753 _v)) at p21617
  rcases p14941 with hlit | hlit
  · exact (False.elim (p21617 hlit))
  · exact hlit
theorem n21619 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e7819 _v) := by
  have p14994 := n14994 _v _q 
  have p21601 := n21601 _v _q h51 h4306 h4653 h4813 h6525
  change (e2303 _v) ∨ (¬ (e7818 _v)) at p14994
  change (¬ (e2303 _v)) at p21601
  rcases p14994 with hlit | hlit
  · exact (False.elim (p21601 hlit))
  · exact hlit
theorem n21620 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e7814 _v) := by
  have p15221 := n15221 _v _q 
  have p21619 := n21619 _v _q h51 h4306 h4653 h4813 h6525
  change (e7818 _v) ∨ (e7814 _v) at p15221
  change (¬ (e7818 _v)) at p21619
  rcases p15221 with hlit | hlit
  · exact (False.elim (p21619 hlit))
  · exact hlit
theorem n21621 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6501 : (e6501 _v)) : (e7742 _v) := by
  have p11353 := n11353 _v _q 
  have p21602 := n21602 _v _q h51 h4306 h4653 h4813 h6501
  change (¬ (e2132 _v)) ∨ (e2303 _v) at p11353
  change (¬ (e2303 _v)) at p21602
  rcases p11353 with hlit | hlit
  · exact hlit
  · exact (False.elim (p21602 hlit))
theorem n21622 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6501 : (e6501 _v)) : (e7754 _v) := by
  have p14942 := n14942 _v _q 
  have p21621 := n21621 _v _q h51 h4306 h4653 h4813 h6501
  change (e2132 _v) ∨ (¬ (e7753 _v)) at p14942
  change (¬ (e2132 _v)) at p21621
  rcases p14942 with hlit | hlit
  · exact (False.elim (p21621 hlit))
  · exact hlit
theorem n21623 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6501 : (e6501 _v)) : (e7749 _v) := by
  have p14941 := n14941 _v _q 
  have p21622 := n21622 _v _q h51 h4306 h4653 h4813 h6501
  change (e7753 _v) ∨ (e7749 _v) at p14941
  change (¬ (e7753 _v)) at p21622
  rcases p14941 with hlit | hlit
  · exact (False.elim (p21622 hlit))
  · exact hlit
theorem n21624 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6501 : (e6501 _v)) : (e4420 _v) := by
  have p16832 := n16832 _v _q 
  have p21603 := n21603 _v _q h51 h4306 h4653 h4813 h6501
  have p21602 := n21602 _v _q h51 h4306 h4653 h4813 h6501
  change (e2303 _v) ∨ (¬ (e4419 _v)) ∨ (e2475 _v) at p16832
  change (¬ (e2475 _v)) at p21603
  change (¬ (e2303 _v)) at p21602
  rcases p16832 with hlit | hlit | hlit
  · exact (False.elim (p21602 hlit))
  · exact hlit
  · exact (False.elim (p21603 hlit))
theorem n21625 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6501 : (e6501 _v)) : (e7921 _v) := by
  have p16347 := n16347 _v _q 
  have p21624 := n21624 _v _q h51 h4306 h4653 h4813 h6501
  change (e7921 _v) ∨ (e4419 _v) at p16347
  change (¬ (e4419 _v)) at p21624
  rcases p16347 with hlit | hlit
  · exact hlit
  · exact (False.elim (p21624 hlit))
theorem n21626 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6501 : (e6501 _v)) : (e5093 _v) := by
  have p11468 := n11468 _v _q 
  have p21602 := n21602 _v _q h51 h4306 h4653 h4813 h6501
  change (¬ (e13 _v)) ∨ (e2303 _v) at p11468
  change (¬ (e2303 _v)) at p21602
  rcases p11468 with hlit | hlit
  · exact hlit
  · exact (False.elim (p21602 hlit))
theorem n21627 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6501 : (e6501 _v)) : (e5105 _v) := by
  have p15204 := n15204 _v _q 
  have p21626 := n21626 _v _q h51 h4306 h4653 h4813 h6501
  change (e13 _v) ∨ (¬ (e5104 _v)) at p15204
  change (¬ (e13 _v)) at p21626
  rcases p15204 with hlit | hlit
  · exact (False.elim (p21626 hlit))
  · exact hlit
theorem n21628 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6501 : (e6501 _v)) : (e5100 _v) := by
  have p15319 := n15319 _v _q 
  have p21627 := n21627 _v _q h51 h4306 h4653 h4813 h6501
  change (e5104 _v) ∨ (e5100 _v) at p15319
  change (¬ (e5104 _v)) at p21627
  rcases p15319 with hlit | hlit
  · exact (False.elim (p21627 hlit))
  · exact hlit
theorem n21629 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6501 : (e6501 _v)) : (e7819 _v) := by
  have p14994 := n14994 _v _q 
  have p21602 := n21602 _v _q h51 h4306 h4653 h4813 h6501
  change (e2303 _v) ∨ (¬ (e7818 _v)) at p14994
  change (¬ (e2303 _v)) at p21602
  rcases p14994 with hlit | hlit
  · exact (False.elim (p21602 hlit))
  · exact hlit
theorem n21630 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6501 : (e6501 _v)) : (e7814 _v) := by
  have p15221 := n15221 _v _q 
  have p21629 := n21629 _v _q h51 h4306 h4653 h4813 h6501
  change (e7818 _v) ∨ (e7814 _v) at p15221
  change (¬ (e7818 _v)) at p21629
  rcases p15221 with hlit | hlit
  · exact (False.elim (p21629 hlit))
  · exact hlit
theorem n21631 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6501 : (e6501 _v)) : (e8050 _v) := by
  have p15207 := n15207 _v _q 
  have p21603 := n21603 _v _q h51 h4306 h4653 h4813 h6501
  change (e2475 _v) ∨ (¬ (e8049 _v)) at p15207
  change (¬ (e2475 _v)) at p21603
  rcases p15207 with hlit | hlit
  · exact (False.elim (p21603 hlit))
  · exact hlit
theorem n21632 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6501 : (e6501 _v)) : (e8045 _v) := by
  have p15206 := n15206 _v _q 
  have p21631 := n21631 _v _q h51 h4306 h4653 h4813 h6501
  change (e8049 _v) ∨ (e8045 _v) at p15206
  change (¬ (e8049 _v)) at p21631
  rcases p15206 with hlit | hlit
  · exact (False.elim (p21631 hlit))
  · exact hlit
theorem n21633 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6501 : (e6501 _v)) : (e6724 _v) := by
  have p14112 := n14112 _v _q 
  have p21603 := n21603 _v _q h51 h4306 h4653 h4813 h6501
  change (¬ (e2691 _v)) ∨ (e2475 _v) at p14112
  change (¬ (e2475 _v)) at p21603
  rcases p14112 with hlit | hlit
  · exact hlit
  · exact (False.elim (p21603 hlit))
theorem n21634 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2296 : (e2296 _v)) (h2529 : (e2529 _v)) (h4264 : (e4264 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h8038 : (e8038 _v)) : (e2402 _v) := by
  have p21605 := n21605 _v _q 
  have p8602 := n8602 _v _q h8038
  have p17118 := n17118 _v _q h4264
  have p17060 := n17060 _v _q h4653
  have p8583 := n8583 _v _q h2296
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p8548 := n8548 _v _q h2529
  have p17138 := n17138 _v _q h4306
  have p4999 := n4999 _v _q h91
  change (e2402 _v) ∨ (¬ (e4306 _v)) ∨ (¬ (e4264 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e2296 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e2529 _v)) ∨ (e2475 _v) ∨ (¬ (e91 _v)) at p21605
  change (¬ (e2475 _v)) at p8602
  rcases p21605 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17118))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p8583))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p8548))
  · exact (False.elim (p8602 hlit))
  · exact (False.elim (hlit p4999))
theorem n21635 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2296 : (e2296 _v)) (h2529 : (e2529 _v)) (h4264 : (e4264 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h8038 : (e8038 _v)) : (e3929 _v) := by
  have p14484 := n14484 _v _q 
  have p21634 := n21634 _v _q h51 h91 h2296 h2529 h4264 h4306 h4653 h4813 h8038
  change (¬ (e2402 _v)) ∨ (¬ (e3923 _v)) at p14484
  rcases p14484 with hlit | hlit
  · exact (False.elim (hlit p21634))
  · exact hlit
theorem n21636 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6454 : (e6454 _v)) : (e7495 _v) := by
  have p16733 := n16733 _v _q 
  have p21608 := n21608 _v _q h51 h4306 h4653 h4813 h6454
  change (e7497 _v) ∨ (e7495 _v) at p16733
  change (¬ (e7497 _v)) at p21608
  rcases p16733 with hlit | hlit
  · exact (False.elim (p21608 hlit))
  · exact hlit
theorem n21637 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6454 : (e6454 _v)) : (e48 _v) := by
  have p16732 := n16732 _v _q 
  have p21636 := n21636 _v _q h51 h4306 h4653 h4813 h6454
  have p16729 := n16729 _v _q h51
  change (e48 _v) ∨ (¬ (e7495 _v)) ∨ (¬ (e51 _v)) at p16732
  rcases p16732 with hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p21636))
  · exact (False.elim (hlit p16729))
theorem n21638 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6454 : (e6454 _v)) : (e2585 _v) := by
  have p11550 := n11550 _v _q 
  have p21637 := n21637 _v _q h51 h4306 h4653 h4813 h6454
  change (e2585 _v) ∨ (¬ (e48 _v)) at p11550
  rcases p11550 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p21637))
theorem n21639 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e6772 _v) := by
  have p14855 := n14855 _v _q 
  have p21610 := n21610 _v _q h51 h4306 h4653 h4813 h6525
  change (¬ (e2787 _v)) ∨ (¬ (e7921 _v)) at p14855
  rcases p14855 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p21610))
theorem n21640 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e7945 _v) := by
  have p15228 := n15228 _v _q 
  have p21639 := n21639 _v _q h51 h4306 h4653 h4813 h6525
  change (e2787 _v) ∨ (¬ (e7944 _v)) at p15228
  change (¬ (e2787 _v)) at p21639
  rcases p15228 with hlit | hlit
  · exact (False.elim (p21639 hlit))
  · exact hlit
theorem n21641 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e7935 _v) := by
  have p15266 := n15266 _v _q 
  have p21640 := n21640 _v _q h51 h4306 h4653 h4813 h6525
  change (e7944 _v) ∨ (e7935 _v) at p15266
  change (¬ (e7944 _v)) at p21640
  rcases p15266 with hlit | hlit
  · exact (False.elim (p21640 hlit))
  · exact hlit
theorem n21642 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6501 : (e6501 _v)) : (e6772 _v) := by
  have p14855 := n14855 _v _q 
  have p21625 := n21625 _v _q h51 h4306 h4653 h4813 h6501
  change (¬ (e2787 _v)) ∨ (¬ (e7921 _v)) at p14855
  rcases p14855 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p21625))
theorem n21643 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6501 : (e6501 _v)) : (e7945 _v) := by
  have p15228 := n15228 _v _q 
  have p21642 := n21642 _v _q h51 h4306 h4653 h4813 h6501
  change (e2787 _v) ∨ (¬ (e7944 _v)) at p15228
  change (¬ (e2787 _v)) at p21642
  rcases p15228 with hlit | hlit
  · exact (False.elim (p21642 hlit))
  · exact hlit
theorem n21644 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6501 : (e6501 _v)) : (e7935 _v) := by
  have p15266 := n15266 _v _q 
  have p21643 := n21643 _v _q h51 h4306 h4653 h4813 h6501
  change (e7944 _v) ∨ (e7935 _v) at p15266
  change (¬ (e7944 _v)) at p21643
  rcases p15266 with hlit | hlit
  · exact (False.elim (p21643 hlit))
  · exact hlit
theorem n21645 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6501 : (e6501 _v)) : (e7517 _v) := by
  have p15196 := n15196 _v _q 
  have p21633 := n21633 _v _q h51 h4306 h4653 h4813 h6501
  change (e2691 _v) ∨ (¬ (e7497 _v)) at p15196
  change (¬ (e2691 _v)) at p21633
  rcases p15196 with hlit | hlit
  · exact (False.elim (p21633 hlit))
  · exact hlit
theorem n21646 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6501 : (e6501 _v)) : (e7495 _v) := by
  have p16733 := n16733 _v _q 
  have p21645 := n21645 _v _q h51 h4306 h4653 h4813 h6501
  change (e7497 _v) ∨ (e7495 _v) at p16733
  change (¬ (e7497 _v)) at p21645
  rcases p16733 with hlit | hlit
  · exact (False.elim (p21645 hlit))
  · exact hlit
theorem n21647 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2296 : (e2296 _v)) (h2529 : (e2529 _v)) (h4264 : (e4264 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h8038 : (e8038 _v)) : (e3919 _v) := by
  have p14797 := n14797 _v _q 
  have p21635 := n21635 _v _q h51 h91 h2296 h2529 h4264 h4306 h4653 h4813 h8038
  change (e3923 _v) ∨ (e3919 _v) at p14797
  change (¬ (e3923 _v)) at p21635
  rcases p14797 with hlit | hlit
  · exact (False.elim (p21635 hlit))
  · exact hlit
theorem n21648 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2296 : (e2296 _v)) (h2529 : (e2529 _v)) (h4264 : (e4264 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h8038 : (e8038 _v)) : (e7489 _v) := by
  have p258 := n258 _v _q 
  have p8583 := n8583 _v _q h2296
  have p20827 := n20827 _v _q 
  have p8602 := n8602 _v _q h8038
  have p21647 := n21647 _v _q h51 h91 h2296 h2529 h4264 h4306 h4653 h4813 h8038
  have p17138 := n17138 _v _q h4306
  have p17118 := n17118 _v _q h4264
  have p21597 := n21597 _v _q h51 h91 h2529 h4306 h4653 h4813
  have p17060 := n17060 _v _q h4653
  have p13951 := n13951 _v _q 
  have p16572 := n16572 _v _q h2529
  have p15100 := n15100 _v _q h2296
  have p17050 := n17050 _v _q 
  have p16778 := n16778 _v _q 
  have p17122 := n17122 _v _q 
  have p4983 := n4983 _v _q h4813
  have p17256 := n17256 _v _q 
  have p20829 := n20829 _v _q 
  have p21574 := n21574 _v _q h51 h91 h2529 h4306 h4653 h4813
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
  have p8548 := n8548 _v _q h2529
  have p17055 := n17055 _v _q 
  have p17093 := n17093 _v _q 
  have p17091 := n17091 _v _q 
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p21577 := n21577 _v _q h51 h91 h2529 h4306 h4653 h4813
  have p21579 := n21579 _v _q h51 h91 h2529 h4306 h4653 h4813
  have p17141 := n17141 _v _q 
  have p17100 := n17100 _v _q 
  have p19610 := n19610 _v _q 
  have p17102 := n17102 _v _q 
  have p21190 := n21190 _v _q h51 h91 h2529 h4306 h4653 h4813
  have p15209 := n15209 _v _q h8038
  have p21581 := n21581 _v _q h51 h91 h2529 h4306 h4653 h4813
  have p16729 := n16729 _v _q h51
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
  have p5255 := n5255 _v _q 
  exact FloorCertificate.node_21648 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2902 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e4541 _v) (e4808 _v) p258 p8583 p20827 p8602 p21647 p17138 p17118 p21597 p17060 p13951 p16572 p15100 p17050 p16778 p17122 p4983 p17256 p20829 p21574 p20426 p20126 p17110 p15113 p17053 p20096 p17131 p17108 p17294 p16943 p17058 p17064 p17067 p17080 p17072 p17074 p17069 p20461 p20836 p20653 p17078 p17136 p17087 p17083 p8548 p17055 p17093 p17091 p17098 p17106 p21577 p21579 p17141 p17100 p19610 p17102 p21190 p15209 p21581 p16729 p17096 p17115 p17758 p17124 p17111 p19665 p17113 p17117 p20467 p17120 p4999 p17133 p17874 p17104 p17127 p17089 p20470 p16705 p17020 p20274 p5255
theorem n21649 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6454 : (e6454 _v)) : (e8038 _v) := by
  have p8574 := n8574 _v _q 
  have p21638 := n21638 _v _q h51 h4306 h4653 h4813 h6454
  have p8430 := n8430 _v _q h6454
  change (¬ (e2475 _v)) ∨ (¬ (e2585 _v)) ∨ (e2061 _v) at p8574
  change (¬ (e2061 _v)) at p8430
  rcases p8574 with hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p21638))
  · exact (False.elim (p8430 hlit))
theorem n21650 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6454 : (e6454 _v)) : (e4420 _v) := by
  have p16832 := n16832 _v _q 
  have p21649 := n21649 _v _q h51 h4306 h4653 h4813 h6454
  have p21599 := n21599 _v _q h51 h4306 h4653 h4813 h6454
  change (e2303 _v) ∨ (¬ (e4419 _v)) ∨ (e2475 _v) at p16832
  change (¬ (e2475 _v)) at p21649
  change (¬ (e2303 _v)) at p21599
  rcases p16832 with hlit | hlit | hlit
  · exact (False.elim (p21599 hlit))
  · exact hlit
  · exact (False.elim (p21649 hlit))
theorem n21652 (_v : Vars) (_q : Query _v)  : (e21651 _v) := by
  by_contra hc
  change ¬ ((e2475 _v) ∨ (¬ (e2296 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4264 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e2529 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e91 _v))) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn)))))))))
  have h2296 : (e2296 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h2529 : (e2529 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h4264 : (e4264 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h8038 : (e8038 _v) := (fun hn => hc (Or.inl hn))
  have p21648 := n21648 _v _q h51 h91 h2296 h2529 h4264 h4306 h4653 h4813 h8038
  exact p21648
theorem n21653 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6454 : (e6454 _v)) : (e7921 _v) := by
  have p16347 := n16347 _v _q 
  have p21650 := n21650 _v _q h51 h4306 h4653 h4813 h6454
  change (e7921 _v) ∨ (e4419 _v) at p16347
  change (¬ (e4419 _v)) at p21650
  rcases p16347 with hlit | hlit
  · exact hlit
  · exact (False.elim (p21650 hlit))
theorem n21654 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6454 : (e6454 _v)) : (e6772 _v) := by
  have p14855 := n14855 _v _q 
  have p21653 := n21653 _v _q h51 h4306 h4653 h4813 h6454
  change (¬ (e2787 _v)) ∨ (¬ (e7921 _v)) at p14855
  rcases p14855 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p21653))
theorem n21655 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6454 : (e6454 _v)) : (e7945 _v) := by
  have p15228 := n15228 _v _q 
  have p21654 := n21654 _v _q h51 h4306 h4653 h4813 h6454
  change (e2787 _v) ∨ (¬ (e7944 _v)) at p15228
  change (¬ (e2787 _v)) at p21654
  rcases p15228 with hlit | hlit
  · exact (False.elim (p21654 hlit))
  · exact hlit
theorem n21656 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2296 : (e2296 _v)) (h2529 : (e2529 _v)) (h4264 : (e4264 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e2475 _v) := by
  have p21652 := n21652 _v _q 
  have p17118 := n17118 _v _q h4264
  have p17138 := n17138 _v _q h4306
  have p8583 := n8583 _v _q h2296
  have p17060 := n17060 _v _q h4653
  have p4983 := n4983 _v _q h4813
  have p8548 := n8548 _v _q h2529
  have p16729 := n16729 _v _q h51
  have p4999 := n4999 _v _q h91
  change (e2475 _v) ∨ (¬ (e2296 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4264 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e2529 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e91 _v)) at p21652
  rcases p21652 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p8583))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17118))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p8548))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p4999))
end
end Assembly
