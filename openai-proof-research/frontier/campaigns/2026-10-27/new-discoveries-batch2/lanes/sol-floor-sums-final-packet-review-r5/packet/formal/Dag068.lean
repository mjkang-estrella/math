import Dag067
import generated.th_lemma_3
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n11553 (_v : Vars) (_q : Query _v)  : (e11552 _v) := by
  by_contra hc
  change ¬ ((e2242 _v) ∨ (¬ (e2781 _v)) ∨ (¬ (e2303 _v))) at hc
  have h2303 : (e2303 _v) := by
    tauto
  have h2781 : (e2781 _v) := by
    tauto
  have h6525 : (e6525 _v) := by
    change (¬ (e2242 _v))
    tauto
  have p11551 := n11551 _v _q h2303 h2781 h6525
  exact p11551
theorem n11554 (_v : Vars) (_q : Query _v) (h196 : (e196 _v)) (h2781 : (e2781 _v)) (h8038 : (e8038 _v)) : (e2585 _v) := by
  have p8140 := n8140 _v _q h196
  have p8602 := n8602 _v _q h8038
  have p5255 := n5255 _v _q 
  have p8421 := n8421 _v _q h2781
  exact FloorCertificate.node_11554 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8140 p8602 p5255 p8421
theorem n11555 (_v : Vars) (_q : Query _v) (h2132 : (e2132 _v)) (h2733 : (e2733 _v)) (h6600 : (e6600 _v)) : (e7489 _v) := by
  have p5255 := n5255 _v _q 
  have p8439 := n8439 _v _q h6600
  have p8587 := n8587 _v _q h2733
  have p5257 := n5257 _v _q 
  have p11349 := n11349 _v _q h2132
  exact FloorCertificate.node_11555 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p5255 p8439 p8587 p5257 p11349
theorem n11557 (_v : Vars) (_q : Query _v)  : (e11556 _v) := by
  by_contra hc
  change ¬ ((e2402 _v) ∨ (¬ (e2733 _v)) ∨ (¬ (e2132 _v))) at hc
  have h2132 : (e2132 _v) := by
    tauto
  have h2733 : (e2733 _v) := by
    tauto
  have h6600 : (e6600 _v) := by
    change (¬ (e2402 _v))
    tauto
  have p11555 := n11555 _v _q h2132 h2733 h6600
  exact p11555
theorem n11558 (_v : Vars) (_q : Query _v) (h2296 : (e2296 _v)) (h6525 : (e6525 _v)) : (e7489 _v) := by
  have p5257 := n5257 _v _q 
  have p8463 := n8463 _v _q h6525
  have p8583 := n8583 _v _q h2296
  exact FloorCertificate.node_11558 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e110 _v) p5257 p8463 p8583
theorem n11560 (_v : Vars) (_q : Query _v)  : (e11559 _v) := by
  by_contra hc
  change ¬ ((¬ (e2296 _v)) ∨ (e2242 _v)) at hc
  have h2296 : (e2296 _v) := by
    tauto
  have h6525 : (e6525 _v) := by
    change (¬ (e2242 _v))
    tauto
  have p11558 := n11558 _v _q h2296 h6525
  exact p11558
theorem n11561 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) (h6454 : (e6454 _v)) : (e7489 _v) := by
  have p5255 := n5255 _v _q 
  have p8438 := n8438 _v _q h2468
  have p8430 := n8430 _v _q h6454
  have p4016 := n4016 _v _q 
  have p5391 := n5391 _v _q 
  exact FloorCertificate.node_11561 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p5255 p8438 p8430 p4016 p5391
theorem n11563 (_v : Vars) (_q : Query _v)  : (e11562 _v) := by
  by_contra hc
  change ¬ ((e2061 _v) ∨ (¬ (e2468 _v))) at hc
  have h2468 : (e2468 _v) := by
    tauto
  have h6454 : (e6454 _v) := by
    change (¬ (e2061 _v))
    tauto
  have p11561 := n11561 _v _q h2468 h6454
  exact p11561
theorem n11564 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) (h6525 : (e6525 _v)) : (e7489 _v) := by
  have p5391 := n5391 _v _q 
  have p8463 := n8463 _v _q h6525
  have p8438 := n8438 _v _q h2468
  exact FloorCertificate.node_11564 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) p5391 p8463 p8438
theorem n11566 (_v : Vars) (_q : Query _v)  : (e11565 _v) := by
  by_contra hc
  change ¬ ((e2242 _v) ∨ (¬ (e2468 _v))) at hc
  have h2468 : (e2468 _v) := by
    tauto
  have h6525 : (e6525 _v) := by
    change (¬ (e2242 _v))
    tauto
  have p11564 := n11564 _v _q h2468 h6525
  exact p11564
theorem n11567 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) (h6776 : (e6776 _v)) : (e2303 _v) := by
  have p8601 := n8601 _v _q h6776
  have p8438 := n8438 _v _q h2468
  exact FloorCertificate.node_11567 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8601 p8438
theorem n11568 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) (h6776 : (e6776 _v)) : (e2358 _v) := by
  have p8451 := n8451 _v _q 
  have p11567 := n11567 _v _q h2468 h6776
  simp only [e2303, e2358, e7807, e8450] at *
  tauto
theorem n11569 (_v : Vars) (_q : Query _v) (h2296 : (e2296 _v)) (h6750 : (e6750 _v)) : (e7489 _v) := by
  have p8420 := n8420 _v _q h6750
  have p8583 := n8583 _v _q h2296
  have p10893 := n10893 _v _q 
  exact FloorCertificate.node_11569 (e2 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8420 p8583 p10893
theorem n11571 (_v : Vars) (_q : Query _v)  : (e11570 _v) := by
  by_contra hc
  change ¬ ((e2733 _v) ∨ (¬ (e2296 _v))) at hc
  have h2296 : (e2296 _v) := by
    tauto
  have h6750 : (e6750 _v) := by
    change (¬ (e2733 _v))
    tauto
  have p11569 := n11569 _v _q h2296 h6750
  exact p11569
theorem n11573 (_v : Vars) (_q : Query _v)  : (e11572 _v) := by
  have p25 := n25 _v _q 
  have p8613 := n8613 _v _q 
  exact (Iff.trans p25 p8613)
theorem n11574 (_v : Vars) (_q : Query _v)  : (e5097 _v) := by
  simp only [e5, e6, e36, e37, e38, e39, e40, e5083, e5097] at *
  omega
theorem n11576 (_v : Vars) (_q : Query _v)  : (e11575 _v) := by
  have p8618 := n8618 _v _q 
  have p8620 := n8620 _v _q 
  exact (Iff.trans p8618 p8620)
theorem n11577 (_v : Vars) (_q : Query _v)  : (e8621 _v) := by
  have p11574 := n11574 _v _q 
  have p11576 := n11576 _v _q 
  exact (Iff.trans p11574 p11576)
theorem n11579 (_v : Vars) (_q : Query _v)  : (e11578 _v) := by
  have p11577 := n11577 _v _q 
  change ((e5083 _v) ↔ (e5105 _v)) at p11577
  simp only [e11578, e5084, e8622, p11577]
theorem n11583 (_v : Vars) (_q : Query _v)  : (e11582 _v) := by
  have p67 := n67 _v _q 
  have p8632 := n8632 _v _q 
  exact (Iff.trans p67 p8632)
theorem n11585 (_v : Vars) (_q : Query _v)  : (e11584 _v) := by
  have p86 := n86 _v _q 
  have p8638 := n8638 _v _q 
  exact (Iff.trans p86 p8638)
theorem n11586 (_v : Vars) (_q : Query _v)  : (e5142 _v) := by
  simp only [e5, e6, e36, e96, e97, e98, e99, e5128, e5142] at *
  omega
theorem n11588 (_v : Vars) (_q : Query _v)  : (e11587 _v) := by
  have p8643 := n8643 _v _q 
  have p8645 := n8645 _v _q 
  exact (Iff.trans p8643 p8645)
theorem n11589 (_v : Vars) (_q : Query _v)  : (e8646 _v) := by
  have p11586 := n11586 _v _q 
  have p11588 := n11588 _v _q 
  exact (Iff.trans p11586 p11588)
theorem n11591 (_v : Vars) (_q : Query _v)  : (e11590 _v) := by
  have p11589 := n11589 _v _q 
  change ((e5128 _v) ↔ (e5150 _v)) at p11589
  simp only [e11590, e5129, e8647, p11589]
theorem n11595 (_v : Vars) (_q : Query _v)  : (e11594 _v) := by
  have p125 := n125 _v _q 
  have p8657 := n8657 _v _q 
  exact (Iff.trans p125 p8657)
theorem n11597 (_v : Vars) (_q : Query _v)  : (e11596 _v) := by
  have p204 := n204 _v _q 
  have p8665 := n8665 _v _q 
  exact (Iff.trans p204 p8665)
theorem n11599 (_v : Vars) (_q : Query _v)  : (e11598 _v) := by
  simp only [e5, e6, e36, e197, e198, e208, e209, e5214, e11598] at *
  omega
theorem n11601 (_v : Vars) (_q : Query _v)  : (e11600 _v) := by
  have p5217 := n5217 _v _q 
  have p8667 := n8667 _v _q 
  exact (Iff.trans p5217 p8667)
theorem n11603 (_v : Vars) (_q : Query _v)  : (e11602 _v) := by
  have p11599 := n11599 _v _q 
  have p11601 := n11601 _v _q 
  exact (Iff.trans p11599 p11601)
theorem n11605 (_v : Vars) (_q : Query _v)  : (e11604 _v) := by
  have p222 := n222 _v _q 
  have p8674 := n8674 _v _q 
  exact (Iff.trans p222 p8674)
theorem n11607 (_v : Vars) (_q : Query _v)  : (e11606 _v) := by
  simp only [e5, e6, e36, e215, e216, e232, e233, e5243, e11606] at *
  omega
theorem n11609 (_v : Vars) (_q : Query _v)  : (e11608 _v) := by
  have p5246 := n5246 _v _q 
  have p8676 := n8676 _v _q 
  exact (Iff.trans p5246 p8676)
theorem n11611 (_v : Vars) (_q : Query _v)  : (e11610 _v) := by
  have p11607 := n11607 _v _q 
  have p11609 := n11609 _v _q 
  exact (Iff.trans p11607 p11609)
theorem n11613 (_v : Vars) (_q : Query _v)  : (e11612 _v) := by
  have p281 := n281 _v _q 
  have p8693 := n8693 _v _q 
  exact (Iff.trans p281 p8693)
theorem n11615 (_v : Vars) (_q : Query _v)  : (e11614 _v) := by
  have p317 := n317 _v _q 
  have p8701 := n8701 _v _q 
  exact (Iff.trans p317 p8701)
theorem n11617 (_v : Vars) (_q : Query _v)  : (e11616 _v) := by
  have p352 := n352 _v _q 
  have p8709 := n8709 _v _q 
  exact (Iff.trans p352 p8709)
theorem n11619 (_v : Vars) (_q : Query _v)  : (e11618 _v) := by
  have p382 := n382 _v _q 
  have p8717 := n8717 _v _q 
  exact (Iff.trans p382 p8717)
theorem n11621 (_v : Vars) (_q : Query _v)  : (e11620 _v) := by
  have p425 := n425 _v _q 
  have p8726 := n8726 _v _q 
  exact (Iff.trans p425 p8726)
theorem n11623 (_v : Vars) (_q : Query _v)  : (e11622 _v) := by
  simp only [e5, e6, e12, e41, e266, e267, e404, e405, e406, e407, e408, e410, e411, e412, e420, e426, e427, e428, e430, e433, e434, e5355, e5356, e5359, e8722, e8727, e8729, e8730, e8731, e8732, e11622] at *
  omega
theorem n11625 (_v : Vars) (_q : Query _v)  : (e411 _v) := by
  have p8663 := n8663 _v _q 
  have p331 := n331 _v _q 
  exact FloorCertificate.node_11625 (e2 _v) (e17 _v) p8663 p331
theorem n11627 (_v : Vars) (_q : Query _v)  : (e11626 _v) := by
  have p451 := n451 _v _q 
  have p8734 := n8734 _v _q 
  exact (Iff.trans p451 p8734)
theorem n11629 (_v : Vars) (_q : Query _v)  : (e11628 _v) := by
  simp only [e5, e6, e36, e444, e445, e455, e456, e5381, e11628] at *
  omega
theorem n11631 (_v : Vars) (_q : Query _v)  : (e11630 _v) := by
  have p5384 := n5384 _v _q 
  have p8736 := n8736 _v _q 
  exact (Iff.trans p5384 p8736)
theorem n11633 (_v : Vars) (_q : Query _v)  : (e11632 _v) := by
  have p11629 := n11629 _v _q 
  have p11631 := n11631 _v _q 
  exact (Iff.trans p11629 p11631)
end
end Assembly
