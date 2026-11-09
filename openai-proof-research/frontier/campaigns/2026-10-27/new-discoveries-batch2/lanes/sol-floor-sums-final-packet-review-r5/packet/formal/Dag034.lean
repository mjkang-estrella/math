import Dag033
import generated.th_lemma_0
import generated.th_lemma_1
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n8552 (_v : Vars) (_q : Query _v)  : (e8551 _v) := by
  by_contra hc
  change ¬ ((¬ (e2529 _v)) ∨ (e196 _v)) at hc
  have h2529 : (e2529 _v) := by
    tauto
  have h5195 : (e5195 _v) := by
    change (¬ (e196 _v))
    tauto
  have p8550 := n8550 _v _q h2529 h5195
  exact p8550
theorem n8553 (_v : Vars) (_q : Query _v) (h2242 : (e2242 _v)) : (e2242 _v) := by
  exact h2242
theorem n8554 (_v : Vars) (_q : Query _v) (h6501 : (e6501 _v)) : (e6501 _v) := by
  exact h6501
theorem n8555 (_v : Vars) (_q : Query _v) (h2242 : (e2242 _v)) (h6501 : (e6501 _v)) : (e7489 _v) := by
  have p8553 := n8553 _v _q h2242
  have p8554 := n8554 _v _q h6501
  have p4016 := n4016 _v _q 
  exact FloorCertificate.node_8555 (e2 _v) (e7 _v) (e9 _v) (e17 _v) p8553 p8554 p4016
theorem n8557 (_v : Vars) (_q : Query _v)  : (e8556 _v) := by
  by_contra hc
  change ¬ ((¬ (e2242 _v)) ∨ (e2179 _v)) at hc
  have h2242 : (e2242 _v) := by
    tauto
  have h6501 : (e6501 _v) := by
    change (¬ (e2179 _v))
    tauto
  have p8555 := n8555 _v _q h2242 h6501
  exact p8555
theorem n8569 (_v : Vars) (_q : Query _v)  : (e8568 _v) := by
  simp only [e4156, e4157, e4158, e4159, e7660, e7668, e8568] at *
  tauto
theorem n8572 (_v : Vars) (_q : Query _v) (h2475 : (e2475 _v)) (h2585 : (e2585 _v)) (h6454 : (e6454 _v)) : (e7489 _v) := by
  have p8457 := n8457 _v _q h2475
  have p8532 := n8532 _v _q h2585
  have p8430 := n8430 _v _q h6454
  exact FloorCertificate.node_8572 (e2 _v) (e7 _v) (e17 _v) (e45 _v) (e110 _v) p8457 p8532 p8430
theorem n8574 (_v : Vars) (_q : Query _v)  : (e8573 _v) := by
  by_contra hc
  change ¬ ((¬ (e2475 _v)) ∨ (¬ (e2585 _v)) ∨ (e2061 _v)) at hc
  have h2475 : (e2475 _v) := by
    tauto
  have h2585 : (e2585 _v) := by
    tauto
  have h6454 : (e6454 _v) := by
    change (¬ (e2061 _v))
    tauto
  have p8572 := n8572 _v _q h2475 h2585 h6454
  exact p8572
theorem n8575 (_v : Vars) (_q : Query _v) (h6480 : (e6480 _v)) : (e6480 _v) := by
  exact h6480
theorem n8576 (_v : Vars) (_q : Query _v) (h79 : (e79 _v)) (h2781 : (e2781 _v)) (h6480 : (e6480 _v)) : (e7489 _v) := by
  have p7487 := n7487 _v _q h79
  have p8421 := n8421 _v _q h2781
  have p8575 := n8575 _v _q h6480
  exact FloorCertificate.node_8576 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p7487 p8421 p8575
theorem n8578 (_v : Vars) (_q : Query _v)  : (e8577 _v) := by
  by_contra hc
  change ¬ ((e2125 _v) ∨ (¬ (e79 _v)) ∨ (¬ (e2781 _v))) at hc
  have h79 : (e79 _v) := by
    tauto
  have h2781 : (e2781 _v) := by
    tauto
  have h6480 : (e6480 _v) := by
    change (¬ (e2125 _v))
    tauto
  have p8576 := n8576 _v _q h79 h2781 h6480
  exact p8576
theorem n8579 (_v : Vars) (_q : Query _v) (h2303 : (e2303 _v)) (h2781 : (e2781 _v)) (h6630 : (e6630 _v)) : (e7489 _v) := by
  have p8421 := n8421 _v _q h2781
  have p8448 := n8448 _v _q h2303
  have p8434 := n8434 _v _q h6630
  exact FloorCertificate.node_8579 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8421 p8448 p8434
theorem n8581 (_v : Vars) (_q : Query _v)  : (e8580 _v) := by
  by_contra hc
  change ¬ ((e2468 _v) ∨ (¬ (e2781 _v)) ∨ (¬ (e2303 _v))) at hc
  have h2303 : (e2303 _v) := by
    tauto
  have h2781 : (e2781 _v) := by
    tauto
  have h6630 : (e6630 _v) := by
    change (¬ (e2468 _v))
    tauto
  have p8579 := n8579 _v _q h2303 h2781 h6630
  exact p8579
theorem n8583 (_v : Vars) (_q : Query _v) (h2296 : (e2296 _v)) : (e2296 _v) := by
  exact h2296
theorem n8584 (_v : Vars) (_q : Query _v) (h2296 : (e2296 _v)) (h2468 : (e2468 _v)) (h6750 : (e6750 _v)) : (e7489 _v) := by
  have p4016 := n4016 _v _q 
  have p258 := n258 _v _q 
  have p8420 := n8420 _v _q h6750
  have p8583 := n8583 _v _q h2296
  have p8438 := n8438 _v _q h2468
  exact FloorCertificate.node_8584 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p4016 p258 p8420 p8583 p8438
theorem n8586 (_v : Vars) (_q : Query _v)  : (e8585 _v) := by
  by_contra hc
  change ¬ ((¬ (e2296 _v)) ∨ (e2733 _v) ∨ (¬ (e2468 _v))) at hc
  have h2296 : (e2296 _v) := by
    tauto
  have h2468 : (e2468 _v) := by
    tauto
  have h6750 : (e6750 _v) := by
    change (¬ (e2733 _v))
    tauto
  have p8584 := n8584 _v _q h2296 h2468 h6750
  exact p8584
theorem n8587 (_v : Vars) (_q : Query _v) (h2733 : (e2733 _v)) : (e2733 _v) := by
  exact h2733
theorem n8588 (_v : Vars) (_q : Query _v) (h2529 : (e2529 _v)) (h2733 : (e2733 _v)) (h6501 : (e6501 _v)) : (e7489 _v) := by
  have p8548 := n8548 _v _q h2529
  have p8554 := n8554 _v _q h6501
  have p8587 := n8587 _v _q h2733
  exact FloorCertificate.node_8588 (e2 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8548 p8554 p8587
theorem n8590 (_v : Vars) (_q : Query _v)  : (e8589 _v) := by
  by_contra hc
  change ¬ ((e2179 _v) ∨ (¬ (e2529 _v)) ∨ (¬ (e2733 _v))) at hc
  have h2529 : (e2529 _v) := by
    tauto
  have h2733 : (e2733 _v) := by
    tauto
  have h6501 : (e6501 _v) := by
    change (¬ (e2179 _v))
    tauto
  have p8588 := n8588 _v _q h2529 h2733 h6501
  exact p8588
theorem n8591 (_v : Vars) (_q : Query _v) (h2402 : (e2402 _v)) : (e2402 _v) := by
  exact h2402
theorem n8592 (_v : Vars) (_q : Query _v) (h2402 : (e2402 _v)) (h2529 : (e2529 _v)) (h6525 : (e6525 _v)) (h6571 : (e6571 _v)) : (e7489 _v) := by
  have p8463 := n8463 _v _q h6525
  have p8447 := n8447 _v _q h6571
  have p8548 := n8548 _v _q h2529
  have p8591 := n8591 _v _q h2402
  exact FloorCertificate.node_8592 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8463 p8447 p8548 p8591
theorem n8594 (_v : Vars) (_q : Query _v)  : (e8593 _v) := by
  by_contra hc
  change ¬ ((¬ (e2402 _v)) ∨ (e2242 _v) ∨ (e2358 _v) ∨ (¬ (e2529 _v))) at hc
  have h2402 : (e2402 _v) := by
    tauto
  have h2529 : (e2529 _v) := by
    tauto
  have h6525 : (e6525 _v) := by
    change (¬ (e2242 _v))
    tauto
  have h6571 : (e6571 _v) := by
    change (¬ (e2358 _v))
    tauto
  have p8592 := n8592 _v _q h2402 h2529 h6525 h6571
  exact p8592
theorem n8595 (_v : Vars) (_q : Query _v) (h2402 : (e2402 _v)) (h2475 : (e2475 _v)) (h6549 : (e6549 _v)) (h6571 : (e6571 _v)) : (e7489 _v) := by
  have p8447 := n8447 _v _q h6571
  have p8591 := n8591 _v _q h2402
  have p8457 := n8457 _v _q h2475
  have p8544 := n8544 _v _q h6549
  exact FloorCertificate.node_8595 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8447 p8591 p8457 p8544
theorem n8597 (_v : Vars) (_q : Query _v)  : (e8596 _v) := by
  by_contra hc
  change ¬ ((e2358 _v) ∨ (¬ (e2402 _v)) ∨ (¬ (e2475 _v)) ∨ (e2296 _v)) at hc
  have h2402 : (e2402 _v) := by
    tauto
  have h2475 : (e2475 _v) := by
    tauto
  have h6549 : (e6549 _v) := by
    change (¬ (e2296 _v))
    tauto
  have h6571 : (e6571 _v) := by
    change (¬ (e2358 _v))
    tauto
  have p8595 := n8595 _v _q h2402 h2475 h6549 h6571
  exact p8595
theorem n8601 (_v : Vars) (_q : Query _v) (h6776 : (e6776 _v)) : (e6776 _v) := by
  exact h6776
theorem n8602 (_v : Vars) (_q : Query _v) (h8038 : (e8038 _v)) : (e8038 _v) := by
  exact h8038
theorem n8603 (_v : Vars) (_q : Query _v) (h2296 : (e2296 _v)) (h6776 : (e6776 _v)) (h8038 : (e8038 _v)) : (e7489 _v) := by
  have p8601 := n8601 _v _q h6776
  have p8583 := n8583 _v _q h2296
  have p8602 := n8602 _v _q h8038
  exact FloorCertificate.node_8603 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8601 p8583 p8602
theorem n8605 (_v : Vars) (_q : Query _v)  : (e8604 _v) := by
  by_contra hc
  change ¬ ((e2781 _v) ∨ (¬ (e2296 _v)) ∨ (e2475 _v)) at hc
  have h2296 : (e2296 _v) := by
    tauto
  have h6776 : (e6776 _v) := by
    change (¬ (e2781 _v))
    tauto
  have h8038 : (e8038 _v) := by
    change (¬ (e2475 _v))
    tauto
  have p8603 := n8603 _v _q h2296 h6776 h8038
  exact p8603
theorem n8608 (_v : Vars) (_q : Query _v) (h2242 : (e2242 _v)) : (e8607 _v) := by
  have p8139 := n8139 _v _q 
  have p8553 := n8553 _v _q h2242
  exact FloorCertificate.node_8608 (e2 _v) (e7 _v) (e9 _v) (e17 _v) p8139 p8553
theorem n8611 (_v : Vars) (_q : Query _v)  : (e8610 _v) := by
  simp only [e13, e16, e18, e5083, e5084, e5093, e5094, e8610] at *
  by_cases hc : ((e11 _v) ≤ (e12 _v)) <;> simp [hc]
theorem n8613 (_v : Vars) (_q : Query _v)  : (e8612 _v) := by
  have p5088 := n5088 _v _q 
  have p5092 := n5092 _v _q 
  exact (Iff.trans p5088 p5092)
theorem n8614 (_v : Vars) (_q : Query _v)  : (e5099 _v) := by
  simp only [e5, e6, e8, e10, e12, e36, e37, e38, e41, e42, e5098, e5099] at *
  omega
theorem n8615 (_v : Vars) (_q : Query _v)  : (e5101 _v) := by
  simp only [e5, e6, e8, e10, e12, e36, e37, e39, e41, e42, e5100, e5101] at *
  omega
theorem n8618 (_v : Vars) (_q : Query _v)  : (e8617 _v) := by
  have p8614 := n8614 _v _q 
  have p8615 := n8615 _v _q 
  change ((e38 _v) ↔ (e5098 _v)) at p8614
  change ((e39 _v) ↔ (e5100 _v)) at p8615
  simp only [e8617, e40, e8616, p8614, p8615]
theorem n8620 (_v : Vars) (_q : Query _v)  : (e8619 _v) := by
  simp only [e5, e6, e8, e10, e12, e41, e42, e5098, e5100, e5102, e5103, e5104, e5105, e8616, e8619] at *
  omega
theorem n8628 (_v : Vars) (_q : Query _v)  : (e8627 _v) := by
  have p55 := n55 _v _q 
  have p5113 := n5113 _v _q 
  exact (Iff.trans p55 p5113)
theorem n8630 (_v : Vars) (_q : Query _v)  : (e8629 _v) := by
  have p8628 := n8628 _v _q 
  change ((e50 _v) ↔ (e60 _v)) at p8628
  simp only [e8629, e5109, e5125, p8628]
theorem n8632 (_v : Vars) (_q : Query _v)  : (e8631 _v) := by
  have p5117 := n5117 _v _q 
  have p5121 := n5121 _v _q 
  exact (Iff.trans p5117 p5121)
theorem n8636 (_v : Vars) (_q : Query _v)  : (e8635 _v) := by
  simp only [e79, e80, e81, e5128, e5129, e5138, e5139, e8635] at *
  by_cases hc : ((e78 _v) ≤ (e12 _v)) <;> simp [hc]
theorem n8638 (_v : Vars) (_q : Query _v)  : (e8637 _v) := by
  have p5133 := n5133 _v _q 
  have p5137 := n5137 _v _q 
  exact (Iff.trans p5133 p5137)
theorem n8639 (_v : Vars) (_q : Query _v)  : (e5144 _v) := by
  simp only [e5, e6, e10, e12, e36, e41, e46, e96, e97, e100, e5143, e5144] at *
  omega
theorem n8640 (_v : Vars) (_q : Query _v)  : (e5146 _v) := by
  simp only [e5, e6, e10, e12, e36, e41, e46, e96, e98, e100, e5145, e5146] at *
  omega
theorem n8643 (_v : Vars) (_q : Query _v)  : (e8642 _v) := by
  have p8639 := n8639 _v _q 
  have p8640 := n8640 _v _q 
  change ((e97 _v) ↔ (e5143 _v)) at p8639
  change ((e98 _v) ↔ (e5145 _v)) at p8640
  simp only [e8642, e99, e8641, p8639, p8640]
theorem n8645 (_v : Vars) (_q : Query _v)  : (e8644 _v) := by
  simp only [e5, e6, e10, e12, e41, e46, e100, e5143, e5145, e5147, e5148, e5149, e5150, e8641, e8644] at *
  omega
theorem n8653 (_v : Vars) (_q : Query _v)  : (e8652 _v) := by
  have p117 := n117 _v _q 
  have p5158 := n5158 _v _q 
  exact (Iff.trans p117 p5158)
end
end Assembly
