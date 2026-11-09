import Dag253
import generated.th_lemma_34
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n21563 (_v : Vars) (_q : Query _v) (h2303 : (e2303 _v)) : (e79 _v) := by
  have p11490 := n11490 _v _q 
  have p8448 := n8448 _v _q h2303
  change (e79 _v) ∨ (¬ (e2303 _v)) at p11490
  rcases p11490 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p8448))
theorem n21564 (_v : Vars) (_q : Query _v) (h2303 : (e2303 _v)) : (e5135 _v) := by
  have p14729 := n14729 _v _q 
  have p21563 := n21563 _v _q h2303
  change (¬ (e79 _v)) ∨ (¬ (e5134 _v)) at p14729
  rcases p14729 with hlit | hlit
  · exact (False.elim (hlit p21563))
  · exact hlit
theorem n21565 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2303 : (e2303 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e95 _v) := by
  have p21558 := n21558 _v _q 
  have p16675 := n16675 _v _q h2303
  have p4983 := n4983 _v _q h4813
  have p17060 := n17060 _v _q h4653
  have p16729 := n16729 _v _q h51
  have p17138 := n17138 _v _q h4306
  have p8463 := n8463 _v _q h6525
  change (e2242 _v) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e2529 _v)) at p21558
  change (¬ (e2242 _v)) at p8463
  rcases p21558 with hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact (False.elim (p8463 hlit))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p4983))
  · exact hlit
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p16675))
theorem n21566 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2303 : (e2303 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e7489 _v) := by
  have p16235 := n16235 _v _q 
  have p21564 := n21564 _v _q h2303
  have p21565 := n21565 _v _q h51 h2303 h4306 h4653 h4813 h6525
  change (e5134 _v) ∨ (e91 _v) at p16235
  change (¬ (e5134 _v)) at p21564
  change (¬ (e91 _v)) at p21565
  rcases p16235 with hlit | hlit
  · exact (False.elim (p21564 hlit))
  · exact (False.elim (p21565 hlit))
theorem n21568 (_v : Vars) (_q : Query _v)  : (e21567 _v) := by
  by_contra hc
  change ¬ ((¬ (e2475 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4306 _v)) ∨ (e2242 _v)) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h2475 : (e2475 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h6525 : (e6525 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))
  have p21560 := n21560 _v _q h51 h2475 h4306 h4653 h4813 h6525
  exact p21560
theorem n21569 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e2125 _v) := by
  have p21562 := n21562 _v _q h51 h91 h2529 h4306 h4653 h4813
  have p5255 := n5255 _v _q 
  exact FloorCertificate.node_21569 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e110 _v) p21562 p5255
theorem n21570 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e2061 _v) := by
  have p8478 := n8478 _v _q 
  have p21569 := n21569 _v _q h51 h91 h2529 h4306 h4653 h4813
  change (e2061 _v) ∨ (¬ (e2125 _v)) at p8478
  rcases p8478 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p21569))
theorem n21571 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e1995 _v) := by
  have p11412 := n11412 _v _q 
  have p21570 := n21570 _v _q h51 h91 h2529 h4306 h4653 h4813
  change (e1995 _v) ∨ (¬ (e2061 _v)) at p11412
  rcases p11412 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p21570))
theorem n21572 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e4575 _v) := by
  have p14696 := n14696 _v _q 
  have p21571 := n21571 _v _q h51 h91 h2529 h4306 h4653 h4813
  change (¬ (e1995 _v)) ∨ (¬ (e4574 _v)) at p14696
  rcases p14696 with hlit | hlit
  · exact (False.elim (hlit p21571))
  · exact hlit
theorem n21573 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e4686 _v) := by
  have p14708 := n14708 _v _q 
  have p21562 := n21562 _v _q h51 h91 h2529 h4306 h4653 h4813
  change (¬ (e2242 _v)) ∨ (¬ (e4685 _v)) at p14708
  rcases p14708 with hlit | hlit
  · exact (False.elim (hlit p21562))
  · exact hlit
theorem n21574 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e4679 _v) := by
  have p14989 := n14989 _v _q 
  have p21573 := n21573 _v _q h51 h91 h2529 h4306 h4653 h4813
  change (e4685 _v) ∨ (e4679 _v) at p14989
  change (¬ (e4685 _v)) at p21573
  rcases p14989 with hlit | hlit
  · exact (False.elim (p21573 hlit))
  · exact hlit
theorem n21575 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e2179 _v) := by
  have p8557 := n8557 _v _q 
  have p21562 := n21562 _v _q h51 h91 h2529 h4306 h4653 h4813
  change (¬ (e2242 _v)) ∨ (e2179 _v) at p8557
  rcases p8557 with hlit | hlit
  · exact (False.elim (hlit p21562))
  · exact hlit
theorem n21576 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e4616 _v) := by
  have p14684 := n14684 _v _q 
  have p21575 := n21575 _v _q h51 h91 h2529 h4306 h4653 h4813
  change (¬ (e2179 _v)) ∨ (¬ (e3162 _v)) at p14684
  rcases p14684 with hlit | hlit
  · exact (False.elim (hlit p21575))
  · exact hlit
theorem n21577 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e3158 _v) := by
  have p15126 := n15126 _v _q 
  have p21576 := n21576 _v _q h51 h91 h2529 h4306 h4653 h4813
  change (e3162 _v) ∨ (e3158 _v) at p15126
  change (¬ (e3162 _v)) at p21576
  rcases p15126 with hlit | hlit
  · exact (False.elim (p21576 hlit))
  · exact hlit
theorem n21578 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e4447 _v) := by
  have p14688 := n14688 _v _q 
  have p21570 := n21570 _v _q h51 h91 h2529 h4306 h4653 h4813
  change (¬ (e2061 _v)) ∨ (¬ (e4446 _v)) at p14688
  rcases p14688 with hlit | hlit
  · exact (False.elim (hlit p21570))
  · exact hlit
theorem n21579 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e4439 _v) := by
  have p14925 := n14925 _v _q 
  have p21578 := n21578 _v _q h51 h91 h2529 h4306 h4653 h4813
  change (e4446 _v) ∨ (e4439 _v) at p14925
  change (¬ (e4446 _v)) at p21578
  rcases p14925 with hlit | hlit
  · exact (False.elim (p21578 hlit))
  · exact hlit
theorem n21580 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e4466 _v) := by
  have p14604 := n14604 _v _q 
  have p21569 := n21569 _v _q h51 h91 h2529 h4306 h4653 h4813
  change (¬ (e2125 _v)) ∨ (¬ (e4465 _v)) at p14604
  rcases p14604 with hlit | hlit
  · exact (False.elim (hlit p21569))
  · exact hlit
theorem n21581 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e4459 _v) := by
  have p8443 := n8443 _v _q 
  have p21580 := n21580 _v _q h51 h91 h2529 h4306 h4653 h4813
  change (e4465 _v) ∨ (e4459 _v) at p8443
  change (¬ (e4465 _v)) at p21580
  rcases p8443 with hlit | hlit
  · exact (False.elim (p21580 hlit))
  · exact hlit
theorem n21582 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h8320 : (e8320 _v)) : (e2125 _v) := by
  have p21561 := n21561 _v _q h51 h4306 h4653 h4813 h8320
  have p5255 := n5255 _v _q 
  exact FloorCertificate.node_21582 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e110 _v) p21561 p5255
theorem n21583 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h8320 : (e8320 _v)) : (e2061 _v) := by
  have p8478 := n8478 _v _q 
  have p21582 := n21582 _v _q h51 h4306 h4653 h4813 h8320
  change (e2061 _v) ∨ (¬ (e2125 _v)) at p8478
  rcases p8478 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p21582))
theorem n21584 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h8320 : (e8320 _v)) : (e1995 _v) := by
  have p11412 := n11412 _v _q 
  have p21583 := n21583 _v _q h51 h4306 h4653 h4813 h8320
  change (e1995 _v) ∨ (¬ (e2061 _v)) at p11412
  rcases p11412 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p21583))
theorem n21585 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h8320 : (e8320 _v)) : (e4575 _v) := by
  have p14696 := n14696 _v _q 
  have p21584 := n21584 _v _q h51 h4306 h4653 h4813 h8320
  change (¬ (e1995 _v)) ∨ (¬ (e4574 _v)) at p14696
  rcases p14696 with hlit | hlit
  · exact (False.elim (hlit p21584))
  · exact hlit
theorem n21586 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h8320 : (e8320 _v)) : (e4686 _v) := by
  have p14708 := n14708 _v _q 
  have p21561 := n21561 _v _q h51 h4306 h4653 h4813 h8320
  change (¬ (e2242 _v)) ∨ (¬ (e4685 _v)) at p14708
  rcases p14708 with hlit | hlit
  · exact (False.elim (hlit p21561))
  · exact hlit
theorem n21587 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h8320 : (e8320 _v)) : (e4679 _v) := by
  have p14989 := n14989 _v _q 
  have p21586 := n21586 _v _q h51 h4306 h4653 h4813 h8320
  change (e4685 _v) ∨ (e4679 _v) at p14989
  change (¬ (e4685 _v)) at p21586
  rcases p14989 with hlit | hlit
  · exact (False.elim (p21586 hlit))
  · exact hlit
theorem n21588 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h8320 : (e8320 _v)) : (e2179 _v) := by
  have p8557 := n8557 _v _q 
  have p21561 := n21561 _v _q h51 h4306 h4653 h4813 h8320
  change (¬ (e2242 _v)) ∨ (e2179 _v) at p8557
  rcases p8557 with hlit | hlit
  · exact (False.elim (hlit p21561))
  · exact hlit
theorem n21589 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h8320 : (e8320 _v)) : (e4616 _v) := by
  have p14684 := n14684 _v _q 
  have p21588 := n21588 _v _q h51 h4306 h4653 h4813 h8320
  change (¬ (e2179 _v)) ∨ (¬ (e3162 _v)) at p14684
  rcases p14684 with hlit | hlit
  · exact (False.elim (hlit p21588))
  · exact hlit
theorem n21590 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h8320 : (e8320 _v)) : (e3158 _v) := by
  have p15126 := n15126 _v _q 
  have p21589 := n21589 _v _q h51 h4306 h4653 h4813 h8320
  change (e3162 _v) ∨ (e3158 _v) at p15126
  change (¬ (e3162 _v)) at p21589
  rcases p15126 with hlit | hlit
  · exact (False.elim (p21589 hlit))
  · exact hlit
theorem n21591 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h8320 : (e8320 _v)) : (e4447 _v) := by
  have p14688 := n14688 _v _q 
  have p21583 := n21583 _v _q h51 h4306 h4653 h4813 h8320
  change (¬ (e2061 _v)) ∨ (¬ (e4446 _v)) at p14688
  rcases p14688 with hlit | hlit
  · exact (False.elim (hlit p21583))
  · exact hlit
theorem n21592 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h8320 : (e8320 _v)) : (e4439 _v) := by
  have p14925 := n14925 _v _q 
  have p21591 := n21591 _v _q h51 h4306 h4653 h4813 h8320
  change (e4446 _v) ∨ (e4439 _v) at p14925
  change (¬ (e4446 _v)) at p21591
  rcases p14925 with hlit | hlit
  · exact (False.elim (p21591 hlit))
  · exact hlit
theorem n21593 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h8320 : (e8320 _v)) : (e4466 _v) := by
  have p14604 := n14604 _v _q 
  have p21582 := n21582 _v _q h51 h4306 h4653 h4813 h8320
  change (¬ (e2125 _v)) ∨ (¬ (e4465 _v)) at p14604
  rcases p14604 with hlit | hlit
  · exact (False.elim (hlit p21582))
  · exact hlit
theorem n21594 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h8320 : (e8320 _v)) : (e4459 _v) := by
  have p8443 := n8443 _v _q 
  have p21593 := n21593 _v _q h51 h4306 h4653 h4813 h8320
  change (e4465 _v) ∨ (e4459 _v) at p8443
  change (¬ (e4465 _v)) at p21593
  rcases p8443 with hlit | hlit
  · exact (False.elim (p21593 hlit))
  · exact hlit
theorem n21596 (_v : Vars) (_q : Query _v)  : (e21595 _v) := by
  by_contra hc
  change ¬ ((¬ (e2303 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4306 _v)) ∨ (e2242 _v)) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h2303 : (e2303 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h6525 : (e6525 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))
  have p21566 := n21566 _v _q h51 h2303 h4306 h4653 h4813 h6525
  exact p21566
theorem n21597 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e4567 _v) := by
  have p8485 := n8485 _v _q 
  have p21572 := n21572 _v _q h51 h91 h2529 h4306 h4653 h4813
  change (e4574 _v) ∨ (e4567 _v) at p8485
  change (¬ (e4574 _v)) at p21572
  rcases p8485 with hlit | hlit
  · exact (False.elim (p21572 hlit))
  · exact hlit
theorem n21598 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2296 : (e2296 _v)) (h2529 : (e2529 _v)) (h4264 : (e4264 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6600 : (e6600 _v)) (h8038 : (e8038 _v)) : (e7489 _v) := by
  have p17138 := n17138 _v _q h4306
  have p8439 := n8439 _v _q h6600
  have p17118 := n17118 _v _q h4264
  have p17256 := n17256 _v _q 
  have p17060 := n17060 _v _q h4653
  have p13951 := n13951 _v _q 
  have p16572 := n16572 _v _q h2529
  have p15907 := n15907 _v _q h6600
  have p17147 := n17147 _v _q 
  have p15100 := n15100 _v _q h2296
  have p8583 := n8583 _v _q h2296
  have p17050 := n17050 _v _q 
  have p16778 := n16778 _v _q 
  have p17122 := n17122 _v _q 
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
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
  have p8602 := n8602 _v _q h8038
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
  have p21597 := n21597 _v _q h51 h91 h2529 h4306 h4653 h4813
  have p20827 := n20827 _v _q 
  have p5255 := n5255 _v _q 
  exact FloorCertificate.node_21598 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2883 _v) (e2902 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e4541 _v) (e4808 _v) p17138 p8439 p17118 p17256 p17060 p13951 p16572 p15907 p17147 p15100 p8583 p17050 p16778 p17122 p4983 p16729 p20829 p21574 p20426 p20126 p17110 p15113 p17053 p20096 p17131 p17108 p17294 p16943 p17058 p17064 p17067 p17080 p17072 p17074 p17069 p20461 p20836 p20653 p17078 p17136 p17087 p17083 p8548 p17055 p17093 p17091 p17098 p17106 p21577 p21579 p17141 p17100 p19610 p17102 p21190 p15209 p21581 p8602 p17096 p17115 p17758 p17124 p17111 p19665 p17113 p17117 p20467 p17120 p4999 p17133 p17874 p17104 p17127 p17089 p20470 p16705 p17020 p20274 p21597 p20827 p5255
theorem n21599 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6454 : (e6454 _v)) : (e7807 _v) := by
  have p21596 := n21596 _v _q 
  have p16125 := n16125 _v _q h6454
  have p17060 := n17060 _v _q h4653
  have p16729 := n16729 _v _q h51
  have p17138 := n17138 _v _q h4306
  have p4983 := n4983 _v _q h4813
  change (¬ (e2303 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4306 _v)) ∨ (e2242 _v) at p21596
  change (¬ (e2242 _v)) at p16125
  rcases p21596 with hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (p16125 hlit))
theorem n21600 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e8038 _v) := by
  have p21568 := n21568 _v _q 
  have p8463 := n8463 _v _q h6525
  have p17060 := n17060 _v _q h4653
  have p16729 := n16729 _v _q h51
  have p17138 := n17138 _v _q h4306
  have p4983 := n4983 _v _q h4813
  change (¬ (e2475 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4306 _v)) ∨ (e2242 _v) at p21568
  change (¬ (e2242 _v)) at p8463
  rcases p21568 with hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (p8463 hlit))
theorem n21601 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e7807 _v) := by
  have p21596 := n21596 _v _q 
  have p8463 := n8463 _v _q h6525
  have p17060 := n17060 _v _q h4653
  have p16729 := n16729 _v _q h51
  have p17138 := n17138 _v _q h4306
  have p4983 := n4983 _v _q h4813
  change (¬ (e2303 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4306 _v)) ∨ (e2242 _v) at p21596
  change (¬ (e2242 _v)) at p8463
  rcases p21596 with hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (p8463 hlit))
theorem n21602 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6501 : (e6501 _v)) : (e7807 _v) := by
  have p21596 := n21596 _v _q 
  have p15772 := n15772 _v _q h6501
  have p17060 := n17060 _v _q h4653
  have p16729 := n16729 _v _q h51
  have p17138 := n17138 _v _q h4306
  have p4983 := n4983 _v _q h4813
  change (¬ (e2303 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4306 _v)) ∨ (e2242 _v) at p21596
  change (¬ (e2242 _v)) at p15772
  rcases p21596 with hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (p15772 hlit))
theorem n21603 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6501 : (e6501 _v)) : (e8038 _v) := by
  have p21568 := n21568 _v _q 
  have p15772 := n15772 _v _q h6501
  have p17060 := n17060 _v _q h4653
  have p16729 := n16729 _v _q h51
  have p17138 := n17138 _v _q h4306
  have p4983 := n4983 _v _q h4813
  change (¬ (e2475 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4306 _v)) ∨ (e2242 _v) at p21568
  change (¬ (e2242 _v)) at p15772
  rcases p21568 with hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (p15772 hlit))
theorem n21605 (_v : Vars) (_q : Query _v)  : (e21604 _v) := by
  by_contra hc
  change ¬ ((e2402 _v) ∨ (¬ (e4306 _v)) ∨ (¬ (e4264 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e2296 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e2529 _v)) ∨ (e2475 _v) ∨ (¬ (e91 _v))) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))))))
  have h2296 : (e2296 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h2529 : (e2529 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h4264 : (e4264 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h6600 : (e6600 _v) := (fun hn => hc (Or.inl hn))
  have h8038 : (e8038 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have p21598 := n21598 _v _q h51 h91 h2296 h2529 h4264 h4306 h4653 h4813 h6600 h8038
  exact p21598
theorem n21606 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6454 : (e6454 _v)) : (e6746 _v) := by
  have p11429 := n11429 _v _q 
  have p21599 := n21599 _v _q h51 h4306 h4653 h4813 h6454
  change (¬ (e2740 _v)) ∨ (e2303 _v) at p11429
  change (¬ (e2303 _v)) at p21599
  rcases p11429 with hlit | hlit
  · exact hlit
  · exact (False.elim (p21599 hlit))
theorem n21607 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6454 : (e6454 _v)) : (e6724 _v) := by
  have p11461 := n11461 _v _q 
  have p21606 := n21606 _v _q h51 h4306 h4653 h4813 h6454
  change (¬ (e2691 _v)) ∨ (e2740 _v) at p11461
  change (¬ (e2740 _v)) at p21606
  rcases p11461 with hlit | hlit
  · exact hlit
  · exact (False.elim (p21606 hlit))
theorem n21608 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6454 : (e6454 _v)) : (e7517 _v) := by
  have p15196 := n15196 _v _q 
  have p21607 := n21607 _v _q h51 h4306 h4653 h4813 h6454
  change (e2691 _v) ∨ (¬ (e7497 _v)) at p15196
  change (¬ (e2691 _v)) at p21607
  rcases p15196 with hlit | hlit
  · exact (False.elim (p21607 hlit))
  · exact hlit
theorem n21609 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e4420 _v) := by
  have p16832 := n16832 _v _q 
  have p21600 := n21600 _v _q h51 h4306 h4653 h4813 h6525
  have p21601 := n21601 _v _q h51 h4306 h4653 h4813 h6525
  change (e2303 _v) ∨ (¬ (e4419 _v)) ∨ (e2475 _v) at p16832
  change (¬ (e2475 _v)) at p21600
  change (¬ (e2303 _v)) at p21601
  rcases p16832 with hlit | hlit | hlit
  · exact (False.elim (p21601 hlit))
  · exact hlit
  · exact (False.elim (p21600 hlit))
theorem n21610 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e7921 _v) := by
  have p16347 := n16347 _v _q 
  have p21609 := n21609 _v _q h51 h4306 h4653 h4813 h6525
  change (e7921 _v) ∨ (e4419 _v) at p16347
  change (¬ (e4419 _v)) at p21609
  rcases p16347 with hlit | hlit
  · exact hlit
  · exact (False.elim (p21609 hlit))
end
end Assembly
