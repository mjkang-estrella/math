import Dag215
import generated.th_lemma_27
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n19689 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) (h5362 : (e5362 _v)) : (e8310 _v) := by
  have p19674 := n19674 _v _q h5362
  have p7488 := n7488 _v _q h5362
  have p15071 := n15071 _v _q h2468
  have p5255 := n5255 _v _q 
  exact FloorCertificate.node_19689 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p19674 p7488 p15071 p5255
theorem n19690 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h2468 : (e2468 _v)) (h5362 : (e5362 _v)) : (e2061 _v) := by
  have p5255 := n5255 _v _q 
  have p15071 := n15071 _v _q h2468
  have p19674 := n19674 _v _q h5362
  have p8464 := n8464 _v _q h2351
  exact FloorCertificate.node_19690 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p5255 p15071 p19674 p8464
theorem n19691 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h2468 : (e2468 _v)) (h5362 : (e5362 _v)) : (e1995 _v) := by
  have p5255 := n5255 _v _q 
  have p8438 := n8438 _v _q h2468
  have p8464 := n8464 _v _q h2351
  have p19674 := n19674 _v _q h5362
  exact FloorCertificate.node_19691 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p5255 p8438 p8464 p19674
theorem n19692 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) : (e8292 _v) := by
  have p14657 := n14657 _v _q 
  have p19673 := n19673 _v _q h5362
  change (e2522 _v) ∨ (¬ (e8284 _v)) at p14657
  change (¬ (e2522 _v)) at p19673
  rcases p14657 with hlit | hlit
  · exact (False.elim (p19673 hlit))
  · exact hlit
theorem n19693 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) : (e4813 _v) := by
  have p16259 := n16259 _v _q 
  have p19692 := n19692 _v _q h5362
  change (e8284 _v) ∨ (e4813 _v) at p16259
  change (¬ (e8284 _v)) at p19692
  rcases p16259 with hlit | hlit
  · exact (False.elim (p19692 hlit))
  · exact hlit
theorem n19694 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) : (e488 _v) := by
  have p15090 := n15090 _v _q 
  have p19675 := n19675 _v _q h5362
  change (e5402 _v) ∨ (e488 _v) at p15090
  change (¬ (e5402 _v)) at p19675
  rcases p15090 with hlit | hlit
  · exact (False.elim (p19675 hlit))
  · exact hlit
theorem n19695 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) (h5362 : (e5362 _v)) : (e8310 _v) := by
  have p15071 := n15071 _v _q h2468
  have p7488 := n7488 _v _q h5362
  have p4016 := n4016 _v _q 
  have p5255 := n5255 _v _q 
  have p19673 := n19673 _v _q h5362
  exact FloorCertificate.node_19695 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p15071 p7488 p4016 p5255 p19673
theorem n19696 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) (h5362 : (e5362 _v)) : (e8322 _v) := by
  have p15218 := n15218 _v _q 
  have p19695 := n19695 _v _q h2468 h5362
  change (e2529 _v) ∨ (¬ (e8321 _v)) at p15218
  change (¬ (e2529 _v)) at p19695
  rcases p15218 with hlit | hlit
  · exact (False.elim (p19695 hlit))
  · exact hlit
theorem n19698 (_v : Vars) (_q : Query _v)  : (e19697 _v) := by
  by_contra hc
  change ¬ ((¬ (e496 _v)) ∨ (e436 _v)) at hc
  have h496 : (e496 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h5362 : (e5362 _v) := (fun hn => hc (Or.inr hn))
  have p19680 := n19680 _v _q h496 h5362
  exact p19680
theorem n19699 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) : (e6720 _v) := by
  have p19698 := n19698 _v _q 
  have p7488 := n7488 _v _q h5362
  change (¬ (e496 _v)) ∨ (e436 _v) at p19698
  change (¬ (e436 _v)) at p7488
  rcases p19698 with hlit | hlit
  · exact hlit
  · exact (False.elim (p7488 hlit))
theorem n19700 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4302 : (e4302 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e1995 _v) := by
  have p15579 := n15579 _v _q h4302
  have p19681 := n19681 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4156 h4199 h4260 h4302 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  exact FloorCertificate.node_19700 (e2 _v) (e7 _v) (e17 _v) (e45 _v) (e110 _v) p15579 p19681
theorem n19701 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4302 : (e4302 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e4575 _v) := by
  have p14696 := n14696 _v _q 
  have p19700 := n19700 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4156 h4199 h4260 h4302 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  change (¬ (e1995 _v)) ∨ (¬ (e4574 _v)) at p14696
  rcases p14696 with hlit | hlit
  · exact (False.elim (hlit p19700))
  · exact hlit
theorem n19702 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4302 : (e4302 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e4567 _v) := by
  have p8485 := n8485 _v _q 
  have p19701 := n19701 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4156 h4199 h4260 h4302 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  change (e4574 _v) ∨ (e4567 _v) at p8485
  change (¬ (e4574 _v)) at p19701
  rcases p8485 with hlit | hlit
  · exact (False.elim (p19701 hlit))
  · exact hlit
theorem n19703 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4302 : (e4302 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e196 _v) := by
  have p4016 := n4016 _v _q 
  have p19681 := n19681 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4156 h4199 h4260 h4302 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  exact FloorCertificate.node_19703 (e2 _v) (e7 _v) (e45 _v) (e110 _v) p4016 p19681
theorem n19704 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4302 : (e4302 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e5203 _v) := by
  have p14730 := n14730 _v _q 
  have p19703 := n19703 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4156 h4199 h4260 h4302 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  change (¬ (e196 _v)) ∨ (¬ (e5193 _v)) at p14730
  rcases p14730 with hlit | hlit
  · exact (False.elim (hlit p19703))
  · exact hlit
theorem n19705 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4302 : (e4302 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e191 _v) := by
  have p16442 := n16442 _v _q 
  have p19704 := n19704 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4156 h4199 h4260 h4302 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  change (e5193 _v) ∨ (e191 _v) at p16442
  change (¬ (e5193 _v)) at p19704
  rcases p16442 with hlit | hlit
  · exact (False.elim (p19704 hlit))
  · exact hlit
theorem n19706 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4302 : (e4302 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e8307 _v) := by
  have p14906 := n14906 _v _q 
  have p19681 := n19681 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4156 h4199 h4260 h4302 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  change (¬ (e2529 _v)) ∨ (¬ (e8301 _v)) at p14906
  rcases p14906 with hlit | hlit
  · exact (False.elim (hlit p19681))
  · exact hlit
theorem n19707 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4302 : (e4302 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e4838 _v) := by
  have p16285 := n16285 _v _q 
  have p19706 := n19706 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4156 h4199 h4260 h4302 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  change (e8301 _v) ∨ (e4838 _v) at p16285
  change (¬ (e8301 _v)) at p19706
  rcases p16285 with hlit | hlit
  · exact (False.elim (p19706 hlit))
  · exact hlit
theorem n19708 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h6784 : (e6784 _v)) : (e6780 _v) := by
  have p11449 := n11449 _v _q 
  have p19653 := n19653 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4260 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872 h6784
  change (¬ (e2799 _v)) ∨ (e13 _v) at p11449
  change (¬ (e13 _v)) at p19653
  rcases p11449 with hlit | hlit
  · exact hlit
  · exact (False.elim (p19653 hlit))
theorem n19709 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h6784 : (e6784 _v)) : (e7489 _v) := by
  have p15435 := n15435 _v _q 
  have p19682 := n19682 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4260 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872 h6784
  have p19708 := n19708 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4260 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872 h6784
  change (e2799 _v) ∨ (¬ (e8407 _v)) at p15435
  change (¬ (e2799 _v)) at p19708
  rcases p15435 with hlit | hlit
  · exact (False.elim (p19708 hlit))
  · exact (False.elim (hlit p19682))
theorem n19711 (_v : Vars) (_q : Query _v)  : (e19710 _v) := by
  by_contra hc
  change ¬ ((e2793 _v) ∨ (¬ (e4787 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e91 _v))) at hc
  have h70 : (e70 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))))))))))))))))))))
  have h191 : (e191 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))
  have h225 : (e225 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h442 : (e442 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))
  have h488 : (e488 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h3069 : (e3069 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))
  have h3105 : (e3105 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))
  have h3946 : (e3946 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h4096 : (e4096 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))
  have h4156 : (e4156 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h4199 : (e4199 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4260 : (e4260 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h4369 : (e4369 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4434 : (e4434 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h4608 : (e4608 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))
  have h4675 : (e4675 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4747 : (e4747 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))
  have h4872 : (e4872 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))
  have h6784 : (e6784 _v) := (fun hn => hc (Or.inl hn))
  have p19709 := n19709 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4260 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872 h6784
  exact p19709
theorem n19712 (_v : Vars) (_q : Query _v) (h6758 : (e6758 _v)) : (e6525 _v) := by
  have p10893 := n10893 _v _q 
  have p11375 := n11375 _v _q 
  have p8425 := n8425 _v _q h6758
  have p19683 := n19683 _v _q h6758
  exact FloorCertificate.node_19712 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p10893 p11375 p8425 p19683
theorem n19713 (_v : Vars) (_q : Query _v) (h6758 : (e6758 _v)) : (e8174 _v) := by
  have p14634 := n14634 _v _q 
  have p19712 := n19712 _v _q h6758
  change (e2242 _v) ∨ (¬ (e8166 _v)) at p14634
  change (¬ (e2242 _v)) at p19712
  rcases p14634 with hlit | hlit
  · exact (False.elim (p19712 hlit))
  · exact hlit
theorem n19715 (_v : Vars) (_q : Query _v)  : (e19714 _v) := by
  by_contra hc
  change ¬ ((¬ (e251 _v)) ∨ (e436 _v)) at hc
  have h251 : (e251 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h5362 : (e5362 _v) := (fun hn => hc (Or.inr hn))
  have p19685 := n19685 _v _q h251 h5362
  exact p19685
theorem n19716 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) : (e6694 _v) := by
  have p19715 := n19715 _v _q 
  have p7488 := n7488 _v _q h5362
  change (¬ (e251 _v)) ∨ (e436 _v) at p19715
  change (¬ (e436 _v)) at p7488
  rcases p19715 with hlit | hlit
  · exact hlit
  · exact (False.elim (p7488 hlit))
theorem n19717 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) (h5362 : (e5362 _v)) : (e8322 _v) := by
  have p15218 := n15218 _v _q 
  have p19689 := n19689 _v _q h2468 h5362
  change (e2529 _v) ∨ (¬ (e8321 _v)) at p15218
  change (¬ (e2529 _v)) at p19689
  rcases p15218 with hlit | hlit
  · exact (False.elim (p19689 hlit))
  · exact hlit
theorem n19718 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) (h5362 : (e5362 _v)) : (e8317 _v) := by
  have p11541 := n11541 _v _q 
  have p19717 := n19717 _v _q h2468 h5362
  change (e8321 _v) ∨ (e8317 _v) at p11541
  change (¬ (e8321 _v)) at p19717
  rcases p11541 with hlit | hlit
  · exact (False.elim (p19717 hlit))
  · exact hlit
theorem n19719 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) : (e6830 _v) := by
  have p14629 := n14629 _v _q 
  have p19699 := n19699 _v _q h5362
  change (e496 _v) ∨ (¬ (e6829 _v)) at p14629
  change (¬ (e496 _v)) at p19699
  rcases p14629 with hlit | hlit
  · exact (False.elim (p19699 hlit))
  · exact hlit
theorem n19720 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) : (e3069 _v) := by
  have p14878 := n14878 _v _q 
  have p19719 := n19719 _v _q h5362
  change (e6829 _v) ∨ (e3069 _v) at p14878
  change (¬ (e6829 _v)) at p19719
  rcases p14878 with hlit | hlit
  · exact (False.elim (p19719 hlit))
  · exact hlit
theorem n19721 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4302 : (e4302 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e3173 _v) := by
  have p6907 := n6907 _v _q 
  have p18609 := n18609 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h4096 h4156 h4199 h4260 h4302 h4369 h4434 h4608 h4675 h4787 h4813 h4872
  change (e3179 _v) ∨ (e3173 _v) at p6907
  change (¬ (e3179 _v)) at p18609
  rcases p6907 with hlit | hlit
  · exact (False.elim (p18609 hlit))
  · exact hlit
theorem n19722 (_v : Vars) (_q : Query _v) (h4302 : (e4302 _v)) (h4434 : (e4434 _v)) : (e7749 _v) := by
  have p14941 := n14941 _v _q 
  have p17019 := n17019 _v _q h4302 h4434
  change (e7753 _v) ∨ (e7749 _v) at p14941
  change (¬ (e7753 _v)) at p17019
  rcases p14941 with hlit | hlit
  · exact (False.elim (p17019 hlit))
  · exact hlit
theorem n19723 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4302 : (e4302 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e7807 _v) := by
  have p17362 := n17362 _v _q 
  have p17013 := n17013 _v _q h4302 h4434
  have p19702 := n19702 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4156 h4199 h4260 h4302 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  have p19705 := n19705 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4156 h4199 h4260 h4302 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  have p4994 := n4994 _v _q h3069
  have p19649 := n19649 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h4096 h4156 h4199 h4260 h4302 h4369 h4434 h4608 h4675 h4787 h4813 h4872
  have p4981 := n4981 _v _q h4260
  have p5001 := n5001 _v _q h4096
  have p4999 := n4999 _v _q h91
  have p17036 := n17036 _v _q h4302 h4434
  have p5010 := n5010 _v _q h70
  have p5003 := n5003 _v _q h4199
  have p5007 := n5007 _v _q h225
  have p4992 := n4992 _v _q h442
  have p19707 := n19707 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4156 h4199 h4260 h4302 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  have p4996 := n4996 _v _q h3937
  have p16842 := n16842 _v _q h4302
  have p19721 := n19721 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h4096 h4156 h4199 h4260 h4302 h4369 h4434 h4608 h4675 h4787 h4813 h4872
  have p16528 := n16528 _v _q h4302
  have p4987 := n4987 _v _q h4434
  have p17137 := n17137 _v _q h4059
  have p16517 := n16517 _v _q h4302
  have p18607 := n18607 _v _q h4302
  have p16845 := n16845 _v _q h4302
  have p17017 := n17017 _v _q h4302 h4434
  have p4983 := n4983 _v _q h4813
  have p4995 := n4995 _v _q h4369
  have p4998 := n4998 _v _q h3152
  have p19722 := n19722 _v _q h4302 h4434
  have p5008 := n5008 _v _q h4787
  have p16540 := n16540 _v _q h4302
  have p5006 := n5006 _v _q h4675
  have p17056 := n17056 _v _q h3946
  have p17061 := n17061 _v _q h4747
  have p4985 := n4985 _v _q h4156
  have p16538 := n16538 _v _q h4302
  have p4988 := n4988 _v _q h488
  have p4986 := n4986 _v _q h3105
  have p4984 := n4984 _v _q h4872
  have p4991 := n4991 _v _q h4608
  change (¬ (e2303 _v)) ∨ (¬ (e8045 _v)) ∨ (¬ (e4567 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e7935 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e7493 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e4724 _v)) ∨ (¬ (e3173 _v)) ∨ (¬ (e4398 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e3976 _v)) ∨ (¬ (e4491 _v)) ∨ (¬ (e5100 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e7749 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e4903 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) at p17362
  rcases p17362 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p17013))
  · exact (False.elim (hlit p19702))
  · exact (False.elim (hlit p19705))
  · exact (False.elim (hlit p4994))
  · exact (False.elim (hlit p19649))
  · exact (False.elim (hlit p4981))
  · exact (False.elim (hlit p5001))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p17036))
  · exact (False.elim (hlit p5010))
  · exact (False.elim (hlit p5003))
  · exact (False.elim (hlit p5007))
  · exact (False.elim (hlit p4992))
  · exact (False.elim (hlit p19707))
  · exact (False.elim (hlit p4996))
  · exact (False.elim (hlit p16842))
  · exact (False.elim (hlit p19721))
  · exact (False.elim (hlit p16528))
  · exact (False.elim (hlit p4987))
  · exact (False.elim (hlit p17137))
  · exact (False.elim (hlit p16517))
  · exact (False.elim (hlit p18607))
  · exact (False.elim (hlit p16845))
  · exact (False.elim (hlit p17017))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p4995))
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p19722))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p16540))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p17056))
  · exact (False.elim (hlit p17061))
  · exact (False.elim (hlit p4985))
  · exact (False.elim (hlit p16538))
  · exact (False.elim (hlit p4988))
  · exact (False.elim (hlit p4986))
  · exact (False.elim (hlit p4984))
  · exact (False.elim (hlit p4991))
theorem n19724 (_v : Vars) (_q : Query _v) (h6636 : (e6636 _v)) (h6784 : (e6784 _v)) : (e7489 _v) := by
  have p19711 := n19711 _v _q 
  have p16599 := n16599 _v _q h6636
  have p16600 := n16600 _v _q h6636
  have p17294 := n17294 _v _q 
  have p17874 := n17874 _v _q 
  have p11473 := n11473 _v _q h6784
  have p16602 := n16602 _v _q h6636
  have p16603 := n16603 _v _q h6784
  have p15686 := n15686 _v _q h6636
  have p16853 := n16853 _v _q h6636
  have p16607 := n16607 _v _q h6784
  have p16608 := n16608 _v _q h6636
  have p16609 := n16609 _v _q h6636
  have p16610 := n16610 _v _q h6636
  have p16611 := n16611 _v _q h6636
  have p17758 := n17758 _v _q 
  have p16612 := n16612 _v _q h6636
  have p16854 := n16854 _v _q h6784
  have p19665 := n19665 _v _q 
  have p16615 := n16615 _v _q h6636
  have p16616 := n16616 _v _q h6636
  have p15702 := n15702 _v _q h6784
  have p15705 := n15705 _v _q h6784
  have p16617 := n16617 _v _q h6636
  have p16855 := n16855 _v _q h6636
  change (e2793 _v) ∨ (¬ (e4787 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e91 _v)) at p19711
  change (¬ (e2793 _v)) at p11473
  rcases p19711 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact (False.elim (p11473 hlit))
  · exact (False.elim (hlit p16616))
  · exact (False.elim (hlit p16602))
  · exact (False.elim (hlit p16599))
  · exact (False.elim (hlit p16610))
  · exact (False.elim (hlit p16853))
  · exact (False.elim (hlit p16608))
  · exact (False.elim (hlit p15686))
  · exact (False.elim (hlit p16600))
  · exact (False.elim (hlit p16603))
  · exact (False.elim (hlit p16609))
  · exact (False.elim (hlit p17874))
  · exact (False.elim (hlit p17294))
  · exact (False.elim (hlit p16611))
  · exact (False.elim (hlit p17758))
  · exact (False.elim (hlit p16612))
  · exact (False.elim (hlit p16854))
  · exact (False.elim (hlit p19665))
  · exact (False.elim (hlit p16615))
  · exact (False.elim (hlit p16607))
  · exact (False.elim (hlit p15702))
  · exact (False.elim (hlit p15705))
  · exact (False.elim (hlit p16617))
  · exact (False.elim (hlit p16855))
theorem n19726 (_v : Vars) (_q : Query _v)  : (e19725 _v) := by
  by_contra hc
  change ¬ ((e2482 _v) ∨ (e2793 _v)) at hc
  have h6636 : (e6636 _v) := (fun hn => hc (Or.inl hn))
  have h6784 : (e6784 _v) := (fun hn => hc (Or.inr hn))
  have p19724 := n19724 _v _q h6636 h6784
  exact p19724
theorem n19727 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) : (e7895 _v) := by
  have p14589 := n14589 _v _q 
  have p19716 := n19716 _v _q h5362
  change (e251 _v) ∨ (¬ (e7887 _v)) at p14589
  change (¬ (e251 _v)) at p19716
  rcases p14589 with hlit | hlit
  · exact (False.elim (p19716 hlit))
  · exact hlit
theorem n19728 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) : (e4369 _v) := by
  have p16222 := n16222 _v _q 
  have p19727 := n19727 _v _q h5362
  change (e7887 _v) ∨ (e4369 _v) at p16222
  change (¬ (e7887 _v)) at p19727
  rcases p16222 with hlit | hlit
  · exact (False.elim (p19727 hlit))
  · exact hlit
theorem n19729 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4302 : (e4302 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e7819 _v) := by
  have p14994 := n14994 _v _q 
  have p19723 := n19723 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4156 h4199 h4260 h4302 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  change (e2303 _v) ∨ (¬ (e7818 _v)) at p14994
  change (¬ (e2303 _v)) at p19723
  rcases p14994 with hlit | hlit
  · exact (False.elim (p19723 hlit))
  · exact hlit
theorem n19730 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4302 : (e4302 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e7814 _v) := by
  have p15221 := n15221 _v _q 
  have p19729 := n19729 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4156 h4199 h4260 h4302 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  change (e7818 _v) ∨ (e7814 _v) at p15221
  change (¬ (e7818 _v)) at p19729
  rcases p15221 with hlit | hlit
  · exact (False.elim (p19729 hlit))
  · exact hlit
theorem n19731 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e2482 _v) := by
  have p19726 := n19726 _v _q 
  have p11473 := n11473 _v _q h6784
  change (e2482 _v) ∨ (e2793 _v) at p19726
  change (¬ (e2793 _v)) at p11473
  rcases p19726 with hlit | hlit
  · exact hlit
  · exact (False.elim (p11473 hlit))
theorem n19732 (_v : Vars) (_q : Query _v) (h2296 : (e2296 _v)) (h6784 : (e6784 _v)) : (e7489 _v) := by
  have p258 := n258 _v _q 
  have p19731 := n19731 _v _q h6784
  have p8583 := n8583 _v _q h2296
  have p11473 := n11473 _v _q h6784
  exact FloorCertificate.node_19732 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p258 p19731 p8583 p11473
theorem n19733 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e2303 _v) := by
  have p19731 := n19731 _v _q h6784
  have p11473 := n11473 _v _q h6784
  exact FloorCertificate.node_19733 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p19731 p11473
theorem n19734 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e4405 _v) := by
  have p14702 := n14702 _v _q 
  have p19731 := n19731 _v _q h6784
  change (¬ (e2482 _v)) ∨ (¬ (e4404 _v)) at p14702
  rcases p14702 with hlit | hlit
  · exact (False.elim (hlit p19731))
  · exact hlit
theorem n19735 (_v : Vars) (_q : Query _v) (h5223 : (e5223 _v)) (h6784 : (e6784 _v)) : (e7489 _v) := by
  have p4946 := n4946 _v _q 
  have p11473 := n11473 _v _q h6784
  have p19731 := n19731 _v _q h6784
  have p11520 := n11520 _v _q h5223
  exact FloorCertificate.node_19735 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p4946 p11473 p19731 p11520
theorem n19736 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e2254 _v) := by
  have p11455 := n11455 _v _q 
  have p19731 := n19731 _v _q h6784
  change (¬ (e2482 _v)) ∨ (e2254 _v) at p11455
  rcases p11455 with hlit | hlit
  · exact (False.elim (hlit p19731))
  · exact hlit
theorem n19737 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e6575 _v) := by
  have p19731 := n19731 _v _q h6784
  have p10893 := n10893 _v _q 
  have p11473 := n11473 _v _q h6784
  have p10896 := n10896 _v _q 
  have p11375 := n11375 _v _q 
  exact FloorCertificate.node_19737 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p19731 p10893 p11473 p10896 p11375
end
end Assembly
