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
  simp only [e2522, e4811, e4812, e4813, e4814, e6650, e8284, e8292, e8295] at *
  tauto
theorem n19693 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) : (e4813 _v) := by
  have p16259 := n16259 _v _q 
  have p19692 := n19692 _v _q h5362
  simp only [e4811, e4812, e4813, e4814, e8284, e8285, e8292] at *
  tauto
theorem n19694 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) : (e488 _v) := by
  have p15090 := n15090 _v _q 
  have p19675 := n19675 _v _q h5362
  simp only [e488, e490, e493, e494, e5402, e5403, e7821] at *
  tauto
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
  simp only [e2529, e8310, e8315, e8317, e8319, e8320, e8321, e8322, e11298] at *
  tauto
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
  simp only [e436, e496, e5362, e6720, e19697] at *
  tauto
theorem n19700 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4302 : (e4302 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e1995 _v) := by
  have p15579 := n15579 _v _q h4302
  have p19681 := n19681 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4156 h4199 h4260 h4302 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  exact FloorCertificate.node_19700 (e2 _v) (e7 _v) (e17 _v) (e45 _v) (e110 _v) p15579 p19681
theorem n19701 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4302 : (e4302 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e4575 _v) := by
  have p14696 := n14696 _v _q 
  have p19700 := n19700 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4156 h4199 h4260 h4302 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  simp only [e1995, e4567, e4568, e4572, e4573, e4574, e4575, e6423, e8066] at *
  tauto
theorem n19702 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4302 : (e4302 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e4567 _v) := by
  have p8485 := n8485 _v _q 
  have p19701 := n19701 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4156 h4199 h4260 h4302 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  simp only [e4567, e4568, e4572, e4573, e4574, e4575, e4956] at *
  tauto
theorem n19703 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4302 : (e4302 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e196 _v) := by
  have p4016 := n4016 _v _q 
  have p19681 := n19681 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4156 h4199 h4260 h4302 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  exact FloorCertificate.node_19703 (e2 _v) (e7 _v) (e45 _v) (e110 _v) p4016 p19681
theorem n19704 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4302 : (e4302 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e5203 _v) := by
  have p14730 := n14730 _v _q 
  have p19703 := n19703 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4156 h4199 h4260 h4302 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  simp only [e191, e192, e193, e194, e196, e5193, e5195, e5203, e5206] at *
  tauto
theorem n19705 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4302 : (e4302 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e191 _v) := by
  have p16442 := n16442 _v _q 
  have p19704 := n19704 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4156 h4199 h4260 h4302 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  simp only [e191, e192, e193, e194, e5193, e5194, e5203] at *
  tauto
theorem n19706 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4302 : (e4302 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e8307 _v) := by
  have p14906 := n14906 _v _q 
  have p19681 := n19681 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4156 h4199 h4260 h4302 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  simp only [e2529, e4836, e4837, e4838, e4839, e8301, e8307, e8310, e8312] at *
  tauto
theorem n19707 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4302 : (e4302 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e4838 _v) := by
  have p16285 := n16285 _v _q 
  have p19706 := n19706 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4156 h4199 h4260 h4302 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  simp only [e4836, e4837, e4838, e4839, e8301, e8302, e8307] at *
  tauto
theorem n19708 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h6784 : (e6784 _v)) : (e6780 _v) := by
  have p11449 := n11449 _v _q 
  have p19653 := n19653 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4260 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872 h6784
  simp only [e13, e2799, e5093, e6780, e11448] at *
  tauto
theorem n19709 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h6784 : (e6784 _v)) : (e7489 _v) := by
  have p15435 := n15435 _v _q 
  have p19682 := n19682 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4260 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872 h6784
  have p19708 := n19708 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4260 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872 h6784
  simp only [e2799, e6780, e8395, e8398, e8405, e8406, e8407, e8408, e11332] at *
  tauto
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
  simp only [e2242, e4673, e4674, e4675, e4676, e6525, e8166, e8174, e8177] at *
  tauto
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
  simp only [e251, e436, e5362, e6694, e19714] at *
  tauto
theorem n19717 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) (h5362 : (e5362 _v)) : (e8322 _v) := by
  have p15218 := n15218 _v _q 
  have p19689 := n19689 _v _q h2468 h5362
  simp only [e2529, e8310, e8315, e8317, e8319, e8320, e8321, e8322, e11298] at *
  tauto
theorem n19718 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) (h5362 : (e5362 _v)) : (e8317 _v) := by
  have p11541 := n11541 _v _q 
  have p19717 := n19717 _v _q h2468 h5362
  simp only [e8315, e8317, e8319, e8320, e8321, e8322, e8491] at *
  tauto
theorem n19719 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) : (e6830 _v) := by
  have p14629 := n14629 _v _q 
  have p19699 := n19699 _v _q h5362
  simp only [e496, e3069, e3071, e3074, e3075, e6720, e6829, e6830, e6833] at *
  tauto
theorem n19720 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) : (e3069 _v) := by
  have p14878 := n14878 _v _q 
  have p19719 := n19719 _v _q h5362
  simp only [e3069, e3071, e3074, e3075, e6829, e6830, e8137] at *
  tauto
theorem n19721 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4302 : (e4302 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e3173 _v) := by
  have p6907 := n6907 _v _q 
  have p18609 := n18609 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h4096 h4156 h4199 h4260 h4302 h4369 h4434 h4608 h4675 h4787 h4813 h4872
  simp only [e3172, e3173, e3177, e3178, e3179, e3180, e3190] at *
  tauto
theorem n19722 (_v : Vars) (_q : Query _v) (h4302 : (e4302 _v)) (h4434 : (e4434 _v)) : (e7749 _v) := by
  have p14941 := n14941 _v _q 
  have p17019 := n17019 _v _q h4302 h4434
  simp only [e7747, e7749, e7751, e7752, e7753, e7754, e8446] at *
  tauto
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
  simp only [e70, e75, e91, e95, e191, e192, e225, e230, e442, e443, e488, e493, e2303, e3069, e3074, e3105, e3106, e3152, e3156, e3173, e3178, e3937, e3942, e3946, e3947, e3976, e3981, e4059, e4064, e4096, e4097, e4156, e4157, e4199, e4200, e4260, e4261, e4306, e4311, e4369, e4370, e4398, e4403, e4434, e4435, e4491, e4496, e4567, e4572, e4608, e4609, e4653, e4658, e4675, e4676, e4724, e4729, e4747, e4752, e4787, e4788, e4813, e4814, e4838, e4839, e4872, e4873, e4903, e4908, e5100, e5103, e7493, e7494, e7749, e7752, e7807, e7935, e7943, e8045, e8048, e17361] at *
  tauto
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
  simp only [e70, e75, e91, e95, e191, e192, e225, e230, e442, e443, e488, e493, e2793, e3069, e3074, e3105, e3106, e3152, e3156, e3937, e3942, e3946, e3947, e4096, e4097, e4156, e4157, e4199, e4200, e4260, e4261, e4369, e4370, e4434, e4435, e4608, e4609, e4675, e4676, e4747, e4752, e4787, e4788, e4813, e4814, e4872, e4873, e6784, e19710] at *
  tauto
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
  simp only [e251, e4367, e4368, e4369, e4370, e6694, e7887, e7895, e7898] at *
  tauto
theorem n19728 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) : (e4369 _v) := by
  have p16222 := n16222 _v _q 
  have p19727 := n19727 _v _q h5362
  simp only [e4367, e4368, e4369, e4370, e7887, e7888, e7895] at *
  tauto
theorem n19729 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4302 : (e4302 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e7819 _v) := by
  have p14994 := n14994 _v _q 
  have p19723 := n19723 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4156 h4199 h4260 h4302 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  simp only [e2303, e7807, e7812, e7814, e7816, e7817, e7818, e7819, e11046] at *
  tauto
theorem n19730 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4302 : (e4302 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e7814 _v) := by
  have p15221 := n15221 _v _q 
  have p19729 := n19729 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4156 h4199 h4260 h4302 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  simp only [e7812, e7814, e7816, e7817, e7818, e7819, e8456] at *
  tauto
theorem n19731 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e2482 _v) := by
  have p19726 := n19726 _v _q 
  have p11473 := n11473 _v _q h6784
  simp only [e2482, e2793, e6784, e19725] at *
  tauto
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
  simp only [e2482, e4397, e4398, e4402, e4403, e4404, e4405, e6636, e7918] at *
  tauto
theorem n19735 (_v : Vars) (_q : Query _v) (h5223 : (e5223 _v)) (h6784 : (e6784 _v)) : (e7489 _v) := by
  have p4946 := n4946 _v _q 
  have p11473 := n11473 _v _q h6784
  have p19731 := n19731 _v _q h6784
  have p11520 := n11520 _v _q h5223
  exact FloorCertificate.node_19735 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p4946 p11473 p19731 p11520
theorem n19736 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e2254 _v) := by
  have p11455 := n11455 _v _q 
  have p19731 := n19731 _v _q h6784
  simp only [e2254, e2482, e6636, e11454] at *
  tauto
theorem n19737 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e6575 _v) := by
  have p19731 := n19731 _v _q h6784
  have p10893 := n10893 _v _q 
  have p11473 := n11473 _v _q h6784
  have p10896 := n10896 _v _q 
  have p11375 := n11375 _v _q 
  exact FloorCertificate.node_19737 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p19731 p10893 p11473 p10896 p11375
end
end Assembly
