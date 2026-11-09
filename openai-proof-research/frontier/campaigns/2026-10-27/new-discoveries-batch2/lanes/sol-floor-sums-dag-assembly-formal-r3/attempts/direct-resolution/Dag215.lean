import Dag214
import generated.th_lemma_26
import generated.th_lemma_27
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n19642 (_v : Vars) (_q : Query _v) (h474 : (e474 _v)) : (e2296 _v) := by
  have p5391 := n5391 _v _q 
  have p11414 := n11414 _v _q h474
  have p4016 := n4016 _v _q 
  exact FloorCertificate.node_19642 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p5391 p11414 p4016
theorem n19643 (_v : Vars) (_q : Query _v) (h474 : (e474 _v)) : (e2522 _v) := by
  have p4016 := n4016 _v _q 
  have p11414 := n11414 _v _q h474
  exact FloorCertificate.node_19643 (e2 _v) (e7 _v) (e17 _v) (e45 _v) (e110 _v) p4016 p11414
theorem n19644 (_v : Vars) (_q : Query _v) (h474 : (e474 _v)) (h5362 : (e5362 _v)) : (e7489 _v) := by
  have p18232 := n18232 _v _q 
  have p19642 := n19642 _v _q h474
  have p19643 := n19643 _v _q h474
  have p7488 := n7488 _v _q h5362
  have p17252 := n17252 _v _q h5362
  have p19630 := n19630 _v _q 
  simp only [e436, e2296, e2522, e2722, e4264, e4269, e5362, e6549, e6650, e6742, e18231] at *
  tauto
theorem n19646 (_v : Vars) (_q : Query _v)  : (e19645 _v) := by
  by_contra hc
  change ¬ ((¬ (e474 _v)) ∨ (e436 _v)) at hc
  have h474 : (e474 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h5362 : (e5362 _v) := (fun hn => hc (Or.inr hn))
  have p19644 := n19644 _v _q h474 h5362
  exact p19644
theorem n19647 (_v : Vars) (_q : Query _v) (h496 : (e496 _v)) (h5362 : (e5362 _v)) : (e2781 _v) := by
  have p8144 := n8144 _v _q h496
  have p4016 := n4016 _v _q 
  have p5255 := n5255 _v _q 
  have p19630 := n19630 _v _q 
  have p5391 := n5391 _v _q 
  have p15080 := n15080 _v _q h5362
  exact FloorCertificate.node_19647 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8144 p4016 p5255 p19630 p5391 p15080
theorem n19648 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4302 : (e4302 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e7945 _v) := by
  have p15228 := n15228 _v _q 
  have p19633 := n19633 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h4096 h4156 h4199 h4260 h4302 h4369 h4434 h4608 h4675 h4787 h4813 h4872
  simp only [e2787, e6772, e7932, e7935, e7942, e7943, e7944, e7945, e11111] at *
  tauto
theorem n19649 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4302 : (e4302 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e7935 _v) := by
  have p15266 := n15266 _v _q 
  have p19648 := n19648 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h4096 h4156 h4199 h4260 h4302 h4369 h4434 h4608 h4675 h4787 h4813 h4872
  simp only [e7932, e7935, e7942, e7943, e7944, e7945, e8489] at *
  tauto
theorem n19650 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h6784 : (e6784 _v)) : (e8310 _v) := by
  have p14906 := n14906 _v _q 
  have p19635 := n19635 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4260 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872 h6784
  simp only [e2529, e4836, e4837, e4838, e4839, e8301, e8307, e8310, e8312] at *
  tauto
theorem n19651 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h6784 : (e6784 _v)) : (e8038 _v) := by
  have p11493 := n11493 _v _q 
  have p19650 := n19650 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4260 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872 h6784
  simp only [e2475, e2529, e8038, e8310, e11492] at *
  tauto
theorem n19652 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h6784 : (e6784 _v)) : (e8405 _v) := by
  have p16847 := n16847 _v _q 
  have p19651 := n19651 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4260 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872 h6784
  have p15617 := n15617 _v _q h6784
  have p19650 := n19650 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4260 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872 h6784
  simp only [e2475, e2529, e4897, e4898, e8038, e8310, e8395, e8405, e16846] at *
  tauto
theorem n19653 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h6784 : (e6784 _v)) : (e5093 _v) := by
  have p11399 := n11399 _v _q 
  have p19651 := n19651 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4260 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872 h6784
  simp only [e13, e2475, e5093, e8038, e11398] at *
  tauto
theorem n19654 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e2697 _v) := by
  have p11391 := n11391 _v _q 
  have p19636 := n19636 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4260 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  simp only [e2254, e2697, e6531, e11390] at *
  tauto
theorem n19655 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e4499 _v) := by
  have p14700 := n14700 _v _q 
  have p19654 := n19654 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4260 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  simp only [e2697, e4491, e4492, e4496, e4497, e4498, e4499, e6732, e7998] at *
  tauto
theorem n19656 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e4491 _v) := by
  have p14969 := n14969 _v _q 
  have p19655 := n19655 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4260 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  simp only [e4491, e4492, e4496, e4497, e4498, e4499, e4960] at *
  tauto
theorem n19657 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e4731 _v) := by
  have p14698 := n14698 _v _q 
  have p19636 := n19636 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4260 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  simp only [e2254, e4723, e4724, e4728, e4729, e4730, e4731, e6531, e8220] at *
  tauto
theorem n19658 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e4724 _v) := by
  have p15518 := n15518 _v _q 
  have p19657 := n19657 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4260 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  simp only [e4723, e4724, e4728, e4729, e4730, e4731, e4958] at *
  tauto
theorem n19659 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e2697 _v) := by
  have p11391 := n11391 _v _q 
  have p19639 := n19639 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4260 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  simp only [e2254, e2697, e6531, e11390] at *
  tauto
theorem n19660 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e4499 _v) := by
  have p14700 := n14700 _v _q 
  have p19659 := n19659 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4260 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  simp only [e2697, e4491, e4492, e4496, e4497, e4498, e4499, e6732, e7998] at *
  tauto
theorem n19661 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e4491 _v) := by
  have p14969 := n14969 _v _q 
  have p19660 := n19660 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4260 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  simp only [e4491, e4492, e4496, e4497, e4498, e4499, e4960] at *
  tauto
theorem n19662 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e4731 _v) := by
  have p14698 := n14698 _v _q 
  have p19639 := n19639 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4260 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  simp only [e2254, e4723, e4724, e4728, e4729, e4730, e4731, e6531, e8220] at *
  tauto
theorem n19663 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e4724 _v) := by
  have p15518 := n15518 _v _q 
  have p19662 := n19662 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4260 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  simp only [e4723, e4724, e4728, e4729, e4730, e4731, e4958] at *
  tauto
theorem n19664 (_v : Vars) (_q : Query _v)  : (e8358 _v) := by
  have p14673 := n14673 _v _q 
  have p19630 := n19630 _v _q 
  simp only [e2722, e4872, e4873, e4874, e4875, e6742, e8350, e8358, e8361] at *
  tauto
theorem n19665 (_v : Vars) (_q : Query _v)  : (e4872 _v) := by
  have p14999 := n14999 _v _q 
  have p19664 := n19664 _v _q 
  simp only [e4872, e4873, e4874, e4875, e8350, e8351, e8358] at *
  tauto
theorem n19666 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) (h5362 : (e5362 _v)) : (e2781 _v) := by
  have p11374 := n11374 _v _q h251
  have p5391 := n5391 _v _q 
  have p7488 := n7488 _v _q h5362
  have p5255 := n5255 _v _q 
  have p19630 := n19630 _v _q 
  exact FloorCertificate.node_19666 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p11374 p5391 p7488 p5255 p19630
theorem n19667 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) (h5362 : (e5362 _v)) : (e4271 _v) := by
  have p14699 := n14699 _v _q 
  have p19666 := n19666 _v _q h251 h5362
  simp only [e2781, e4263, e4264, e4268, e4269, e4270, e4271, e6776, e7795] at *
  tauto
theorem n19668 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h5362 : (e5362 _v)) : (e6650 _v) := by
  have p18232 := n18232 _v _q 
  have p15781 := n15781 _v _q h2351
  have p7488 := n7488 _v _q h5362
  have p17252 := n17252 _v _q h5362
  have p19630 := n19630 _v _q 
  simp only [e436, e2296, e2522, e2722, e4264, e4269, e5362, e6549, e6650, e6742, e18231] at *
  tauto
theorem n19669 (_v : Vars) (_q : Query _v)  : (e8561 _v) := by
  simp only [e4872, e4873, e4874, e4875, e8350, e8561] at *
  tauto
theorem n19670 (_v : Vars) (_q : Query _v)  : (e4874 _v) := by
  have p19669 := n19669 _v _q 
  have p19664 := n19664 _v _q 
  simp only [e4872, e4873, e4874, e4875, e8350, e8358, e8561] at *
  tauto
theorem n19672 (_v : Vars) (_q : Query _v)  : (e19671 _v) := by
  by_contra hc
  change ¬ ((¬ (e2522 _v)) ∨ (e436 _v)) at hc
  have h2522 : (e2522 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h5362 : (e5362 _v) := (fun hn => hc (Or.inr hn))
  have p19641 := n19641 _v _q h2522 h5362
  exact p19641
theorem n19673 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) : (e6650 _v) := by
  have p19672 := n19672 _v _q 
  have p7488 := n7488 _v _q h5362
  simp only [e436, e2522, e5362, e6650, e19671] at *
  tauto
theorem n19674 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) : (e5392 _v) := by
  have p19646 := n19646 _v _q 
  have p7488 := n7488 _v _q h5362
  simp only [e436, e474, e5362, e5392, e19645] at *
  tauto
theorem n19675 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) : (e5403 _v) := by
  have p14577 := n14577 _v _q 
  have p19674 := n19674 _v _q h5362
  simp only [e474, e488, e490, e493, e494, e5392, e5402, e5403, e5406] at *
  tauto
theorem n19676 (_v : Vars) (_q : Query _v) (h496 : (e496 _v)) (h5362 : (e5362 _v)) : (e4271 _v) := by
  have p14699 := n14699 _v _q 
  have p19647 := n19647 _v _q h496 h5362
  simp only [e2781, e4263, e4264, e4268, e4269, e4270, e4271, e6776, e7795] at *
  tauto
theorem n19677 (_v : Vars) (_q : Query _v) (h496 : (e496 _v)) : (e2296 _v) := by
  have p4016 := n4016 _v _q 
  have p8144 := n8144 _v _q h496
  have p5391 := n5391 _v _q 
  have p5255 := n5255 _v _q 
  exact FloorCertificate.node_19677 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p4016 p8144 p5391 p5255
theorem n19678 (_v : Vars) (_q : Query _v) (h496 : (e496 _v)) : (e2522 _v) := by
  have p8144 := n8144 _v _q h496
  have p5255 := n5255 _v _q 
  have p4016 := n4016 _v _q 
  exact FloorCertificate.node_19678 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8144 p5255 p4016
theorem n19679 (_v : Vars) (_q : Query _v) (h496 : (e496 _v)) (h5362 : (e5362 _v)) : (e4269 _v) := by
  have p18194 := n18194 _v _q 
  have p19677 := n19677 _v _q h496
  have p16992 := n16992 _v _q 
  have p7488 := n7488 _v _q h5362
  have p14737 := n14737 _v _q h496
  have p19678 := n19678 _v _q h496
  have p19630 := n19630 _v _q 
  simp only [e436, e474, e2296, e2522, e2722, e4264, e4269, e5237, e5247, e5362, e5392, e6549, e6650, e6742, e18193] at *
  tauto
theorem n19680 (_v : Vars) (_q : Query _v) (h496 : (e496 _v)) (h5362 : (e5362 _v)) : (e7489 _v) := by
  have p14966 := n14966 _v _q 
  have p19676 := n19676 _v _q h496 h5362
  have p19679 := n19679 _v _q h496 h5362
  simp only [e4263, e4264, e4268, e4269, e4270, e4271, e4959] at *
  tauto
theorem n19681 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4302 : (e4302 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e2529 _v) := by
  have p18650 := n18650 _v _q 
  have p19649 := n19649 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h4096 h4156 h4199 h4260 h4302 h4369 h4434 h4608 h4675 h4787 h4813 h4872
  have p4994 := n4994 _v _q h3069
  have p4981 := n4981 _v _q h4260
  have p5001 := n5001 _v _q h4096
  have p4999 := n4999 _v _q h91
  have p5010 := n5010 _v _q h70
  have p5003 := n5003 _v _q h4199
  have p5007 := n5007 _v _q h225
  have p4992 := n4992 _v _q h442
  have p4996 := n4996 _v _q h3937
  have p16528 := n16528 _v _q h4302
  have p4987 := n4987 _v _q h4434
  have p17137 := n17137 _v _q h4059
  have p16517 := n16517 _v _q h4302
  have p4983 := n4983 _v _q h4813
  have p4995 := n4995 _v _q h4369
  have p4998 := n4998 _v _q h3152
  have p5008 := n5008 _v _q h4787
  have p5006 := n5006 _v _q h4675
  have p17056 := n17056 _v _q h3946
  have p17061 := n17061 _v _q h4747
  have p4985 := n4985 _v _q h4156
  have p4988 := n4988 _v _q h488
  have p4986 := n4986 _v _q h3105
  have p4984 := n4984 _v _q h4872
  have p4991 := n4991 _v _q h4608
  have p16532 := n16532 _v _q h4302
  simp only [e70, e75, e91, e95, e225, e230, e442, e443, e488, e493, e2364, e2529, e3069, e3074, e3105, e3106, e3152, e3156, e3937, e3942, e3946, e3947, e4059, e4064, e4096, e4097, e4156, e4157, e4199, e4200, e4260, e4261, e4306, e4311, e4369, e4370, e4398, e4403, e4434, e4435, e4608, e4609, e4675, e4676, e4747, e4752, e4787, e4788, e4813, e4814, e4872, e4873, e6583, e7935, e7943, e18649] at *
  tauto
theorem n19682 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h6784 : (e6784 _v)) : (e8407 _v) := by
  have p19396 := n19396 _v _q 
  have p19652 := n19652 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4260 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872 h6784
  simp only [e8395, e8398, e8405, e8406, e8407, e8507] at *
  tauto
theorem n19683 (_v : Vars) (_q : Query _v) (h6758 : (e6758 _v)) : (e2475 _v) := by
  have p17852 := n17852 _v _q 
  have p15652 := n15652 _v _q h6758
  have p12891 := n12891 _v _q h6758
  have p16520 := n16520 _v _q h6758
  have p15654 := n15654 _v _q h6758
  have p19665 := n19665 _v _q 
  have p16580 := n16580 _v _q h6758
  have p16581 := n16581 _v _q h6758
  have p16582 := n16582 _v _q h6758
  have p16583 := n16583 _v _q h6758
  have p16585 := n16585 _v _q h6758
  have p16586 := n16586 _v _q h6758
  have p17758 := n17758 _v _q 
  have p15667 := n15667 _v _q h6758
  have p16851 := n16851 _v _q h6758
  have p15669 := n15669 _v _q h6758
  have p15673 := n15673 _v _q h6758
  simp only [e91, e95, e225, e230, e488, e493, e2475, e2793, e3069, e3074, e3105, e3106, e3152, e3156, e3937, e3942, e4096, e4097, e4369, e4370, e4434, e4435, e4608, e4609, e4787, e4788, e4813, e4814, e4838, e4839, e4872, e4873, e6784, e17851] at *
  tauto
theorem n19684 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) (h5362 : (e5362 _v)) : (e4269 _v) := by
  have p18232 := n18232 _v _q 
  have p15865 := n15865 _v _q h251
  have p7488 := n7488 _v _q h5362
  have p15816 := n15816 _v _q h251
  have p19630 := n19630 _v _q 
  simp only [e436, e2296, e2522, e2722, e4264, e4269, e5362, e6549, e6650, e6742, e18231] at *
  tauto
theorem n19685 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) (h5362 : (e5362 _v)) : (e7489 _v) := by
  have p14966 := n14966 _v _q 
  have p19684 := n19684 _v _q h251 h5362
  have p19667 := n19667 _v _q h251 h5362
  simp only [e4263, e4264, e4268, e4269, e4270, e4271, e4959] at *
  tauto
theorem n19686 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h5362 : (e5362 _v)) : (e8292 _v) := by
  have p14657 := n14657 _v _q 
  have p19668 := n19668 _v _q h2351 h5362
  simp only [e2522, e4811, e4812, e4813, e4814, e6650, e8284, e8292, e8295] at *
  tauto
theorem n19687 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h5362 : (e5362 _v)) : (e4813 _v) := by
  have p16259 := n16259 _v _q 
  have p19686 := n19686 _v _q h2351 h5362
  simp only [e4811, e4812, e4813, e4814, e8284, e8285, e8292] at *
  tauto
theorem n19688 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h2468 : (e2468 _v)) (h5362 : (e5362 _v)) : (e2242 _v) := by
  have p8438 := n8438 _v _q h2468
  have p19674 := n19674 _v _q h5362
  have p8464 := n8464 _v _q h2351
  exact FloorCertificate.node_19688 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8438 p19674 p8464
end
end Assembly
