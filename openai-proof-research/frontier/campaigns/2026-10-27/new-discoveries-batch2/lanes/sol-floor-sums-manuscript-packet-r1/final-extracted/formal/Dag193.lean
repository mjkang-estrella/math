import Dag192
import generated.th_lemma_22
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n18563 (_v : Vars) (_q : Query _v)  : (e18562 _v) := by
  by_contra hc
  change ¬ ((e2529 _v) ∨ (e2475 _v) ∨ (¬ (e4608 _v)) ∨ (e2634 _v) ∨ (¬ (e4369 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e4903 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e3976 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e3169 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4156 _v))) at hc
  have h70 : (e70 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h225 : (e225 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h442 : (e442 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))
  have h488 : (e488 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))
  have h3069 : (e3069 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))
  have h3105 : (e3105 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h3169 : (e3169 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h3976 : (e3976 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h4096 : (e4096 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h4156 : (e4156 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn)))))))))))))))))))))))))
  have h4199 : (e4199 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h4260 : (e4260 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))
  have h4369 : (e4369 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4608 : (e4608 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4675 : (e4675 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))
  have h4872 : (e4872 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))
  have h4903 : (e4903 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h6700 : (e6700 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h8038 : (e8038 _v) := (fun hn => hc (Or.inr (Or.inl hn)))
  have h8310 : (e8310 _v) := (fun hn => hc (Or.inl hn))
  have p18561 := n18561 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038 h8310
  exact p18561
theorem n18564 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3976 : (e3976 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h6700 : (e6700 _v)) (h8038 : (e8038 _v)) : (e2529 _v) := by
  have p18563 := n18563 _v _q 
  have p11027 := n11027 _v _q h6700
  have p4991 := n4991 _v _q h4608
  have p8602 := n8602 _v _q h8038
  have p4995 := n4995 _v _q h4369
  have p4996 := n4996 _v _q h3937
  have p4998 := n4998 _v _q h3152
  have p4999 := n4999 _v _q h91
  have p5001 := n5001 _v _q h4096
  have p5003 := n5003 _v _q h4199
  have p17129 := n17129 _v _q h4903
  have p5006 := n5006 _v _q h4675
  have p17076 := n17076 _v _q h3976
  have p5007 := n5007 _v _q h225
  have p5008 := n5008 _v _q h4787
  have p5005 := n5005 _v _q h3169
  have p5010 := n5010 _v _q h70
  have p4981 := n4981 _v _q h4260
  have p4988 := n4988 _v _q h488
  have p4986 := n4986 _v _q h3105
  have p4983 := n4983 _v _q h4813
  have p4994 := n4994 _v _q h3069
  have p4992 := n4992 _v _q h442
  have p4984 := n4984 _v _q h4872
  have p4985 := n4985 _v _q h4156
  change (e2529 _v) ∨ (e2475 _v) ∨ (¬ (e4608 _v)) ∨ (e2634 _v) ∨ (¬ (e4369 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e4903 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e3976 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e3169 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4156 _v)) at p18563
  change (¬ (e2634 _v)) at p11027
  change (¬ (e2475 _v)) at p8602
  rcases p18563 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (p8602 hlit))
  · exact (False.elim (hlit p4991))
  · exact (False.elim (p11027 hlit))
  · exact (False.elim (hlit p4995))
  · exact (False.elim (hlit p4996))
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p5001))
  · exact (False.elim (hlit p5003))
  · exact (False.elim (hlit p17129))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p17076))
  · exact (False.elim (hlit p5007))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p5005))
  · exact (False.elim (hlit p5010))
  · exact (False.elim (hlit p4981))
  · exact (False.elim (hlit p4988))
  · exact (False.elim (hlit p4986))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p4994))
  · exact (False.elim (hlit p4992))
  · exact (False.elim (hlit p4984))
  · exact (False.elim (hlit p4985))
theorem n18565 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3976 : (e3976 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h6700 : (e6700 _v)) (h8038 : (e8038 _v)) : (e8307 _v) := by
  have p14906 := n14906 _v _q 
  have p18564 := n18564 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  change (¬ (e2529 _v)) ∨ (¬ (e8301 _v)) at p14906
  rcases p14906 with hlit | hlit
  · exact (False.elim (hlit p18564))
  · exact hlit
theorem n18566 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3976 : (e3976 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h6700 : (e6700 _v)) (h8038 : (e8038 _v)) : (e4838 _v) := by
  have p16285 := n16285 _v _q 
  have p18565 := n18565 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  change (e8301 _v) ∨ (e4838 _v) at p16285
  change (¬ (e8301 _v)) at p18565
  rcases p16285 with hlit | hlit
  · exact (False.elim (p18565 hlit))
  · exact hlit
theorem n18567 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3976 : (e3976 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h6700 : (e6700 _v)) (h8038 : (e8038 _v)) : (e6676 _v) := by
  have p16394 := n16394 _v _q 
  have p18564 := n18564 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  have p18482 := n18482 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  have p18490 := n18490 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  exact FloorCertificate.node_18567 (e2 _v) (e7 _v) (e17 _v) (e45 _v) (e110 _v) (e2834 _v) (e2918 _v) p16394 p18564 p18482 p18490
theorem n18568 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3976 : (e3976 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h6700 : (e6700 _v)) (h8038 : (e8038 _v)) : (e7830 _v) := by
  have p14579 := n14579 _v _q 
  have p18567 := n18567 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  change (e2585 _v) ∨ (¬ (e7822 _v)) at p14579
  change (¬ (e2585 _v)) at p18567
  rcases p14579 with hlit | hlit
  · exact (False.elim (p18567 hlit))
  · exact hlit
theorem n18569 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3976 : (e3976 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h6700 : (e6700 _v)) (h8038 : (e8038 _v)) : (e4301 _v) := by
  have p14840 := n14840 _v _q 
  have p18568 := n18568 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  change (e7822 _v) ∨ (e4301 _v) at p14840
  change (¬ (e7822 _v)) at p18568
  rcases p14840 with hlit | hlit
  · exact (False.elim (p18568 hlit))
  · exact hlit
theorem n18570 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3976 : (e3976 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h6700 : (e6700 _v)) (h8038 : (e8038 _v)) : (e2536 _v) := by
  have p18126 := n18126 _v _q 
  have p18566 := n18566 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  have p18569 := n18569 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  have p18549 := n18549 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  have p18482 := n18482 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  have p8602 := n8602 _v _q h8038
  have p18494 := n18494 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  have p4991 := n4991 _v _q h4608
  have p4995 := n4995 _v _q h4369
  have p4996 := n4996 _v _q h3937
  have p4998 := n4998 _v _q h3152
  have p4999 := n4999 _v _q h91
  have p5001 := n5001 _v _q h4096
  have p5003 := n5003 _v _q h4199
  have p17129 := n17129 _v _q h4903
  have p5006 := n5006 _v _q h4675
  have p17076 := n17076 _v _q h3976
  have p5007 := n5007 _v _q h225
  have p5008 := n5008 _v _q h4787
  have p5005 := n5005 _v _q h3169
  have p5010 := n5010 _v _q h70
  have p4981 := n4981 _v _q h4260
  have p4988 := n4988 _v _q h488
  have p4986 := n4986 _v _q h3105
  have p4983 := n4983 _v _q h4813
  have p4994 := n4994 _v _q h3069
  have p4992 := n4992 _v _q h442
  have p4984 := n4984 _v _q h4872
  have p4985 := n4985 _v _q h4156
  have p18534 := n18534 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  change (e2536 _v) ∨ (¬ (e4838 _v)) ∨ (¬ (e4301 _v)) ∨ (¬ (e7935 _v)) ∨ (e4567 _v) ∨ (e2475 _v) ∨ (¬ (e191 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e4903 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e3976 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e3169 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e2358 _v)) at p18126
  change (¬ (e4567 _v)) at p18482
  change (¬ (e2475 _v)) at p8602
  rcases p18126 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p18566))
  · exact (False.elim (hlit p18569))
  · exact (False.elim (hlit p18549))
  · exact (False.elim (p18482 hlit))
  · exact (False.elim (p8602 hlit))
  · exact (False.elim (hlit p18494))
  · exact (False.elim (hlit p4991))
  · exact (False.elim (hlit p4995))
  · exact (False.elim (hlit p4996))
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p5001))
  · exact (False.elim (hlit p5003))
  · exact (False.elim (hlit p17129))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p17076))
  · exact (False.elim (hlit p5007))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p5005))
  · exact (False.elim (hlit p5010))
  · exact (False.elim (hlit p4981))
  · exact (False.elim (hlit p4988))
  · exact (False.elim (hlit p4986))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p4994))
  · exact (False.elim (hlit p4992))
  · exact (False.elim (hlit p4984))
  · exact (False.elim (hlit p4985))
  · exact (False.elim (hlit p18534))
theorem n18571 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3976 : (e3976 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h6700 : (e6700 _v)) (h8038 : (e8038 _v)) : (e4286 _v) := by
  have p17542 := n17542 _v _q 
  have p18482 := n18482 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  have p4992 := n4992 _v _q h442
  have p18570 := n18570 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  have p4984 := n4984 _v _q h4872
  have p4985 := n4985 _v _q h4156
  have p15336 := n15336 _v _q h8038
  have p18566 := n18566 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  have p18569 := n18569 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  have p18549 := n18549 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  have p17170 := n17170 _v _q h8038
  have p18494 := n18494 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  have p18536 := n18536 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  have p18537 := n18537 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  have p4991 := n4991 _v _q h4608
  have p17167 := n17167 _v _q h8038
  have p4995 := n4995 _v _q h4369
  have p4996 := n4996 _v _q h3937
  have p16918 := n16918 _v _q h8038
  have p4998 := n4998 _v _q h3152
  have p15194 := n15194 _v _q h8038
  have p4999 := n4999 _v _q h91
  have p15198 := n15198 _v _q h8038
  have p5001 := n5001 _v _q h4096
  have p15200 := n15200 _v _q h8038
  have p15203 := n15203 _v _q h8038
  have p18506 := n18506 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  have p5003 := n5003 _v _q h4199
  have p17168 := n17168 _v _q h8038
  have p17129 := n17129 _v _q h4903
  have p5006 := n5006 _v _q h4675
  have p17076 := n17076 _v _q h3976
  have p5007 := n5007 _v _q h225
  have p5008 := n5008 _v _q h4787
  have p5005 := n5005 _v _q h3169
  have p5010 := n5010 _v _q h70
  have p4981 := n4981 _v _q h4260
  have p15209 := n15209 _v _q h8038
  have p15211 := n15211 _v _q h8038
  have p4988 := n4988 _v _q h488
  have p4986 := n4986 _v _q h3105
  have p4983 := n4983 _v _q h4813
  have p17169 := n17169 _v _q h8038
  have p4994 := n4994 _v _q h3069
  have p15340 := n15340 _v _q h8038
  change (¬ (e4285 _v)) ∨ (e4567 _v) ∨ (¬ (e442 _v)) ∨ (¬ (e2536 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e8335 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4301 _v)) ∨ (¬ (e7935 _v)) ∨ (¬ (e4398 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e7606 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e3855 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e7749 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e7493 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e4491 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e3271 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e5100 _v)) ∨ (¬ (e4903 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e3976 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e3169 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e8045 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4724 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e7688 _v)) at p17542
  change (¬ (e4567 _v)) at p18482
  rcases p17542 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (p18482 hlit))
  · exact (False.elim (hlit p4992))
  · exact (False.elim (hlit p18570))
  · exact (False.elim (hlit p4984))
  · exact (False.elim (hlit p4985))
  · exact (False.elim (hlit p15336))
  · exact (False.elim (hlit p18566))
  · exact (False.elim (hlit p18569))
  · exact (False.elim (hlit p18549))
  · exact (False.elim (hlit p17170))
  · exact (False.elim (hlit p18494))
  · exact (False.elim (hlit p18536))
  · exact (False.elim (hlit p18537))
  · exact (False.elim (hlit p4991))
  · exact (False.elim (hlit p17167))
  · exact (False.elim (hlit p4995))
  · exact (False.elim (hlit p4996))
  · exact (False.elim (hlit p16918))
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p15194))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p15198))
  · exact (False.elim (hlit p5001))
  · exact (False.elim (hlit p15200))
  · exact (False.elim (hlit p15203))
  · exact (False.elim (hlit p18506))
  · exact (False.elim (hlit p5003))
  · exact (False.elim (hlit p17168))
  · exact (False.elim (hlit p17129))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p17076))
  · exact (False.elim (hlit p5007))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p5005))
  · exact (False.elim (hlit p5010))
  · exact (False.elim (hlit p4981))
  · exact (False.elim (hlit p15209))
  · exact (False.elim (hlit p15211))
  · exact (False.elim (hlit p4988))
  · exact (False.elim (hlit p4986))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p17169))
  · exact (False.elim (hlit p4994))
  · exact (False.elim (hlit p15340))
theorem n18572 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3976 : (e3976 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h6700 : (e6700 _v)) (h8038 : (e8038 _v)) : (e7798 _v) := by
  have p16274 := n16274 _v _q 
  have p18571 := n18571 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  change (e7798 _v) ∨ (e4285 _v) at p16274
  change (¬ (e4285 _v)) at p18571
  rcases p16274 with hlit | hlit
  · exact hlit
  · exact (False.elim (p18571 hlit))
theorem n18573 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3976 : (e3976 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h6700 : (e6700 _v)) (h8038 : (e8038 _v)) : (e3573 _v) := by
  have p14426 := n14426 _v _q 
  have p18570 := n18570 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  change (¬ (e2536 _v)) ∨ (¬ (e3572 _v)) at p14426
  rcases p14426 with hlit | hlit
  · exact (False.elim (hlit p18570))
  · exact hlit
theorem n18574 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3976 : (e3976 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h6700 : (e6700 _v)) (h8038 : (e8038 _v)) : (e3566 _v) := by
  have p7179 := n7179 _v _q 
  have p18573 := n18573 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  change (e3572 _v) ∨ (e3566 _v) at p7179
  change (¬ (e3572 _v)) at p18573
  rcases p7179 with hlit | hlit
  · exact (False.elim (p18573 hlit))
  · exact hlit
theorem n18575 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3976 : (e3976 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h6700 : (e6700 _v)) (h8038 : (e8038 _v)) : (e7807 _v) := by
  have p14837 := n14837 _v _q 
  have p18572 := n18572 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  change (¬ (e2303 _v)) ∨ (¬ (e7798 _v)) at p14837
  rcases p14837 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p18572))
theorem n18576 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3976 : (e3976 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h6700 : (e6700 _v)) (h8038 : (e8038 _v)) : (e7819 _v) := by
  have p14994 := n14994 _v _q 
  have p18575 := n18575 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  change (e2303 _v) ∨ (¬ (e7818 _v)) at p14994
  change (¬ (e2303 _v)) at p18575
  rcases p14994 with hlit | hlit
  · exact (False.elim (p18575 hlit))
  · exact hlit
theorem n18577 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3976 : (e3976 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h6700 : (e6700 _v)) (h8038 : (e8038 _v)) : (e7814 _v) := by
  have p15221 := n15221 _v _q 
  have p18576 := n18576 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  change (e7818 _v) ∨ (e7814 _v) at p15221
  change (¬ (e7818 _v)) at p18576
  rcases p15221 with hlit | hlit
  · exact (False.elim (p18576 hlit))
  · exact hlit
theorem n18578 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3976 : (e3976 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h6700 : (e6700 _v)) (h8038 : (e8038 _v)) : (e4658 _v) := by
  have p4984 := n4984 _v _q h4872
  have p18577 := n18577 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  have p4985 := n4985 _v _q h4156
  have p18574 := n18574 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  have p8663 := n8663 _v _q 
  have p16394 := n16394 _v _q 
  have p18490 := n18490 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  have p18482 := n18482 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  have p11027 := n11027 _v _q h6700
  have p17074 := n17074 _v _q 
  have p15336 := n15336 _v _q h8038
  have p18566 := n18566 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  have p18569 := n18569 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  have p18549 := n18549 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  have p17170 := n17170 _v _q h8038
  have p8602 := n8602 _v _q h8038
  have p17072 := n17072 _v _q 
  have p17091 := n17091 _v _q 
  have p17080 := n17080 _v _q 
  have p17098 := n17098 _v _q 
  have p17078 := n17078 _v _q 
  have p18494 := n18494 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  have p18536 := n18536 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  have p18537 := n18537 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  have p17087 := n17087 _v _q 
  have p17067 := n17067 _v _q 
  have p17100 := n17100 _v _q 
  have p4991 := n4991 _v _q h4608
  have p18495 := n18495 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  have p17110 := n17110 _v _q 
  have p17115 := n17115 _v _q 
  have p17083 := n17083 _v _q 
  have p16576 := n16576 _v _q 
  have p17058 := n17058 _v _q 
  have p17113 := n17113 _v _q 
  have p17064 := n17064 _v _q 
  have p17102 := n17102 _v _q 
  have p13951 := n13951 _v _q 
  have p17167 := n17167 _v _q h8038
  have p17096 := n17096 _v _q 
  have p16929 := n16929 _v _q 
  have p17122 := n17122 _v _q 
  have p17124 := n17124 _v _q 
  have p17106 := n17106 _v _q 
  have p17108 := n17108 _v _q 
  have p17104 := n17104 _v _q 
  have p4995 := n4995 _v _q h4369
  have p17117 := n17117 _v _q 
  have p17120 := n17120 _v _q 
  have p17069 := n17069 _v _q 
  have p17141 := n17141 _v _q 
  have p17093 := n17093 _v _q 
  have p17131 := n17131 _v _q 
  have p17053 := n17053 _v _q 
  have p4996 := n4996 _v _q h3937
  have p16918 := n16918 _v _q h8038
  have p4998 := n4998 _v _q h3152
  have p18497 := n18497 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  have p15194 := n15194 _v _q h8038
  have p4999 := n4999 _v _q h91
  have p17055 := n17055 _v _q 
  have p15198 := n15198 _v _q h8038
  have p5001 := n5001 _v _q h4096
  have p17136 := n17136 _v _q 
  have p17127 := n17127 _v _q 
  have p15200 := n15200 _v _q h8038
  have p15203 := n15203 _v _q h8038
  have p18506 := n18506 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  have p5003 := n5003 _v _q h4199
  have p17168 := n17168 _v _q h8038
  have p17129 := n17129 _v _q h4903
  have p5006 := n5006 _v _q h4675
  have p17076 := n17076 _v _q h3976
  have p17147 := n17147 _v _q 
  have p5007 := n5007 _v _q h225
  have p5008 := n5008 _v _q h4787
  have p17133 := n17133 _v _q 
  have p5005 := n5005 _v _q h3169
  have p5010 := n5010 _v _q h70
  have p4981 := n4981 _v _q h4260
  have p15209 := n15209 _v _q h8038
  have p15211 := n15211 _v _q h8038
  have p4988 := n4988 _v _q h488
  have p4986 := n4986 _v _q h3105
  have p16175 := n16175 _v _q 
  have p4983 := n4983 _v _q h4813
  have p17169 := n17169 _v _q h8038
  have p4994 := n4994 _v _q h3069
  have p4992 := n4992 _v _q h442
  exact FloorCertificate.node_18578 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e61 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2834 _v) (e2849 _v) (e2863 _v) (e2877 _v) (e2883 _v) (e2898 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e3164 _v) (e4215 _v) (e4541 _v) (e4808 _v) p4984 p18577 p4985 p18574 p8663 p16394 p18490 p18482 p11027 p17074 p15336 p18566 p18569 p18549 p17170 p8602 p17072 p17091 p17080 p17098 p17078 p18494 p18536 p18537 p17087 p17067 p17100 p4991 p18495 p17110 p17115 p17083 p16576 p17058 p17113 p17064 p17102 p13951 p17167 p17096 p16929 p17122 p17124 p17106 p17108 p17104 p4995 p17117 p17120 p17069 p17141 p17093 p17131 p17053 p4996 p16918 p4998 p18497 p15194 p4999 p17055 p15198 p5001 p17136 p17127 p15200 p15203 p18506 p5003 p17168 p17129 p5006 p17076 p17147 p5007 p5008 p17133 p5005 p5010 p4981 p15209 p15211 p4988 p4986 p16175 p4983 p17169 p4994 p4992
theorem n18579 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3976 : (e3976 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h6700 : (e6700 _v)) (h8038 : (e8038 _v)) : (e4649 _v) := by
  have p18575 := n18575 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  have p15340 := n15340 _v _q h8038
  have p16394 := n16394 _v _q 
  have p18482 := n18482 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  have p18490 := n18490 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  have p4984 := n4984 _v _q h4872
  have p18577 := n18577 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  have p4985 := n4985 _v _q h4156
  have p18574 := n18574 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  have p8663 := n8663 _v _q 
  have p11027 := n11027 _v _q h6700
  have p17074 := n17074 _v _q 
  have p15336 := n15336 _v _q h8038
  have p18566 := n18566 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  have p18569 := n18569 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  have p18549 := n18549 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  have p17170 := n17170 _v _q h8038
  have p8602 := n8602 _v _q h8038
  have p17072 := n17072 _v _q 
  have p17091 := n17091 _v _q 
  have p17080 := n17080 _v _q 
  have p17098 := n17098 _v _q 
  have p17078 := n17078 _v _q 
  have p18494 := n18494 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  have p18536 := n18536 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  have p18537 := n18537 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  have p17087 := n17087 _v _q 
  have p17067 := n17067 _v _q 
  have p17100 := n17100 _v _q 
  have p4991 := n4991 _v _q h4608
  have p18495 := n18495 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  have p17110 := n17110 _v _q 
  have p17115 := n17115 _v _q 
  have p17083 := n17083 _v _q 
  have p16576 := n16576 _v _q 
  have p17058 := n17058 _v _q 
  have p17113 := n17113 _v _q 
  have p17064 := n17064 _v _q 
  have p17102 := n17102 _v _q 
  have p13951 := n13951 _v _q 
  have p17167 := n17167 _v _q h8038
  have p17096 := n17096 _v _q 
  have p16929 := n16929 _v _q 
  have p17122 := n17122 _v _q 
  have p17124 := n17124 _v _q 
  have p17106 := n17106 _v _q 
  have p17108 := n17108 _v _q 
  have p17104 := n17104 _v _q 
  have p4995 := n4995 _v _q h4369
  have p17117 := n17117 _v _q 
  have p17120 := n17120 _v _q 
  have p17069 := n17069 _v _q 
  have p17141 := n17141 _v _q 
  have p17093 := n17093 _v _q 
  have p17131 := n17131 _v _q 
  have p17053 := n17053 _v _q 
  have p4996 := n4996 _v _q h3937
  have p16918 := n16918 _v _q h8038
  have p4998 := n4998 _v _q h3152
  have p18497 := n18497 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  have p15194 := n15194 _v _q h8038
  have p4999 := n4999 _v _q h91
  have p17055 := n17055 _v _q 
  have p15198 := n15198 _v _q h8038
  have p5001 := n5001 _v _q h4096
  have p17136 := n17136 _v _q 
  have p17127 := n17127 _v _q 
  have p15200 := n15200 _v _q h8038
  have p15203 := n15203 _v _q h8038
  have p18506 := n18506 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  have p5003 := n5003 _v _q h4199
  have p17168 := n17168 _v _q h8038
  have p17129 := n17129 _v _q h4903
  have p5006 := n5006 _v _q h4675
  have p17076 := n17076 _v _q h3976
  have p17147 := n17147 _v _q 
  have p5007 := n5007 _v _q h225
  have p5008 := n5008 _v _q h4787
  have p17133 := n17133 _v _q 
  have p5005 := n5005 _v _q h3169
  have p5010 := n5010 _v _q h70
  have p4981 := n4981 _v _q h4260
  have p15209 := n15209 _v _q h8038
  have p15211 := n15211 _v _q h8038
  have p4988 := n4988 _v _q h488
  have p4986 := n4986 _v _q h3105
  have p16175 := n16175 _v _q 
  have p4983 := n4983 _v _q h4813
  have p17169 := n17169 _v _q h8038
  have p4994 := n4994 _v _q h3069
  have p4992 := n4992 _v _q h442
  exact FloorCertificate.node_18579 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e61 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2834 _v) (e2849 _v) (e2863 _v) (e2877 _v) (e2879 _v) (e2883 _v) (e2898 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e3164 _v) (e4215 _v) (e4541 _v) (e4808 _v) p18575 p15340 p16394 p18482 p18490 p4984 p18577 p4985 p18574 p8663 p11027 p17074 p15336 p18566 p18569 p18549 p17170 p8602 p17072 p17091 p17080 p17098 p17078 p18494 p18536 p18537 p17087 p17067 p17100 p4991 p18495 p17110 p17115 p17083 p16576 p17058 p17113 p17064 p17102 p13951 p17167 p17096 p16929 p17122 p17124 p17106 p17108 p17104 p4995 p17117 p17120 p17069 p17141 p17093 p17131 p17053 p4996 p16918 p4998 p18497 p15194 p4999 p17055 p15198 p5001 p17136 p17127 p15200 p15203 p18506 p5003 p17168 p17129 p5006 p17076 p17147 p5007 p5008 p17133 p5005 p5010 p4981 p15209 p15211 p4988 p4986 p16175 p4983 p17169 p4994 p4992
theorem n18580 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3976 : (e3976 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h6700 : (e6700 _v)) (h8038 : (e8038 _v)) : (e4660 _v) := by
  have p15168 := n15168 _v _q 
  have p18578 := n18578 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  change (e4660 _v) ∨ (e4653 _v) at p15168
  change (¬ (e4653 _v)) at p18578
  rcases p15168 with hlit | hlit
  · exact hlit
  · exact (False.elim (p18578 hlit))
theorem n18581 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3976 : (e3976 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h6700 : (e6700 _v)) (h8038 : (e8038 _v)) : (e6583 _v) := by
  have p14686 := n14686 _v _q 
  have p18580 := n18580 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  change (¬ (e2364 _v)) ∨ (¬ (e4660 _v)) at p14686
  rcases p14686 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p18580))
theorem n18582 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3976 : (e3976 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h6700 : (e6700 _v)) (h8038 : (e8038 _v)) : (e8149 _v) := by
  have p15027 := n15027 _v _q 
  have p18579 := n18579 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  change (e8149 _v) ∨ (e4648 _v) at p15027
  change (¬ (e4648 _v)) at p18579
  rcases p15027 with hlit | hlit
  · exact hlit
  · exact (False.elim (p18579 hlit))
theorem n18583 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3976 : (e3976 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h6700 : (e6700 _v)) (h8038 : (e8038 _v)) : (e7489 _v) := by
  have p14632 := n14632 _v _q 
  have p18581 := n18581 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  have p18582 := n18582 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  change (e2364 _v) ∨ (¬ (e8149 _v)) at p14632
  change (¬ (e2364 _v)) at p18581
  rcases p14632 with hlit | hlit
  · exact (False.elim (p18581 hlit))
  · exact (False.elim (hlit p18582))
theorem n18585 (_v : Vars) (_q : Query _v)  : (e18584 _v) := by
  by_contra hc
  change ¬ ((e2634 _v) ∨ (¬ (e4872 _v)) ∨ (¬ (e4156 _v)) ∨ (e2475 _v) ∨ (¬ (e4608 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e4903 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e3976 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e3169 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e442 _v))) at hc
  have h70 : (e70 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h225 : (e225 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h442 : (e442 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))))))))))))))))))))
  have h488 : (e488 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))
  have h3069 : (e3069 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))
  have h3105 : (e3105 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h3169 : (e3169 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h3976 : (e3976 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h4096 : (e4096 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h4156 : (e4156 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4199 : (e4199 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h4260 : (e4260 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))
  have h4369 : (e4369 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h4608 : (e4608 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4675 : (e4675 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))
  have h4872 : (e4872 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h4903 : (e4903 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h6700 : (e6700 _v) := (fun hn => hc (Or.inl hn))
  have h8038 : (e8038 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have p18583 := n18583 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  exact p18583
theorem n18586 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h8038 : (e8038 _v)) : (e2634 _v) := by
  have p18585 := n18585 _v _q 
  have p17966 := n17966 _v _q h91 h225 h488 h3069 h3105 h3152 h3937 h4096 h4369 h4434 h4608 h4787 h4813 h4838 h4872 h8038
  have p4985 := n4985 _v _q h4156
  have p8602 := n8602 _v _q h8038
  have p4991 := n4991 _v _q h4608
  have p4995 := n4995 _v _q h4369
  have p4996 := n4996 _v _q h3937
  have p4998 := n4998 _v _q h3152
  have p4999 := n4999 _v _q h91
  have p5001 := n5001 _v _q h4096
  have p5003 := n5003 _v _q h4199
  have p5005 := n5005 _v _q h3169
  have p5006 := n5006 _v _q h4675
  have p4984 := n4984 _v _q h4872
  have p5007 := n5007 _v _q h225
  have p5008 := n5008 _v _q h4787
  have p17968 := n17968 _v _q h91 h225 h488 h3069 h3105 h3152 h3937 h4096 h4369 h4434 h4608 h4787 h4813 h4838 h4872 h8038
  have p5010 := n5010 _v _q h70
  have p4981 := n4981 _v _q h4260
  have p4988 := n4988 _v _q h488
  have p4986 := n4986 _v _q h3105
  have p4983 := n4983 _v _q h4813
  have p4994 := n4994 _v _q h3069
  have p4992 := n4992 _v _q h442
  change (e2634 _v) ∨ (¬ (e4872 _v)) ∨ (¬ (e4156 _v)) ∨ (e2475 _v) ∨ (¬ (e4608 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e4903 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e3976 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e3169 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e442 _v)) at p18585
  change (¬ (e2475 _v)) at p8602
  rcases p18585 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p4984))
  · exact (False.elim (hlit p4985))
  · exact (False.elim (p8602 hlit))
  · exact (False.elim (hlit p4991))
  · exact (False.elim (hlit p4995))
  · exact (False.elim (hlit p4996))
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p5001))
  · exact (False.elim (hlit p5003))
  · exact (False.elim (hlit p17968))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p17966))
  · exact (False.elim (hlit p5007))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p5005))
  · exact (False.elim (hlit p5010))
  · exact (False.elim (hlit p4981))
  · exact (False.elim (hlit p4988))
  · exact (False.elim (hlit p4986))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p4994))
  · exact (False.elim (hlit p4992))
theorem n18587 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3976 : (e3976 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h6700 : (e6700 _v)) (h8038 : (e8038 _v)) : (e4908 _v) := by
  have p18585 := n18585 _v _q 
  have p8602 := n8602 _v _q h8038
  have p4985 := n4985 _v _q h4156
  have p17076 := n17076 _v _q h3976
  have p4991 := n4991 _v _q h4608
  have p4995 := n4995 _v _q h4369
  have p4996 := n4996 _v _q h3937
  have p4998 := n4998 _v _q h3152
  have p4999 := n4999 _v _q h91
  have p5001 := n5001 _v _q h4096
  have p5003 := n5003 _v _q h4199
  have p5005 := n5005 _v _q h3169
  have p5006 := n5006 _v _q h4675
  have p4984 := n4984 _v _q h4872
  have p5007 := n5007 _v _q h225
  have p5008 := n5008 _v _q h4787
  have p11027 := n11027 _v _q h6700
  have p5010 := n5010 _v _q h70
  have p4981 := n4981 _v _q h4260
  have p4988 := n4988 _v _q h488
  have p4986 := n4986 _v _q h3105
  have p4983 := n4983 _v _q h4813
  have p4994 := n4994 _v _q h3069
  have p4992 := n4992 _v _q h442
  change (e2634 _v) ∨ (¬ (e4872 _v)) ∨ (¬ (e4156 _v)) ∨ (e2475 _v) ∨ (¬ (e4608 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e4903 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e3976 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e3169 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e442 _v)) at p18585
  change (¬ (e2475 _v)) at p8602
  change (¬ (e2634 _v)) at p11027
  rcases p18585 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact (False.elim (p11027 hlit))
  · exact (False.elim (hlit p4984))
  · exact (False.elim (hlit p4985))
  · exact (False.elim (p8602 hlit))
  · exact (False.elim (hlit p4991))
  · exact (False.elim (hlit p4995))
  · exact (False.elim (hlit p4996))
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p5001))
  · exact (False.elim (hlit p5003))
  · exact hlit
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p17076))
  · exact (False.elim (hlit p5007))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p5005))
  · exact (False.elim (hlit p5010))
  · exact (False.elim (hlit p4981))
  · exact (False.elim (hlit p4988))
  · exact (False.elim (hlit p4986))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p4994))
  · exact (False.elim (hlit p4992))
theorem n18588 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3976 : (e3976 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h6700 : (e6700 _v)) (h8038 : (e8038 _v)) : (e4909 _v) := by
  have p14973 := n14973 _v _q 
  have p18587 := n18587 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4608 h4675 h4787 h4813 h4872 h6700 h8038
  change (e4909 _v) ∨ (e4903 _v) at p14973
  change (¬ (e4903 _v)) at p18587
  rcases p14973 with hlit | hlit
  · exact hlit
  · exact (False.elim (p18587 hlit))
theorem n18589 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3976 : (e3976 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h6700 : (e6700 _v)) (h8038 : (e8038 _v)) : (e3170 _v) := by
  have p18585 := n18585 _v _q 
  have p11027 := n11027 _v _q h6700
  have p4985 := n4985 _v _q h4156
  have p17076 := n17076 _v _q h3976
  have p4991 := n4991 _v _q h4608
  have p4995 := n4995 _v _q h4369
  have p4996 := n4996 _v _q h3937
  have p4998 := n4998 _v _q h3152
  have p4999 := n4999 _v _q h91
  have p5001 := n5001 _v _q h4096
  have p5003 := n5003 _v _q h4199
  have p8602 := n8602 _v _q h8038
  have p5006 := n5006 _v _q h4675
  have p4984 := n4984 _v _q h4872
  have p5007 := n5007 _v _q h225
  have p5008 := n5008 _v _q h4787
  have p17129 := n17129 _v _q h4903
  have p5010 := n5010 _v _q h70
  have p4981 := n4981 _v _q h4260
  have p4988 := n4988 _v _q h488
  have p4986 := n4986 _v _q h3105
  have p4983 := n4983 _v _q h4813
  have p4994 := n4994 _v _q h3069
  have p4992 := n4992 _v _q h442
  change (e2634 _v) ∨ (¬ (e4872 _v)) ∨ (¬ (e4156 _v)) ∨ (e2475 _v) ∨ (¬ (e4608 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e4903 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e3976 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e3169 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e442 _v)) at p18585
  change (¬ (e2634 _v)) at p11027
  change (¬ (e2475 _v)) at p8602
  rcases p18585 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact (False.elim (p11027 hlit))
  · exact (False.elim (hlit p4984))
  · exact (False.elim (hlit p4985))
  · exact (False.elim (p8602 hlit))
  · exact (False.elim (hlit p4991))
  · exact (False.elim (hlit p4995))
  · exact (False.elim (hlit p4996))
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p5001))
  · exact (False.elim (hlit p5003))
  · exact (False.elim (hlit p17129))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p17076))
  · exact (False.elim (hlit p5007))
  · exact (False.elim (hlit p5008))
  · exact hlit
  · exact (False.elim (hlit p5010))
  · exact (False.elim (hlit p4981))
  · exact (False.elim (hlit p4988))
  · exact (False.elim (hlit p4986))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p4994))
  · exact (False.elim (hlit p4992))
theorem n18590 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3976 : (e3976 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h6700 : (e6700 _v)) (h8038 : (e8038 _v)) : (e7489 _v) := by
  have p14769 := n14769 _v _q 
  have p18589 := n18589 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  have p15233 := n15233 _v _q h6700
  change (e6888 _v) ∨ (e3169 _v) at p14769
  change (¬ (e3169 _v)) at p18589
  change (¬ (e6888 _v)) at p15233
  rcases p14769 with hlit | hlit
  · exact (False.elim (p15233 hlit))
  · exact (False.elim (p18589 hlit))
theorem n18591 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h225 : (e225 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h4096 : (e4096 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) (h8038 : (e8038 _v)) (h8398 : (e8398 _v)) : (e2793 _v) := by
  have p17800 := n17800 _v _q 
  have p8602 := n8602 _v _q h8038
  have p4988 := n4988 _v _q h488
  have p4986 := n4986 _v _q h3105
  have p4983 := n4983 _v _q h4813
  have p4994 := n4994 _v _q h3069
  have p4984 := n4984 _v _q h4872
  have p4991 := n4991 _v _q h4608
  have p4972 := n4972 _v _q h4899
  have p4998 := n4998 _v _q h3152
  have p4995 := n4995 _v _q h4369
  have p17208 := n17208 _v _q h8398
  have p4999 := n4999 _v _q h91
  have p5001 := n5001 _v _q h4096
  have p4989 := n4989 _v _q h4838
  have p4996 := n4996 _v _q h3937
  have p5007 := n5007 _v _q h225
  have p4987 := n4987 _v _q h4434
  have p5008 := n5008 _v _q h4787
  change (e2793 _v) ∨ (e2475 _v) ∨ (¬ (e488 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e8398 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4899 _v)) ∨ (¬ (e4787 _v)) at p17800
  change (¬ (e2475 _v)) at p8602
  rcases p17800 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (p8602 hlit))
  · exact (False.elim (hlit p4988))
  · exact (False.elim (hlit p4986))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p4994))
  · exact (False.elim (hlit p4984))
  · exact (False.elim (hlit p4991))
  · exact (False.elim (hlit p4989))
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p4995))
  · exact (False.elim (hlit p17208))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p5001))
  · exact (False.elim (hlit p4987))
  · exact (False.elim (hlit p4996))
  · exact (False.elim (hlit p5007))
  · exact (False.elim (hlit p4972))
  · exact (False.elim (hlit p5008))
theorem n18592 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3976 : (e3976 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) (h6700 : (e6700 _v)) (h8038 : (e8038 _v)) (h8398 : (e8398 _v)) : (e7489 _v) := by
  have p14701 := n14701 _v _q 
  have p18588 := n18588 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4608 h4675 h4787 h4813 h4872 h6700 h8038
  have p18591 := n18591 _v _q h91 h225 h488 h3069 h3105 h3152 h3937 h4096 h4369 h4434 h4608 h4787 h4813 h4838 h4872 h4899 h8038 h8398
  change (¬ (e2793 _v)) ∨ (¬ (e4909 _v)) at p14701
  rcases p14701 with hlit | hlit
  · exact (False.elim (hlit p18591))
  · exact (False.elim (hlit p18588))
theorem n18593 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h8038 : (e8038 _v)) : (e3180 _v) := by
  have p14361 := n14361 _v _q 
  have p18586 := n18586 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h4096 h4156 h4199 h4260 h4369 h4434 h4608 h4675 h4787 h4813 h4838 h4872 h8038
  change (¬ (e2634 _v)) ∨ (¬ (e3179 _v)) at p14361
  rcases p14361 with hlit | hlit
  · exact (False.elim (hlit p18586))
  · exact hlit
theorem n18594 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h8038 : (e8038 _v)) : (e3173 _v) := by
  have p6907 := n6907 _v _q 
  have p18593 := n18593 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h4096 h4156 h4199 h4260 h4369 h4434 h4608 h4675 h4787 h4813 h4838 h4872 h8038
  change (e3179 _v) ∨ (e3173 _v) at p6907
  change (¬ (e3179 _v)) at p18593
  rcases p6907 with hlit | hlit
  · exact (False.elim (p18593 hlit))
  · exact hlit
theorem n18595 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h8038 : (e8038 _v)) : (e2310 _v) := by
  have p11365 := n11365 _v _q 
  have p18586 := n18586 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h4096 h4156 h4199 h4260 h4369 h4434 h4608 h4675 h4787 h4813 h4838 h4872 h8038
  change (e2310 _v) ∨ (¬ (e2634 _v)) at p11365
  rcases p11365 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p18586))
theorem n18596 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h8038 : (e8038 _v)) : (e3278 _v) := by
  have p14378 := n14378 _v _q 
  have p18595 := n18595 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h4096 h4156 h4199 h4260 h4369 h4434 h4608 h4675 h4787 h4813 h4838 h4872 h8038
  change (¬ (e2310 _v)) ∨ (¬ (e3277 _v)) at p14378
  rcases p14378 with hlit | hlit
  · exact (False.elim (hlit p18595))
  · exact hlit
theorem n18597 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h8038 : (e8038 _v)) : (e3271 _v) := by
  have p6982 := n6982 _v _q 
  have p18596 := n18596 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h4096 h4156 h4199 h4260 h4369 h4434 h4608 h4675 h4787 h4813 h4838 h4872 h8038
  change (e3277 _v) ∨ (e3271 _v) at p6982
  change (¬ (e3277 _v)) at p18596
  rcases p6982 with hlit | hlit
  · exact (False.elim (p18596 hlit))
  · exact hlit
theorem n18598 (_v : Vars) (_q : Query _v)  : (e5016 _v) := by
  simp only [e3172, e3173, e3177, e3178, e3179, e5016] at *
  tauto
theorem n18599 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h8038 : (e8038 _v)) : (e3172 _v) := by
  have p18598 := n18598 _v _q 
  have p18593 := n18593 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h4096 h4156 h4199 h4260 h4369 h4434 h4608 h4675 h4787 h4813 h4838 h4872 h8038
  change (e3179 _v) ∨ (e3172 _v) at p18598
  change (¬ (e3179 _v)) at p18593
  rcases p18598 with hlit | hlit
  · exact (False.elim (p18593 hlit))
  · exact hlit
theorem n18601 (_v : Vars) (_q : Query _v)  : (e18600 _v) := by
  by_contra hc
  change ¬ ((e2634 _v) ∨ (¬ (e4156 _v)) ∨ (¬ (e3976 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e4199 _v)) ∨ (e2475 _v) ∨ (¬ (e4675 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4903 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e442 _v))) at hc
  have h70 : (e70 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h225 : (e225 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h442 : (e442 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn)))))))))))))))))))))))
  have h488 : (e488 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))
  have h3069 : (e3069 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))
  have h3105 : (e3105 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h3976 : (e3976 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4096 : (e4096 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h4156 : (e4156 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h4199 : (e4199 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h4260 : (e4260 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))
  have h4369 : (e4369 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4608 : (e4608 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4675 : (e4675 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))
  have h4872 : (e4872 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h4903 : (e4903 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))
  have h6700 : (e6700 _v) := (fun hn => hc (Or.inl hn))
  have h8038 : (e8038 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have p18590 := n18590 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  exact p18590
theorem n18603 (_v : Vars) (_q : Query _v)  : (e18602 _v) := by
  by_contra hc
  change ¬ ((e2475 _v) ∨ (¬ (e488 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e4899 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e8398 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e3976 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e3169 _v)) ∨ (¬ (e4675 _v)) ∨ (e2634 _v) ∨ (¬ (e70 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e442 _v))) at hc
  have h70 : (e70 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h225 : (e225 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))
  have h442 : (e442 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn)))))))))))))))))))))))))))
  have h488 : (e488 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h3069 : (e3069 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h3105 : (e3105 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h3169 : (e3169 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h3976 : (e3976 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))
  have h4096 : (e4096 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h4156 : (e4156 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))
  have h4199 : (e4199 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))
  have h4260 : (e4260 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))
  have h4369 : (e4369 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h4434 : (e4434 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))
  have h4608 : (e4608 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h4675 : (e4675 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4838 : (e4838 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h4872 : (e4872 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h4899 : (e4899 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h6700 : (e6700 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))
  have h8038 : (e8038 _v) := (fun hn => hc (Or.inl hn))
  have h8398 : (e8398 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have p18592 := n18592 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4434 h4608 h4675 h4787 h4813 h4838 h4872 h4899 h6700 h8038 h8398
  exact p18592
theorem n18604 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h8038 : (e8038 _v)) : (e2536 _v) := by
  have p16175 := n16175 _v _q 
  have p18599 := n18599 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h4096 h4156 h4199 h4260 h4369 h4434 h4608 h4675 h4787 h4813 h4838 h4872 h8038
  have p5255 := n5255 _v _q 
  have p5005 := n5005 _v _q h3169
  exact FloorCertificate.node_18604 (e2 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) (e2977 _v) (e3164 _v) p16175 p18599 p5255 p5005
theorem n18605 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h8038 : (e8038 _v)) : (e3573 _v) := by
  have p14426 := n14426 _v _q 
  have p18604 := n18604 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h4096 h4156 h4199 h4260 h4369 h4434 h4608 h4675 h4787 h4813 h4838 h4872 h8038
  change (¬ (e2536 _v)) ∨ (¬ (e3572 _v)) at p14426
  rcases p14426 with hlit | hlit
  · exact (False.elim (hlit p18604))
  · exact hlit
theorem n18606 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2364 : (e2364 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h8310 : (e8310 _v)) : (e2634 _v) := by
  have p18601 := n18601 _v _q 
  have p12880 := n12880 _v _q h8310
  have p17440 := n17440 _v _q h2364
  have p4991 := n4991 _v _q h4608
  have p4995 := n4995 _v _q h4369
  have p4996 := n4996 _v _q h3937
  have p4998 := n4998 _v _q h3152
  have p4999 := n4999 _v _q h91
  have p5001 := n5001 _v _q h4096
  have p5003 := n5003 _v _q h4199
  have p4985 := n4985 _v _q h4156
  have p5006 := n5006 _v _q h4675
  have p4984 := n4984 _v _q h4872
  have p5007 := n5007 _v _q h225
  have p5008 := n5008 _v _q h4787
  have p15567 := n15567 _v _q h2364
  have p5010 := n5010 _v _q h70
  have p4981 := n4981 _v _q h4260
  have p4988 := n4988 _v _q h488
  have p4986 := n4986 _v _q h3105
  have p4983 := n4983 _v _q h4813
  have p4994 := n4994 _v _q h3069
  have p4992 := n4992 _v _q h442
  change (e2634 _v) ∨ (¬ (e4156 _v)) ∨ (¬ (e3976 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e4199 _v)) ∨ (e2475 _v) ∨ (¬ (e4675 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4903 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e442 _v)) at p18601
  change (¬ (e2475 _v)) at p12880
  rcases p18601 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p4985))
  · exact (False.elim (hlit p17440))
  · exact (False.elim (hlit p4991))
  · exact (False.elim (hlit p4995))
  · exact (False.elim (hlit p4996))
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p5001))
  · exact (False.elim (hlit p5003))
  · exact (False.elim (p12880 hlit))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p4984))
  · exact (False.elim (hlit p5007))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p15567))
  · exact (False.elim (hlit p5010))
  · exact (False.elim (hlit p4981))
  · exact (False.elim (hlit p4988))
  · exact (False.elim (hlit p4986))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p4994))
  · exact (False.elim (hlit p4992))
theorem n18607 (_v : Vars) (_q : Query _v) (h4302 : (e4302 _v)) : (e3976 _v) := by
  have p14935 := n14935 _v _q 
  have p16536 := n16536 _v _q h4302
  change (e3983 _v) ∨ (e3976 _v) at p14935
  change (¬ (e3983 _v)) at p16536
  rcases p14935 with hlit | hlit
  · exact (False.elim (p16536 hlit))
  · exact hlit
theorem n18608 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4302 : (e4302 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e2634 _v) := by
  have p18601 := n18601 _v _q 
  have p16988 := n16988 _v _q h4302 h4434
  have p18607 := n18607 _v _q h4302
  have p4991 := n4991 _v _q h4608
  have p4995 := n4995 _v _q h4369
  have p4996 := n4996 _v _q h3937
  have p4998 := n4998 _v _q h3152
  have p4999 := n4999 _v _q h91
  have p5001 := n5001 _v _q h4096
  have p5003 := n5003 _v _q h4199
  have p4985 := n4985 _v _q h4156
  have p5006 := n5006 _v _q h4675
  have p4984 := n4984 _v _q h4872
  have p5007 := n5007 _v _q h225
  have p5008 := n5008 _v _q h4787
  have p16538 := n16538 _v _q h4302
  have p5010 := n5010 _v _q h70
  have p4981 := n4981 _v _q h4260
  have p4988 := n4988 _v _q h488
  have p4986 := n4986 _v _q h3105
  have p4983 := n4983 _v _q h4813
  have p4994 := n4994 _v _q h3069
  have p4992 := n4992 _v _q h442
  change (e2634 _v) ∨ (¬ (e4156 _v)) ∨ (¬ (e3976 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e4199 _v)) ∨ (e2475 _v) ∨ (¬ (e4675 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4903 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e442 _v)) at p18601
  change (¬ (e2475 _v)) at p16988
  rcases p18601 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p4985))
  · exact (False.elim (hlit p18607))
  · exact (False.elim (hlit p4991))
  · exact (False.elim (hlit p4995))
  · exact (False.elim (hlit p4996))
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p5001))
  · exact (False.elim (hlit p5003))
  · exact (False.elim (p16988 hlit))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p4984))
  · exact (False.elim (hlit p5007))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p16538))
  · exact (False.elim (hlit p5010))
  · exact (False.elim (hlit p4981))
  · exact (False.elim (hlit p4988))
  · exact (False.elim (hlit p4986))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p4994))
  · exact (False.elim (hlit p4992))
theorem n18609 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4302 : (e4302 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e3180 _v) := by
  have p14361 := n14361 _v _q 
  have p18608 := n18608 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h4096 h4156 h4199 h4260 h4302 h4369 h4434 h4608 h4675 h4787 h4813 h4872
  change (¬ (e2634 _v)) ∨ (¬ (e3179 _v)) at p14361
  rcases p14361 with hlit | hlit
  · exact (False.elim (hlit p18608))
  · exact hlit
theorem n18610 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4491 : (e4491 _v)) (h4546 : (e4546 _v)) (h4562 : (e4562 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h5093 : (e5093 _v)) : (e6700 _v) := by
  have p17417 := n17417 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h3976 h4059 h4096 h4139 h4156 h4199 h4260 h4285 h4301 h4369 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h5093
  have p5255 := n5255 _v _q 
  exact FloorCertificate.node_18610 (e2 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p17417 p5255
end
end Assembly
