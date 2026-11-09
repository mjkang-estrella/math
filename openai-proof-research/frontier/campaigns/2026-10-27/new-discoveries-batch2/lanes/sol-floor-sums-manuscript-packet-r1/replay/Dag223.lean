import Dag222
import generated.th_lemma_28
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n20030 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h5100 : (e5100 _v)) (h7493 : (e7493 _v)) : (e7489 _v) := by
  have p15207 := n15207 _v _q 
  have p20029 := n20029 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4156 h4199 h4260 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872 h5100 h7493
  have p20027 := n20027 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4156 h4199 h4260 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872 h5100 h7493
  change (e2475 _v) ∨ (¬ (e8049 _v)) at p15207
  change (¬ (e2475 _v)) at p20029
  rcases p15207 with hlit | hlit
  · exact (False.elim (p20029 hlit))
  · exact (False.elim (hlit p20027))
theorem n20032 (_v : Vars) (_q : Query _v)  : (e20031 _v) := by
  by_contra hc
  change ¬ ((¬ (e7493 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e5100 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e3152 _v))) at hc
  have h70 : (e70 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h225 : (e225 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))
  have h442 : (e442 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))
  have h488 : (e488 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h3069 : (e3069 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h3105 : (e3105 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn)))))))))))))))))))))))))
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))
  have h3946 : (e3946 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4059 : (e4059 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))
  have h4096 : (e4096 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h4156 : (e4156 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h4199 : (e4199 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))
  have h4260 : (e4260 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h4369 : (e4369 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))
  have h4434 : (e4434 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))
  have h4608 : (e4608 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h4675 : (e4675 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4747 : (e4747 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))
  have h4872 : (e4872 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h5100 : (e5100 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h7493 : (e7493 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have p20030 := n20030 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4156 h4199 h4260 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872 h5100 h7493
  exact p20030
theorem n20033 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e5103 _v) := by
  have p20032 := n20032 _v _q 
  have p19944 := n19944 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4156 h4199 h4260 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  have p5006 := n5006 _v _q h4675
  have p17056 := n17056 _v _q h3946
  have p17061 := n17061 _v _q h4747
  have p4985 := n4985 _v _q h4156
  have p4988 := n4988 _v _q h488
  have p4986 := n4986 _v _q h3105
  have p4984 := n4984 _v _q h4872
  have p4991 := n4991 _v _q h4608
  have p5008 := n5008 _v _q h4787
  have p4994 := n4994 _v _q h3069
  have p4981 := n4981 _v _q h4260
  have p5001 := n5001 _v _q h4096
  have p4999 := n4999 _v _q h91
  have p5010 := n5010 _v _q h70
  have p5003 := n5003 _v _q h4199
  have p5007 := n5007 _v _q h225
  have p4992 := n4992 _v _q h442
  have p4996 := n4996 _v _q h3937
  have p4987 := n4987 _v _q h4434
  have p17137 := n17137 _v _q h4059
  have p4983 := n4983 _v _q h4813
  have p4995 := n4995 _v _q h4369
  have p4998 := n4998 _v _q h3152
  change (¬ (e7493 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e5100 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e3152 _v)) at p20032
  rcases p20032 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact (False.elim (hlit p19944))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p17056))
  · exact (False.elim (hlit p17061))
  · exact (False.elim (hlit p4985))
  · exact (False.elim (hlit p4988))
  · exact (False.elim (hlit p4986))
  · exact (False.elim (hlit p4984))
  · exact (False.elim (hlit p4991))
  · exact hlit
  · exact (False.elim (hlit p4994))
  · exact (False.elim (hlit p4981))
  · exact (False.elim (hlit p5001))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p5010))
  · exact (False.elim (hlit p5003))
  · exact (False.elim (hlit p5007))
  · exact (False.elim (hlit p4992))
  · exact (False.elim (hlit p4996))
  · exact (False.elim (hlit p4987))
  · exact (False.elim (hlit p17137))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p4995))
  · exact (False.elim (hlit p4998))
theorem n20034 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e5104 _v) := by
  have p15319 := n15319 _v _q 
  have p20033 := n20033 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4156 h4199 h4260 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  change (e5104 _v) ∨ (e5100 _v) at p15319
  change (¬ (e5100 _v)) at p20033
  rcases p15319 with hlit | hlit
  · exact hlit
  · exact (False.elim (p20033 hlit))
theorem n20035 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e13 _v) := by
  have p15204 := n15204 _v _q 
  have p20034 := n20034 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4156 h4199 h4260 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  change (e13 _v) ∨ (¬ (e5104 _v)) at p15204
  rcases p15204 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p20034))
theorem n20036 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e2303 _v) := by
  have p11468 := n11468 _v _q 
  have p20035 := n20035 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4156 h4199 h4260 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  change (¬ (e13 _v)) ∨ (e2303 _v) at p11468
  rcases p11468 with hlit | hlit
  · exact (False.elim (hlit p20035))
  · exact hlit
theorem n20037 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e2475 _v) := by
  have p11399 := n11399 _v _q 
  have p20035 := n20035 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4156 h4199 h4260 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  change (¬ (e13 _v)) ∨ (e2475 _v) at p11399
  rcases p11399 with hlit | hlit
  · exact (False.elim (hlit p20035))
  · exact hlit
theorem n20038 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e7489 _v) := by
  have p8461 := n8461 _v _q 
  have p20036 := n20036 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4156 h4199 h4260 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  have p20037 := n20037 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4156 h4199 h4260 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  have p19935 := n19935 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4156 h4199 h4260 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  change (¬ (e2475 _v)) ∨ (¬ (e2303 _v)) ∨ (e2787 _v) at p8461
  change (¬ (e2787 _v)) at p19935
  rcases p8461 with hlit | hlit | hlit
  · exact (False.elim (hlit p20037))
  · exact (False.elim (hlit p20036))
  · exact (False.elim (p19935 hlit))
theorem n20040 (_v : Vars) (_q : Query _v)  : (e20039 _v) := by
  by_contra hc
  change ¬ ((¬ (e4059 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e3152 _v))) at hc
  have h70 : (e70 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h225 : (e225 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))
  have h442 : (e442 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))
  have h488 : (e488 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h3069 : (e3069 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h3105 : (e3105 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn)))))))))))))))))))))))
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))
  have h3946 : (e3946 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4059 : (e4059 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h4096 : (e4096 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h4156 : (e4156 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4199 : (e4199 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))
  have h4260 : (e4260 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h4369 : (e4369 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))
  have h4434 : (e4434 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))
  have h4608 : (e4608 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h4675 : (e4675 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h4747 : (e4747 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))
  have h4872 : (e4872 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have p20038 := n20038 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4156 h4199 h4260 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  exact p20038
theorem n20041 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e4064 _v) := by
  have p20040 := n20040 _v _q 
  have p4981 := n4981 _v _q h4260
  have p17056 := n17056 _v _q h3946
  have p17061 := n17061 _v _q h4747
  have p4985 := n4985 _v _q h4156
  have p4988 := n4988 _v _q h488
  have p4986 := n4986 _v _q h3105
  have p4984 := n4984 _v _q h4872
  have p4991 := n4991 _v _q h4608
  have p5008 := n5008 _v _q h4787
  have p4994 := n4994 _v _q h3069
  have p5006 := n5006 _v _q h4675
  have p5001 := n5001 _v _q h4096
  have p4999 := n4999 _v _q h91
  have p5010 := n5010 _v _q h70
  have p5003 := n5003 _v _q h4199
  have p5007 := n5007 _v _q h225
  have p4992 := n4992 _v _q h442
  have p4996 := n4996 _v _q h3937
  have p4987 := n4987 _v _q h4434
  have p4983 := n4983 _v _q h4813
  have p4995 := n4995 _v _q h4369
  have p4998 := n4998 _v _q h3152
  change (¬ (e4059 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e3152 _v)) at p20040
  rcases p20040 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p17056))
  · exact (False.elim (hlit p17061))
  · exact (False.elim (hlit p4985))
  · exact (False.elim (hlit p4988))
  · exact (False.elim (hlit p4986))
  · exact (False.elim (hlit p4984))
  · exact (False.elim (hlit p4991))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p4994))
  · exact (False.elim (hlit p4981))
  · exact (False.elim (hlit p5001))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p5010))
  · exact (False.elim (hlit p5003))
  · exact (False.elim (hlit p5007))
  · exact (False.elim (hlit p4992))
  · exact (False.elim (hlit p4996))
  · exact (False.elim (hlit p4987))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p4995))
  · exact (False.elim (hlit p4998))
theorem n20042 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e4066 _v) := by
  have p14980 := n14980 _v _q 
  have p20041 := n20041 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4260 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  change (e4066 _v) ∨ (e4059 _v) at p14980
  change (¬ (e4059 _v)) at p20041
  rcases p14980 with hlit | hlit
  · exact hlit
  · exact (False.elim (p20041 hlit))
theorem n20043 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h5108 : (e5108 _v)) (h6454 : (e6454 _v)) : (e4097 _v) := by
  have p20040 := n20040 _v _q 
  have p16579 := n16579 _v _q h5108 h6454
  have p17056 := n17056 _v _q h3946
  have p17061 := n17061 _v _q h4747
  have p4985 := n4985 _v _q h4156
  have p4988 := n4988 _v _q h488
  have p4986 := n4986 _v _q h3105
  have p4984 := n4984 _v _q h4872
  have p17137 := n17137 _v _q h4059
  have p5008 := n5008 _v _q h4787
  have p4994 := n4994 _v _q h3069
  have p5006 := n5006 _v _q h4675
  have p4991 := n4991 _v _q h4608
  have p4999 := n4999 _v _q h91
  have p15650 := n15650 _v _q h5108
  have p5003 := n5003 _v _q h4199
  have p5007 := n5007 _v _q h225
  have p4992 := n4992 _v _q h442
  have p4996 := n4996 _v _q h3937
  have p4987 := n4987 _v _q h4434
  have p4983 := n4983 _v _q h4813
  have p4995 := n4995 _v _q h4369
  have p4998 := n4998 _v _q h3152
  change (¬ (e4059 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e3152 _v)) at p20040
  rcases p20040 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact (False.elim (hlit p17137))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p17056))
  · exact (False.elim (hlit p17061))
  · exact (False.elim (hlit p4985))
  · exact (False.elim (hlit p4988))
  · exact (False.elim (hlit p4986))
  · exact (False.elim (hlit p4984))
  · exact (False.elim (hlit p4991))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p4994))
  · exact (False.elim (hlit p16579))
  · exact hlit
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p15650))
  · exact (False.elim (hlit p5003))
  · exact (False.elim (hlit p5007))
  · exact (False.elim (hlit p4992))
  · exact (False.elim (hlit p4996))
  · exact (False.elim (hlit p4987))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p4995))
  · exact (False.elim (hlit p4998))
theorem n20044 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h5108 : (e5108 _v)) (h6454 : (e6454 _v)) : (e7589 _v) := by
  have p15703 := n15703 _v _q 
  have p20043 := n20043 _v _q h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4156 h4199 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872 h5108 h6454
  change (e7589 _v) ∨ (e4096 _v) at p15703
  change (¬ (e4096 _v)) at p20043
  rcases p15703 with hlit | hlit
  · exact hlit
  · exact (False.elim (p20043 hlit))
theorem n20045 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e6684 _v) := by
  have p14703 := n14703 _v _q 
  have p20042 := n20042 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4260 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  change (¬ (e2598 _v)) ∨ (¬ (e4066 _v)) at p14703
  rcases p14703 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p20042))
theorem n20046 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e7489 _v) := by
  have p20045 := n20045 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4260 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  have p5255 := n5255 _v _q 
  have p19639 := n19639 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4260 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  have p10893 := n10893 _v _q 
  exact FloorCertificate.node_20046 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p20045 p5255 p19639 p10893
theorem n20048 (_v : Vars) (_q : Query _v)  : (e20047 _v) := by
  by_contra hc
  change ¬ ((¬ (e4260 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e3152 _v))) at hc
  have h70 : (e70 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h225 : (e225 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))
  have h442 : (e442 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))
  have h488 : (e488 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h3069 : (e3069 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h3105 : (e3105 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))))))))))))))))))
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))
  have h3946 : (e3946 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h4096 : (e4096 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h4156 : (e4156 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4199 : (e4199 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h4260 : (e4260 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h4369 : (e4369 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))
  have h4434 : (e4434 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))
  have h4608 : (e4608 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h4675 : (e4675 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h4747 : (e4747 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))
  have h4872 : (e4872 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have p20046 := n20046 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4260 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  exact p20046
theorem n20049 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h5108 : (e5108 _v)) (h6454 : (e6454 _v)) : (e2733 _v) := by
  have p14525 := n14525 _v _q 
  have p20044 := n20044 _v _q h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4156 h4199 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872 h5108 h6454
  change (e2733 _v) ∨ (¬ (e7589 _v)) at p14525
  rcases p14525 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p20044))
theorem n20050 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h5108 : (e5108 _v)) (h6454 : (e6454 _v)) : (e7489 _v) := by
  have p11366 := n11366 _v _q h5108
  have p5257 := n5257 _v _q 
  have p20049 := n20049 _v _q h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4156 h4199 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872 h5108 h6454
  exact FloorCertificate.node_20050 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p11366 p5257 p20049
theorem n20052 (_v : Vars) (_q : Query _v)  : (e20051 _v) := by
  by_contra hc
  change ¬ ((e48 _v) ∨ (¬ (e3946 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e3152 _v)) ∨ (e2061 _v)) at hc
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h225 : (e225 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h442 : (e442 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))
  have h488 : (e488 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h3069 : (e3069 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h3105 : (e3105 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))
  have h3946 : (e3946 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h4059 : (e4059 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h4156 : (e4156 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4199 : (e4199 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h4369 : (e4369 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))
  have h4434 : (e4434 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))
  have h4608 : (e4608 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h4675 : (e4675 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h4747 : (e4747 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))
  have h4872 : (e4872 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h5108 : (e5108 _v) := (fun hn => hc (Or.inl hn))
  have h6454 : (e6454 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))))))))))))))))))
  have p20050 := n20050 _v _q h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4156 h4199 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872 h5108 h6454
  exact p20050
theorem n20053 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3152 : (e3152 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h6501 : (e6501 _v)) : (e3942 _v) := by
  have p20048 := n20048 _v _q 
  have p15641 := n15641 _v _q h6501
  have p17294 := n17294 _v _q 
  have p17874 := n17874 _v _q 
  have p4981 := n4981 _v _q h4260
  have p17758 := n17758 _v _q 
  have p19665 := n19665 _v _q 
  have p5010 := n5010 _v _q h70
  have p5008 := n5008 _v _q h4787
  have p4994 := n4994 _v _q h3069
  have p4985 := n4985 _v _q h4156
  have p4988 := n4988 _v _q h488
  have p5006 := n5006 _v _q h4675
  have p5001 := n5001 _v _q h4096
  have p5003 := n5003 _v _q h4199
  have p4999 := n4999 _v _q h91
  have p4992 := n4992 _v _q h442
  have p5007 := n5007 _v _q h225
  have p4987 := n4987 _v _q h4434
  have p4983 := n4983 _v _q h4813
  have p4995 := n4995 _v _q h4369
  have p4998 := n4998 _v _q h3152
  change (¬ (e4260 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e3152 _v)) at p20048
  rcases p20048 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact (False.elim (hlit p4981))
  · exact (False.elim (hlit p17294))
  · exact (False.elim (hlit p17874))
  · exact (False.elim (hlit p4985))
  · exact (False.elim (hlit p4988))
  · exact (False.elim (hlit p17758))
  · exact (False.elim (hlit p19665))
  · exact (False.elim (hlit p15641))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p4994))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p5001))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p5010))
  · exact (False.elim (hlit p5003))
  · exact (False.elim (hlit p5007))
  · exact (False.elim (hlit p4992))
  · exact hlit
  · exact (False.elim (hlit p4987))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p4995))
  · exact (False.elim (hlit p4998))
theorem n20054 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3152 : (e3152 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h6501 : (e6501 _v)) : (e7489 _v) := by
  have p15012 := n15012 _v _q 
  have p20053 := n20053 _v _q h70 h91 h225 h442 h488 h3069 h3152 h4096 h4156 h4199 h4260 h4369 h4434 h4675 h4787 h4813 h6501
  have p15070 := n15070 _v _q h6501
  change (e7415 _v) ∨ (e3937 _v) at p15012
  change (¬ (e3937 _v)) at p20053
  change (¬ (e7415 _v)) at p15070
  rcases p15012 with hlit | hlit
  · exact (False.elim (p15070 hlit))
  · exact (False.elim (p20053 hlit))
theorem n20056 (_v : Vars) (_q : Query _v)  : (e20055 _v) := by
  by_contra hc
  change ¬ ((e2179 _v) ∨ (¬ (e4260 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e3152 _v))) at hc
  have h70 : (e70 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h225 : (e225 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h442 : (e442 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h488 : (e488 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h3069 : (e3069 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn)))))))))))))))))
  have h4096 : (e4096 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h4156 : (e4156 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h4199 : (e4199 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h4260 : (e4260 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h4369 : (e4369 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))
  have h4434 : (e4434 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h4675 : (e4675 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h6501 : (e6501 _v) := (fun hn => hc (Or.inl hn))
  have p20054 := n20054 _v _q h70 h91 h225 h442 h488 h3069 h3152 h4096 h4156 h4199 h4260 h4369 h4434 h4675 h4787 h4813 h6501
  exact p20054
theorem n20057 (_v : Vars) (_q : Query _v) (h6758 : (e6758 _v)) : (e5108 _v) := by
  have p8425 := n8425 _v _q h6758
  have p11375 := n11375 _v _q 
  have p19683 := n19683 _v _q h6758
  have p10893 := n10893 _v _q 
  exact FloorCertificate.node_20057 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8425 p11375 p19683 p10893
theorem n20058 (_v : Vars) (_q : Query _v) (h6758 : (e6758 _v)) : (e4676 _v) := by
  have p20052 := n20052 _v _q 
  have p20057 := n20057 _v _q h6758
  have p17874 := n17874 _v _q 
  have p19610 := n19610 _v _q 
  have p11507 := n11507 _v _q h6758
  have p17758 := n17758 _v _q 
  have p19665 := n19665 _v _q 
  have p16589 := n16589 _v _q h6758
  have p15673 := n15673 _v _q h6758
  have p15654 := n15654 _v _q h6758
  have p15652 := n15652 _v _q h6758
  have p16580 := n16580 _v _q h6758
  have p16585 := n16585 _v _q h6758
  have p16592 := n16592 _v _q h6758
  have p16851 := n16851 _v _q h6758
  have p16595 := n16595 _v _q h6758
  have p15667 := n15667 _v _q h6758
  have p15669 := n15669 _v _q h6758
  have p16581 := n16581 _v _q h6758
  have p16583 := n16583 _v _q h6758
  have p16582 := n16582 _v _q h6758
  have p17294 := n17294 _v _q 
  change (e48 _v) ∨ (¬ (e3946 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e3152 _v)) ∨ (e2061 _v) at p20052
  change (¬ (e48 _v)) at p20057
  change (¬ (e2061 _v)) at p11507
  rcases p20052 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact (False.elim (p20057 hlit))
  · exact (False.elim (hlit p17294))
  · exact (False.elim (hlit p17874))
  · exact (False.elim (hlit p16589))
  · exact (False.elim (hlit p15652))
  · exact (False.elim (hlit p17758))
  · exact (False.elim (hlit p19665))
  · exact (False.elim (hlit p19610))
  · exact (False.elim (hlit p15673))
  · exact (False.elim (hlit p15654))
  · exact hlit
  · exact (False.elim (hlit p16580))
  · exact (False.elim (hlit p16585))
  · exact (False.elim (hlit p16592))
  · exact (False.elim (hlit p16851))
  · exact (False.elim (hlit p16595))
  · exact (False.elim (hlit p15667))
  · exact (False.elim (hlit p15669))
  · exact (False.elim (hlit p16581))
  · exact (False.elim (hlit p16583))
  · exact (False.elim (hlit p16582))
  · exact (False.elim (p11507 hlit))
theorem n20059 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h6423 : (e6423 _v)) : (e48 _v) := by
  have p20052 := n20052 _v _q 
  have p12853 := n12853 _v _q h6423
  have p17061 := n17061 _v _q h4747
  have p4985 := n4985 _v _q h4156
  have p4988 := n4988 _v _q h488
  have p4986 := n4986 _v _q h3105
  have p4984 := n4984 _v _q h4872
  have p17137 := n17137 _v _q h4059
  have p5008 := n5008 _v _q h4787
  have p4994 := n4994 _v _q h3069
  have p5006 := n5006 _v _q h4675
  have p4991 := n4991 _v _q h4608
  have p4999 := n4999 _v _q h91
  have p5003 := n5003 _v _q h4199
  have p5007 := n5007 _v _q h225
  have p4992 := n4992 _v _q h442
  have p4996 := n4996 _v _q h3937
  have p4987 := n4987 _v _q h4434
  have p4983 := n4983 _v _q h4813
  have p4995 := n4995 _v _q h4369
  have p4998 := n4998 _v _q h3152
  have p17056 := n17056 _v _q h3946
  change (e48 _v) ∨ (¬ (e3946 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e3152 _v)) ∨ (e2061 _v) at p20052
  change (¬ (e2061 _v)) at p12853
  rcases p20052 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p17056))
  · exact (False.elim (hlit p17061))
  · exact (False.elim (hlit p4985))
  · exact (False.elim (hlit p4988))
  · exact (False.elim (hlit p4986))
  · exact (False.elim (hlit p4984))
  · exact (False.elim (hlit p17137))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p4994))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p4991))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p5003))
  · exact (False.elim (hlit p5007))
  · exact (False.elim (hlit p4992))
  · exact (False.elim (hlit p4996))
  · exact (False.elim (hlit p4987))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p4995))
  · exact (False.elim (hlit p4998))
  · exact (False.elim (p12853 hlit))
theorem n20060 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h6454 : (e6454 _v)) : (e48 _v) := by
  have p20052 := n20052 _v _q 
  have p8430 := n8430 _v _q h6454
  have p17061 := n17061 _v _q h4747
  have p4985 := n4985 _v _q h4156
  have p4988 := n4988 _v _q h488
  have p4986 := n4986 _v _q h3105
  have p4984 := n4984 _v _q h4872
  have p17137 := n17137 _v _q h4059
  have p5008 := n5008 _v _q h4787
  have p4994 := n4994 _v _q h3069
  have p5006 := n5006 _v _q h4675
  have p4991 := n4991 _v _q h4608
  have p4999 := n4999 _v _q h91
  have p5003 := n5003 _v _q h4199
  have p5007 := n5007 _v _q h225
  have p4992 := n4992 _v _q h442
  have p4996 := n4996 _v _q h3937
  have p4987 := n4987 _v _q h4434
  have p4983 := n4983 _v _q h4813
  have p4995 := n4995 _v _q h4369
  have p4998 := n4998 _v _q h3152
  have p17056 := n17056 _v _q h3946
  change (e48 _v) ∨ (¬ (e3946 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e3152 _v)) ∨ (e2061 _v) at p20052
  change (¬ (e2061 _v)) at p8430
  rcases p20052 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p17056))
  · exact (False.elim (hlit p17061))
  · exact (False.elim (hlit p4985))
  · exact (False.elim (hlit p4988))
  · exact (False.elim (hlit p4986))
  · exact (False.elim (hlit p4984))
  · exact (False.elim (hlit p17137))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p4994))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p4991))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p5003))
  · exact (False.elim (hlit p5007))
  · exact (False.elim (hlit p4992))
  · exact (False.elim (hlit p4996))
  · exact (False.elim (hlit p4987))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p4995))
  · exact (False.elim (hlit p4998))
  · exact (False.elim (p8430 hlit))
theorem n20061 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h6454 : (e6454 _v)) : (e60 _v) := by
  have p14152 := n14152 _v _q 
  have p20060 := n20060 _v _q h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4156 h4199 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872 h6454
  change (¬ (e48 _v)) ∨ (¬ (e59 _v)) at p14152
  rcases p14152 with hlit | hlit
  · exact (False.elim (hlit p20060))
  · exact hlit
theorem n20062 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e4261 _v) := by
  have p20048 := n20048 _v _q 
  have p5001 := n5001 _v _q h4096
  have p17061 := n17061 _v _q h4747
  have p4985 := n4985 _v _q h4156
  have p4988 := n4988 _v _q h488
  have p4986 := n4986 _v _q h3105
  have p4984 := n4984 _v _q h4872
  have p4991 := n4991 _v _q h4608
  have p5008 := n5008 _v _q h4787
  have p4994 := n4994 _v _q h3069
  have p5006 := n5006 _v _q h4675
  have p17056 := n17056 _v _q h3946
  have p4999 := n4999 _v _q h91
  have p5010 := n5010 _v _q h70
  have p5003 := n5003 _v _q h4199
  have p5007 := n5007 _v _q h225
  have p4992 := n4992 _v _q h442
  have p4996 := n4996 _v _q h3937
  have p4987 := n4987 _v _q h4434
  have p4983 := n4983 _v _q h4813
  have p4995 := n4995 _v _q h4369
  have p4998 := n4998 _v _q h3152
  change (¬ (e4260 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e3152 _v)) at p20048
  rcases p20048 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p17056))
  · exact (False.elim (hlit p17061))
  · exact (False.elim (hlit p4985))
  · exact (False.elim (hlit p4988))
  · exact (False.elim (hlit p4986))
  · exact (False.elim (hlit p4984))
  · exact (False.elim (hlit p4991))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p4994))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p5001))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p5010))
  · exact (False.elim (hlit p5003))
  · exact (False.elim (hlit p5007))
  · exact (False.elim (hlit p4992))
  · exact (False.elim (hlit p4996))
  · exact (False.elim (hlit p4987))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p4995))
  · exact (False.elim (hlit p4998))
theorem n20063 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e7781 _v) := by
  have p15824 := n15824 _v _q 
  have p20062 := n20062 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  change (e7781 _v) ∨ (e4260 _v) at p15824
  change (¬ (e4260 _v)) at p20062
  rcases p15824 with hlit | hlit
  · exact hlit
  · exact (False.elim (p20062 hlit))
theorem n20064 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3152 : (e3152 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h6423 : (e6423 _v)) : (e2179 _v) := by
  have p20056 := n20056 _v _q 
  have p16396 := n16396 _v _q h6423
  have p5010 := n5010 _v _q h70
  have p5008 := n5008 _v _q h4787
  have p4994 := n4994 _v _q h3069
  have p4985 := n4985 _v _q h4156
  have p4988 := n4988 _v _q h488
  have p5006 := n5006 _v _q h4675
  have p5001 := n5001 _v _q h4096
  have p5003 := n5003 _v _q h4199
  have p4999 := n4999 _v _q h91
  have p4992 := n4992 _v _q h442
  have p5007 := n5007 _v _q h225
  have p4981 := n4981 _v _q h4260
  have p4983 := n4983 _v _q h4813
  have p4995 := n4995 _v _q h4369
  have p4998 := n4998 _v _q h3152
  change (e2179 _v) ∨ (¬ (e4260 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e3152 _v)) at p20056
  rcases p20056 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p4981))
  · exact (False.elim (hlit p5010))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p4994))
  · exact (False.elim (hlit p4985))
  · exact (False.elim (hlit p4988))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p5001))
  · exact (False.elim (hlit p5003))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p4992))
  · exact (False.elim (hlit p5007))
  · exact (False.elim (hlit p16396))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p4995))
  · exact (False.elim (hlit p4998))
theorem n20065 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3152 : (e3152 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h6423 : (e6423 _v)) : (e4616 _v) := by
  have p14684 := n14684 _v _q 
  have p20064 := n20064 _v _q h70 h91 h225 h442 h488 h3069 h3152 h4096 h4156 h4199 h4260 h4369 h4675 h4787 h4813 h6423
  change (¬ (e2179 _v)) ∨ (¬ (e3162 _v)) at p14684
  rcases p14684 with hlit | hlit
  · exact (False.elim (hlit p20064))
  · exact hlit
theorem n20066 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3152 : (e3152 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h6423 : (e6423 _v)) : (e3158 _v) := by
  have p15126 := n15126 _v _q 
  have p20065 := n20065 _v _q h70 h91 h225 h442 h488 h3069 h3152 h4096 h4156 h4199 h4260 h4369 h4675 h4787 h4813 h6423
  change (e3162 _v) ∨ (e3158 _v) at p15126
  change (¬ (e3162 _v)) at p20065
  rcases p15126 with hlit | hlit
  · exact (False.elim (p20065 hlit))
  · exact hlit
theorem n20067 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3152 : (e3152 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h6423 : (e6423 _v)) : (e7489 _v) := by
  have p16858 := n16858 _v _q 
  have p5257 := n5257 _v _q 
  have p5255 := n5255 _v _q 
  have p8452 := n8452 _v _q h6423
  have p20066 := n20066 _v _q h70 h91 h225 h442 h488 h3069 h3152 h4096 h4156 h4199 h4260 h4369 h4675 h4787 h4813 h6423
  have p16578 := n16578 _v _q 
  exact FloorCertificate.node_20067 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e110 _v) (e2863 _v) (e2935 _v) p16858 p5257 p5255 p8452 p20066 p16578
theorem n20068 (_v : Vars) (_q : Query _v) (h6758 : (e6758 _v)) : (e7489 _v) := by
  have p15965 := n15965 _v _q 
  have p20058 := n20058 _v _q h6758
  have p19713 := n19713 _v _q h6758
  change (e8166 _v) ∨ (e4675 _v) at p15965
  change (¬ (e4675 _v)) at p20058
  change (¬ (e8166 _v)) at p19713
  rcases p15965 with hlit | hlit
  · exact (False.elim (p19713 hlit))
  · exact (False.elim (p20058 hlit))
theorem n20069 (_v : Vars) (_q : Query _v)  : (e2746 _v) := by
  by_contra hc
  change ¬ (e2746 _v) at hc
  have h6758 : (e6758 _v) := (fun hn => hc hn)
  have p20068 := n20068 _v _q h6758
  exact p20068
theorem n20070 (_v : Vars) (_q : Query _v)  : (e3984 _v) := by
  have p14691 := n14691 _v _q 
  have p20069 := n20069 _v _q 
  change (¬ (e2746 _v)) ∨ (¬ (e3983 _v)) at p14691
  rcases p14691 with hlit | hlit
  · exact (False.elim (hlit p20069))
  · exact hlit
theorem n20071 (_v : Vars) (_q : Query _v)  : (e2697 _v) := by
  have p11373 := n11373 _v _q 
  have p20069 := n20069 _v _q 
  change (e2697 _v) ∨ (¬ (e2746 _v)) at p11373
  rcases p11373 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p20069))
theorem n20072 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h6423 : (e6423 _v)) : (e5147 _v) := by
  have p4999 := n4999 _v _q h91
  have p20059 := n20059 _v _q h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4156 h4199 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872 h6423
  have p8452 := n8452 _v _q h6423
  exact FloorCertificate.node_20072 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e80 _v) p4999 p20059 p8452
theorem n20073 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h6423 : (e6423 _v)) : (e5149 _v) := by
  have p16670 := n16670 _v _q 
  have p20072 := n20072 _v _q h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4156 h4199 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872 h6423
  change (e5149 _v) ∨ (e5143 _v) at p16670
  change (¬ (e5143 _v)) at p20072
  rcases p16670 with hlit | hlit
  · exact hlit
  · exact (False.elim (p20072 hlit))
theorem n20074 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h6454 : (e6454 _v)) : (e51 _v) := by
  have p14962 := n14962 _v _q 
  have p20061 := n20061 _v _q h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4156 h4199 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872 h6454
  change (e59 _v) ∨ (e51 _v) at p14962
  change (¬ (e59 _v)) at p20061
  rcases p14962 with hlit | hlit
  · exact (False.elim (p20061 hlit))
  · exact hlit
theorem n20075 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4306 : (e4306 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4434 : (e4434 _v)) (h4491 : (e4491 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5100 : (e5100 _v)) (h5208 : (e5208 _v)) (h6454 : (e6454 _v)) (h6571 : (e6571 _v)) (h7749 : (e7749 _v)) (h7814 : (e7814 _v)) (h8045 : (e8045 _v)) : (e4839 _v) := by
  have p17370 := n17370 _v _q 
  have p16947 := n16947 _v _q h91 h6454
  have p8447 := n8447 _v _q h6571
  have p20074 := n20074 _v _q h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4156 h4199 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872 h6454
  have p4994 := n4994 _v _q h3069
  have p4987 := n4987 _v _q h4434
  have p16269 := n16269 _v _q h7749
  have p4991 := n4991 _v _q h4608
  have p4999 := n4999 _v _q h91
  have p4996 := n4996 _v _q h3937
  have p16950 := n16950 _v _q h91 h6454
  have p5003 := n5003 _v _q h4199
  have p4998 := n4998 _v _q h3152
  have p17128 := n17128 _v _q h4491
  have p4983 := n4983 _v _q h4813
  have p5008 := n5008 _v _q h4787
  have p17129 := n17129 _v _q h4903
  have p17175 := n17175 _v _q h5208
  have p5006 := n5006 _v _q h4675
  have p17159 := n17159 _v _q h5100
  have p17172 := n17172 _v _q h7814
  have p17134 := n17134 _v _q h4398
  have p17157 := n17157 _v _q h8045
  have p17137 := n17137 _v _q h4059
  have p17138 := n17138 _v _q h4306
  have p5007 := n5007 _v _q h225
  have p4992 := n4992 _v _q h442
  have p17143 := n17143 _v _q h4567
  have p17056 := n17056 _v _q h3946
  have p17060 := n17060 _v _q h4653
  have p17061 := n17061 _v _q h4747
  have p4995 := n4995 _v _q h4369
  have p17076 := n17076 _v _q h3976
  have p4985 := n4985 _v _q h4156
  have p4988 := n4988 _v _q h488
  have p4986 := n4986 _v _q h3105
  have p4984 := n4984 _v _q h4872
  have p17094 := n17094 _v _q h4724
  change (¬ (e4838 _v)) ∨ (e2358 _v) ∨ (¬ (e4096 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e7749 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4491 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4903 _v)) ∨ (¬ (e5208 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e5100 _v)) ∨ (¬ (e7814 _v)) ∨ (¬ (e4398 _v)) ∨ (¬ (e8045 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e4567 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e3976 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4724 _v)) at p17370
  change (¬ (e2358 _v)) at p8447
  rcases p17370 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (p8447 hlit))
  · exact (False.elim (hlit p16947))
  · exact (False.elim (hlit p20074))
  · exact (False.elim (hlit p4994))
  · exact (False.elim (hlit p4987))
  · exact (False.elim (hlit p16269))
  · exact (False.elim (hlit p4991))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p4996))
  · exact (False.elim (hlit p16950))
  · exact (False.elim (hlit p5003))
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p17128))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p17129))
  · exact (False.elim (hlit p17175))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p17159))
  · exact (False.elim (hlit p17172))
  · exact (False.elim (hlit p17134))
  · exact (False.elim (hlit p17157))
  · exact (False.elim (hlit p17137))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p5007))
  · exact (False.elim (hlit p4992))
  · exact (False.elim (hlit p17143))
  · exact (False.elim (hlit p17056))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p17061))
  · exact (False.elim (hlit p4995))
  · exact (False.elim (hlit p17076))
  · exact (False.elim (hlit p4985))
  · exact (False.elim (hlit p4988))
  · exact (False.elim (hlit p4986))
  · exact (False.elim (hlit p4984))
  · exact (False.elim (hlit p17094))
theorem n20076 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4306 : (e4306 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4434 : (e4434 _v)) (h4491 : (e4491 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5100 : (e5100 _v)) (h5208 : (e5208 _v)) (h6454 : (e6454 _v)) (h6571 : (e6571 _v)) (h7749 : (e7749 _v)) (h7814 : (e7814 _v)) (h8045 : (e8045 _v)) : (e8301 _v) := by
  have p16285 := n16285 _v _q 
  have p20075 := n20075 _v _q h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h3976 h4059 h4156 h4199 h4306 h4369 h4398 h4434 h4491 h4567 h4608 h4653 h4675 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h5208 h6454 h6571 h7749 h7814 h8045
  change (e8301 _v) ∨ (e4838 _v) at p16285
  change (¬ (e4838 _v)) at p20075
  rcases p16285 with hlit | hlit
  · exact hlit
  · exact (False.elim (p20075 hlit))
theorem n20077 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e2781 _v) := by
  have p14570 := n14570 _v _q 
  have p20063 := n20063 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  change (e2781 _v) ∨ (¬ (e7781 _v)) at p14570
  rcases p14570 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p20063))
theorem n20078 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e2598 _v) := by
  have p20077 := n20077 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  have p10893 := n10893 _v _q 
  have p11376 := n11376 _v _q 
  have p8663 := n8663 _v _q 
  have p5255 := n5255 _v _q 
  have p11375 := n11375 _v _q 
  exact FloorCertificate.node_20078 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p20077 p10893 p11376 p8663 p5255 p11375
theorem n20079 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e4067 _v) := by
  have p14703 := n14703 _v _q 
  have p20078 := n20078 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  change (¬ (e2598 _v)) ∨ (¬ (e4066 _v)) at p14703
  rcases p14703 with hlit | hlit
  · exact (False.elim (hlit p20078))
  · exact hlit
end
end Assembly
