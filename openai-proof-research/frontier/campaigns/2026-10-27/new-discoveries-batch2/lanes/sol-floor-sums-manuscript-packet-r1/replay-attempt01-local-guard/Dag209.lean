import Dag208
import generated.th_lemma_25
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n19350 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h1995 : (e1995 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4220 : (e4220 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) (h4924 : (e4924 _v)) : (e7683 _v) := by
  have p14831 := n14831 _v _q 
  have p19348 := n19348 _v _q h30 h70 h91 h191 h225 h442 h488 h1995 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4220 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h4899 h4924
  change (¬ (e2371 _v)) ∨ (¬ (e7677 _v)) at p14831
  rcases p14831 with hlit | hlit
  · exact (False.elim (hlit p19348))
  · exact hlit
theorem n19351 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h1995 : (e1995 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4220 : (e4220 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) (h4924 : (e4924 _v)) : (e7489 _v) := by
  have p16453 := n16453 _v _q 
  have p19350 := n19350 _v _q h30 h70 h91 h191 h225 h442 h488 h1995 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4220 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h4899 h4924
  have p19349 := n19349 _v _q h30 h70 h91 h191 h225 h442 h488 h1995 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4220 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h4899 h4924
  change (e7677 _v) ∨ (e4181 _v) at p16453
  change (¬ (e7677 _v)) at p19350
  change (¬ (e4181 _v)) at p19349
  rcases p16453 with hlit | hlit
  · exact (False.elim (p19350 hlit))
  · exact (False.elim (p19349 hlit))
theorem n19353 (_v : Vars) (_q : Query _v)  : (e19352 _v) := by
  by_contra hc
  change ¬ ((¬ (e4924 _v)) ∨ (¬ (e4648 _v)) ∨ (¬ (e30 _v)) ∨ (¬ (e4899 _v)) ∨ (¬ (e4220 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e1995 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4419 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4477 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4301 _v))) at hc
  have h30 : (e30 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h70 : (e70 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))
  have h191 : (e191 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))
  have h225 : (e225 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))))))
  have h442 : (e442 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))
  have h488 : (e488 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h1995 : (e1995 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h3069 : (e3069 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))
  have h3105 : (e3105 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))
  have h3946 : (e3946 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))))
  have h4059 : (e4059 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))))
  have h4096 : (e4096 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))
  have h4139 : (e4139 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h4156 : (e4156 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h4199 : (e4199 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))
  have h4220 : (e4220 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4260 : (e4260 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h4301 : (e4301 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn)))))))))))))))))))))))))))))))))))
  have h4369 : (e4369 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))
  have h4419 : (e4419 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h4434 : (e4434 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h4477 : (e4477 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))
  have h4608 : (e4608 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))
  have h4648 : (e4648 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h4675 : (e4675 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))
  have h4747 : (e4747 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))
  have h4838 : (e4838 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h4872 : (e4872 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))
  have h4899 : (e4899 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4924 : (e4924 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have p19351 := n19351 _v _q h30 h70 h91 h191 h225 h442 h488 h1995 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4220 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h4899 h4924
  exact p19351
theorem n19354 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h1995 : (e1995 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4220 : (e4220 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) : (e4925 _v) := by
  have p19353 := n19353 _v _q 
  have p5000 := n5000 _v _q h30
  have p4990 := n4990 _v _q h4648
  have p4972 := n4972 _v _q h4899
  have p5004 := n5004 _v _q h4220
  have p4985 := n4985 _v _q h4156
  have p15572 := n15572 _v _q h1995
  have p4987 := n4987 _v _q h4434
  have p5010 := n5010 _v _q h70
  have p4981 := n4981 _v _q h4260
  have p4988 := n4988 _v _q h488
  have p4989 := n4989 _v _q h4838
  have p4971 := n4971 _v _q h4419
  have p4979 := n4979 _v _q h4139
  have p4986 := n4986 _v _q h3105
  have p4978 := n4978 _v _q h4477
  have p4992 := n4992 _v _q h442
  have p4984 := n4984 _v _q h4872
  have p4991 := n4991 _v _q h4608
  have p253 := n253 _v _q h191
  have p4994 := n4994 _v _q h3069
  have p5001 := n5001 _v _q h4096
  have p4996 := n4996 _v _q h3937
  have p4999 := n4999 _v _q h91
  have p4998 := n4998 _v _q h3152
  have p4983 := n4983 _v _q h4813
  have p5003 := n5003 _v _q h4199
  have p4995 := n4995 _v _q h4369
  have p5008 := n5008 _v _q h4787
  have p17061 := n17061 _v _q h4747
  have p5006 := n5006 _v _q h4675
  have p17137 := n17137 _v _q h4059
  have p17056 := n17056 _v _q h3946
  have p5007 := n5007 _v _q h225
  have p4980 := n4980 _v _q h4301
  change (¬ (e4924 _v)) ∨ (¬ (e4648 _v)) ∨ (¬ (e30 _v)) ∨ (¬ (e4899 _v)) ∨ (¬ (e4220 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e1995 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4419 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4477 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4301 _v)) at p19353
  rcases p19353 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p4990))
  · exact (False.elim (hlit p5000))
  · exact (False.elim (hlit p4972))
  · exact (False.elim (hlit p5004))
  · exact (False.elim (hlit p4985))
  · exact (False.elim (hlit p15572))
  · exact (False.elim (hlit p4987))
  · exact (False.elim (hlit p5010))
  · exact (False.elim (hlit p4981))
  · exact (False.elim (hlit p4988))
  · exact (False.elim (hlit p4989))
  · exact (False.elim (hlit p4971))
  · exact (False.elim (hlit p4979))
  · exact (False.elim (hlit p4986))
  · exact (False.elim (hlit p4978))
  · exact (False.elim (hlit p4992))
  · exact (False.elim (hlit p4984))
  · exact (False.elim (hlit p4991))
  · exact (False.elim (hlit p253))
  · exact (False.elim (hlit p4994))
  · exact (False.elim (hlit p5001))
  · exact (False.elim (hlit p4996))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p5003))
  · exact (False.elim (hlit p4995))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p17061))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p17137))
  · exact (False.elim (hlit p17056))
  · exact (False.elim (hlit p5007))
  · exact (False.elim (hlit p4980))
theorem n19355 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h1995 : (e1995 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4220 : (e4220 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) : (e8384 _v) := by
  have p16462 := n16462 _v _q 
  have p19354 := n19354 _v _q h30 h70 h91 h191 h225 h442 h488 h1995 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4220 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h4899
  change (e8384 _v) ∨ (e4924 _v) at p16462
  change (¬ (e4924 _v)) at p19354
  rcases p16462 with hlit | hlit
  · exact hlit
  · exact (False.elim (p19354 hlit))
theorem n19356 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h1995 : (e1995 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4220 : (e4220 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) : (e6780 _v) := by
  have p14912 := n14912 _v _q 
  have p19355 := n19355 _v _q h30 h70 h91 h191 h225 h442 h488 h1995 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4220 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h4899
  change (¬ (e2799 _v)) ∨ (¬ (e8384 _v)) at p14912
  rcases p14912 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p19355))
theorem n19357 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h1995 : (e1995 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4220 : (e4220 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) : (e8408 _v) := by
  have p15435 := n15435 _v _q 
  have p19356 := n19356 _v _q h30 h70 h91 h191 h225 h442 h488 h1995 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4220 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h4899
  change (e2799 _v) ∨ (¬ (e8407 _v)) at p15435
  change (¬ (e2799 _v)) at p19356
  rcases p15435 with hlit | hlit
  · exact (False.elim (p19356 hlit))
  · exact hlit
theorem n19358 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h1995 : (e1995 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4220 : (e4220 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) : (e8398 _v) := by
  have p11470 := n11470 _v _q 
  have p19357 := n19357 _v _q h30 h70 h91 h191 h225 h442 h488 h1995 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4220 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h4899
  change (e8407 _v) ∨ (e8398 _v) at p11470
  change (¬ (e8407 _v)) at p19357
  rcases p11470 with hlit | hlit
  · exact (False.elim (p19357 hlit))
  · exact hlit
theorem n19359 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h1995 : (e1995 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4220 : (e4220 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) : (e7489 _v) := by
  have p4990 := n4990 _v _q h4648
  have p19358 := n19358 _v _q h30 h70 h91 h191 h225 h442 h488 h1995 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4220 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h4899
  have p11375 := n11375 _v _q 
  have p19279 := n19279 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p5000 := n5000 _v _q h30
  have p19344 := n19344 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p4972 := n4972 _v _q h4899
  have p5004 := n5004 _v _q h4220
  have p17074 := n17074 _v _q 
  have p4985 := n4985 _v _q h4156
  have p13951 := n13951 _v _q 
  have p15572 := n15572 _v _q h1995
  have p15574 := n15574 _v _q h1995
  have p16913 := n16913 _v _q 
  have p10893 := n10893 _v _q 
  have p4987 := n4987 _v _q h4434
  have p5010 := n5010 _v _q h70
  have p4981 := n4981 _v _q h4260
  have p19289 := n19289 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p4988 := n4988 _v _q h488
  have p19317 := n19317 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p17080 := n17080 _v _q 
  have p17078 := n17078 _v _q 
  have p4989 := n4989 _v _q h4838
  have p4971 := n4971 _v _q h4419
  have p17091 := n17091 _v _q 
  have p4979 := n4979 _v _q h4139
  have p4986 := n4986 _v _q h3105
  have p4978 := n4978 _v _q h4477
  have p4992 := n4992 _v _q h442
  have p17221 := n17221 _v _q 
  have p19275 := n19275 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p4984 := n4984 _v _q h4872
  have p17083 := n17083 _v _q 
  have p4991 := n4991 _v _q h4608
  have p17087 := n17087 _v _q 
  have p16778 := n16778 _v _q 
  have p17115 := n17115 _v _q 
  have p17111 := n17111 _v _q 
  have p253 := n253 _v _q h191
  have p19347 := n19347 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p17098 := n17098 _v _q 
  have p17104 := n17104 _v _q 
  have p17110 := n17110 _v _q 
  have p17096 := n17096 _v _q 
  have p17106 := n17106 _v _q 
  have p17089 := n17089 _v _q 
  have p17102 := n17102 _v _q 
  have p17108 := n17108 _v _q 
  have p4994 := n4994 _v _q h3069
  have p17117 := n17117 _v _q 
  have p17120 := n17120 _v _q 
  have p17113 := n17113 _v _q 
  have p17124 := n17124 _v _q 
  have p17122 := n17122 _v _q 
  have p16911 := n16911 _v _q 
  have p17093 := n17093 _v _q 
  have p17141 := n17141 _v _q 
  have p17131 := n17131 _v _q 
  have p17069 := n17069 _v _q 
  have p5001 := n5001 _v _q h4096
  have p4996 := n4996 _v _q h3937
  have p17100 := n17100 _v _q 
  have p4999 := n4999 _v _q h91
  have p17133 := n17133 _v _q 
  have p17136 := n17136 _v _q 
  have p4998 := n4998 _v _q h3152
  have p4983 := n4983 _v _q h4813
  have p17053 := n17053 _v _q 
  have p5003 := n5003 _v _q h4199
  have p17127 := n17127 _v _q 
  have p4995 := n4995 _v _q h4369
  have p5008 := n5008 _v _q h4787
  have p16576 := n16576 _v _q 
  have p19278 := n19278 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p17061 := n17061 _v _q h4747
  have p17055 := n17055 _v _q 
  have p17147 := n17147 _v _q 
  have p17058 := n17058 _v _q 
  have p5006 := n5006 _v _q h4675
  have p17137 := n17137 _v _q h4059
  have p17056 := n17056 _v _q h3946
  have p5007 := n5007 _v _q h225
  have p17064 := n17064 _v _q 
  have p16929 := n16929 _v _q 
  have p4980 := n4980 _v _q h4301
  have p17067 := n17067 _v _q 
  have p17072 := n17072 _v _q 
  have p19287 := n19287 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p16994 := n16994 _v _q 
  exact FloorCertificate.node_19359 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e61 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2849 _v) (e2863 _v) (e2877 _v) (e2879 _v) (e2883 _v) (e2898 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2913 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p4990 p19358 p11375 p19279 p5000 p19344 p4972 p5004 p17074 p4985 p13951 p15572 p15574 p16913 p10893 p4987 p5010 p4981 p19289 p4988 p19317 p17080 p17078 p4989 p4971 p17091 p4979 p4986 p4978 p4992 p17221 p19275 p4984 p17083 p4991 p17087 p16778 p17115 p17111 p253 p19347 p17098 p17104 p17110 p17096 p17106 p17089 p17102 p17108 p4994 p17117 p17120 p17113 p17124 p17122 p16911 p17093 p17141 p17131 p17069 p5001 p4996 p17100 p4999 p17133 p17136 p4998 p4983 p17053 p5003 p17127 p4995 p5008 p16576 p19278 p17061 p17055 p17147 p17058 p5006 p17137 p17056 p5007 p17064 p16929 p4980 p17067 p17072 p19287 p16994
theorem n19361 (_v : Vars) (_q : Query _v)  : (e19360 _v) := by
  by_contra hc
  change ¬ ((¬ (e30 _v)) ∨ (¬ (e4648 _v)) ∨ (¬ (e4899 _v)) ∨ (¬ (e4220 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e1995 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4419 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4477 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4301 _v))) at hc
  have h30 : (e30 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h70 : (e70 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))
  have h191 : (e191 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))
  have h225 : (e225 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))))
  have h442 : (e442 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))
  have h488 : (e488 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h1995 : (e1995 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h3069 : (e3069 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))
  have h3105 : (e3105 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))
  have h3946 : (e3946 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))))
  have h4059 : (e4059 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))
  have h4096 : (e4096 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))
  have h4139 : (e4139 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h4156 : (e4156 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4199 : (e4199 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))
  have h4220 : (e4220 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4260 : (e4260 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h4301 : (e4301 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))))))))))))))))))))))))))))))
  have h4369 : (e4369 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))
  have h4419 : (e4419 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h4434 : (e4434 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h4477 : (e4477 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h4608 : (e4608 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))
  have h4648 : (e4648 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h4675 : (e4675 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))
  have h4747 : (e4747 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))
  have h4838 : (e4838 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h4872 : (e4872 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))
  have h4899 : (e4899 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have p19359 := n19359 _v _q h30 h70 h91 h191 h225 h442 h488 h1995 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4220 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h4899
  exact p19359
theorem n19362 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4220 : (e4220 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h6784 : (e6784 _v)) : (e6423 _v) := by
  have p19361 := n19361 _v _q 
  have p16513 := n16513 _v _q h6784
  have p5000 := n5000 _v _q h30
  have p5004 := n5004 _v _q h4220
  have p4985 := n4985 _v _q h4156
  have p15560 := n15560 _v _q h6784
  have p4987 := n4987 _v _q h4434
  have p5010 := n5010 _v _q h70
  have p4981 := n4981 _v _q h4260
  have p4988 := n4988 _v _q h488
  have p4989 := n4989 _v _q h4838
  have p4971 := n4971 _v _q h4419
  have p4979 := n4979 _v _q h4139
  have p4986 := n4986 _v _q h3105
  have p4978 := n4978 _v _q h4477
  have p4992 := n4992 _v _q h442
  have p4984 := n4984 _v _q h4872
  have p4991 := n4991 _v _q h4608
  have p253 := n253 _v _q h191
  have p4994 := n4994 _v _q h3069
  have p5001 := n5001 _v _q h4096
  have p4996 := n4996 _v _q h3937
  have p4999 := n4999 _v _q h91
  have p4998 := n4998 _v _q h3152
  have p4983 := n4983 _v _q h4813
  have p5003 := n5003 _v _q h4199
  have p4995 := n4995 _v _q h4369
  have p5008 := n5008 _v _q h4787
  have p17061 := n17061 _v _q h4747
  have p5006 := n5006 _v _q h4675
  have p17137 := n17137 _v _q h4059
  have p17056 := n17056 _v _q h3946
  have p5007 := n5007 _v _q h225
  have p4980 := n4980 _v _q h4301
  change (¬ (e30 _v)) ∨ (¬ (e4648 _v)) ∨ (¬ (e4899 _v)) ∨ (¬ (e4220 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e1995 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4419 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4477 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4301 _v)) at p19361
  rcases p19361 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact (False.elim (hlit p5000))
  · exact (False.elim (hlit p16513))
  · exact (False.elim (hlit p15560))
  · exact (False.elim (hlit p5004))
  · exact (False.elim (hlit p4985))
  · exact hlit
  · exact (False.elim (hlit p4987))
  · exact (False.elim (hlit p5010))
  · exact (False.elim (hlit p4981))
  · exact (False.elim (hlit p4988))
  · exact (False.elim (hlit p4989))
  · exact (False.elim (hlit p4971))
  · exact (False.elim (hlit p4979))
  · exact (False.elim (hlit p4986))
  · exact (False.elim (hlit p4978))
  · exact (False.elim (hlit p4992))
  · exact (False.elim (hlit p4984))
  · exact (False.elim (hlit p4991))
  · exact (False.elim (hlit p253))
  · exact (False.elim (hlit p4994))
  · exact (False.elim (hlit p5001))
  · exact (False.elim (hlit p4996))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p5003))
  · exact (False.elim (hlit p4995))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p17061))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p17137))
  · exact (False.elim (hlit p17056))
  · exact (False.elim (hlit p5007))
  · exact (False.elim (hlit p4980))
theorem n19363 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4220 : (e4220 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h6784 : (e6784 _v)) : (e8060 _v) := by
  have p14622 := n14622 _v _q 
  have p19362 := n19362 _v _q h30 h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4220 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872 h6784
  change (e1995 _v) ∨ (¬ (e8052 _v)) at p14622
  change (¬ (e1995 _v)) at p19362
  rcases p14622 with hlit | hlit
  · exact (False.elim (p19362 hlit))
  · exact hlit
theorem n19364 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4220 : (e4220 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) : (e6423 _v) := by
  have p19361 := n19361 _v _q 
  have p4990 := n4990 _v _q h4648
  have p5000 := n5000 _v _q h30
  have p5004 := n5004 _v _q h4220
  have p4985 := n4985 _v _q h4156
  have p4972 := n4972 _v _q h4899
  have p4987 := n4987 _v _q h4434
  have p5010 := n5010 _v _q h70
  have p4981 := n4981 _v _q h4260
  have p4988 := n4988 _v _q h488
  have p4989 := n4989 _v _q h4838
  have p4971 := n4971 _v _q h4419
  have p4979 := n4979 _v _q h4139
  have p4986 := n4986 _v _q h3105
  have p4978 := n4978 _v _q h4477
  have p4992 := n4992 _v _q h442
  have p4984 := n4984 _v _q h4872
  have p4991 := n4991 _v _q h4608
  have p253 := n253 _v _q h191
  have p4994 := n4994 _v _q h3069
  have p5001 := n5001 _v _q h4096
  have p4996 := n4996 _v _q h3937
  have p4999 := n4999 _v _q h91
  have p4998 := n4998 _v _q h3152
  have p4983 := n4983 _v _q h4813
  have p5003 := n5003 _v _q h4199
  have p4995 := n4995 _v _q h4369
  have p5008 := n5008 _v _q h4787
  have p17061 := n17061 _v _q h4747
  have p5006 := n5006 _v _q h4675
  have p17137 := n17137 _v _q h4059
  have p17056 := n17056 _v _q h3946
  have p5007 := n5007 _v _q h225
  have p4980 := n4980 _v _q h4301
  change (¬ (e30 _v)) ∨ (¬ (e4648 _v)) ∨ (¬ (e4899 _v)) ∨ (¬ (e4220 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e1995 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4419 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4477 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4301 _v)) at p19361
  rcases p19361 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact (False.elim (hlit p5000))
  · exact (False.elim (hlit p4990))
  · exact (False.elim (hlit p4972))
  · exact (False.elim (hlit p5004))
  · exact (False.elim (hlit p4985))
  · exact hlit
  · exact (False.elim (hlit p4987))
  · exact (False.elim (hlit p5010))
  · exact (False.elim (hlit p4981))
  · exact (False.elim (hlit p4988))
  · exact (False.elim (hlit p4989))
  · exact (False.elim (hlit p4971))
  · exact (False.elim (hlit p4979))
  · exact (False.elim (hlit p4986))
  · exact (False.elim (hlit p4978))
  · exact (False.elim (hlit p4992))
  · exact (False.elim (hlit p4984))
  · exact (False.elim (hlit p4991))
  · exact (False.elim (hlit p253))
  · exact (False.elim (hlit p4994))
  · exact (False.elim (hlit p5001))
  · exact (False.elim (hlit p4996))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p5003))
  · exact (False.elim (hlit p4995))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p17061))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p17137))
  · exact (False.elim (hlit p17056))
  · exact (False.elim (hlit p5007))
  · exact (False.elim (hlit p4980))
theorem n19365 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4220 : (e4220 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) : (e8060 _v) := by
  have p14622 := n14622 _v _q 
  have p19364 := n19364 _v _q h30 h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4220 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h4899
  change (e1995 _v) ∨ (¬ (e8052 _v)) at p14622
  change (¬ (e1995 _v)) at p19364
  rcases p14622 with hlit | hlit
  · exact (False.elim (p19364 hlit))
  · exact hlit
theorem n19366 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4220 : (e4220 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h6784 : (e6784 _v)) : (e4562 _v) := by
  have p15155 := n15155 _v _q 
  have p19363 := n19363 _v _q h30 h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4220 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872 h6784
  change (e8052 _v) ∨ (e4562 _v) at p15155
  change (¬ (e8052 _v)) at p19363
  rcases p15155 with hlit | hlit
  · exact (False.elim (p19363 hlit))
  · exact hlit
theorem n19367 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4220 : (e4220 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) : (e4562 _v) := by
  have p15155 := n15155 _v _q 
  have p19365 := n19365 _v _q h30 h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4220 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h4899
  change (e8052 _v) ∨ (e4562 _v) at p15155
  change (¬ (e8052 _v)) at p19365
  rcases p15155 with hlit | hlit
  · exact (False.elim (p19365 hlit))
  · exact hlit
theorem n19368 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2799 : (e2799 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4220 : (e4220 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) : (e7489 _v) := by
  have p11376 := n11376 _v _q 
  have p8511 := n8511 _v _q h2799
  have p5255 := n5255 _v _q 
  have p19273 := n19273 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p19279 := n19279 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p19367 := n19367 _v _q h30 h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4220 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h4899
  have p4990 := n4990 _v _q h4648
  have p5000 := n5000 _v _q h30
  have p16464 := n16464 _v _q h2799
  have p19344 := n19344 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p4972 := n4972 _v _q h4899
  have p5004 := n5004 _v _q h4220
  have p17074 := n17074 _v _q 
  have p4985 := n4985 _v _q h4156
  have p13951 := n13951 _v _q 
  have p16913 := n16913 _v _q 
  have p4987 := n4987 _v _q h4434
  have p5010 := n5010 _v _q h70
  have p4981 := n4981 _v _q h4260
  have p19289 := n19289 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p4988 := n4988 _v _q h488
  have p19317 := n19317 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p17080 := n17080 _v _q 
  have p17078 := n17078 _v _q 
  have p4989 := n4989 _v _q h4838
  have p4971 := n4971 _v _q h4419
  have p17091 := n17091 _v _q 
  have p4979 := n4979 _v _q h4139
  have p4986 := n4986 _v _q h3105
  have p4978 := n4978 _v _q h4477
  have p4992 := n4992 _v _q h442
  have p16461 := n16461 _v _q h2799
  have p19275 := n19275 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p4984 := n4984 _v _q h4872
  have p17083 := n17083 _v _q 
  have p4991 := n4991 _v _q h4608
  have p17087 := n17087 _v _q 
  have p16778 := n16778 _v _q 
  have p17115 := n17115 _v _q 
  have p17111 := n17111 _v _q 
  have p253 := n253 _v _q h191
  have p19347 := n19347 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p17098 := n17098 _v _q 
  have p17104 := n17104 _v _q 
  have p17110 := n17110 _v _q 
  have p17096 := n17096 _v _q 
  have p17106 := n17106 _v _q 
  have p17089 := n17089 _v _q 
  have p17102 := n17102 _v _q 
  have p17108 := n17108 _v _q 
  have p4994 := n4994 _v _q h3069
  have p17117 := n17117 _v _q 
  have p17120 := n17120 _v _q 
  have p17113 := n17113 _v _q 
  have p17124 := n17124 _v _q 
  have p17122 := n17122 _v _q 
  have p16911 := n16911 _v _q 
  have p17093 := n17093 _v _q 
  have p17141 := n17141 _v _q 
  have p17131 := n17131 _v _q 
  have p17069 := n17069 _v _q 
  have p5001 := n5001 _v _q h4096
  have p4996 := n4996 _v _q h3937
  have p17100 := n17100 _v _q 
  have p4999 := n4999 _v _q h91
  have p17133 := n17133 _v _q 
  have p17136 := n17136 _v _q 
  have p4998 := n4998 _v _q h3152
  have p4983 := n4983 _v _q h4813
  have p17053 := n17053 _v _q 
  have p5003 := n5003 _v _q h4199
  have p17127 := n17127 _v _q 
  have p4995 := n4995 _v _q h4369
  have p5008 := n5008 _v _q h4787
  have p16576 := n16576 _v _q 
  have p19278 := n19278 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p17061 := n17061 _v _q h4747
  have p17055 := n17055 _v _q 
  have p17147 := n17147 _v _q 
  have p17058 := n17058 _v _q 
  have p5006 := n5006 _v _q h4675
  have p17137 := n17137 _v _q h4059
  have p17056 := n17056 _v _q h3946
  have p5007 := n5007 _v _q h225
  have p17064 := n17064 _v _q 
  have p16929 := n16929 _v _q 
  have p4980 := n4980 _v _q h4301
  have p17067 := n17067 _v _q 
  have p17072 := n17072 _v _q 
  have p19287 := n19287 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p16394 := n16394 _v _q 
  have p16828 := n16828 _v _q h2799
  exact FloorCertificate.node_19368 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e61 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2834 _v) (e2849 _v) (e2863 _v) (e2877 _v) (e2879 _v) (e2883 _v) (e2898 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2913 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p11376 p8511 p5255 p19273 p19279 p19367 p4990 p5000 p16464 p19344 p4972 p5004 p17074 p4985 p13951 p16913 p4987 p5010 p4981 p19289 p4988 p19317 p17080 p17078 p4989 p4971 p17091 p4979 p4986 p4978 p4992 p16461 p19275 p4984 p17083 p4991 p17087 p16778 p17115 p17111 p253 p19347 p17098 p17104 p17110 p17096 p17106 p17089 p17102 p17108 p4994 p17117 p17120 p17113 p17124 p17122 p16911 p17093 p17141 p17131 p17069 p5001 p4996 p17100 p4999 p17133 p17136 p4998 p4983 p17053 p5003 p17127 p4995 p5008 p16576 p19278 p17061 p17055 p17147 p17058 p5006 p17137 p17056 p5007 p17064 p16929 p4980 p17067 p17072 p19287 p16394 p16828
theorem n19370 (_v : Vars) (_q : Query _v)  : (e19369 _v) := by
  by_contra hc
  change ¬ ((¬ (e2799 _v)) ∨ (¬ (e4648 _v)) ∨ (¬ (e30 _v)) ∨ (¬ (e4899 _v)) ∨ (¬ (e4220 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4419 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4477 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4301 _v))) at hc
  have h30 : (e30 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h70 : (e70 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))
  have h191 : (e191 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))
  have h225 : (e225 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))))
  have h442 : (e442 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))
  have h488 : (e488 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h2799 : (e2799 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h3069 : (e3069 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))
  have h3105 : (e3105 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))
  have h3946 : (e3946 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))))
  have h4059 : (e4059 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))
  have h4096 : (e4096 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))
  have h4139 : (e4139 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h4156 : (e4156 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h4199 : (e4199 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))
  have h4220 : (e4220 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4260 : (e4260 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h4301 : (e4301 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))))))))))))))))))))))))))))))
  have h4369 : (e4369 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))
  have h4419 : (e4419 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h4434 : (e4434 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h4477 : (e4477 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h4608 : (e4608 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))
  have h4648 : (e4648 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h4675 : (e4675 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))
  have h4747 : (e4747 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))
  have h4838 : (e4838 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h4872 : (e4872 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))
  have h4899 : (e4899 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have p19368 := n19368 _v _q h30 h70 h91 h191 h225 h442 h488 h2799 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4220 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h4899
  exact p19368
theorem n19371 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4220 : (e4220 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h6784 : (e6784 _v)) : (e6780 _v) := by
  have p19370 := n19370 _v _q 
  have p16513 := n16513 _v _q h6784
  have p5000 := n5000 _v _q h30
  have p15560 := n15560 _v _q h6784
  have p5004 := n5004 _v _q h4220
  have p4985 := n4985 _v _q h4156
  have p4987 := n4987 _v _q h4434
  have p5010 := n5010 _v _q h70
  have p4981 := n4981 _v _q h4260
  have p4988 := n4988 _v _q h488
  have p4989 := n4989 _v _q h4838
  have p4971 := n4971 _v _q h4419
  have p4979 := n4979 _v _q h4139
  have p4986 := n4986 _v _q h3105
  have p4978 := n4978 _v _q h4477
  have p4992 := n4992 _v _q h442
  have p4984 := n4984 _v _q h4872
  have p4991 := n4991 _v _q h4608
  have p253 := n253 _v _q h191
  have p4994 := n4994 _v _q h3069
  have p5001 := n5001 _v _q h4096
  have p4996 := n4996 _v _q h3937
  have p4999 := n4999 _v _q h91
  have p4998 := n4998 _v _q h3152
  have p4983 := n4983 _v _q h4813
  have p5003 := n5003 _v _q h4199
  have p4995 := n4995 _v _q h4369
  have p5008 := n5008 _v _q h4787
  have p17061 := n17061 _v _q h4747
  have p5006 := n5006 _v _q h4675
  have p17137 := n17137 _v _q h4059
  have p17056 := n17056 _v _q h3946
  have p5007 := n5007 _v _q h225
  have p4980 := n4980 _v _q h4301
  change (¬ (e2799 _v)) ∨ (¬ (e4648 _v)) ∨ (¬ (e30 _v)) ∨ (¬ (e4899 _v)) ∨ (¬ (e4220 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4419 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4477 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4301 _v)) at p19370
  rcases p19370 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p16513))
  · exact (False.elim (hlit p5000))
  · exact (False.elim (hlit p15560))
  · exact (False.elim (hlit p5004))
  · exact (False.elim (hlit p4985))
  · exact (False.elim (hlit p4987))
  · exact (False.elim (hlit p5010))
  · exact (False.elim (hlit p4981))
  · exact (False.elim (hlit p4988))
  · exact (False.elim (hlit p4989))
  · exact (False.elim (hlit p4971))
  · exact (False.elim (hlit p4979))
  · exact (False.elim (hlit p4986))
  · exact (False.elim (hlit p4978))
  · exact (False.elim (hlit p4992))
  · exact (False.elim (hlit p4984))
  · exact (False.elim (hlit p4991))
  · exact (False.elim (hlit p253))
  · exact (False.elim (hlit p4994))
  · exact (False.elim (hlit p5001))
  · exact (False.elim (hlit p4996))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p5003))
  · exact (False.elim (hlit p4995))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p17061))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p17137))
  · exact (False.elim (hlit p17056))
  · exact (False.elim (hlit p5007))
  · exact (False.elim (hlit p4980))
theorem n19372 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4220 : (e4220 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h6784 : (e6784 _v)) : (e8408 _v) := by
  have p15435 := n15435 _v _q 
  have p19371 := n19371 _v _q h30 h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4220 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872 h6784
  change (e2799 _v) ∨ (¬ (e8407 _v)) at p15435
  change (¬ (e2799 _v)) at p19371
  rcases p15435 with hlit | hlit
  · exact (False.elim (p19371 hlit))
  · exact hlit
theorem n19373 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4220 : (e4220 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) : (e6780 _v) := by
  have p19370 := n19370 _v _q 
  have p4990 := n4990 _v _q h4648
  have p5000 := n5000 _v _q h30
  have p4972 := n4972 _v _q h4899
  have p5004 := n5004 _v _q h4220
  have p4985 := n4985 _v _q h4156
  have p4987 := n4987 _v _q h4434
  have p5010 := n5010 _v _q h70
  have p4981 := n4981 _v _q h4260
  have p4988 := n4988 _v _q h488
  have p4989 := n4989 _v _q h4838
  have p4971 := n4971 _v _q h4419
  have p4979 := n4979 _v _q h4139
  have p4986 := n4986 _v _q h3105
  have p4978 := n4978 _v _q h4477
  have p4992 := n4992 _v _q h442
  have p4984 := n4984 _v _q h4872
  have p4991 := n4991 _v _q h4608
  have p253 := n253 _v _q h191
  have p4994 := n4994 _v _q h3069
  have p5001 := n5001 _v _q h4096
  have p4996 := n4996 _v _q h3937
  have p4999 := n4999 _v _q h91
  have p4998 := n4998 _v _q h3152
  have p4983 := n4983 _v _q h4813
  have p5003 := n5003 _v _q h4199
  have p4995 := n4995 _v _q h4369
  have p5008 := n5008 _v _q h4787
  have p17061 := n17061 _v _q h4747
  have p5006 := n5006 _v _q h4675
  have p17137 := n17137 _v _q h4059
  have p17056 := n17056 _v _q h3946
  have p5007 := n5007 _v _q h225
  have p4980 := n4980 _v _q h4301
  change (¬ (e2799 _v)) ∨ (¬ (e4648 _v)) ∨ (¬ (e30 _v)) ∨ (¬ (e4899 _v)) ∨ (¬ (e4220 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4419 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4477 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4301 _v)) at p19370
  rcases p19370 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p4990))
  · exact (False.elim (hlit p5000))
  · exact (False.elim (hlit p4972))
  · exact (False.elim (hlit p5004))
  · exact (False.elim (hlit p4985))
  · exact (False.elim (hlit p4987))
  · exact (False.elim (hlit p5010))
  · exact (False.elim (hlit p4981))
  · exact (False.elim (hlit p4988))
  · exact (False.elim (hlit p4989))
  · exact (False.elim (hlit p4971))
  · exact (False.elim (hlit p4979))
  · exact (False.elim (hlit p4986))
  · exact (False.elim (hlit p4978))
  · exact (False.elim (hlit p4992))
  · exact (False.elim (hlit p4984))
  · exact (False.elim (hlit p4991))
  · exact (False.elim (hlit p253))
  · exact (False.elim (hlit p4994))
  · exact (False.elim (hlit p5001))
  · exact (False.elim (hlit p4996))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p5003))
  · exact (False.elim (hlit p4995))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p17061))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p17137))
  · exact (False.elim (hlit p17056))
  · exact (False.elim (hlit p5007))
  · exact (False.elim (hlit p4980))
theorem n19374 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4220 : (e4220 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) : (e8408 _v) := by
  have p15435 := n15435 _v _q 
  have p19373 := n19373 _v _q h30 h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4220 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h4899
  change (e2799 _v) ∨ (¬ (e8407 _v)) at p15435
  change (¬ (e2799 _v)) at p19373
  rcases p15435 with hlit | hlit
  · exact (False.elim (p19373 hlit))
  · exact hlit
theorem n19375 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4220 : (e4220 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) : (e8398 _v) := by
  have p11470 := n11470 _v _q 
  have p19374 := n19374 _v _q h30 h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4220 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h4899
  change (e8407 _v) ∨ (e8398 _v) at p11470
  change (¬ (e8407 _v)) at p19374
  rcases p11470 with hlit | hlit
  · exact (False.elim (p19374 hlit))
  · exact hlit
theorem n19376 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2691 : (e2691 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4220 : (e4220 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) (h6579 : (e6579 _v)) : (e7489 _v) := by
  have p19273 := n19273 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p5257 := n5257 _v _q 
  have p17230 := n17230 _v _q h6579
  have p5255 := n5255 _v _q 
  have p19367 := n19367 _v _q h30 h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4220 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h4899
  have p4990 := n4990 _v _q h4648
  have p17221 := n17221 _v _q 
  have p5000 := n5000 _v _q h30
  have p19375 := n19375 _v _q h30 h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4220 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h4899
  have p19344 := n19344 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p4972 := n4972 _v _q h4899
  have p5004 := n5004 _v _q h4220
  have p17074 := n17074 _v _q 
  have p4985 := n4985 _v _q h4156
  have p13951 := n13951 _v _q 
  have p16913 := n16913 _v _q 
  have p4987 := n4987 _v _q h4434
  have p5010 := n5010 _v _q h70
  have p4981 := n4981 _v _q h4260
  have p19289 := n19289 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p4988 := n4988 _v _q h488
  have p19317 := n19317 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p17080 := n17080 _v _q 
  have p17078 := n17078 _v _q 
  have p4989 := n4989 _v _q h4838
  have p4971 := n4971 _v _q h4419
  have p17091 := n17091 _v _q 
  have p4979 := n4979 _v _q h4139
  have p4986 := n4986 _v _q h3105
  have p4978 := n4978 _v _q h4477
  have p4992 := n4992 _v _q h442
  have p16994 := n16994 _v _q 
  have p19275 := n19275 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p4984 := n4984 _v _q h4872
  have p17083 := n17083 _v _q 
  have p4991 := n4991 _v _q h4608
  have p17087 := n17087 _v _q 
  have p16778 := n16778 _v _q 
  have p17115 := n17115 _v _q 
  have p17111 := n17111 _v _q 
  have p253 := n253 _v _q h191
  have p19347 := n19347 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p17098 := n17098 _v _q 
  have p17104 := n17104 _v _q 
  have p17110 := n17110 _v _q 
  have p17096 := n17096 _v _q 
  have p17106 := n17106 _v _q 
  have p17089 := n17089 _v _q 
  have p17102 := n17102 _v _q 
  have p17108 := n17108 _v _q 
  have p4994 := n4994 _v _q h3069
  have p17117 := n17117 _v _q 
  have p17120 := n17120 _v _q 
  have p17113 := n17113 _v _q 
  have p17124 := n17124 _v _q 
  have p17122 := n17122 _v _q 
  have p16911 := n16911 _v _q 
  have p17093 := n17093 _v _q 
  have p17141 := n17141 _v _q 
  have p17131 := n17131 _v _q 
  have p17069 := n17069 _v _q 
  have p5001 := n5001 _v _q h4096
  have p4996 := n4996 _v _q h3937
  have p17100 := n17100 _v _q 
  have p4999 := n4999 _v _q h91
  have p17133 := n17133 _v _q 
  have p17136 := n17136 _v _q 
  have p4998 := n4998 _v _q h3152
  have p4983 := n4983 _v _q h4813
  have p17053 := n17053 _v _q 
  have p5003 := n5003 _v _q h4199
  have p17127 := n17127 _v _q 
  have p4995 := n4995 _v _q h4369
  have p5008 := n5008 _v _q h4787
  have p16576 := n16576 _v _q 
  have p19278 := n19278 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p17061 := n17061 _v _q h4747
  have p17055 := n17055 _v _q 
  have p17147 := n17147 _v _q 
  have p17058 := n17058 _v _q 
  have p5006 := n5006 _v _q h4675
  have p17137 := n17137 _v _q h4059
  have p17056 := n17056 _v _q h3946
  have p5007 := n5007 _v _q h225
  have p17064 := n17064 _v _q 
  have p16929 := n16929 _v _q 
  have p4980 := n4980 _v _q h4301
  have p17067 := n17067 _v _q 
  have p17072 := n17072 _v _q 
  have p19287 := n19287 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p16394 := n16394 _v _q 
  have p11457 := n11457 _v _q h2691
  exact FloorCertificate.node_19376 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e61 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2834 _v) (e2849 _v) (e2863 _v) (e2877 _v) (e2879 _v) (e2883 _v) (e2898 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2913 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p19273 p5257 p17230 p5255 p19367 p4990 p17221 p5000 p19375 p19344 p4972 p5004 p17074 p4985 p13951 p16913 p4987 p5010 p4981 p19289 p4988 p19317 p17080 p17078 p4989 p4971 p17091 p4979 p4986 p4978 p4992 p16994 p19275 p4984 p17083 p4991 p17087 p16778 p17115 p17111 p253 p19347 p17098 p17104 p17110 p17096 p17106 p17089 p17102 p17108 p4994 p17117 p17120 p17113 p17124 p17122 p16911 p17093 p17141 p17131 p17069 p5001 p4996 p17100 p4999 p17133 p17136 p4998 p4983 p17053 p5003 p17127 p4995 p5008 p16576 p19278 p17061 p17055 p17147 p17058 p5006 p17137 p17056 p5007 p17064 p16929 p4980 p17067 p17072 p19287 p16394 p11457
theorem n19377 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2371 : (e2371 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4220 : (e4220 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) : (e7489 _v) := by
  have p17511 := n17511 _v _q 
  have p15576 := n15576 _v _q h2371
  have p11400 := n11400 _v _q h2371
  have p4989 := n4989 _v _q h4838
  have p4990 := n4990 _v _q h4648
  have p253 := n253 _v _q h191
  have p19347 := n19347 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p4991 := n4991 _v _q h4608
  have p4992 := n4992 _v _q h442
  have p4972 := n4972 _v _q h4899
  have p4995 := n4995 _v _q h4369
  have p4994 := n4994 _v _q h3069
  have p19276 := n19276 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p4996 := n4996 _v _q h3937
  have p4999 := n4999 _v _q h91
  have p4998 := n4998 _v _q h3152
  have p5001 := n5001 _v _q h4096
  have p17111 := n17111 _v _q 
  have p19287 := n19287 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p5003 := n5003 _v _q h4199
  have p19278 := n19278 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p5000 := n5000 _v _q h30
  have p17056 := n17056 _v _q h3946
  have p5007 := n5007 _v _q h225
  have p5008 := n5008 _v _q h4787
  have p17061 := n17061 _v _q h4747
  have p5010 := n5010 _v _q h70
  have p17137 := n17137 _v _q h4059
  have p5006 := n5006 _v _q h4675
  have p19289 := n19289 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p4971 := n4971 _v _q h4419
  have p5004 := n5004 _v _q h4220
  have p19367 := n19367 _v _q h30 h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4220 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h4899
  have p19375 := n19375 _v _q h30 h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4220 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h4899
  have p19344 := n19344 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p19317 := n19317 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p4978 := n4978 _v _q h4477
  have p4979 := n4979 _v _q h4139
  have p4980 := n4980 _v _q h4301
  have p4981 := n4981 _v _q h4260
  have p4983 := n4983 _v _q h4813
  have p4984 := n4984 _v _q h4872
  have p4985 := n4985 _v _q h4156
  have p4986 := n4986 _v _q h3105
  have p4987 := n4987 _v _q h4434
  have p4988 := n4988 _v _q h488
  have p19273 := n19273 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (¬ (e5018 _v)) ∨ (¬ (e2634 _v)) ∨ (¬ (e2371 _v)) ∨ (¬ (e2482 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e4648 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e3566 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4398 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e30 _v)) ∨ (¬ (e4491 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e4220 _v)) ∨ (¬ (e3976 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e8398 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4724 _v)) ∨ (¬ (e4419 _v)) ∨ (¬ (e4899 _v)) ∨ (¬ (e4562 _v)) ∨ (¬ (e4546 _v)) ∨ (¬ (e4285 _v)) ∨ (¬ (e4477 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e4301 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e4838 _v)) at p17511
  rcases p17511 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact (False.elim (hlit p15576))
  · exact (False.elim (hlit p19273))
  · exact (False.elim (hlit p11400))
  · exact (False.elim (hlit p19276))
  · exact (False.elim (hlit p253))
  · exact (False.elim (hlit p4990))
  · exact (False.elim (hlit p4991))
  · exact (False.elim (hlit p4992))
  · exact (False.elim (hlit p17111))
  · exact (False.elim (hlit p4995))
  · exact (False.elim (hlit p4994))
  · exact (False.elim (hlit p19278))
  · exact (False.elim (hlit p4996))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p5001))
  · exact (False.elim (hlit p5000))
  · exact (False.elim (hlit p19287))
  · exact (False.elim (hlit p5003))
  · exact (False.elim (hlit p5004))
  · exact (False.elim (hlit p19347))
  · exact (False.elim (hlit p17056))
  · exact (False.elim (hlit p5007))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p19375))
  · exact (False.elim (hlit p17061))
  · exact (False.elim (hlit p5010))
  · exact (False.elim (hlit p17137))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p19289))
  · exact (False.elim (hlit p4971))
  · exact (False.elim (hlit p4972))
  · exact (False.elim (hlit p19367))
  · exact (False.elim (hlit p19344))
  · exact (False.elim (hlit p19317))
  · exact (False.elim (hlit p4978))
  · exact (False.elim (hlit p4979))
  · exact (False.elim (hlit p4980))
  · exact (False.elim (hlit p4981))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p4984))
  · exact (False.elim (hlit p4985))
  · exact (False.elim (hlit p4986))
  · exact (False.elim (hlit p4987))
  · exact (False.elim (hlit p4988))
  · exact (False.elim (hlit p4989))
theorem n19379 (_v : Vars) (_q : Query _v)  : (e19378 _v) := by
  by_contra hc
  change ¬ ((¬ (e2371 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4648 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e4899 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e30 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4419 _v)) ∨ (¬ (e4220 _v)) ∨ (¬ (e4477 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e4301 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e488 _v))) at hc
  have h30 : (e30 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h70 : (e70 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h191 : (e191 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h225 : (e225 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))
  have h442 : (e442 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h488 : (e488 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))))))))))))))))))))))))))))))
  have h2371 : (e2371 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h3069 : (e3069 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h3105 : (e3105 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h3946 : (e3946 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))
  have h4059 : (e4059 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))
  have h4096 : (e4096 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h4139 : (e4139 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))
  have h4156 : (e4156 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))
  have h4199 : (e4199 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h4220 : (e4220 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))
  have h4260 : (e4260 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))
  have h4301 : (e4301 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))
  have h4369 : (e4369 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h4419 : (e4419 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))
  have h4434 : (e4434 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))))
  have h4477 : (e4477 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))
  have h4608 : (e4608 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4648 : (e4648 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4675 : (e4675 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))
  have h4747 : (e4747 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))
  have h4838 : (e4838 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h4872 : (e4872 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))
  have h4899 : (e4899 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have p19377 := n19377 _v _q h30 h70 h91 h191 h225 h442 h488 h2371 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4220 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h4899
  exact p19377
theorem n19381 (_v : Vars) (_q : Query _v)  : (e19380 _v) := by
  by_contra hc
  change ¬ ((e2371 _v) ∨ (¬ (e4648 _v)) ∨ (¬ (e30 _v)) ∨ (¬ (e4899 _v)) ∨ (¬ (e4220 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4419 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4477 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4301 _v)) ∨ (¬ (e2691 _v))) at hc
  have h30 : (e30 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h70 : (e70 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))
  have h191 : (e191 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))
  have h225 : (e225 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))))
  have h442 : (e442 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))
  have h488 : (e488 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h2691 : (e2691 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn)))))))))))))))))))))))))))))))))))
  have h3069 : (e3069 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))
  have h3105 : (e3105 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))
  have h3946 : (e3946 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))))
  have h4059 : (e4059 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))
  have h4096 : (e4096 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))
  have h4139 : (e4139 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h4156 : (e4156 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h4199 : (e4199 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))
  have h4220 : (e4220 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4260 : (e4260 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h4301 : (e4301 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))))))
  have h4369 : (e4369 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))
  have h4419 : (e4419 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h4434 : (e4434 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h4477 : (e4477 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h4608 : (e4608 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))
  have h4648 : (e4648 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h4675 : (e4675 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))
  have h4747 : (e4747 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))
  have h4838 : (e4838 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h4872 : (e4872 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))
  have h4899 : (e4899 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h6579 : (e6579 _v) := (fun hn => hc (Or.inl hn))
  have p19376 := n19376 _v _q h30 h70 h91 h191 h225 h442 h488 h2691 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4220 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h4899 h6579
  exact p19376
theorem n19382 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4220 : (e4220 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h6784 : (e6784 _v)) : (e6579 _v) := by
  have p19379 := n19379 _v _q 
  have p16513 := n16513 _v _q h6784
  have p4989 := n4989 _v _q h4838
  have p253 := n253 _v _q h191
  have p4991 := n4991 _v _q h4608
  have p4992 := n4992 _v _q h442
  have p15560 := n15560 _v _q h6784
  have p4995 := n4995 _v _q h4369
  have p4994 := n4994 _v _q h3069
  have p4996 := n4996 _v _q h3937
  have p4999 := n4999 _v _q h91
  have p4998 := n4998 _v _q h3152
  have p5001 := n5001 _v _q h4096
  have p5003 := n5003 _v _q h4199
  have p5000 := n5000 _v _q h30
  have p17056 := n17056 _v _q h3946
  have p5007 := n5007 _v _q h225
  have p5008 := n5008 _v _q h4787
  have p17061 := n17061 _v _q h4747
  have p5010 := n5010 _v _q h70
  have p17137 := n17137 _v _q h4059
  have p5006 := n5006 _v _q h4675
  have p4971 := n4971 _v _q h4419
  have p5004 := n5004 _v _q h4220
  have p4978 := n4978 _v _q h4477
  have p4979 := n4979 _v _q h4139
  have p4980 := n4980 _v _q h4301
  have p4981 := n4981 _v _q h4260
  have p4983 := n4983 _v _q h4813
  have p4984 := n4984 _v _q h4872
  have p4985 := n4985 _v _q h4156
  have p4986 := n4986 _v _q h3105
  have p4987 := n4987 _v _q h4434
  have p4988 := n4988 _v _q h488
  change (¬ (e2371 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4648 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e4899 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e30 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4419 _v)) ∨ (¬ (e4220 _v)) ∨ (¬ (e4477 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e4301 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e488 _v)) at p19379
  rcases p19379 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p4989))
  · exact (False.elim (hlit p16513))
  · exact (False.elim (hlit p253))
  · exact (False.elim (hlit p4991))
  · exact (False.elim (hlit p4992))
  · exact (False.elim (hlit p15560))
  · exact (False.elim (hlit p4995))
  · exact (False.elim (hlit p4994))
  · exact (False.elim (hlit p4996))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p5001))
  · exact (False.elim (hlit p5003))
  · exact (False.elim (hlit p5000))
  · exact (False.elim (hlit p17056))
  · exact (False.elim (hlit p5007))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p17061))
  · exact (False.elim (hlit p5010))
  · exact (False.elim (hlit p17137))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p4971))
  · exact (False.elim (hlit p5004))
  · exact (False.elim (hlit p4978))
  · exact (False.elim (hlit p4979))
  · exact (False.elim (hlit p4980))
  · exact (False.elim (hlit p4981))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p4984))
  · exact (False.elim (hlit p4985))
  · exact (False.elim (hlit p4986))
  · exact (False.elim (hlit p4987))
  · exact (False.elim (hlit p4988))
theorem n19383 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4220 : (e4220 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h6784 : (e6784 _v)) : (e6724 _v) := by
  have p19381 := n19381 _v _q 
  have p19382 := n19382 _v _q h30 h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4220 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872 h6784
  have p5000 := n5000 _v _q h30
  have p15560 := n15560 _v _q h6784
  have p5004 := n5004 _v _q h4220
  have p4985 := n4985 _v _q h4156
  have p4987 := n4987 _v _q h4434
  have p5010 := n5010 _v _q h70
  have p4981 := n4981 _v _q h4260
  have p4988 := n4988 _v _q h488
  have p4989 := n4989 _v _q h4838
  have p4971 := n4971 _v _q h4419
  have p4979 := n4979 _v _q h4139
  have p4986 := n4986 _v _q h3105
  have p4978 := n4978 _v _q h4477
  have p4992 := n4992 _v _q h442
  have p4984 := n4984 _v _q h4872
  have p4991 := n4991 _v _q h4608
  have p253 := n253 _v _q h191
  have p4994 := n4994 _v _q h3069
  have p5001 := n5001 _v _q h4096
  have p4996 := n4996 _v _q h3937
  have p4999 := n4999 _v _q h91
  have p4998 := n4998 _v _q h3152
  have p4983 := n4983 _v _q h4813
  have p5003 := n5003 _v _q h4199
  have p4995 := n4995 _v _q h4369
  have p5008 := n5008 _v _q h4787
  have p17061 := n17061 _v _q h4747
  have p5006 := n5006 _v _q h4675
  have p17137 := n17137 _v _q h4059
  have p17056 := n17056 _v _q h3946
  have p5007 := n5007 _v _q h225
  have p4980 := n4980 _v _q h4301
  have p16513 := n16513 _v _q h6784
  change (e2371 _v) ∨ (¬ (e4648 _v)) ∨ (¬ (e30 _v)) ∨ (¬ (e4899 _v)) ∨ (¬ (e4220 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4419 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4477 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4301 _v)) ∨ (¬ (e2691 _v)) at p19381
  change (¬ (e2371 _v)) at p19382
  rcases p19381 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact (False.elim (p19382 hlit))
  · exact (False.elim (hlit p16513))
  · exact (False.elim (hlit p5000))
  · exact (False.elim (hlit p15560))
  · exact (False.elim (hlit p5004))
  · exact (False.elim (hlit p4985))
  · exact (False.elim (hlit p4987))
  · exact (False.elim (hlit p5010))
  · exact (False.elim (hlit p4981))
  · exact (False.elim (hlit p4988))
  · exact (False.elim (hlit p4989))
  · exact (False.elim (hlit p4971))
  · exact (False.elim (hlit p4979))
  · exact (False.elim (hlit p4986))
  · exact (False.elim (hlit p4978))
  · exact (False.elim (hlit p4992))
  · exact (False.elim (hlit p4984))
  · exact (False.elim (hlit p4991))
  · exact (False.elim (hlit p253))
  · exact (False.elim (hlit p4994))
  · exact (False.elim (hlit p5001))
  · exact (False.elim (hlit p4996))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p5003))
  · exact (False.elim (hlit p4995))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p17061))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p17137))
  · exact (False.elim (hlit p17056))
  · exact (False.elim (hlit p5007))
  · exact (False.elim (hlit p4980))
  · exact hlit
theorem n19384 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4220 : (e4220 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h6784 : (e6784 _v)) : (e7517 _v) := by
  have p15196 := n15196 _v _q 
  have p19383 := n19383 _v _q h30 h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4220 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872 h6784
  change (e2691 _v) ∨ (¬ (e7497 _v)) at p15196
  change (¬ (e2691 _v)) at p19383
  rcases p15196 with hlit | hlit
  · exact (False.elim (p19383 hlit))
  · exact hlit
theorem n19385 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4220 : (e4220 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h6784 : (e6784 _v)) : (e8398 _v) := by
  have p11470 := n11470 _v _q 
  have p19372 := n19372 _v _q h30 h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4220 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872 h6784
  change (e8407 _v) ∨ (e8398 _v) at p11470
  change (¬ (e8407 _v)) at p19372
  rcases p11470 with hlit | hlit
  · exact (False.elim (p19372 hlit))
  · exact hlit
theorem n19386 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4220 : (e4220 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h6784 : (e6784 _v)) : (e7493 _v) := by
  have p15195 := n15195 _v _q 
  have p19384 := n19384 _v _q h30 h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4220 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872 h6784
  change (e7497 _v) ∨ (e7493 _v) at p15195
  change (¬ (e7497 _v)) at p19384
  rcases p15195 with hlit | hlit
  · exact (False.elim (p19384 hlit))
  · exact hlit
theorem n19387 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4220 : (e4220 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h6784 : (e6784 _v)) : (e7489 _v) := by
  have p16977 := n16977 _v _q 
  have p5257 := n5257 _v _q 
  have p5255 := n5255 _v _q 
  have p19366 := n19366 _v _q h30 h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4220 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872 h6784
  have p16513 := n16513 _v _q h6784
  have p17221 := n17221 _v _q 
  have p5000 := n5000 _v _q h30
  have p19385 := n19385 _v _q h30 h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4220 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872 h6784
  have p19344 := n19344 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p15560 := n15560 _v _q h6784
  have p5004 := n5004 _v _q h4220
  have p17074 := n17074 _v _q 
  have p4985 := n4985 _v _q h4156
  have p13951 := n13951 _v _q 
  have p19273 := n19273 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p16394 := n16394 _v _q 
  have p19386 := n19386 _v _q h30 h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4220 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872 h6784
  have p4987 := n4987 _v _q h4434
  have p5010 := n5010 _v _q h70
  have p4981 := n4981 _v _q h4260
  have p19289 := n19289 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p4988 := n4988 _v _q h488
  have p19317 := n19317 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p17080 := n17080 _v _q 
  have p17078 := n17078 _v _q 
  have p4989 := n4989 _v _q h4838
  have p4971 := n4971 _v _q h4419
  have p17091 := n17091 _v _q 
  have p4979 := n4979 _v _q h4139
  have p4986 := n4986 _v _q h3105
  have p4978 := n4978 _v _q h4477
  have p4992 := n4992 _v _q h442
  have p16994 := n16994 _v _q 
  have p19275 := n19275 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p4984 := n4984 _v _q h4872
  have p17083 := n17083 _v _q 
  have p4991 := n4991 _v _q h4608
  have p17087 := n17087 _v _q 
  have p16778 := n16778 _v _q 
  have p17115 := n17115 _v _q 
  have p17111 := n17111 _v _q 
  have p253 := n253 _v _q h191
  have p19347 := n19347 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p17098 := n17098 _v _q 
  have p17104 := n17104 _v _q 
  have p17110 := n17110 _v _q 
  have p17096 := n17096 _v _q 
  have p17106 := n17106 _v _q 
  have p17089 := n17089 _v _q 
  have p17102 := n17102 _v _q 
  have p17108 := n17108 _v _q 
  have p4994 := n4994 _v _q h3069
  have p17117 := n17117 _v _q 
  have p17120 := n17120 _v _q 
  have p17113 := n17113 _v _q 
  have p17124 := n17124 _v _q 
  have p17122 := n17122 _v _q 
  have p19382 := n19382 _v _q h30 h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4220 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872 h6784
  have p17093 := n17093 _v _q 
  have p17141 := n17141 _v _q 
  have p17131 := n17131 _v _q 
  have p17069 := n17069 _v _q 
  have p5001 := n5001 _v _q h4096
  have p4996 := n4996 _v _q h3937
  have p17100 := n17100 _v _q 
  have p4999 := n4999 _v _q h91
  have p17133 := n17133 _v _q 
  have p17136 := n17136 _v _q 
  have p4998 := n4998 _v _q h3152
  have p4983 := n4983 _v _q h4813
  have p17053 := n17053 _v _q 
  have p5003 := n5003 _v _q h4199
  have p17127 := n17127 _v _q 
  have p4995 := n4995 _v _q h4369
  have p5008 := n5008 _v _q h4787
  have p16576 := n16576 _v _q 
  have p19278 := n19278 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p17061 := n17061 _v _q h4747
  have p17055 := n17055 _v _q 
  have p17147 := n17147 _v _q 
  have p17058 := n17058 _v _q 
  have p5006 := n5006 _v _q h4675
  have p17137 := n17137 _v _q h4059
  have p17056 := n17056 _v _q h3946
  have p5007 := n5007 _v _q h225
  have p17064 := n17064 _v _q 
  have p16929 := n16929 _v _q 
  have p4980 := n4980 _v _q h4301
  have p17067 := n17067 _v _q 
  have p17072 := n17072 _v _q 
  have p19287 := n19287 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  exact FloorCertificate.node_19387 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e61 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2834 _v) (e2849 _v) (e2863 _v) (e2877 _v) (e2879 _v) (e2883 _v) (e2898 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2913 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p16977 p5257 p5255 p19366 p16513 p17221 p5000 p19385 p19344 p15560 p5004 p17074 p4985 p13951 p19273 p16394 p19386 p4987 p5010 p4981 p19289 p4988 p19317 p17080 p17078 p4989 p4971 p17091 p4979 p4986 p4978 p4992 p16994 p19275 p4984 p17083 p4991 p17087 p16778 p17115 p17111 p253 p19347 p17098 p17104 p17110 p17096 p17106 p17089 p17102 p17108 p4994 p17117 p17120 p17113 p17124 p17122 p19382 p17093 p17141 p17131 p17069 p5001 p4996 p17100 p4999 p17133 p17136 p4998 p4983 p17053 p5003 p17127 p4995 p5008 p16576 p19278 p17061 p17055 p17147 p17058 p5006 p17137 p17056 p5007 p17064 p16929 p4980 p17067 p17072 p19287
theorem n19389 (_v : Vars) (_q : Query _v)  : (e19388 _v) := by
  by_contra hc
  change ¬ ((e2793 _v) ∨ (¬ (e30 _v)) ∨ (¬ (e4220 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4419 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4477 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4301 _v))) at hc
  have h30 : (e30 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h70 : (e70 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))
  have h191 : (e191 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))
  have h225 : (e225 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))
  have h442 : (e442 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h488 : (e488 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h3069 : (e3069 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))
  have h3105 : (e3105 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))
  have h3946 : (e3946 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))
  have h4059 : (e4059 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))
  have h4096 : (e4096 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))
  have h4139 : (e4139 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h4156 : (e4156 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4199 : (e4199 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))
  have h4220 : (e4220 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4260 : (e4260 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h4301 : (e4301 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))))))))))))))))))))))))))))
  have h4369 : (e4369 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))
  have h4419 : (e4419 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h4434 : (e4434 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4477 : (e4477 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h4608 : (e4608 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))
  have h4675 : (e4675 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))
  have h4747 : (e4747 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))
  have h4838 : (e4838 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h4872 : (e4872 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h6784 : (e6784 _v) := (fun hn => hc (Or.inl hn))
  have p19387 := n19387 _v _q h30 h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4220 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872 h6784
  exact p19387
theorem n19390 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2132 : (e2132 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e2793 _v) := by
  have p19389 := n19389 _v _q 
  have p16515 := n16515 _v _q h2132
  have p16336 := n16336 _v _q h2132
  have p4985 := n4985 _v _q h4156
  have p4987 := n4987 _v _q h4434
  have p5010 := n5010 _v _q h70
  have p4981 := n4981 _v _q h4260
  have p4988 := n4988 _v _q h488
  have p4989 := n4989 _v _q h4838
  have p4971 := n4971 _v _q h4419
  have p4979 := n4979 _v _q h4139
  have p4986 := n4986 _v _q h3105
  have p4978 := n4978 _v _q h4477
  have p4992 := n4992 _v _q h442
  have p4984 := n4984 _v _q h4872
  have p4991 := n4991 _v _q h4608
  have p253 := n253 _v _q h191
  have p4994 := n4994 _v _q h3069
  have p5001 := n5001 _v _q h4096
  have p4996 := n4996 _v _q h3937
  have p4999 := n4999 _v _q h91
  have p4998 := n4998 _v _q h3152
  have p4983 := n4983 _v _q h4813
  have p5003 := n5003 _v _q h4199
  have p4995 := n4995 _v _q h4369
  have p5008 := n5008 _v _q h4787
  have p17061 := n17061 _v _q h4747
  have p5006 := n5006 _v _q h4675
  have p17137 := n17137 _v _q h4059
  have p17056 := n17056 _v _q h3946
  have p5007 := n5007 _v _q h225
  have p4980 := n4980 _v _q h4301
  change (e2793 _v) ∨ (¬ (e30 _v)) ∨ (¬ (e4220 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4419 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4477 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4301 _v)) at p19389
  rcases p19389 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p16515))
  · exact (False.elim (hlit p16336))
  · exact (False.elim (hlit p4985))
  · exact (False.elim (hlit p4987))
  · exact (False.elim (hlit p5010))
  · exact (False.elim (hlit p4981))
  · exact (False.elim (hlit p4988))
  · exact (False.elim (hlit p4989))
  · exact (False.elim (hlit p4971))
  · exact (False.elim (hlit p4979))
  · exact (False.elim (hlit p4986))
  · exact (False.elim (hlit p4978))
  · exact (False.elim (hlit p4992))
  · exact (False.elim (hlit p4984))
  · exact (False.elim (hlit p4991))
  · exact (False.elim (hlit p253))
  · exact (False.elim (hlit p4994))
  · exact (False.elim (hlit p5001))
  · exact (False.elim (hlit p4996))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p5003))
  · exact (False.elim (hlit p4995))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p17061))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p17137))
  · exact (False.elim (hlit p17056))
  · exact (False.elim (hlit p5007))
  · exact (False.elim (hlit p4980))
theorem n19391 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2132 : (e2132 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e4910 _v) := by
  have p14701 := n14701 _v _q 
  have p19390 := n19390 _v _q h70 h91 h191 h225 h442 h488 h2132 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (¬ (e2793 _v)) ∨ (¬ (e4909 _v)) at p14701
  rcases p14701 with hlit | hlit
  · exact (False.elim (hlit p19390))
  · exact hlit
theorem n19392 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2132 : (e2132 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e4903 _v) := by
  have p14973 := n14973 _v _q 
  have p19391 := n19391 _v _q h70 h91 h191 h225 h442 h488 h2132 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (e4909 _v) ∨ (e4903 _v) at p14973
  change (¬ (e4909 _v)) at p19391
  rcases p14973 with hlit | hlit
  · exact (False.elim (p19391 hlit))
  · exact hlit
theorem n19394 (_v : Vars) (_q : Query _v)  : (e19393 _v) := by
  by_contra hc
  change ¬ ((¬ (e2799 _v)) ∨ (¬ (e2793 _v))) at hc
  have h2793 : (e2793 _v) := Classical.byContradiction (fun hn => hc (Or.inr hn))
  have h2799 : (e2799 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have p11483 := n11483 _v _q h2793 h2799
  exact p11483
theorem n19395 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2132 : (e2132 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e6780 _v) := by
  have p19394 := n19394 _v _q 
  have p19390 := n19390 _v _q h70 h91 h191 h225 h442 h488 h2132 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (¬ (e2799 _v)) ∨ (¬ (e2793 _v)) at p19394
  rcases p19394 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p19390))
theorem n19396 (_v : Vars) (_q : Query _v)  : (e8507 _v) := by
  simp only [e8395, e8398, e8405, e8406, e8407, e8507] at *
  tauto
theorem n19397 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2132 : (e2132 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e8408 _v) := by
  have p15435 := n15435 _v _q 
  have p19395 := n19395 _v _q h70 h91 h191 h225 h442 h488 h2132 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (e2799 _v) ∨ (¬ (e8407 _v)) at p15435
  change (¬ (e2799 _v)) at p19395
  rcases p15435 with hlit | hlit
  · exact (False.elim (p19395 hlit))
  · exact hlit
theorem n19398 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2132 : (e2132 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e8395 _v) := by
  have p19396 := n19396 _v _q 
  have p19397 := n19397 _v _q h70 h91 h191 h225 h442 h488 h2132 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (e8407 _v) ∨ (e8395 _v) at p19396
  change (¬ (e8407 _v)) at p19397
  rcases p19396 with hlit | hlit
  · exact (False.elim (p19397 hlit))
  · exact hlit
theorem n19399 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2132 : (e2132 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e4899 _v) := by
  have p19398 := n19398 _v _q h70 h91 h191 h225 h442 h488 h2132 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p19390 := n19390 _v _q h70 h91 h191 h225 h442 h488 h2132 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p19392 := n19392 _v _q h70 h91 h191 h225 h442 h488 h2132 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  exact FloorCertificate.node_19399 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) (e2913 _v) (e2996 _v) p19398 p19390 p19392
theorem n19400 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2132 : (e2132 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4563 : (e4563 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e4649 _v) := by
  have p19361 := n19361 _v _q 
  have p15158 := n15158 _v _q h4563
  have p16515 := n16515 _v _q h2132
  have p16336 := n16336 _v _q h2132
  have p4985 := n4985 _v _q h4156
  have p19399 := n19399 _v _q h70 h91 h191 h225 h442 h488 h2132 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p4987 := n4987 _v _q h4434
  have p5010 := n5010 _v _q h70
  have p4981 := n4981 _v _q h4260
  have p4988 := n4988 _v _q h488
  have p4989 := n4989 _v _q h4838
  have p4971 := n4971 _v _q h4419
  have p4979 := n4979 _v _q h4139
  have p4986 := n4986 _v _q h3105
  have p4978 := n4978 _v _q h4477
  have p4992 := n4992 _v _q h442
  have p4984 := n4984 _v _q h4872
  have p4991 := n4991 _v _q h4608
  have p253 := n253 _v _q h191
  have p4994 := n4994 _v _q h3069
  have p5001 := n5001 _v _q h4096
  have p4996 := n4996 _v _q h3937
  have p4999 := n4999 _v _q h91
  have p4998 := n4998 _v _q h3152
  have p4983 := n4983 _v _q h4813
  have p5003 := n5003 _v _q h4199
  have p4995 := n4995 _v _q h4369
  have p5008 := n5008 _v _q h4787
  have p17061 := n17061 _v _q h4747
  have p5006 := n5006 _v _q h4675
  have p17137 := n17137 _v _q h4059
  have p17056 := n17056 _v _q h3946
  have p5007 := n5007 _v _q h225
  have p4980 := n4980 _v _q h4301
  change (¬ (e30 _v)) ∨ (¬ (e4648 _v)) ∨ (¬ (e4899 _v)) ∨ (¬ (e4220 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e1995 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4419 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4477 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4301 _v)) at p19361
  rcases p19361 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact (False.elim (hlit p16515))
  · exact hlit
  · exact (False.elim (hlit p19399))
  · exact (False.elim (hlit p16336))
  · exact (False.elim (hlit p4985))
  · exact (False.elim (hlit p15158))
  · exact (False.elim (hlit p4987))
  · exact (False.elim (hlit p5010))
  · exact (False.elim (hlit p4981))
  · exact (False.elim (hlit p4988))
  · exact (False.elim (hlit p4989))
  · exact (False.elim (hlit p4971))
  · exact (False.elim (hlit p4979))
  · exact (False.elim (hlit p4986))
  · exact (False.elim (hlit p4978))
  · exact (False.elim (hlit p4992))
  · exact (False.elim (hlit p4984))
  · exact (False.elim (hlit p4991))
  · exact (False.elim (hlit p253))
  · exact (False.elim (hlit p4994))
  · exact (False.elim (hlit p5001))
  · exact (False.elim (hlit p4996))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p5003))
  · exact (False.elim (hlit p4995))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p17061))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p17137))
  · exact (False.elim (hlit p17056))
  · exact (False.elim (hlit p5007))
  · exact (False.elim (hlit p4980))
theorem n19401 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2132 : (e2132 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4563 : (e4563 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e7489 _v) := by
  have p15027 := n15027 _v _q 
  have p19400 := n19400 _v _q h70 h91 h191 h225 h442 h488 h2132 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4563 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p19346 := n19346 _v _q h70 h91 h191 h225 h442 h488 h2132 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4419 h4434 h4477 h4563 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (e8149 _v) ∨ (e4648 _v) at p15027
  change (¬ (e4648 _v)) at p19400
  change (¬ (e8149 _v)) at p19346
  rcases p15027 with hlit | hlit
  · exact (False.elim (p19346 hlit))
  · exact (False.elim (p19400 hlit))
end
end Assembly
