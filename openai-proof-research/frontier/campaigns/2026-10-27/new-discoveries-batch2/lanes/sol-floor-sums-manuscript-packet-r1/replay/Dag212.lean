import Dag211
import generated.th_lemma_26
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n19500 (_v : Vars) (_q : Query _v)  : (e19499 _v) := by
  by_contra hc
  change ¬ ((e2475 _v) ∨ (¬ (e4369 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4419 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4477 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4199 _v))) at hc
  have h70 : (e70 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))
  have h191 : (e191 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))
  have h225 : (e225 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h442 : (e442 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))
  have h488 : (e488 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h3069 : (e3069 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))
  have h3105 : (e3105 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))
  have h3946 : (e3946 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h4059 : (e4059 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4096 : (e4096 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))
  have h4139 : (e4139 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))
  have h4156 : (e4156 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h4199 : (e4199 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn)))))))))))))))))))))))))))))
  have h4260 : (e4260 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h4369 : (e4369 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h4419 : (e4419 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h4434 : (e4434 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h4477 : (e4477 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))
  have h4608 : (e4608 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))
  have h4675 : (e4675 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4747 : (e4747 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))
  have h4838 : (e4838 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h4872 : (e4872 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))
  have h8038 : (e8038 _v) := (fun hn => hc (Or.inl hn))
  have p19498 := n19498 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872 h8038
  exact p19498
theorem n19501 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e2475 _v) := by
  have p19500 := n19500 _v _q 
  have p17137 := n17137 _v _q h4059
  have p5008 := n5008 _v _q h4787
  have p5006 := n5006 _v _q h4675
  have p4995 := n4995 _v _q h4369
  have p17056 := n17056 _v _q h3946
  have p17061 := n17061 _v _q h4747
  have p5007 := n5007 _v _q h225
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
  change (e2475 _v) ∨ (¬ (e4369 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4419 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4477 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4199 _v)) at p19500
  rcases p19500 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p4995))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p17137))
  · exact (False.elim (hlit p17056))
  · exact (False.elim (hlit p17061))
  · exact (False.elim (hlit p5007))
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
theorem n19502 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e8346 _v) := by
  have p16987 := n16987 _v _q 
  have p19501 := n19501 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p4987 := n4987 _v _q h4434
  have p19463 := n19463 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (¬ (e8338 _v)) ∨ (¬ (e2475 _v)) ∨ (¬ (e4434 _v)) ∨ (e4301 _v) at p16987
  change (¬ (e4301 _v)) at p19463
  rcases p16987 with hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p19501))
  · exact (False.elim (hlit p4987))
  · exact (False.elim (p19463 hlit))
theorem n19503 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e8347 _v) := by
  have p15580 := n15580 _v _q 
  have p19502 := n19502 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (e8347 _v) ∨ (e8338 _v) at p15580
  change (¬ (e8338 _v)) at p19502
  rcases p15580 with hlit | hlit
  · exact hlit
  · exact (False.elim (p19502 hlit))
theorem n19504 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e2592 _v) := by
  have p15312 := n15312 _v _q 
  have p19503 := n19503 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (e2592 _v) ∨ (¬ (e8347 _v)) at p15312
  rcases p15312 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p19503))
theorem n19505 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e8330 _v) := by
  have p14907 := n14907 _v _q 
  have p19504 := n19504 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (¬ (e2592 _v)) ∨ (¬ (e8324 _v)) at p14907
  rcases p14907 with hlit | hlit
  · exact (False.elim (hlit p19504))
  · exact hlit
theorem n19506 (_v : Vars) (_q : Query _v)  : (e8516 _v) := by
  simp only [e4855, e4856, e4857, e4858, e8324, e8516] at *
  tauto
theorem n19507 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e4857 _v) := by
  have p19506 := n19506 _v _q 
  have p19505 := n19505 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (e8324 _v) ∨ (e4857 _v) at p19506
  change (¬ (e8324 _v)) at p19505
  rcases p19506 with hlit | hlit
  · exact (False.elim (p19505 hlit))
  · exact hlit
theorem n19508 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e7489 _v) := by
  have p19470 := n19470 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p19507 := n19507 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p258 := n258 _v _q 
  have p19463 := n19463 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  exact FloorCertificate.node_19508 (e17 _v) (e2898 _v) (e2970 _v) p19470 p19507 p258 p19463
theorem n19510 (_v : Vars) (_q : Query _v)  : (e19509 _v) := by
  by_contra hc
  change ¬ ((¬ (e4059 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4419 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4477 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4199 _v))) at hc
  have h70 : (e70 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))
  have h191 : (e191 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))
  have h225 : (e225 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h442 : (e442 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))
  have h488 : (e488 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h3069 : (e3069 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))
  have h3105 : (e3105 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))
  have h3946 : (e3946 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h4059 : (e4059 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h4096 : (e4096 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))
  have h4139 : (e4139 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h4156 : (e4156 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h4199 : (e4199 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))))))))))))))))))))))))
  have h4260 : (e4260 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h4369 : (e4369 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4419 : (e4419 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h4434 : (e4434 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h4477 : (e4477 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))
  have h4608 : (e4608 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))
  have h4675 : (e4675 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4747 : (e4747 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))
  have h4838 : (e4838 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h4872 : (e4872 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))
  have p19508 := n19508 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  exact p19508
theorem n19511 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e4064 _v) := by
  have p19510 := n19510 _v _q 
  have p4978 := n4978 _v _q h4477
  have p5008 := n5008 _v _q h4787
  have p5006 := n5006 _v _q h4675
  have p4995 := n4995 _v _q h4369
  have p17056 := n17056 _v _q h3946
  have p17061 := n17061 _v _q h4747
  have p5007 := n5007 _v _q h225
  have p4985 := n4985 _v _q h4156
  have p5010 := n5010 _v _q h70
  have p4981 := n4981 _v _q h4260
  have p4988 := n4988 _v _q h488
  have p4989 := n4989 _v _q h4838
  have p4971 := n4971 _v _q h4419
  have p4979 := n4979 _v _q h4139
  have p4986 := n4986 _v _q h3105
  have p4987 := n4987 _v _q h4434
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
  change (¬ (e4059 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4419 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4477 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4199 _v)) at p19510
  rcases p19510 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p4987))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p4995))
  · exact (False.elim (hlit p17056))
  · exact (False.elim (hlit p17061))
  · exact (False.elim (hlit p5007))
  · exact (False.elim (hlit p4985))
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
theorem n19512 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e4066 _v) := by
  have p14980 := n14980 _v _q 
  have p19511 := n19511 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (e4066 _v) ∨ (e4059 _v) at p14980
  change (¬ (e4059 _v)) at p19511
  rcases p14980 with hlit | hlit
  · exact hlit
  · exact (False.elim (p19511 hlit))
theorem n19513 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e6684 _v) := by
  have p14703 := n14703 _v _q 
  have p19512 := n19512 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (¬ (e2598 _v)) ∨ (¬ (e4066 _v)) at p14703
  rcases p14703 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p19512))
theorem n19514 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e6583 _v) := by
  have p19513 := n19513 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p10893 := n10893 _v _q 
  have p11376 := n11376 _v _q 
  have p5255 := n5255 _v _q 
  have p8663 := n8663 _v _q 
  exact FloorCertificate.node_19514 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p19513 p10893 p11376 p5255 p8663
theorem n19515 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e8157 _v) := by
  have p14632 := n14632 _v _q 
  have p19514 := n19514 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (e2364 _v) ∨ (¬ (e8149 _v)) at p14632
  change (¬ (e2364 _v)) at p19514
  rcases p14632 with hlit | hlit
  · exact (False.elim (p19514 hlit))
  · exact hlit
theorem n19516 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e6784 _v) := by
  have p5255 := n5255 _v _q 
  have p19513 := n19513 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p11376 := n11376 _v _q 
  have p8663 := n8663 _v _q 
  have p10893 := n10893 _v _q 
  exact FloorCertificate.node_19516 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p5255 p19513 p11376 p8663 p10893
theorem n19517 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e8375 _v) := by
  have p14675 := n14675 _v _q 
  have p19516 := n19516 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (e2793 _v) ∨ (¬ (e8367 _v)) at p14675
  change (¬ (e2793 _v)) at p19516
  rcases p14675 with hlit | hlit
  · exact (False.elim (p19516 hlit))
  · exact hlit
theorem n19518 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e6423 _v) := by
  have p10893 := n10893 _v _q 
  have p19513 := n19513 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p11375 := n11375 _v _q 
  exact FloorCertificate.node_19518 (e2 _v) (e7 _v) (e17 _v) (e45 _v) (e110 _v) p10893 p19513 p11375
theorem n19519 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e8060 _v) := by
  have p14622 := n14622 _v _q 
  have p19518 := n19518 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (e1995 _v) ∨ (¬ (e8052 _v)) at p14622
  change (¬ (e1995 _v)) at p19518
  rcases p14622 with hlit | hlit
  · exact (False.elim (p19518 hlit))
  · exact hlit
theorem n19520 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e2475 _v) := by
  have p19513 := n19513 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p11375 := n11375 _v _q 
  have p8663 := n8663 _v _q 
  exact FloorCertificate.node_19520 (e2 _v) (e7 _v) (e17 _v) (e45 _v) (e110 _v) p19513 p11375 p8663
theorem n19521 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e8035 _v) := by
  have p14871 := n14871 _v _q 
  have p19520 := n19520 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (¬ (e2475 _v)) ∨ (¬ (e8029 _v)) at p14871
  rcases p14871 with hlit | hlit
  · exact (False.elim (hlit p19520))
  · exact hlit
theorem n19522 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e2132 _v) := by
  have p19513 := n19513 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p10893 := n10893 _v _q 
  have p8663 := n8663 _v _q 
  exact FloorCertificate.node_19522 (e2 _v) (e7 _v) (e17 _v) (e45 _v) (e110 _v) p19513 p10893 p8663
theorem n19523 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e6676 _v) := by
  have p19513 := n19513 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p8663 := n8663 _v _q 
  have p11375 := n11375 _v _q 
  have p10893 := n10893 _v _q 
  have p11376 := n11376 _v _q 
  exact FloorCertificate.node_19523 (e2 _v) (e7 _v) (e17 _v) (e45 _v) (e110 _v) p19513 p8663 p11375 p10893 p11376
theorem n19524 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e7830 _v) := by
  have p14579 := n14579 _v _q 
  have p19523 := n19523 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (e2585 _v) ∨ (¬ (e7822 _v)) at p14579
  change (¬ (e2585 _v)) at p19523
  rcases p14579 with hlit | hlit
  · exact (False.elim (p19523 hlit))
  · exact hlit
theorem n19525 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e6656 _v) := by
  have p19513 := n19513 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p11376 := n11376 _v _q 
  exact FloorCertificate.node_19525 (e2 _v) (e7 _v) (e17 _v) (e45 _v) (e110 _v) p19513 p11376
theorem n19526 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e7170 _v) := by
  have p14427 := n14427 _v _q 
  have p19525 := n19525 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (e2536 _v) ∨ (¬ (e7169 _v)) at p14427
  change (¬ (e2536 _v)) at p19525
  rcases p14427 with hlit | hlit
  · exact (False.elim (p19525 hlit))
  · exact hlit
theorem n19527 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e2592 _v) := by
  have p19513 := n19513 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p8663 := n8663 _v _q 
  exact FloorCertificate.node_19527 (e2 _v) (e7 _v) (e17 _v) (e45 _v) (e110 _v) p19513 p8663
theorem n19528 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e8330 _v) := by
  have p14907 := n14907 _v _q 
  have p19527 := n19527 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (¬ (e2592 _v)) ∨ (¬ (e8324 _v)) at p14907
  rcases p14907 with hlit | hlit
  · exact (False.elim (hlit p19527))
  · exact hlit
theorem n19529 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e13 _v) := by
  have p5255 := n5255 _v _q 
  have p19513 := n19513 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p10893 := n10893 _v _q 
  have p8663 := n8663 _v _q 
  exact FloorCertificate.node_19529 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p5255 p19513 p10893 p8663
theorem n19530 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e5090 _v) := by
  have p14728 := n14728 _v _q 
  have p19529 := n19529 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (¬ (e13 _v)) ∨ (¬ (e5089 _v)) at p14728
  rcases p14728 with hlit | hlit
  · exact (False.elim (hlit p19529))
  · exact hlit
theorem n19531 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e6732 _v) := by
  have p5255 := n5255 _v _q 
  have p19513 := n19513 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  exact FloorCertificate.node_19531 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p5255 p19513
theorem n19532 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e7992 _v) := by
  have p14606 := n14606 _v _q 
  have p19531 := n19531 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (e2697 _v) ∨ (¬ (e7984 _v)) at p14606
  change (¬ (e2697 _v)) at p19531
  rcases p14606 with hlit | hlit
  · exact (False.elim (p19531 hlit))
  · exact hlit
theorem n19533 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e6700 _v) := by
  have p5255 := n5255 _v _q 
  have p11376 := n11376 _v _q 
  have p19513 := n19513 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  exact FloorCertificate.node_19533 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p5255 p11376 p19513
theorem n19534 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e6896 _v) := by
  have p14360 := n14360 _v _q 
  have p19533 := n19533 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (e2634 _v) ∨ (¬ (e6888 _v)) at p14360
  change (¬ (e2634 _v)) at p19533
  rcases p14360 with hlit | hlit
  · exact (False.elim (p19533 hlit))
  · exact hlit
theorem n19535 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e6486 _v) := by
  have p10893 := n10893 _v _q 
  have p19513 := n19513 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  exact FloorCertificate.node_19535 (e2 _v) (e7 _v) (e17 _v) (e45 _v) (e110 _v) p10893 p19513
theorem n19536 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e6555 _v) := by
  have p11062 := n11062 _v _q 
  have p19535 := n19535 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (e2139 _v) ∨ (¬ (e2310 _v)) at p11062
  change (¬ (e2139 _v)) at p19535
  rcases p11062 with hlit | hlit
  · exact (False.elim (p19535 hlit))
  · exact hlit
theorem n19537 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e7554 _v) := by
  have p14515 := n14515 _v _q 
  have p19513 := n19513 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (e2598 _v) ∨ (¬ (e7546 _v)) at p14515
  change (¬ (e2598 _v)) at p19513
  rcases p14515 with hlit | hlit
  · exact (False.elim (p19513 hlit))
  · exact hlit
theorem n19538 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e4054 _v) := by
  have p15495 := n15495 _v _q 
  have p19537 := n19537 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (e7546 _v) ∨ (e4054 _v) at p15495
  change (¬ (e7546 _v)) at p19537
  rcases p15495 with hlit | hlit
  · exact (False.elim (p19537 hlit))
  · exact hlit
theorem n19539 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e6636 _v) := by
  have p19513 := n19513 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p11375 := n11375 _v _q 
  exact FloorCertificate.node_19539 (e2 _v) (e7 _v) (e17 _v) (e45 _v) (e110 _v) p19513 p11375
theorem n19540 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e7912 _v) := by
  have p14591 := n14591 _v _q 
  have p19539 := n19539 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (e2482 _v) ∨ (¬ (e7904 _v)) at p14591
  change (¬ (e2482 _v)) at p19539
  rcases p14591 with hlit | hlit
  · exact (False.elim (p19539 hlit))
  · exact hlit
theorem n19541 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e6531 _v) := by
  have p10893 := n10893 _v _q 
  have p19513 := n19513 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p5255 := n5255 _v _q 
  exact FloorCertificate.node_19541 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p10893 p19513 p5255
theorem n19542 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e8214 _v) := by
  have p14642 := n14642 _v _q 
  have p19541 := n19541 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (e2254 _v) ∨ (¬ (e8206 _v)) at p14642
  change (¬ (e2254 _v)) at p19541
  rcases p14642 with hlit | hlit
  · exact (False.elim (p19541 hlit))
  · exact hlit
theorem n19543 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e4648 _v) := by
  have p15027 := n15027 _v _q 
  have p19515 := n19515 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (e8149 _v) ∨ (e4648 _v) at p15027
  change (¬ (e8149 _v)) at p19515
  rcases p15027 with hlit | hlit
  · exact (False.elim (p19515 hlit))
  · exact hlit
theorem n19544 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e4899 _v) := by
  have p15064 := n15064 _v _q 
  have p19517 := n19517 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (e8367 _v) ∨ (e4899 _v) at p15064
  change (¬ (e8367 _v)) at p19517
  rcases p15064 with hlit | hlit
  · exact (False.elim (p19517 hlit))
  · exact hlit
theorem n19545 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e4562 _v) := by
  have p15155 := n15155 _v _q 
  have p19519 := n19519 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (e8052 _v) ∨ (e4562 _v) at p15155
  change (¬ (e8052 _v)) at p19519
  rcases p15155 with hlit | hlit
  · exact (False.elim (p19519 hlit))
  · exact hlit
end
end Assembly
