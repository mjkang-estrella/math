import Dag213
import generated.th_lemma_26
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n19594 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4302 : (e4302 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e7489 _v) := by
  have p19593 := n19593 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h4096 h4156 h4199 h4260 h4302 h4369 h4419 h4434 h4608 h4675 h4787 h4813 h4872
  have p5391 := n5391 _v _q 
  have p17010 := n17010 _v _q h4302 h4419 h4434
  exact FloorCertificate.node_19594 (e2 _v) (e9 _v) (e45 _v) (e110 _v) p19593 p5391 p17010
theorem n19595 (_v : Vars) (_q : Query _v)  : (e8531 _v) := by
  by_contra hc
  change ¬ ((¬ (e4419 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e91 _v)) ∨ (e4301 _v)) at hc
  have h70 : (e70 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))
  have h225 : (e225 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h442 : (e442 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h488 : (e488 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h3069 : (e3069 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))
  have h3105 : (e3105 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))
  have h4096 : (e4096 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))
  have h4156 : (e4156 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h4199 : (e4199 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4260 : (e4260 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h4302 : (e4302 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))))))))))))))))))
  have h4369 : (e4369 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h4419 : (e4419 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h4434 : (e4434 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h4608 : (e4608 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))
  have h4675 : (e4675 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h4872 : (e4872 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))
  have p19594 := n19594 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h4096 h4156 h4199 h4260 h4302 h4369 h4419 h4434 h4608 h4675 h4787 h4813 h4872
  exact p19594
theorem n19596 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h6784 : (e6784 _v)) : (e6772 _v) := by
  have p14855 := n14855 _v _q 
  have p19585 := n19585 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4260 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4838 h4872 h6784
  change (¬ (e2787 _v)) ∨ (¬ (e7921 _v)) at p14855
  rcases p14855 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p19585))
theorem n19597 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h6784 : (e6784 _v)) : (e7489 _v) := by
  have p11473 := n11473 _v _q h6784
  have p8663 := n8663 _v _q 
  have p19596 := n19596 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4260 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4838 h4872 h6784
  exact FloorCertificate.node_19597 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p11473 p8663 p19596
theorem n19599 (_v : Vars) (_q : Query _v)  : (e19598 _v) := by
  by_contra hc
  change ¬ ((e2793 _v) ∨ (¬ (e3152 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e91 _v))) at hc
  have h70 : (e70 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn)))))))))))))))))))))))))
  have h191 : (e191 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))
  have h225 : (e225 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h442 : (e442 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))
  have h488 : (e488 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h3069 : (e3069 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))
  have h3105 : (e3105 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))
  have h3946 : (e3946 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h4096 : (e4096 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))
  have h4156 : (e4156 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h4199 : (e4199 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4260 : (e4260 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h4369 : (e4369 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h4434 : (e4434 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h4608 : (e4608 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))
  have h4675 : (e4675 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4747 : (e4747 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))
  have h4838 : (e4838 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h4872 : (e4872 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))
  have h6784 : (e6784 _v) := (fun hn => hc (Or.inl hn))
  have p19597 := n19597 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4260 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4838 h4872 h6784
  exact p19597
theorem n19600 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h6531 : (e6531 _v)) : (e6772 _v) := by
  have p14855 := n14855 _v _q 
  have p19587 := n19587 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4260 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872 h6531
  change (¬ (e2787 _v)) ∨ (¬ (e7921 _v)) at p14855
  rcases p14855 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p19587))
theorem n19601 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h6531 : (e6531 _v)) : (e7489 _v) := by
  have p11358 := n11358 _v _q h6531
  have p5391 := n5391 _v _q 
  have p5257 := n5257 _v _q 
  have p19600 := n19600 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4260 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872 h6531
  have p8663 := n8663 _v _q 
  exact FloorCertificate.node_19601 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p11358 p5391 p5257 p19600 p8663
theorem n19603 (_v : Vars) (_q : Query _v)  : (e19602 _v) := by
  by_contra hc
  change ¬ ((e2254 _v) ∨ (¬ (e3152 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e91 _v))) at hc
  have h70 : (e70 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn)))))))))))))))))))))))
  have h225 : (e225 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h442 : (e442 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))
  have h488 : (e488 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h3069 : (e3069 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))
  have h3105 : (e3105 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))
  have h3946 : (e3946 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h4096 : (e4096 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))
  have h4156 : (e4156 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h4199 : (e4199 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4260 : (e4260 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h4369 : (e4369 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h4434 : (e4434 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h4608 : (e4608 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))
  have h4675 : (e4675 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4747 : (e4747 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))
  have h4872 : (e4872 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))
  have h6531 : (e6531 _v) := (fun hn => hc (Or.inl hn))
  have p19601 := n19601 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4260 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872 h6531
  exact p19601
theorem n19604 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2132 : (e2132 _v)) (h2529 : (e2529 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e6772 _v) := by
  have p14855 := n14855 _v _q 
  have p19589 := n19589 _v _q h70 h91 h191 h225 h442 h488 h2132 h2529 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4260 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  change (¬ (e2787 _v)) ∨ (¬ (e7921 _v)) at p14855
  rcases p14855 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p19589))
theorem n19605 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2132 : (e2132 _v)) (h2529 : (e2529 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e7489 _v) := by
  have p19604 := n19604 _v _q h70 h91 h191 h225 h442 h488 h2132 h2529 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4260 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  have p11349 := n11349 _v _q h2132
  have p8548 := n8548 _v _q h2529
  have p5255 := n5255 _v _q 
  exact FloorCertificate.node_19605 (e2 _v) (e7 _v) (e9 _v) (e45 _v) (e110 _v) p19604 p11349 p8548 p5255
theorem n19607 (_v : Vars) (_q : Query _v)  : (e19606 _v) := by
  by_contra hc
  change ¬ ((¬ (e2132 _v)) ∨ (¬ (e2529 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e91 _v))) at hc
  have h70 : (e70 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn)))))))))))))))))))))))))
  have h191 : (e191 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))
  have h225 : (e225 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h442 : (e442 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))
  have h488 : (e488 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h2132 : (e2132 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h2529 : (e2529 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h3069 : (e3069 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))
  have h3105 : (e3105 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))
  have h3946 : (e3946 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h4096 : (e4096 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))
  have h4156 : (e4156 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h4199 : (e4199 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4260 : (e4260 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h4369 : (e4369 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h4434 : (e4434 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h4608 : (e4608 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))
  have h4675 : (e4675 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h4747 : (e4747 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))
  have h4872 : (e4872 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))
  have p19605 := n19605 _v _q h70 h91 h191 h225 h442 h488 h2132 h2529 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4260 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  exact p19605
theorem n19608 (_v : Vars) (_q : Query _v) (h2722 : (e2722 _v)) : (e4459 _v) := by
  have p8443 := n8443 _v _q 
  have p17693 := n17693 _v _q h2722
  change (e4465 _v) ∨ (e4459 _v) at p8443
  change (¬ (e4465 _v)) at p17693
  rcases p8443 with hlit | hlit
  · exact (False.elim (p17693 hlit))
  · exact hlit
theorem n19609 (_v : Vars) (_q : Query _v) (h2722 : (e2722 _v)) : (e4653 _v) := by
  have p15168 := n15168 _v _q 
  have p17695 := n17695 _v _q h2722
  change (e4660 _v) ∨ (e4653 _v) at p15168
  change (¬ (e4660 _v)) at p17695
  rcases p15168 with hlit | hlit
  · exact (False.elim (p17695 hlit))
  · exact hlit
theorem n19610 (_v : Vars) (_q : Query _v)  : (e4059 _v) := by
  have p14980 := n14980 _v _q 
  have p19592 := n19592 _v _q 
  change (e4066 _v) ∨ (e4059 _v) at p14980
  change (¬ (e4066 _v)) at p19592
  rcases p14980 with hlit | hlit
  · exact (False.elim (p19592 hlit))
  · exact hlit
theorem n19611 (_v : Vars) (_q : Query _v) (h2722 : (e2722 _v)) : (e3919 _v) := by
  have p14797 := n14797 _v _q 
  have p17722 := n17722 _v _q h2722
  change (e3923 _v) ∨ (e3919 _v) at p14797
  change (¬ (e3923 _v)) at p17722
  rcases p14797 with hlit | hlit
  · exact (False.elim (p17722 hlit))
  · exact hlit
theorem n19612 (_v : Vars) (_q : Query _v) (h2722 : (e2722 _v)) : (e51 _v) := by
  have p14962 := n14962 _v _q 
  have p17724 := n17724 _v _q h2722
  change (e59 _v) ∨ (e51 _v) at p14962
  change (¬ (e59 _v)) at p17724
  rcases p14962 with hlit | hlit
  · exact (False.elim (p17724 hlit))
  · exact hlit
theorem n19613 (_v : Vars) (_q : Query _v) (h2722 : (e2722 _v)) : (e3133 _v) := by
  have p15098 := n15098 _v _q 
  have p17726 := n17726 _v _q h2722
  change (e3139 _v) ∨ (e3133 _v) at p15098
  change (¬ (e3139 _v)) at p17726
  rcases p15098 with hlit | hlit
  · exact (False.elim (p17726 hlit))
  · exact hlit
theorem n19614 (_v : Vars) (_q : Query _v) (h2722 : (e2722 _v)) : (e4491 _v) := by
  have p14969 := n14969 _v _q 
  have p17728 := n17728 _v _q h2722
  change (e4498 _v) ∨ (e4491 _v) at p14969
  change (¬ (e4498 _v)) at p17728
  rcases p14969 with hlit | hlit
  · exact (False.elim (p17728 hlit))
  · exact hlit
theorem n19615 (_v : Vars) (_q : Query _v) (h2722 : (e2722 _v)) : (e4724 _v) := by
  have p15518 := n15518 _v _q 
  have p17730 := n17730 _v _q h2722
  change (e4730 _v) ∨ (e4724 _v) at p15518
  change (¬ (e4730 _v)) at p17730
  rcases p15518 with hlit | hlit
  · exact (False.elim (p17730 hlit))
  · exact hlit
theorem n19616 (_v : Vars) (_q : Query _v) (h2722 : (e2722 _v)) : (e4567 _v) := by
  have p8485 := n8485 _v _q 
  have p17732 := n17732 _v _q h2722
  change (e4574 _v) ∨ (e4567 _v) at p8485
  change (¬ (e4574 _v)) at p17732
  rcases p8485 with hlit | hlit
  · exact (False.elim (p17732 hlit))
  · exact hlit
theorem n19617 (_v : Vars) (_q : Query _v) (h2722 : (e2722 _v)) : (e4791 _v) := by
  have p14932 := n14932 _v _q 
  have p17734 := n17734 _v _q h2722
  change (e4797 _v) ∨ (e4791 _v) at p14932
  change (¬ (e4797 _v)) at p17734
  rcases p14932 with hlit | hlit
  · exact (False.elim (p17734 hlit))
  · exact hlit
theorem n19618 (_v : Vars) (_q : Query _v) (h2722 : (e2722 _v)) : (e4398 _v) := by
  have p14976 := n14976 _v _q 
  have p17736 := n17736 _v _q h2722
  change (e4404 _v) ∨ (e4398 _v) at p14976
  change (¬ (e4404 _v)) at p17736
  rcases p14976 with hlit | hlit
  · exact (False.elim (p17736 hlit))
  · exact hlit
theorem n19619 (_v : Vars) (_q : Query _v) (h2722 : (e2722 _v)) : (e4679 _v) := by
  have p14989 := n14989 _v _q 
  have p17738 := n17738 _v _q h2722
  change (e4685 _v) ∨ (e4679 _v) at p14989
  change (¬ (e4685 _v)) at p17738
  rcases p14989 with hlit | hlit
  · exact (False.elim (p17738 hlit))
  · exact hlit
theorem n19620 (_v : Vars) (_q : Query _v) (h2722 : (e2722 _v)) : (e4817 _v) := by
  have p15123 := n15123 _v _q 
  have p17740 := n17740 _v _q h2722
  change (e4823 _v) ∨ (e4817 _v) at p15123
  change (¬ (e4823 _v)) at p17740
  rcases p15123 with hlit | hlit
  · exact (False.elim (p17740 hlit))
  · exact hlit
theorem n19621 (_v : Vars) (_q : Query _v) (h2722 : (e2722 _v)) : (e4264 _v) := by
  have p14966 := n14966 _v _q 
  have p17742 := n17742 _v _q h2722
  change (e4270 _v) ∨ (e4264 _v) at p14966
  change (¬ (e4270 _v)) at p17742
  rcases p14966 with hlit | hlit
  · exact (False.elim (p17742 hlit))
  · exact hlit
theorem n19622 (_v : Vars) (_q : Query _v) (h2722 : (e2722 _v)) : (e5195 _v) := by
  have p8410 := n8410 _v _q h2722
  have p5257 := n5257 _v _q 
  have p5255 := n5255 _v _q 
  have p258 := n258 _v _q 
  exact FloorCertificate.node_19622 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8410 p5257 p5255 p258
theorem n19623 (_v : Vars) (_q : Query _v) (h2722 : (e2722 _v)) : (e4101 _v) := by
  have p14929 := n14929 _v _q 
  have p17744 := n17744 _v _q h2722
  change (e4108 _v) ∨ (e4101 _v) at p14929
  change (¬ (e4108 _v)) at p17744
  rcases p14929 with hlit | hlit
  · exact (False.elim (p17744 hlit))
  · exact hlit
theorem n19624 (_v : Vars) (_q : Query _v) (h2722 : (e2722 _v)) : (e4903 _v) := by
  have p14973 := n14973 _v _q 
  have p17746 := n17746 _v _q h2722
  change (e4909 _v) ∨ (e4903 _v) at p14973
  change (¬ (e4909 _v)) at p17746
  rcases p14973 with hlit | hlit
  · exact (False.elim (p17746 hlit))
  · exact hlit
theorem n19625 (_v : Vars) (_q : Query _v) (h2722 : (e2722 _v)) : (e4439 _v) := by
  have p14925 := n14925 _v _q 
  have p17748 := n17748 _v _q h2722
  change (e4446 _v) ∨ (e4439 _v) at p14925
  change (¬ (e4446 _v)) at p17748
  rcases p14925 with hlit | hlit
  · exact (False.elim (p17748 hlit))
  · exact hlit
theorem n19626 (_v : Vars) (_q : Query _v) (h2722 : (e2722 _v)) : (e3976 _v) := by
  have p14935 := n14935 _v _q 
  have p17750 := n17750 _v _q h2722
  change (e3983 _v) ∨ (e3976 _v) at p14935
  change (¬ (e3983 _v)) at p17750
  rcases p14935 with hlit | hlit
  · exact (False.elim (p17750 hlit))
  · exact hlit
theorem n19627 (_v : Vars) (_q : Query _v) (h2722 : (e2722 _v)) : (e3158 _v) := by
  have p15126 := n15126 _v _q 
  have p17752 := n17752 _v _q h2722
  change (e3162 _v) ∨ (e3158 _v) at p15126
  change (¬ (e3162 _v)) at p17752
  rcases p15126 with hlit | hlit
  · exact (False.elim (p17752 hlit))
  · exact hlit
theorem n19628 (_v : Vars) (_q : Query _v) (h2722 : (e2722 _v)) : (e4306 _v) := by
  have p14984 := n14984 _v _q 
  have p17754 := n17754 _v _q h2722
  change (e4313 _v) ∨ (e4306 _v) at p14984
  change (¬ (e4313 _v)) at p17754
  rcases p14984 with hlit | hlit
  · exact (False.elim (p17754 hlit))
  · exact hlit
theorem n19629 (_v : Vars) (_q : Query _v) (h2722 : (e2722 _v)) : (e7489 _v) := by
  have p18064 := n18064 _v _q 
  have p15151 := n15151 _v _q h2722
  have p19608 := n19608 _v _q h2722
  have p8410 := n8410 _v _q h2722
  have p19609 := n19609 _v _q h2722
  have p19610 := n19610 _v _q 
  have p19611 := n19611 _v _q h2722
  have p19612 := n19612 _v _q h2722
  have p19613 := n19613 _v _q h2722
  have p19614 := n19614 _v _q h2722
  have p19615 := n19615 _v _q h2722
  have p19616 := n19616 _v _q h2722
  have p19617 := n19617 _v _q h2722
  have p19618 := n19618 _v _q h2722
  have p19619 := n19619 _v _q h2722
  have p19620 := n19620 _v _q h2722
  have p19621 := n19621 _v _q h2722
  have p19622 := n19622 _v _q h2722
  have p19623 := n19623 _v _q h2722
  have p19624 := n19624 _v _q h2722
  have p19625 := n19625 _v _q h2722
  have p19626 := n19626 _v _q h2722
  have p19627 := n19627 _v _q h2722
  have p19628 := n19628 _v _q h2722
  change (¬ (e4161 _v)) ∨ (¬ (e2722 _v)) ∨ (¬ (e4459 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e3919 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e3133 _v)) ∨ (¬ (e4491 _v)) ∨ (¬ (e4724 _v)) ∨ (¬ (e4567 _v)) ∨ (¬ (e4791 _v)) ∨ (¬ (e4398 _v)) ∨ (¬ (e4679 _v)) ∨ (¬ (e4817 _v)) ∨ (¬ (e4264 _v)) ∨ (e196 _v) ∨ (¬ (e4101 _v)) ∨ (¬ (e4903 _v)) ∨ (¬ (e4439 _v)) ∨ (¬ (e3976 _v)) ∨ (¬ (e3158 _v)) ∨ (¬ (e4306 _v)) at p18064
  change (¬ (e196 _v)) at p19622
  rcases p18064 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact (False.elim (hlit p15151))
  · exact (False.elim (hlit p8410))
  · exact (False.elim (hlit p19608))
  · exact (False.elim (hlit p19609))
  · exact (False.elim (hlit p19610))
  · exact (False.elim (hlit p19611))
  · exact (False.elim (hlit p19612))
  · exact (False.elim (hlit p19613))
  · exact (False.elim (hlit p19614))
  · exact (False.elim (hlit p19615))
  · exact (False.elim (hlit p19616))
  · exact (False.elim (hlit p19617))
  · exact (False.elim (hlit p19618))
  · exact (False.elim (hlit p19619))
  · exact (False.elim (hlit p19620))
  · exact (False.elim (hlit p19621))
  · exact (False.elim (p19622 hlit))
  · exact (False.elim (hlit p19623))
  · exact (False.elim (hlit p19624))
  · exact (False.elim (hlit p19625))
  · exact (False.elim (hlit p19626))
  · exact (False.elim (hlit p19627))
  · exact (False.elim (hlit p19628))
theorem n19630 (_v : Vars) (_q : Query _v)  : (e6742 _v) := by
  by_contra hc
  change ¬ (¬ (e2722 _v)) at hc
  have h2722 : (e2722 _v) := Classical.byContradiction (fun hn => hc hn)
  have p19629 := n19629 _v _q h2722
  exact p19629
theorem n19631 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4302 : (e4302 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e4420 _v) := by
  have p19595 := n19595 _v _q 
  have p15577 := n15577 _v _q h4302
  have p5008 := n5008 _v _q h4787
  have p5003 := n5003 _v _q h4199
  have p5006 := n5006 _v _q h4675
  have p4995 := n4995 _v _q h4369
  have p5007 := n5007 _v _q h225
  have p4985 := n4985 _v _q h4156
  have p4987 := n4987 _v _q h4434
  have p5010 := n5010 _v _q h70
  have p4981 := n4981 _v _q h4260
  have p4988 := n4988 _v _q h488
  have p4986 := n4986 _v _q h3105
  have p4983 := n4983 _v _q h4813
  have p4992 := n4992 _v _q h442
  have p4984 := n4984 _v _q h4872
  have p4991 := n4991 _v _q h4608
  have p4994 := n4994 _v _q h3069
  have p5001 := n5001 _v _q h4096
  have p4996 := n4996 _v _q h3937
  have p4999 := n4999 _v _q h91
  have p4998 := n4998 _v _q h3152
  change (¬ (e4419 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e91 _v)) ∨ (e4301 _v) at p19595
  change (¬ (e4301 _v)) at p15577
  rcases p19595 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p5003))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p4995))
  · exact (False.elim (hlit p5007))
  · exact (False.elim (hlit p4985))
  · exact (False.elim (hlit p4987))
  · exact (False.elim (hlit p5010))
  · exact (False.elim (hlit p4981))
  · exact (False.elim (hlit p4988))
  · exact (False.elim (hlit p4986))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p4992))
  · exact (False.elim (hlit p4984))
  · exact (False.elim (hlit p4991))
  · exact (False.elim (hlit p4994))
  · exact (False.elim (hlit p5001))
  · exact (False.elim (hlit p4996))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (p15577 hlit))
theorem n19632 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4302 : (e4302 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e7921 _v) := by
  have p16347 := n16347 _v _q 
  have p19631 := n19631 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h4096 h4156 h4199 h4260 h4302 h4369 h4434 h4608 h4675 h4787 h4813 h4872
  change (e7921 _v) ∨ (e4419 _v) at p16347
  change (¬ (e4419 _v)) at p19631
  rcases p16347 with hlit | hlit
  · exact hlit
  · exact (False.elim (p19631 hlit))
theorem n19633 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4302 : (e4302 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e6772 _v) := by
  have p14855 := n14855 _v _q 
  have p19632 := n19632 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h4096 h4156 h4199 h4260 h4302 h4369 h4434 h4608 h4675 h4787 h4813 h4872
  change (¬ (e2787 _v)) ∨ (¬ (e7921 _v)) at p14855
  rcases p14855 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p19632))
theorem n19634 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h6784 : (e6784 _v)) : (e4839 _v) := by
  have p19599 := n19599 _v _q 
  have p11473 := n11473 _v _q h6784
  have p5008 := n5008 _v _q h4787
  have p5003 := n5003 _v _q h4199
  have p5006 := n5006 _v _q h4675
  have p4995 := n4995 _v _q h4369
  have p5007 := n5007 _v _q h225
  have p4985 := n4985 _v _q h4156
  have p4987 := n4987 _v _q h4434
  have p5010 := n5010 _v _q h70
  have p4981 := n4981 _v _q h4260
  have p4988 := n4988 _v _q h488
  have p17061 := n17061 _v _q h4747
  have p17056 := n17056 _v _q h3946
  have p4998 := n4998 _v _q h3152
  have p4986 := n4986 _v _q h3105
  have p4983 := n4983 _v _q h4813
  have p4992 := n4992 _v _q h442
  have p4984 := n4984 _v _q h4872
  have p4991 := n4991 _v _q h4608
  have p253 := n253 _v _q h191
  have p4994 := n4994 _v _q h3069
  have p5001 := n5001 _v _q h4096
  have p4996 := n4996 _v _q h3937
  have p4999 := n4999 _v _q h91
  change (e2793 _v) ∨ (¬ (e3152 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e91 _v)) at p19599
  change (¬ (e2793 _v)) at p11473
  rcases p19599 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact (False.elim (p11473 hlit))
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p5003))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p4995))
  · exact (False.elim (hlit p5007))
  · exact (False.elim (hlit p4985))
  · exact (False.elim (hlit p4987))
  · exact (False.elim (hlit p5010))
  · exact (False.elim (hlit p4981))
  · exact (False.elim (hlit p4988))
  · exact (False.elim (hlit p17061))
  · exact (False.elim (hlit p17056))
  · exact hlit
  · exact (False.elim (hlit p4986))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p4992))
  · exact (False.elim (hlit p4984))
  · exact (False.elim (hlit p4991))
  · exact (False.elim (hlit p253))
  · exact (False.elim (hlit p4994))
  · exact (False.elim (hlit p5001))
  · exact (False.elim (hlit p4996))
  · exact (False.elim (hlit p4999))
theorem n19635 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h6784 : (e6784 _v)) : (e8301 _v) := by
  have p16285 := n16285 _v _q 
  have p19634 := n19634 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4260 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872 h6784
  change (e8301 _v) ∨ (e4838 _v) at p16285
  change (¬ (e4838 _v)) at p19634
  rcases p16285 with hlit | hlit
  · exact hlit
  · exact (False.elim (p19634 hlit))
theorem n19636 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e2254 _v) := by
  have p19603 := n19603 _v _q 
  have p5003 := n5003 _v _q h4199
  have p5008 := n5008 _v _q h4787
  have p4998 := n4998 _v _q h3152
  have p5006 := n5006 _v _q h4675
  have p4995 := n4995 _v _q h4369
  have p5007 := n5007 _v _q h225
  have p4985 := n4985 _v _q h4156
  have p4987 := n4987 _v _q h4434
  have p5010 := n5010 _v _q h70
  have p4981 := n4981 _v _q h4260
  have p4988 := n4988 _v _q h488
  have p17061 := n17061 _v _q h4747
  have p17056 := n17056 _v _q h3946
  have p4986 := n4986 _v _q h3105
  have p4983 := n4983 _v _q h4813
  have p4992 := n4992 _v _q h442
  have p4984 := n4984 _v _q h4872
  have p4991 := n4991 _v _q h4608
  have p4994 := n4994 _v _q h3069
  have p5001 := n5001 _v _q h4096
  have p4996 := n4996 _v _q h3937
  have p4999 := n4999 _v _q h91
  change (e2254 _v) ∨ (¬ (e3152 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e91 _v)) at p19603
  rcases p19603 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p5003))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p4995))
  · exact (False.elim (hlit p5007))
  · exact (False.elim (hlit p4985))
  · exact (False.elim (hlit p4987))
  · exact (False.elim (hlit p5010))
  · exact (False.elim (hlit p4981))
  · exact (False.elim (hlit p4988))
  · exact (False.elim (hlit p17061))
  · exact (False.elim (hlit p17056))
  · exact (False.elim (hlit p4986))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p4992))
  · exact (False.elim (hlit p4984))
  · exact (False.elim (hlit p4991))
  · exact (False.elim (hlit p4994))
  · exact (False.elim (hlit p5001))
  · exact (False.elim (hlit p4996))
  · exact (False.elim (hlit p4999))
theorem n19637 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h6636 : (e6636 _v)) : (e2793 _v) := by
  have p19599 := n19599 _v _q 
  have p16554 := n16554 _v _q h6636
  have p5008 := n5008 _v _q h4787
  have p5003 := n5003 _v _q h4199
  have p5006 := n5006 _v _q h4675
  have p4995 := n4995 _v _q h4369
  have p5007 := n5007 _v _q h225
  have p4985 := n4985 _v _q h4156
  have p4987 := n4987 _v _q h4434
  have p5010 := n5010 _v _q h70
  have p4981 := n4981 _v _q h4260
  have p4988 := n4988 _v _q h488
  have p17061 := n17061 _v _q h4747
  have p17056 := n17056 _v _q h3946
  have p4998 := n4998 _v _q h3152
  have p4986 := n4986 _v _q h3105
  have p4983 := n4983 _v _q h4813
  have p4992 := n4992 _v _q h442
  have p4984 := n4984 _v _q h4872
  have p4991 := n4991 _v _q h4608
  have p16552 := n16552 _v _q h6636
  have p4994 := n4994 _v _q h3069
  have p5001 := n5001 _v _q h4096
  have p4996 := n4996 _v _q h3937
  have p4999 := n4999 _v _q h91
  change (e2793 _v) ∨ (¬ (e3152 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e91 _v)) at p19599
  rcases p19599 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p5003))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p4995))
  · exact (False.elim (hlit p5007))
  · exact (False.elim (hlit p4985))
  · exact (False.elim (hlit p4987))
  · exact (False.elim (hlit p5010))
  · exact (False.elim (hlit p4981))
  · exact (False.elim (hlit p4988))
  · exact (False.elim (hlit p17061))
  · exact (False.elim (hlit p17056))
  · exact (False.elim (hlit p16554))
  · exact (False.elim (hlit p4986))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p4992))
  · exact (False.elim (hlit p4984))
  · exact (False.elim (hlit p4991))
  · exact (False.elim (hlit p16552))
  · exact (False.elim (hlit p4994))
  · exact (False.elim (hlit p5001))
  · exact (False.elim (hlit p4996))
  · exact (False.elim (hlit p4999))
theorem n19638 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h6636 : (e6636 _v)) : (e4910 _v) := by
  have p14701 := n14701 _v _q 
  have p19637 := n19637 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4260 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872 h6636
  change (¬ (e2793 _v)) ∨ (¬ (e4909 _v)) at p14701
  rcases p14701 with hlit | hlit
  · exact (False.elim (hlit p19637))
  · exact hlit
theorem n19639 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e2254 _v) := by
  have p19603 := n19603 _v _q 
  have p4981 := n4981 _v _q h4260
  have p5008 := n5008 _v _q h4787
  have p4998 := n4998 _v _q h3152
  have p5006 := n5006 _v _q h4675
  have p4995 := n4995 _v _q h4369
  have p5007 := n5007 _v _q h225
  have p4985 := n4985 _v _q h4156
  have p4987 := n4987 _v _q h4434
  have p5003 := n5003 _v _q h4199
  have p5010 := n5010 _v _q h70
  have p4988 := n4988 _v _q h488
  have p17061 := n17061 _v _q h4747
  have p17056 := n17056 _v _q h3946
  have p4986 := n4986 _v _q h3105
  have p4983 := n4983 _v _q h4813
  have p4992 := n4992 _v _q h442
  have p4984 := n4984 _v _q h4872
  have p4991 := n4991 _v _q h4608
  have p4994 := n4994 _v _q h3069
  have p5001 := n5001 _v _q h4096
  have p4996 := n4996 _v _q h3937
  have p4999 := n4999 _v _q h91
  change (e2254 _v) ∨ (¬ (e3152 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e91 _v)) at p19603
  rcases p19603 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p5003))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p4995))
  · exact (False.elim (hlit p5007))
  · exact (False.elim (hlit p4985))
  · exact (False.elim (hlit p4987))
  · exact (False.elim (hlit p5010))
  · exact (False.elim (hlit p4981))
  · exact (False.elim (hlit p4988))
  · exact (False.elim (hlit p17061))
  · exact (False.elim (hlit p17056))
  · exact (False.elim (hlit p4986))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p4992))
  · exact (False.elim (hlit p4984))
  · exact (False.elim (hlit p4991))
  · exact (False.elim (hlit p4994))
  · exact (False.elim (hlit p5001))
  · exact (False.elim (hlit p4996))
  · exact (False.elim (hlit p4999))
theorem n19640 (_v : Vars) (_q : Query _v) (h2522 : (e2522 _v)) (h5362 : (e5362 _v)) : (e6549 _v) := by
  have p18232 := n18232 _v _q 
  have p12831 := n12831 _v _q h2522
  have p7488 := n7488 _v _q h5362
  have p17252 := n17252 _v _q h5362
  have p19630 := n19630 _v _q 
  change (e436 _v) ∨ (¬ (e2296 _v)) ∨ (¬ (e4264 _v)) ∨ (¬ (e2522 _v)) ∨ (e2722 _v) at p18232
  change (¬ (e436 _v)) at p7488
  change (¬ (e2722 _v)) at p19630
  rcases p18232 with hlit | hlit | hlit | hlit | hlit
  · exact (False.elim (p7488 hlit))
  · exact hlit
  · exact (False.elim (hlit p17252))
  · exact (False.elim (hlit p12831))
  · exact (False.elim (p19630 hlit))
theorem n19641 (_v : Vars) (_q : Query _v) (h2522 : (e2522 _v)) (h5362 : (e5362 _v)) : (e7489 _v) := by
  have p5391 := n5391 _v _q 
  have p19640 := n19640 _v _q h2522 h5362
  have p12831 := n12831 _v _q h2522
  exact FloorCertificate.node_19641 (e2 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p5391 p19640 p12831
end
end Assembly
