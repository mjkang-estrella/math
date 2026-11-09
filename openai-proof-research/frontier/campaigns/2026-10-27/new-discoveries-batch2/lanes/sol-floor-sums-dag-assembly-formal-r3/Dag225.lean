import Dag224
import generated.th_lemma_28
import generated.th_lemma_29
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n20128 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4306 : (e4306 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4434 : (e4434 _v)) (h4491 : (e4491 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5100 : (e5100 _v)) (h5208 : (e5208 _v)) (h6571 : (e6571 _v)) (h7807 : (e7807 _v)) (h8045 : (e8045 _v)) : (e2061 _v) := by
  have p20122 := n20122 _v _q 
  have p17143 := n17143 _v _q h4567
  have p4987 := n4987 _v _q h4434
  have p17786 := n17786 _v _q h7807
  have p4991 := n4991 _v _q h4608
  have p4999 := n4999 _v _q h91
  have p4996 := n4996 _v _q h3937
  have p5003 := n5003 _v _q h4199
  have p4998 := n4998 _v _q h3152
  have p17128 := n17128 _v _q h4491
  have p4983 := n4983 _v _q h4813
  have p5008 := n5008 _v _q h4787
  have p17129 := n17129 _v _q h4903
  have p17175 := n17175 _v _q h5208
  have p5006 := n5006 _v _q h4675
  have p17159 := n17159 _v _q h5100
  have p15373 := n15373 _v _q h7807
  have p17134 := n17134 _v _q h4398
  have p17157 := n17157 _v _q h8045
  have p17137 := n17137 _v _q h4059
  have p17138 := n17138 _v _q h4306
  have p5007 := n5007 _v _q h225
  have p4992 := n4992 _v _q h442
  have p4994 := n4994 _v _q h3069
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
  have p8447 := n8447 _v _q h6571
  change (e2061 _v) ∨ (¬ (e3069 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e7749 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4491 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4903 _v)) ∨ (¬ (e5208 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e5100 _v)) ∨ (¬ (e7814 _v)) ∨ (¬ (e4398 _v)) ∨ (¬ (e8045 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e4567 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e3976 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4724 _v)) ∨ (e2358 _v) at p20122
  change (¬ (e2358 _v)) at p8447
  rcases p20122 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p4994))
  · exact (False.elim (hlit p4987))
  · exact (False.elim (hlit p17786))
  · exact (False.elim (hlit p4991))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p4996))
  · exact (False.elim (hlit p5003))
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p17128))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p17129))
  · exact (False.elim (hlit p17175))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p17159))
  · exact (False.elim (hlit p15373))
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
  · exact (False.elim (p8447 hlit))
theorem n20129 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4306 : (e4306 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4434 : (e4434 _v)) (h4491 : (e4491 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5100 : (e5100 _v)) (h5208 : (e5208 _v)) (h6571 : (e6571 _v)) (h7807 : (e7807 _v)) (h8045 : (e8045 _v)) : (e4447 _v) := by
  have p14688 := n14688 _v _q 
  have p20128 := n20128 _v _q h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h3976 h4059 h4156 h4199 h4306 h4369 h4398 h4434 h4491 h4567 h4608 h4653 h4675 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h5208 h6571 h7807 h8045
  change (¬ (e2061 _v)) ∨ (¬ (e4446 _v)) at p14688
  rcases p14688 with hlit | hlit
  · exact (False.elim (hlit p20128))
  · exact hlit
theorem n20131 (_v : Vars) (_q : Query _v)  : (e20130 _v) := by
  by_contra hc
  change ¬ ((¬ (e4306 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e4567 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e8317 _v)) ∨ (¬ (e8045 _v)) ∨ (¬ (e3976 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e5100 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4903 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e4096 _v)) ∨ (e196 _v) ∨ (¬ (e70 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e7749 _v))) at hc
  have h70 : (e70 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h225 : (e225 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h442 : (e442 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h488 : (e488 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h3069 : (e3069 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))
  have h3105 : (e3105 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))
  have h3946 : (e3946 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h3976 : (e3976 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h4096 : (e4096 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))
  have h4156 : (e4156 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h4199 : (e4199 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h4369 : (e4369 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h4434 : (e4434 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))
  have h4567 : (e4567 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4608 : (e4608 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))
  have h4675 : (e4675 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h4747 : (e4747 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))
  have h4872 : (e4872 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))
  have h4903 : (e4903 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))
  have h5100 : (e5100 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))
  have h5195 : (e5195 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))
  have h7749 : (e7749 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))))))))))))))))))))))))))
  have h8045 : (e8045 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h8317 : (e8317 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have p20125 := n20125 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h3976 h4096 h4156 h4199 h4306 h4369 h4434 h4567 h4608 h4675 h4747 h4787 h4813 h4872 h4903 h5100 h5195 h7749 h8045 h8317
  exact p20125
theorem n20133 (_v : Vars) (_q : Query _v)  : (e20132 _v) := by
  by_contra hc
  change ¬ ((e2371 _v) ∨ (¬ (e2061 _v)) ∨ (¬ (e4924 _v)) ∨ (¬ (e4648 _v)) ∨ (¬ (e4899 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e4546 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e30 _v)) ∨ (¬ (e4285 _v)) ∨ (¬ (e4398 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4301 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4724 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4419 _v)) ∨ (¬ (e4220 _v)) ∨ (¬ (e488 _v))) at hc
  have h30 : (e30 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))
  have h70 : (e70 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))
  have h191 : (e191 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h225 : (e225 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))
  have h442 : (e442 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))
  have h488 : (e488 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn)))))))))))))))))))))))))))))))))
  have h2061 : (e2061 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h3069 : (e3069 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h4096 : (e4096 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))
  have h4139 : (e4139 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h4156 : (e4156 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))
  have h4199 : (e4199 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h4220 : (e4220 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))))
  have h4260 : (e4260 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))
  have h4285 : (e4285 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))
  have h4301 : (e4301 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))
  have h4369 : (e4369 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h4398 : (e4398 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))
  have h4419 : (e4419 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))
  have h4546 : (e4546 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h4608 : (e4608 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h4648 : (e4648 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4675 : (e4675 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h4724 : (e4724 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))
  have h4838 : (e4838 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))
  have h4899 : (e4899 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4924 : (e4924 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h6579 : (e6579 _v) := (fun hn => hc (Or.inl hn))
  have p20127 := n20127 _v _q h30 h70 h91 h191 h225 h442 h488 h2061 h3069 h3152 h3937 h4096 h4139 h4156 h4199 h4220 h4260 h4285 h4301 h4369 h4398 h4419 h4546 h4608 h4648 h4675 h4724 h4787 h4813 h4838 h4899 h4924 h6579
  exact p20127
theorem n20134 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5100 : (e5100 _v)) (h5195 : (e5195 _v)) (h7749 : (e7749 _v)) : (e4572 _v) := by
  have p20131 := n20131 _v _q 
  have p17276 := n17276 _v _q h5195
  have p5007 := n5007 _v _q h225
  have p4992 := n4992 _v _q h442
  have p20107 := n20107 _v _q h5195
  have p5008 := n5008 _v _q h4787
  have p5006 := n5006 _v _q h4675
  have p17056 := n17056 _v _q h3946
  have p17061 := n17061 _v _q h4747
  have p4995 := n4995 _v _q h4369
  have p4999 := n4999 _v _q h91
  have p17022 := n17022 _v _q h4434 h5195
  have p17076 := n17076 _v _q h3976
  have p4985 := n4985 _v _q h4156
  have p4988 := n4988 _v _q h488
  have p4986 := n4986 _v _q h3105
  have p4984 := n4984 _v _q h4872
  have p4991 := n4991 _v _q h4608
  have p17159 := n17159 _v _q h5100
  have p4994 := n4994 _v _q h3069
  have p4998 := n4998 _v _q h3152
  have p5003 := n5003 _v _q h4199
  have p4983 := n4983 _v _q h4813
  have p17129 := n17129 _v _q h4903
  have p4996 := n4996 _v _q h3937
  have p5001 := n5001 _v _q h4096
  have p8549 := n8549 _v _q h5195
  have p5010 := n5010 _v _q h70
  have p4987 := n4987 _v _q h4434
  have p16269 := n16269 _v _q h7749
  change (¬ (e4306 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e4567 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e8317 _v)) ∨ (¬ (e8045 _v)) ∨ (¬ (e3976 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e5100 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4903 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e4096 _v)) ∨ (e196 _v) ∨ (¬ (e70 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e7749 _v)) at p20131
  change (¬ (e196 _v)) at p8549
  rcases p20131 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact (False.elim (hlit p20107))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p5007))
  · exact (False.elim (hlit p4992))
  · exact hlit
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p17056))
  · exact (False.elim (hlit p17061))
  · exact (False.elim (hlit p4995))
  · exact (False.elim (hlit p17276))
  · exact (False.elim (hlit p17022))
  · exact (False.elim (hlit p17076))
  · exact (False.elim (hlit p4985))
  · exact (False.elim (hlit p4988))
  · exact (False.elim (hlit p4986))
  · exact (False.elim (hlit p4984))
  · exact (False.elim (hlit p4991))
  · exact (False.elim (hlit p17159))
  · exact (False.elim (hlit p4994))
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p5003))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p17129))
  · exact (False.elim (hlit p4996))
  · exact (False.elim (hlit p5001))
  · exact (False.elim (p8549 hlit))
  · exact (False.elim (hlit p5010))
  · exact (False.elim (hlit p4987))
  · exact (False.elim (hlit p16269))
theorem n20135 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5100 : (e5100 _v)) (h5195 : (e5195 _v)) (h7749 : (e7749 _v)) : (e4574 _v) := by
  have p8485 := n8485 _v _q 
  have p20134 := n20134 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h3976 h4096 h4156 h4199 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872 h4903 h5100 h5195 h7749
  change (e4574 _v) ∨ (e4567 _v) at p8485
  change (¬ (e4567 _v)) at p20134
  rcases p8485 with hlit | hlit
  · exact hlit
  · exact (False.elim (p20134 hlit))
theorem n20136 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2061 : (e2061 _v)) (h3069 : (e3069 _v)) (h3152 : (e3152 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4220 : (e4220 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4419 : (e4419 _v)) (h4546 : (e4546 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4899 : (e4899 _v)) (h4924 : (e4924 _v)) (h6501 : (e6501 _v)) : (e2371 _v) := by
  have p20133 := n20133 _v _q 
  have p4968 := n4968 _v _q h4924
  have p11409 := n11409 _v _q h2061
  have p4990 := n4990 _v _q h4648
  have p4972 := n4972 _v _q h4899
  have p5006 := n5006 _v _q h4675
  have p4979 := n4979 _v _q h4139
  have p4976 := n4976 _v _q h4546
  have p4998 := n4998 _v _q h3152
  have p253 := n253 _v _q h191
  have p5010 := n5010 _v _q h70
  have p16325 := n16325 _v _q h6501
  have p15641 := n15641 _v _q h6501
  have p4995 := n4995 _v _q h4369
  have p5003 := n5003 _v _q h4199
  have p5001 := n5001 _v _q h4096
  have p4999 := n4999 _v _q h91
  have p4989 := n4989 _v _q h4838
  have p4994 := n4994 _v _q h3069
  have p5000 := n5000 _v _q h30
  have p4977 := n4977 _v _q h4285
  have p17134 := n17134 _v _q h4398
  have p4992 := n4992 _v _q h442
  have p5007 := n5007 _v _q h225
  have p4980 := n4980 _v _q h4301
  have p4983 := n4983 _v _q h4813
  have p5008 := n5008 _v _q h4787
  have p17094 := n17094 _v _q h4724
  have p4985 := n4985 _v _q h4156
  have p4981 := n4981 _v _q h4260
  have p4971 := n4971 _v _q h4419
  have p5004 := n5004 _v _q h4220
  have p4988 := n4988 _v _q h488
  change (e2371 _v) ∨ (¬ (e2061 _v)) ∨ (¬ (e4924 _v)) ∨ (¬ (e4648 _v)) ∨ (¬ (e4899 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e4546 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e30 _v)) ∨ (¬ (e4285 _v)) ∨ (¬ (e4398 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4301 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4724 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4419 _v)) ∨ (¬ (e4220 _v)) ∨ (¬ (e488 _v)) at p20133
  rcases p20133 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p11409))
  · exact (False.elim (hlit p4968))
  · exact (False.elim (hlit p4990))
  · exact (False.elim (hlit p4972))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p4979))
  · exact (False.elim (hlit p4976))
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p253))
  · exact (False.elim (hlit p5010))
  · exact (False.elim (hlit p16325))
  · exact (False.elim (hlit p15641))
  · exact (False.elim (hlit p4995))
  · exact (False.elim (hlit p5003))
  · exact (False.elim (hlit p5001))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p4989))
  · exact (False.elim (hlit p4994))
  · exact (False.elim (hlit p5000))
  · exact (False.elim (hlit p4977))
  · exact (False.elim (hlit p17134))
  · exact (False.elim (hlit p4992))
  · exact (False.elim (hlit p5007))
  · exact (False.elim (hlit p4980))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p17094))
  · exact (False.elim (hlit p4985))
  · exact (False.elim (hlit p4981))
  · exact (False.elim (hlit p4971))
  · exact (False.elim (hlit p5004))
  · exact (False.elim (hlit p4988))
theorem n20137 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2061 : (e2061 _v)) (h3069 : (e3069 _v)) (h3152 : (e3152 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4220 : (e4220 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4419 : (e4419 _v)) (h4546 : (e4546 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4899 : (e4899 _v)) (h4924 : (e4924 _v)) (h6501 : (e6501 _v)) : (e7683 _v) := by
  have p14831 := n14831 _v _q 
  have p20136 := n20136 _v _q h30 h70 h91 h191 h225 h442 h488 h2061 h3069 h3152 h4096 h4139 h4156 h4199 h4220 h4260 h4285 h4301 h4369 h4398 h4419 h4546 h4648 h4675 h4724 h4787 h4813 h4838 h4899 h4924 h6501
  change (¬ (e2371 _v)) ∨ (¬ (e7677 _v)) at p14831
  rcases p14831 with hlit | hlit
  · exact (False.elim (hlit p20136))
  · exact hlit
theorem n20138 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5100 : (e5100 _v)) (h5195 : (e5195 _v)) (h7749 : (e7749 _v)) : (e7489 _v) := by
  have p14696 := n14696 _v _q 
  have p20135 := n20135 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h3976 h4096 h4156 h4199 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872 h4903 h5100 h5195 h7749
  have p20109 := n20109 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872 h5195
  change (¬ (e1995 _v)) ∨ (¬ (e4574 _v)) at p14696
  rcases p14696 with hlit | hlit
  · exact (False.elim (hlit p20109))
  · exact (False.elim (hlit p20135))
theorem n20140 (_v : Vars) (_q : Query _v)  : (e20139 _v) := by
  by_contra hc
  change ¬ ((e196 _v) ∨ (¬ (e442 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e3976 _v)) ∨ (¬ (e5100 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e4903 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e7749 _v))) at hc
  have h70 : (e70 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))
  have h225 : (e225 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))
  have h442 : (e442 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h488 : (e488 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h3069 : (e3069 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h3105 : (e3105 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))
  have h3946 : (e3946 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h3976 : (e3976 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))
  have h4096 : (e4096 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))
  have h4156 : (e4156 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h4199 : (e4199 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))
  have h4369 : (e4369 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h4434 : (e4434 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))
  have h4608 : (e4608 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h4675 : (e4675 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4747 : (e4747 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h4872 : (e4872 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h4903 : (e4903 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))
  have h5100 : (e5100 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))
  have h5195 : (e5195 _v) := (fun hn => hc (Or.inl hn))
  have h7749 : (e7749 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))))))))))))))))))))))
  have p20138 := n20138 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h3976 h4096 h4156 h4199 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872 h4903 h5100 h5195 h7749
  exact p20138
theorem n20141 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2061 : (e2061 _v)) (h3069 : (e3069 _v)) (h3152 : (e3152 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4220 : (e4220 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4419 : (e4419 _v)) (h4546 : (e4546 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4899 : (e4899 _v)) (h4924 : (e4924 _v)) (h6501 : (e6501 _v)) : (e4181 _v) := by
  have p16453 := n16453 _v _q 
  have p20137 := n20137 _v _q h30 h70 h91 h191 h225 h442 h488 h2061 h3069 h3152 h4096 h4139 h4156 h4199 h4220 h4260 h4285 h4301 h4369 h4398 h4419 h4546 h4648 h4675 h4724 h4787 h4813 h4838 h4899 h4924 h6501
  change (e7677 _v) ∨ (e4181 _v) at p16453
  change (¬ (e7677 _v)) at p20137
  rcases p16453 with hlit | hlit
  · exact (False.elim (p20137 hlit))
  · exact hlit
theorem n20142 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5100 : (e5100 _v)) (h5108 : (e5108 _v)) (h5195 : (e5195 _v)) (h7749 : (e7749 _v)) : (e4097 _v) := by
  have p20140 := n20140 _v _q 
  have p15650 := n15650 _v _q h5108
  have p5008 := n5008 _v _q h4787
  have p5006 := n5006 _v _q h4675
  have p17056 := n17056 _v _q h3946
  have p17061 := n17061 _v _q h4747
  have p4995 := n4995 _v _q h4369
  have p4983 := n4983 _v _q h4813
  have p4985 := n4985 _v _q h4156
  have p4988 := n4988 _v _q h488
  have p4986 := n4986 _v _q h3105
  have p4984 := n4984 _v _q h4872
  have p16269 := n16269 _v _q h7749
  have p4994 := n4994 _v _q h3069
  have p4998 := n4998 _v _q h3152
  have p4996 := n4996 _v _q h3937
  have p4987 := n4987 _v _q h4434
  have p5007 := n5007 _v _q h225
  have p4999 := n4999 _v _q h91
  have p17076 := n17076 _v _q h3976
  have p17159 := n17159 _v _q h5100
  have p5003 := n5003 _v _q h4199
  have p17129 := n17129 _v _q h4903
  have p4991 := n4991 _v _q h4608
  have p8549 := n8549 _v _q h5195
  have p4992 := n4992 _v _q h442
  change (e196 _v) ∨ (¬ (e442 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e3976 _v)) ∨ (¬ (e5100 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e4903 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e7749 _v)) at p20140
  change (¬ (e196 _v)) at p8549
  rcases p20140 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact (False.elim (p8549 hlit))
  · exact (False.elim (hlit p4992))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p17056))
  · exact (False.elim (hlit p17061))
  · exact (False.elim (hlit p4995))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p4985))
  · exact (False.elim (hlit p4988))
  · exact (False.elim (hlit p4986))
  · exact (False.elim (hlit p4984))
  · exact (False.elim (hlit p4991))
  · exact (False.elim (hlit p4994))
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p4996))
  · exact (False.elim (hlit p4987))
  · exact (False.elim (hlit p5007))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p17076))
  · exact (False.elim (hlit p17159))
  · exact (False.elim (hlit p5003))
  · exact (False.elim (hlit p17129))
  · exact hlit
  · exact (False.elim (hlit p15650))
  · exact (False.elim (hlit p16269))
theorem n20143 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5100 : (e5100 _v)) (h5108 : (e5108 _v)) (h5195 : (e5195 _v)) (h7749 : (e7749 _v)) : (e7589 _v) := by
  have p15703 := n15703 _v _q 
  have p20142 := n20142 _v _q h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h3976 h4156 h4199 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872 h4903 h5100 h5108 h5195 h7749
  change (e7589 _v) ∨ (e4096 _v) at p15703
  change (¬ (e4096 _v)) at p20142
  rcases p15703 with hlit | hlit
  · exact hlit
  · exact (False.elim (p20142 hlit))
theorem n20144 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2061 : (e2061 _v)) (h3069 : (e3069 _v)) (h3152 : (e3152 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4220 : (e4220 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4419 : (e4419 _v)) (h4546 : (e4546 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4899 : (e4899 _v)) (h4924 : (e4924 _v)) (h6501 : (e6501 _v)) : (e7489 _v) := by
  have p17089 := n17089 _v _q 
  have p20141 := n20141 _v _q h30 h70 h91 h191 h225 h442 h488 h2061 h3069 h3152 h4096 h4139 h4156 h4199 h4220 h4260 h4285 h4301 h4369 h4398 h4419 h4546 h4648 h4675 h4724 h4787 h4813 h4838 h4899 h4924 h6501
  have p10896 := n10896 _v _q 
  have p10893 := n10893 _v _q 
  have p19665 := n19665 _v _q 
  have p20110 := n20110 _v _q h70 h91 h225 h442 h488 h3069 h3152 h4096 h4156 h4199 h4260 h4369 h4675 h4787 h4813
  have p11409 := n11409 _v _q h2061
  have p17050 := n17050 _v _q 
  have p4968 := n4968 _v _q h4924
  have p4990 := n4990 _v _q h4648
  have p20118 := n20118 _v _q h70 h91 h225 h442 h488 h3069 h3152 h4096 h4156 h4199 h4260 h4369 h4675 h4787 h4813
  have p16994 := n16994 _v _q 
  have p4972 := n4972 _v _q h4899
  have p5006 := n5006 _v _q h4675
  have p4979 := n4979 _v _q h4139
  have p4976 := n4976 _v _q h4546
  have p20126 := n20126 _v _q 
  have p13951 := n13951 _v _q 
  have p17009 := n17009 _v _q 
  have p4998 := n4998 _v _q h3152
  have p253 := n253 _v _q h191
  have p5010 := n5010 _v _q h70
  have p16911 := n16911 _v _q 
  have p16325 := n16325 _v _q h6501
  have p15641 := n15641 _v _q h6501
  have p4995 := n4995 _v _q h4369
  have p5003 := n5003 _v _q h4199
  have p5001 := n5001 _v _q h4096
  have p16576 := n16576 _v _q 
  have p4999 := n4999 _v _q h91
  have p4989 := n4989 _v _q h4838
  have p4994 := n4994 _v _q h3069
  have p5000 := n5000 _v _q h30
  have p4977 := n4977 _v _q h4285
  have p17134 := n17134 _v _q h4398
  have p17058 := n17058 _v _q 
  have p17064 := n17064 _v _q 
  have p17067 := n17067 _v _q 
  have p17069 := n17069 _v _q 
  have p17072 := n17072 _v _q 
  have p4992 := n4992 _v _q h442
  have p5007 := n5007 _v _q h225
  have p17078 := n17078 _v _q 
  have p17080 := n17080 _v _q 
  have p17083 := n17083 _v _q 
  have p17074 := n17074 _v _q 
  have p17087 := n17087 _v _q 
  have p17758 := n17758 _v _q 
  have p17091 := n17091 _v _q 
  have p17093 := n17093 _v _q 
  have p4980 := n4980 _v _q h4301
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p17100 := n17100 _v _q 
  have p17102 := n17102 _v _q 
  have p19610 := n19610 _v _q 
  have p17104 := n17104 _v _q 
  have p17096 := n17096 _v _q 
  have p4983 := n4983 _v _q h4813
  have p5008 := n5008 _v _q h4787
  have p17113 := n17113 _v _q 
  have p17094 := n17094 _v _q h4724
  have p17122 := n17122 _v _q 
  have p17117 := n17117 _v _q 
  have p17124 := n17124 _v _q 
  have p17115 := n17115 _v _q 
  have p17120 := n17120 _v _q 
  have p4985 := n4985 _v _q h4156
  have p17127 := n17127 _v _q 
  have p16778 := n16778 _v _q 
  have p17874 := n17874 _v _q 
  have p17131 := n17131 _v _q 
  have p17110 := n17110 _v _q 
  have p17133 := n17133 _v _q 
  have p4981 := n4981 _v _q h4260
  have p4971 := n4971 _v _q h4419
  have p17111 := n17111 _v _q 
  have p17294 := n17294 _v _q 
  have p17136 := n17136 _v _q 
  have p17141 := n17141 _v _q 
  have p16913 := n16913 _v _q 
  have p5004 := n5004 _v _q h4220
  have p17147 := n17147 _v _q 
  have p20096 := n20096 _v _q 
  have p17053 := n17053 _v _q 
  have p15217 := n15217 _v _q h2061
  have p17055 := n17055 _v _q 
  have p17108 := n17108 _v _q 
  have p4988 := n4988 _v _q h488
  have p8554 := n8554 _v _q h6501
  exact FloorCertificate.node_20144 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e61 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2863 _v) (e2877 _v) (e2879 _v) (e2883 _v) (e2898 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2913 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p17089 p20141 p10896 p10893 p19665 p20110 p11409 p17050 p4968 p4990 p20118 p16994 p4972 p5006 p4979 p4976 p20126 p13951 p17009 p4998 p253 p5010 p16911 p16325 p15641 p4995 p5003 p5001 p16576 p4999 p4989 p4994 p5000 p4977 p17134 p17058 p17064 p17067 p17069 p17072 p4992 p5007 p17078 p17080 p17083 p17074 p17087 p17758 p17091 p17093 p4980 p17098 p17106 p17100 p17102 p19610 p17104 p17096 p4983 p5008 p17113 p17094 p17122 p17117 p17124 p17115 p17120 p4985 p17127 p16778 p17874 p17131 p17110 p17133 p4981 p4971 p17111 p17294 p17136 p17141 p16913 p5004 p17147 p20096 p17053 p15217 p17055 p17108 p4988 p8554
theorem n20145 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5100 : (e5100 _v)) (h5108 : (e5108 _v)) (h5195 : (e5195 _v)) (h7749 : (e7749 _v)) : (e2733 _v) := by
  have p14525 := n14525 _v _q 
  have p20143 := n20143 _v _q h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h3976 h4156 h4199 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872 h4903 h5100 h5108 h5195 h7749
  change (e2733 _v) ∨ (¬ (e7589 _v)) at p14525
  rcases p14525 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p20143))
theorem n20146 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5100 : (e5100 _v)) (h5108 : (e5108 _v)) (h5195 : (e5195 _v)) (h7749 : (e7749 _v)) : (e7489 _v) := by
  have p11366 := n11366 _v _q h5108
  have p5257 := n5257 _v _q 
  have p20145 := n20145 _v _q h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h3976 h4156 h4199 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872 h4903 h5100 h5108 h5195 h7749
  exact FloorCertificate.node_20146 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p11366 p5257 p20145
theorem n20148 (_v : Vars) (_q : Query _v)  : (e20147 _v) := by
  by_contra hc
  change ¬ ((e48 _v) ∨ (¬ (e4787 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e7749 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e3976 _v)) ∨ (¬ (e5100 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e4903 _v)) ∨ (¬ (e4608 _v)) ∨ (e196 _v) ∨ (¬ (e442 _v))) at hc
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))
  have h225 : (e225 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))
  have h442 : (e442 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn)))))))))))))))))))))))))
  have h488 : (e488 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h3069 : (e3069 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h3105 : (e3105 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h3946 : (e3946 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h3976 : (e3976 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))
  have h4156 : (e4156 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h4199 : (e4199 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))
  have h4369 : (e4369 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h4434 : (e4434 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))
  have h4608 : (e4608 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))
  have h4675 : (e4675 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4747 : (e4747 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h4872 : (e4872 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h4903 : (e4903 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))
  have h5100 : (e5100 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))
  have h5108 : (e5108 _v) := (fun hn => hc (Or.inl hn))
  have h5195 : (e5195 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))
  have h7749 : (e7749 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have p20146 := n20146 _v _q h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h3976 h4156 h4199 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872 h4903 h5100 h5108 h5195 h7749
  exact p20146
theorem n20150 (_v : Vars) (_q : Query _v)  : (e20149 _v) := by
  by_contra hc
  change ¬ ((¬ (e4924 _v)) ∨ (¬ (e2061 _v)) ∨ (¬ (e4648 _v)) ∨ (¬ (e4899 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e4546 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e30 _v)) ∨ (¬ (e4285 _v)) ∨ (¬ (e4398 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4301 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4724 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4419 _v)) ∨ (¬ (e4220 _v)) ∨ (¬ (e488 _v)) ∨ (e2179 _v)) at hc
  have h30 : (e30 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))
  have h70 : (e70 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h191 : (e191 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h225 : (e225 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))
  have h442 : (e442 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))
  have h488 : (e488 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))
  have h2061 : (e2061 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h3069 : (e3069 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h4096 : (e4096 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h4139 : (e4139 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h4156 : (e4156 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))
  have h4199 : (e4199 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h4220 : (e4220 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))
  have h4260 : (e4260 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))
  have h4285 : (e4285 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))
  have h4301 : (e4301 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))
  have h4369 : (e4369 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h4398 : (e4398 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))
  have h4419 : (e4419 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))
  have h4546 : (e4546 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h4648 : (e4648 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4675 : (e4675 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4724 : (e4724 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))
  have h4838 : (e4838 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h4899 : (e4899 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4924 : (e4924 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h6501 : (e6501 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn)))))))))))))))))))))))))))))))
  have p20144 := n20144 _v _q h30 h70 h91 h191 h225 h442 h488 h2061 h3069 h3152 h4096 h4139 h4156 h4199 h4220 h4260 h4285 h4301 h4369 h4398 h4419 h4546 h4648 h4675 h4724 h4787 h4813 h4838 h4899 h4924 h6501
  exact p20144
theorem n20151 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5100 : (e5100 _v)) (h5195 : (e5195 _v)) (h7807 : (e7807 _v)) : (e48 _v) := by
  have p20148 := n20148 _v _q 
  have p8549 := n8549 _v _q h5195
  have p5006 := n5006 _v _q h4675
  have p17056 := n17056 _v _q h3946
  have p17061 := n17061 _v _q h4747
  have p4995 := n4995 _v _q h4369
  have p4983 := n4983 _v _q h4813
  have p4985 := n4985 _v _q h4156
  have p4988 := n4988 _v _q h488
  have p4986 := n4986 _v _q h3105
  have p4984 := n4984 _v _q h4872
  have p17786 := n17786 _v _q h7807
  have p4994 := n4994 _v _q h3069
  have p4998 := n4998 _v _q h3152
  have p4996 := n4996 _v _q h3937
  have p4987 := n4987 _v _q h4434
  have p5007 := n5007 _v _q h225
  have p4999 := n4999 _v _q h91
  have p17076 := n17076 _v _q h3976
  have p17159 := n17159 _v _q h5100
  have p5003 := n5003 _v _q h4199
  have p17129 := n17129 _v _q h4903
  have p4991 := n4991 _v _q h4608
  have p5008 := n5008 _v _q h4787
  have p4992 := n4992 _v _q h442
  change (e48 _v) ∨ (¬ (e4787 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e7749 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e3976 _v)) ∨ (¬ (e5100 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e4903 _v)) ∨ (¬ (e4608 _v)) ∨ (e196 _v) ∨ (¬ (e442 _v)) at p20148
  change (¬ (e196 _v)) at p8549
  rcases p20148 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p17056))
  · exact (False.elim (hlit p17061))
  · exact (False.elim (hlit p4995))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p4985))
  · exact (False.elim (hlit p4988))
  · exact (False.elim (hlit p4986))
  · exact (False.elim (hlit p4984))
  · exact (False.elim (hlit p17786))
  · exact (False.elim (hlit p4994))
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p4996))
  · exact (False.elim (hlit p4987))
  · exact (False.elim (hlit p5007))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p17076))
  · exact (False.elim (hlit p17159))
  · exact (False.elim (hlit p5003))
  · exact (False.elim (hlit p17129))
  · exact (False.elim (hlit p4991))
  · exact (False.elim (p8549 hlit))
  · exact (False.elim (hlit p4992))
theorem n20152 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2061 : (e2061 _v)) (h3069 : (e3069 _v)) (h3152 : (e3152 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4220 : (e4220 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4419 : (e4419 _v)) (h4546 : (e4546 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4899 : (e4899 _v)) (h6501 : (e6501 _v)) : (e4925 _v) := by
  have p20150 := n20150 _v _q 
  have p5004 := n5004 _v _q h4220
  have p4990 := n4990 _v _q h4648
  have p4972 := n4972 _v _q h4899
  have p5006 := n5006 _v _q h4675
  have p4979 := n4979 _v _q h4139
  have p4976 := n4976 _v _q h4546
  have p4998 := n4998 _v _q h3152
  have p253 := n253 _v _q h191
  have p5010 := n5010 _v _q h70
  have p4995 := n4995 _v _q h4369
  have p5003 := n5003 _v _q h4199
  have p5001 := n5001 _v _q h4096
  have p4999 := n4999 _v _q h91
  have p4989 := n4989 _v _q h4838
  have p4994 := n4994 _v _q h3069
  have p5000 := n5000 _v _q h30
  have p4977 := n4977 _v _q h4285
  have p17134 := n17134 _v _q h4398
  have p4992 := n4992 _v _q h442
  have p5007 := n5007 _v _q h225
  have p4980 := n4980 _v _q h4301
  have p4983 := n4983 _v _q h4813
  have p5008 := n5008 _v _q h4787
  have p17094 := n17094 _v _q h4724
  have p4985 := n4985 _v _q h4156
  have p4981 := n4981 _v _q h4260
  have p4971 := n4971 _v _q h4419
  have p11409 := n11409 _v _q h2061
  have p4988 := n4988 _v _q h488
  have p8554 := n8554 _v _q h6501
  change (¬ (e4924 _v)) ∨ (¬ (e2061 _v)) ∨ (¬ (e4648 _v)) ∨ (¬ (e4899 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e4546 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e30 _v)) ∨ (¬ (e4285 _v)) ∨ (¬ (e4398 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4301 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4724 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4419 _v)) ∨ (¬ (e4220 _v)) ∨ (¬ (e488 _v)) ∨ (e2179 _v) at p20150
  change (¬ (e2179 _v)) at p8554
  rcases p20150 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p11409))
  · exact (False.elim (hlit p4990))
  · exact (False.elim (hlit p4972))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p4979))
  · exact (False.elim (hlit p4976))
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p253))
  · exact (False.elim (hlit p5010))
  · exact (False.elim (hlit p4995))
  · exact (False.elim (hlit p5003))
  · exact (False.elim (hlit p5001))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p4989))
  · exact (False.elim (hlit p4994))
  · exact (False.elim (hlit p5000))
  · exact (False.elim (hlit p4977))
  · exact (False.elim (hlit p17134))
  · exact (False.elim (hlit p4992))
  · exact (False.elim (hlit p5007))
  · exact (False.elim (hlit p4980))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p17094))
  · exact (False.elim (hlit p4985))
  · exact (False.elim (hlit p4981))
  · exact (False.elim (hlit p4971))
  · exact (False.elim (hlit p5004))
  · exact (False.elim (hlit p4988))
  · exact (False.elim (p8554 hlit))
theorem n20153 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2061 : (e2061 _v)) (h3069 : (e3069 _v)) (h3152 : (e3152 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4220 : (e4220 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4419 : (e4419 _v)) (h4546 : (e4546 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4899 : (e4899 _v)) (h6501 : (e6501 _v)) : (e8384 _v) := by
  have p16462 := n16462 _v _q 
  have p20152 := n20152 _v _q h30 h70 h91 h191 h225 h442 h488 h2061 h3069 h3152 h4096 h4139 h4156 h4199 h4220 h4260 h4285 h4301 h4369 h4398 h4419 h4546 h4648 h4675 h4724 h4787 h4813 h4838 h4899 h6501
  change (e8384 _v) ∨ (e4924 _v) at p16462
  change (¬ (e4924 _v)) at p20152
  rcases p16462 with hlit | hlit
  · exact hlit
  · exact (False.elim (p20152 hlit))
theorem n20154 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5100 : (e5100 _v)) (h5195 : (e5195 _v)) (h7807 : (e7807 _v)) : (e60 _v) := by
  have p14152 := n14152 _v _q 
  have p20151 := n20151 _v _q h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h3976 h4156 h4199 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872 h4903 h5100 h5195 h7807
  change (¬ (e48 _v)) ∨ (¬ (e59 _v)) at p14152
  rcases p14152 with hlit | hlit
  · exact (False.elim (hlit p20151))
  · exact hlit
theorem n20155 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5100 : (e5100 _v)) (h5195 : (e5195 _v)) (h7807 : (e7807 _v)) : (e51 _v) := by
  have p14962 := n14962 _v _q 
  have p20154 := n20154 _v _q h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h3976 h4156 h4199 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872 h4903 h5100 h5195 h7807
  change (e59 _v) ∨ (e51 _v) at p14962
  change (¬ (e59 _v)) at p20154
  rcases p14962 with hlit | hlit
  · exact (False.elim (p20154 hlit))
  · exact hlit
theorem n20156 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2061 : (e2061 _v)) (h3069 : (e3069 _v)) (h3152 : (e3152 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4220 : (e4220 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4419 : (e4419 _v)) (h4546 : (e4546 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4899 : (e4899 _v)) (h6501 : (e6501 _v)) : (e6780 _v) := by
  have p14912 := n14912 _v _q 
  have p20153 := n20153 _v _q h30 h70 h91 h191 h225 h442 h488 h2061 h3069 h3152 h4096 h4139 h4156 h4199 h4220 h4260 h4285 h4301 h4369 h4398 h4419 h4546 h4648 h4675 h4724 h4787 h4813 h4838 h4899 h6501
  change (¬ (e2799 _v)) ∨ (¬ (e8384 _v)) at p14912
  rcases p14912 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p20153))
theorem n20157 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2061 : (e2061 _v)) (h3069 : (e3069 _v)) (h3152 : (e3152 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4220 : (e4220 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4419 : (e4419 _v)) (h4546 : (e4546 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4899 : (e4899 _v)) (h6501 : (e6501 _v)) : (e8408 _v) := by
  have p15435 := n15435 _v _q 
  have p20156 := n20156 _v _q h30 h70 h91 h191 h225 h442 h488 h2061 h3069 h3152 h4096 h4139 h4156 h4199 h4220 h4260 h4285 h4301 h4369 h4398 h4419 h4546 h4648 h4675 h4724 h4787 h4813 h4838 h4899 h6501
  change (e2799 _v) ∨ (¬ (e8407 _v)) at p15435
  change (¬ (e2799 _v)) at p20156
  rcases p15435 with hlit | hlit
  · exact (False.elim (p20156 hlit))
  · exact hlit
theorem n20158 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2061 : (e2061 _v)) (h3069 : (e3069 _v)) (h3152 : (e3152 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4220 : (e4220 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4419 : (e4419 _v)) (h4546 : (e4546 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4899 : (e4899 _v)) (h6501 : (e6501 _v)) : (e8398 _v) := by
  have p11470 := n11470 _v _q 
  have p20157 := n20157 _v _q h30 h70 h91 h191 h225 h442 h488 h2061 h3069 h3152 h4096 h4139 h4156 h4199 h4220 h4260 h4285 h4301 h4369 h4398 h4419 h4546 h4648 h4675 h4724 h4787 h4813 h4838 h4899 h6501
  change (e8407 _v) ∨ (e8398 _v) at p11470
  change (¬ (e8407 _v)) at p20157
  rcases p11470 with hlit | hlit
  · exact (False.elim (p20157 hlit))
  · exact hlit
theorem n20159 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4306 : (e4306 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4434 : (e4434 _v)) (h4491 : (e4491 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5100 : (e5100 _v)) (h5195 : (e5195 _v)) (h5208 : (e5208 _v)) (h6571 : (e6571 _v)) (h7807 : (e7807 _v)) (h8045 : (e8045 _v)) : (e6776 _v) := by
  have p17813 := n17813 _v _q 
  have p20155 := n20155 _v _q h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h3976 h4156 h4199 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872 h4903 h5100 h5195 h7807
  have p4999 := n4999 _v _q h91
  have p4996 := n4996 _v _q h3937
  have p5003 := n5003 _v _q h4199
  have p4998 := n4998 _v _q h3152
  have p17128 := n17128 _v _q h4491
  have p4983 := n4983 _v _q h4813
  have p5008 := n5008 _v _q h4787
  have p17129 := n17129 _v _q h4903
  have p5006 := n5006 _v _q h4675
  have p17159 := n17159 _v _q h5100
  have p17134 := n17134 _v _q h4398
  have p17157 := n17157 _v _q h8045
  have p17137 := n17137 _v _q h4059
  have p17138 := n17138 _v _q h4306
  have p5007 := n5007 _v _q h225
  have p4992 := n4992 _v _q h442
  have p17175 := n17175 _v _q h5208
  have p17056 := n17056 _v _q h3946
  have p17060 := n17060 _v _q h4653
  have p17061 := n17061 _v _q h4747
  have p4995 := n4995 _v _q h4369
  have p17076 := n17076 _v _q h3976
  have p4985 := n4985 _v _q h4156
  have p4991 := n4991 _v _q h4608
  have p4988 := n4988 _v _q h488
  have p4986 := n4986 _v _q h3105
  have p4984 := n4984 _v _q h4872
  have p17094 := n17094 _v _q h4724
  have p4994 := n4994 _v _q h3069
  have p4987 := n4987 _v _q h4434
  have p11350 := n11350 _v _q h7807
  have p17143 := n17143 _v _q h4567
  have p8447 := n8447 _v _q h6571
  have p12925 := n12925 _v _q h5195
  change (¬ (e5208 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4491 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4903 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e5100 _v)) ∨ (¬ (e4398 _v)) ∨ (¬ (e8045 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e4567 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e3976 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4724 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4434 _v)) ∨ (e2303 _v) ∨ (e2529 _v) ∨ (e2358 _v) ∨ (¬ (e2781 _v)) at p17813
  change (¬ (e2303 _v)) at p11350
  change (¬ (e2358 _v)) at p8447
  change (¬ (e2529 _v)) at p12925
  rcases p17813 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact (False.elim (hlit p17175))
  · exact (False.elim (hlit p4991))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p4996))
  · exact (False.elim (hlit p5003))
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p17128))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p17129))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p17159))
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
  · exact (False.elim (hlit p20155))
  · exact (False.elim (hlit p4988))
  · exact (False.elim (hlit p4986))
  · exact (False.elim (hlit p4984))
  · exact (False.elim (hlit p17094))
  · exact (False.elim (hlit p4994))
  · exact (False.elim (hlit p4987))
  · exact (False.elim (p11350 hlit))
  · exact (False.elim (p12925 hlit))
  · exact (False.elim (p8447 hlit))
  · exact hlit
theorem n20160 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2061 : (e2061 _v)) (h3069 : (e3069 _v)) (h3152 : (e3152 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4220 : (e4220 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4419 : (e4419 _v)) (h4546 : (e4546 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4899 : (e4899 _v)) (h6501 : (e6501 _v)) : (e7489 _v) := by
  have p20158 := n20158 _v _q h30 h70 h91 h191 h225 h442 h488 h2061 h3069 h3152 h4096 h4139 h4156 h4199 h4220 h4260 h4285 h4301 h4369 h4398 h4419 h4546 h4648 h4675 h4724 h4787 h4813 h4838 h4899 h6501
  have p17089 := n17089 _v _q 
  have p10893 := n10893 _v _q 
  have p10896 := n10896 _v _q 
  have p19665 := n19665 _v _q 
  have p20110 := n20110 _v _q h70 h91 h225 h442 h488 h3069 h3152 h4096 h4156 h4199 h4260 h4369 h4675 h4787 h4813
  have p11409 := n11409 _v _q h2061
  have p17050 := n17050 _v _q 
  have p4990 := n4990 _v _q h4648
  have p20118 := n20118 _v _q h70 h91 h225 h442 h488 h3069 h3152 h4096 h4156 h4199 h4260 h4369 h4675 h4787 h4813
  have p16994 := n16994 _v _q 
  have p4972 := n4972 _v _q h4899
  have p5006 := n5006 _v _q h4675
  have p4979 := n4979 _v _q h4139
  have p4976 := n4976 _v _q h4546
  have p20126 := n20126 _v _q 
  have p13951 := n13951 _v _q 
  have p17009 := n17009 _v _q 
  have p4998 := n4998 _v _q h3152
  have p253 := n253 _v _q h191
  have p5010 := n5010 _v _q h70
  have p16911 := n16911 _v _q 
  have p16325 := n16325 _v _q h6501
  have p15641 := n15641 _v _q h6501
  have p4995 := n4995 _v _q h4369
  have p5003 := n5003 _v _q h4199
  have p5001 := n5001 _v _q h4096
  have p16576 := n16576 _v _q 
  have p4999 := n4999 _v _q h91
  have p4989 := n4989 _v _q h4838
  have p4994 := n4994 _v _q h3069
  have p5000 := n5000 _v _q h30
  have p4977 := n4977 _v _q h4285
  have p17134 := n17134 _v _q h4398
  have p17058 := n17058 _v _q 
  have p17064 := n17064 _v _q 
  have p17067 := n17067 _v _q 
  have p17069 := n17069 _v _q 
  have p17072 := n17072 _v _q 
  have p4992 := n4992 _v _q h442
  have p5007 := n5007 _v _q h225
  have p17078 := n17078 _v _q 
  have p17080 := n17080 _v _q 
  have p17083 := n17083 _v _q 
  have p17074 := n17074 _v _q 
  have p17087 := n17087 _v _q 
  have p17758 := n17758 _v _q 
  have p17091 := n17091 _v _q 
  have p17093 := n17093 _v _q 
  have p4980 := n4980 _v _q h4301
  have p17221 := n17221 _v _q 
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p17100 := n17100 _v _q 
  have p17102 := n17102 _v _q 
  have p19610 := n19610 _v _q 
  have p17104 := n17104 _v _q 
  have p17096 := n17096 _v _q 
  have p4983 := n4983 _v _q h4813
  have p5008 := n5008 _v _q h4787
  have p17113 := n17113 _v _q 
  have p17094 := n17094 _v _q h4724
  have p17122 := n17122 _v _q 
  have p17117 := n17117 _v _q 
  have p17124 := n17124 _v _q 
  have p17115 := n17115 _v _q 
  have p17120 := n17120 _v _q 
  have p4985 := n4985 _v _q h4156
  have p17127 := n17127 _v _q 
  have p16778 := n16778 _v _q 
  have p17874 := n17874 _v _q 
  have p17131 := n17131 _v _q 
  have p17110 := n17110 _v _q 
  have p17133 := n17133 _v _q 
  have p4981 := n4981 _v _q h4260
  have p4971 := n4971 _v _q h4419
  have p17111 := n17111 _v _q 
  have p17294 := n17294 _v _q 
  have p17136 := n17136 _v _q 
  have p17141 := n17141 _v _q 
  have p16913 := n16913 _v _q 
  have p5004 := n5004 _v _q h4220
  have p17147 := n17147 _v _q 
  have p20096 := n20096 _v _q 
  have p17053 := n17053 _v _q 
  have p15217 := n15217 _v _q h2061
  have p17055 := n17055 _v _q 
  have p17108 := n17108 _v _q 
  have p4988 := n4988 _v _q h488
  have p8554 := n8554 _v _q h6501
  exact FloorCertificate.node_20160 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e61 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2863 _v) (e2877 _v) (e2879 _v) (e2883 _v) (e2898 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2913 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p20158 p17089 p10893 p10896 p19665 p20110 p11409 p17050 p4990 p20118 p16994 p4972 p5006 p4979 p4976 p20126 p13951 p17009 p4998 p253 p5010 p16911 p16325 p15641 p4995 p5003 p5001 p16576 p4999 p4989 p4994 p5000 p4977 p17134 p17058 p17064 p17067 p17069 p17072 p4992 p5007 p17078 p17080 p17083 p17074 p17087 p17758 p17091 p17093 p4980 p17221 p17098 p17106 p17100 p17102 p19610 p17104 p17096 p4983 p5008 p17113 p17094 p17122 p17117 p17124 p17115 p17120 p4985 p17127 p16778 p17874 p17131 p17110 p17133 p4981 p4971 p17111 p17294 p17136 p17141 p16913 p5004 p17147 p20096 p17053 p15217 p17055 p17108 p4988 p8554
theorem n20161 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4306 : (e4306 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4434 : (e4434 _v)) (h4491 : (e4491 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5100 : (e5100 _v)) (h5195 : (e5195 _v)) (h5208 : (e5208 _v)) (h6571 : (e6571 _v)) (h7807 : (e7807 _v)) (h8045 : (e8045 _v)) : (e7789 _v) := by
  have p14570 := n14570 _v _q 
  have p20159 := n20159 _v _q h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h3976 h4059 h4156 h4199 h4306 h4369 h4398 h4434 h4491 h4567 h4608 h4653 h4675 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h5195 h5208 h6571 h7807 h8045
  change (e2781 _v) ∨ (¬ (e7781 _v)) at p14570
  change (¬ (e2781 _v)) at p20159
  rcases p14570 with hlit | hlit
  · exact (False.elim (p20159 hlit))
  · exact hlit
theorem n20162 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4306 : (e4306 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4434 : (e4434 _v)) (h4491 : (e4491 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5100 : (e5100 _v)) (h5195 : (e5195 _v)) (h5208 : (e5208 _v)) (h6571 : (e6571 _v)) (h7807 : (e7807 _v)) (h8045 : (e8045 _v)) : (e4260 _v) := by
  have p15824 := n15824 _v _q 
  have p20161 := n20161 _v _q h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h3976 h4059 h4156 h4199 h4306 h4369 h4398 h4434 h4491 h4567 h4608 h4653 h4675 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h5195 h5208 h6571 h7807 h8045
  change (e7781 _v) ∨ (e4260 _v) at p15824
  change (¬ (e7781 _v)) at p20161
  rcases p15824 with hlit | hlit
  · exact (False.elim (p20161 hlit))
  · exact hlit
theorem n20163 (_v : Vars) (_q : Query _v) (h7807 : (e7807 _v)) : (e7608 _v) := by
  have p18879 := n18879 _v _q 
  have p16014 := n16014 _v _q h7807
  change (e7610 _v) ∨ (e7608 _v) at p18879
  change (¬ (e7610 _v)) at p16014
  rcases p18879 with hlit | hlit
  · exact (False.elim (p16014 hlit))
  · exact hlit
theorem n20164 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4306 : (e4306 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4434 : (e4434 _v)) (h4491 : (e4491 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5100 : (e5100 _v)) (h5195 : (e5195 _v)) (h5208 : (e5208 _v)) (h6571 : (e6571 _v)) (h7807 : (e7807 _v)) (h8045 : (e8045 _v)) : (e4444 _v) := by
  have p17617 := n17617 _v _q 
  have p20159 := n20159 _v _q h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h3976 h4059 h4156 h4199 h4306 h4369 h4398 h4434 h4491 h4567 h4608 h4653 h4675 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h5195 h5208 h6571 h7807 h8045
  have p17786 := n17786 _v _q h7807
  have p4991 := n4991 _v _q h4608
  have p4999 := n4999 _v _q h91
  have p4996 := n4996 _v _q h3937
  have p5003 := n5003 _v _q h4199
  have p4998 := n4998 _v _q h3152
  have p17128 := n17128 _v _q h4491
  have p4983 := n4983 _v _q h4813
  have p5008 := n5008 _v _q h4787
  have p17129 := n17129 _v _q h4903
  have p17175 := n17175 _v _q h5208
  have p5006 := n5006 _v _q h4675
  have p17159 := n17159 _v _q h5100
  have p15373 := n15373 _v _q h7807
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
  have p20163 := n20163 _v _q h7807
  have p4988 := n4988 _v _q h488
  have p4986 := n4986 _v _q h3105
  have p4984 := n4984 _v _q h4872
  have p17094 := n17094 _v _q h4724
  have p4994 := n4994 _v _q h3069
  have p17255 := n17255 _v _q h6571
  have p8549 := n8549 _v _q h5195
  have p20151 := n20151 _v _q h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h3976 h4156 h4199 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872 h4903 h5100 h5195 h7807
  change (¬ (e4439 _v)) ∨ (¬ (e7749 _v)) ∨ (e2781 _v) ∨ (¬ (e4608 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4491 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4903 _v)) ∨ (¬ (e5208 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e5100 _v)) ∨ (¬ (e7814 _v)) ∨ (¬ (e4398 _v)) ∨ (¬ (e8045 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e4567 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e3976 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e7608 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4724 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e7935 _v)) ∨ (e196 _v) ∨ (¬ (e48 _v)) at p17617
  change (¬ (e2781 _v)) at p20159
  change (¬ (e196 _v)) at p8549
  rcases p17617 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p17786))
  · exact (False.elim (p20159 hlit))
  · exact (False.elim (hlit p4991))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p4996))
  · exact (False.elim (hlit p5003))
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p17128))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p17129))
  · exact (False.elim (hlit p17175))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p17159))
  · exact (False.elim (hlit p15373))
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
  · exact (False.elim (hlit p20163))
  · exact (False.elim (hlit p4988))
  · exact (False.elim (hlit p4986))
  · exact (False.elim (hlit p4984))
  · exact (False.elim (hlit p17094))
  · exact (False.elim (hlit p4994))
  · exact (False.elim (hlit p17255))
  · exact (False.elim (p8549 hlit))
  · exact (False.elim (hlit p20151))
theorem n20166 (_v : Vars) (_q : Query _v)  : (e20165 _v) := by
  by_contra hc
  change ¬ ((¬ (e4220 _v)) ∨ (¬ (e2061 _v)) ∨ (¬ (e4648 _v)) ∨ (¬ (e4899 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e4546 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e30 _v)) ∨ (¬ (e4285 _v)) ∨ (¬ (e4398 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4301 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4724 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4419 _v)) ∨ (¬ (e488 _v)) ∨ (e2179 _v)) at hc
  have h30 : (e30 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))
  have h70 : (e70 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h191 : (e191 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h225 : (e225 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))
  have h442 : (e442 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))
  have h488 : (e488 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))
  have h2061 : (e2061 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h3069 : (e3069 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h4096 : (e4096 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h4139 : (e4139 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h4156 : (e4156 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))
  have h4199 : (e4199 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h4220 : (e4220 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h4260 : (e4260 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))
  have h4285 : (e4285 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))
  have h4301 : (e4301 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))
  have h4369 : (e4369 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h4398 : (e4398 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))
  have h4419 : (e4419 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))
  have h4546 : (e4546 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h4648 : (e4648 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4675 : (e4675 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4724 : (e4724 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))
  have h4838 : (e4838 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h4899 : (e4899 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h6501 : (e6501 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))))))))))))))))))))))))))
  have p20160 := n20160 _v _q h30 h70 h91 h191 h225 h442 h488 h2061 h3069 h3152 h4096 h4139 h4156 h4199 h4220 h4260 h4285 h4301 h4369 h4398 h4419 h4546 h4648 h4675 h4724 h4787 h4813 h4838 h4899 h6501
  exact p20160
theorem n20167 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4306 : (e4306 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4434 : (e4434 _v)) (h4491 : (e4491 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5100 : (e5100 _v)) (h5195 : (e5195 _v)) (h5208 : (e5208 _v)) (h6571 : (e6571 _v)) (h7807 : (e7807 _v)) (h8045 : (e8045 _v)) : (e4097 _v) := by
  have p4016 := n4016 _v _q 
  have p4994 := n4994 _v _q h3069
  have p17117 := n17117 _v _q 
  have p17255 := n17255 _v _q h6571
  have p17113 := n17113 _v _q 
  have p17120 := n17120 _v _q 
  have p16977 := n16977 _v _q 
  have p4987 := n4987 _v _q h4434
  have p16929 := n16929 _v _q 
  have p17786 := n17786 _v _q h7807
  have p17009 := n17009 _v _q 
  have p17122 := n17122 _v _q 
  have p4991 := n4991 _v _q h4608
  have p16576 := n16576 _v _q 
  have p17124 := n17124 _v _q 
  have p20155 := n20155 _v _q h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h3976 h4156 h4199 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872 h4903 h5100 h5195 h7807
  have p4999 := n4999 _v _q h91
  have p4996 := n4996 _v _q h3937
  have p20162 := n20162 _v _q h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h3976 h4059 h4156 h4199 h4306 h4369 h4398 h4434 h4491 h4567 h4608 h4653 h4675 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h5195 h5208 h6571 h7807 h8045
  have p17147 := n17147 _v _q 
  have p5003 := n5003 _v _q h4199
  have p4998 := n4998 _v _q h3152
  have p17127 := n17127 _v _q 
  have p17276 := n17276 _v _q h5195
  have p17128 := n17128 _v _q h4491
  have p4983 := n4983 _v _q h4813
  have p5008 := n5008 _v _q h4787
  have p17256 := n17256 _v _q 
  have p17129 := n17129 _v _q h4903
  have p17175 := n17175 _v _q h5208
  have p5006 := n5006 _v _q h4675
  have p17159 := n17159 _v _q h5100
  have p17131 := n17131 _v _q 
  have p15373 := n15373 _v _q h7807
  have p17133 := n17133 _v _q 
  have p17134 := n17134 _v _q h4398
  have p17136 := n17136 _v _q 
  have p17157 := n17157 _v _q h8045
  have p17137 := n17137 _v _q h4059
  have p17138 := n17138 _v _q h4306
  have p5007 := n5007 _v _q h225
  have p16778 := n16778 _v _q 
  have p17141 := n17141 _v _q 
  have p4992 := n4992 _v _q h442
  have p17143 := n17143 _v _q h4567
  have p17050 := n17050 _v _q 
  have p17053 := n17053 _v _q 
  have p17055 := n17055 _v _q 
  have p17056 := n17056 _v _q h3946
  have p17058 := n17058 _v _q 
  have p17060 := n17060 _v _q h4653
  have p17061 := n17061 _v _q h4747
  have p17064 := n17064 _v _q 
  have p4995 := n4995 _v _q h4369
  have p17067 := n17067 _v _q 
  have p17069 := n17069 _v _q 
  have p17072 := n17072 _v _q 
  have p17074 := n17074 _v _q 
  have p17076 := n17076 _v _q h3976
  have p4985 := n4985 _v _q h4156
  have p4988 := n4988 _v _q h488
  have p17078 := n17078 _v _q 
  have p4986 := n4986 _v _q h3105
  have p17080 := n17080 _v _q 
  have p17083 := n17083 _v _q 
  have p4984 := n4984 _v _q h4872
  have p17087 := n17087 _v _q 
  have p17091 := n17091 _v _q 
  have p17094 := n17094 _v _q h4724
  have p17093 := n17093 _v _q 
  have p17111 := n17111 _v _q 
  have p17115 := n17115 _v _q 
  have p17089 := n17089 _v _q 
  have p17100 := n17100 _v _q 
  have p17098 := n17098 _v _q 
  have p17096 := n17096 _v _q 
  have p17110 := n17110 _v _q 
  have p17102 := n17102 _v _q 
  have p17104 := n17104 _v _q 
  have p17106 := n17106 _v _q 
  have p17108 := n17108 _v _q 
  have p13951 := n13951 _v _q 
  have p8663 := n8663 _v _q 
  have p20159 := n20159 _v _q h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h3976 h4059 h4156 h4199 h4306 h4369 h4398 h4434 h4491 h4567 h4608 h4653 h4675 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h5195 h5208 h6571 h7807 h8045
  have p8549 := n8549 _v _q h5195
  have p5391 := n5391 _v _q 
  have p20164 := n20164 _v _q h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h3976 h4059 h4156 h4199 h4306 h4369 h4398 h4434 h4491 h4567 h4608 h4653 h4675 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h5195 h5208 h6571 h7807 h8045
  exact FloorCertificate.node_20167 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2849 _v) (e2863 _v) (e2877 _v) (e2883 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p4016 p4994 p17117 p17255 p17113 p17120 p16977 p4987 p16929 p17786 p17009 p17122 p4991 p16576 p17124 p20155 p4999 p4996 p20162 p17147 p5003 p4998 p17127 p17276 p17128 p4983 p5008 p17256 p17129 p17175 p5006 p17159 p17131 p15373 p17133 p17134 p17136 p17157 p17137 p17138 p5007 p16778 p17141 p4992 p17143 p17050 p17053 p17055 p17056 p17058 p17060 p17061 p17064 p4995 p17067 p17069 p17072 p17074 p17076 p4985 p4988 p17078 p4986 p17080 p17083 p4984 p17087 p17091 p17094 p17093 p17111 p17115 p17089 p17100 p17098 p17096 p17110 p17102 p17104 p17106 p17108 p13951 p8663 p20159 p8549 p5391 p20164
theorem n20168 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4306 : (e4306 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4434 : (e4434 _v)) (h4491 : (e4491 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5100 : (e5100 _v)) (h5195 : (e5195 _v)) (h5208 : (e5208 _v)) (h6571 : (e6571 _v)) (h7807 : (e7807 _v)) (h8045 : (e8045 _v)) : (e4106 _v) := by
  have p17113 := n17113 _v _q 
  have p20159 := n20159 _v _q h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h3976 h4059 h4156 h4199 h4306 h4369 h4398 h4434 h4491 h4567 h4608 h4653 h4675 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h5195 h5208 h6571 h7807 h8045
  have p4016 := n4016 _v _q 
  have p4994 := n4994 _v _q h3069
  have p17117 := n17117 _v _q 
  have p17255 := n17255 _v _q h6571
  have p17120 := n17120 _v _q 
  have p4987 := n4987 _v _q h4434
  have p16929 := n16929 _v _q 
  have p17786 := n17786 _v _q h7807
  have p17009 := n17009 _v _q 
  have p17122 := n17122 _v _q 
  have p4991 := n4991 _v _q h4608
  have p16576 := n16576 _v _q 
  have p17124 := n17124 _v _q 
  have p20155 := n20155 _v _q h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h3976 h4156 h4199 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872 h4903 h5100 h5195 h7807
  have p4999 := n4999 _v _q h91
  have p4996 := n4996 _v _q h3937
  have p20162 := n20162 _v _q h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h3976 h4059 h4156 h4199 h4306 h4369 h4398 h4434 h4491 h4567 h4608 h4653 h4675 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h5195 h5208 h6571 h7807 h8045
  have p17147 := n17147 _v _q 
  have p5003 := n5003 _v _q h4199
  have p4998 := n4998 _v _q h3152
  have p17127 := n17127 _v _q 
  have p17276 := n17276 _v _q h5195
  have p17128 := n17128 _v _q h4491
  have p4983 := n4983 _v _q h4813
  have p5008 := n5008 _v _q h4787
  have p17256 := n17256 _v _q 
  have p17129 := n17129 _v _q h4903
  have p17175 := n17175 _v _q h5208
  have p5006 := n5006 _v _q h4675
  have p17159 := n17159 _v _q h5100
  have p17131 := n17131 _v _q 
  have p15373 := n15373 _v _q h7807
  have p17133 := n17133 _v _q 
  have p17134 := n17134 _v _q h4398
  have p17136 := n17136 _v _q 
  have p17157 := n17157 _v _q h8045
  have p17137 := n17137 _v _q h4059
  have p17138 := n17138 _v _q h4306
  have p5007 := n5007 _v _q h225
  have p16778 := n16778 _v _q 
  have p17141 := n17141 _v _q 
  have p4992 := n4992 _v _q h442
  have p17143 := n17143 _v _q h4567
  have p17050 := n17050 _v _q 
  have p17053 := n17053 _v _q 
  have p17055 := n17055 _v _q 
  have p17056 := n17056 _v _q h3946
  have p17058 := n17058 _v _q 
  have p17060 := n17060 _v _q h4653
  have p17061 := n17061 _v _q h4747
  have p17064 := n17064 _v _q 
  have p4995 := n4995 _v _q h4369
  have p17067 := n17067 _v _q 
  have p17069 := n17069 _v _q 
  have p17072 := n17072 _v _q 
  have p17074 := n17074 _v _q 
  have p17076 := n17076 _v _q h3976
  have p4985 := n4985 _v _q h4156
  have p4988 := n4988 _v _q h488
  have p17078 := n17078 _v _q 
  have p4986 := n4986 _v _q h3105
  have p17080 := n17080 _v _q 
  have p17083 := n17083 _v _q 
  have p4984 := n4984 _v _q h4872
  have p17087 := n17087 _v _q 
  have p17091 := n17091 _v _q 
  have p17094 := n17094 _v _q h4724
  have p17093 := n17093 _v _q 
  have p17111 := n17111 _v _q 
  have p17115 := n17115 _v _q 
  have p17089 := n17089 _v _q 
  have p17100 := n17100 _v _q 
  have p17098 := n17098 _v _q 
  have p17096 := n17096 _v _q 
  have p17110 := n17110 _v _q 
  have p17102 := n17102 _v _q 
  have p17104 := n17104 _v _q 
  have p17106 := n17106 _v _q 
  have p17108 := n17108 _v _q 
  have p13951 := n13951 _v _q 
  have p8663 := n8663 _v _q 
  have p8549 := n8549 _v _q h5195
  have p5391 := n5391 _v _q 
  have p20164 := n20164 _v _q h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h3976 h4059 h4156 h4199 h4306 h4369 h4398 h4434 h4491 h4567 h4608 h4653 h4675 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h5195 h5208 h6571 h7807 h8045
  exact FloorCertificate.node_20168 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2849 _v) (e2863 _v) (e2877 _v) (e2883 _v) (e2902 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p17113 p20159 p4016 p4994 p17117 p17255 p17120 p4987 p16929 p17786 p17009 p17122 p4991 p16576 p17124 p20155 p4999 p4996 p20162 p17147 p5003 p4998 p17127 p17276 p17128 p4983 p5008 p17256 p17129 p17175 p5006 p17159 p17131 p15373 p17133 p17134 p17136 p17157 p17137 p17138 p5007 p16778 p17141 p4992 p17143 p17050 p17053 p17055 p17056 p17058 p17060 p17061 p17064 p4995 p17067 p17069 p17072 p17074 p17076 p4985 p4988 p17078 p4986 p17080 p17083 p4984 p17087 p17091 p17094 p17093 p17111 p17115 p17089 p17100 p17098 p17096 p17110 p17102 p17104 p17106 p17108 p13951 p8663 p8549 p5391 p20164
theorem n20169 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e4398 _v) := by
  have p14976 := n14976 _v _q 
  have p19734 := n19734 _v _q h6784
  change (e4404 _v) ∨ (e4398 _v) at p14976
  change (¬ (e4404 _v)) at p19734
  rcases p14976 with hlit | hlit
  · exact (False.elim (p19734 hlit))
  · exact hlit
theorem n20170 (_v : Vars) (_q : Query _v) (h2061 : (e2061 _v)) (h6501 : (e6501 _v)) (h6784 : (e6784 _v)) : (e4221 _v) := by
  have p20166 := n20166 _v _q 
  have p16852 := n16852 _v _q h2061 h6784
  have p16513 := n16513 _v _q h6784
  have p15560 := n15560 _v _q h6784
  have p16598 := n16598 _v _q h6784
  have p16549 := n16549 _v _q h6784
  have p11409 := n11409 _v _q h2061
  have p19771 := n19771 _v _q h6784
  have p16607 := n16607 _v _q h6784
  have p16619 := n16619 _v _q h6784
  have p16620 := n16620 _v _q h6784
  have p16856 := n16856 _v _q h6784
  have p15705 := n15705 _v _q h6784
  have p19747 := n19747 _v _q h6784
  have p19750 := n19750 _v _q h6784
  have p15702 := n15702 _v _q h6784
  have p16857 := n16857 _v _q h2061 h6784
  have p19752 := n19752 _v _q h6784
  have p20169 := n20169 _v _q h6784
  have p16854 := n16854 _v _q h6784
  have p19772 := n19772 _v _q h6784
  have p15713 := n15713 _v _q h6784
  have p16625 := n16625 _v _q h6784
  have p16626 := n16626 _v _q h6784
  have p19758 := n19758 _v _q h6784
  have p19760 := n19760 _v _q h6784
  have p16603 := n16603 _v _q h6784
  have p16816 := n16816 _v _q h6784
  have p19762 := n19762 _v _q h6784
  have p8554 := n8554 _v _q h6501
  change (¬ (e4220 _v)) ∨ (¬ (e2061 _v)) ∨ (¬ (e4648 _v)) ∨ (¬ (e4899 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e4546 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e30 _v)) ∨ (¬ (e4285 _v)) ∨ (¬ (e4398 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4301 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4724 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4419 _v)) ∨ (¬ (e488 _v)) ∨ (e2179 _v) at p20166
  change (¬ (e2179 _v)) at p8554
  rcases p20166 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p11409))
  · exact (False.elim (hlit p16513))
  · exact (False.elim (hlit p15560))
  · exact (False.elim (hlit p16598))
  · exact (False.elim (hlit p16549))
  · exact (False.elim (hlit p16852))
  · exact (False.elim (hlit p19771))
  · exact (False.elim (hlit p16607))
  · exact (False.elim (hlit p16619))
  · exact (False.elim (hlit p16620))
  · exact (False.elim (hlit p16856))
  · exact (False.elim (hlit p15705))
  · exact (False.elim (hlit p19747))
  · exact (False.elim (hlit p19750))
  · exact (False.elim (hlit p15702))
  · exact (False.elim (hlit p16857))
  · exact (False.elim (hlit p19752))
  · exact (False.elim (hlit p20169))
  · exact (False.elim (hlit p16854))
  · exact (False.elim (hlit p19772))
  · exact (False.elim (hlit p15713))
  · exact (False.elim (hlit p16625))
  · exact (False.elim (hlit p16626))
  · exact (False.elim (hlit p19758))
  · exact (False.elim (hlit p19760))
  · exact (False.elim (hlit p16603))
  · exact (False.elim (hlit p16816))
  · exact (False.elim (hlit p19762))
  · exact (False.elim (p8554 hlit))
theorem n20171 (_v : Vars) (_q : Query _v) (h2061 : (e2061 _v)) (h6501 : (e6501 _v)) (h6784 : (e6784 _v)) : (e7733 _v) := by
  have p16334 := n16334 _v _q 
  have p20170 := n20170 _v _q h2061 h6501 h6784
  change (e7733 _v) ∨ (e4220 _v) at p16334
  change (¬ (e4220 _v)) at p20170
  rcases p16334 with hlit | hlit
  · exact hlit
  · exact (False.elim (p20170 hlit))
theorem n20172 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4306 : (e4306 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4434 : (e4434 _v)) (h4491 : (e4491 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5100 : (e5100 _v)) (h5195 : (e5195 _v)) (h5208 : (e5208 _v)) (h6571 : (e6571 _v)) (h7807 : (e7807 _v)) (h8045 : (e8045 _v)) : (e4108 _v) := by
  have p14929 := n14929 _v _q 
  have p20168 := n20168 _v _q h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h3976 h4059 h4156 h4199 h4306 h4369 h4398 h4434 h4491 h4567 h4608 h4653 h4675 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h5195 h5208 h6571 h7807 h8045
  change (e4108 _v) ∨ (e4101 _v) at p14929
  change (¬ (e4101 _v)) at p20168
  rcases p14929 with hlit | hlit
  · exact hlit
  · exact (False.elim (p20168 hlit))
theorem n20173 (_v : Vars) (_q : Query _v) (h2061 : (e2061 _v)) (h6501 : (e6501 _v)) (h6784 : (e6784 _v)) : (e7742 _v) := by
  have p14833 := n14833 _v _q 
  have p20171 := n20171 _v _q h2061 h6501 h6784
  change (¬ (e2132 _v)) ∨ (¬ (e7733 _v)) at p14833
  rcases p14833 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p20171))
theorem n20174 (_v : Vars) (_q : Query _v) (h2061 : (e2061 _v)) (h6501 : (e6501 _v)) (h6784 : (e6784 _v)) : (e7754 _v) := by
  have p14942 := n14942 _v _q 
  have p20173 := n20173 _v _q h2061 h6501 h6784
  change (e2132 _v) ∨ (¬ (e7753 _v)) at p14942
  change (¬ (e2132 _v)) at p20173
  rcases p14942 with hlit | hlit
  · exact (False.elim (p20173 hlit))
  · exact hlit
theorem n20175 (_v : Vars) (_q : Query _v) (h2061 : (e2061 _v)) (h6501 : (e6501 _v)) (h6784 : (e6784 _v)) : (e7749 _v) := by
  have p14941 := n14941 _v _q 
  have p20174 := n20174 _v _q h2061 h6501 h6784
  change (e7753 _v) ∨ (e7749 _v) at p14941
  change (¬ (e7753 _v)) at p20174
  rcases p14941 with hlit | hlit
  · exact (False.elim (p20174 hlit))
  · exact hlit
theorem n20176 (_v : Vars) (_q : Query _v) (h2061 : (e2061 _v)) (h6501 : (e6501 _v)) (h6784 : (e6784 _v)) : (e6700 _v) := by
  have p11473 := n11473 _v _q h6784
  have p20173 := n20173 _v _q h2061 h6501 h6784
  exact FloorCertificate.node_20176 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p11473 p20173
theorem n20177 (_v : Vars) (_q : Query _v) (h2061 : (e2061 _v)) (h6501 : (e6501 _v)) (h6784 : (e6784 _v)) : (e6896 _v) := by
  have p14360 := n14360 _v _q 
  have p20176 := n20176 _v _q h2061 h6501 h6784
  change (e2634 _v) ∨ (¬ (e6888 _v)) at p14360
  change (¬ (e2634 _v)) at p20176
  rcases p14360 with hlit | hlit
  · exact (False.elim (p20176 hlit))
  · exact hlit
theorem n20178 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4306 : (e4306 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4434 : (e4434 _v)) (h4491 : (e4491 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5100 : (e5100 _v)) (h5195 : (e5195 _v)) (h5208 : (e5208 _v)) (h6571 : (e6571 _v)) (h7807 : (e7807 _v)) (h8045 : (e8045 _v)) : (e7589 _v) := by
  have p15703 := n15703 _v _q 
  have p20167 := n20167 _v _q h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h3976 h4059 h4156 h4199 h4306 h4369 h4398 h4434 h4491 h4567 h4608 h4653 h4675 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h5195 h5208 h6571 h7807 h8045
  change (e7589 _v) ∨ (e4096 _v) at p15703
  change (¬ (e4096 _v)) at p20167
  rcases p15703 with hlit | hlit
  · exact hlit
  · exact (False.elim (p20167 hlit))
end
end Assembly
