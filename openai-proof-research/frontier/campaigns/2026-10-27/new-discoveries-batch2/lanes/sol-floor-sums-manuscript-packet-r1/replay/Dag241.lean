import Dag240
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n20910 (_v : Vars) (_q : Query _v) (h225 : (e225 _v)) (h4813 : (e4813 _v)) (h6423 : (e6423 _v)) : (e5145 _v) := by
  have p15925 := n15925 _v _q 
  have p20909 := n20909 _v _q h225 h4813 h6423
  change (e5149 _v) ∨ (e5145 _v) at p15925
  change (¬ (e5149 _v)) at p20909
  rcases p15925 with hlit | hlit
  · exact (False.elim (p20909 hlit))
  · exact hlit
theorem n20911 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h3152 : (e3152 _v)) (h4260 : (e4260 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h6454 : (e6454 _v)) : (e5118 _v) := by
  have p15648 := n15648 _v _q 
  have p20851 := n20851 _v _q h91 h3152 h4260 h4675 h4787 h4813 h6454
  change (e5118 _v) ∨ (e70 _v) at p15648
  change (¬ (e70 _v)) at p20851
  rcases p15648 with hlit | hlit
  · exact hlit
  · exact (False.elim (p20851 hlit))
theorem n20912 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h3152 : (e3152 _v)) (h4260 : (e4260 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h6454 : (e6454 _v)) : (e48 _v) := by
  have p14487 := n14487 _v _q 
  have p20911 := n20911 _v _q h91 h3152 h4260 h4675 h4787 h4813 h6454
  change (e48 _v) ∨ (¬ (e5118 _v)) at p14487
  rcases p14487 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p20911))
theorem n20913 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h3152 : (e3152 _v)) (h4260 : (e4260 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h6454 : (e6454 _v)) : (e2585 _v) := by
  have p11550 := n11550 _v _q 
  have p20912 := n20912 _v _q h91 h3152 h4260 h4675 h4787 h4813 h6454
  change (e2585 _v) ∨ (¬ (e48 _v)) at p11550
  rcases p11550 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p20912))
theorem n20915 (_v : Vars) (_q : Query _v)  : (e20914 _v) := by
  by_contra hc
  change ¬ ((¬ (e4419 _v)) ∨ (e2733 _v) ∨ (¬ (e2468 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e4679 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e3152 _v))) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h191 : (e191 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h2468 : (e2468 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))))))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h4419 : (e4419 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h4679 : (e4679 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h4838 : (e4838 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h6750 : (e6750 _v) := (fun hn => hc (Or.inr (Or.inl hn)))
  have p20856 := n20856 _v _q h51 h91 h191 h2468 h3152 h4306 h4419 h4653 h4679 h4813 h4838 h6750
  exact p20856
theorem n20917 (_v : Vars) (_q : Query _v)  : (e20916 _v) := by
  by_contra hc
  change ¬ ((¬ (e2303 _v)) ∨ (¬ (e4459 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4264 _v)) ∨ (¬ (e3919 _v)) ∨ (¬ (e4439 _v)) ∨ (¬ (e4101 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e4679 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e4791 _v)) ∨ (¬ (e4567 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e3158 _v))) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h191 : (e191 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h2303 : (e2303 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h3158 : (e3158 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))))))))))))))
  have h3919 : (e3919 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4101 : (e4101 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h4264 : (e4264 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h4439 : (e4439 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h4459 : (e4459 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h4567 : (e4567 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h4679 : (e4679 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h4791 : (e4791 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))
  have h4838 : (e4838 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))
  have p20857 := n20857 _v _q h51 h91 h191 h2303 h3152 h3158 h3919 h4101 h4264 h4306 h4439 h4459 h4567 h4653 h4679 h4791 h4813 h4838
  exact p20857
theorem n20919 (_v : Vars) (_q : Query _v)  : (e20918 _v) := by
  by_contra hc
  change ¬ ((¬ (e2787 _v)) ∨ (e2303 _v) ∨ (¬ (e4139 _v)) ∨ (¬ (e2402 _v)) ∨ (¬ (e4101 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e2242 _v)) ∨ (e2296 _v) ∨ (¬ (e4546 _v))) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h191 : (e191 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h2242 : (e2242 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h2402 : (e2402 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h2787 : (e2787 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h4101 : (e4101 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4139 : (e4139 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4260 : (e4260 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h4546 : (e4546 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn)))))))))))))))))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h4838 : (e4838 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h6549 : (e6549 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))
  have h7807 : (e7807 _v) := (fun hn => hc (Or.inr (Or.inl hn)))
  have p20858 := n20858 _v _q h51 h91 h191 h2242 h2402 h2787 h4101 h4139 h4260 h4306 h4546 h4653 h4787 h4813 h4838 h6549 h7807
  exact p20858
theorem n20921 (_v : Vars) (_q : Query _v)  : (e20920 _v) := by
  by_contra hc
  change ¬ ((e2303 _v) ∨ (e2475 _v) ∨ (¬ (e4101 _v)) ∨ (¬ (e2402 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e7935 _v)) ∨ (¬ (e2242 _v)) ∨ (e2781 _v)) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h191 : (e191 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h2242 : (e2242 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h2402 : (e2402 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4101 : (e4101 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h4838 : (e4838 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h6776 : (e6776 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))))))))))))
  have h7807 : (e7807 _v) := (fun hn => hc (Or.inl hn))
  have h7935 : (e7935 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h8038 : (e8038 _v) := (fun hn => hc (Or.inr (Or.inl hn)))
  have p20859 := n20859 _v _q h51 h91 h191 h2242 h2402 h3152 h4101 h4306 h4653 h4787 h4813 h4838 h6776 h7807 h7935 h8038
  exact p20859
theorem n20923 (_v : Vars) (_q : Query _v)  : (e20922 _v) := by
  by_contra hc
  change ¬ ((e2402 _v) ∨ (¬ (e2358 _v)) ∨ (¬ (e2296 _v)) ∨ (¬ (e4546 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4264 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4679 _v)) ∨ (¬ (e4567 _v)) ∨ (¬ (e3158 _v)) ∨ (¬ (e4439 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4459 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e191 _v))) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))
  have h191 : (e191 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))))))))))))))
  have h2296 : (e2296 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h2358 : (e2358 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h3158 : (e3158 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h4264 : (e4264 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4439 : (e4439 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h4459 : (e4459 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))
  have h4546 : (e4546 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4567 : (e4567 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h4679 : (e4679 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h4838 : (e4838 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h6600 : (e6600 _v) := (fun hn => hc (Or.inl hn))
  have p20860 := n20860 _v _q h51 h91 h191 h2296 h2358 h3158 h4264 h4306 h4439 h4459 h4546 h4567 h4653 h4679 h4787 h4813 h4838 h6600
  exact p20860
theorem n20924 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2296 : (e2296 _v)) (h3158 : (e3158 _v)) (h4306 : (e4306 _v)) (h4439 : (e4439 _v)) (h4459 : (e4459 _v)) (h4567 : (e4567 _v)) (h4653 : (e4653 _v)) (h4679 : (e4679 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6600 : (e6600 _v)) (h6776 : (e6776 _v)) : (e7944 _v) := by
  have p15266 := n15266 _v _q 
  have p20861 := n20861 _v _q h51 h91 h191 h2296 h3158 h4306 h4439 h4459 h4567 h4653 h4679 h4787 h4813 h4838 h6600 h6776
  change (e7944 _v) ∨ (e7935 _v) at p15266
  change (¬ (e7935 _v)) at p20861
  rcases p15266 with hlit | hlit
  · exact hlit
  · exact (False.elim (p20861 hlit))
theorem n20926 (_v : Vars) (_q : Query _v)  : (e20925 _v) := by
  by_contra hc
  change ¬ ((¬ (e3937 _v)) ∨ (e2296 _v) ∨ (e2303 _v) ∨ (¬ (e4264 _v)) ∨ (¬ (e8045 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e4567 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4679 _v)) ∨ (¬ (e4101 _v)) ∨ (¬ (e3158 _v)) ∨ (¬ (e4439 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4459 _v)) ∨ (¬ (e91 _v))) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn)))))))))))))))))))
  have h191 : (e191 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h3158 : (e3158 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h4101 : (e4101 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h4264 : (e4264 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h4439 : (e4439 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))
  have h4459 : (e4459 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))
  have h4567 : (e4567 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h4679 : (e4679 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h4838 : (e4838 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h6549 : (e6549 _v) := (fun hn => hc (Or.inr (Or.inl hn)))
  have h7807 : (e7807 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h8045 : (e8045 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have p20863 := n20863 _v _q h51 h91 h191 h3158 h3937 h4101 h4264 h4306 h4439 h4459 h4567 h4653 h4679 h4787 h4813 h4838 h6549 h7807 h8045
  exact p20863
theorem n20927 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2242 : (e2242 _v)) (h2733 : (e2733 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6571 : (e6571 _v)) (h6776 : (e6776 _v)) (h7814 : (e7814 _v)) : (e8049 _v) := by
  have p15206 := n15206 _v _q 
  have p20865 := n20865 _v _q h51 h91 h191 h2242 h2733 h3152 h3937 h4306 h4653 h4787 h4813 h4838 h6571 h6776 h7814
  change (e8049 _v) ∨ (e8045 _v) at p15206
  change (¬ (e8045 _v)) at p20865
  rcases p15206 with hlit | hlit
  · exact hlit
  · exact (False.elim (p20865 hlit))
theorem n20929 (_v : Vars) (_q : Query _v)  : (e20928 _v) := by
  by_contra hc
  change ¬ ((¬ (e2781 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e1995 _v)) ∨ (e2061 _v) ∨ (¬ (e4813 _v)) ∨ (¬ (e5145 _v)) ∨ (e2303 _v) ∨ (¬ (e4787 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4306 _v)) ∨ (e2529 _v)) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h1995 : (e1995 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h2781 : (e2781 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h5145 : (e5145 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h6454 : (e6454 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h7807 : (e7807 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h8310 : (e8310 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn)))))))))))
  have p20867 := n20867 _v _q h51 h1995 h2781 h4306 h4653 h4787 h4813 h5145 h6454 h7807 h8310
  exact p20867
theorem n20931 (_v : Vars) (_q : Query _v)  : (e20930 _v) := by
  by_contra hc
  change ¬ ((e2585 _v) ∨ (¬ (e2364 _v)) ∨ (¬ (e7935 _v)) ∨ (e48 _v) ∨ (¬ (e4813 _v)) ∨ (¬ (e7749 _v)) ∨ (¬ (e7814 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e7493 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e5100 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e4562 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e3937 _v)) ∨ (e79 _v)) at hc
  have h2364 : (e2364 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))
  have h4260 : (e4260 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h4434 : (e4434 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))
  have h4562 : (e4562 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h4608 : (e4608 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h4675 : (e4675 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h5100 : (e5100 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h5108 : (e5108 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h5138 : (e5138 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))))))))))))))
  have h6676 : (e6676 _v) := (fun hn => hc (Or.inl hn))
  have h7493 : (e7493 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h7749 : (e7749 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h7814 : (e7814 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h7935 : (e7935 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have p20874 := n20874 _v _q h2364 h3152 h3937 h4260 h4434 h4562 h4608 h4675 h4787 h4813 h5100 h5108 h5138 h6676 h7493 h7749 h7814 h7935
  exact p20874
theorem n20932 (_v : Vars) (_q : Query _v) (h5108 : (e5108 _v)) (h6423 : (e6423 _v)) : (e5138 _v) := by
  have p14729 := n14729 _v _q 
  have p20873 := n20873 _v _q h5108 h6423
  change (¬ (e79 _v)) ∨ (¬ (e5134 _v)) at p14729
  rcases p14729 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p20873))
theorem n20933 (_v : Vars) (_q : Query _v) (h5108 : (e5108 _v)) (h6423 : (e6423 _v)) : (e8317 _v) := by
  have p17001 := n17001 _v _q 
  have p20932 := n20932 _v _q h5108 h6423
  change (e8317 _v) ∨ (e79 _v) at p17001
  change (¬ (e79 _v)) at p20932
  rcases p17001 with hlit | hlit
  · exact hlit
  · exact (False.elim (p20932 hlit))
theorem n20934 (_v : Vars) (_q : Query _v) (h5108 : (e5108 _v)) (h6423 : (e6423 _v)) : (e8038 _v) := by
  have p11510 := n11510 _v _q 
  have p20932 := n20932 _v _q h5108 h6423
  change (e79 _v) ∨ (¬ (e2475 _v)) at p11510
  change (¬ (e79 _v)) at p20932
  rcases p11510 with hlit | hlit
  · exact (False.elim (p20932 hlit))
  · exact hlit
theorem n20935 (_v : Vars) (_q : Query _v) (h5108 : (e5108 _v)) (h6423 : (e6423 _v)) : (e8050 _v) := by
  have p15207 := n15207 _v _q 
  have p20934 := n20934 _v _q h5108 h6423
  change (e2475 _v) ∨ (¬ (e8049 _v)) at p15207
  change (¬ (e2475 _v)) at p20934
  rcases p15207 with hlit | hlit
  · exact (False.elim (p20934 hlit))
  · exact hlit
theorem n20936 (_v : Vars) (_q : Query _v) (h5108 : (e5108 _v)) (h6423 : (e6423 _v)) : (e5150 _v) := by
  have p15115 := n15115 _v _q 
  have p20932 := n20932 _v _q h5108 h6423
  change (e79 _v) ∨ (¬ (e5149 _v)) at p15115
  change (¬ (e79 _v)) at p20932
  rcases p15115 with hlit | hlit
  · exact (False.elim (p20932 hlit))
  · exact hlit
theorem n20937 (_v : Vars) (_q : Query _v) (h5108 : (e5108 _v)) (h6423 : (e6423 _v)) : (e5145 _v) := by
  have p15925 := n15925 _v _q 
  have p20936 := n20936 _v _q h5108 h6423
  change (e5149 _v) ∨ (e5145 _v) at p15925
  change (¬ (e5149 _v)) at p20936
  rcases p15925 with hlit | hlit
  · exact (False.elim (p20936 hlit))
  · exact hlit
theorem n20938 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2242 : (e2242 _v)) (h2303 : (e2303 _v)) (h3152 : (e3152 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6600 : (e6600 _v)) (h8045 : (e8045 _v)) : (e6772 _v) := by
  have p20884 := n20884 _v _q 
  have p16436 := n16436 _v _q h2303
  have p4979 := n4979 _v _q h4139
  have p4998 := n4998 _v _q h3152
  have p4981 := n4981 _v _q h4260
  have p17157 := n17157 _v _q h8045
  have p253 := n253 _v _q h191
  have p8439 := n8439 _v _q h6600
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4989 := n4989 _v _q h4838
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p5008 := n5008 _v _q h4787
  have p4999 := n4999 _v _q h91
  have p5001 := n5001 _v _q h4096
  have p8553 := n8553 _v _q h2242
  change (¬ (e2787 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4285 _v)) ∨ (¬ (e8045 _v)) ∨ (¬ (e191 _v)) ∨ (e2402 _v) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e2242 _v)) at p20884
  change (¬ (e2402 _v)) at p8439
  rcases p20884 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p4981))
  · exact (False.elim (hlit p4979))
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p16436))
  · exact (False.elim (hlit p17157))
  · exact (False.elim (hlit p253))
  · exact (False.elim (p8439 hlit))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p4989))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p5001))
  · exact (False.elim (hlit p8553))
theorem n20939 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2242 : (e2242 _v)) (h2303 : (e2303 _v)) (h3152 : (e3152 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6600 : (e6600 _v)) (h8045 : (e8045 _v)) : (e7945 _v) := by
  have p15228 := n15228 _v _q 
  have p20938 := n20938 _v _q h51 h91 h191 h2242 h2303 h3152 h4096 h4139 h4260 h4306 h4653 h4787 h4813 h4838 h6600 h8045
  change (e2787 _v) ∨ (¬ (e7944 _v)) at p15228
  change (¬ (e2787 _v)) at p20938
  rcases p15228 with hlit | hlit
  · exact (False.elim (p20938 hlit))
  · exact hlit
theorem n20940 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2242 : (e2242 _v)) (h3152 : (e3152 _v)) (h4096 : (e4096 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6600 : (e6600 _v)) (h6776 : (e6776 _v)) (h8038 : (e8038 _v)) : (e2358 _v) := by
  have p20886 := n20886 _v _q 
  have p15209 := n15209 _v _q h8038
  have p4998 := n4998 _v _q h3152
  have p8601 := n8601 _v _q h6776
  have p253 := n253 _v _q h191
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4989 := n4989 _v _q h4838
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p5008 := n5008 _v _q h4787
  have p4999 := n4999 _v _q h91
  have p5001 := n5001 _v _q h4096
  have p8553 := n8553 _v _q h2242
  have p15907 := n15907 _v _q h6600
  change (e2358 _v) ∨ (e2781 _v) ∨ (¬ (e3152 _v)) ∨ (¬ (e8045 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e2242 _v)) ∨ (¬ (e3937 _v)) at p20886
  change (¬ (e2781 _v)) at p8601
  rcases p20886 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (p8601 hlit))
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p15209))
  · exact (False.elim (hlit p253))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p4989))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p5001))
  · exact (False.elim (hlit p8553))
  · exact (False.elim (hlit p15907))
theorem n20941 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4434 : (e4434 _v)) (h4562 : (e4562 _v)) (h4608 : (e4608 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h5100 : (e5100 _v)) (h5145 : (e5145 _v)) (h6750 : (e6750 _v)) (h7749 : (e7749 _v)) (h7814 : (e7814 _v)) (h7935 : (e7935 _v)) (h8045 : (e8045 _v)) (h8317 : (e8317 _v)) : (e196 _v) := by
  have p20890 := n20890 _v _q 
  have p8420 := n8420 _v _q h6750
  have p16729 := n16729 _v _q h51
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p17163 := n17163 _v _q h7935
  have p17174 := n17174 _v _q h8317
  have p4983 := n4983 _v _q h4813
  have p16269 := n16269 _v _q h7749
  have p17157 := n17157 _v _q h8045
  have p17172 := n17172 _v _q h7814
  have p4998 := n4998 _v _q h3152
  have p4981 := n4981 _v _q h4260
  have p5006 := n5006 _v _q h4675
  have p17159 := n17159 _v _q h5100
  have p4991 := n4991 _v _q h4608
  have p17245 := n17245 _v _q h5145
  have p4973 := n4973 _v _q h4562
  have p5008 := n5008 _v _q h4787
  have p4987 := n4987 _v _q h4434
  have p4996 := n4996 _v _q h3937
  change (e196 _v) ∨ (¬ (e51 _v)) ∨ (e2733 _v) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e7935 _v)) ∨ (¬ (e8317 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e7749 _v)) ∨ (¬ (e8045 _v)) ∨ (¬ (e7814 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e5100 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e5145 _v)) ∨ (¬ (e4562 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e3937 _v)) at p20890
  change (¬ (e2733 _v)) at p8420
  rcases p20890 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p16729))
  · exact (False.elim (p8420 hlit))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p17163))
  · exact (False.elim (hlit p17174))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p16269))
  · exact (False.elim (hlit p17157))
  · exact (False.elim (hlit p17172))
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p4981))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p17159))
  · exact (False.elim (hlit p4991))
  · exact (False.elim (hlit p17245))
  · exact (False.elim (hlit p4973))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p4987))
  · exact (False.elim (hlit p4996))
theorem n20942 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4434 : (e4434 _v)) (h4562 : (e4562 _v)) (h4608 : (e4608 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h5100 : (e5100 _v)) (h5145 : (e5145 _v)) (h6750 : (e6750 _v)) (h7749 : (e7749 _v)) (h7814 : (e7814 _v)) (h7935 : (e7935 _v)) (h8045 : (e8045 _v)) (h8317 : (e8317 _v)) : (e5203 _v) := by
  have p14730 := n14730 _v _q 
  have p20941 := n20941 _v _q h51 h3152 h3937 h4260 h4306 h4434 h4562 h4608 h4653 h4675 h4787 h4813 h5100 h5145 h6750 h7749 h7814 h7935 h8045 h8317
  change (¬ (e196 _v)) ∨ (¬ (e5193 _v)) at p14730
  rcases p14730 with hlit | hlit
  · exact (False.elim (hlit p20941))
  · exact hlit
theorem n20943 (_v : Vars) (_q : Query _v) (h6423 : (e6423 _v)) (h6583 : (e6583 _v)) : (e7921 _v) := by
  have p16347 := n16347 _v _q 
  have p20894 := n20894 _v _q h6423 h6583
  change (e7921 _v) ∨ (e4419 _v) at p16347
  change (¬ (e4419 _v)) at p20894
  rcases p16347 with hlit | hlit
  · exact hlit
  · exact (False.elim (p20894 hlit))
theorem n20944 (_v : Vars) (_q : Query _v) (h6423 : (e6423 _v)) (h6583 : (e6583 _v)) : (e6772 _v) := by
  have p14855 := n14855 _v _q 
  have p20943 := n20943 _v _q h6423 h6583
  change (¬ (e2787 _v)) ∨ (¬ (e7921 _v)) at p14855
  rcases p14855 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p20943))
theorem n20945 (_v : Vars) (_q : Query _v) (h6423 : (e6423 _v)) (h6583 : (e6583 _v)) : (e7945 _v) := by
  have p15228 := n15228 _v _q 
  have p20944 := n20944 _v _q h6423 h6583
  change (e2787 _v) ∨ (¬ (e7944 _v)) at p15228
  change (¬ (e2787 _v)) at p20944
  rcases p15228 with hlit | hlit
  · exact (False.elim (p20944 hlit))
  · exact hlit
theorem n20946 (_v : Vars) (_q : Query _v) (h6423 : (e6423 _v)) (h6583 : (e6583 _v)) : (e7517 _v) := by
  have p15196 := n15196 _v _q 
  have p20899 := n20899 _v _q h6423 h6583
  change (e2691 _v) ∨ (¬ (e7497 _v)) at p15196
  change (¬ (e2691 _v)) at p20899
  rcases p15196 with hlit | hlit
  · exact (False.elim (p20899 hlit))
  · exact hlit
theorem n20947 (_v : Vars) (_q : Query _v) (h6423 : (e6423 _v)) (h6583 : (e6583 _v)) : (e7493 _v) := by
  have p15195 := n15195 _v _q 
  have p20946 := n20946 _v _q h6423 h6583
  change (e7497 _v) ∨ (e7493 _v) at p15195
  change (¬ (e7497 _v)) at p20946
  rcases p15195 with hlit | hlit
  · exact (False.elim (p20946 hlit))
  · exact hlit
theorem n20948 (_v : Vars) (_q : Query _v) (h6423 : (e6423 _v)) (h6583 : (e6583 _v)) : (e7754 _v) := by
  have p14942 := n14942 _v _q 
  have p20903 := n20903 _v _q h6423 h6583
  change (e2132 _v) ∨ (¬ (e7753 _v)) at p14942
  change (¬ (e2132 _v)) at p20903
  rcases p14942 with hlit | hlit
  · exact (False.elim (p20903 hlit))
  · exact hlit
theorem n20949 (_v : Vars) (_q : Query _v) (h6423 : (e6423 _v)) (h6583 : (e6583 _v)) : (e7749 _v) := by
  have p14941 := n14941 _v _q 
  have p20948 := n20948 _v _q h6423 h6583
  change (e7753 _v) ∨ (e7749 _v) at p14941
  change (¬ (e7753 _v)) at p20948
  rcases p14941 with hlit | hlit
  · exact (False.elim (p20948 hlit))
  · exact hlit
theorem n20950 (_v : Vars) (_q : Query _v) (h6423 : (e6423 _v)) (h6583 : (e6583 _v)) : (e5105 _v) := by
  have p15204 := n15204 _v _q 
  have p20902 := n20902 _v _q h6423 h6583
  change (e13 _v) ∨ (¬ (e5104 _v)) at p15204
  change (¬ (e13 _v)) at p20902
  rcases p15204 with hlit | hlit
  · exact (False.elim (p20902 hlit))
  · exact hlit
theorem n20951 (_v : Vars) (_q : Query _v) (h6423 : (e6423 _v)) (h6583 : (e6583 _v)) : (e5100 _v) := by
  have p15319 := n15319 _v _q 
  have p20950 := n20950 _v _q h6423 h6583
  change (e5104 _v) ∨ (e5100 _v) at p15319
  change (¬ (e5104 _v)) at p20950
  rcases p15319 with hlit | hlit
  · exact (False.elim (p20950 hlit))
  · exact hlit
theorem n20952 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h3152 : (e3152 _v)) (h4260 : (e4260 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h6454 : (e6454 _v)) : (e2364 _v) := by
  have p11343 := n11343 _v _q 
  have p20913 := n20913 _v _q h91 h3152 h4260 h4675 h4787 h4813 h6454
  change (e2364 _v) ∨ (¬ (e2585 _v)) at p11343
  rcases p11343 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p20913))
theorem n20953 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h3152 : (e3152 _v)) (h4260 : (e4260 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h6454 : (e6454 _v)) : (e7742 _v) := by
  have p11546 := n11546 _v _q 
  have p20952 := n20952 _v _q h91 h3152 h4260 h4675 h4787 h4813 h6454
  have p8430 := n8430 _v _q h6454
  change (¬ (e2132 _v)) ∨ (¬ (e2364 _v)) ∨ (e2061 _v) at p11546
  change (¬ (e2061 _v)) at p8430
  rcases p11546 with hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p20952))
  · exact (False.elim (p8430 hlit))
theorem n20954 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h3152 : (e3152 _v)) (h4260 : (e4260 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h6454 : (e6454 _v)) : (e8038 _v) := by
  have p8574 := n8574 _v _q 
  have p20913 := n20913 _v _q h91 h3152 h4260 h4675 h4787 h4813 h6454
  have p8430 := n8430 _v _q h6454
  change (¬ (e2475 _v)) ∨ (¬ (e2585 _v)) ∨ (e2061 _v) at p8574
  change (¬ (e2061 _v)) at p8430
  rcases p8574 with hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p20913))
  · exact (False.elim (p8430 hlit))
theorem n20955 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h3152 : (e3152 _v)) (h4260 : (e4260 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h6454 : (e6454 _v)) : (e8050 _v) := by
  have p15207 := n15207 _v _q 
  have p20954 := n20954 _v _q h91 h3152 h4260 h4675 h4787 h4813 h6454
  change (e2475 _v) ∨ (¬ (e8049 _v)) at p15207
  change (¬ (e2475 _v)) at p20954
  rcases p15207 with hlit | hlit
  · exact (False.elim (p20954 hlit))
  · exact hlit
theorem n20956 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h3152 : (e3152 _v)) (h4260 : (e4260 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h6454 : (e6454 _v)) : (e5093 _v) := by
  have p11399 := n11399 _v _q 
  have p20954 := n20954 _v _q h91 h3152 h4260 h4675 h4787 h4813 h6454
  change (¬ (e13 _v)) ∨ (e2475 _v) at p11399
  change (¬ (e2475 _v)) at p20954
  rcases p11399 with hlit | hlit
  · exact hlit
  · exact (False.elim (p20954 hlit))
theorem n20957 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2468 : (e2468 _v)) (h3152 : (e3152 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4679 : (e4679 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6750 : (e6750 _v)) : (e4420 _v) := by
  have p20915 := n20915 _v _q 
  have p4998 := n4998 _v _q h3152
  have p8438 := n8438 _v _q h2468
  have p4999 := n4999 _v _q h91
  have p17070 := n17070 _v _q h4679
  have p253 := n253 _v _q h191
  have p16729 := n16729 _v _q h51
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4989 := n4989 _v _q h4838
  have p4983 := n4983 _v _q h4813
  have p8420 := n8420 _v _q h6750
  change (¬ (e4419 _v)) ∨ (e2733 _v) ∨ (¬ (e2468 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e4679 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e3152 _v)) at p20915
  change (¬ (e2733 _v)) at p8420
  rcases p20915 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (p8420 hlit))
  · exact (False.elim (hlit p8438))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p17070))
  · exact (False.elim (hlit p253))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p4989))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p4998))
theorem n20958 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2468 : (e2468 _v)) (h3152 : (e3152 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4679 : (e4679 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6750 : (e6750 _v)) : (e7921 _v) := by
  have p16347 := n16347 _v _q 
  have p20957 := n20957 _v _q h51 h91 h191 h2468 h3152 h4306 h4653 h4679 h4813 h4838 h6750
  change (e7921 _v) ∨ (e4419 _v) at p16347
  change (¬ (e4419 _v)) at p20957
  rcases p16347 with hlit | hlit
  · exact hlit
  · exact (False.elim (p20957 hlit))
theorem n20959 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2242 : (e2242 _v)) (h2402 : (e2402 _v)) (h4101 : (e4101 _v)) (h4139 : (e4139 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4546 : (e4546 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6549 : (e6549 _v)) (h7807 : (e7807 _v)) : (e6772 _v) := by
  have p20919 := n20919 _v _q 
  have p11350 := n11350 _v _q h7807
  have p4979 := n4979 _v _q h4139
  have p8591 := n8591 _v _q h2402
  have p17065 := n17065 _v _q h4101
  have p4981 := n4981 _v _q h4260
  have p4999 := n4999 _v _q h91
  have p253 := n253 _v _q h191
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4989 := n4989 _v _q h4838
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p5008 := n5008 _v _q h4787
  have p8553 := n8553 _v _q h2242
  have p8544 := n8544 _v _q h6549
  have p4976 := n4976 _v _q h4546
  change (¬ (e2787 _v)) ∨ (e2303 _v) ∨ (¬ (e4139 _v)) ∨ (¬ (e2402 _v)) ∨ (¬ (e4101 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e2242 _v)) ∨ (e2296 _v) ∨ (¬ (e4546 _v)) at p20919
  change (¬ (e2303 _v)) at p11350
  change (¬ (e2296 _v)) at p8544
  rcases p20919 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (p11350 hlit))
  · exact (False.elim (hlit p4979))
  · exact (False.elim (hlit p8591))
  · exact (False.elim (hlit p17065))
  · exact (False.elim (hlit p4981))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p253))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p4989))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p8553))
  · exact (False.elim (p8544 hlit))
  · exact (False.elim (hlit p4976))
theorem n20960 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2242 : (e2242 _v)) (h2402 : (e2402 _v)) (h4101 : (e4101 _v)) (h4139 : (e4139 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4546 : (e4546 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6549 : (e6549 _v)) (h7807 : (e7807 _v)) : (e7945 _v) := by
  have p15228 := n15228 _v _q 
  have p20959 := n20959 _v _q h51 h91 h191 h2242 h2402 h4101 h4139 h4260 h4306 h4546 h4653 h4787 h4813 h4838 h6549 h7807
  change (e2787 _v) ∨ (¬ (e7944 _v)) at p15228
  change (¬ (e2787 _v)) at p20959
  rcases p15228 with hlit | hlit
  · exact (False.elim (p20959 hlit))
  · exact hlit
theorem n20961 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2242 : (e2242 _v)) (h2402 : (e2402 _v)) (h3152 : (e3152 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6776 : (e6776 _v)) (h7935 : (e7935 _v)) (h8038 : (e8038 _v)) : (e2303 _v) := by
  have p20921 := n20921 _v _q 
  have p17163 := n17163 _v _q h7935
  have p17065 := n17065 _v _q h4101
  have p8591 := n8591 _v _q h2402
  have p4998 := n4998 _v _q h3152
  have p4999 := n4999 _v _q h91
  have p253 := n253 _v _q h191
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4989 := n4989 _v _q h4838
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p5008 := n5008 _v _q h4787
  have p8602 := n8602 _v _q h8038
  have p8553 := n8553 _v _q h2242
  have p8601 := n8601 _v _q h6776
  change (e2303 _v) ∨ (e2475 _v) ∨ (¬ (e4101 _v)) ∨ (¬ (e2402 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e7935 _v)) ∨ (¬ (e2242 _v)) ∨ (e2781 _v) at p20921
  change (¬ (e2475 _v)) at p8602
  change (¬ (e2781 _v)) at p8601
  rcases p20921 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (p8602 hlit))
  · exact (False.elim (hlit p17065))
  · exact (False.elim (hlit p8591))
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p253))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p4989))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p17163))
  · exact (False.elim (hlit p8553))
  · exact (False.elim (p8601 hlit))
theorem n20962 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2242 : (e2242 _v)) (h2402 : (e2402 _v)) (h3152 : (e3152 _v)) (h4101 : (e4101 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6776 : (e6776 _v)) (h7935 : (e7935 _v)) (h8038 : (e8038 _v)) : (e7804 _v) := by
  have p14837 := n14837 _v _q 
  have p20961 := n20961 _v _q h51 h91 h191 h2242 h2402 h3152 h4101 h4306 h4653 h4787 h4813 h4838 h6776 h7935 h8038
  change (¬ (e2303 _v)) ∨ (¬ (e7798 _v)) at p14837
  rcases p14837 with hlit | hlit
  · exact (False.elim (hlit p20961))
  · exact hlit
end
end Assembly
