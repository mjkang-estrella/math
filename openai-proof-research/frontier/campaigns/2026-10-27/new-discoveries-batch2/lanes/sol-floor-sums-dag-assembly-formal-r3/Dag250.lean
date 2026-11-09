import Dag249
import generated.th_lemma_33
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n21367 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h3152 : (e3152 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4813 : (e4813 _v)) (h6501 : (e6501 _v)) (h6750 : (e6750 _v)) (h7807 : (e7807 _v)) : (e4547 _v) := by
  have p21307 := n21307 _v _q 
  have p11350 := n11350 _v _q h7807
  have p15940 := n15940 _v _q h6750
  have p21355 := n21355 _v _q h51 h91 h2529 h3152 h4260 h4306 h4653 h4675 h4813 h6501 h6750
  have p4981 := n4981 _v _q h4260
  have p21190 := n21190 _v _q h51 h91 h2529 h4306 h4653 h4813
  have p5006 := n5006 _v _q h4675
  have p4998 := n4998 _v _q h3152
  have p4999 := n4999 _v _q h91
  have p16705 := n16705 _v _q h2529
  have p16729 := n16729 _v _q h51
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p16572 := n16572 _v _q h2529
  have p4983 := n4983 _v _q h4813
  have p8554 := n8554 _v _q h6501
  change (¬ (e4546 _v)) ∨ (e2179 _v) ∨ (¬ (e4096 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4813 _v)) ∨ (e2303 _v) at p21307
  change (¬ (e2303 _v)) at p11350
  change (¬ (e2179 _v)) at p8554
  rcases p21307 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (p8554 hlit))
  · exact (False.elim (hlit p15940))
  · exact (False.elim (hlit p21355))
  · exact (False.elim (hlit p4981))
  · exact (False.elim (hlit p21190))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p16705))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p16572))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (p11350 hlit))
theorem n21368 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h3152 : (e3152 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4813 : (e4813 _v)) (h6501 : (e6501 _v)) (h6750 : (e6750 _v)) (h7807 : (e7807 _v)) : (e8029 _v) := by
  have p16307 := n16307 _v _q 
  have p21367 := n21367 _v _q h51 h91 h2529 h3152 h4260 h4306 h4653 h4675 h4813 h6501 h6750 h7807
  change (e8029 _v) ∨ (e4546 _v) at p16307
  change (¬ (e4546 _v)) at p21367
  rcases p16307 with hlit | hlit
  · exact hlit
  · exact (False.elim (p21367 hlit))
theorem n21370 (_v : Vars) (_q : Query _v)  : (e21369 _v) := by
  by_contra hc
  change ¬ ((e2787 _v) ∨ (¬ (e2179 _v)) ∨ (e2733 _v) ∨ (e2242 _v) ∨ (¬ (e4260 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e3919 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e2303 _v))) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h191 : (e191 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h2179 : (e2179 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h2303 : (e2303 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn)))))))))))))))
  have h3919 : (e3919 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h4260 : (e4260 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h4838 : (e4838 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h6525 : (e6525 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h6750 : (e6750 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h6772 : (e6772 _v) := (fun hn => hc (Or.inl hn))
  have p21362 := n21362 _v _q h51 h91 h191 h2179 h2303 h3919 h4260 h4306 h4653 h4787 h4813 h4838 h6525 h6750 h6772
  exact p21362
theorem n21371 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2242 : (e2242 _v)) (h3152 : (e3152 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6630 : (e6630 _v)) (h6750 : (e6750 _v)) (h6776 : (e6776 _v)) : (e2475 _v) := by
  have p15207 := n15207 _v _q 
  have p21364 := n21364 _v _q h51 h91 h191 h2242 h3152 h4306 h4653 h4813 h4838 h6630 h6750 h6776
  change (e2475 _v) ∨ (¬ (e8049 _v)) at p15207
  rcases p15207 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p21364))
theorem n21372 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2242 : (e2242 _v)) (h3152 : (e3152 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6630 : (e6630 _v)) (h6750 : (e6750 _v)) (h6776 : (e6776 _v)) : (e8035 _v) := by
  have p14871 := n14871 _v _q 
  have p21371 := n21371 _v _q h51 h91 h191 h2242 h3152 h4306 h4653 h4813 h4838 h6630 h6750 h6776
  change (¬ (e2475 _v)) ∨ (¬ (e8029 _v)) at p14871
  rcases p14871 with hlit | hlit
  · exact (False.elim (hlit p21371))
  · exact hlit
theorem n21373 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h3152 : (e3152 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4813 : (e4813 _v)) (h6501 : (e6501 _v)) (h6750 : (e6750 _v)) (h7807 : (e7807 _v)) : (e8038 _v) := by
  have p14871 := n14871 _v _q 
  have p21368 := n21368 _v _q h51 h91 h2529 h3152 h4260 h4306 h4653 h4675 h4813 h6501 h6750 h7807
  change (¬ (e2475 _v)) ∨ (¬ (e8029 _v)) at p14871
  rcases p14871 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p21368))
theorem n21374 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h3152 : (e3152 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4813 : (e4813 _v)) (h6501 : (e6501 _v)) (h6750 : (e6750 _v)) (h7807 : (e7807 _v)) : (e8050 _v) := by
  have p15207 := n15207 _v _q 
  have p21373 := n21373 _v _q h51 h91 h2529 h3152 h4260 h4306 h4653 h4675 h4813 h6501 h6750 h7807
  change (e2475 _v) ∨ (¬ (e8049 _v)) at p15207
  change (¬ (e2475 _v)) at p21373
  rcases p15207 with hlit | hlit
  · exact (False.elim (p21373 hlit))
  · exact hlit
theorem n21375 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h3152 : (e3152 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4813 : (e4813 _v)) (h6501 : (e6501 _v)) (h6750 : (e6750 _v)) (h7807 : (e7807 _v)) : (e8045 _v) := by
  have p15206 := n15206 _v _q 
  have p21374 := n21374 _v _q h51 h91 h2529 h3152 h4260 h4306 h4653 h4675 h4813 h6501 h6750 h7807
  change (e8049 _v) ∨ (e8045 _v) at p15206
  change (¬ (e8049 _v)) at p21374
  rcases p15206 with hlit | hlit
  · exact (False.elim (p21374 hlit))
  · exact hlit
theorem n21376 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h3152 : (e3152 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4813 : (e4813 _v)) (h6501 : (e6501 _v)) (h6750 : (e6750 _v)) (h7807 : (e7807 _v)) : (e4420 _v) := by
  have p16832 := n16832 _v _q 
  have p21373 := n21373 _v _q h51 h91 h2529 h3152 h4260 h4306 h4653 h4675 h4813 h6501 h6750 h7807
  have p11350 := n11350 _v _q h7807
  change (e2303 _v) ∨ (¬ (e4419 _v)) ∨ (e2475 _v) at p16832
  change (¬ (e2475 _v)) at p21373
  change (¬ (e2303 _v)) at p11350
  rcases p16832 with hlit | hlit | hlit
  · exact (False.elim (p11350 hlit))
  · exact hlit
  · exact (False.elim (p21373 hlit))
theorem n21377 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h3152 : (e3152 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4813 : (e4813 _v)) (h6501 : (e6501 _v)) (h6750 : (e6750 _v)) (h7807 : (e7807 _v)) : (e7921 _v) := by
  have p16347 := n16347 _v _q 
  have p21376 := n21376 _v _q h51 h91 h2529 h3152 h4260 h4306 h4653 h4675 h4813 h6501 h6750 h7807
  change (e7921 _v) ∨ (e4419 _v) at p16347
  change (¬ (e4419 _v)) at p21376
  rcases p16347 with hlit | hlit
  · exact hlit
  · exact (False.elim (p21376 hlit))
theorem n21378 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2179 : (e2179 _v)) (h2402 : (e2402 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6525 : (e6525 _v)) (h6750 : (e6750 _v)) : (e2787 _v) := by
  have p21370 := n21370 _v _q 
  have p14799 := n14799 _v _q h2402
  have p8420 := n8420 _v _q h6750
  have p8463 := n8463 _v _q h6525
  have p4981 := n4981 _v _q h4260
  have p5008 := n5008 _v _q h4787
  have p15957 := n15957 _v _q h2179
  have p4999 := n4999 _v _q h91
  have p253 := n253 _v _q h191
  have p16729 := n16729 _v _q h51
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4989 := n4989 _v _q h4838
  have p4983 := n4983 _v _q h4813
  have p11534 := n11534 _v _q h2402 h6750
  change (e2787 _v) ∨ (¬ (e2179 _v)) ∨ (e2733 _v) ∨ (e2242 _v) ∨ (¬ (e4260 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e3919 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e2303 _v)) at p21370
  change (¬ (e2733 _v)) at p8420
  change (¬ (e2242 _v)) at p8463
  rcases p21370 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p15957))
  · exact (False.elim (p8420 hlit))
  · exact (False.elim (p8463 hlit))
  · exact (False.elim (hlit p4981))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p14799))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p253))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p4989))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p11534))
theorem n21379 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2242 : (e2242 _v)) (h3152 : (e3152 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6630 : (e6630 _v)) (h6750 : (e6750 _v)) (h6776 : (e6776 _v)) : (e4546 _v) := by
  have p16307 := n16307 _v _q 
  have p21372 := n21372 _v _q h51 h91 h191 h2242 h3152 h4306 h4653 h4813 h4838 h6630 h6750 h6776
  change (e8029 _v) ∨ (e4546 _v) at p16307
  change (¬ (e8029 _v)) at p21372
  rcases p16307 with hlit | hlit
  · exact (False.elim (p21372 hlit))
  · exact hlit
theorem n21380 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h3152 : (e3152 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4813 : (e4813 _v)) (h6501 : (e6501 _v)) (h6750 : (e6750 _v)) (h7807 : (e7807 _v)) : (e7943 _v) := by
  have p21266 := n21266 _v _q 
  have p21375 := n21375 _v _q h51 h91 h2529 h3152 h4260 h4306 h4653 h4675 h4813 h6501 h6750 h7807
  have p8548 := n8548 _v _q h2529
  have p15641 := n15641 _v _q h6501
  have p8420 := n8420 _v _q h6750
  have p4981 := n4981 _v _q h4260
  have p16325 := n16325 _v _q h6501
  have p5006 := n5006 _v _q h4675
  have p4998 := n4998 _v _q h3152
  have p4999 := n4999 _v _q h91
  have p16729 := n16729 _v _q h51
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4983 := n4983 _v _q h4813
  have p11350 := n11350 _v _q h7807
  change (¬ (e8045 _v)) ∨ (e2303 _v) ∨ (¬ (e2529 _v)) ∨ (¬ (e4608 _v)) ∨ (e2733 _v) ∨ (¬ (e4260 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e7935 _v)) at p21266
  change (¬ (e2733 _v)) at p8420
  change (¬ (e2303 _v)) at p11350
  rcases p21266 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact (False.elim (hlit p21375))
  · exact (False.elim (p11350 hlit))
  · exact (False.elim (hlit p8548))
  · exact (False.elim (hlit p15641))
  · exact (False.elim (p8420 hlit))
  · exact (False.elim (hlit p4981))
  · exact (False.elim (hlit p16325))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p4983))
  · exact hlit
theorem n21381 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h3152 : (e3152 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4813 : (e4813 _v)) (h6501 : (e6501 _v)) (h6750 : (e6750 _v)) (h7807 : (e7807 _v)) : (e7944 _v) := by
  have p15266 := n15266 _v _q 
  have p21380 := n21380 _v _q h51 h91 h2529 h3152 h4260 h4306 h4653 h4675 h4813 h6501 h6750 h7807
  change (e7944 _v) ∨ (e7935 _v) at p15266
  change (¬ (e7935 _v)) at p21380
  rcases p15266 with hlit | hlit
  · exact hlit
  · exact (False.elim (p21380 hlit))
theorem n21382 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2179 : (e2179 _v)) (h2402 : (e2402 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6525 : (e6525 _v)) (h6750 : (e6750 _v)) : (e7927 _v) := by
  have p14855 := n14855 _v _q 
  have p21378 := n21378 _v _q h51 h91 h191 h2179 h2402 h4260 h4306 h4653 h4787 h4813 h4838 h6525 h6750
  change (¬ (e2787 _v)) ∨ (¬ (e7921 _v)) at p14855
  rcases p14855 with hlit | hlit
  · exact (False.elim (hlit p21378))
  · exact hlit
theorem n21383 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2179 : (e2179 _v)) (h2402 : (e2402 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6525 : (e6525 _v)) (h6750 : (e6750 _v)) : (e4419 _v) := by
  have p16347 := n16347 _v _q 
  have p21382 := n21382 _v _q h51 h91 h191 h2179 h2402 h4260 h4306 h4653 h4787 h4813 h4838 h6525 h6750
  change (e7921 _v) ∨ (e4419 _v) at p16347
  change (¬ (e7921 _v)) at p21382
  rcases p16347 with hlit | hlit
  · exact (False.elim (p21382 hlit))
  · exact hlit
theorem n21384 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2242 : (e2242 _v)) (h3152 : (e3152 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6630 : (e6630 _v)) (h6750 : (e6750 _v)) (h6776 : (e6776 _v)) : (e7489 _v) := by
  have p21379 := n21379 _v _q h51 h91 h191 h2242 h3152 h4306 h4653 h4813 h4838 h6630 h6750 h6776
  have p8420 := n8420 _v _q h6750
  have p8434 := n8434 _v _q h6630
  have p21330 := n21330 _v _q h51 h91 h191 h2242 h3152 h4306 h4653 h4813 h4838 h6630 h6750 h6776
  have p21350 := n21350 _v _q h51 h91 h191 h2242 h3152 h4306 h4653 h4813 h4838 h6630 h6750 h6776
  have p21339 := n21339 _v _q h51 h91 h191 h2242 h3152 h4306 h4653 h4813 h4838 h6630 h6750 h6776
  have p16913 := n16913 _v _q 
  have p15940 := n15940 _v _q h6750
  have p21351 := n21351 _v _q h51 h91 h191 h2242 h3152 h4306 h4653 h4813 h4838 h6630 h6750 h6776
  have p17133 := n17133 _v _q 
  have p12927 := n12927 _v _q h2242
  have p15956 := n15956 _v _q h6776
  have p21353 := n21353 _v _q h51 h91 h191 h2242 h3152 h4306 h4653 h4813 h4838 h6630 h6750 h6776
  have p17104 := n17104 _v _q 
  have p17874 := n17874 _v _q 
  have p17127 := n17127 _v _q 
  have p17089 := n17089 _v _q 
  have p4998 := n4998 _v _q h3152
  have p8553 := n8553 _v _q h2242
  have p13951 := n13951 _v _q 
  have p253 := n253 _v _q h191
  have p15946 := n15946 _v _q h2242
  have p17020 := n17020 _v _q 
  have p17138 := n17138 _v _q h4306
  have p20274 := n20274 _v _q 
  have p17060 := n17060 _v _q h4653
  have p20470 := n20470 _v _q 
  have p4989 := n4989 _v _q h4838
  have p17050 := n17050 _v _q 
  have p16778 := n16778 _v _q 
  have p17122 := n17122 _v _q 
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p20829 := n20829 _v _q 
  have p15775 := n15775 _v _q h2242
  have p20426 := n20426 _v _q 
  have p20126 := n20126 _v _q 
  have p17110 := n17110 _v _q 
  have p17053 := n17053 _v _q 
  have p20096 := n20096 _v _q 
  have p17131 := n17131 _v _q 
  have p17108 := n17108 _v _q 
  have p17294 := n17294 _v _q 
  have p16943 := n16943 _v _q 
  have p17058 := n17058 _v _q 
  have p17064 := n17064 _v _q 
  have p17067 := n17067 _v _q 
  have p17080 := n17080 _v _q 
  have p17072 := n17072 _v _q 
  have p17074 := n17074 _v _q 
  have p17069 := n17069 _v _q 
  have p20461 := n20461 _v _q 
  have p20836 := n20836 _v _q 
  have p20653 := n20653 _v _q 
  have p17078 := n17078 _v _q 
  have p17136 := n17136 _v _q 
  have p17087 := n17087 _v _q 
  have p17083 := n17083 _v _q 
  have p17055 := n17055 _v _q 
  have p17093 := n17093 _v _q 
  have p17091 := n17091 _v _q 
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p15949 := n15949 _v _q h2242
  have p20838 := n20838 _v _q h2242
  have p17141 := n17141 _v _q 
  have p17100 := n17100 _v _q 
  have p19610 := n19610 _v _q 
  have p17102 := n17102 _v _q 
  have p15934 := n15934 _v _q h6630
  have p15952 := n15952 _v _q h2242
  have p17096 := n17096 _v _q 
  have p17115 := n17115 _v _q 
  have p17758 := n17758 _v _q 
  have p17124 := n17124 _v _q 
  have p17111 := n17111 _v _q 
  have p19665 := n19665 _v _q 
  have p17113 := n17113 _v _q 
  have p17117 := n17117 _v _q 
  have p20467 := n20467 _v _q 
  have p17120 := n17120 _v _q 
  have p4999 := n4999 _v _q h91
  have p258 := n258 _v _q 
  exact FloorCertificate.node_21384 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4541 _v) (e4808 _v) p21379 p8420 p8434 p21330 p21350 p21339 p16913 p15940 p21351 p17133 p12927 p15956 p21353 p17104 p17874 p17127 p17089 p4998 p8553 p13951 p253 p15946 p17020 p17138 p20274 p17060 p20470 p4989 p17050 p16778 p17122 p4983 p16729 p20829 p15775 p20426 p20126 p17110 p17053 p20096 p17131 p17108 p17294 p16943 p17058 p17064 p17067 p17080 p17072 p17074 p17069 p20461 p20836 p20653 p17078 p17136 p17087 p17083 p17055 p17093 p17091 p17098 p17106 p15949 p20838 p17141 p17100 p19610 p17102 p15934 p15952 p17096 p17115 p17758 p17124 p17111 p19665 p17113 p17117 p20467 p17120 p4999 p258
theorem n21385 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h3152 : (e3152 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4813 : (e4813 _v)) (h6501 : (e6501 _v)) (h6750 : (e6750 _v)) (h7807 : (e7807 _v)) : (e6772 _v) := by
  have p14855 := n14855 _v _q 
  have p21377 := n21377 _v _q h51 h91 h2529 h3152 h4260 h4306 h4653 h4675 h4813 h6501 h6750 h7807
  change (¬ (e2787 _v)) ∨ (¬ (e7921 _v)) at p14855
  rcases p14855 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p21377))
theorem n21386 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h3152 : (e3152 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4813 : (e4813 _v)) (h6501 : (e6501 _v)) (h6750 : (e6750 _v)) (h7807 : (e7807 _v)) : (e7489 _v) := by
  have p15228 := n15228 _v _q 
  have p21381 := n21381 _v _q h51 h91 h2529 h3152 h4260 h4306 h4653 h4675 h4813 h6501 h6750 h7807
  have p21385 := n21385 _v _q h51 h91 h2529 h3152 h4260 h4306 h4653 h4675 h4813 h6501 h6750 h7807
  change (e2787 _v) ∨ (¬ (e7944 _v)) at p15228
  change (¬ (e2787 _v)) at p21385
  rcases p15228 with hlit | hlit
  · exact (False.elim (p21385 hlit))
  · exact (False.elim (hlit p21381))
theorem n21388 (_v : Vars) (_q : Query _v)  : (e21387 _v) := by
  by_contra hc
  change ¬ ((e2303 _v) ∨ (¬ (e2529 _v)) ∨ (e2733 _v) ∨ (¬ (e4260 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (e2179 _v)) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h2529 : (e2529 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h4260 : (e4260 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h4675 : (e4675 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h6501 : (e6501 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))))))))
  have h6750 : (e6750 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h7807 : (e7807 _v) := (fun hn => hc (Or.inl hn))
  have p21386 := n21386 _v _q h51 h91 h2529 h3152 h4260 h4306 h4653 h4675 h4813 h6501 h6750 h7807
  exact p21386
theorem n21389 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2179 : (e2179 _v)) (h2402 : (e2402 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6525 : (e6525 _v)) (h6750 : (e6750 _v)) : (e8048 _v) := by
  have p21357 := n21357 _v _q 
  have p21359 := n21359 _v _q h51 h91 h191 h2179 h2402 h4260 h4306 h4653 h4787 h4813 h4838 h6525 h6750
  have p15957 := n15957 _v _q h2179
  have p8420 := n8420 _v _q h6750
  have p8463 := n8463 _v _q h6525
  have p21383 := n21383 _v _q h51 h91 h191 h2179 h2402 h4260 h4306 h4653 h4787 h4813 h4838 h6525 h6750
  have p16864 := n16864 _v _q h2402 h6750
  have p4981 := n4981 _v _q h4260
  have p5008 := n5008 _v _q h4787
  have p14799 := n14799 _v _q h2402
  have p4999 := n4999 _v _q h91
  have p253 := n253 _v _q h191
  have p16729 := n16729 _v _q h51
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4989 := n4989 _v _q h4838
  have p4983 := n4983 _v _q h4813
  change (¬ (e8045 _v)) ∨ (e2242 _v) ∨ (¬ (e2179 _v)) ∨ (e2733 _v) ∨ (¬ (e5100 _v)) ∨ (¬ (e4419 _v)) ∨ (¬ (e4285 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e3919 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4813 _v)) at p21357
  change (¬ (e2733 _v)) at p8420
  change (¬ (e2242 _v)) at p8463
  rcases p21357 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (p8463 hlit))
  · exact (False.elim (hlit p15957))
  · exact (False.elim (p8420 hlit))
  · exact (False.elim (hlit p21359))
  · exact (False.elim (hlit p21383))
  · exact (False.elim (hlit p16864))
  · exact (False.elim (hlit p4981))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p14799))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p253))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p4989))
  · exact (False.elim (hlit p4983))
theorem n21390 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2179 : (e2179 _v)) (h2402 : (e2402 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6525 : (e6525 _v)) (h6750 : (e6750 _v)) : (e8049 _v) := by
  have p15206 := n15206 _v _q 
  have p21389 := n21389 _v _q h51 h91 h191 h2179 h2402 h4260 h4306 h4653 h4787 h4813 h4838 h6525 h6750
  change (e8049 _v) ∨ (e8045 _v) at p15206
  change (¬ (e8045 _v)) at p21389
  rcases p15206 with hlit | hlit
  · exact hlit
  · exact (False.elim (p21389 hlit))
theorem n21392 (_v : Vars) (_q : Query _v)  : (e21391 _v) := by
  by_contra hc
  change ¬ ((e2733 _v) ∨ (e2468 _v) ∨ (¬ (e3152 _v)) ∨ (¬ (e2242 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e91 _v)) ∨ (e2781 _v)) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h191 : (e191 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h2242 : (e2242 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h4838 : (e4838 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h6630 : (e6630 _v) := (fun hn => hc (Or.inr (Or.inl hn)))
  have h6750 : (e6750 _v) := (fun hn => hc (Or.inl hn))
  have h6776 : (e6776 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))))))))
  have p21384 := n21384 _v _q h51 h91 h191 h2242 h3152 h4306 h4653 h4813 h4838 h6630 h6750 h6776
  exact p21384
theorem n21393 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h3152 : (e3152 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4813 : (e4813 _v)) (h6501 : (e6501 _v)) (h6750 : (e6750 _v)) : (e2303 _v) := by
  have p21388 := n21388 _v _q 
  have p8554 := n8554 _v _q h6501
  have p8420 := n8420 _v _q h6750
  have p4981 := n4981 _v _q h4260
  have p5006 := n5006 _v _q h4675
  have p4998 := n4998 _v _q h3152
  have p4999 := n4999 _v _q h91
  have p16729 := n16729 _v _q h51
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4983 := n4983 _v _q h4813
  have p8548 := n8548 _v _q h2529
  change (e2303 _v) ∨ (¬ (e2529 _v)) ∨ (e2733 _v) ∨ (¬ (e4260 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (e2179 _v) at p21388
  change (¬ (e2179 _v)) at p8554
  change (¬ (e2733 _v)) at p8420
  rcases p21388 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p8548))
  · exact (False.elim (p8420 hlit))
  · exact (False.elim (hlit p4981))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (p8554 hlit))
theorem n21394 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2179 : (e2179 _v)) (h2402 : (e2402 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6525 : (e6525 _v)) (h6750 : (e6750 _v)) : (e2475 _v) := by
  have p15207 := n15207 _v _q 
  have p21390 := n21390 _v _q h51 h91 h191 h2179 h2402 h4260 h4306 h4653 h4787 h4813 h4838 h6525 h6750
  change (e2475 _v) ∨ (¬ (e8049 _v)) at p15207
  rcases p15207 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p21390))
theorem n21395 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2179 : (e2179 _v)) (h2402 : (e2402 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6525 : (e6525 _v)) (h6750 : (e6750 _v)) : (e8035 _v) := by
  have p14871 := n14871 _v _q 
  have p21394 := n21394 _v _q h51 h91 h191 h2179 h2402 h4260 h4306 h4653 h4787 h4813 h4838 h6525 h6750
  change (¬ (e2475 _v)) ∨ (¬ (e8029 _v)) at p14871
  rcases p14871 with hlit | hlit
  · exact (False.elim (hlit p21394))
  · exact hlit
theorem n21396 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h3152 : (e3152 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4813 : (e4813 _v)) (h6501 : (e6501 _v)) (h6750 : (e6750 _v)) : (e7804 _v) := by
  have p14837 := n14837 _v _q 
  have p21393 := n21393 _v _q h51 h91 h2529 h3152 h4260 h4306 h4653 h4675 h4813 h6501 h6750
  change (¬ (e2303 _v)) ∨ (¬ (e7798 _v)) at p14837
  rcases p14837 with hlit | hlit
  · exact (False.elim (hlit p21393))
  · exact hlit
theorem n21397 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h3152 : (e3152 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4813 : (e4813 _v)) (h6501 : (e6501 _v)) (h6750 : (e6750 _v)) : (e4285 _v) := by
  have p16274 := n16274 _v _q 
  have p21396 := n21396 _v _q h51 h91 h2529 h3152 h4260 h4306 h4653 h4675 h4813 h6501 h6750
  change (e7798 _v) ∨ (e4285 _v) at p16274
  change (¬ (e7798 _v)) at p21396
  rcases p16274 with hlit | hlit
  · exact (False.elim (p21396 hlit))
  · exact hlit
theorem n21398 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2179 : (e2179 _v)) (h2402 : (e2402 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6525 : (e6525 _v)) (h6750 : (e6750 _v)) : (e4546 _v) := by
  have p16307 := n16307 _v _q 
  have p21395 := n21395 _v _q h51 h91 h191 h2179 h2402 h4260 h4306 h4653 h4787 h4813 h4838 h6525 h6750
  change (e8029 _v) ∨ (e4546 _v) at p16307
  change (¬ (e8029 _v)) at p21395
  rcases p16307 with hlit | hlit
  · exact (False.elim (p21395 hlit))
  · exact hlit
theorem n21399 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2242 : (e2242 _v)) (h3152 : (e3152 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6630 : (e6630 _v)) (h6776 : (e6776 _v)) : (e2733 _v) := by
  have p21392 := n21392 _v _q 
  have p8434 := n8434 _v _q h6630
  have p4998 := n4998 _v _q h3152
  have p8553 := n8553 _v _q h2242
  have p253 := n253 _v _q h191
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4989 := n4989 _v _q h4838
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p4999 := n4999 _v _q h91
  have p8601 := n8601 _v _q h6776
  change (e2733 _v) ∨ (e2468 _v) ∨ (¬ (e3152 _v)) ∨ (¬ (e2242 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e91 _v)) ∨ (e2781 _v) at p21392
  change (¬ (e2468 _v)) at p8434
  change (¬ (e2781 _v)) at p8601
  rcases p21392 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (p8434 hlit))
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p8553))
  · exact (False.elim (hlit p253))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p4989))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (p8601 hlit))
theorem n21400 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h3152 : (e3152 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4813 : (e4813 _v)) (h6501 : (e6501 _v)) (h6750 : (e6750 _v)) : (e6772 _v) := by
  have p21366 := n21366 _v _q 
  have p21397 := n21397 _v _q h51 h91 h2529 h3152 h4260 h4306 h4653 h4675 h4813 h6501 h6750
  have p8554 := n8554 _v _q h6501
  have p15940 := n15940 _v _q h6750
  have p21355 := n21355 _v _q h51 h91 h2529 h3152 h4260 h4306 h4653 h4675 h4813 h6501 h6750
  have p4981 := n4981 _v _q h4260
  have p21190 := n21190 _v _q h51 h91 h2529 h4306 h4653 h4813
  have p5006 := n5006 _v _q h4675
  have p4998 := n4998 _v _q h3152
  have p4999 := n4999 _v _q h91
  have p16705 := n16705 _v _q h2529
  have p16729 := n16729 _v _q h51
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p16572 := n16572 _v _q h2529
  have p4983 := n4983 _v _q h4813
  change (¬ (e2787 _v)) ∨ (¬ (e4285 _v)) ∨ (e2179 _v) ∨ (¬ (e4096 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4813 _v)) at p21366
  change (¬ (e2179 _v)) at p8554
  rcases p21366 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p21397))
  · exact (False.elim (p8554 hlit))
  · exact (False.elim (hlit p15940))
  · exact (False.elim (hlit p21355))
  · exact (False.elim (hlit p4981))
  · exact (False.elim (hlit p21190))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p16705))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p16572))
  · exact (False.elim (hlit p4983))
theorem n21401 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2179 : (e2179 _v)) (h2402 : (e2402 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6525 : (e6525 _v)) (h6750 : (e6750 _v)) : (e7489 _v) := by
  have p17064 := n17064 _v _q 
  have p21398 := n21398 _v _q h51 h91 h191 h2179 h2402 h4260 h4306 h4653 h4787 h4813 h4838 h6525 h6750
  have p17067 := n17067 _v _q 
  have p8591 := n8591 _v _q h2402
  have p17080 := n17080 _v _q 
  have p21347 := n21347 _v _q h51 h91 h191 h2179 h2402 h4260 h4306 h4653 h4787 h4813 h4838 h6525 h6750
  have p8463 := n8463 _v _q h6525
  have p8420 := n8420 _v _q h6750
  have p17072 := n17072 _v _q 
  have p17074 := n17074 _v _q 
  have p17069 := n17069 _v _q 
  have p16913 := n16913 _v _q 
  have p21359 := n21359 _v _q h51 h91 h191 h2179 h2402 h4260 h4306 h4653 h4787 h4813 h4838 h6525 h6750
  have p21383 := n21383 _v _q h51 h91 h191 h2179 h2402 h4260 h4306 h4653 h4787 h4813 h4838 h6525 h6750
  have p16864 := n16864 _v _q h2402 h6750
  have p15959 := n15959 _v _q h2179
  have p20836 := n20836 _v _q 
  have p20653 := n20653 _v _q 
  have p17078 := n17078 _v _q 
  have p17136 := n17136 _v _q 
  have p21335 := n21335 _v _q h51 h91 h191 h2179 h4260 h4306 h4653 h4787 h4813 h4838 h6525 h6750
  have p17087 := n17087 _v _q 
  have p17083 := n17083 _v _q 
  have p21244 := n21244 _v _q h51 h91 h191 h4260 h4306 h4653 h4787 h4813 h4838 h6525
  have p17055 := n17055 _v _q 
  have p17093 := n17093 _v _q 
  have p17091 := n17091 _v _q 
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p15940 := n15940 _v _q h6750
  have p21245 := n21245 _v _q h51 h91 h191 h4260 h4306 h4653 h4787 h4813 h4838 h6525
  have p17141 := n17141 _v _q 
  have p17100 := n17100 _v _q 
  have p19610 := n19610 _v _q 
  have p4981 := n4981 _v _q h4260
  have p17102 := n17102 _v _q 
  have p5008 := n5008 _v _q h4787
  have p17009 := n17009 _v _q 
  have p14799 := n14799 _v _q h2402
  have p16058 := n16058 _v _q h6525
  have p16689 := n16689 _v _q h6525
  have p17096 := n17096 _v _q 
  have p17115 := n17115 _v _q 
  have p17758 := n17758 _v _q 
  have p17124 := n17124 _v _q 
  have p17111 := n17111 _v _q 
  have p19665 := n19665 _v _q 
  have p17113 := n17113 _v _q 
  have p17117 := n17117 _v _q 
  have p20467 := n20467 _v _q 
  have p17120 := n17120 _v _q 
  have p4999 := n4999 _v _q h91
  have p17133 := n17133 _v _q 
  have p17874 := n17874 _v _q 
  have p17104 := n17104 _v _q 
  have p17127 := n17127 _v _q 
  have p17089 := n17089 _v _q 
  have p20470 := n20470 _v _q 
  have p253 := n253 _v _q h191
  have p17020 := n17020 _v _q 
  have p20274 := n20274 _v _q 
  have p21142 := n21142 _v _q h51 h4260 h4306 h4653 h4813
  have p16729 := n16729 _v _q h51
  have p17050 := n17050 _v _q 
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4989 := n4989 _v _q h4838
  have p4983 := n4983 _v _q h4813
  have p17122 := n17122 _v _q 
  have p16778 := n16778 _v _q 
  have p20829 := n20829 _v _q 
  have p17108 := n17108 _v _q 
  have p20461 := n20461 _v _q 
  have p20426 := n20426 _v _q 
  have p20126 := n20126 _v _q 
  have p17110 := n17110 _v _q 
  have p17053 := n17053 _v _q 
  have p17131 := n17131 _v _q 
  have p20096 := n20096 _v _q 
  have p17058 := n17058 _v _q 
  have p17294 := n17294 _v _q 
  have p16943 := n16943 _v _q 
  have p13951 := n13951 _v _q 
  have p21394 := n21394 _v _q h51 h91 h191 h2179 h2402 h4260 h4306 h4653 h4787 h4813 h4838 h6525 h6750
  exact FloorCertificate.node_21401 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p17064 p21398 p17067 p8591 p17080 p21347 p8463 p8420 p17072 p17074 p17069 p16913 p21359 p21383 p16864 p15959 p20836 p20653 p17078 p17136 p21335 p17087 p17083 p21244 p17055 p17093 p17091 p17098 p17106 p15940 p21245 p17141 p17100 p19610 p4981 p17102 p5008 p17009 p14799 p16058 p16689 p17096 p17115 p17758 p17124 p17111 p19665 p17113 p17117 p20467 p17120 p4999 p17133 p17874 p17104 p17127 p17089 p20470 p253 p17020 p20274 p21142 p16729 p17050 p17138 p17060 p4989 p4983 p17122 p16778 p20829 p17108 p20461 p20426 p20126 p17110 p17053 p17131 p20096 p17058 p17294 p16943 p13951 p21394
theorem n21402 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2242 : (e2242 _v)) (h3152 : (e3152 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6630 : (e6630 _v)) (h6776 : (e6776 _v)) : (e4109 _v) := by
  have p14689 := n14689 _v _q 
  have p21399 := n21399 _v _q h51 h91 h191 h2242 h3152 h4306 h4653 h4813 h4838 h6630 h6776
  change (¬ (e2733 _v)) ∨ (¬ (e4108 _v)) at p14689
  rcases p14689 with hlit | hlit
  · exact (False.elim (hlit p21399))
  · exact hlit
theorem n21403 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2242 : (e2242 _v)) (h3152 : (e3152 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6630 : (e6630 _v)) (h6776 : (e6776 _v)) : (e4101 _v) := by
  have p14929 := n14929 _v _q 
  have p21402 := n21402 _v _q h51 h91 h191 h2242 h3152 h4306 h4653 h4813 h4838 h6630 h6776
  change (e4108 _v) ∨ (e4101 _v) at p14929
  change (¬ (e4108 _v)) at p21402
  rcases p14929 with hlit | hlit
  · exact (False.elim (p21402 hlit))
  · exact hlit
theorem n21404 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h3152 : (e3152 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4813 : (e4813 _v)) (h6501 : (e6501 _v)) (h6750 : (e6750 _v)) : (e8038 _v) := by
  have p8461 := n8461 _v _q 
  have p21400 := n21400 _v _q h51 h91 h2529 h3152 h4260 h4306 h4653 h4675 h4813 h6501 h6750
  have p21393 := n21393 _v _q h51 h91 h2529 h3152 h4260 h4306 h4653 h4675 h4813 h6501 h6750
  change (¬ (e2475 _v)) ∨ (¬ (e2303 _v)) ∨ (e2787 _v) at p8461
  change (¬ (e2787 _v)) at p21400
  rcases p8461 with hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p21393))
  · exact (False.elim (p21400 hlit))
theorem n21405 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h3152 : (e3152 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4813 : (e4813 _v)) (h6501 : (e6501 _v)) (h6750 : (e6750 _v)) : (e5093 _v) := by
  have p11399 := n11399 _v _q 
  have p21404 := n21404 _v _q h51 h91 h2529 h3152 h4260 h4306 h4653 h4675 h4813 h6501 h6750
  change (¬ (e13 _v)) ∨ (e2475 _v) at p11399
  change (¬ (e2475 _v)) at p21404
  rcases p11399 with hlit | hlit
  · exact hlit
  · exact (False.elim (p21404 hlit))
theorem n21406 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h3152 : (e3152 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4813 : (e4813 _v)) (h6501 : (e6501 _v)) (h6750 : (e6750 _v)) : (e7945 _v) := by
  have p15228 := n15228 _v _q 
  have p21400 := n21400 _v _q h51 h91 h2529 h3152 h4260 h4306 h4653 h4675 h4813 h6501 h6750
  change (e2787 _v) ∨ (¬ (e7944 _v)) at p15228
  change (¬ (e2787 _v)) at p21400
  rcases p15228 with hlit | hlit
  · exact (False.elim (p21400 hlit))
  · exact hlit
theorem n21407 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h3152 : (e3152 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4813 : (e4813 _v)) (h6501 : (e6501 _v)) (h6750 : (e6750 _v)) : (e7935 _v) := by
  have p15266 := n15266 _v _q 
  have p21406 := n21406 _v _q h51 h91 h2529 h3152 h4260 h4306 h4653 h4675 h4813 h6501 h6750
  change (e7944 _v) ∨ (e7935 _v) at p15266
  change (¬ (e7944 _v)) at p21406
  rcases p15266 with hlit | hlit
  · exact (False.elim (p21406 hlit))
  · exact hlit
theorem n21408 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h3152 : (e3152 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4813 : (e4813 _v)) (h6501 : (e6501 _v)) (h6750 : (e6750 _v)) : (e8050 _v) := by
  have p15207 := n15207 _v _q 
  have p21404 := n21404 _v _q h51 h91 h2529 h3152 h4260 h4306 h4653 h4675 h4813 h6501 h6750
  change (e2475 _v) ∨ (¬ (e8049 _v)) at p15207
  change (¬ (e2475 _v)) at p21404
  rcases p15207 with hlit | hlit
  · exact (False.elim (p21404 hlit))
  · exact hlit
theorem n21409 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h3152 : (e3152 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4813 : (e4813 _v)) (h6501 : (e6501 _v)) (h6750 : (e6750 _v)) : (e8045 _v) := by
  have p15206 := n15206 _v _q 
  have p21408 := n21408 _v _q h51 h91 h2529 h3152 h4260 h4306 h4653 h4675 h4813 h6501 h6750
  change (e8049 _v) ∨ (e8045 _v) at p15206
  change (¬ (e8049 _v)) at p21408
  rcases p15206 with hlit | hlit
  · exact (False.elim (p21408 hlit))
  · exact hlit
theorem n21411 (_v : Vars) (_q : Query _v)  : (e21410 _v) := by
  by_contra hc
  change ¬ ((¬ (e2402 _v)) ∨ (e2242 _v) ∨ (e2733 _v) ∨ (¬ (e4260 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e2179 _v))) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h191 : (e191 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h2179 : (e2179 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn)))))))))))))
  have h2402 : (e2402 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h4260 : (e4260 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h4838 : (e4838 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h6525 : (e6525 _v) := (fun hn => hc (Or.inr (Or.inl hn)))
  have h6750 : (e6750 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have p21401 := n21401 _v _q h51 h91 h191 h2179 h2402 h4260 h4306 h4653 h4787 h4813 h4838 h6525 h6750
  exact p21401
theorem n21412 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2242 : (e2242 _v)) (h2402 : (e2402 _v)) (h3152 : (e3152 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6630 : (e6630 _v)) (h6776 : (e6776 _v)) (h8038 : (e8038 _v)) : (e7943 _v) := by
  have p21027 := n21027 _v _q 
  have p8602 := n8602 _v _q h8038
  have p8601 := n8601 _v _q h6776
  have p21403 := n21403 _v _q h51 h91 h191 h2242 h3152 h4306 h4653 h4813 h4838 h6630 h6776
  have p4998 := n4998 _v _q h3152
  have p4999 := n4999 _v _q h91
  have p253 := n253 _v _q h191
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4989 := n4989 _v _q h4838
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p15934 := n15934 _v _q h6630
  have p8591 := n8591 _v _q h2402
  have p8553 := n8553 _v _q h2242
  change (¬ (e7935 _v)) ∨ (¬ (e2242 _v)) ∨ (e2781 _v) ∨ (¬ (e4101 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e2402 _v)) ∨ (e2475 _v) at p21027
  change (¬ (e2475 _v)) at p8602
  change (¬ (e2781 _v)) at p8601
  rcases p21027 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p8553))
  · exact (False.elim (p8601 hlit))
  · exact (False.elim (hlit p21403))
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p253))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p4989))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p15934))
  · exact (False.elim (hlit p8591))
  · exact (False.elim (p8602 hlit))
theorem n21413 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2242 : (e2242 _v)) (h2402 : (e2402 _v)) (h3152 : (e3152 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6630 : (e6630 _v)) (h6776 : (e6776 _v)) (h8038 : (e8038 _v)) : (e7944 _v) := by
  have p15266 := n15266 _v _q 
  have p21412 := n21412 _v _q h51 h91 h191 h2242 h2402 h3152 h4306 h4653 h4813 h4838 h6630 h6776 h8038
  change (e7944 _v) ∨ (e7935 _v) at p15266
  change (¬ (e7935 _v)) at p21412
  rcases p15266 with hlit | hlit
  · exact hlit
  · exact (False.elim (p21412 hlit))
theorem n21414 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h3152 : (e3152 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4813 : (e4813 _v)) (h6501 : (e6501 _v)) (h6750 : (e6750 _v)) : (e5105 _v) := by
  have p15204 := n15204 _v _q 
  have p21405 := n21405 _v _q h51 h91 h2529 h3152 h4260 h4306 h4653 h4675 h4813 h6501 h6750
  change (e13 _v) ∨ (¬ (e5104 _v)) at p15204
  change (¬ (e13 _v)) at p21405
  rcases p15204 with hlit | hlit
  · exact (False.elim (p21405 hlit))
  · exact hlit
theorem n21415 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2529 : (e2529 _v)) (h3152 : (e3152 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4813 : (e4813 _v)) (h6501 : (e6501 _v)) (h6750 : (e6750 _v)) : (e5100 _v) := by
  have p15319 := n15319 _v _q 
  have p21414 := n21414 _v _q h51 h91 h2529 h3152 h4260 h4306 h4653 h4675 h4813 h6501 h6750
  change (e5104 _v) ∨ (e5100 _v) at p15319
  change (¬ (e5104 _v)) at p21414
  rcases p15319 with hlit | hlit
  · exact (False.elim (p21414 hlit))
  · exact hlit
end
end Assembly
