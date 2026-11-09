import Dag244
import generated.th_lemma_32
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n21111 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2242 : (e2242 _v)) (h3152 : (e3152 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6600 : (e6600 _v)) (h6750 : (e6750 _v)) (h6776 : (e6776 _v)) : (e2787 _v) := by
  have p20882 := n20882 _v _q 
  have p15907 := n15907 _v _q h6600
  have p15940 := n15940 _v _q h6750
  have p4999 := n4999 _v _q h91
  have p15956 := n15956 _v _q h6776
  have p4998 := n4998 _v _q h3152
  have p253 := n253 _v _q h191
  have p15946 := n15946 _v _q h2242
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4989 := n4989 _v _q h4838
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p15775 := n15775 _v _q h2242
  have p15949 := n15949 _v _q h2242
  have p20838 := n20838 _v _q h2242
  have p5008 := n5008 _v _q h4787
  have p15952 := n15952 _v _q h2242
  have p21099 := n21099 _v _q h51 h91 h191 h2242 h3152 h4306 h4653 h4787 h4813 h4838 h6600 h6750 h6776
  change (e2787 _v) ∨ (¬ (e91 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e4567 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4679 _v)) ∨ (¬ (e3158 _v)) ∨ (¬ (e4439 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4459 _v)) ∨ (¬ (e2475 _v)) at p20882
  rcases p20882 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p15940))
  · exact (False.elim (hlit p15907))
  · exact (False.elim (hlit p15956))
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p253))
  · exact (False.elim (hlit p15946))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p4989))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p15775))
  · exact (False.elim (hlit p15949))
  · exact (False.elim (hlit p20838))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p15952))
  · exact (False.elim (hlit p21099))
theorem n21112 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2242 : (e2242 _v)) (h3152 : (e3152 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6600 : (e6600 _v)) (h6750 : (e6750 _v)) (h6776 : (e6776 _v)) : (e7927 _v) := by
  have p14855 := n14855 _v _q 
  have p21111 := n21111 _v _q h51 h91 h191 h2242 h3152 h4306 h4653 h4787 h4813 h4838 h6600 h6750 h6776
  change (¬ (e2787 _v)) ∨ (¬ (e7921 _v)) at p14855
  rcases p14855 with hlit | hlit
  · exact (False.elim (hlit p21111))
  · exact hlit
theorem n21113 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2242 : (e2242 _v)) (h3152 : (e3152 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6600 : (e6600 _v)) (h6750 : (e6750 _v)) (h6776 : (e6776 _v)) : (e8035 _v) := by
  have p14871 := n14871 _v _q 
  have p21099 := n21099 _v _q h51 h91 h191 h2242 h3152 h4306 h4653 h4787 h4813 h4838 h6600 h6750 h6776
  change (¬ (e2475 _v)) ∨ (¬ (e8029 _v)) at p14871
  rcases p14871 with hlit | hlit
  · exact (False.elim (hlit p21099))
  · exact hlit
theorem n21114 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2242 : (e2242 _v)) (h3152 : (e3152 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6600 : (e6600 _v)) (h6750 : (e6750 _v)) (h6776 : (e6776 _v)) : (e4546 _v) := by
  have p16307 := n16307 _v _q 
  have p21113 := n21113 _v _q h51 h91 h191 h2242 h3152 h4306 h4653 h4787 h4813 h4838 h6600 h6750 h6776
  change (e8029 _v) ∨ (e4546 _v) at p16307
  change (¬ (e8029 _v)) at p21113
  rcases p16307 with hlit | hlit
  · exact (False.elim (p21113 hlit))
  · exact hlit
theorem n21115 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2242 : (e2242 _v)) (h3152 : (e3152 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6600 : (e6600 _v)) (h6750 : (e6750 _v)) (h6776 : (e6776 _v)) : (e2358 _v) := by
  have p20888 := n20888 _v _q 
  have p21099 := n21099 _v _q h51 h91 h191 h2242 h3152 h4306 h4653 h4787 h4813 h4838 h6600 h6750 h6776
  have p8420 := n8420 _v _q h6750
  have p15907 := n15907 _v _q h6600
  have p15956 := n15956 _v _q h6776
  have p4998 := n4998 _v _q h3152
  have p8553 := n8553 _v _q h2242
  have p253 := n253 _v _q h191
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4989 := n4989 _v _q h4838
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p5008 := n5008 _v _q h4787
  have p4999 := n4999 _v _q h91
  change (e2358 _v) ∨ (¬ (e2475 _v)) ∨ (e2733 _v) ∨ (¬ (e3937 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e2242 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e91 _v)) at p20888
  change (¬ (e2733 _v)) at p8420
  rcases p20888 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p21099))
  · exact (False.elim (p8420 hlit))
  · exact (False.elim (hlit p15907))
  · exact (False.elim (hlit p15956))
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p8553))
  · exact (False.elim (hlit p253))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p4989))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p4999))
theorem n21116 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2242 : (e2242 _v)) (h3152 : (e3152 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6600 : (e6600 _v)) (h6750 : (e6750 _v)) (h6776 : (e6776 _v)) : (e7640 _v) := by
  have p14828 := n14828 _v _q 
  have p21115 := n21115 _v _q h51 h91 h191 h2242 h3152 h4306 h4653 h4787 h4813 h4838 h6600 h6750 h6776
  change (¬ (e2358 _v)) ∨ (¬ (e7634 _v)) at p14828
  rcases p14828 with hlit | hlit
  · exact (False.elim (hlit p21115))
  · exact hlit
theorem n21118 (_v : Vars) (_q : Query _v)  : (e21117 _v) := by
  by_contra hc
  change ¬ ((¬ (e225 _v)) ∨ (e1995 _v) ∨ (¬ (e51 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4260 _v))) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h225 : (e225 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h4260 : (e4260 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn)))))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h6423 : (e6423 _v) := (fun hn => hc (Or.inr (Or.inl hn)))
  have p21101 := n21101 _v _q h51 h225 h4260 h4306 h4653 h4813 h6423
  exact p21101
theorem n21119 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2468 : (e2468 _v)) (h3152 : (e3152 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6776 : (e6776 _v)) : (e7944 _v) := by
  have p15266 := n15266 _v _q 
  have p21103 := n21103 _v _q h51 h91 h191 h2468 h3152 h4306 h4653 h4813 h4838 h6776
  change (e7944 _v) ∨ (e7935 _v) at p15266
  change (¬ (e7935 _v)) at p21103
  rcases p15266 with hlit | hlit
  · exact hlit
  · exact (False.elim (p21103 hlit))
theorem n21120 (_v : Vars) (_q : Query _v) (h2296 : (e2296 _v)) (h2468 : (e2468 _v)) : (e2781 _v) := by
  have p8438 := n8438 _v _q h2468
  have p258 := n258 _v _q 
  have p8583 := n8583 _v _q h2296
  exact FloorCertificate.node_21120 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8438 p258 p8583
theorem n21121 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2296 : (e2296 _v)) (h2468 : (e2468 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e7489 _v) := by
  have p14699 := n14699 _v _q 
  have p21105 := n21105 _v _q h51 h91 h2296 h2468 h2529 h4306 h4653 h4813
  have p21120 := n21120 _v _q h2296 h2468
  change (¬ (e2781 _v)) ∨ (¬ (e4270 _v)) at p14699
  rcases p14699 with hlit | hlit
  · exact (False.elim (hlit p21120))
  · exact (False.elim (hlit p21105))
theorem n21123 (_v : Vars) (_q : Query _v)  : (e21122 _v) := by
  by_contra hc
  change ¬ ((¬ (e2296 _v)) ∨ (¬ (e2468 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e2529 _v))) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h2296 : (e2296 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h2468 : (e2468 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h2529 : (e2529 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have p21121 := n21121 _v _q h51 h91 h2296 h2468 h2529 h4306 h4653 h4813
  exact p21121
theorem n21124 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2242 : (e2242 _v)) (h2733 : (e2733 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6549 : (e6549 _v)) (h6600 : (e6600 _v)) (h6776 : (e6776 _v)) : (e4419 _v) := by
  have p16347 := n16347 _v _q 
  have p21107 := n21107 _v _q h51 h91 h191 h2242 h2733 h4306 h4653 h4787 h4813 h4838 h6549 h6600 h6776
  change (e7921 _v) ∨ (e4419 _v) at p16347
  change (¬ (e7921 _v)) at p21107
  rcases p16347 with hlit | hlit
  · exact (False.elim (p21107 hlit))
  · exact hlit
theorem n21125 (_v : Vars) (_q : Query _v) (h4260 : (e4260 _v)) (h5108 : (e5108 _v)) (h6423 : (e6423 _v)) : (e5193 _v) := by
  have p16442 := n16442 _v _q 
  have p21110 := n21110 _v _q h4260 h5108 h6423
  change (e5193 _v) ∨ (e191 _v) at p16442
  change (¬ (e191 _v)) at p21110
  rcases p16442 with hlit | hlit
  · exact hlit
  · exact (False.elim (p21110 hlit))
theorem n21126 (_v : Vars) (_q : Query _v) (h4260 : (e4260 _v)) (h5108 : (e5108 _v)) (h6423 : (e6423 _v)) : (e5195 _v) := by
  have p14730 := n14730 _v _q 
  have p21125 := n21125 _v _q h4260 h5108 h6423
  change (¬ (e196 _v)) ∨ (¬ (e5193 _v)) at p14730
  rcases p14730 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p21125))
theorem n21127 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2242 : (e2242 _v)) (h3152 : (e3152 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6600 : (e6600 _v)) (h6750 : (e6750 _v)) (h6776 : (e6776 _v)) : (e4419 _v) := by
  have p16347 := n16347 _v _q 
  have p21112 := n21112 _v _q h51 h91 h191 h2242 h3152 h4306 h4653 h4787 h4813 h4838 h6600 h6750 h6776
  change (e7921 _v) ∨ (e4419 _v) at p16347
  change (¬ (e7921 _v)) at p21112
  rcases p16347 with hlit | hlit
  · exact (False.elim (p21112 hlit))
  · exact hlit
theorem n21128 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2242 : (e2242 _v)) (h3152 : (e3152 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6600 : (e6600 _v)) (h6750 : (e6750 _v)) (h6776 : (e6776 _v)) : (e4139 _v) := by
  have p16281 := n16281 _v _q 
  have p21116 := n21116 _v _q h51 h91 h191 h2242 h3152 h4306 h4653 h4787 h4813 h4838 h6600 h6750 h6776
  change (e7634 _v) ∨ (e4139 _v) at p16281
  change (¬ (e7634 _v)) at p21116
  rcases p16281 with hlit | hlit
  · exact (False.elim (p21116 hlit))
  · exact hlit
theorem n21129 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e1995 _v) := by
  have p21118 := n21118 _v _q 
  have p4981 := n4981 _v _q h4260
  have p17020 := n17020 _v _q 
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  change (¬ (e225 _v)) ∨ (e1995 _v) ∨ (¬ (e51 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4260 _v)) at p21118
  rcases p21118 with hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact (False.elim (hlit p17020))
  · exact hlit
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p4981))
theorem n21130 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e4575 _v) := by
  have p14696 := n14696 _v _q 
  have p21129 := n21129 _v _q h51 h4260 h4306 h4653 h4813
  change (¬ (e1995 _v)) ∨ (¬ (e4574 _v)) at p14696
  rcases p14696 with hlit | hlit
  · exact (False.elim (hlit p21129))
  · exact hlit
theorem n21131 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2468 : (e2468 _v)) (h3152 : (e3152 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6776 : (e6776 _v)) : (e2787 _v) := by
  have p15228 := n15228 _v _q 
  have p21119 := n21119 _v _q h51 h91 h191 h2468 h3152 h4306 h4653 h4813 h4838 h6776
  change (e2787 _v) ∨ (¬ (e7944 _v)) at p15228
  rcases p15228 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p21119))
theorem n21132 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2468 : (e2468 _v)) (h3152 : (e3152 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6776 : (e6776 _v)) : (e7921 _v) := by
  have p16347 := n16347 _v _q 
  have p21104 := n21104 _v _q h51 h91 h191 h2468 h3152 h4306 h4653 h4813 h4838 h6776
  change (e7921 _v) ∨ (e4419 _v) at p16347
  change (¬ (e4419 _v)) at p21104
  rcases p16347 with hlit | hlit
  · exact hlit
  · exact (False.elim (p21104 hlit))
theorem n21133 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2468 : (e2468 _v)) (h3152 : (e3152 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6776 : (e6776 _v)) : (e7489 _v) := by
  have p14855 := n14855 _v _q 
  have p21131 := n21131 _v _q h51 h91 h191 h2468 h3152 h4306 h4653 h4813 h4838 h6776
  have p21132 := n21132 _v _q h51 h91 h191 h2468 h3152 h4306 h4653 h4813 h4838 h6776
  change (¬ (e2787 _v)) ∨ (¬ (e7921 _v)) at p14855
  rcases p14855 with hlit | hlit
  · exact (False.elim (hlit p21131))
  · exact (False.elim (hlit p21132))
theorem n21134 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2468 : (e2468 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e6549 _v) := by
  have p21123 := n21123 _v _q 
  have p8438 := n8438 _v _q h2468
  have p4999 := n4999 _v _q h91
  have p16729 := n16729 _v _q h51
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4983 := n4983 _v _q h4813
  have p8548 := n8548 _v _q h2529
  change (¬ (e2296 _v)) ∨ (¬ (e2468 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e2529 _v)) at p21123
  rcases p21123 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p8438))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p8548))
theorem n21135 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e1995 _v) := by
  have p21118 := n21118 _v _q 
  have p16706 := n16706 _v _q h2529 h6525
  have p17020 := n17020 _v _q 
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  change (¬ (e225 _v)) ∨ (e1995 _v) ∨ (¬ (e51 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4260 _v)) at p21118
  rcases p21118 with hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact (False.elim (hlit p17020))
  · exact hlit
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p16706))
theorem n21136 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6525 : (e6525 _v)) : (e4575 _v) := by
  have p14696 := n14696 _v _q 
  have p21135 := n21135 _v _q h51 h2529 h4306 h4653 h4813 h6525
  change (¬ (e1995 _v)) ∨ (¬ (e4574 _v)) at p14696
  rcases p14696 with hlit | hlit
  · exact (False.elim (hlit p21135))
  · exact hlit
theorem n21137 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2242 : (e2242 _v)) (h2733 : (e2733 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6549 : (e6549 _v)) (h6600 : (e6600 _v)) (h6776 : (e6776 _v)) : (e2475 _v) := by
  have p16832 := n16832 _v _q 
  have p21124 := n21124 _v _q h51 h91 h191 h2242 h2733 h4306 h4653 h4787 h4813 h4838 h6549 h6600 h6776
  have p16093 := n16093 _v _q h2733 h6600
  change (e2303 _v) ∨ (¬ (e4419 _v)) ∨ (e2475 _v) at p16832
  change (¬ (e2303 _v)) at p16093
  rcases p16832 with hlit | hlit | hlit
  · exact (False.elim (p16093 hlit))
  · exact (False.elim (hlit p21124))
  · exact hlit
theorem n21138 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6423 : (e6423 _v)) : (e4261 _v) := by
  have p21118 := n21118 _v _q 
  have p8452 := n8452 _v _q h6423
  have p17020 := n17020 _v _q 
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  change (¬ (e225 _v)) ∨ (e1995 _v) ∨ (¬ (e51 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4260 _v)) at p21118
  change (¬ (e1995 _v)) at p8452
  rcases p21118 with hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact (False.elim (hlit p17020))
  · exact (False.elim (p8452 hlit))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p4983))
  · exact hlit
theorem n21139 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6423 : (e6423 _v)) : (e7781 _v) := by
  have p15824 := n15824 _v _q 
  have p21138 := n21138 _v _q h51 h4306 h4653 h4813 h6423
  change (e7781 _v) ∨ (e4260 _v) at p15824
  change (¬ (e4260 _v)) at p21138
  rcases p15824 with hlit | hlit
  · exact hlit
  · exact (False.elim (p21138 hlit))
theorem n21140 (_v : Vars) (_q : Query _v) (h4260 : (e4260 _v)) (h5108 : (e5108 _v)) (h6423 : (e6423 _v)) : (e6571 _v) := by
  have p11357 := n11357 _v _q 
  have p21126 := n21126 _v _q h4260 h5108 h6423
  change (e196 _v) ∨ (¬ (e2358 _v)) at p11357
  change (¬ (e196 _v)) at p21126
  rcases p11357 with hlit | hlit
  · exact (False.elim (p21126 hlit))
  · exact hlit
theorem n21141 (_v : Vars) (_q : Query _v) (h4260 : (e4260 _v)) (h5108 : (e5108 _v)) (h6423 : (e6423 _v)) : (e7489 _v) := by
  have p8663 := n8663 _v _q 
  have p17953 := n17953 _v _q 
  have p5257 := n5257 _v _q 
  have p20932 := n20932 _v _q h5108 h6423
  have p16977 := n16977 _v _q 
  have p11366 := n11366 _v _q h5108
  have p21140 := n21140 _v _q h4260 h5108 h6423
  have p17256 := n17256 _v _q 
  have p21108 := n21108 _v _q h4260 h5108 h6423
  have p21063 := n21063 _v _q h4260 h6423
  have p21096 := n21096 _v _q h4260 h5108 h6423
  have p15650 := n15650 _v _q h5108
  have p13951 := n13951 _v _q 
  have p20933 := n20933 _v _q h5108 h6423
  have p16659 := n16659 _v _q h6423
  have p21069 := n21069 _v _q h4260 h6423
  have p21109 := n21109 _v _q h5108 h6423
  have p21088 := n21088 _v _q h4260 h6423
  have p16660 := n16660 _v _q h6423
  have p20829 := n20829 _v _q 
  have p17108 := n17108 _v _q 
  have p20461 := n20461 _v _q 
  have p4981 := n4981 _v _q h4260
  have p21083 := n21083 _v _q h4260 h6423
  have p20426 := n20426 _v _q 
  have p15967 := n15967 _v _q h6423
  have p20126 := n20126 _v _q 
  have p17110 := n17110 _v _q 
  have p17009 := n17009 _v _q 
  have p17053 := n17053 _v _q 
  have p17131 := n17131 _v _q 
  have p21071 := n21071 _v _q h4260 h6423
  have p20096 := n20096 _v _q 
  have p16892 := n16892 _v _q h5108
  have p17058 := n17058 _v _q 
  have p17294 := n17294 _v _q 
  have p16943 := n16943 _v _q 
  have p17064 := n17064 _v _q 
  have p16658 := n16658 _v _q h6423
  have p16748 := n16748 _v _q h5108
  have p17067 := n17067 _v _q 
  have p17069 := n17069 _v _q 
  have p17080 := n17080 _v _q 
  have p17072 := n17072 _v _q 
  have p17083 := n17083 _v _q 
  have p17074 := n17074 _v _q 
  have p20836 := n20836 _v _q 
  have p17078 := n17078 _v _q 
  have p20653 := n20653 _v _q 
  have p17087 := n17087 _v _q 
  have p17136 := n17136 _v _q 
  have p17055 := n17055 _v _q 
  have p17091 := n17091 _v _q 
  have p17093 := n17093 _v _q 
  have p17141 := n17141 _v _q 
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p17102 := n17102 _v _q 
  have p17100 := n17100 _v _q 
  have p19610 := n19610 _v _q 
  have p16929 := n16929 _v _q 
  have p17122 := n17122 _v _q 
  have p17096 := n17096 _v _q 
  have p20937 := n20937 _v _q h5108 h6423
  have p15379 := n15379 _v _q h6423
  have p17758 := n17758 _v _q 
  have p15964 := n15964 _v _q h6423
  have p19665 := n19665 _v _q 
  have p17115 := n17115 _v _q 
  have p17120 := n17120 _v _q 
  have p17111 := n17111 _v _q 
  have p17124 := n17124 _v _q 
  have p17050 := n17050 _v _q 
  have p16778 := n16778 _v _q 
  have p17113 := n17113 _v _q 
  have p17117 := n17117 _v _q 
  have p20467 := n20467 _v _q 
  have p17104 := n17104 _v _q 
  have p17874 := n17874 _v _q 
  have p17127 := n17127 _v _q 
  have p20274 := n20274 _v _q 
  have p20470 := n20470 _v _q 
  have p17133 := n17133 _v _q 
  have p17089 := n17089 _v _q 
  have p16394 := n16394 _v _q 
  have p16396 := n16396 _v _q h6423
  have p16576 := n16576 _v _q 
  have p16657 := n16657 _v _q h6423
  have p17147 := n17147 _v _q 
  have p21126 := n21126 _v _q h4260 h5108 h6423
  exact FloorCertificate.node_21141 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e61 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2834 _v) (e2849 _v) (e2863 _v) (e2877 _v) (e2883 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p8663 p17953 p5257 p20932 p16977 p11366 p21140 p17256 p21108 p21063 p21096 p15650 p13951 p20933 p16659 p21069 p21109 p21088 p16660 p20829 p17108 p20461 p4981 p21083 p20426 p15967 p20126 p17110 p17009 p17053 p17131 p21071 p20096 p16892 p17058 p17294 p16943 p17064 p16658 p16748 p17067 p17069 p17080 p17072 p17083 p17074 p20836 p17078 p20653 p17087 p17136 p17055 p17091 p17093 p17141 p17098 p17106 p17102 p17100 p19610 p16929 p17122 p17096 p20937 p15379 p17758 p15964 p19665 p17115 p17120 p17111 p17124 p17050 p16778 p17113 p17117 p20467 p17104 p17874 p17127 p20274 p20470 p17133 p17089 p16394 p16396 p16576 p16657 p17147 p21126
theorem n21142 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e4567 _v) := by
  have p8485 := n8485 _v _q 
  have p21130 := n21130 _v _q h51 h4260 h4306 h4653 h4813
  change (e4574 _v) ∨ (e4567 _v) at p8485
  change (¬ (e4574 _v)) at p21130
  rcases p8485 with hlit | hlit
  · exact (False.elim (p21130 hlit))
  · exact hlit
theorem n21143 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2787 : (e2787 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h4096 : (e4096 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h7742 : (e7742 _v)) (h8038 : (e8038 _v)) : (e7489 _v) := by
  have p10893 := n10893 _v _q 
  have p4016 := n4016 _v _q 
  have p16913 := n16913 _v _q 
  have p5008 := n5008 _v _q h4787
  have p15508 := n15508 _v _q h7742
  have p15209 := n15209 _v _q h8038
  have p19045 := n19045 _v _q h8038
  have p4987 := n4987 _v _q h4434
  have p16944 := n16944 _v _q h2787 h8038
  have p17009 := n17009 _v _q 
  have p16649 := n16649 _v _q h2787
  have p17147 := n17147 _v _q 
  have p4996 := n4996 _v _q h3937
  have p5006 := n5006 _v _q h4675
  have p16576 := n16576 _v _q 
  have p4991 := n4991 _v _q h4608
  have p4998 := n4998 _v _q h3152
  have p17096 := n17096 _v _q 
  have p17115 := n17115 _v _q 
  have p17758 := n17758 _v _q 
  have p17124 := n17124 _v _q 
  have p17111 := n17111 _v _q 
  have p11430 := n11430 _v _q h2787
  have p5001 := n5001 _v _q h4096
  have p19665 := n19665 _v _q 
  have p17113 := n17113 _v _q 
  have p17117 := n17117 _v _q 
  have p20467 := n20467 _v _q 
  have p17120 := n17120 _v _q 
  have p16929 := n16929 _v _q 
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
  have p13951 := n13951 _v _q 
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
  have p17064 := n17064 _v _q 
  have p17067 := n17067 _v _q 
  have p17069 := n17069 _v _q 
  have p17080 := n17080 _v _q 
  have p17072 := n17072 _v _q 
  have p17083 := n17083 _v _q 
  have p17074 := n17074 _v _q 
  have p20836 := n20836 _v _q 
  have p17078 := n17078 _v _q 
  have p20653 := n20653 _v _q 
  have p17087 := n17087 _v _q 
  have p17136 := n17136 _v _q 
  have p17055 := n17055 _v _q 
  have p17091 := n17091 _v _q 
  have p17093 := n17093 _v _q 
  have p17141 := n17141 _v _q 
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p17102 := n17102 _v _q 
  have p17100 := n17100 _v _q 
  have p19610 := n19610 _v _q 
  have p11462 := n11462 _v _q h7742
  have p4981 := n4981 _v _q h4260
  have p16349 := n16349 _v _q h2787
  have p10896 := n10896 _v _q 
  exact FloorCertificate.node_21143 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2849 _v) (e2863 _v) (e2877 _v) (e2883 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p10893 p4016 p16913 p5008 p15508 p15209 p19045 p4987 p16944 p17009 p16649 p17147 p4996 p5006 p16576 p4991 p4998 p17096 p17115 p17758 p17124 p17111 p11430 p5001 p19665 p17113 p17117 p20467 p17120 p16929 p4999 p17133 p17874 p17104 p17127 p17089 p20470 p253 p17020 p20274 p13951 p21142 p16729 p17050 p17138 p17060 p4989 p4983 p17122 p16778 p20829 p17108 p20461 p20426 p20126 p17110 p17053 p17131 p20096 p17058 p17294 p16943 p17064 p17067 p17069 p17080 p17072 p17083 p17074 p20836 p17078 p20653 p17087 p17136 p17055 p17091 p17093 p17141 p17098 p17106 p17102 p17100 p19610 p11462 p4981 p16349 p10896
theorem n21144 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h3152 : (e3152 _v)) (h4260 : (e4260 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h6454 : (e6454 _v)) : (e8045 _v) := by
  have p15206 := n15206 _v _q 
  have p20955 := n20955 _v _q h91 h3152 h4260 h4675 h4787 h4813 h6454
  change (e8049 _v) ∨ (e8045 _v) at p15206
  change (¬ (e8049 _v)) at p20955
  rcases p15206 with hlit | hlit
  · exact (False.elim (p20955 hlit))
  · exact hlit
theorem n21145 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h3152 : (e3152 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h6454 : (e6454 _v)) (h7807 : (e7807 _v)) : (e2358 _v) := by
  have p20260 := n20260 _v _q 
  have p11350 := n11350 _v _q h7807
  have p17953 := n17953 _v _q 
  have p20274 := n20274 _v _q 
  have p20426 := n20426 _v _q 
  have p20461 := n20461 _v _q 
  have p17020 := n17020 _v _q 
  have p16943 := n16943 _v _q 
  have p4999 := n4999 _v _q h91
  have p4983 := n4983 _v _q h4813
  have p5008 := n5008 _v _q h4787
  have p20096 := n20096 _v _q 
  have p5006 := n5006 _v _q h4675
  have p4998 := n4998 _v _q h3152
  have p16632 := n16632 _v _q h6454
  have p20467 := n20467 _v _q 
  have p15762 := n15762 _v _q h6454
  have p19610 := n19610 _v _q 
  have p17138 := n17138 _v _q h4306
  have p20954 := n20954 _v _q h91 h3152 h4260 h4675 h4787 h4813 h6454
  have p21144 := n21144 _v _q h91 h3152 h4260 h4675 h4787 h4813 h6454
  have p17294 := n17294 _v _q 
  have p17060 := n17060 _v _q h4653
  have p17874 := n17874 _v _q 
  have p20653 := n20653 _v _q 
  have p20126 := n20126 _v _q 
  have p20829 := n20829 _v _q 
  have p20836 := n20836 _v _q 
  have p17758 := n17758 _v _q 
  have p19665 := n19665 _v _q 
  have p20470 := n20470 _v _q 
  have p15764 := n15764 _v _q h6454
  have p21142 := n21142 _v _q h51 h4260 h4306 h4653 h4813
  have p20984 := n20984 _v _q h91 h3152 h4260 h4675 h4787 h4813 h6454
  change (¬ (e4567 _v)) ∨ (e2358 _v) ∨ (¬ (e3069 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4491 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4903 _v)) ∨ (¬ (e5208 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e5100 _v)) ∨ (¬ (e4398 _v)) ∨ (¬ (e8045 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e3976 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4724 _v)) ∨ (¬ (e4434 _v)) ∨ (e2475 _v) ∨ (e2303 _v) at p20260
  change (¬ (e2303 _v)) at p11350
  change (¬ (e2475 _v)) at p20954
  rcases p20260 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact (False.elim (hlit p21142))
  · exact hlit
  · exact (False.elim (hlit p20461))
  · exact (False.elim (hlit p16632))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p15762))
  · exact (False.elim (hlit p16943))
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p20096))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p20274))
  · exact (False.elim (hlit p17953))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p20984))
  · exact (False.elim (hlit p20467))
  · exact (False.elim (hlit p21144))
  · exact (False.elim (hlit p19610))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17020))
  · exact (False.elim (hlit p20426))
  · exact (False.elim (hlit p17294))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p17874))
  · exact (False.elim (hlit p20653))
  · exact (False.elim (hlit p20126))
  · exact (False.elim (hlit p20829))
  · exact (False.elim (hlit p20836))
  · exact (False.elim (hlit p17758))
  · exact (False.elim (hlit p19665))
  · exact (False.elim (hlit p20470))
  · exact (False.elim (hlit p15764))
  · exact (False.elim (p20954 hlit))
  · exact (False.elim (p11350 hlit))
theorem n21147 (_v : Vars) (_q : Query _v)  : (e21146 _v) := by
  by_contra hc
  change ¬ ((e2781 _v) ∨ (¬ (e2468 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e3152 _v))) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h191 : (e191 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h2468 : (e2468 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h4838 : (e4838 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h6776 : (e6776 _v) := (fun hn => hc (Or.inl hn))
  have p21133 := n21133 _v _q h51 h91 h191 h2468 h3152 h4306 h4653 h4813 h4838 h6776
  exact p21133
theorem n21148 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2468 : (e2468 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e6879 _v) := by
  have p14643 := n14643 _v _q 
  have p21134 := n21134 _v _q h51 h91 h2468 h2529 h4306 h4653 h4813
  change (e2296 _v) ∨ (¬ (e6878 _v)) at p14643
  change (¬ (e2296 _v)) at p21134
  rcases p14643 with hlit | hlit
  · exact (False.elim (p21134 hlit))
  · exact hlit
theorem n21149 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h2468 : (e2468 _v)) (h2529 : (e2529 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e3152 _v) := by
  have p15776 := n15776 _v _q 
  have p21148 := n21148 _v _q h51 h91 h2468 h2529 h4306 h4653 h4813
  change (e6878 _v) ∨ (e3152 _v) at p15776
  change (¬ (e6878 _v)) at p21148
  rcases p15776 with hlit | hlit
  · exact (False.elim (p21148 hlit))
  · exact hlit
theorem n21150 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2242 : (e2242 _v)) (h2733 : (e2733 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6549 : (e6549 _v)) (h6600 : (e6600 _v)) (h6776 : (e6776 _v)) : (e8035 _v) := by
  have p14871 := n14871 _v _q 
  have p21137 := n21137 _v _q h51 h91 h191 h2242 h2733 h4306 h4653 h4787 h4813 h4838 h6549 h6600 h6776
  change (¬ (e2475 _v)) ∨ (¬ (e8029 _v)) at p14871
  rcases p14871 with hlit | hlit
  · exact (False.elim (hlit p21137))
  · exact hlit
theorem n21151 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h2242 : (e2242 _v)) (h2733 : (e2733 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h6549 : (e6549 _v)) (h6600 : (e6600 _v)) (h6776 : (e6776 _v)) : (e4546 _v) := by
  have p16307 := n16307 _v _q 
  have p21150 := n21150 _v _q h51 h91 h191 h2242 h2733 h4306 h4653 h4787 h4813 h4838 h6549 h6600 h6776
  change (e8029 _v) ∨ (e4546 _v) at p16307
  change (¬ (e8029 _v)) at p21150
  rcases p16307 with hlit | hlit
  · exact (False.elim (p21150 hlit))
  · exact hlit
theorem n21152 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6423 : (e6423 _v)) : (e2781 _v) := by
  have p14570 := n14570 _v _q 
  have p21139 := n21139 _v _q h51 h4306 h4653 h4813 h6423
  change (e2781 _v) ∨ (¬ (e7781 _v)) at p14570
  rcases p14570 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p21139))
theorem n21153 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6423 : (e6423 _v)) : (e5138 _v) := by
  have p8578 := n8578 _v _q 
  have p21152 := n21152 _v _q h51 h4306 h4653 h4813 h6423
  have p12854 := n12854 _v _q h6423
  change (e2125 _v) ∨ (¬ (e79 _v)) ∨ (¬ (e2781 _v)) at p8578
  change (¬ (e2125 _v)) at p12854
  rcases p8578 with hlit | hlit | hlit
  · exact (False.elim (p12854 hlit))
  · exact hlit
  · exact (False.elim (hlit p21152))
theorem n21154 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6423 : (e6423 _v)) : (e8038 _v) := by
  have p11510 := n11510 _v _q 
  have p21153 := n21153 _v _q h51 h4306 h4653 h4813 h6423
  change (e79 _v) ∨ (¬ (e2475 _v)) at p11510
  change (¬ (e79 _v)) at p21153
  rcases p11510 with hlit | hlit
  · exact (False.elim (p21153 hlit))
  · exact hlit
theorem n21155 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6423 : (e6423 _v)) : (e8050 _v) := by
  have p15207 := n15207 _v _q 
  have p21154 := n21154 _v _q h51 h4306 h4653 h4813 h6423
  change (e2475 _v) ∨ (¬ (e8049 _v)) at p15207
  change (¬ (e2475 _v)) at p21154
  rcases p15207 with hlit | hlit
  · exact (False.elim (p21154 hlit))
  · exact hlit
theorem n21157 (_v : Vars) (_q : Query _v)  : (e21156 _v) := by
  by_contra hc
  change ¬ ((¬ (e2787 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4813 _v)) ∨ (e2132 _v) ∨ (¬ (e4260 _v)) ∨ (e2475 _v)) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h191 : (e191 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h2787 : (e2787 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4096 : (e4096 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h4260 : (e4260 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h4434 : (e4434 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4608 : (e4608 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h4675 : (e4675 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h4838 : (e4838 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h7742 : (e7742 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))
  have h8038 : (e8038 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))))))))))))))
  have p21143 := n21143 _v _q h51 h91 h191 h2787 h3152 h3937 h4096 h4260 h4306 h4434 h4608 h4653 h4675 h4787 h4813 h4838 h7742 h8038
  exact p21143
theorem n21158 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h3152 : (e3152 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h6454 : (e6454 _v)) (h7807 : (e7807 _v)) : (e7640 _v) := by
  have p14828 := n14828 _v _q 
  have p21145 := n21145 _v _q h51 h91 h3152 h4260 h4306 h4653 h4675 h4787 h4813 h6454 h7807
  change (¬ (e2358 _v)) ∨ (¬ (e7634 _v)) at p14828
  rcases p14828 with hlit | hlit
  · exact (False.elim (hlit p21145))
  · exact hlit
theorem n21159 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h3152 : (e3152 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h6454 : (e6454 _v)) (h7807 : (e7807 _v)) : (e4139 _v) := by
  have p16281 := n16281 _v _q 
  have p21158 := n21158 _v _q h51 h91 h3152 h4260 h4306 h4653 h4675 h4787 h4813 h6454 h7807
  change (e7634 _v) ∨ (e4139 _v) at p16281
  change (¬ (e7634 _v)) at p21158
  rcases p16281 with hlit | hlit
  · exact (False.elim (p21158 hlit))
  · exact hlit
end
end Assembly
