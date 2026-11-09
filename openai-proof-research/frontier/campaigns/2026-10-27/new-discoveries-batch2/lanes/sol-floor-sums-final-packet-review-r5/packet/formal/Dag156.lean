import Dag155
import generated.th_lemma_14
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n16694 (_v : Vars) (_q : Query _v) (h13 : (e13 _v)) : (e4546 _v) := by
  have p16307 := n16307 _v _q 
  have p16693 := n16693 _v _q h13
  simp only [e4544, e4545, e4546, e4547, e8029, e8030, e8035] at *
  tauto
theorem n16695 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) (h6750 : (e6750 _v)) : (e2358 _v) := by
  have p8438 := n8438 _v _q h2468
  have p8420 := n8420 _v _q h6750
  have p4016 := n4016 _v _q 
  exact FloorCertificate.node_16695 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8438 p8420 p4016
theorem n16696 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) (h6750 : (e6750 _v)) : (e7640 _v) := by
  have p14828 := n14828 _v _q 
  have p16695 := n16695 _v _q h2468 h6750
  simp only [e2358, e4139, e4140, e4141, e4142, e6571, e7634, e7640, e7643] at *
  tauto
theorem n16697 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) (h6750 : (e6750 _v)) : (e2303 _v) := by
  have p8420 := n8420 _v _q h6750
  have p8438 := n8438 _v _q h2468
  have p4016 := n4016 _v _q 
  exact FloorCertificate.node_16697 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8420 p8438 p4016
theorem n16698 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) (h6750 : (e6750 _v)) : (e7804 _v) := by
  have p14837 := n14837 _v _q 
  have p16697 := n16697 _v _q h2468 h6750
  simp only [e2303, e4283, e4284, e4285, e4286, e7798, e7804, e7807, e7809] at *
  tauto
theorem n16699 (_v : Vars) (_q : Query _v) (h6750 : (e6750 _v)) : (e4260 _v) := by
  have p15824 := n15824 _v _q 
  have p16071 := n16071 _v _q h6750
  simp only [e4258, e4259, e4260, e4261, e7781, e7782, e7789] at *
  tauto
theorem n16700 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) (h6776 : (e6776 _v)) : (e7640 _v) := by
  have p14828 := n14828 _v _q 
  have p11568 := n11568 _v _q h2468 h6776
  simp only [e2358, e4139, e4140, e4141, e4142, e6571, e7634, e7640, e7643] at *
  tauto
theorem n16701 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) (h6776 : (e6776 _v)) : (e4139 _v) := by
  have p16281 := n16281 _v _q 
  have p16700 := n16700 _v _q h2468 h6776
  simp only [e4139, e4140, e4141, e4142, e7634, e7635, e7640] at *
  tauto
theorem n16702 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) (h6776 : (e6776 _v)) : (e7804 _v) := by
  have p14837 := n14837 _v _q 
  have p11567 := n11567 _v _q h2468 h6776
  simp only [e2303, e4283, e4284, e4285, e4286, e7798, e7804, e7807, e7809] at *
  tauto
theorem n16703 (_v : Vars) (_q : Query _v) (h2529 : (e2529 _v)) : (e196 _v) := by
  have p8552 := n8552 _v _q 
  have p8548 := n8548 _v _q h2529
  simp only [e196, e2529, e8310, e8551] at *
  tauto
theorem n16704 (_v : Vars) (_q : Query _v) (h2529 : (e2529 _v)) : (e5203 _v) := by
  have p14730 := n14730 _v _q 
  have p16703 := n16703 _v _q h2529
  simp only [e191, e192, e193, e194, e196, e5193, e5195, e5203, e5206] at *
  tauto
theorem n16705 (_v : Vars) (_q : Query _v) (h2529 : (e2529 _v)) : (e191 _v) := by
  have p16442 := n16442 _v _q 
  have p16704 := n16704 _v _q h2529
  simp only [e191, e192, e193, e194, e5193, e5194, e5203] at *
  tauto
theorem n16706 (_v : Vars) (_q : Query _v) (h2529 : (e2529 _v)) (h6525 : (e6525 _v)) : (e4260 _v) := by
  have p15824 := n15824 _v _q 
  have p16076 := n16076 _v _q h2529 h6525
  simp only [e4258, e4259, e4260, e4261, e7781, e7782, e7789] at *
  tauto
theorem n16707 (_v : Vars) (_q : Query _v) (h2179 : (e2179 _v)) (h6525 : (e6525 _v)) (h6571 : (e6571 _v)) (h6750 : (e6750 _v)) : (e3937 _v) := by
  have p15012 := n15012 _v _q 
  have p16078 := n16078 _v _q h2179 h6525 h6571 h6750
  simp only [e3937, e3939, e3942, e3943, e7415, e7416, e7633] at *
  tauto
theorem n16708 (_v : Vars) (_q : Query _v) (h13 : (e13 _v)) (h2303 : (e2303 _v)) : (e2787 _v) := by
  have p8461 := n8461 _v _q 
  have p16692 := n16692 _v _q h13
  have p8448 := n8448 _v _q h2303
  simp only [e2303, e2475, e2787, e7807, e8038, e8460] at *
  tauto
theorem n16709 (_v : Vars) (_q : Query _v) (h13 : (e13 _v)) (h2303 : (e2303 _v)) : (e7927 _v) := by
  have p14855 := n14855 _v _q 
  have p16708 := n16708 _v _q h13 h2303
  simp only [e2787, e4417, e4418, e4419, e4420, e6772, e7921, e7927, e7930] at *
  tauto
theorem n16710 (_v : Vars) (_q : Query _v) (h13 : (e13 _v)) : (e2303 _v) := by
  have p11468 := n11468 _v _q 
  have p11396 := n11396 _v _q h13
  simp only [e13, e2303, e5093, e11467] at *
  tauto
theorem n16711 (_v : Vars) (_q : Query _v) (h13 : (e13 _v)) : (e2787 _v) := by
  have p8461 := n8461 _v _q 
  have p16692 := n16692 _v _q h13
  have p16710 := n16710 _v _q h13
  simp only [e2303, e2475, e2787, e7807, e8038, e8460] at *
  tauto
theorem n16712 (_v : Vars) (_q : Query _v) (h13 : (e13 _v)) : (e7927 _v) := by
  have p14855 := n14855 _v _q 
  have p16711 := n16711 _v _q h13
  simp only [e2787, e4417, e4418, e4419, e4420, e6772, e7921, e7927, e7930] at *
  tauto
theorem n16713 (_v : Vars) (_q : Query _v) (h13 : (e13 _v)) : (e7804 _v) := by
  have p14837 := n14837 _v _q 
  have p16710 := n16710 _v _q h13
  simp only [e2303, e4283, e4284, e4285, e4286, e7798, e7804, e7807, e7809] at *
  tauto
theorem n16714 (_v : Vars) (_q : Query _v) (h13 : (e13 _v)) : (e4285 _v) := by
  have p16274 := n16274 _v _q 
  have p16713 := n16713 _v _q h13
  simp only [e4283, e4284, e4285, e4286, e7798, e7799, e7804] at *
  tauto
theorem n16715 (_v : Vars) (_q : Query _v) (h2529 : (e2529 _v)) (h6525 : (e6525 _v)) (h6571 : (e6571 _v)) : (e3937 _v) := by
  have p15012 := n15012 _v _q 
  have p16082 := n16082 _v _q h2529 h6525 h6571
  simp only [e3937, e3939, e3942, e3943, e7415, e7416, e7633] at *
  tauto
theorem n16716 (_v : Vars) (_q : Query _v) (h13 : (e13 _v)) : (e2787 _v) := by
  have p8461 := n8461 _v _q 
  have p16710 := n16710 _v _q h13
  have p16692 := n16692 _v _q h13
  simp only [e2303, e2475, e2787, e7807, e8038, e8460] at *
  tauto
theorem n16717 (_v : Vars) (_q : Query _v) (h13 : (e13 _v)) : (e7927 _v) := by
  have p14855 := n14855 _v _q 
  have p16716 := n16716 _v _q h13
  simp only [e2787, e4417, e4418, e4419, e4420, e6772, e7921, e7927, e7930] at *
  tauto
theorem n16718 (_v : Vars) (_q : Query _v) (h6423 : (e6423 _v)) : (e4675 _v) := by
  have p15965 := n15965 _v _q 
  have p16086 := n16086 _v _q h6423
  simp only [e4673, e4674, e4675, e4676, e8166, e8167, e8174] at *
  tauto
theorem n16719 (_v : Vars) (_q : Query _v) (h2402 : (e2402 _v)) (h6776 : (e6776 _v)) : (e2358 _v) := by
  have p8601 := n8601 _v _q h6776
  have p8591 := n8591 _v _q h2402
  exact FloorCertificate.node_16719 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8601 p8591
theorem n16720 (_v : Vars) (_q : Query _v) (h2402 : (e2402 _v)) (h6776 : (e6776 _v)) : (e7640 _v) := by
  have p14828 := n14828 _v _q 
  have p16719 := n16719 _v _q h2402 h6776
  simp only [e2358, e4139, e4140, e4141, e4142, e6571, e7634, e7640, e7643] at *
  tauto
theorem n16721 (_v : Vars) (_q : Query _v) (h2296 : (e2296 _v)) (h6776 : (e6776 _v)) : (e2475 _v) := by
  have p8601 := n8601 _v _q h6776
  have p8583 := n8583 _v _q h2296
  exact FloorCertificate.node_16721 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8601 p8583
theorem n16722 (_v : Vars) (_q : Query _v) (h2296 : (e2296 _v)) (h6776 : (e6776 _v)) : (e8035 _v) := by
  have p14871 := n14871 _v _q 
  have p16721 := n16721 _v _q h2296 h6776
  simp only [e2475, e4544, e4545, e4546, e4547, e8029, e8035, e8038, e8040] at *
  tauto
theorem n16723 (_v : Vars) (_q : Query _v) (h8320 : (e8320 _v)) : (e5203 _v) := by
  have p14730 := n14730 _v _q 
  have p16088 := n16088 _v _q h8320
  simp only [e191, e192, e193, e194, e196, e5193, e5195, e5203, e5206] at *
  tauto
theorem n16724 (_v : Vars) (_q : Query _v) (h8320 : (e8320 _v)) : (e191 _v) := by
  have p16442 := n16442 _v _q 
  have p16723 := n16723 _v _q h8320
  simp only [e191, e192, e193, e194, e5193, e5194, e5203] at *
  tauto
theorem n16725 (_v : Vars) (_q : Query _v) (h6423 : (e6423 _v)) : (e3152 _v) := by
  have p15776 := n15776 _v _q 
  have p16098 := n16098 _v _q h6423
  simp only [e3150, e3152, e3155, e3156, e6878, e6879, e8223] at *
  tauto
theorem n16726 (_v : Vars) (_q : Query _v) (h6454 : (e6454 _v)) : (e4675 _v) := by
  have p15965 := n15965 _v _q 
  have p16106 := n16106 _v _q h6454
  simp only [e4673, e4674, e4675, e4676, e8166, e8167, e8174] at *
  tauto
theorem n16727 (_v : Vars) (_q : Query _v) (h6454 : (e6454 _v)) : (e3152 _v) := by
  have p15776 := n15776 _v _q 
  have p16111 := n16111 _v _q h6454
  simp only [e3150, e3152, e3155, e3156, e6878, e6879, e8223] at *
  tauto
theorem n16728 (_v : Vars) (_q : Query _v) (h7495 : (e7495 _v)) : (e7495 _v) := by
  exact h7495
theorem n16729 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) : (e51 _v) := by
  exact h51
theorem n16730 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h5108 : (e5108 _v)) (h7495 : (e7495 _v)) : (e7489 _v) := by
  have p16728 := n16728 _v _q h7495
  have p16729 := n16729 _v _q h51
  have p16117 := n16117 _v _q h5108
  have p11366 := n11366 _v _q h5108
  exact FloorCertificate.node_16730 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e61 _v) p16728 p16729 p16117 p11366
theorem n16732 (_v : Vars) (_q : Query _v)  : (e16731 _v) := by
  by_contra hc
  change ¬ ((e48 _v) ∨ (¬ (e7495 _v)) ∨ (¬ (e51 _v))) at hc
  have h51 : (e51 _v) := by
    tauto
  have h5108 : (e5108 _v) := by
    change (¬ (e48 _v))
    tauto
  have h7495 : (e7495 _v) := by
    tauto
  have p16730 := n16730 _v _q h51 h5108 h7495
  exact p16730
theorem n16733 (_v : Vars) (_q : Query _v)  : (e8599 _v) := by
  simp only [e7493, e7494, e7495, e7496, e7497, e8599] at *
  tauto
theorem n16734 (_v : Vars) (_q : Query _v) (h5195 : (e5195 _v)) : (e7495 _v) := by
  have p16733 := n16733 _v _q 
  have p16673 := n16673 _v _q h5195
  simp only [e7493, e7494, e7495, e7496, e7497, e7517, e8599] at *
  tauto
theorem n16735 (_v : Vars) (_q : Query _v) (h6454 : (e6454 _v)) : (e4608 _v) := by
  have p15033 := n15033 _v _q 
  have p16124 := n16124 _v _q h6454
  simp only [e4608, e4609, e4610, e4611, e8095, e8096, e8103] at *
  tauto
theorem n16736 (_v : Vars) (_q : Query _v) (h6454 : (e6454 _v)) : (e4675 _v) := by
  have p15965 := n15965 _v _q 
  have p16126 := n16126 _v _q h6454
  simp only [e4673, e4674, e4675, e4676, e8166, e8167, e8174] at *
  tauto
theorem n16737 (_v : Vars) (_q : Query _v) (h2475 : (e2475 _v)) : (e2529 _v) := by
  have p11493 := n11493 _v _q 
  have p8457 := n8457 _v _q h2475
  simp only [e2475, e2529, e8038, e11492] at *
  tauto
theorem n16738 (_v : Vars) (_q : Query _v) (h2475 : (e2475 _v)) : (e8307 _v) := by
  have p14906 := n14906 _v _q 
  have p16737 := n16737 _v _q h2475
  simp only [e2529, e4836, e4837, e4838, e4839, e8301, e8307, e8310, e8312] at *
  tauto
theorem n16739 (_v : Vars) (_q : Query _v) (h2475 : (e2475 _v)) : (e4838 _v) := by
  have p16285 := n16285 _v _q 
  have p16738 := n16738 _v _q h2475
  simp only [e4836, e4837, e4838, e4839, e8301, e8302, e8307] at *
  tauto
end
end Assembly
