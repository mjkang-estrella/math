import Dag152
import generated.th_lemma_14
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n16559 (_v : Vars) (_q : Query _v) (h6531 : (e6531 _v)) : (e8307 _v) := by
  have p14906 := n14906 _v _q 
  have p16558 := n16558 _v _q h6531
  simp only [e2529, e4836, e4837, e4838, e4839, e8301, e8307, e8310, e8312] at *
  tauto
theorem n16560 (_v : Vars) (_q : Query _v) (h6531 : (e6531 _v)) : (e4838 _v) := by
  have p16285 := n16285 _v _q 
  have p16559 := n16559 _v _q h6531
  simp only [e4836, e4837, e4838, e4839, e8301, e8302, e8307] at *
  tauto
theorem n16561 (_v : Vars) (_q : Query _v) (h6531 : (e6531 _v)) : (e2358 _v) := by
  have p12849 := n12849 _v _q 
  have p14716 := n14716 _v _q h6531
  simp only [e2358, e2364, e6583, e12848] at *
  tauto
theorem n16562 (_v : Vars) (_q : Query _v) (h6531 : (e6531 _v)) : (e7640 _v) := by
  have p14828 := n14828 _v _q 
  have p16561 := n16561 _v _q h6531
  simp only [e2358, e4139, e4140, e4141, e4142, e6571, e7634, e7640, e7643] at *
  tauto
theorem n16563 (_v : Vars) (_q : Query _v) (h6531 : (e6531 _v)) : (e4139 _v) := by
  have p16281 := n16281 _v _q 
  have p16562 := n16562 _v _q h6531
  simp only [e4139, e4140, e4141, e4142, e7634, e7635, e7640] at *
  tauto
theorem n16564 (_v : Vars) (_q : Query _v) (h6636 : (e6636 _v)) : (e2475 _v) := by
  have p11031 := n11031 _v _q h6636
  have p8663 := n8663 _v _q 
  exact FloorCertificate.node_16564 (e2 _v) (e7 _v) (e17 _v) (e45 _v) p11031 p8663
theorem n16565 (_v : Vars) (_q : Query _v) (h6636 : (e6636 _v)) : (e8035 _v) := by
  have p14871 := n14871 _v _q 
  have p16564 := n16564 _v _q h6636
  simp only [e2475, e4544, e4545, e4546, e4547, e8029, e8035, e8038, e8040] at *
  tauto
theorem n16566 (_v : Vars) (_q : Query _v) (h2132 : (e2132 _v)) : (e7804 _v) := by
  have p14837 := n14837 _v _q 
  have p12942 := n12942 _v _q h2132
  simp only [e2303, e4283, e4284, e4285, e4286, e7798, e7804, e7807, e7809] at *
  tauto
theorem n16567 (_v : Vars) (_q : Query _v) (h2132 : (e2132 _v)) : (e4285 _v) := by
  have p16274 := n16274 _v _q 
  have p16566 := n16566 _v _q h2132
  simp only [e4283, e4284, e4285, e4286, e7798, e7799, e7804] at *
  tauto
theorem n16568 (_v : Vars) (_q : Query _v) (h2132 : (e2132 _v)) (h6636 : (e6636 _v)) : (e4648 _v) := by
  have p15027 := n15027 _v _q 
  have p15631 := n15631 _v _q h2132 h6636
  simp only [e4648, e4649, e4650, e4651, e8149, e8150, e8157] at *
  tauto
theorem n16569 (_v : Vars) (_q : Query _v) (h2132 : (e2132 _v)) : (e2358 _v) := by
  have p8451 := n8451 _v _q 
  have p12942 := n12942 _v _q h2132
  simp only [e2303, e2358, e7807, e8450] at *
  tauto
theorem n16570 (_v : Vars) (_q : Query _v) (h2132 : (e2132 _v)) : (e7640 _v) := by
  have p14828 := n14828 _v _q 
  have p16569 := n16569 _v _q h2132
  simp only [e2358, e4139, e4140, e4141, e4142, e6571, e7634, e7640, e7643] at *
  tauto
theorem n16571 (_v : Vars) (_q : Query _v) (h2529 : (e2529 _v)) : (e8307 _v) := by
  have p14906 := n14906 _v _q 
  have p8548 := n8548 _v _q h2529
  simp only [e2529, e4836, e4837, e4838, e4839, e8301, e8307, e8310, e8312] at *
  tauto
theorem n16572 (_v : Vars) (_q : Query _v) (h2529 : (e2529 _v)) : (e4838 _v) := by
  have p16285 := n16285 _v _q 
  have p16571 := n16571 _v _q h2529
  simp only [e4836, e4837, e4838, e4839, e8301, e8302, e8307] at *
  tauto
theorem n16573 (_v : Vars) (_q : Query _v)  : (e5025 _v) := by
  simp only [e3158, e3159, e3160, e3161, e3162, e5025] at *
  tauto
theorem n16574 (_v : Vars) (_q : Query _v) (h4611 : (e4611 _v)) : (e4616 _v) := by
  have p14684 := n14684 _v _q 
  have p15645 := n15645 _v _q h4611
  simp only [e2179, e3158, e3159, e3160, e3161, e3162, e4616, e6501, e8109] at *
  tauto
theorem n16575 (_v : Vars) (_q : Query _v) (h4611 : (e4611 _v)) : (e3160 _v) := by
  have p16573 := n16573 _v _q 
  have p16574 := n16574 _v _q h4611
  simp only [e3158, e3159, e3160, e3161, e3162, e4616, e5025] at *
  tauto
theorem n16576 (_v : Vars) (_q : Query _v)  : (e4587 _v) := by
  have p8074 := n8074 _v _q 
  have p14624 := n14624 _v _q 
  simp only [e4587, e4588, e8070, e8071, e8072, e8073, e8089] at *
  tauto
theorem n16577 (_v : Vars) (_q : Query _v) (h4611 : (e4611 _v)) : (e7489 _v) := by
  have p15645 := n15645 _v _q h4611
  have p15643 := n15643 _v _q h4611
  have p16575 := n16575 _v _q h4611
  have p16576 := n16576 _v _q 
  exact FloorCertificate.node_16577 (e2 _v) (e9 _v) (e17 _v) (e2863 _v) (e2935 _v) p15645 p15643 p16575 p16576
theorem n16578 (_v : Vars) (_q : Query _v)  : (e4610 _v) := by
  by_contra hc
  change ¬ (e4610 _v) at hc
  have h4611 : (e4611 _v) := by
    change (¬ (e4610 _v))
    tauto
  have p16577 := n16577 _v _q h4611
  exact p16577
theorem n16579 (_v : Vars) (_q : Query _v) (h5108 : (e5108 _v)) (h6454 : (e6454 _v)) : (e4260 _v) := by
  have p15824 := n15824 _v _q 
  have p15647 := n15647 _v _q h5108 h6454
  simp only [e4258, e4259, e4260, e4261, e7781, e7782, e7789] at *
  tauto
theorem n16580 (_v : Vars) (_q : Query _v) (h6758 : (e6758 _v)) : (e4608 _v) := by
  have p15033 := n15033 _v _q 
  have p15656 := n15656 _v _q h6758
  simp only [e4608, e4609, e4610, e4611, e8095, e8096, e8103] at *
  tauto
theorem n16581 (_v : Vars) (_q : Query _v) (h6758 : (e6758 _v)) : (e4813 _v) := by
  have p16259 := n16259 _v _q 
  have p15658 := n15658 _v _q h6758
  simp only [e4811, e4812, e4813, e4814, e8284, e8285, e8292] at *
  tauto
theorem n16582 (_v : Vars) (_q : Query _v) (h6758 : (e6758 _v)) : (e3152 _v) := by
  have p15776 := n15776 _v _q 
  have p15660 := n15660 _v _q h6758
  simp only [e3150, e3152, e3155, e3156, e6878, e6879, e8223] at *
  tauto
theorem n16583 (_v : Vars) (_q : Query _v) (h6758 : (e6758 _v)) : (e4369 _v) := by
  have p16222 := n16222 _v _q 
  have p15662 := n15662 _v _q h6758
  simp only [e4367, e4368, e4369, e4370, e7887, e7888, e7895] at *
  tauto
theorem n16584 (_v : Vars) (_q : Query _v) (h6758 : (e6758 _v)) : (e5135 _v) := by
  have p14729 := n14729 _v _q 
  have p14127 := n14127 _v _q h6758
  simp only [e79, e89, e91, e94, e95, e5134, e5135, e5138, e5140] at *
  tauto
theorem n16585 (_v : Vars) (_q : Query _v) (h6758 : (e6758 _v)) : (e91 _v) := by
  have p16235 := n16235 _v _q 
  have p16584 := n16584 _v _q h6758
  simp only [e89, e91, e94, e95, e5134, e5135, e7983] at *
  tauto
theorem n16586 (_v : Vars) (_q : Query _v) (h6758 : (e6758 _v)) : (e4096 _v) := by
  have p15703 := n15703 _v _q 
  have p15665 := n15665 _v _q h6758
  simp only [e4096, e4097, e4098, e4099, e7589, e7590, e7597] at *
  tauto
theorem n16587 (_v : Vars) (_q : Query _v) (h6758 : (e6758 _v)) : (e214 _v) := by
  have p10893 := n10893 _v _q 
  have p10896 := n10896 _v _q 
  have p11375 := n11375 _v _q 
  have p8425 := n8425 _v _q h6758
  have p8663 := n8663 _v _q 
  exact FloorCertificate.node_16587 (e2 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p10893 p10896 p11375 p8425 p8663
theorem n16588 (_v : Vars) (_q : Query _v) (h6758 : (e6758 _v)) : (e5232 _v) := by
  have p14731 := n14731 _v _q 
  have p16587 := n16587 _v _q h6758
  simp only [e214, e225, e227, e230, e231, e5223, e5231, e5232, e5235] at *
  tauto
theorem n16589 (_v : Vars) (_q : Query _v) (h6758 : (e6758 _v)) : (e4156 _v) := by
  have p11524 := n11524 _v _q 
  have p15674 := n15674 _v _q h6758
  simp only [e4156, e4157, e4158, e4159, e7660, e7661, e7668] at *
  tauto
theorem n16590 (_v : Vars) (_q : Query _v) (h6758 : (e6758 _v)) : (e2680 _v) := by
  have p7732 := n7732 _v _q 
  have p14127 := n14127 _v _q h6758
  simp only [e79, e2680, e5138, e7731] at *
  tauto
theorem n16591 (_v : Vars) (_q : Query _v) (h6758 : (e6758 _v)) : (e7709 _v) := by
  have p14832 := n14832 _v _q 
  have p16590 := n16590 _v _q h6758
  simp only [e2680, e4199, e4200, e4201, e4202, e6716, e7703, e7709, e7712] at *
  tauto
theorem n16592 (_v : Vars) (_q : Query _v) (h6758 : (e6758 _v)) : (e4199 _v) := by
  have p16212 := n16212 _v _q 
  have p16591 := n16591 _v _q h6758
  simp only [e4199, e4200, e4201, e4202, e7703, e7704, e7709] at *
  tauto
theorem n16593 (_v : Vars) (_q : Query _v) (h6758 : (e6758 _v)) : (e436 _v) := by
  have p7492 := n7492 _v _q 
  have p14127 := n14127 _v _q h6758
  simp only [e79, e436, e5138, e7491] at *
  tauto
theorem n16594 (_v : Vars) (_q : Query _v) (h6758 : (e6758 _v)) : (e5370 _v) := by
  have p14735 := n14735 _v _q 
  have p16593 := n16593 _v _q h6758
  simp only [e436, e440, e441, e442, e443, e5360, e5362, e5370, e5373] at *
  tauto
theorem n16595 (_v : Vars) (_q : Query _v) (h6758 : (e6758 _v)) : (e442 _v) := by
  have p16149 := n16149 _v _q 
  have p16594 := n16594 _v _q h6758
  simp only [e440, e441, e442, e443, e5360, e5361, e5370] at *
  tauto
theorem n16596 (_v : Vars) (_q : Query _v) (h2061 : (e2061 _v)) (h6784 : (e6784 _v)) : (e2475 _v) := by
  have p10896 := n10896 _v _q 
  have p11473 := n11473 _v _q h6784
  have p11409 := n11409 _v _q h2061
  exact FloorCertificate.node_16596 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p10896 p11473 p11409
theorem n16597 (_v : Vars) (_q : Query _v) (h2061 : (e2061 _v)) (h6784 : (e6784 _v)) : (e8035 _v) := by
  have p14871 := n14871 _v _q 
  have p16596 := n16596 _v _q h2061 h6784
  simp only [e2475, e4544, e4545, e4546, e4547, e8029, e8035, e8038, e8040] at *
  tauto
theorem n16598 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e4675 _v) := by
  have p15965 := n15965 _v _q 
  have p15676 := n15676 _v _q h6784
  simp only [e4673, e4674, e4675, e4676, e8166, e8167, e8174] at *
  tauto
theorem n16599 (_v : Vars) (_q : Query _v) (h6636 : (e6636 _v)) : (e4675 _v) := by
  have p15965 := n15965 _v _q 
  have p15678 := n15678 _v _q h6636
  simp only [e4673, e4674, e4675, e4676, e8166, e8167, e8174] at *
  tauto
theorem n16600 (_v : Vars) (_q : Query _v) (h6636 : (e6636 _v)) : (e70 _v) := by
  have p15648 := n15648 _v _q 
  have p15680 := n15680 _v _q h6636
  simp only [e70, e72, e75, e76, e5118, e5119, e7441] at *
  tauto
theorem n16601 (_v : Vars) (_q : Query _v) (h6636 : (e6636 _v)) : (e7709 _v) := by
  have p14832 := n14832 _v _q 
  have p14129 := n14129 _v _q h6636
  simp only [e2680, e4199, e4200, e4201, e4202, e6716, e7703, e7709, e7712] at *
  tauto
theorem n16602 (_v : Vars) (_q : Query _v) (h6636 : (e6636 _v)) : (e4199 _v) := by
  have p16212 := n16212 _v _q 
  have p16601 := n16601 _v _q h6636
  simp only [e4199, e4200, e4201, e4202, e7703, e7704, e7709] at *
  tauto
theorem n16603 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e4260 _v) := by
  have p15824 := n15824 _v _q 
  have p15683 := n15683 _v _q h6784
  simp only [e4258, e4259, e4260, e4261, e7781, e7782, e7789] at *
  tauto
end
end Assembly
