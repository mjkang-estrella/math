import Dag158
import generated.th_lemma_14
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n16839 (_v : Vars) (_q : Query _v) (h4302 : (e4302 _v)) : (e8348 _v) := by
  have p15312 := n15312 _v _q 
  have p16531 := n16531 _v _q h4302
  simp only [e2592, e6672, e8335, e8338, e8345, e8346, e8347, e8348, e11307] at *
  tauto
theorem n16840 (_v : Vars) (_q : Query _v) (h4302 : (e4302 _v)) : (e8338 _v) := by
  have p15580 := n15580 _v _q 
  have p16839 := n16839 _v _q h4302
  simp only [e8335, e8338, e8345, e8346, e8347, e8348, e8517] at *
  tauto
theorem n16841 (_v : Vars) (_q : Query _v) (h4302 : (e4302 _v)) : (e4731 _v) := by
  have p14698 := n14698 _v _q 
  have p16533 := n16533 _v _q h4302
  simp only [e2254, e4723, e4724, e4728, e4729, e4730, e4731, e6531, e8220] at *
  tauto
theorem n16842 (_v : Vars) (_q : Query _v) (h4302 : (e4302 _v)) : (e4724 _v) := by
  have p15518 := n15518 _v _q 
  have p16841 := n16841 _v _q h4302
  simp only [e4723, e4724, e4728, e4729, e4730, e4731, e4958] at *
  tauto
theorem n16843 (_v : Vars) (_q : Query _v) (h4302 : (e4302 _v)) : (e2697 _v) := by
  have p11391 := n11391 _v _q 
  have p16533 := n16533 _v _q h4302
  simp only [e2254, e2697, e6531, e11390] at *
  tauto
theorem n16844 (_v : Vars) (_q : Query _v) (h4302 : (e4302 _v)) : (e4499 _v) := by
  have p14700 := n14700 _v _q 
  have p16843 := n16843 _v _q h4302
  simp only [e2697, e4491, e4492, e4496, e4497, e4498, e4499, e6732, e7998] at *
  tauto
theorem n16845 (_v : Vars) (_q : Query _v) (h4302 : (e4302 _v)) : (e4491 _v) := by
  have p14969 := n14969 _v _q 
  have p16844 := n16844 _v _q h4302
  simp only [e4491, e4492, e4496, e4497, e4498, e4499, e4960] at *
  tauto
theorem n16847 (_v : Vars) (_q : Query _v)  : (e16846 _v) := by
  by_contra hc
  change ¬ ((e2529 _v) ∨ (¬ (e4897 _v)) ∨ (e2475 _v) ∨ (¬ (e8395 _v))) at hc
  have h4897 : (e4897 _v) := by
    tauto
  have h8038 : (e8038 _v) := by
    change (¬ (e2475 _v))
    tauto
  have h8310 : (e8310 _v) := by
    change (¬ (e2529 _v))
    tauto
  have h8395 : (e8395 _v) := by
    tauto
  have p16547 := n16547 _v _q h4897 h8038 h8310 h8395
  exact p16547
theorem n16848 (_v : Vars) (_q : Query _v) (h6636 : (e6636 _v)) : (e4546 _v) := by
  have p16307 := n16307 _v _q 
  have p16565 := n16565 _v _q h6636
  simp only [e4544, e4545, e4546, e4547, e8029, e8030, e8035] at *
  tauto
theorem n16849 (_v : Vars) (_q : Query _v) (h8310 : (e8310 _v)) : (e4420 _v) := by
  have p16832 := n16832 _v _q 
  have p12880 := n12880 _v _q h8310
  have p12885 := n12885 _v _q h8310
  simp only [e2303, e2475, e4419, e4420, e7807, e8038, e16831] at *
  tauto
theorem n16850 (_v : Vars) (_q : Query _v) (h2132 : (e2132 _v)) : (e4139 _v) := by
  have p16281 := n16281 _v _q 
  have p16570 := n16570 _v _q h2132
  simp only [e4139, e4140, e4141, e4142, e7634, e7635, e7640] at *
  tauto
theorem n16851 (_v : Vars) (_q : Query _v) (h6758 : (e6758 _v)) : (e225 _v) := by
  have p16653 := n16653 _v _q 
  have p16588 := n16588 _v _q h6758
  simp only [e225, e227, e230, e231, e5231, e5232, e5253] at *
  tauto
theorem n16852 (_v : Vars) (_q : Query _v) (h2061 : (e2061 _v)) (h6784 : (e6784 _v)) : (e4546 _v) := by
  have p16307 := n16307 _v _q 
  have p16597 := n16597 _v _q h2061 h6784
  simp only [e4544, e4545, e4546, e4547, e8029, e8030, e8035] at *
  tauto
theorem n16853 (_v : Vars) (_q : Query _v) (h6636 : (e6636 _v)) : (e225 _v) := by
  have p16653 := n16653 _v _q 
  have p16605 := n16605 _v _q h6636
  simp only [e225, e227, e230, e231, e5231, e5232, e5253] at *
  tauto
theorem n16854 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e442 _v) := by
  have p16149 := n16149 _v _q 
  have p16614 := n16614 _v _q h6784
  simp only [e440, e441, e442, e443, e5360, e5361, e5370] at *
  tauto
theorem n16855 (_v : Vars) (_q : Query _v) (h6636 : (e6636 _v)) : (e91 _v) := by
  have p16235 := n16235 _v _q 
  have p16618 := n16618 _v _q h6636
  simp only [e89, e91, e94, e95, e5134, e5135, e7983] at *
  tauto
theorem n16856 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e4199 _v) := by
  have p16212 := n16212 _v _q 
  have p16622 := n16622 _v _q h6784
  simp only [e4199, e4200, e4201, e4202, e7703, e7704, e7709] at *
  tauto
theorem n16857 (_v : Vars) (_q : Query _v) (h2061 : (e2061 _v)) (h6784 : (e6784 _v)) : (e30 _v) := by
  have p16290 := n16290 _v _q 
  have p16624 := n16624 _v _q h2061 h6784
  simp only [e28, e30, e34, e35, e5089, e5090, e5107] at *
  tauto
theorem n16858 (_v : Vars) (_q : Query _v)  : (e4588 _v) := by
  have p8526 := n8526 _v _q 
  have p14624 := n14624 _v _q 
  simp only [e4587, e4588, e8070, e8071, e8072, e8089, e8525] at *
  tauto
theorem n16859 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) : (e3158 _v) := by
  have p15126 := n15126 _v _q 
  have p15089 := n15089 _v _q h2468
  simp only [e3158, e3159, e3160, e3161, e3162, e3163, e4616] at *
  tauto
theorem n16860 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) : (e2061 _v) := by
  have p16578 := n16578 _v _q 
  have p5255 := n5255 _v _q 
  have p16858 := n16858 _v _q 
  have p16859 := n16859 _v _q h2468
  exact FloorCertificate.node_16860 (e2 _v) (e9 _v) (e17 _v) (e110 _v) (e2863 _v) (e2935 _v) p16578 p5255 p16858 p16859
theorem n16861 (_v : Vars) (_q : Query _v)  : (e8468 _v) := by
  simp only [e7714, e7717, e7724, e7725, e7726, e8468] at *
  tauto
theorem n16862 (_v : Vars) (_q : Query _v) (h4200 : (e4200 _v)) : (e7727 _v) := by
  have p15077 := n15077 _v _q 
  have p16642 := n16642 _v _q h4200
  simp only [e2680, e6716, e7714, e7717, e7724, e7725, e7726, e7727, e10986] at *
  tauto
theorem n16863 (_v : Vars) (_q : Query _v) (h4200 : (e4200 _v)) : (e7714 _v) := by
  have p16861 := n16861 _v _q 
  have p16862 := n16862 _v _q h4200
  simp only [e7714, e7717, e7724, e7725, e7726, e7727, e8468] at *
  tauto
theorem n16864 (_v : Vars) (_q : Query _v) (h2402 : (e2402 _v)) (h6750 : (e6750 _v)) : (e4285 _v) := by
  have p16274 := n16274 _v _q 
  have p16644 := n16644 _v _q h2402 h6750
  simp only [e4283, e4284, e4285, e4286, e7798, e7799, e7804] at *
  tauto
theorem n16865 (_v : Vars) (_q : Query _v) (h2787 : (e2787 _v)) (h8038 : (e8038 _v)) : (e2303 _v) := by
  have p16832 := n16832 _v _q 
  have p16349 := n16349 _v _q h2787
  have p8602 := n8602 _v _q h8038
  simp only [e2303, e2475, e4419, e4420, e8038, e16831] at *
  tauto
theorem n16866 (_v : Vars) (_q : Query _v) (h2787 : (e2787 _v)) (h8038 : (e8038 _v)) : (e7804 _v) := by
  have p14837 := n14837 _v _q 
  have p16865 := n16865 _v _q h2787 h8038
  simp only [e2303, e4283, e4284, e4285, e4286, e7798, e7804, e7807, e7809] at *
  tauto
theorem n16867 (_v : Vars) (_q : Query _v) (h6750 : (e6750 _v)) : (e225 _v) := by
  have p16653 := n16653 _v _q 
  have p16651 := n16651 _v _q h6750
  simp only [e225, e227, e230, e231, e5231, e5232, e5253] at *
  tauto
theorem n16868 (_v : Vars) (_q : Query _v) (h8320 : (e8320 _v)) : (e4838 _v) := by
  have p16285 := n16285 _v _q 
  have p16661 := n16661 _v _q h8320
  simp only [e4836, e4837, e4838, e4839, e8301, e8302, e8307] at *
  tauto
theorem n16869 (_v : Vars) (_q : Query _v) (h6583 : (e6583 _v)) : (e4139 _v) := by
  have p16281 := n16281 _v _q 
  have p16665 := n16665 _v _q h6583
  simp only [e4139, e4140, e4141, e4142, e7634, e7635, e7640] at *
  tauto
theorem n16871 (_v : Vars) (_q : Query _v)  : (e16870 _v) := by
  by_contra hc
  change ¬ ((¬ (e2733 _v)) ∨ (¬ (e91 _v)) ∨ (e2061 _v)) at hc
  have h91 : (e91 _v) := by
    tauto
  have h2733 : (e2733 _v) := by
    tauto
  have h6454 : (e6454 _v) := by
    change (¬ (e2061 _v))
    tauto
  have p16672 := n16672 _v _q h91 h2733 h6454
  exact p16672
theorem n16872 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h6454 : (e6454 _v)) : (e6750 _v) := by
  have p16871 := n16871 _v _q 
  have p8430 := n8430 _v _q h6454
  have p4999 := n4999 _v _q h91
  simp only [e91, e95, e2061, e2733, e6454, e6750, e16870] at *
  tauto
theorem n16873 (_v : Vars) (_q : Query _v) (h2132 : (e2132 _v)) : (e4546 _v) := by
  have p16307 := n16307 _v _q 
  have p16680 := n16680 _v _q h2132
  simp only [e4544, e4545, e4546, e4547, e8029, e8030, e8035] at *
  tauto
theorem n16874 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) (h6750 : (e6750 _v)) : (e4139 _v) := by
  have p16281 := n16281 _v _q 
  have p16696 := n16696 _v _q h2468 h6750
  simp only [e4139, e4140, e4141, e4142, e7634, e7635, e7640] at *
  tauto
theorem n16875 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) (h6750 : (e6750 _v)) : (e4285 _v) := by
  have p16274 := n16274 _v _q 
  have p16698 := n16698 _v _q h2468 h6750
  simp only [e4283, e4284, e4285, e4286, e7798, e7799, e7804] at *
  tauto
theorem n16876 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) (h6776 : (e6776 _v)) : (e4285 _v) := by
  have p16274 := n16274 _v _q 
  have p16702 := n16702 _v _q h2468 h6776
  simp only [e4283, e4284, e4285, e4286, e7798, e7799, e7804] at *
  tauto
theorem n16877 (_v : Vars) (_q : Query _v) (h13 : (e13 _v)) (h2303 : (e2303 _v)) : (e4419 _v) := by
  have p16347 := n16347 _v _q 
  have p16709 := n16709 _v _q h13 h2303
  simp only [e4417, e4418, e4419, e4420, e7921, e7922, e7927] at *
  tauto
theorem n16878 (_v : Vars) (_q : Query _v) (h13 : (e13 _v)) : (e4419 _v) := by
  have p16347 := n16347 _v _q 
  have p16712 := n16712 _v _q h13
  simp only [e4417, e4418, e4419, e4420, e7921, e7922, e7927] at *
  tauto
theorem n16879 (_v : Vars) (_q : Query _v) (h13 : (e13 _v)) : (e4419 _v) := by
  have p16347 := n16347 _v _q 
  have p16717 := n16717 _v _q h13
  simp only [e4417, e4418, e4419, e4420, e7921, e7922, e7927] at *
  tauto
theorem n16880 (_v : Vars) (_q : Query _v) (h7807 : (e7807 _v)) (h8038 : (e8038 _v)) : (e4420 _v) := by
  have p16832 := n16832 _v _q 
  have p11350 := n11350 _v _q h7807
  have p8602 := n8602 _v _q h8038
  simp only [e2303, e2475, e4419, e4420, e7807, e8038, e16831] at *
  tauto
theorem n16881 (_v : Vars) (_q : Query _v) (h7807 : (e7807 _v)) (h8038 : (e8038 _v)) : (e7921 _v) := by
  have p16347 := n16347 _v _q 
  have p16880 := n16880 _v _q h7807 h8038
  simp only [e4417, e4418, e4419, e4420, e7921, e7922] at *
  tauto
theorem n16882 (_v : Vars) (_q : Query _v) (h2402 : (e2402 _v)) (h6776 : (e6776 _v)) : (e4139 _v) := by
  have p16281 := n16281 _v _q 
  have p16720 := n16720 _v _q h2402 h6776
  simp only [e4139, e4140, e4141, e4142, e7634, e7635, e7640] at *
  tauto
theorem n16883 (_v : Vars) (_q : Query _v) (h2296 : (e2296 _v)) (h6776 : (e6776 _v)) : (e4546 _v) := by
  have p16307 := n16307 _v _q 
  have p16722 := n16722 _v _q h2296 h6776
  simp only [e4544, e4545, e4546, e4547, e8029, e8030, e8035] at *
  tauto
theorem n16884 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) (h5195 : (e5195 _v)) : (e2781 _v) := by
  have p8549 := n8549 _v _q h5195
  have p16859 := n16859 _v _q h2468
  have p16578 := n16578 _v _q 
  have p16858 := n16858 _v _q 
  exact FloorCertificate.node_16884 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) (e2863 _v) (e2935 _v) p8549 p16859 p16578 p16858
theorem n16885 (_v : Vars) (_q : Query _v) (h3158 : (e3158 _v)) : (e3158 _v) := by
  exact h3158
end
end Assembly
