import Dag157
import generated.th_lemma_14
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n16791 (_v : Vars) (_q : Query _v)  : (e4237 _v) := by
  have p8481 := n8481 _v _q 
  have p14568 := n14568 _v _q 
  simp only [e4236, e4237, e7756, e7757, e7758, e7775, e8480] at *
  tauto
theorem n16792 (_v : Vars) (_q : Query _v) (h4563 : (e4563 _v)) : (e2482 _v) := by
  have p10893 := n10893 _v _q 
  have p16791 := n16791 _v _q 
  have p15156 := n15156 _v _q h4563
  have p16330 := n16330 _v _q h4563
  exact FloorCertificate.node_16792 (e2 _v) (e7 _v) (e17 _v) (e45 _v) (e2834 _v) (e2918 _v) p10893 p16791 p15156 p16330
theorem n16793 (_v : Vars) (_q : Query _v) (h4563 : (e4563 _v)) : (e4405 _v) := by
  have p14702 := n14702 _v _q 
  have p16792 := n16792 _v _q h4563
  simp only [e2482, e4397, e4398, e4402, e4403, e4404, e4405, e6636, e7918] at *
  tauto
theorem n16794 (_v : Vars) (_q : Query _v) (h4563 : (e4563 _v)) : (e4398 _v) := by
  have p14976 := n14976 _v _q 
  have p16793 := n16793 _v _q h4563
  simp only [e4397, e4398, e4402, e4403, e4404, e4405, e4962] at *
  tauto
theorem n16795 (_v : Vars) (_q : Query _v) (h4563 : (e4563 _v)) : (e2697 _v) := by
  have p16791 := n16791 _v _q 
  have p15156 := n15156 _v _q h4563
  have p16330 := n16330 _v _q h4563
  have p10893 := n10893 _v _q 
  have p10896 := n10896 _v _q 
  exact FloorCertificate.node_16795 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e2834 _v) (e2918 _v) p16791 p15156 p16330 p10893 p10896
theorem n16796 (_v : Vars) (_q : Query _v) (h4563 : (e4563 _v)) : (e4499 _v) := by
  have p14700 := n14700 _v _q 
  have p16795 := n16795 _v _q h4563
  simp only [e2697, e4491, e4492, e4496, e4497, e4498, e4499, e6732, e7998] at *
  tauto
theorem n16797 (_v : Vars) (_q : Query _v) (h4563 : (e4563 _v)) : (e4491 _v) := by
  have p14969 := n14969 _v _q 
  have p16796 := n16796 _v _q h4563
  simp only [e4491, e4492, e4496, e4497, e4498, e4499, e4960] at *
  tauto
theorem n16798 (_v : Vars) (_q : Query _v) (h8345 : (e8345 _v)) : (e4855 _v) := by
  have p16317 := n16317 _v _q 
  have p16340 := n16340 _v _q h8345
  simp only [e4855, e4856, e4857, e4858, e8324, e8325, e8330] at *
  tauto
theorem n16799 (_v : Vars) (_q : Query _v) (h4563 : (e4563 _v)) : (e2254 _v) := by
  have p10896 := n10896 _v _q 
  have p16791 := n16791 _v _q 
  have p15156 := n15156 _v _q h4563
  have p16330 := n16330 _v _q h4563
  exact FloorCertificate.node_16799 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e2834 _v) (e2918 _v) p10896 p16791 p15156 p16330
theorem n16800 (_v : Vars) (_q : Query _v) (h4563 : (e4563 _v)) : (e4731 _v) := by
  have p14698 := n14698 _v _q 
  have p16799 := n16799 _v _q h4563
  simp only [e2254, e4723, e4724, e4728, e4729, e4730, e4731, e6531, e8220] at *
  tauto
theorem n16801 (_v : Vars) (_q : Query _v) (h4563 : (e4563 _v)) : (e4724 _v) := by
  have p15518 := n15518 _v _q 
  have p16800 := n16800 _v _q h4563
  simp only [e4723, e4724, e4728, e4729, e4730, e4731, e4958] at *
  tauto
theorem n16802 (_v : Vars) (_q : Query _v) (h2787 : (e2787 _v)) (h8038 : (e8038 _v)) : (e4285 _v) := by
  have p16274 := n16274 _v _q 
  have p16351 := n16351 _v _q h2787 h8038
  simp only [e4283, e4284, e4285, e4286, e7798, e7799, e7804] at *
  tauto
theorem n16803 (_v : Vars) (_q : Query _v) (h6700 : (e6700 _v)) : (e4199 _v) := by
  have p16212 := n16212 _v _q 
  have p16355 := n16355 _v _q h6700
  simp only [e4199, e4200, e4201, e4202, e7703, e7704, e7709] at *
  tauto
theorem n16804 (_v : Vars) (_q : Query _v) (h6700 : (e6700 _v)) : (e442 _v) := by
  have p16149 := n16149 _v _q 
  have p16357 := n16357 _v _q h6700
  simp only [e440, e441, e442, e443, e5360, e5361, e5370] at *
  tauto
theorem n16805 (_v : Vars) (_q : Query _v) (h6700 : (e6700 _v)) : (e91 _v) := by
  have p16235 := n16235 _v _q 
  have p16360 := n16360 _v _q h6700
  simp only [e89, e91, e94, e95, e5134, e5135, e7983] at *
  tauto
theorem n16806 (_v : Vars) (_q : Query _v) (h5093 : (e5093 _v)) (h6480 : (e6480 _v)) (h6555 : (e6555 _v)) : (e4434 _v) := by
  have p16375 := n16375 _v _q 
  have p11362 := n11362 _v _q h6555
  have p11440 := n11440 _v _q h5093
  have p8575 := n8575 _v _q h6480
  simp only [e13, e2125, e2310, e4434, e5093, e6480, e6555, e8494] at *
  tauto
theorem n16807 (_v : Vars) (_q : Query _v) (h2740 : (e2740 _v)) : (e4139 _v) := by
  have p16281 := n16281 _v _q 
  have p16383 := n16383 _v _q h2740
  simp only [e4139, e4140, e4141, e4142, e7634, e7635, e7640] at *
  tauto
theorem n16808 (_v : Vars) (_q : Query _v) (h6555 : (e6555 _v)) : (e4285 _v) := by
  have p16274 := n16274 _v _q 
  have p16390 := n16390 _v _q h6555
  simp only [e4283, e4284, e4285, e4286, e7798, e7799, e7804] at *
  tauto
theorem n16810 (_v : Vars) (_q : Query _v)  : (e16809 _v) := by
  by_contra hc
  change ¬ ((¬ (e2740 _v)) ∨ (¬ (e2310 _v)) ∨ (e2475 _v) ∨ (e4567 _v)) at hc
  have h2310 : (e2310 _v) := by
    tauto
  have h2740 : (e2740 _v) := by
    tauto
  have h4572 : (e4572 _v) := by
    change (¬ (e4567 _v))
    tauto
  have h8038 : (e8038 _v) := by
    change (¬ (e2475 _v))
    tauto
  have p16395 := n16395 _v _q h2310 h2740 h4572 h8038
  exact p16395
theorem n16811 (_v : Vars) (_q : Query _v) (h6555 : (e6555 _v)) : (e4838 _v) := by
  have p16285 := n16285 _v _q 
  have p16400 := n16400 _v _q h6555
  simp only [e4836, e4837, e4838, e4839, e8301, e8302, e8307] at *
  tauto
theorem n16812 (_v : Vars) (_q : Query _v) (h6423 : (e6423 _v)) (h6555 : (e6555 _v)) : (e4139 _v) := by
  have p16281 := n16281 _v _q 
  have p16402 := n16402 _v _q h6423 h6555
  simp only [e4139, e4140, e4141, e4142, e7634, e7635, e7640] at *
  tauto
theorem n16813 (_v : Vars) (_q : Query _v) (h6555 : (e6555 _v)) : (e4285 _v) := by
  have p16274 := n16274 _v _q 
  have p16404 := n16404 _v _q h6555
  simp only [e4283, e4284, e4285, e4286, e7798, e7799, e7804] at *
  tauto
theorem n16814 (_v : Vars) (_q : Query _v) (h2787 : (e2787 _v)) (h8038 : (e8038 _v)) : (e4285 _v) := by
  have p16274 := n16274 _v _q 
  have p16406 := n16406 _v _q h2787 h8038
  simp only [e4283, e4284, e4285, e4286, e7798, e7799, e7804] at *
  tauto
theorem n16815 (_v : Vars) (_q : Query _v) (h2787 : (e2787 _v)) (h8038 : (e8038 _v)) : (e4838 _v) := by
  have p16285 := n16285 _v _q 
  have p16408 := n16408 _v _q h2787 h8038
  simp only [e4836, e4837, e4838, e4839, e8301, e8302, e8307] at *
  tauto
theorem n16816 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e4419 _v) := by
  have p16347 := n16347 _v _q 
  have p16413 := n16413 _v _q h6784
  simp only [e4417, e4418, e4419, e4420, e7921, e7922, e7927] at *
  tauto
theorem n16817 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) (h8038 : (e8038 _v)) : (e442 _v) := by
  have p16149 := n16149 _v _q 
  have p16417 := n16417 _v _q h6784 h8038
  simp only [e440, e441, e442, e443, e5360, e5361, e5370] at *
  tauto
theorem n16818 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) (h8038 : (e8038 _v)) : (e4285 _v) := by
  have p16274 := n16274 _v _q 
  have p16423 := n16423 _v _q h6784 h8038
  simp only [e4283, e4284, e4285, e4286, e7798, e7799, e7804] at *
  tauto
theorem n16819 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) (h8038 : (e8038 _v)) : (e4139 _v) := by
  have p16281 := n16281 _v _q 
  have p16425 := n16425 _v _q h6784 h8038
  simp only [e4139, e4140, e4141, e4142, e7634, e7635, e7640] at *
  tauto
theorem n16820 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) (h8038 : (e8038 _v)) : (e191 _v) := by
  have p16442 := n16442 _v _q 
  have p16427 := n16427 _v _q h6784 h8038
  simp only [e191, e192, e193, e194, e5193, e5194, e5203] at *
  tauto
theorem n16821 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e4199 _v) := by
  have p16212 := n16212 _v _q 
  have p16429 := n16429 _v _q h6784
  simp only [e4199, e4200, e4201, e4202, e7703, e7704, e7709] at *
  tauto
theorem n16823 (_v : Vars) (_q : Query _v)  : (e16822 _v) := by
  by_contra hc
  change ¬ ((e3173 _v) ∨ (e2475 _v) ∨ (e2793 _v)) at hc
  have h3178 : (e3178 _v) := by
    change (¬ (e3173 _v))
    tauto
  have h6784 : (e6784 _v) := by
    change (¬ (e2793 _v))
    tauto
  have h8038 : (e8038 _v) := by
    change (¬ (e2475 _v))
    tauto
  have p16432 := n16432 _v _q h3178 h6784 h8038
  exact p16432
theorem n16824 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) (h8038 : (e8038 _v)) : (e3173 _v) := by
  have p16823 := n16823 _v _q 
  have p11473 := n11473 _v _q h6784
  have p8602 := n8602 _v _q h8038
  simp only [e2475, e2793, e3173, e6784, e8038, e16822] at *
  tauto
theorem n16825 (_v : Vars) (_q : Query _v) (h7698 : (e7698 _v)) : (e4181 _v) := by
  have p16453 := n16453 _v _q 
  have p16434 := n16434 _v _q h7698
  simp only [e4181, e4182, e4183, e4184, e7677, e7678, e7683] at *
  tauto
theorem n16826 (_v : Vars) (_q : Query _v) (h2475 : (e2475 _v)) (h6555 : (e6555 _v)) : (e4419 _v) := by
  have p16347 := n16347 _v _q 
  have p16447 := n16447 _v _q h2475 h6555
  simp only [e4417, e4418, e4419, e4420, e7921, e7922, e7927] at *
  tauto
theorem n16827 (_v : Vars) (_q : Query _v) (h3855 : (e3855 _v)) : (e3851 _v) := by
  have p16777 := n16777 _v _q 
  have p16250 := n16250 _v _q h3855
  simp only [e3851, e3855, e3860, e4585] at *
  tauto
theorem n16828 (_v : Vars) (_q : Query _v) (h2799 : (e2799 _v)) : (e4855 _v) := by
  have p16317 := n16317 _v _q 
  have p16486 := n16486 _v _q h2799
  simp only [e4855, e4856, e4857, e4858, e8324, e8325, e8330] at *
  tauto
theorem n16829 (_v : Vars) (_q : Query _v) (h6758 : (e6758 _v)) : (e4285 _v) := by
  have p16274 := n16274 _v _q 
  have p16502 := n16502 _v _q h6758
  simp only [e4283, e4284, e4285, e4286, e7798, e7799, e7804] at *
  tauto
theorem n16830 (_v : Vars) (_q : Query _v) (h6531 : (e6531 _v)) : (e30 _v) := by
  have p16290 := n16290 _v _q 
  have p16505 := n16505 _v _q h6531
  simp only [e28, e30, e34, e35, e5089, e5090, e5107] at *
  tauto
theorem n16832 (_v : Vars) (_q : Query _v)  : (e16831 _v) := by
  by_contra hc
  change ¬ ((e2303 _v) ∨ (¬ (e4419 _v)) ∨ (e2475 _v)) at hc
  have h4419 : (e4419 _v) := by
    tauto
  have h7807 : (e7807 _v) := by
    change (¬ (e2303 _v))
    tauto
  have h8038 : (e8038 _v) := by
    change (¬ (e2475 _v))
    tauto
  have p16511 := n16511 _v _q h4419 h7807 h8038
  exact p16511
theorem n16833 (_v : Vars) (_q : Query _v) (h4419 : (e4419 _v)) (h8038 : (e8038 _v)) : (e2303 _v) := by
  have p16832 := n16832 _v _q 
  have p8602 := n8602 _v _q h8038
  have p4971 := n4971 _v _q h4419
  simp only [e2303, e2475, e4419, e4420, e8038, e16831] at *
  tauto
theorem n16834 (_v : Vars) (_q : Query _v) (h4419 : (e4419 _v)) (h7807 : (e7807 _v)) : (e2475 _v) := by
  have p16832 := n16832 _v _q 
  have p11350 := n11350 _v _q h7807
  have p4971 := n4971 _v _q h4419
  simp only [e2303, e2475, e4419, e4420, e7807, e16831] at *
  tauto
theorem n16835 (_v : Vars) (_q : Query _v) (h8338 : (e8338 _v)) : (e8338 _v) := by
  exact h8338
theorem n16836 (_v : Vars) (_q : Query _v) (h2475 : (e2475 _v)) (h4302 : (e4302 _v)) (h8338 : (e8338 _v)) : (e2061 _v) := by
  have p8457 := n8457 _v _q h2475
  have p16835 := n16835 _v _q h8338
  have p15577 := n15577 _v _q h4302
  have p16517 := n16517 _v _q h4302
  exact FloorCertificate.node_16836 (e2 _v) (e7 _v) (e17 _v) (e45 _v) (e110 _v) (e2898 _v) (e2970 _v) p8457 p16835 p15577 p16517
theorem n16837 (_v : Vars) (_q : Query _v) (h2475 : (e2475 _v)) (h4302 : (e4302 _v)) (h8338 : (e8338 _v)) : (e4447 _v) := by
  have p14688 := n14688 _v _q 
  have p16836 := n16836 _v _q h2475 h4302 h8338
  simp only [e2061, e4439, e4440, e4444, e4445, e4446, e4447, e6454, e7961] at *
  tauto
theorem n16838 (_v : Vars) (_q : Query _v) (h6684 : (e6684 _v)) : (e191 _v) := by
  have p16442 := n16442 _v _q 
  have p16518 := n16518 _v _q h6684
  simp only [e191, e192, e193, e194, e5193, e5194, e5203] at *
  tauto
end
end Assembly
