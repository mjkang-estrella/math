import Dag132
import generated.th_lemma_10
import generated.th_lemma_9
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n15643 (_v : Vars) (_q : Query _v) (h4611 : (e4611 _v)) : (e4611 _v) := by
  exact h4611
theorem n15644 (_v : Vars) (_q : Query _v) (h4611 : (e4611 _v)) : (e8095 _v) := by
  have p15642 := n15642 _v _q 
  have p15643 := n15643 _v _q h4611
  simp only [e4608, e4609, e4610, e4611, e8095, e8543] at *
  tauto
theorem n15645 (_v : Vars) (_q : Query _v) (h4611 : (e4611 _v)) : (e2179 _v) := by
  have p14626 := n14626 _v _q 
  have p15644 := n15644 _v _q h4611
  simp only [e2179, e4608, e4609, e4610, e4611, e8095, e8103, e8106] at *
  tauto
theorem n15646 (_v : Vars) (_q : Query _v) (h5108 : (e5108 _v)) (h6454 : (e6454 _v)) : (e6776 _v) := by
  have p11366 := n11366 _v _q h5108
  have p8663 := n8663 _v _q 
  have p8430 := n8430 _v _q h6454
  exact FloorCertificate.node_15646 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p11366 p8663 p8430
theorem n15647 (_v : Vars) (_q : Query _v) (h5108 : (e5108 _v)) (h6454 : (e6454 _v)) : (e7789 _v) := by
  have p14570 := n14570 _v _q 
  have p15646 := n15646 _v _q h5108 h6454
  simp only [e2781, e4258, e4259, e4260, e4261, e6776, e7781, e7789, e7792] at *
  tauto
theorem n15648 (_v : Vars) (_q : Query _v)  : (e7441 _v) := by
  simp only [e70, e72, e75, e76, e5118, e7441] at *
  tauto
theorem n15649 (_v : Vars) (_q : Query _v) (h5108 : (e5108 _v)) : (e5119 _v) := by
  have p14487 := n14487 _v _q 
  have p11366 := n11366 _v _q h5108
  simp only [e48, e70, e72, e75, e76, e5108, e5118, e5119, e5122] at *
  tauto
theorem n15650 (_v : Vars) (_q : Query _v) (h5108 : (e5108 _v)) : (e70 _v) := by
  have p15648 := n15648 _v _q 
  have p15649 := n15649 _v _q h5108
  simp only [e70, e72, e75, e76, e5118, e5119, e7441] at *
  tauto
theorem n15651 (_v : Vars) (_q : Query _v) (h6758 : (e6758 _v)) : (e5403 _v) := by
  have p14577 := n14577 _v _q 
  have p12890 := n12890 _v _q h6758
  simp only [e474, e488, e490, e493, e494, e5392, e5402, e5403, e5406] at *
  tauto
theorem n15652 (_v : Vars) (_q : Query _v) (h6758 : (e6758 _v)) : (e488 _v) := by
  have p15090 := n15090 _v _q 
  have p15651 := n15651 _v _q h6758
  simp only [e488, e490, e493, e494, e5402, e5403, e7821] at *
  tauto
theorem n15653 (_v : Vars) (_q : Query _v) (h6758 : (e6758 _v)) : (e6830 _v) := by
  have p14629 := n14629 _v _q 
  have p14721 := n14721 _v _q h6758
  simp only [e496, e3069, e3071, e3074, e3075, e6720, e6829, e6830, e6833] at *
  tauto
theorem n15654 (_v : Vars) (_q : Query _v) (h6758 : (e6758 _v)) : (e3069 _v) := by
  have p14878 := n14878 _v _q 
  have p15653 := n15653 _v _q h6758
  simp only [e3069, e3071, e3074, e3075, e6829, e6830, e8137] at *
  tauto
theorem n15655 (_v : Vars) (_q : Query _v) (h6758 : (e6758 _v)) : (e6501 _v) := by
  have p11375 := n11375 _v _q 
  have p8425 := n8425 _v _q h6758
  have p10893 := n10893 _v _q 
  exact FloorCertificate.node_15655 (e2 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p11375 p8425 p10893
theorem n15656 (_v : Vars) (_q : Query _v) (h6758 : (e6758 _v)) : (e8103 _v) := by
  have p14626 := n14626 _v _q 
  have p15655 := n15655 _v _q h6758
  simp only [e2179, e4608, e4609, e4610, e4611, e6501, e8095, e8103, e8106] at *
  tauto
theorem n15657 (_v : Vars) (_q : Query _v) (h6758 : (e6758 _v)) : (e6650 _v) := by
  have p11375 := n11375 _v _q 
  have p10893 := n10893 _v _q 
  have p10896 := n10896 _v _q 
  have p8663 := n8663 _v _q 
  have p8425 := n8425 _v _q h6758
  exact FloorCertificate.node_15657 (e2 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p11375 p10893 p10896 p8663 p8425
theorem n15658 (_v : Vars) (_q : Query _v) (h6758 : (e6758 _v)) : (e8292 _v) := by
  have p14657 := n14657 _v _q 
  have p15657 := n15657 _v _q h6758
  simp only [e2522, e4811, e4812, e4813, e4814, e6650, e8284, e8292, e8295] at *
  tauto
theorem n15659 (_v : Vars) (_q : Query _v) (h6758 : (e6758 _v)) : (e6549 _v) := by
  have p10896 := n10896 _v _q 
  have p11375 := n11375 _v _q 
  have p8663 := n8663 _v _q 
  have p10893 := n10893 _v _q 
  have p8425 := n8425 _v _q h6758
  exact FloorCertificate.node_15659 (e2 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p10896 p11375 p8663 p10893 p8425
theorem n15660 (_v : Vars) (_q : Query _v) (h6758 : (e6758 _v)) : (e6879 _v) := by
  have p14643 := n14643 _v _q 
  have p15659 := n15659 _v _q h6758
  simp only [e2296, e3150, e3152, e3155, e3156, e6549, e6878, e6879, e6882] at *
  tauto
theorem n15661 (_v : Vars) (_q : Query _v) (h6758 : (e6758 _v)) : (e6694 _v) := by
  have p10893 := n10893 _v _q 
  have p8663 := n8663 _v _q 
  have p10896 := n10896 _v _q 
  have p11375 := n11375 _v _q 
  have p8425 := n8425 _v _q h6758
  exact FloorCertificate.node_15661 (e2 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p10893 p8663 p10896 p11375 p8425
theorem n15662 (_v : Vars) (_q : Query _v) (h6758 : (e6758 _v)) : (e7895 _v) := by
  have p14589 := n14589 _v _q 
  have p15661 := n15661 _v _q h6758
  simp only [e251, e4367, e4368, e4369, e4370, e6694, e7887, e7895, e7898] at *
  tauto
theorem n15663 (_v : Vars) (_q : Query _v) (h6758 : (e6758 _v)) : (e6676 _v) := by
  have p11343 := n11343 _v _q 
  have p12892 := n12892 _v _q h6758
  simp only [e2364, e2585, e6583, e6676, e11342] at *
  tauto
theorem n15664 (_v : Vars) (_q : Query _v) (h6758 : (e6758 _v)) : (e6750 _v) := by
  have p10946 := n10946 _v _q 
  have p15663 := n15663 _v _q h6758
  simp only [e2585, e2733, e6676, e6750, e10945] at *
  tauto
theorem n15665 (_v : Vars) (_q : Query _v) (h6758 : (e6758 _v)) : (e7597 _v) := by
  have p14525 := n14525 _v _q 
  have p15664 := n15664 _v _q h6758
  simp only [e2733, e4096, e4097, e4098, e4099, e6750, e7589, e7597, e7600] at *
  tauto
theorem n15666 (_v : Vars) (_q : Query _v) (h6758 : (e6758 _v)) : (e7416 _v) := by
  have p14534 := n14534 _v _q 
  have p11506 := n11506 _v _q h6758
  simp only [e2402, e3937, e3939, e3942, e3943, e6600, e7415, e7416, e7419] at *
  tauto
theorem n15667 (_v : Vars) (_q : Query _v) (h6758 : (e6758 _v)) : (e3937 _v) := by
  have p15012 := n15012 _v _q 
  have p15666 := n15666 _v _q h6758
  simp only [e3937, e3939, e3942, e3943, e7415, e7416, e7633] at *
  tauto
theorem n15668 (_v : Vars) (_q : Query _v) (h6758 : (e6758 _v)) : (e7955 _v) := by
  have p14601 := n14601 _v _q 
  have p11507 := n11507 _v _q h6758
  simp only [e2061, e4434, e4435, e4436, e4437, e6454, e7947, e7955, e7958] at *
  tauto
theorem n15669 (_v : Vars) (_q : Query _v) (h6758 : (e6758 _v)) : (e4434 _v) := by
  have p15307 := n15307 _v _q 
  have p15668 := n15668 _v _q h6758
  simp only [e4434, e4435, e4436, e4437, e7947, e7948, e7955] at *
  tauto
theorem n15670 (_v : Vars) (_q : Query _v)  : (e8268 _v) := by
  simp only [e4785, e4786, e4787, e4788, e8267, e8268] at *
  tauto
theorem n15671 (_v : Vars) (_q : Query _v) (h6758 : (e6758 _v)) : (e6630 _v) := by
  have p8442 := n8442 _v _q 
  have p11506 := n11506 _v _q h6758
  simp only [e2402, e2468, e6600, e6630, e8441] at *
  tauto
theorem n15672 (_v : Vars) (_q : Query _v) (h6758 : (e6758 _v)) : (e8275 _v) := by
  have p14655 := n14655 _v _q 
  have p15671 := n15671 _v _q h6758
  simp only [e2468, e4785, e4786, e4787, e4788, e6630, e8267, e8275, e8278] at *
  tauto
theorem n15673 (_v : Vars) (_q : Query _v) (h6758 : (e6758 _v)) : (e4787 _v) := by
  have p15670 := n15670 _v _q 
  have p15672 := n15672 _v _q h6758
  simp only [e4785, e4786, e4787, e4788, e8267, e8268, e8275] at *
  tauto
theorem n15674 (_v : Vars) (_q : Query _v) (h6758 : (e6758 _v)) : (e7668 _v) := by
  have p14544 := n14544 _v _q 
  have p12889 := n12889 _v _q h6758
  simp only [e2351, e4156, e4157, e4158, e4159, e6575, e7660, e7668, e7671] at *
  tauto
theorem n15675 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e6525 _v) := by
  have p10893 := n10893 _v _q 
  have p11473 := n11473 _v _q h6784
  have p11375 := n11375 _v _q 
  exact FloorCertificate.node_15675 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p10893 p11473 p11375
theorem n15676 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e8174 _v) := by
  have p14634 := n14634 _v _q 
  have p15675 := n15675 _v _q h6784
  simp only [e2242, e4673, e4674, e4675, e4676, e6525, e8166, e8174, e8177] at *
  tauto
theorem n15677 (_v : Vars) (_q : Query _v) (h6636 : (e6636 _v)) : (e6525 _v) := by
  have p10893 := n10893 _v _q 
  have p11031 := n11031 _v _q h6636
  have p5255 := n5255 _v _q 
  have p8663 := n8663 _v _q 
  have p5257 := n5257 _v _q 
  exact FloorCertificate.node_15677 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p10893 p11031 p5255 p8663 p5257
theorem n15678 (_v : Vars) (_q : Query _v) (h6636 : (e6636 _v)) : (e8174 _v) := by
  have p14634 := n14634 _v _q 
  have p15677 := n15677 _v _q h6636
  simp only [e2242, e4673, e4674, e4675, e4676, e6525, e8166, e8174, e8177] at *
  tauto
theorem n15679 (_v : Vars) (_q : Query _v) (h6636 : (e6636 _v)) : (e5108 _v) := by
  have p11031 := n11031 _v _q h6636
  have p5255 := n5255 _v _q 
  have p10893 := n10893 _v _q 
  have p8663 := n8663 _v _q 
  have p5257 := n5257 _v _q 
  exact FloorCertificate.node_15679 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p11031 p5255 p10893 p8663 p5257
theorem n15680 (_v : Vars) (_q : Query _v) (h6636 : (e6636 _v)) : (e5119 _v) := by
  have p14487 := n14487 _v _q 
  have p15679 := n15679 _v _q h6636
  simp only [e48, e70, e72, e75, e76, e5108, e5118, e5119, e5122] at *
  tauto
theorem n15681 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e6750 _v) := by
  have p10946 := n10946 _v _q 
  have p12894 := n12894 _v _q h6784
  simp only [e2585, e2733, e6676, e6750, e10945] at *
  tauto
theorem n15682 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e6776 _v) := by
  have p8424 := n8424 _v _q 
  have p15681 := n15681 _v _q h6784
  simp only [e2733, e2781, e6750, e6776, e8423] at *
  tauto
theorem n15683 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e7789 _v) := by
  have p14570 := n14570 _v _q 
  have p15682 := n15682 _v _q h6784
  simp only [e2781, e4258, e4259, e4260, e4261, e6776, e7781, e7789, e7792] at *
  tauto
theorem n15684 (_v : Vars) (_q : Query _v) (h6636 : (e6636 _v)) : (e6454 _v) := by
  have p11412 := n11412 _v _q 
  have p11495 := n11495 _v _q h6636
  simp only [e1995, e2061, e6423, e6454, e11411] at *
  tauto
theorem n15685 (_v : Vars) (_q : Query _v) (h6636 : (e6636 _v)) : (e7955 _v) := by
  have p14601 := n14601 _v _q 
  have p15684 := n15684 _v _q h6636
  simp only [e2061, e4434, e4435, e4436, e4437, e6454, e7947, e7955, e7958] at *
  tauto
theorem n15686 (_v : Vars) (_q : Query _v) (h6636 : (e6636 _v)) : (e4434 _v) := by
  have p15307 := n15307 _v _q 
  have p15685 := n15685 _v _q h6636
  simp only [e4434, e4435, e4436, e4437, e7947, e7948, e7955] at *
  tauto
theorem n15687 (_v : Vars) (_q : Query _v) (h6636 : (e6636 _v)) : (e6575 _v) := by
  have p11031 := n11031 _v _q h6636
  have p10893 := n10893 _v _q 
  have p5257 := n5257 _v _q 
  have p8663 := n8663 _v _q 
  have p5255 := n5255 _v _q 
  exact FloorCertificate.node_15687 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p11031 p10893 p5257 p8663 p5255
end
end Assembly
