import Dag114
import generated.th_lemma_6
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n14832 (_v : Vars) (_q : Query _v)  : (e7712 _v) := by
  have p14560 := n14560 _v _q 
  simp only [e2680, e4199, e4200, e4201, e4202, e6716, e7703, e7709, e7712, e7714, e7717, e7724, e7725, e7726, e7727, e7728, e10986, e10988, e10989, e10990] at *
  tauto
theorem n14833 (_v : Vars) (_q : Query _v)  : (e7744 _v) := by
  have p14566 := n14566 _v _q 
  simp only [e2132, e4218, e4219, e4220, e4221, e7733, e7739, e7742, e7744, e7747, e7749, e7751, e7752, e7753, e7754, e7755, e11001, e11003, e11004, e11005] at *
  tauto
theorem n14834 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e6700 _v) := by
  have p11035 := n11035 _v _q 
  have p12548 := n12548 _v _q h6792
  simp only [e2482, e2634, e6636, e6700, e11034] at *
  tauto
theorem n14835 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e6776 _v) := by
  have p11030 := n11030 _v _q 
  have p14834 := n14834 _v _q h6792
  simp only [e2634, e2781, e6700, e6776, e11029] at *
  tauto
theorem n14836 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e7789 _v) := by
  have p14570 := n14570 _v _q 
  have p14835 := n14835 _v _q h6792
  simp only [e2781, e4258, e4259, e4260, e4261, e6776, e7781, e7789, e7792] at *
  tauto
theorem n14837 (_v : Vars) (_q : Query _v)  : (e7809 _v) := by
  have p14576 := n14576 _v _q 
  simp only [e2303, e4283, e4284, e4285, e4286, e7798, e7804, e7807, e7809, e7812, e7814, e7816, e7817, e7818, e7819, e7820, e11046, e11048, e11049, e11050] at *
  tauto
theorem n14838 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e5392 _v) := by
  have p11376 := n11376 _v _q 
  have p10893 := n10893 _v _q 
  have p11375 := n11375 _v _q 
  have p8663 := n8663 _v _q 
  have p10896 := n10896 _v _q 
  have p10895 := n10895 _v _q h6792
  exact FloorCertificate.node_14838 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p11376 p10893 p11375 p8663 p10896 p10895
theorem n14839 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e5403 _v) := by
  have p14577 := n14577 _v _q 
  have p14838 := n14838 _v _q h6792
  simp only [e474, e488, e490, e493, e494, e5392, e5402, e5403, e5406] at *
  tauto
theorem n14840 (_v : Vars) (_q : Query _v)  : (e7823 _v) := by
  simp only [e4301, e4302, e4303, e4304, e7822, e7823] at *
  tauto
theorem n14841 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e7830 _v) := by
  have p14579 := n14579 _v _q 
  have p14822 := n14822 _v _q h6792
  simp only [e2585, e4301, e4302, e4303, e4304, e6676, e7822, e7830, e7833] at *
  tauto
theorem n14842 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e4301 _v) := by
  have p14840 := n14840 _v _q 
  have p14841 := n14841 _v _q h6792
  simp only [e4301, e4302, e4303, e4304, e7822, e7823, e7830] at *
  tauto
theorem n14843 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e6973 _v) := by
  have p14377 := n14377 _v _q 
  have p12649 := n12649 _v _q h6792
  simp only [e2310, e3265, e3266, e3267, e3268, e6555, e6965, e6973, e6976] at *
  tauto
theorem n14844 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e3267 _v) := by
  have p14776 := n14776 _v _q 
  have p14843 := n14843 _v _q h6792
  simp only [e3265, e3266, e3267, e3268, e6965, e6966, e6973] at *
  tauto
theorem n14845 (_v : Vars) (_q : Query _v)  : (e7844 _v) := by
  simp only [e7839, e7840, e7841, e7842, e7843, e7844] at *
  tauto
theorem n14846 (_v : Vars) (_q : Query _v)  : (e11073 _v) := by
  have p14585 := n14585 _v _q 
  simp only [e2489, e4334, e4336, e4339, e4340, e7839, e7840, e7841, e7842, e7843, e7849, e7850, e7853, e7855, e7860, e7861, e11073, e11075, e11076, e11077] at *
  tauto
theorem n14847 (_v : Vars) (_q : Query _v)  : (e7853 _v) := by
  have p10893 := n10893 _v _q 
  have p11376 := n11376 _v _q 
  exact FloorCertificate.node_14847 (e2 _v) (e7 _v) (e45 _v) p10893 p11376
theorem n14848 (_v : Vars) (_q : Query _v)  : (e7860 _v) := by
  have p14846 := n14846 _v _q 
  have p14847 := n14847 _v _q 
  simp only [e2489, e7839, e7840, e7841, e7842, e7843, e7853, e7860, e11073] at *
  tauto
theorem n14849 (_v : Vars) (_q : Query _v)  : (e7841 _v) := by
  have p14845 := n14845 _v _q 
  have p14848 := n14848 _v _q 
  simp only [e7839, e7840, e7841, e7842, e7843, e7844, e7860] at *
  tauto
theorem n14850 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e6694 _v) := by
  have p10895 := n10895 _v _q h6792
  have p11376 := n11376 _v _q 
  have p11375 := n11375 _v _q 
  have p8663 := n8663 _v _q 
  have p10896 := n10896 _v _q 
  have p10893 := n10893 _v _q 
  exact FloorCertificate.node_14850 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p10895 p11376 p11375 p8663 p10896 p10893
theorem n14851 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e7895 _v) := by
  have p14589 := n14589 _v _q 
  have p14850 := n14850 _v _q h6792
  simp only [e251, e4367, e4368, e4369, e4370, e6694, e7887, e7895, e7898] at *
  tauto
theorem n14852 (_v : Vars) (_q : Query _v)  : (e7905 _v) := by
  simp only [e4392, e4393, e4394, e4395, e7904, e7905] at *
  tauto
theorem n14853 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e7912 _v) := by
  have p14591 := n14591 _v _q 
  have p12548 := n12548 _v _q h6792
  simp only [e2482, e4392, e4393, e4394, e4395, e6636, e7904, e7912, e7915] at *
  tauto
theorem n14854 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e4394 _v) := by
  have p14852 := n14852 _v _q 
  have p14853 := n14853 _v _q h6792
  simp only [e4392, e4393, e4394, e4395, e7904, e7905, e7912] at *
  tauto
theorem n14855 (_v : Vars) (_q : Query _v)  : (e7930 _v) := by
  have p14599 := n14599 _v _q 
  simp only [e2787, e4417, e4418, e4419, e4420, e6772, e7921, e7927, e7930, e7932, e7935, e7942, e7943, e7944, e7945, e7946, e11111, e11113, e11114, e11115] at *
  tauto
theorem n14856 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e6454 _v) := by
  have p11376 := n11376 _v _q 
  have p10896 := n10896 _v _q 
  have p10895 := n10895 _v _q h6792
  have p10893 := n10893 _v _q 
  exact FloorCertificate.node_14856 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p11376 p10896 p10895 p10893
theorem n14857 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e7955 _v) := by
  have p14601 := n14601 _v _q 
  have p14856 := n14856 _v _q h6792
  simp only [e2061, e4434, e4435, e4436, e4437, e6454, e7947, e7955, e7958] at *
  tauto
theorem n14858 (_v : Vars) (_q : Query _v)  : (e7980 _v) := by
  simp only [e4475, e4477, e4480, e4481, e7970, e7980] at *
  tauto
theorem n14859 (_v : Vars) (_q : Query _v) (h4481 : (e4481 _v)) : (e4481 _v) := by
  exact h4481
theorem n14860 (_v : Vars) (_q : Query _v) (h4481 : (e4481 _v)) : (e7970 _v) := by
  have p14858 := n14858 _v _q 
  have p14859 := n14859 _v _q h4481
  simp only [e4475, e4477, e4480, e4481, e7970, e7980] at *
  tauto
theorem n14861 (_v : Vars) (_q : Query _v) (h4481 : (e4481 _v)) : (e2125 _v) := by
  have p14603 := n14603 _v _q 
  have p14860 := n14860 _v _q h4481
  simp only [e2125, e4475, e4477, e4480, e4481, e7970, e7971, e7974] at *
  tauto
theorem n14862 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e6896 _v) := by
  have p14360 := n14360 _v _q 
  have p14834 := n14834 _v _q h6792
  simp only [e2634, e3167, e3168, e3169, e3170, e6700, e6888, e6896, e6899] at *
  tauto
theorem n14863 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e3169 _v) := by
  have p14769 := n14769 _v _q 
  have p14862 := n14862 _v _q h6792
  simp only [e3167, e3168, e3169, e3170, e6888, e6889, e6896] at *
  tauto
theorem n14864 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e6732 _v) := by
  have p10895 := n10895 _v _q h6792
  have p11375 := n11375 _v _q 
  exact FloorCertificate.node_14864 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p10895 p11375
theorem n14865 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e7992 _v) := by
  have p14606 := n14606 _v _q 
  have p14864 := n14864 _v _q h6792
  simp only [e2697, e4486, e4487, e4488, e4489, e6732, e7984, e7992, e7995] at *
  tauto
theorem n14866 (_v : Vars) (_q : Query _v)  : (e11150 _v) := by
  have p14614 := n14614 _v _q 
  simp only [e2811, e4532, e4534, e4537, e4538, e6788, e8003, e8004, e8005, e8006, e8007, e8013, e8014, e8017, e8027, e8028, e11150, e11152, e11153, e11154] at *
  tauto
theorem n14867 (_v : Vars) (_q : Query _v) (h2811 : (e2811 _v)) : (e2811 _v) := by
  exact h2811
theorem n14868 (_v : Vars) (_q : Query _v) (h2811 : (e2811 _v)) : (e7489 _v) := by
  have p11375 := n11375 _v _q 
  have p10896 := n10896 _v _q 
  have p10893 := n10893 _v _q 
  have p14867 := n14867 _v _q h2811
  have p11376 := n11376 _v _q 
  exact FloorCertificate.node_14868 (e2 _v) (e7 _v) (e9 _v) (e45 _v) (e110 _v) p11375 p10896 p10893 p14867 p11376
theorem n14869 (_v : Vars) (_q : Query _v)  : (e6788 _v) := by
  by_contra hc
  change ¬ (¬ (e2811 _v)) at hc
  have h2811 : (e2811 _v) := by
    tauto
  have p14868 := n14868 _v _q h2811
  exact p14868
theorem n14870 (_v : Vars) (_q : Query _v)  : (e8027 _v) := by
  have p14866 := n14866 _v _q 
  have p14869 := n14869 _v _q 
  simp only [e2811, e6788, e8003, e8004, e8005, e8006, e8007, e8027, e11150] at *
  tauto
theorem n14871 (_v : Vars) (_q : Query _v)  : (e8040 _v) := by
  have p14620 := n14620 _v _q 
  simp only [e2475, e4544, e4545, e4546, e4547, e8029, e8035, e8038, e8040, e8043, e8045, e8047, e8048, e8049, e8050, e8051, e11165, e11167, e11168, e11169] at *
  tauto
theorem n14872 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e6423 _v) := by
  have p11375 := n11375 _v _q 
  have p10896 := n10896 _v _q 
  have p10895 := n10895 _v _q h6792
  have p10893 := n10893 _v _q 
  exact FloorCertificate.node_14872 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p11375 p10896 p10895 p10893
theorem n14873 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e8060 _v) := by
  have p14622 := n14622 _v _q 
  have p14872 := n14872 _v _q h6792
  simp only [e1995, e4562, e4563, e4564, e4565, e6423, e8052, e8060, e8063] at *
  tauto
theorem n14874 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e6501 _v) := by
  have p11376 := n11376 _v _q 
  have p11375 := n11375 _v _q 
  have p10895 := n10895 _v _q h6792
  have p10893 := n10893 _v _q 
  exact FloorCertificate.node_14874 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p11376 p11375 p10895 p10893
theorem n14875 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e8103 _v) := by
  have p14626 := n14626 _v _q 
  have p14874 := n14874 _v _q h6792
  simp only [e2179, e4608, e4609, e4610, e4611, e6501, e8095, e8103, e8106] at *
  tauto
theorem n14876 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e7170 _v) := by
  have p14427 := n14427 _v _q 
  have p13992 := n13992 _v _q h6792
  simp only [e2536, e3583, e3585, e3588, e3589, e6656, e7169, e7170, e7173] at *
  tauto
end
end Assembly
