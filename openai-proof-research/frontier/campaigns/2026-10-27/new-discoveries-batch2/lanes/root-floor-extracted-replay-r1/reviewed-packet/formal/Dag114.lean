import Dag113
import generated.th_lemma_5
import generated.th_lemma_6
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n14787 (_v : Vars) (_q : Query _v)  : (e10747 _v) := by
  have p14433 := n14433 _v _q 
  simp only [e2543, e3600, e3602, e3605, e3606, e7183, e7184, e7185, e7186, e7187, e7193, e7194, e7197, e7199, e7204, e7205, e10747, e10749, e10750, e10751] at *
  tauto
theorem n14788 (_v : Vars) (_q : Query _v)  : (e7197 _v) := by
  have p11375 := n11375 _v _q 
  have p10893 := n10893 _v _q 
  exact FloorCertificate.node_14788 (e2 _v) (e45 _v) (e110 _v) p11375 p10893
theorem n14789 (_v : Vars) (_q : Query _v)  : (e7204 _v) := by
  have p14787 := n14787 _v _q 
  have p14788 := n14788 _v _q 
  simp only [e2543, e7183, e7184, e7185, e7186, e7187, e7197, e7204, e10747] at *
  tauto
theorem n14790 (_v : Vars) (_q : Query _v)  : (e7351 _v) := by
  simp only [e3849, e3850, e3851, e3852, e7350, e7351] at *
  tauto
theorem n14791 (_v : Vars) (_q : Query _v) (h3860 : (e3860 _v)) : (e6486 _v) := by
  have p14472 := n14472 _v _q 
  have p7369 := n7369 _v _q h3860
  simp only [e2139, e3854, e3855, e3859, e3860, e3861, e3862, e6486, e7364] at *
  tauto
theorem n14792 (_v : Vars) (_q : Query _v) (h3860 : (e3860 _v)) : (e7358 _v) := by
  have p14471 := n14471 _v _q 
  have p14791 := n14791 _v _q h3860
  simp only [e2139, e3849, e3850, e3851, e3852, e6486, e7350, e7358, e7361] at *
  tauto
theorem n14793 (_v : Vars) (_q : Query _v) (h3860 : (e3860 _v)) : (e3851 _v) := by
  have p14790 := n14790 _v _q 
  have p14792 := n14792 _v _q h3860
  simp only [e3849, e3850, e3851, e3852, e7350, e7351, e7358] at *
  tauto
theorem n14794 (_v : Vars) (_q : Query _v)  : (e10842 _v) := by
  have p14478 := n14478 _v _q 
  simp only [e2146, e3882, e3884, e3887, e3888, e7370, e7371, e7372, e7373, e7374, e7380, e7381, e7384, e7386, e7391, e7392, e10842, e10844, e10845, e10846] at *
  tauto
theorem n14795 (_v : Vars) (_q : Query _v)  : (e7384 _v) := by
  have p11375 := n11375 _v _q 
  have p11376 := n11376 _v _q 
  exact FloorCertificate.node_14795 (e2 _v) (e7 _v) (e110 _v) p11375 p11376
theorem n14796 (_v : Vars) (_q : Query _v)  : (e7391 _v) := by
  have p14794 := n14794 _v _q 
  have p14795 := n14795 _v _q 
  simp only [e2146, e7370, e7371, e7372, e7373, e7374, e7384, e7391, e10842] at *
  tauto
theorem n14797 (_v : Vars) (_q : Query _v)  : (e3924 _v) := by
  simp only [e3919, e3920, e3921, e3922, e3923, e3924] at *
  tauto
theorem n14798 (_v : Vars) (_q : Query _v) (h2402 : (e2402 _v)) : (e3929 _v) := by
  have p14484 := n14484 _v _q 
  have p8591 := n8591 _v _q h2402
  simp only [e2402, e3919, e3920, e3921, e3922, e3923, e3929, e6600, e7422] at *
  tauto
theorem n14799 (_v : Vars) (_q : Query _v) (h2402 : (e2402 _v)) : (e3919 _v) := by
  have p14797 := n14797 _v _q 
  have p14798 := n14798 _v _q h2402
  simp only [e3919, e3920, e3921, e3922, e3923, e3924, e3929] at *
  tauto
theorem n14800 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e5108 _v) := by
  have p11376 := n11376 _v _q 
  have p10895 := n10895 _v _q h6792
  have p11375 := n11375 _v _q 
  have p8663 := n8663 _v _q 
  have p10896 := n10896 _v _q 
  have p10893 := n10893 _v _q 
  exact FloorCertificate.node_14800 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p11376 p10895 p11375 p8663 p10896 p10893
theorem n14801 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e5119 _v) := by
  have p14487 := n14487 _v _q 
  have p14800 := n14800 _v _q h6792
  simp only [e48, e70, e72, e75, e76, e5108, e5118, e5119, e5122] at *
  tauto
theorem n14802 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e6758 _v) := by
  have p10895 := n10895 _v _q h6792
  have p11376 := n11376 _v _q 
  exact FloorCertificate.node_14802 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p10895 p11376
theorem n14803 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e7450 _v) := by
  have p14489 := n14489 _v _q 
  have p14802 := n14802 _v _q h6792
  simp only [e2746, e3971, e3972, e3973, e3974, e6758, e7442, e7450, e7453] at *
  tauto
theorem n14804 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e6768 _v) := by
  have p11376 := n11376 _v _q 
  have p11375 := n11375 _v _q 
  have p10895 := n10895 _v _q h6792
  have p8663 := n8663 _v _q 
  have p10896 := n10896 _v _q 
  have p10893 := n10893 _v _q 
  exact FloorCertificate.node_14804 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p11376 p11375 p10895 p8663 p10896 p10893
theorem n14805 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e6863 _v) := by
  have p14356 := n14356 _v _q 
  have p14804 := n14804 _v _q h6792
  simp only [e2771, e3103, e3104, e3105, e3106, e6768, e6855, e6863, e6866] at *
  tauto
theorem n14806 (_v : Vars) (_q : Query _v)  : (e7464 _v) := by
  simp only [e7459, e7460, e7461, e7462, e7463, e7464] at *
  tauto
theorem n14807 (_v : Vars) (_q : Query _v)  : (e10883 _v) := by
  have p14497 := n14497 _v _q 
  simp only [e2704, e4003, e4005, e4008, e4009, e6728, e7459, e7460, e7461, e7462, e7463, e7469, e7470, e7473, e7483, e7484, e10883, e10885, e10886, e10887] at *
  tauto
theorem n14808 (_v : Vars) (_q : Query _v)  : (e6728 _v) := by
  have p10893 := n10893 _v _q 
  have p11376 := n11376 _v _q 
  have p10896 := n10896 _v _q 
  exact FloorCertificate.node_14808 (e2 _v) (e7 _v) (e9 _v) (e45 _v) p10893 p11376 p10896
theorem n14809 (_v : Vars) (_q : Query _v)  : (e7483 _v) := by
  have p14807 := n14807 _v _q 
  have p14808 := n14808 _v _q 
  simp only [e2704, e6728, e7459, e7460, e7461, e7462, e7463, e7483, e10883] at *
  tauto
theorem n14810 (_v : Vars) (_q : Query _v)  : (e7459 _v) := by
  have p14806 := n14806 _v _q 
  have p14809 := n14809 _v _q 
  simp only [e7459, e7460, e7461, e7462, e7463, e7464, e7483] at *
  tauto
theorem n14811 (_v : Vars) (_q : Query _v)  : (e7507 _v) := by
  have p14505 := n14505 _v _q 
  simp only [e2691, e4026, e4028, e4031, e4032, e6724, e7493, e7494, e7495, e7496, e7497, e7503, e7504, e7507, e7517, e7518, e10904, e10906, e10907, e10908] at *
  tauto
theorem n14812 (_v : Vars) (_q : Query _v)  : (e10913 _v) := by
  have p14513 := n14513 _v _q 
  simp only [e2753, e4044, e4046, e4049, e4050, e6754, e7520, e7521, e7522, e7523, e7524, e7530, e7531, e7534, e7544, e7545, e10913, e10915, e10916, e10917] at *
  tauto
theorem n14813 (_v : Vars) (_q : Query _v)  : (e6754 _v) := by
  have p10896 := n10896 _v _q 
  have p10893 := n10893 _v _q 
  have p11375 := n11375 _v _q 
  exact FloorCertificate.node_14813 (e2 _v) (e9 _v) (e45 _v) (e110 _v) p10896 p10893 p11375
theorem n14814 (_v : Vars) (_q : Query _v)  : (e7544 _v) := by
  have p14812 := n14812 _v _q 
  have p14813 := n14813 _v _q 
  simp only [e2753, e6754, e7520, e7521, e7522, e7523, e7524, e7544, e10913] at *
  tauto
theorem n14815 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e6684 _v) := by
  have p10895 := n10895 _v _q h6792
  have p10896 := n10896 _v _q 
  exact FloorCertificate.node_14815 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p10895 p10896
theorem n14816 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e7554 _v) := by
  have p14515 := n14515 _v _q 
  have p14815 := n14815 _v _q h6792
  simp only [e2598, e4054, e4055, e4056, e4057, e6684, e7546, e7554, e7557] at *
  tauto
theorem n14817 (_v : Vars) (_q : Query _v)  : (e7568 _v) := by
  simp only [e7563, e7564, e7565, e7566, e7567, e7568] at *
  tauto
theorem n14818 (_v : Vars) (_q : Query _v)  : (e10930 _v) := by
  have p14523 := n14523 _v _q 
  simp only [e2605, e4086, e4088, e4091, e4092, e6680, e7563, e7564, e7565, e7566, e7567, e7573, e7574, e7577, e7587, e7588, e10930, e10932, e10933, e10934] at *
  tauto
theorem n14819 (_v : Vars) (_q : Query _v)  : (e6680 _v) := by
  have p10893 := n10893 _v _q 
  have p11376 := n11376 _v _q 
  have p11375 := n11375 _v _q 
  exact FloorCertificate.node_14819 (e2 _v) (e7 _v) (e45 _v) (e110 _v) p10893 p11376 p11375
theorem n14820 (_v : Vars) (_q : Query _v)  : (e7587 _v) := by
  have p14818 := n14818 _v _q 
  have p14819 := n14819 _v _q 
  simp only [e2605, e6680, e7563, e7564, e7565, e7566, e7567, e7587, e10930] at *
  tauto
theorem n14821 (_v : Vars) (_q : Query _v)  : (e7563 _v) := by
  have p14817 := n14817 _v _q 
  have p14820 := n14820 _v _q 
  simp only [e7563, e7564, e7565, e7566, e7567, e7568, e7587] at *
  tauto
theorem n14822 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e6676 _v) := by
  have p12579 := n12579 _v _q 
  have p12548 := n12548 _v _q h6792
  simp only [e2482, e2585, e6636, e6676, e12578] at *
  tauto
theorem n14823 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e6750 _v) := by
  have p10946 := n10946 _v _q 
  have p14822 := n14822 _v _q h6792
  simp only [e2585, e2733, e6676, e6750, e10945] at *
  tauto
theorem n14824 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e7597 _v) := by
  have p14525 := n14525 _v _q 
  have p14823 := n14823 _v _q h6792
  simp only [e2733, e4096, e4097, e4098, e4099, e6750, e7589, e7597, e7600] at *
  tauto
theorem n14825 (_v : Vars) (_q : Query _v)  : (e7620 _v) := by
  have p14533 := n14533 _v _q 
  simp only [e2740, e4128, e4130, e4133, e4134, e6746, e7606, e7607, e7608, e7609, e7610, e7616, e7617, e7620, e7630, e7631, e10951, e10953, e10954, e10955] at *
  tauto
theorem n14826 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e6600 _v) := by
  have p10895 := n10895 _v _q h6792
  have p11376 := n11376 _v _q 
  have p11375 := n11375 _v _q 
  have p10896 := n10896 _v _q 
  exact FloorCertificate.node_14826 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p10895 p11376 p11375 p10896
theorem n14827 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e7416 _v) := by
  have p14534 := n14534 _v _q 
  have p14826 := n14826 _v _q h6792
  simp only [e2402, e3937, e3939, e3942, e3943, e6600, e7415, e7416, e7419] at *
  tauto
theorem n14828 (_v : Vars) (_q : Query _v)  : (e7643 _v) := by
  have p14542 := n14542 _v _q 
  simp only [e2358, e4139, e4140, e4141, e4142, e6571, e7634, e7640, e7643, e7645, e7648, e7655, e7656, e7657, e7658, e7659, e10960, e10962, e10963, e10964] at *
  tauto
theorem n14829 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e6575 _v) := by
  have p11376 := n11376 _v _q 
  have p11375 := n11375 _v _q 
  have p8663 := n8663 _v _q 
  have p10893 := n10893 _v _q 
  have p10895 := n10895 _v _q h6792
  have p10896 := n10896 _v _q 
  exact FloorCertificate.node_14829 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p11376 p11375 p8663 p10893 p10895 p10896
theorem n14830 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e7668 _v) := by
  have p14544 := n14544 _v _q 
  have p14829 := n14829 _v _q h6792
  simp only [e2351, e4156, e4157, e4158, e4159, e6575, e7660, e7668, e7671] at *
  tauto
theorem n14831 (_v : Vars) (_q : Query _v)  : (e7686 _v) := by
  have p14552 := n14552 _v _q 
  simp only [e2371, e4181, e4182, e4183, e4184, e6579, e7677, e7683, e7686, e7688, e7691, e7698, e7699, e7700, e7701, e7702, e10977, e10979, e10980, e10981] at *
  tauto
end
end Assembly
