import Dag108
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n14510 (_v : Vars) (_q : Query _v)  : (e14509 _v) := by
  simp only [e5, e6, e10, e12, e41, e46, e111, e266, e267, e2752, e2753, e4035, e4042, e4043, e4044, e4046, e4049, e4050, e6754, e7520, e7521, e7522, e7523, e7524, e7530, e7531, e7534, e7544, e7545, e10913, e10914, e10915, e10916, e10917, e14509] at *
  omega
theorem n14512 (_v : Vars) (_q : Query _v)  : (e14511 _v) := by
  have p14508 := n14508 _v _q 
  have p14510 := n14510 _v _q 
  exact (Iff.trans p14508 p14510)
theorem n14513 (_v : Vars) (_q : Query _v)  : (e10917 _v) := by
  have p10469 := n10469 _v _q 
  have p14512 := n14512 _v _q 
  simp only [e2753, e2910, e4036, e4044, e4046, e4049, e4050, e6754, e6755, e6756, e6757, e7520, e7521, e7522, e7523, e7524, e7530, e7531, e7534, e7544, e7545, e10913, e10915, e10916, e10917, e14511] at *
  tauto
theorem n14514 (_v : Vars) (_q : Query _v)  : (e13806 _v) := by
  have p10387 := n10387 _v _q 
  have p13810 := n13810 _v _q 
  simp only [e2598, e4054, e4055, e4056, e4057, e4058, e4059, e4060, e4064, e4065, e4066, e4067, e4068, e6684, e6685, e6686, e6687, e7546, e7554, e7557, e7560, e7562, e10924, e10925, e13806, e13809] at *
  tauto
theorem n14515 (_v : Vars) (_q : Query _v)  : (e7557 _v) := by
  have p14514 := n14514 _v _q 
  simp only [e2598, e4054, e4055, e4056, e4057, e4059, e4060, e4064, e4065, e4066, e4067, e6684, e7546, e7554, e7557, e7560, e7562, e10924, e10925, e13806] at *
  tauto
theorem n14516 (_v : Vars) (_q : Query _v)  : (e7578 _v) := by
  have p12568 := n12568 _v _q 
  change ((e4078 _v) ↔ (e7574 _v)) at p12568
  simp only [e7578, e6681, e7577, p12568]
theorem n14518 (_v : Vars) (_q : Query _v)  : (e14517 _v) := by
  have p14516 := n14516 _v _q 
  have p13815 := n13815 _v _q 
  change ((e6681 _v) ↔ (e7577 _v)) at p14516
  change ((e6682 _v) ↔ (e10930 _v)) at p13815
  simp only [e14517, e6683, e10931, p14516, p13815]
theorem n14520 (_v : Vars) (_q : Query _v)  : (e14519 _v) := by
  simp only [e5, e6, e8, e12, e41, e46, e111, e266, e267, e2604, e2605, e4077, e4084, e4085, e4086, e4088, e4091, e4092, e6680, e7563, e7564, e7565, e7566, e7567, e7573, e7574, e7577, e7587, e7588, e10930, e10931, e10932, e10933, e10934, e14519] at *
  omega
theorem n14522 (_v : Vars) (_q : Query _v)  : (e14521 _v) := by
  have p14518 := n14518 _v _q 
  have p14520 := n14520 _v _q 
  exact (Iff.trans p14518 p14520)
theorem n14523 (_v : Vars) (_q : Query _v)  : (e10934 _v) := by
  have p10381 := n10381 _v _q 
  have p14522 := n14522 _v _q 
  simp only [e2605, e2901, e4078, e4086, e4088, e4091, e4092, e6680, e6681, e6682, e6683, e7563, e7564, e7565, e7566, e7567, e7573, e7574, e7577, e7587, e7588, e10930, e10932, e10933, e10934, e14521] at *
  tauto
theorem n14524 (_v : Vars) (_q : Query _v)  : (e13821 _v) := by
  have p10464 := n10464 _v _q 
  have p13825 := n13825 _v _q 
  simp only [e2733, e4096, e4097, e4098, e4099, e4100, e4101, e4102, e4106, e4107, e4108, e4109, e4110, e6750, e6751, e6752, e6753, e7589, e7597, e7600, e7603, e7605, e10941, e10942, e13821, e13824] at *
  tauto
theorem n14525 (_v : Vars) (_q : Query _v)  : (e7600 _v) := by
  have p14524 := n14524 _v _q 
  simp only [e2733, e4096, e4097, e4098, e4099, e4101, e4102, e4106, e4107, e4108, e4109, e6750, e7589, e7597, e7600, e7603, e7605, e10941, e10942, e13821] at *
  tauto
theorem n14526 (_v : Vars) (_q : Query _v)  : (e7621 _v) := by
  have p12581 := n12581 _v _q 
  change ((e4120 _v) ↔ (e7617 _v)) at p12581
  simp only [e7621, e6747, e7620, p12581]
theorem n14528 (_v : Vars) (_q : Query _v)  : (e14527 _v) := by
  have p14526 := n14526 _v _q 
  have p13830 := n13830 _v _q 
  change ((e6747 _v) ↔ (e7620 _v)) at p14526
  change ((e6748 _v) ↔ (e10951 _v)) at p13830
  simp only [e14527, e6749, e10952, p14526, p13830]
theorem n14530 (_v : Vars) (_q : Query _v)  : (e14529 _v) := by
  simp only [e5, e6, e10, e12, e41, e43, e44, e46, e111, e2739, e2740, e4119, e4126, e4127, e4128, e4130, e4133, e4134, e6746, e7606, e7607, e7608, e7609, e7610, e7616, e7617, e7620, e7630, e7631, e10951, e10952, e10953, e10954, e10955, e14529] at *
  omega
theorem n14532 (_v : Vars) (_q : Query _v)  : (e14531 _v) := by
  have p14528 := n14528 _v _q 
  have p14530 := n14530 _v _q 
  exact (Iff.trans p14528 p14530)
theorem n14533 (_v : Vars) (_q : Query _v)  : (e10955 _v) := by
  have p10458 := n10458 _v _q 
  have p14532 := n14532 _v _q 
  simp only [e2740, e2908, e4120, e4128, e4130, e4133, e4134, e6746, e6747, e6748, e6749, e7606, e7607, e7608, e7609, e7610, e7616, e7617, e7620, e7630, e7631, e10951, e10953, e10954, e10955, e14531] at *
  tauto
theorem n14534 (_v : Vars) (_q : Query _v)  : (e7419 _v) := by
  have p14483 := n14483 _v _q 
  simp only [e2402, e3919, e3920, e3921, e3922, e3923, e3929, e3937, e3939, e3942, e3943, e6600, e7415, e7416, e7419, e7422, e7424, e10861, e10862, e13761] at *
  tauto
theorem n14535 (_v : Vars) (_q : Query _v)  : (e7644 _v) := by
  have p12589 := n12589 _v _q 
  change ((e4143 _v) ↔ (e7640 _v)) at p12589
  simp only [e7644, e6572, e7643, p12589]
theorem n14537 (_v : Vars) (_q : Query _v)  : (e14536 _v) := by
  have p14535 := n14535 _v _q 
  have p13835 := n13835 _v _q 
  change ((e6572 _v) ↔ (e7643 _v)) at p14535
  change ((e6573 _v) ↔ (e10960 _v)) at p13835
  simp only [e14536, e6574, e10961, p14535, p13835]
theorem n14539 (_v : Vars) (_q : Query _v)  : (e14538 _v) := by
  simp only [e5, e6, e8, e10, e12, e41, e111, e2357, e2358, e4137, e4138, e4139, e4140, e4141, e4142, e4154, e6571, e7634, e7640, e7643, e7645, e7648, e7655, e7656, e7657, e7658, e7659, e10960, e10961, e10962, e10963, e10964, e14538] at *
  omega
theorem n14541 (_v : Vars) (_q : Query _v)  : (e14540 _v) := by
  have p14537 := n14537 _v _q 
  have p14539 := n14539 _v _q 
  exact (Iff.trans p14537 p14539)
theorem n14542 (_v : Vars) (_q : Query _v)  : (e10964 _v) := by
  have p10253 := n10253 _v _q 
  have p14541 := n14541 _v _q 
  simp only [e2358, e2878, e4139, e4140, e4141, e4142, e4143, e6571, e6572, e6573, e6574, e7634, e7640, e7643, e7645, e7648, e7655, e7656, e7657, e7658, e7659, e10960, e10962, e10963, e10964, e14540] at *
  tauto
theorem n14543 (_v : Vars) (_q : Query _v)  : (e13841 _v) := by
  have p10259 := n10259 _v _q 
  have p13845 := n13845 _v _q 
  simp only [e2351, e4156, e4157, e4158, e4159, e4160, e4161, e4162, e4166, e4167, e4168, e4169, e4170, e6575, e6576, e6577, e6578, e7660, e7668, e7671, e7674, e7676, e10971, e10972, e13841, e13844] at *
  tauto
theorem n14544 (_v : Vars) (_q : Query _v)  : (e7671 _v) := by
  have p14543 := n14543 _v _q 
  simp only [e2351, e4156, e4157, e4158, e4159, e4161, e4162, e4166, e4167, e4168, e4169, e6575, e7660, e7668, e7671, e7674, e7676, e10971, e10972, e13841] at *
  tauto
theorem n14545 (_v : Vars) (_q : Query _v)  : (e7687 _v) := by
  have p12599 := n12599 _v _q 
  change ((e4185 _v) ↔ (e7683 _v)) at p12599
  simp only [e7687, e6580, e7686, p12599]
theorem n14547 (_v : Vars) (_q : Query _v)  : (e14546 _v) := by
  have p14545 := n14545 _v _q 
  have p13850 := n13850 _v _q 
  change ((e6580 _v) ↔ (e7686 _v)) at p14545
  change ((e6581 _v) ↔ (e10977 _v)) at p13850
  simp only [e14546, e6582, e10978, p14545, p13850]
theorem n14549 (_v : Vars) (_q : Query _v)  : (e14548 _v) := by
  simp only [e5, e6, e8, e10, e12, e41, e43, e44, e111, e2370, e2371, e4179, e4180, e4181, e4182, e4183, e4184, e4196, e6579, e7677, e7683, e7686, e7688, e7691, e7698, e7699, e7700, e7701, e7702, e10977, e10978, e10979, e10980, e10981, e14548] at *
  omega
theorem n14551 (_v : Vars) (_q : Query _v)  : (e14550 _v) := by
  have p14547 := n14547 _v _q 
  have p14549 := n14549 _v _q 
  exact (Iff.trans p14547 p14549)
theorem n14552 (_v : Vars) (_q : Query _v)  : (e10981 _v) := by
  have p10264 := n10264 _v _q 
  have p14551 := n14551 _v _q 
  simp only [e2371, e2880, e4181, e4182, e4183, e4184, e4185, e6579, e6580, e6581, e6582, e7677, e7683, e7686, e7688, e7691, e7698, e7699, e7700, e7701, e7702, e10977, e10979, e10980, e10981, e14550] at *
  tauto
theorem n14553 (_v : Vars) (_q : Query _v)  : (e7713 _v) := by
  have p12607 := n12607 _v _q 
  change ((e4203 _v) ↔ (e7709 _v)) at p12607
  simp only [e7713, e6717, e7712, p12607]
theorem n14555 (_v : Vars) (_q : Query _v)  : (e14554 _v) := by
  have p14553 := n14553 _v _q 
  have p13855 := n13855 _v _q 
  change ((e6717 _v) ↔ (e7712 _v)) at p14553
  change ((e6718 _v) ↔ (e10986 _v)) at p13855
  simp only [e14554, e6719, e10987, p14553, p13855]
theorem n14557 (_v : Vars) (_q : Query _v)  : (e14556 _v) := by
  simp only [e5, e6, e8, e10, e12, e41, e46, e2679, e2680, e4197, e4198, e4199, e4200, e4201, e4202, e4214, e6716, e7703, e7709, e7712, e7714, e7717, e7724, e7725, e7726, e7727, e7728, e10986, e10987, e10988, e10989, e10990, e14556] at *
  omega
theorem n14559 (_v : Vars) (_q : Query _v)  : (e14558 _v) := by
  have p14555 := n14555 _v _q 
  have p14557 := n14557 _v _q 
  exact (Iff.trans p14555 p14557)
theorem n14560 (_v : Vars) (_q : Query _v)  : (e10990 _v) := by
  have p10409 := n10409 _v _q 
  have p14559 := n14559 _v _q 
  simp only [e2680, e2903, e4199, e4200, e4201, e4202, e4203, e6716, e6717, e6718, e6719, e7703, e7709, e7712, e7714, e7717, e7724, e7725, e7726, e7727, e7728, e10986, e10988, e10989, e10990, e14558] at *
  tauto
theorem n14561 (_v : Vars) (_q : Query _v)  : (e7745 _v) := by
  have p12615 := n12615 _v _q 
  change ((e4222 _v) ↔ (e7739 _v)) at p12615
  simp only [e7745, e7743, e7744, p12615]
theorem n14562 (_v : Vars) (_q : Query _v)  : (e12622 _v) := by
  have p14561 := n14561 _v _q 
  have p13858 := n13858 _v _q 
  change ((e7743 _v) ↔ (e7744 _v)) at p14561
  change ((e6479 _v) ↔ (e11001 _v)) at p13858
  simp only [e12622, e10173, e11002, p14561, p13858]
theorem n14564 (_v : Vars) (_q : Query _v)  : (e14563 _v) := by
  simp only [e5, e6, e8, e12, e41, e111, e2131, e2132, e4216, e4217, e4218, e4219, e4220, e4221, e4234, e7733, e7739, e7742, e7744, e7747, e7749, e7751, e7752, e7753, e7754, e7755, e11001, e11002, e11003, e11004, e11005, e14563] at *
  omega
theorem n14565 (_v : Vars) (_q : Query _v)  : (e12623 _v) := by
  have p14562 := n14562 _v _q 
  have p14564 := n14564 _v _q 
  exact (Iff.trans p14562 p14564)
theorem n14566 (_v : Vars) (_q : Query _v)  : (e11005 _v) := by
  have p10174 := n10174 _v _q 
  have p14565 := n14565 _v _q 
  simp only [e2132, e4218, e4219, e4220, e4221, e4222, e6478, e6479, e7733, e7739, e7742, e7743, e7744, e7747, e7749, e7751, e7752, e7753, e7754, e7755, e10173, e11001, e11003, e11004, e11005, e12623] at *
  tauto
theorem n14567 (_v : Vars) (_q : Query _v)  : (e7779 _v) := by
  have p13863 := n13863 _v _q 
  simp only [e163, e165, e4236, e4237, e4246, e4248, e4251, e4252, e7756, e7757, e7758, e7765, e7766, e7769, e7775, e7779, e7780, e11015, e11016, e11017] at *
  tauto
theorem n14568 (_v : Vars) (_q : Query _v)  : (e7775 _v) := by
  have p14567 := n14567 _v _q 
  have p11376 := n11376 _v _q 
  simp only [e163, e165, e4236, e4237, e7756, e7757, e7758, e7775, e7779] at *
  tauto
theorem n14569 (_v : Vars) (_q : Query _v)  : (e13869 _v) := by
  have p10502 := n10502 _v _q 
  have p13873 := n13873 _v _q 
  simp only [e2781, e4258, e4259, e4260, e4261, e4262, e4263, e4264, e4268, e4269, e4270, e4271, e4272, e6776, e6777, e6778, e6779, e7781, e7789, e7792, e7795, e7797, e11025, e11026, e13869, e13872] at *
  tauto
theorem n14570 (_v : Vars) (_q : Query _v)  : (e7792 _v) := by
  have p14569 := n14569 _v _q 
  simp only [e2781, e4258, e4259, e4260, e4261, e4263, e4264, e4268, e4269, e4270, e4271, e6776, e7781, e7789, e7792, e7795, e7797, e11025, e11026, e13869] at *
  tauto
theorem n14571 (_v : Vars) (_q : Query _v)  : (e7810 _v) := by
  have p12638 := n12638 _v _q 
  change ((e4287 _v) ↔ (e7804 _v)) at p12638
  simp only [e7810, e7808, e7809, p12638]
end
end Assembly
