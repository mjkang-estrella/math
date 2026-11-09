import Dag026
import generated.th_lemma_0
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n7490 (_v : Vars) (_q : Query _v) (h79 : (e79 _v)) (h5362 : (e5362 _v)) : (e7489 _v) := by
  have p7487 := n7487 _v _q h79
  have p7488 := n7488 _v _q h5362
  have p3130 := n3130 _v _q 
  have p4016 := n4016 _v _q 
  exact FloorCertificate.node_7490 (e2 _v) (e7 _v) (e9 _v) (e45 _v) (e110 _v) p7487 p7488 p3130 p4016
theorem n7492 (_v : Vars) (_q : Query _v)  : (e7491 _v) := by
  by_contra hc
  change ¬ ((e436 _v) ∨ (¬ (e79 _v))) at hc
  have h79 : (e79 _v) := by
    tauto
  have h5362 : (e5362 _v) := by
    change (¬ (e436 _v))
    tauto
  have p7490 := n7490 _v _q h79 h5362
  exact p7490
theorem n7499 (_v : Vars) (_q : Query _v)  : (e4027 _v) := by
  simp only [e5, e6, e12, e4019, e4024, e4025, e4026, e4027] at *
  omega
theorem n7500 (_v : Vars) (_q : Query _v)  : (e4029 _v) := by
  simp only [e5, e6, e12, e4020, e4024, e4025, e4028, e4029] at *
  omega
theorem n7502 (_v : Vars) (_q : Query _v)  : (e7501 _v) := by
  have p7499 := n7499 _v _q 
  have p7500 := n7500 _v _q 
  change ((e4019 _v) ↔ (e4026 _v)) at p7499
  change ((e4020 _v) ↔ (e4028 _v)) at p7500
  simp only [e7501, e4021, e4030, p7499, p7500]
theorem n7506 (_v : Vars) (_q : Query _v)  : (e7505 _v) := by
  simp only [e5, e6, e12, e4024, e4025, e4026, e4028, e4030, e4031, e4032, e7503, e7504, e7505] at *
  omega
theorem n7510 (_v : Vars) (_q : Query _v)  : (e7509 _v) := by
  simp only [e5, e6, e8, e10, e12, e41, e43, e44, e46, e760, e761, e2681, e4017, e4033, e7493, e7509] at *
  omega
theorem n7512 (_v : Vars) (_q : Query _v)  : (e7511 _v) := by
  simp only [e5, e6, e8, e10, e12, e41, e43, e44, e46, e760, e761, e2681, e4017, e4034, e7495, e7511] at *
  omega
theorem n7516 (_v : Vars) (_q : Query _v)  : (e7515 _v) := by
  have p7510 := n7510 _v _q 
  have p7512 := n7512 _v _q 
  change ((e4033 _v) ↔ (e7493 _v)) at p7510
  change ((e4034 _v) ↔ (e7495 _v)) at p7512
  simp only [e7515, e7513, e7514, p7510, p7512]
theorem n7526 (_v : Vars) (_q : Query _v)  : (e4045 _v) := by
  simp only [e5, e6, e12, e4037, e4042, e4043, e4044, e4045] at *
  omega
theorem n7527 (_v : Vars) (_q : Query _v)  : (e4047 _v) := by
  simp only [e5, e6, e12, e4038, e4042, e4043, e4046, e4047] at *
  omega
theorem n7529 (_v : Vars) (_q : Query _v)  : (e7528 _v) := by
  have p7526 := n7526 _v _q 
  have p7527 := n7527 _v _q 
  change ((e4037 _v) ↔ (e4044 _v)) at p7526
  change ((e4038 _v) ↔ (e4046 _v)) at p7527
  simp only [e7528, e4039, e4048, p7526, p7527]
theorem n7533 (_v : Vars) (_q : Query _v)  : (e7532 _v) := by
  simp only [e5, e6, e12, e4042, e4043, e4044, e4046, e4048, e4049, e4050, e7530, e7531, e7532] at *
  omega
theorem n7537 (_v : Vars) (_q : Query _v)  : (e7536 _v) := by
  simp only [e5, e6, e10, e12, e41, e46, e111, e266, e267, e781, e782, e2741, e4035, e4051, e7520, e7536] at *
  omega
theorem n7539 (_v : Vars) (_q : Query _v)  : (e7538 _v) := by
  simp only [e5, e6, e10, e12, e41, e46, e111, e266, e267, e781, e782, e2741, e4035, e4052, e7522, e7538] at *
  omega
theorem n7543 (_v : Vars) (_q : Query _v)  : (e7542 _v) := by
  have p7537 := n7537 _v _q 
  have p7539 := n7539 _v _q 
  change ((e4051 _v) ↔ (e7520 _v)) at p7537
  change ((e4052 _v) ↔ (e7522 _v)) at p7539
  simp only [e7542, e7540, e7541, p7537, p7539]
theorem n7549 (_v : Vars) (_q : Query _v)  : (e7548 _v) := by
  simp only [e12, e4059, e4060, e4061, e4064, e4065, e4066, e4067, e7548] at *
  omega
theorem n7550 (_v : Vars) (_q : Query _v)  : (e4074 _v) := by
  simp only [e5, e6, e12, e2973, e4053, e4054, e4069, e4074] at *
  omega
theorem n7551 (_v : Vars) (_q : Query _v)  : (e4075 _v) := by
  simp only [e5, e6, e12, e2973, e4053, e4056, e4070, e4075] at *
  omega
theorem n7553 (_v : Vars) (_q : Query _v)  : (e7552 _v) := by
  have p7550 := n7550 _v _q 
  have p7551 := n7551 _v _q 
  change ((e4069 _v) ↔ (e4054 _v)) at p7550
  change ((e4070 _v) ↔ (e4056 _v)) at p7551
  simp only [e7552, e4071, e4076, p7550, p7551]
theorem n7556 (_v : Vars) (_q : Query _v)  : (e7555 _v) := by
  simp only [e5, e6, e12, e2973, e4053, e4054, e4055, e4056, e4057, e4076, e7546, e7554, e7555] at *
  omega
theorem n7569 (_v : Vars) (_q : Query _v)  : (e4087 _v) := by
  simp only [e5, e6, e12, e4079, e4084, e4085, e4086, e4087] at *
  omega
theorem n7570 (_v : Vars) (_q : Query _v)  : (e4089 _v) := by
  simp only [e5, e6, e12, e4080, e4084, e4085, e4088, e4089] at *
  omega
theorem n7572 (_v : Vars) (_q : Query _v)  : (e7571 _v) := by
  have p7569 := n7569 _v _q 
  have p7570 := n7570 _v _q 
  change ((e4079 _v) ↔ (e4086 _v)) at p7569
  change ((e4080 _v) ↔ (e4088 _v)) at p7570
  simp only [e7571, e4081, e4090, p7569, p7570]
theorem n7576 (_v : Vars) (_q : Query _v)  : (e7575 _v) := by
  simp only [e5, e6, e12, e4084, e4085, e4086, e4088, e4090, e4091, e4092, e7573, e7574, e7575] at *
  omega
theorem n7580 (_v : Vars) (_q : Query _v)  : (e7579 _v) := by
  simp only [e5, e6, e8, e12, e41, e46, e111, e266, e267, e781, e782, e2593, e4077, e4093, e7563, e7579] at *
  omega
theorem n7582 (_v : Vars) (_q : Query _v)  : (e7581 _v) := by
  simp only [e5, e6, e8, e12, e41, e46, e111, e266, e267, e781, e782, e2593, e4077, e4094, e7565, e7581] at *
  omega
theorem n7586 (_v : Vars) (_q : Query _v)  : (e7585 _v) := by
  have p7580 := n7580 _v _q 
  have p7582 := n7582 _v _q 
  change ((e4093 _v) ↔ (e7563 _v)) at p7580
  change ((e4094 _v) ↔ (e7565 _v)) at p7582
  simp only [e7585, e7583, e7584, p7580, p7582]
theorem n7592 (_v : Vars) (_q : Query _v)  : (e7591 _v) := by
  simp only [e12, e4101, e4102, e4103, e4106, e4107, e4108, e4109, e7591] at *
  omega
theorem n7593 (_v : Vars) (_q : Query _v)  : (e4116 _v) := by
  simp only [e5, e6, e12, e2989, e4095, e4096, e4111, e4116] at *
  omega
theorem n7594 (_v : Vars) (_q : Query _v)  : (e4117 _v) := by
  simp only [e5, e6, e12, e2989, e4095, e4098, e4112, e4117] at *
  omega
theorem n7596 (_v : Vars) (_q : Query _v)  : (e7595 _v) := by
  have p7593 := n7593 _v _q 
  have p7594 := n7594 _v _q 
  change ((e4111 _v) ↔ (e4096 _v)) at p7593
  change ((e4112 _v) ↔ (e4098 _v)) at p7594
  simp only [e7595, e4113, e4118, p7593, p7594]
theorem n7599 (_v : Vars) (_q : Query _v)  : (e7598 _v) := by
  simp only [e5, e6, e12, e2989, e4095, e4096, e4097, e4098, e4099, e4118, e7589, e7597, e7598] at *
  omega
theorem n7612 (_v : Vars) (_q : Query _v)  : (e4129 _v) := by
  simp only [e5, e6, e12, e4121, e4126, e4127, e4128, e4129] at *
  omega
theorem n7613 (_v : Vars) (_q : Query _v)  : (e4131 _v) := by
  simp only [e5, e6, e12, e4122, e4126, e4127, e4130, e4131] at *
  omega
theorem n7615 (_v : Vars) (_q : Query _v)  : (e7614 _v) := by
  have p7612 := n7612 _v _q 
  have p7613 := n7613 _v _q 
  change ((e4121 _v) ↔ (e4128 _v)) at p7612
  change ((e4122 _v) ↔ (e4130 _v)) at p7613
  simp only [e7614, e4123, e4132, p7612, p7613]
theorem n7619 (_v : Vars) (_q : Query _v)  : (e7618 _v) := by
  simp only [e5, e6, e12, e4126, e4127, e4128, e4130, e4132, e4133, e4134, e7616, e7617, e7618] at *
  omega
theorem n7623 (_v : Vars) (_q : Query _v)  : (e7622 _v) := by
  simp only [e5, e6, e10, e12, e41, e43, e44, e46, e111, e760, e761, e2728, e4119, e4135, e7606, e7622] at *
  omega
theorem n7625 (_v : Vars) (_q : Query _v)  : (e7624 _v) := by
  simp only [e5, e6, e10, e12, e41, e43, e44, e46, e111, e760, e761, e2728, e4119, e4136, e7608, e7624] at *
  omega
theorem n7629 (_v : Vars) (_q : Query _v)  : (e7628 _v) := by
  have p7623 := n7623 _v _q 
  have p7625 := n7625 _v _q 
  change ((e4135 _v) ↔ (e7606 _v)) at p7623
  change ((e4136 _v) ↔ (e7608 _v)) at p7625
  simp only [e7628, e7626, e7627, p7623, p7625]
theorem n7636 (_v : Vars) (_q : Query _v)  : (e4149 _v) := by
  simp only [e5, e6, e12, e4137, e4138, e4139, e4144, e4149] at *
  omega
theorem n7637 (_v : Vars) (_q : Query _v)  : (e4150 _v) := by
  simp only [e5, e6, e12, e4137, e4138, e4141, e4145, e4150] at *
  omega
theorem n7639 (_v : Vars) (_q : Query _v)  : (e7638 _v) := by
  have p7636 := n7636 _v _q 
  have p7637 := n7637 _v _q 
  change ((e4144 _v) ↔ (e4139 _v)) at p7636
  change ((e4145 _v) ↔ (e4141 _v)) at p7637
  simp only [e7638, e4146, e4151, p7636, p7637]
theorem n7642 (_v : Vars) (_q : Query _v)  : (e7641 _v) := by
  simp only [e5, e6, e12, e4137, e4138, e4139, e4140, e4141, e4142, e4151, e7634, e7640, e7641] at *
  omega
theorem n7647 (_v : Vars) (_q : Query _v)  : (e7646 _v) := by
  simp only [e5, e6, e8, e10, e12, e36, e41, e111, e2346, e4152, e4154, e7645, e7646] at *
  omega
end
end Assembly
