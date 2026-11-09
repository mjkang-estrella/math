import Dag024
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n7189 (_v : Vars) (_q : Query _v)  : (e3601 _v) := by
  simp only [e5, e6, e12, e3593, e3598, e3599, e3600, e3601] at *
  omega
theorem n7190 (_v : Vars) (_q : Query _v)  : (e3603 _v) := by
  simp only [e5, e6, e12, e3594, e3598, e3599, e3602, e3603] at *
  omega
theorem n7192 (_v : Vars) (_q : Query _v)  : (e7191 _v) := by
  have p7189 := n7189 _v _q 
  have p7190 := n7190 _v _q 
  change ((e3593 _v) ↔ (e3600 _v)) at p7189
  change ((e3594 _v) ↔ (e3602 _v)) at p7190
  simp only [e7191, e3595, e3604, p7189, p7190]
theorem n7196 (_v : Vars) (_q : Query _v)  : (e7195 _v) := by
  simp only [e5, e6, e12, e3598, e3599, e3600, e3602, e3604, e3605, e3606, e7193, e7194, e7195] at *
  omega
theorem n7207 (_v : Vars) (_q : Query _v)  : (e7206 _v) := by
  simp only [e12, e3610, e3611, e3612, e3613, e3614, e3617, e3620, e7206] at *
  omega
theorem n7208 (_v : Vars) (_q : Query _v)  : (e3629 _v) := by
  simp only [e5, e6, e12, e2938, e3622, e3627, e3628, e3629] at *
  omega
theorem n7209 (_v : Vars) (_q : Query _v)  : (e3631 _v) := by
  simp only [e5, e6, e12, e2938, e3623, e3627, e3630, e3631] at *
  omega
theorem n7211 (_v : Vars) (_q : Query _v)  : (e7210 _v) := by
  have p7208 := n7208 _v _q 
  have p7209 := n7209 _v _q 
  change ((e3622 _v) ↔ (e3628 _v)) at p7208
  change ((e3623 _v) ↔ (e3630 _v)) at p7209
  simp only [e7210, e3624, e3632, p7208, p7209]
theorem n7215 (_v : Vars) (_q : Query _v)  : (e7214 _v) := by
  simp only [e5, e6, e12, e2938, e3627, e3628, e3630, e3632, e3633, e3634, e7212, e7213, e7214] at *
  omega
theorem n7223 (_v : Vars) (_q : Query _v)  : (e7222 _v) := by
  simp only [e12, e3635, e3636, e3637, e3638, e3639, e3642, e3645, e7222] at *
  omega
theorem n7224 (_v : Vars) (_q : Query _v)  : (e3654 _v) := by
  simp only [e5, e6, e12, e2925, e3647, e3652, e3653, e3654] at *
  omega
theorem n7225 (_v : Vars) (_q : Query _v)  : (e3656 _v) := by
  simp only [e5, e6, e12, e2925, e3648, e3652, e3655, e3656] at *
  omega
theorem n7227 (_v : Vars) (_q : Query _v)  : (e7226 _v) := by
  have p7224 := n7224 _v _q 
  have p7225 := n7225 _v _q 
  change ((e3647 _v) ↔ (e3653 _v)) at p7224
  change ((e3648 _v) ↔ (e3655 _v)) at p7225
  simp only [e7226, e3649, e3657, p7224, p7225]
theorem n7231 (_v : Vars) (_q : Query _v)  : (e7230 _v) := by
  simp only [e5, e6, e12, e2925, e3652, e3653, e3655, e3657, e3658, e3659, e7228, e7229, e7230] at *
  omega
theorem n7239 (_v : Vars) (_q : Query _v)  : (e7238 _v) := by
  simp only [e12, e3660, e3661, e3662, e3663, e3664, e3667, e3670, e7238] at *
  omega
theorem n7240 (_v : Vars) (_q : Query _v)  : (e3681 _v) := by
  simp only [e5, e6, e12, e3673, e3678, e3679, e3680, e3681] at *
  omega
theorem n7241 (_v : Vars) (_q : Query _v)  : (e3683 _v) := by
  simp only [e5, e6, e12, e3674, e3678, e3679, e3682, e3683] at *
  omega
theorem n7243 (_v : Vars) (_q : Query _v)  : (e7242 _v) := by
  have p7240 := n7240 _v _q 
  have p7241 := n7241 _v _q 
  change ((e3673 _v) ↔ (e3680 _v)) at p7240
  change ((e3674 _v) ↔ (e3682 _v)) at p7241
  simp only [e7242, e3675, e3684, p7240, p7241]
theorem n7247 (_v : Vars) (_q : Query _v)  : (e7246 _v) := by
  simp only [e5, e6, e12, e3678, e3679, e3680, e3682, e3684, e3685, e3686, e7244, e7245, e7246] at *
  omega
theorem n7255 (_v : Vars) (_q : Query _v)  : (e7254 _v) := by
  simp only [e12, e3687, e3688, e3689, e3690, e3691, e3694, e3697, e7254] at *
  omega
theorem n7256 (_v : Vars) (_q : Query _v)  : (e3708 _v) := by
  simp only [e5, e6, e12, e3700, e3705, e3706, e3707, e3708] at *
  omega
theorem n7257 (_v : Vars) (_q : Query _v)  : (e3710 _v) := by
  simp only [e5, e6, e12, e3701, e3705, e3706, e3709, e3710] at *
  omega
theorem n7259 (_v : Vars) (_q : Query _v)  : (e7258 _v) := by
  have p7256 := n7256 _v _q 
  have p7257 := n7257 _v _q 
  change ((e3700 _v) ↔ (e3707 _v)) at p7256
  change ((e3701 _v) ↔ (e3709 _v)) at p7257
  simp only [e7258, e3702, e3711, p7256, p7257]
theorem n7263 (_v : Vars) (_q : Query _v)  : (e7262 _v) := by
  simp only [e5, e6, e12, e3705, e3706, e3707, e3709, e3711, e3712, e3713, e7260, e7261, e7262] at *
  omega
theorem n7271 (_v : Vars) (_q : Query _v)  : (e7270 _v) := by
  simp only [e12, e3714, e3715, e3716, e3717, e3718, e3721, e3724, e7270] at *
  omega
theorem n7272 (_v : Vars) (_q : Query _v)  : (e3735 _v) := by
  simp only [e5, e6, e12, e3727, e3732, e3733, e3734, e3735] at *
  omega
theorem n7273 (_v : Vars) (_q : Query _v)  : (e3737 _v) := by
  simp only [e5, e6, e12, e3728, e3732, e3733, e3736, e3737] at *
  omega
theorem n7275 (_v : Vars) (_q : Query _v)  : (e7274 _v) := by
  have p7272 := n7272 _v _q 
  have p7273 := n7273 _v _q 
  change ((e3727 _v) ↔ (e3734 _v)) at p7272
  change ((e3728 _v) ↔ (e3736 _v)) at p7273
  simp only [e7274, e3729, e3738, p7272, p7273]
theorem n7279 (_v : Vars) (_q : Query _v)  : (e7278 _v) := by
  simp only [e5, e6, e12, e3732, e3733, e3734, e3736, e3738, e3739, e3740, e7276, e7277, e7278] at *
  omega
theorem n7287 (_v : Vars) (_q : Query _v)  : (e7286 _v) := by
  simp only [e12, e3741, e3742, e3743, e3744, e3745, e3748, e3751, e7286] at *
  omega
theorem n7288 (_v : Vars) (_q : Query _v)  : (e3762 _v) := by
  simp only [e5, e6, e12, e3754, e3759, e3760, e3761, e3762] at *
  omega
theorem n7289 (_v : Vars) (_q : Query _v)  : (e3764 _v) := by
  simp only [e5, e6, e12, e3755, e3759, e3760, e3763, e3764] at *
  omega
theorem n7291 (_v : Vars) (_q : Query _v)  : (e7290 _v) := by
  have p7288 := n7288 _v _q 
  have p7289 := n7289 _v _q 
  change ((e3754 _v) ↔ (e3761 _v)) at p7288
  change ((e3755 _v) ↔ (e3763 _v)) at p7289
  simp only [e7290, e3756, e3765, p7288, p7289]
theorem n7295 (_v : Vars) (_q : Query _v)  : (e7294 _v) := by
  simp only [e5, e6, e12, e3759, e3760, e3761, e3763, e3765, e3766, e3767, e7292, e7293, e7294] at *
  omega
theorem n7303 (_v : Vars) (_q : Query _v)  : (e7302 _v) := by
  simp only [e12, e3768, e3769, e3770, e3771, e3772, e3775, e3778, e7302] at *
  omega
theorem n7304 (_v : Vars) (_q : Query _v)  : (e3787 _v) := by
  simp only [e5, e6, e12, e2960, e3780, e3785, e3786, e3787] at *
  omega
theorem n7305 (_v : Vars) (_q : Query _v)  : (e3789 _v) := by
  simp only [e5, e6, e12, e2960, e3781, e3785, e3788, e3789] at *
  omega
theorem n7307 (_v : Vars) (_q : Query _v)  : (e7306 _v) := by
  have p7304 := n7304 _v _q 
  have p7305 := n7305 _v _q 
  change ((e3780 _v) ↔ (e3786 _v)) at p7304
  change ((e3781 _v) ↔ (e3788 _v)) at p7305
  simp only [e7306, e3782, e3790, p7304, p7305]
theorem n7311 (_v : Vars) (_q : Query _v)  : (e7310 _v) := by
  simp only [e5, e6, e12, e2960, e3785, e3786, e3788, e3790, e3791, e3792, e7308, e7309, e7310] at *
  omega
theorem n7319 (_v : Vars) (_q : Query _v)  : (e7318 _v) := by
  simp only [e12, e3793, e3794, e3795, e3796, e3797, e3800, e3803, e7318] at *
  omega
theorem n7320 (_v : Vars) (_q : Query _v)  : (e3813 _v) := by
  simp only [e5, e6, e12, e2993, e3806, e3811, e3812, e3813] at *
  omega
theorem n7321 (_v : Vars) (_q : Query _v)  : (e3815 _v) := by
  simp only [e5, e6, e12, e2993, e3807, e3811, e3814, e3815] at *
  omega
theorem n7323 (_v : Vars) (_q : Query _v)  : (e7322 _v) := by
  have p7320 := n7320 _v _q 
  have p7321 := n7321 _v _q 
  change ((e3806 _v) ↔ (e3812 _v)) at p7320
  change ((e3807 _v) ↔ (e3814 _v)) at p7321
  simp only [e7322, e3808, e3816, p7320, p7321]
theorem n7327 (_v : Vars) (_q : Query _v)  : (e7326 _v) := by
  simp only [e5, e6, e12, e2993, e3811, e3812, e3814, e3816, e3817, e3818, e7324, e7325, e7326] at *
  omega
theorem n7335 (_v : Vars) (_q : Query _v)  : (e7334 _v) := by
  simp only [e12, e3819, e3820, e3821, e3822, e3823, e3826, e3829, e7334] at *
  omega
end
end Assembly
