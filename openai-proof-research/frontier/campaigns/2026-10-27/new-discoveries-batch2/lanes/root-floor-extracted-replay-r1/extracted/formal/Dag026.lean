import Dag025
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n7336 (_v : Vars) (_q : Query _v)  : (e3840 _v) := by
  simp only [e5, e6, e12, e3832, e3837, e3838, e3839, e3840] at *
  omega
theorem n7337 (_v : Vars) (_q : Query _v)  : (e3842 _v) := by
  simp only [e5, e6, e12, e3833, e3837, e3838, e3841, e3842] at *
  omega
theorem n7339 (_v : Vars) (_q : Query _v)  : (e7338 _v) := by
  have p7336 := n7336 _v _q 
  have p7337 := n7337 _v _q 
  change ((e3832 _v) ↔ (e3839 _v)) at p7336
  change ((e3833 _v) ↔ (e3841 _v)) at p7337
  simp only [e7338, e3834, e3843, p7336, p7337]
theorem n7343 (_v : Vars) (_q : Query _v)  : (e7342 _v) := by
  simp only [e5, e6, e12, e3837, e3838, e3839, e3841, e3843, e3844, e3845, e7340, e7341, e7342] at *
  omega
theorem n7353 (_v : Vars) (_q : Query _v)  : (e7352 _v) := by
  simp only [e12, e3854, e3855, e3856, e3859, e3860, e3861, e3862, e7352] at *
  omega
theorem n7354 (_v : Vars) (_q : Query _v)  : (e3869 _v) := by
  simp only [e5, e6, e12, e3847, e3848, e3849, e3864, e3869] at *
  omega
theorem n7355 (_v : Vars) (_q : Query _v)  : (e3870 _v) := by
  simp only [e5, e6, e12, e3847, e3848, e3851, e3865, e3870] at *
  omega
theorem n7357 (_v : Vars) (_q : Query _v)  : (e7356 _v) := by
  have p7354 := n7354 _v _q 
  have p7355 := n7355 _v _q 
  change ((e3864 _v) ↔ (e3849 _v)) at p7354
  change ((e3865 _v) ↔ (e3851 _v)) at p7355
  simp only [e7356, e3866, e3871, p7354, p7355]
theorem n7360 (_v : Vars) (_q : Query _v)  : (e7359 _v) := by
  simp only [e5, e6, e12, e3847, e3848, e3849, e3850, e3851, e3852, e3871, e7350, e7358, e7359] at *
  omega
theorem n7367 (_v : Vars) (_q : Query _v)  : (e3872 _v) := by
  simp only [e3854, e3855, e3859, e3860, e3861, e3872] at *
  tauto
theorem n7368 (_v : Vars) (_q : Query _v) (h3860 : (e3860 _v)) : (e3860 _v) := by
  exact h3860
theorem n7369 (_v : Vars) (_q : Query _v) (h3860 : (e3860 _v)) : (e3861 _v) := by
  have p7367 := n7367 _v _q 
  have p7368 := n7368 _v _q h3860
  simp only [e3854, e3855, e3859, e3860, e3861, e3872] at *
  tauto
theorem n7376 (_v : Vars) (_q : Query _v)  : (e3883 _v) := by
  simp only [e5, e6, e12, e3875, e3880, e3881, e3882, e3883] at *
  omega
theorem n7377 (_v : Vars) (_q : Query _v)  : (e3885 _v) := by
  simp only [e5, e6, e12, e3876, e3880, e3881, e3884, e3885] at *
  omega
theorem n7379 (_v : Vars) (_q : Query _v)  : (e7378 _v) := by
  have p7376 := n7376 _v _q 
  have p7377 := n7377 _v _q 
  change ((e3875 _v) ↔ (e3882 _v)) at p7376
  change ((e3876 _v) ↔ (e3884 _v)) at p7377
  simp only [e7378, e3877, e3886, p7376, p7377]
theorem n7383 (_v : Vars) (_q : Query _v)  : (e7382 _v) := by
  simp only [e5, e6, e12, e3880, e3881, e3882, e3884, e3886, e3887, e3888, e7380, e7381, e7382] at *
  omega
theorem n7394 (_v : Vars) (_q : Query _v)  : (e7393 _v) := by
  simp only [e12, e3892, e3893, e3894, e3895, e3896, e3899, e3902, e7393] at *
  omega
theorem n7395 (_v : Vars) (_q : Query _v)  : (e3913 _v) := by
  simp only [e5, e6, e12, e3905, e3910, e3911, e3912, e3913] at *
  omega
theorem n7396 (_v : Vars) (_q : Query _v)  : (e3915 _v) := by
  simp only [e5, e6, e12, e3906, e3910, e3911, e3914, e3915] at *
  omega
theorem n7398 (_v : Vars) (_q : Query _v)  : (e7397 _v) := by
  have p7395 := n7395 _v _q 
  have p7396 := n7396 _v _q 
  change ((e3905 _v) ↔ (e3912 _v)) at p7395
  change ((e3906 _v) ↔ (e3914 _v)) at p7396
  simp only [e7397, e3907, e3916, p7395, p7396]
theorem n7402 (_v : Vars) (_q : Query _v)  : (e7401 _v) := by
  simp only [e5, e6, e12, e3910, e3911, e3912, e3914, e3916, e3917, e3918, e7399, e7400, e7401] at *
  omega
theorem n7410 (_v : Vars) (_q : Query _v)  : (e7409 _v) := by
  simp only [e12, e3919, e3920, e3921, e3922, e3923, e3926, e3929, e7409] at *
  omega
theorem n7411 (_v : Vars) (_q : Query _v)  : (e3938 _v) := by
  simp only [e5, e6, e12, e2956, e3931, e3936, e3937, e3938] at *
  omega
theorem n7412 (_v : Vars) (_q : Query _v)  : (e3940 _v) := by
  simp only [e5, e6, e12, e2956, e3932, e3936, e3939, e3940] at *
  omega
theorem n7414 (_v : Vars) (_q : Query _v)  : (e7413 _v) := by
  have p7411 := n7411 _v _q 
  have p7412 := n7412 _v _q 
  change ((e3931 _v) ↔ (e3937 _v)) at p7411
  change ((e3932 _v) ↔ (e3939 _v)) at p7412
  simp only [e7413, e3933, e3941, p7411, p7412]
theorem n7418 (_v : Vars) (_q : Query _v)  : (e7417 _v) := by
  simp only [e5, e6, e12, e2956, e3936, e3937, e3939, e3941, e3942, e3943, e7415, e7416, e7417] at *
  omega
theorem n7426 (_v : Vars) (_q : Query _v)  : (e7425 _v) := by
  simp only [e12, e3944, e3945, e3946, e3947, e3948, e3951, e3954, e7425] at *
  omega
theorem n7427 (_v : Vars) (_q : Query _v)  : (e3964 _v) := by
  simp only [e5, e6, e12, e3956, e3961, e3962, e3963, e3964] at *
  omega
theorem n7428 (_v : Vars) (_q : Query _v)  : (e3966 _v) := by
  simp only [e5, e6, e12, e3957, e3961, e3962, e3965, e3966] at *
  omega
theorem n7430 (_v : Vars) (_q : Query _v)  : (e7429 _v) := by
  have p7427 := n7427 _v _q 
  have p7428 := n7428 _v _q 
  change ((e3956 _v) ↔ (e3963 _v)) at p7427
  change ((e3957 _v) ↔ (e3965 _v)) at p7428
  simp only [e7429, e3958, e3967, p7427, p7428]
theorem n7434 (_v : Vars) (_q : Query _v)  : (e7433 _v) := by
  simp only [e5, e6, e12, e3961, e3962, e3963, e3965, e3967, e3968, e3969, e7431, e7432, e7433] at *
  omega
theorem n7445 (_v : Vars) (_q : Query _v)  : (e7444 _v) := by
  simp only [e12, e3976, e3977, e3978, e3981, e3982, e3983, e3984, e7444] at *
  omega
theorem n7446 (_v : Vars) (_q : Query _v)  : (e3991 _v) := by
  simp only [e5, e6, e12, e2991, e3970, e3971, e3986, e3991] at *
  omega
theorem n7447 (_v : Vars) (_q : Query _v)  : (e3992 _v) := by
  simp only [e5, e6, e12, e2991, e3970, e3973, e3987, e3992] at *
  omega
theorem n7449 (_v : Vars) (_q : Query _v)  : (e7448 _v) := by
  have p7446 := n7446 _v _q 
  have p7447 := n7447 _v _q 
  change ((e3986 _v) ↔ (e3971 _v)) at p7446
  change ((e3987 _v) ↔ (e3973 _v)) at p7447
  simp only [e7448, e3988, e3993, p7446, p7447]
theorem n7452 (_v : Vars) (_q : Query _v)  : (e7451 _v) := by
  simp only [e5, e6, e12, e2991, e3970, e3971, e3972, e3973, e3974, e3993, e7442, e7450, e7451] at *
  omega
theorem n7465 (_v : Vars) (_q : Query _v)  : (e4004 _v) := by
  simp only [e5, e6, e12, e3996, e4001, e4002, e4003, e4004] at *
  omega
theorem n7466 (_v : Vars) (_q : Query _v)  : (e4006 _v) := by
  simp only [e5, e6, e12, e3997, e4001, e4002, e4005, e4006] at *
  omega
theorem n7468 (_v : Vars) (_q : Query _v)  : (e7467 _v) := by
  have p7465 := n7465 _v _q 
  have p7466 := n7466 _v _q 
  change ((e3996 _v) ↔ (e4003 _v)) at p7465
  change ((e3997 _v) ↔ (e4005 _v)) at p7466
  simp only [e7467, e3998, e4007, p7465, p7466]
theorem n7472 (_v : Vars) (_q : Query _v)  : (e7471 _v) := by
  simp only [e5, e6, e12, e4001, e4002, e4003, e4005, e4007, e4008, e4009, e7469, e7470, e7471] at *
  omega
theorem n7476 (_v : Vars) (_q : Query _v)  : (e7475 _v) := by
  simp only [e5, e6, e8, e10, e12, e41, e46, e266, e267, e781, e782, e2692, e3994, e4010, e7459, e7475] at *
  omega
theorem n7478 (_v : Vars) (_q : Query _v)  : (e7477 _v) := by
  simp only [e5, e6, e8, e10, e12, e41, e46, e266, e267, e781, e782, e2692, e3994, e4011, e7461, e7477] at *
  omega
theorem n7482 (_v : Vars) (_q : Query _v)  : (e7481 _v) := by
  have p7476 := n7476 _v _q 
  have p7478 := n7478 _v _q 
  change ((e4010 _v) ↔ (e7459 _v)) at p7476
  change ((e4011 _v) ↔ (e7461 _v)) at p7478
  simp only [e7481, e7479, e7480, p7476, p7478]
theorem n7487 (_v : Vars) (_q : Query _v) (h79 : (e79 _v)) : (e79 _v) := by
  exact h79
theorem n7488 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) : (e5362 _v) := by
  exact h5362
end
end Assembly
