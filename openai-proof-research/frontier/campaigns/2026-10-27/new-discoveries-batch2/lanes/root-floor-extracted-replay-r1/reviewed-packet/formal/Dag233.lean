import Dag232
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n20515 (_v : Vars) (_q : Query _v)  : (e3795 _v) := by
  have p20514 := n20514 _v _q 
  have p14465 := n14465 _v _q 
  change (e3797 _v) ∨ (e3795 _v) at p20514
  change (¬ (e3797 _v)) at p14465
  rcases p20514 with hlit | hlit
  · exact (False.elim (p14465 hlit))
  · exact hlit
theorem n20516 (_v : Vars) (_q : Query _v)  : (e5031 _v) := by
  simp only [e3976, e3977, e3981, e3982, e3983, e5031] at *
  tauto
theorem n20517 (_v : Vars) (_q : Query _v)  : (e3977 _v) := by
  have p20516 := n20516 _v _q 
  have p20070 := n20070 _v _q 
  change (e3983 _v) ∨ (e3977 _v) at p20516
  change (¬ (e3983 _v)) at p20070
  rcases p20516 with hlit | hlit
  · exact (False.elim (p20070 hlit))
  · exact hlit
theorem n20518 (_v : Vars) (_q : Query _v)  : (e5032 _v) := by
  simp only [e4101, e4102, e4106, e4107, e4108, e5032] at *
  tauto
theorem n20519 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e4102 _v) := by
  have p20518 := n20518 _v _q 
  have p15870 := n15870 _v _q h251
  change (e4108 _v) ∨ (e4102 _v) at p20518
  change (¬ (e4108 _v)) at p15870
  rcases p20518 with hlit | hlit
  · exact (False.elim (p15870 hlit))
  · exact hlit
theorem n20520 (_v : Vars) (_q : Query _v)  : (e5033 _v) := by
  simp only [e3236, e3237, e3238, e3239, e3240, e5033] at *
  tauto
theorem n20521 (_v : Vars) (_q : Query _v)  : (e3238 _v) := by
  have p20520 := n20520 _v _q 
  have p14375 := n14375 _v _q 
  change (e3240 _v) ∨ (e3238 _v) at p20520
  change (¬ (e3240 _v)) at p14375
  rcases p20520 with hlit | hlit
  · exact (False.elim (p14375 hlit))
  · exact hlit
theorem n20522 (_v : Vars) (_q : Query _v)  : (e5034 _v) := by
  simp only [e4491, e4492, e4496, e4497, e4498, e5034] at *
  tauto
theorem n20523 (_v : Vars) (_q : Query _v)  : (e4492 _v) := by
  have p20522 := n20522 _v _q 
  have p20095 := n20095 _v _q 
  change (e4498 _v) ∨ (e4492 _v) at p20522
  change (¬ (e4498 _v)) at p20095
  rcases p20522 with hlit | hlit
  · exact (False.elim (p20095 hlit))
  · exact hlit
theorem n20524 (_v : Vars) (_q : Query _v)  : (e5035 _v) := by
  simp only [e51, e52, e57, e58, e59, e5035] at *
  tauto
theorem n20525 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e52 _v) := by
  have p20524 := n20524 _v _q 
  have p15871 := n15871 _v _q h251
  change (e59 _v) ∨ (e52 _v) at p20524
  change (¬ (e59 _v)) at p15871
  rcases p20524 with hlit | hlit
  · exact (False.elim (p15871 hlit))
  · exact hlit
theorem n20526 (_v : Vars) (_q : Query _v)  : (e5036 _v) := by
  simp only [e3741, e3742, e3743, e3744, e3745, e5036] at *
  tauto
theorem n20527 (_v : Vars) (_q : Query _v)  : (e3741 _v) := by
  have p20526 := n20526 _v _q 
  have p14457 := n14457 _v _q 
  change (e3745 _v) ∨ (e3741 _v) at p20526
  change (¬ (e3745 _v)) at p14457
  rcases p20526 with hlit | hlit
  · exact (False.elim (p14457 hlit))
  · exact hlit
theorem n20528 (_v : Vars) (_q : Query _v)  : (e5037 _v) := by
  simp only [e3819, e3820, e3821, e3822, e3823, e5037] at *
  tauto
theorem n20529 (_v : Vars) (_q : Query _v)  : (e3819 _v) := by
  have p20528 := n20528 _v _q 
  have p14469 := n14469 _v _q 
  change (e3823 _v) ∨ (e3819 _v) at p20528
  change (¬ (e3823 _v)) at p14469
  rcases p20528 with hlit | hlit
  · exact (False.elim (p14469 hlit))
  · exact hlit
theorem n20530 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e3172 _v) := by
  have p18598 := n18598 _v _q 
  have p15875 := n15875 _v _q h251
  change (e3179 _v) ∨ (e3172 _v) at p18598
  change (¬ (e3179 _v)) at p15875
  rcases p18598 with hlit | hlit
  · exact (False.elim (p15875 hlit))
  · exact hlit
theorem n20531 (_v : Vars) (_q : Query _v)  : (e5038 _v) := by
  simp only [e4372, e4373, e4377, e4378, e4379, e5038] at *
  tauto
theorem n20532 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e4372 _v) := by
  have p20531 := n20531 _v _q 
  have p15118 := n15118 _v _q h251
  change (e4379 _v) ∨ (e4372 _v) at p20531
  change (¬ (e4379 _v)) at p15118
  rcases p20531 with hlit | hlit
  · exact (False.elim (p15118 hlit))
  · exact hlit
theorem n20533 (_v : Vars) (_q : Query _v)  : (e5039 _v) := by
  simp only [e3210, e3211, e3212, e3213, e3214, e5039] at *
  tauto
theorem n20534 (_v : Vars) (_q : Query _v)  : (e3212 _v) := by
  have p20533 := n20533 _v _q 
  have p14371 := n14371 _v _q 
  change (e3214 _v) ∨ (e3212 _v) at p20533
  change (¬ (e3214 _v)) at p14371
  rcases p20533 with hlit | hlit
  · exact (False.elim (p14371 hlit))
  · exact hlit
theorem n20535 (_v : Vars) (_q : Query _v)  : (e5040 _v) := by
  simp only [e4059, e4060, e4064, e4065, e4066, e5040] at *
  tauto
theorem n20536 (_v : Vars) (_q : Query _v)  : (e4060 _v) := by
  have p20535 := n20535 _v _q 
  have p19592 := n19592 _v _q 
  change (e4066 _v) ∨ (e4060 _v) at p20535
  change (¬ (e4066 _v)) at p19592
  rcases p20535 with hlit | hlit
  · exact (False.elim (p19592 hlit))
  · exact hlit
theorem n20537 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e4307 _v) := by
  have p16995 := n16995 _v _q 
  have p15849 := n15849 _v _q h251
  change (e4313 _v) ∨ (e4307 _v) at p16995
  change (¬ (e4313 _v)) at p15849
  rcases p16995 with hlit | hlit
  · exact (False.elim (p15849 hlit))
  · exact hlit
theorem n20538 (_v : Vars) (_q : Query _v)  : (e5042 _v) := by
  simp only [e3333, e3334, e3335, e3336, e3337, e5042] at *
  tauto
theorem n20539 (_v : Vars) (_q : Query _v)  : (e3333 _v) := by
  have p20538 := n20538 _v _q 
  have p14392 := n14392 _v _q 
  change (e3337 _v) ∨ (e3333 _v) at p20538
  change (¬ (e3337 _v)) at p14392
  rcases p20538 with hlit | hlit
  · exact (False.elim (p14392 hlit))
  · exact hlit
theorem n20540 (_v : Vars) (_q : Query _v)  : (e5043 _v) := by
  simp only [e3892, e3893, e3894, e3895, e3896, e5043] at *
  tauto
theorem n20541 (_v : Vars) (_q : Query _v)  : (e3892 _v) := by
  have p20540 := n20540 _v _q 
  have p14482 := n14482 _v _q 
  change (e3896 _v) ∨ (e3892 _v) at p20540
  change (¬ (e3896 _v)) at p14482
  rcases p20540 with hlit | hlit
  · exact (False.elim (p14482 hlit))
  · exact hlit
theorem n20542 (_v : Vars) (_q : Query _v)  : (e5044 _v) := by
  simp only [e3565, e3566, e3570, e3571, e3572, e5044] at *
  tauto
theorem n20543 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e3573 _v) := by
  have p14426 := n14426 _v _q 
  have p12917 := n12917 _v _q h251
  change (¬ (e2536 _v)) ∨ (¬ (e3572 _v)) at p14426
  rcases p14426 with hlit | hlit
  · exact (False.elim (hlit p12917))
  · exact hlit
theorem n20544 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e3565 _v) := by
  have p20542 := n20542 _v _q 
  have p20543 := n20543 _v _q h251
  change (e3572 _v) ∨ (e3565 _v) at p20542
  change (¬ (e3572 _v)) at p20543
  rcases p20542 with hlit | hlit
  · exact (False.elim (p20543 hlit))
  · exact hlit
theorem n20545 (_v : Vars) (_q : Query _v)  : (e5046 _v) := by
  simp only [e363, e364, e365, e366, e367, e5046] at *
  tauto
theorem n20546 (_v : Vars) (_q : Query _v)  : (e363 _v) := by
  have p20545 := n20545 _v _q 
  have p14194 := n14194 _v _q 
  change (e367 _v) ∨ (e363 _v) at p20545
  change (¬ (e367 _v)) at p14194
  rcases p20545 with hlit | hlit
  · exact (False.elim (p14194 hlit))
  · exact hlit
theorem n20547 (_v : Vars) (_q : Query _v)  : (e5047 _v) := by
  simp only [e3660, e3661, e3662, e3663, e3664, e5047] at *
  tauto
theorem n20548 (_v : Vars) (_q : Query _v)  : (e3660 _v) := by
  have p20547 := n20547 _v _q 
  have p14445 := n14445 _v _q 
  change (e3664 _v) ∨ (e3660 _v) at p20547
  change (¬ (e3664 _v)) at p14445
  rcases p20547 with hlit | hlit
  · exact (False.elim (p14445 hlit))
  · exact hlit
theorem n20549 (_v : Vars) (_q : Query _v)  : (e5048 _v) := by
  simp only [e4397, e4398, e4402, e4403, e4404, e5048] at *
  tauto
theorem n20550 (_v : Vars) (_q : Query _v)  : (e4397 _v) := by
  have p20549 := n20549 _v _q 
  have p20466 := n20466 _v _q 
  change (e4404 _v) ∨ (e4397 _v) at p20549
  change (¬ (e4404 _v)) at p20466
  rcases p20549 with hlit | hlit
  · exact (False.elim (p20466 hlit))
  · exact hlit
theorem n20551 (_v : Vars) (_q : Query _v)  : (e5050 _v) := by
  simp only [e3487, e3488, e3489, e3490, e3491, e5050] at *
  tauto
theorem n20552 (_v : Vars) (_q : Query _v)  : (e3489 _v) := by
  have p20551 := n20551 _v _q 
  have p14416 := n14416 _v _q 
  change (e3491 _v) ∨ (e3489 _v) at p20551
  change (¬ (e3491 _v)) at p14416
  rcases p20551 with hlit | hlit
  · exact (False.elim (p14416 hlit))
  · exact hlit
theorem n20553 (_v : Vars) (_q : Query _v)  : (e5051 _v) := by
  simp only [e3768, e3769, e3770, e3771, e3772, e5051] at *
  tauto
theorem n20554 (_v : Vars) (_q : Query _v)  : (e3770 _v) := by
  have p20553 := n20553 _v _q 
  have p14461 := n14461 _v _q 
  change (e3772 _v) ∨ (e3770 _v) at p20553
  change (¬ (e3772 _v)) at p14461
  rcases p20553 with hlit | hlit
  · exact (False.elim (p14461 hlit))
  · exact hlit
theorem n20555 (_v : Vars) (_q : Query _v)  : (e5052 _v) := by
  simp only [e3462, e3463, e3464, e3465, e3466, e5052] at *
  tauto
theorem n20556 (_v : Vars) (_q : Query _v)  : (e3464 _v) := by
  have p20555 := n20555 _v _q 
  have p14412 := n14412 _v _q 
  change (e3466 _v) ∨ (e3464 _v) at p20555
  change (¬ (e3466 _v)) at p14412
  rcases p20555 with hlit | hlit
  · exact (False.elim (p14412 hlit))
  · exact hlit
theorem n20557 (_v : Vars) (_q : Query _v)  : (e5053 _v) := by
  simp only [e3919, e3920, e3921, e3922, e3923, e5053] at *
  tauto
theorem n20558 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e3921 _v) := by
  have p20557 := n20557 _v _q 
  have p20460 := n20460 _v _q h251
  change (e3923 _v) ∨ (e3921 _v) at p20557
  change (¬ (e3923 _v)) at p20460
  rcases p20557 with hlit | hlit
  · exact (False.elim (p20460 hlit))
  · exact hlit
theorem n20559 (_v : Vars) (_q : Query _v)  : (e5054 _v) := by
  simp only [e102, e103, e104, e105, e106, e5054] at *
  tauto
end
end Assembly
