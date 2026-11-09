import Dag121
import generated.th_lemma_7
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n15147 (_v : Vars) (_q : Query _v) (h2722 : (e2722 _v)) : (e4885 _v) := by
  have p14697 := n14697 _v _q 
  have p8410 := n8410 _v _q h2722
  simp only [e2722, e4877, e4878, e4882, e4883, e4884, e4885, e6742, e8364] at *
  tauto
theorem n15148 (_v : Vars) (_q : Query _v) (h2722 : (e2722 _v)) : (e4877 _v) := by
  have p14955 := n14955 _v _q 
  have p15147 := n15147 _v _q h2722
  simp only [e4877, e4878, e4882, e4883, e4884, e4885, e4957] at *
  tauto
theorem n15149 (_v : Vars) (_q : Query _v) (h2722 : (e2722 _v)) : (e2351 _v) := by
  have p8410 := n8410 _v _q h2722
  have p5257 := n5257 _v _q 
  have p5391 := n5391 _v _q 
  have p5255 := n5255 _v _q 
  exact FloorCertificate.node_15149 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8410 p5257 p5391 p5255
theorem n15150 (_v : Vars) (_q : Query _v) (h2722 : (e2722 _v)) : (e4169 _v) := by
  have p14695 := n14695 _v _q 
  have p15149 := n15149 _v _q h2722
  simp only [e2351, e4161, e4162, e4166, e4167, e4168, e4169, e6575, e7674] at *
  tauto
theorem n15151 (_v : Vars) (_q : Query _v) (h2722 : (e2722 _v)) : (e4161 _v) := by
  have p14945 := n14945 _v _q 
  have p15150 := n15150 _v _q h2722
  simp only [e4161, e4162, e4166, e4167, e4168, e4169, e4955] at *
  tauto
theorem n15152 (_v : Vars) (_q : Query _v)  : (e10951 _v) := by
  have p14533 := n14533 _v _q 
  simp only [e2740, e4128, e4130, e4133, e4134, e6746, e7606, e7607, e7608, e7609, e7610, e7616, e7617, e7620, e7630, e7631, e10951, e10953, e10954, e10955] at *
  tauto
theorem n15153 (_v : Vars) (_q : Query _v) (h7607 : (e7607 _v)) : (e2740 _v) := by
  have p15152 := n15152 _v _q 
  have p11420 := n11420 _v _q h7607
  simp only [e2740, e7606, e7607, e7608, e7609, e7610, e7630, e10951] at *
  tauto
theorem n15154 (_v : Vars) (_q : Query _v) (h4128 : (e4128 _v)) (h7607 : (e7607 _v)) : (e7489 _v) := by
  have p11419 := n11419 _v _q h7607
  have p4974 := n4974 _v _q h4128
  have p15153 := n15153 _v _q h7607
  exact FloorCertificate.node_15154 (e2 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) (e2907 _v) p11419 p4974 p15153
theorem n15155 (_v : Vars) (_q : Query _v)  : (e8053 _v) := by
  simp only [e4562, e4563, e4564, e4565, e8052, e8053] at *
  tauto
theorem n15156 (_v : Vars) (_q : Query _v) (h4563 : (e4563 _v)) : (e4563 _v) := by
  exact h4563
theorem n15157 (_v : Vars) (_q : Query _v) (h4563 : (e4563 _v)) : (e8052 _v) := by
  have p15155 := n15155 _v _q 
  have p15156 := n15156 _v _q h4563
  simp only [e4562, e4563, e4564, e4565, e8052, e8053] at *
  tauto
theorem n15158 (_v : Vars) (_q : Query _v) (h4563 : (e4563 _v)) : (e1995 _v) := by
  have p14622 := n14622 _v _q 
  have p15157 := n15157 _v _q h4563
  simp only [e1995, e4562, e4563, e4564, e4565, e8052, e8060, e8063] at *
  tauto
theorem n15159 (_v : Vars) (_q : Query _v) (h2132 : (e2132 _v)) (h2364 : (e2364 _v)) : (e2634 _v) := by
  have p11349 := n11349 _v _q h2132
  have p10893 := n10893 _v _q 
  have p8527 := n8527 _v _q h2364
  exact FloorCertificate.node_15159 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p11349 p10893 p8527
theorem n15160 (_v : Vars) (_q : Query _v) (h2132 : (e2132 _v)) (h2364 : (e2364 _v)) : (e3180 _v) := by
  have p14361 := n14361 _v _q 
  have p15159 := n15159 _v _q h2132 h2364
  simp only [e2634, e3172, e3173, e3177, e3178, e3179, e3180, e6700, e6902] at *
  tauto
theorem n15161 (_v : Vars) (_q : Query _v) (h2132 : (e2132 _v)) (h2364 : (e2364 _v)) : (e3173 _v) := by
  have p6907 := n6907 _v _q 
  have p15160 := n15160 _v _q h2132 h2364
  simp only [e3172, e3173, e3177, e3178, e3179, e3180, e3190] at *
  tauto
theorem n15162 (_v : Vars) (_q : Query _v) (h2132 : (e2132 _v)) (h2364 : (e2364 _v)) : (e2536 _v) := by
  have p11349 := n11349 _v _q h2132
  have p10893 := n10893 _v _q 
  have p5255 := n5255 _v _q 
  have p8527 := n8527 _v _q h2364
  exact FloorCertificate.node_15162 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p11349 p10893 p5255 p8527
theorem n15163 (_v : Vars) (_q : Query _v) (h2132 : (e2132 _v)) (h2364 : (e2364 _v)) : (e3573 _v) := by
  have p14426 := n14426 _v _q 
  have p15162 := n15162 _v _q h2132 h2364
  simp only [e2536, e3565, e3566, e3570, e3571, e3572, e3573, e6656, e7176] at *
  tauto
theorem n15164 (_v : Vars) (_q : Query _v) (h2132 : (e2132 _v)) (h2364 : (e2364 _v)) : (e3566 _v) := by
  have p7179 := n7179 _v _q 
  have p15163 := n15163 _v _q h2132 h2364
  simp only [e3565, e3566, e3570, e3571, e3572, e3573, e3590] at *
  tauto
theorem n15165 (_v : Vars) (_q : Query _v) (h2364 : (e2364 _v)) : (e2793 _v) := by
  have p10893 := n10893 _v _q 
  have p8527 := n8527 _v _q h2364
  exact FloorCertificate.node_15165 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p10893 p8527
theorem n15166 (_v : Vars) (_q : Query _v) (h2364 : (e2364 _v)) : (e4910 _v) := by
  have p14701 := n14701 _v _q 
  have p15165 := n15165 _v _q h2364
  simp only [e2793, e4902, e4903, e4907, e4908, e4909, e4910, e6784, e8381] at *
  tauto
theorem n15167 (_v : Vars) (_q : Query _v) (h2364 : (e2364 _v)) : (e4903 _v) := by
  have p14973 := n14973 _v _q 
  have p15166 := n15166 _v _q h2364
  simp only [e4902, e4903, e4907, e4908, e4909, e4910, e4961] at *
  tauto
theorem n15168 (_v : Vars) (_q : Query _v)  : (e4939 _v) := by
  simp only [e4653, e4654, e4658, e4659, e4660, e4939] at *
  tauto
theorem n15169 (_v : Vars) (_q : Query _v) (h2364 : (e2364 _v)) : (e4661 _v) := by
  have p14686 := n14686 _v _q 
  have p8527 := n8527 _v _q h2364
  simp only [e2364, e4653, e4654, e4658, e4659, e4660, e4661, e6583, e8163] at *
  tauto
theorem n15170 (_v : Vars) (_q : Query _v) (h2364 : (e2364 _v)) : (e4653 _v) := by
  have p15168 := n15168 _v _q 
  have p15169 := n15169 _v _q h2364
  simp only [e4653, e4654, e4658, e4659, e4660, e4661, e4939] at *
  tauto
theorem n15171 (_v : Vars) (_q : Query _v) (h2364 : (e2364 _v)) (h2475 : (e2475 _v)) : (e2310 _v) := by
  have p8527 := n8527 _v _q h2364
  have p10893 := n10893 _v _q 
  have p8457 := n8457 _v _q h2475
  exact FloorCertificate.node_15171 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8527 p10893 p8457
theorem n15172 (_v : Vars) (_q : Query _v) (h2364 : (e2364 _v)) (h2475 : (e2475 _v)) : (e3278 _v) := by
  have p14378 := n14378 _v _q 
  have p15171 := n15171 _v _q h2364 h2475
  simp only [e2310, e3270, e3271, e3275, e3276, e3277, e3278, e6555, e6979] at *
  tauto
theorem n15173 (_v : Vars) (_q : Query _v) (h2364 : (e2364 _v)) (h2475 : (e2475 _v)) : (e3271 _v) := by
  have p6982 := n6982 _v _q 
  have p15172 := n15172 _v _q h2364 h2475
  simp only [e3270, e3271, e3275, e3276, e3277, e3278, e3288] at *
  tauto
theorem n15174 (_v : Vars) (_q : Query _v) (h2364 : (e2364 _v)) (h2475 : (e2475 _v)) : (e2746 _v) := by
  have p10893 := n10893 _v _q 
  have p8527 := n8527 _v _q h2364
  have p8457 := n8457 _v _q h2475
  exact FloorCertificate.node_15174 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p10893 p8527 p8457
theorem n15175 (_v : Vars) (_q : Query _v) (h2364 : (e2364 _v)) (h2475 : (e2475 _v)) : (e3984 _v) := by
  have p14691 := n14691 _v _q 
  have p15174 := n15174 _v _q h2364 h2475
  simp only [e2746, e3976, e3977, e3981, e3982, e3983, e3984, e6758, e7456] at *
  tauto
theorem n15176 (_v : Vars) (_q : Query _v) (h2364 : (e2364 _v)) (h2475 : (e2475 _v)) : (e3976 _v) := by
  have p14935 := n14935 _v _q 
  have p15175 := n15175 _v _q h2364 h2475
  simp only [e3976, e3977, e3981, e3982, e3983, e3984, e4954] at *
  tauto
theorem n15177 (_v : Vars) (_q : Query _v) (h2310 : (e2310 _v)) : (e3278 _v) := by
  have p14378 := n14378 _v _q 
  have p11059 := n11059 _v _q h2310
  simp only [e2310, e3270, e3271, e3275, e3276, e3277, e3278, e6555, e6979] at *
  tauto
theorem n15178 (_v : Vars) (_q : Query _v) (h2310 : (e2310 _v)) : (e3271 _v) := by
  have p6982 := n6982 _v _q 
  have p15177 := n15177 _v _q h2310
  simp only [e3270, e3271, e3275, e3276, e3277, e3278, e3288] at *
  tauto
theorem n15179 (_v : Vars) (_q : Query _v) (h4572 : (e4572 _v)) : (e6423 _v) := by
  have p14696 := n14696 _v _q 
  have p8487 := n8487 _v _q h4572
  simp only [e1995, e4567, e4568, e4572, e4573, e4574, e4575, e6423, e8066] at *
  tauto
theorem n15180 (_v : Vars) (_q : Query _v) (h4572 : (e4572 _v)) : (e8060 _v) := by
  have p14622 := n14622 _v _q 
  have p15179 := n15179 _v _q h4572
  simp only [e1995, e4562, e4563, e4564, e4565, e6423, e8052, e8060, e8063] at *
  tauto
theorem n15181 (_v : Vars) (_q : Query _v) (h4572 : (e4572 _v)) : (e4562 _v) := by
  have p15155 := n15155 _v _q 
  have p15180 := n15180 _v _q h4572
  simp only [e4562, e4563, e4564, e4565, e8052, e8053, e8060] at *
  tauto
theorem n15182 (_v : Vars) (_q : Query _v) (h2536 : (e2536 _v)) : (e3573 _v) := by
  have p14426 := n14426 _v _q 
  have p11132 := n11132 _v _q h2536
  simp only [e2536, e3565, e3566, e3570, e3571, e3572, e3573, e6656, e7176] at *
  tauto
theorem n15183 (_v : Vars) (_q : Query _v) (h2536 : (e2536 _v)) : (e3566 _v) := by
  have p7179 := n7179 _v _q 
  have p15182 := n15182 _v _q h2536
  simp only [e3565, e3566, e3570, e3571, e3572, e3573, e3590] at *
  tauto
theorem n15184 (_v : Vars) (_q : Query _v) (h4572 : (e4572 _v)) : (e6454 _v) := by
  have p11412 := n11412 _v _q 
  have p15179 := n15179 _v _q h4572
  simp only [e1995, e2061, e6423, e6454, e11411] at *
  tauto
theorem n15185 (_v : Vars) (_q : Query _v) (h4572 : (e4572 _v)) : (e7955 _v) := by
  have p14601 := n14601 _v _q 
  have p15184 := n15184 _v _q h4572
  simp only [e2061, e4434, e4435, e4436, e4437, e6454, e7947, e7955, e7958] at *
  tauto
theorem n15186 (_v : Vars) (_q : Query _v) (h4572 : (e4572 _v)) : (e6480 _v) := by
  have p8478 := n8478 _v _q 
  have p15184 := n15184 _v _q h4572
  simp only [e2061, e2125, e6454, e6480, e8477] at *
  tauto
theorem n15187 (_v : Vars) (_q : Query _v) (h8038 : (e8038 _v)) : (e2139 _v) := by
  have p8602 := n8602 _v _q h8038
  have p5391 := n5391 _v _q 
  have p8663 := n8663 _v _q 
  have p5255 := n5255 _v _q 
  exact FloorCertificate.node_15187 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8602 p5391 p8663 p5255
theorem n15188 (_v : Vars) (_q : Query _v) (h8038 : (e8038 _v)) : (e3862 _v) := by
  have p14472 := n14472 _v _q 
  have p15187 := n15187 _v _q h8038
  simp only [e2139, e3854, e3855, e3859, e3860, e3861, e3862, e6486, e7364] at *
  tauto
theorem n15189 (_v : Vars) (_q : Query _v) (h6746 : (e6746 _v)) : (e7630 _v) := by
  have p15152 := n15152 _v _q 
  have p11458 := n11458 _v _q h6746
  simp only [e2740, e6746, e7606, e7607, e7608, e7609, e7610, e7630, e10951] at *
  tauto
theorem n15190 (_v : Vars) (_q : Query _v) (h6746 : (e6746 _v)) : (e7606 _v) := by
  have p11418 := n11418 _v _q 
  have p15189 := n15189 _v _q h6746
  simp only [e7606, e7607, e7608, e7609, e7610, e7611, e7630] at *
  tauto
theorem n15191 (_v : Vars) (_q : Query _v) (h8038 : (e8038 _v)) : (e7742 _v) := by
  have p8602 := n8602 _v _q h8038
  have p5391 := n5391 _v _q 
  have p5255 := n5255 _v _q 
  exact FloorCertificate.node_15191 (e2 _v) (e7 _v) (e9 _v) (e45 _v) (e110 _v) p8602 p5391 p5255
end
end Assembly
