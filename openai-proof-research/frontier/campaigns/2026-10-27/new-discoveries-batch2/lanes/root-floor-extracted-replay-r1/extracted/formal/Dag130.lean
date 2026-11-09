import Dag129
import generated.th_lemma_9
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n15507 (_v : Vars) (_q : Query _v) (h7742 : (e7742 _v)) : (e7754 _v) := by
  have p14942 := n14942 _v _q 
  have p11462 := n11462 _v _q h7742
  simp only [e2132, e7742, e7747, e7749, e7751, e7752, e7753, e7754, e11001] at *
  tauto
theorem n15508 (_v : Vars) (_q : Query _v) (h7742 : (e7742 _v)) : (e7749 _v) := by
  have p14941 := n14941 _v _q 
  have p15507 := n15507 _v _q h7742
  simp only [e7747, e7749, e7751, e7752, e7753, e7754, e8446] at *
  tauto
theorem n15509 (_v : Vars) (_q : Query _v) (h7807 : (e7807 _v)) : (e2310 _v) := by
  have p8663 := n8663 _v _q 
  have p11350 := n11350 _v _q h7807
  exact FloorCertificate.node_15509 (e2 _v) (e9 _v) (e17 _v) (e110 _v) p8663 p11350
theorem n15510 (_v : Vars) (_q : Query _v) (h7807 : (e7807 _v)) : (e3278 _v) := by
  have p14378 := n14378 _v _q 
  have p15509 := n15509 _v _q h7807
  simp only [e2310, e3270, e3271, e3275, e3276, e3277, e3278, e6555, e6979] at *
  tauto
theorem n15511 (_v : Vars) (_q : Query _v) (h7807 : (e7807 _v)) : (e7754 _v) := by
  have p14942 := n14942 _v _q 
  have p12869 := n12869 _v _q h7807
  simp only [e2132, e7742, e7747, e7749, e7751, e7752, e7753, e7754, e11001] at *
  tauto
theorem n15512 (_v : Vars) (_q : Query _v) (h7807 : (e7807 _v)) : (e5093 _v) := by
  have p11350 := n11350 _v _q h7807
  have p5257 := n5257 _v _q 
  exact FloorCertificate.node_15512 (e2 _v) (e7 _v) (e9 _v) (e110 _v) p11350 p5257
theorem n15513 (_v : Vars) (_q : Query _v) (h7807 : (e7807 _v)) : (e5105 _v) := by
  have p15204 := n15204 _v _q 
  have p15512 := n15512 _v _q h7807
  simp only [e13, e5093, e5098, e5100, e5102, e5103, e5104, e5105, e8622] at *
  tauto
theorem n15514 (_v : Vars) (_q : Query _v) (h7807 : (e7807 _v)) : (e2254 _v) := by
  have p8663 := n8663 _v _q 
  have p5257 := n5257 _v _q 
  have p11350 := n11350 _v _q h7807
  exact FloorCertificate.node_15514 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e110 _v) p8663 p5257 p11350
theorem n15515 (_v : Vars) (_q : Query _v) (h7807 : (e7807 _v)) : (e4731 _v) := by
  have p14698 := n14698 _v _q 
  have p15514 := n15514 _v _q h7807
  simp only [e2254, e4723, e4724, e4728, e4729, e4730, e4731, e6531, e8220] at *
  tauto
theorem n15516 (_v : Vars) (_q : Query _v) (h2793 : (e2793 _v)) : (e4910 _v) := by
  have p14701 := n14701 _v _q 
  have p8426 := n8426 _v _q h2793
  simp only [e2793, e4902, e4903, e4907, e4908, e4909, e4910, e6784, e8381] at *
  tauto
theorem n15517 (_v : Vars) (_q : Query _v) (h2793 : (e2793 _v)) : (e4903 _v) := by
  have p14973 := n14973 _v _q 
  have p15516 := n15516 _v _q h2793
  simp only [e4902, e4903, e4907, e4908, e4909, e4910, e4961] at *
  tauto
theorem n15518 (_v : Vars) (_q : Query _v)  : (e4958 _v) := by
  simp only [e4723, e4724, e4728, e4729, e4730, e4958] at *
  tauto
theorem n15519 (_v : Vars) (_q : Query _v) (h2482 : (e2482 _v)) : (e2254 _v) := by
  have p11455 := n11455 _v _q 
  have p10888 := n10888 _v _q h2482
  simp only [e2254, e2482, e6636, e11454] at *
  tauto
theorem n15520 (_v : Vars) (_q : Query _v) (h2482 : (e2482 _v)) : (e4731 _v) := by
  have p14698 := n14698 _v _q 
  have p15519 := n15519 _v _q h2482
  simp only [e2254, e4723, e4724, e4728, e4729, e4730, e4731, e6531, e8220] at *
  tauto
theorem n15521 (_v : Vars) (_q : Query _v) (h2482 : (e2482 _v)) : (e4724 _v) := by
  have p15518 := n15518 _v _q 
  have p15520 := n15520 _v _q h2482
  simp only [e4723, e4724, e4728, e4729, e4730, e4731, e4958] at *
  tauto
theorem n15522 (_v : Vars) (_q : Query _v) (h7807 : (e7807 _v)) (h8038 : (e8038 _v)) : (e6772 _v) := by
  have p11350 := n11350 _v _q h7807
  have p8602 := n8602 _v _q h8038
  exact FloorCertificate.node_15522 (e2 _v) (e7 _v) (e9 _v) (e45 _v) (e110 _v) p11350 p8602
theorem n15523 (_v : Vars) (_q : Query _v) (h7807 : (e7807 _v)) (h8038 : (e8038 _v)) : (e7945 _v) := by
  have p15228 := n15228 _v _q 
  have p15522 := n15522 _v _q h7807 h8038
  simp only [e2787, e6772, e7932, e7935, e7942, e7943, e7944, e7945, e11111] at *
  tauto
theorem n15524 (_v : Vars) (_q : Query _v) (h8038 : (e8038 _v)) : (e6579 _v) := by
  have p11404 := n11404 _v _q 
  have p12868 := n12868 _v _q h8038
  simp only [e2371, e2592, e6579, e6672, e11403] at *
  tauto
theorem n15525 (_v : Vars) (_q : Query _v) (h8038 : (e8038 _v)) : (e7701 _v) := by
  have p15330 := n15330 _v _q 
  have p15524 := n15524 _v _q h8038
  simp only [e2371, e6579, e7688, e7691, e7698, e7699, e7700, e7701, e10977] at *
  tauto
theorem n15526 (_v : Vars) (_q : Query _v) (h8038 : (e8038 _v)) : (e7691 _v) := by
  have p15370 := n15370 _v _q 
  have p15525 := n15525 _v _q h8038
  simp only [e7688, e7691, e7698, e7699, e7700, e7701, e8497] at *
  tauto
theorem n15527 (_v : Vars) (_q : Query _v) (h7807 : (e7807 _v)) : (e7701 _v) := by
  have p15330 := n15330 _v _q 
  have p12870 := n12870 _v _q h7807
  simp only [e2371, e6579, e7688, e7691, e7698, e7699, e7700, e7701, e10977] at *
  tauto
theorem n15528 (_v : Vars) (_q : Query _v) (h7807 : (e7807 _v)) : (e7691 _v) := by
  have p15370 := n15370 _v _q 
  have p15527 := n15527 _v _q h7807
  simp only [e7688, e7691, e7698, e7699, e7700, e7701, e8497] at *
  tauto
theorem n15529 (_v : Vars) (_q : Query _v) (h7807 : (e7807 _v)) : (e5105 _v) := by
  have p15204 := n15204 _v _q 
  have p14109 := n14109 _v _q h7807
  simp only [e13, e5093, e5098, e5100, e5102, e5103, e5104, e5105, e8622] at *
  tauto
theorem n15530 (_v : Vars) (_q : Query _v) (h7807 : (e7807 _v)) : (e4731 _v) := by
  have p14698 := n14698 _v _q 
  have p14110 := n14110 _v _q h7807
  simp only [e2254, e4723, e4724, e4728, e4729, e4730, e4731, e6531, e8220] at *
  tauto
theorem n15531 (_v : Vars) (_q : Query _v) (h7807 : (e7807 _v)) : (e4724 _v) := by
  have p15518 := n15518 _v _q 
  have p15530 := n15530 _v _q h7807
  simp only [e4723, e4724, e4728, e4729, e4730, e4731, e4958] at *
  tauto
theorem n15532 (_v : Vars) (_q : Query _v) (h2364 : (e2364 _v)) : (e2310 _v) := by
  have p4016 := n4016 _v _q 
  have p8527 := n8527 _v _q h2364
  exact FloorCertificate.node_15532 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e110 _v) p4016 p8527
theorem n15533 (_v : Vars) (_q : Query _v) (h2364 : (e2364 _v)) : (e2254 _v) := by
  have p11361 := n11361 _v _q 
  have p15532 := n15532 _v _q h2364
  simp only [e2254, e2310, e6555, e11360] at *
  tauto
theorem n15534 (_v : Vars) (_q : Query _v) (h2364 : (e2364 _v)) : (e4731 _v) := by
  have p14698 := n14698 _v _q 
  have p15533 := n15533 _v _q h2364
  simp only [e2254, e4723, e4724, e4728, e4729, e4730, e4731, e6531, e8220] at *
  tauto
theorem n15535 (_v : Vars) (_q : Query _v) (h2303 : (e2303 _v)) (h2364 : (e2364 _v)) : (e2482 _v) := by
  have p8527 := n8527 _v _q h2364
  have p8448 := n8448 _v _q h2303
  have p10893 := n10893 _v _q 
  exact FloorCertificate.node_15535 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8527 p8448 p10893
theorem n15536 (_v : Vars) (_q : Query _v) (h2303 : (e2303 _v)) (h2364 : (e2364 _v)) : (e4405 _v) := by
  have p14702 := n14702 _v _q 
  have p15535 := n15535 _v _q h2303 h2364
  simp only [e2482, e4397, e4398, e4402, e4403, e4404, e4405, e6636, e7918] at *
  tauto
theorem n15537 (_v : Vars) (_q : Query _v) (h2303 : (e2303 _v)) (h2364 : (e2364 _v)) : (e4398 _v) := by
  have p14976 := n14976 _v _q 
  have p15536 := n15536 _v _q h2303 h2364
  simp only [e4397, e4398, e4402, e4403, e4404, e4405, e4962] at *
  tauto
theorem n15538 (_v : Vars) (_q : Query _v) (h2132 : (e2132 _v)) (h2364 : (e2364 _v)) : (e2536 _v) := by
  have p10893 := n10893 _v _q 
  have p11349 := n11349 _v _q h2132
  have p8527 := n8527 _v _q h2364
  have p5255 := n5255 _v _q 
  exact FloorCertificate.node_15538 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p10893 p11349 p8527 p5255
theorem n15539 (_v : Vars) (_q : Query _v) (h2132 : (e2132 _v)) (h2364 : (e2364 _v)) : (e3573 _v) := by
  have p14426 := n14426 _v _q 
  have p15538 := n15538 _v _q h2132 h2364
  simp only [e2536, e3565, e3566, e3570, e3571, e3572, e3573, e6656, e7176] at *
  tauto
theorem n15540 (_v : Vars) (_q : Query _v) (h2132 : (e2132 _v)) (h2364 : (e2364 _v)) : (e3566 _v) := by
  have p7179 := n7179 _v _q 
  have p15539 := n15539 _v _q h2132 h2364
  simp only [e3565, e3566, e3570, e3571, e3572, e3573, e3590] at *
  tauto
theorem n15541 (_v : Vars) (_q : Query _v) (h2132 : (e2132 _v)) (h2364 : (e2364 _v)) : (e2634 _v) := by
  have p8527 := n8527 _v _q h2364
  have p10893 := n10893 _v _q 
  have p11349 := n11349 _v _q h2132
  exact FloorCertificate.node_15541 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8527 p10893 p11349
theorem n15542 (_v : Vars) (_q : Query _v) (h2132 : (e2132 _v)) (h2364 : (e2364 _v)) : (e3180 _v) := by
  have p14361 := n14361 _v _q 
  have p15541 := n15541 _v _q h2132 h2364
  simp only [e2634, e3172, e3173, e3177, e3178, e3179, e3180, e6700, e6902] at *
  tauto
theorem n15543 (_v : Vars) (_q : Query _v) (h2132 : (e2132 _v)) (h2364 : (e2364 _v)) : (e3173 _v) := by
  have p6907 := n6907 _v _q 
  have p15542 := n15542 _v _q h2132 h2364
  simp only [e3172, e3173, e3177, e3178, e3179, e3180, e3190] at *
  tauto
theorem n15544 (_v : Vars) (_q : Query _v) (h2364 : (e2364 _v)) : (e2746 _v) := by
  have p8527 := n8527 _v _q h2364
  have p4016 := n4016 _v _q 
  have p10893 := n10893 _v _q 
  exact FloorCertificate.node_15544 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8527 p4016 p10893
theorem n15545 (_v : Vars) (_q : Query _v) (h2364 : (e2364 _v)) : (e3984 _v) := by
  have p14691 := n14691 _v _q 
  have p15544 := n15544 _v _q h2364
  simp only [e2746, e3976, e3977, e3981, e3982, e3983, e3984, e6758, e7456] at *
  tauto
theorem n15546 (_v : Vars) (_q : Query _v) (h2364 : (e2364 _v)) : (e3976 _v) := by
  have p14935 := n14935 _v _q 
  have p15545 := n15545 _v _q h2364
  simp only [e3976, e3977, e3981, e3982, e3983, e3984, e4954] at *
  tauto
theorem n15547 (_v : Vars) (_q : Query _v) (h2364 : (e2364 _v)) : (e3278 _v) := by
  have p14378 := n14378 _v _q 
  have p15532 := n15532 _v _q h2364
  simp only [e2310, e3270, e3271, e3275, e3276, e3277, e3278, e6555, e6979] at *
  tauto
theorem n15548 (_v : Vars) (_q : Query _v) (h2364 : (e2364 _v)) : (e3271 _v) := by
  have p6982 := n6982 _v _q 
  have p15547 := n15547 _v _q h2364
  simp only [e3270, e3271, e3275, e3276, e3277, e3278, e3288] at *
  tauto
theorem n15549 (_v : Vars) (_q : Query _v) (h2364 : (e2364 _v)) : (e2793 _v) := by
  have p8527 := n8527 _v _q h2364
  have p10893 := n10893 _v _q 
  exact FloorCertificate.node_15549 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8527 p10893
theorem n15550 (_v : Vars) (_q : Query _v) (h2364 : (e2364 _v)) : (e4910 _v) := by
  have p14701 := n14701 _v _q 
  have p15549 := n15549 _v _q h2364
  simp only [e2793, e4902, e4903, e4907, e4908, e4909, e4910, e6784, e8381] at *
  tauto
theorem n15551 (_v : Vars) (_q : Query _v) (h2364 : (e2364 _v)) : (e4903 _v) := by
  have p14973 := n14973 _v _q 
  have p15550 := n15550 _v _q h2364
  simp only [e4902, e4903, e4907, e4908, e4909, e4910, e4961] at *
  tauto
end
end Assembly
