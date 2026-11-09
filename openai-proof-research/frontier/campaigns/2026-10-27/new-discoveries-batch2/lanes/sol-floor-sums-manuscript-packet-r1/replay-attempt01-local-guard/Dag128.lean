import Dag127
import generated.th_lemma_9
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n15417 (_v : Vars) (_q : Query _v) (h8038 : (e8038 _v)) : (e2697 _v) := by
  have p4016 := n4016 _v _q 
  have p5391 := n5391 _v _q 
  have p8663 := n8663 _v _q 
  have p8602 := n8602 _v _q h8038
  exact FloorCertificate.node_15417 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) p4016 p5391 p8663 p8602
theorem n15418 (_v : Vars) (_q : Query _v) (h8038 : (e8038 _v)) : (e4499 _v) := by
  have p14700 := n14700 _v _q 
  have p15417 := n15417 _v _q h8038
  simp only [e2697, e4491, e4492, e4496, e4497, e4498, e4499, e6732, e7998] at *
  tauto
theorem n15419 (_v : Vars) (_q : Query _v) (h8038 : (e8038 _v)) : (e6579 _v) := by
  have p8602 := n8602 _v _q h8038
  have p11375 := n11375 _v _q 
  have p5391 := n5391 _v _q 
  exact FloorCertificate.node_15419 (e2 _v) (e7 _v) (e9 _v) (e45 _v) (e110 _v) p8602 p11375 p5391
theorem n15420 (_v : Vars) (_q : Query _v) (h8038 : (e8038 _v)) : (e7701 _v) := by
  have p15330 := n15330 _v _q 
  have p15419 := n15419 _v _q h8038
  simp only [e2371, e6579, e7688, e7691, e7698, e7699, e7700, e7701, e10977] at *
  tauto
theorem n15421 (_v : Vars) (_q : Query _v) (h8038 : (e8038 _v)) : (e2598 _v) := by
  have p11375 := n11375 _v _q 
  have p8602 := n8602 _v _q h8038
  have p8663 := n8663 _v _q 
  exact FloorCertificate.node_15421 (e2 _v) (e7 _v) (e17 _v) (e45 _v) (e110 _v) p11375 p8602 p8663
theorem n15422 (_v : Vars) (_q : Query _v) (h8038 : (e8038 _v)) : (e4067 _v) := by
  have p14703 := n14703 _v _q 
  have p15421 := n15421 _v _q h8038
  simp only [e2598, e4059, e4060, e4064, e4065, e4066, e4067, e6684, e7560] at *
  tauto
theorem n15423 (_v : Vars) (_q : Query _v) (h8038 : (e8038 _v)) : (e6672 _v) := by
  have p8602 := n8602 _v _q h8038
  have p11375 := n11375 _v _q 
  exact FloorCertificate.node_15423 (e2 _v) (e7 _v) (e45 _v) (e110 _v) p8602 p11375
theorem n15424 (_v : Vars) (_q : Query _v) (h8038 : (e8038 _v)) : (e8348 _v) := by
  have p15312 := n15312 _v _q 
  have p15423 := n15423 _v _q h8038
  simp only [e2592, e6672, e8335, e8338, e8345, e8346, e8347, e8348, e11307] at *
  tauto
theorem n15425 (_v : Vars) (_q : Query _v) (h8038 : (e8038 _v)) : (e6724 _v) := by
  have p5391 := n5391 _v _q 
  have p8602 := n8602 _v _q h8038
  have p4016 := n4016 _v _q 
  exact FloorCertificate.node_15425 (e2 _v) (e7 _v) (e9 _v) (e45 _v) p5391 p8602 p4016
theorem n15426 (_v : Vars) (_q : Query _v) (h8038 : (e8038 _v)) : (e7517 _v) := by
  have p15196 := n15196 _v _q 
  have p15425 := n15425 _v _q h8038
  simp only [e2691, e6724, e7493, e7494, e7495, e7496, e7497, e7517, e10904] at *
  tauto
theorem n15427 (_v : Vars) (_q : Query _v) (h6746 : (e6746 _v)) : (e2746 _v) := by
  have p8663 := n8663 _v _q 
  have p11458 := n11458 _v _q h6746
  exact FloorCertificate.node_15427 (e2 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8663 p11458
theorem n15428 (_v : Vars) (_q : Query _v) (h6746 : (e6746 _v)) : (e3984 _v) := by
  have p14691 := n14691 _v _q 
  have p15427 := n15427 _v _q h6746
  simp only [e2746, e3976, e3977, e3981, e3982, e3983, e3984, e6758, e7456] at *
  tauto
theorem n15429 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) (h8038 : (e8038 _v)) : (e6583 _v) := by
  have p8602 := n8602 _v _q h8038
  have p11473 := n11473 _v _q h6784
  have p4016 := n4016 _v _q 
  exact FloorCertificate.node_15429 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8602 p11473 p4016
theorem n15430 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) (h8038 : (e8038 _v)) : (e8157 _v) := by
  have p14632 := n14632 _v _q 
  have p15429 := n15429 _v _q h6784 h8038
  simp only [e2364, e4648, e4649, e4650, e4651, e6583, e8149, e8157, e8160] at *
  tauto
theorem n15431 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) (h8038 : (e8038 _v)) : (e6525 _v) := by
  have p11473 := n11473 _v _q h6784
  have p8602 := n8602 _v _q h8038
  have p11375 := n11375 _v _q 
  have p4016 := n4016 _v _q 
  exact FloorCertificate.node_15431 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p11473 p8602 p11375 p4016
theorem n15432 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) (h8038 : (e8038 _v)) : (e8174 _v) := by
  have p14634 := n14634 _v _q 
  have p15431 := n15431 _v _q h6784 h8038
  simp only [e2242, e4673, e4674, e4675, e4676, e6525, e8166, e8174, e8177] at *
  tauto
theorem n15433 (_v : Vars) (_q : Query _v) (h8038 : (e8038 _v)) : (e2805 _v) := by
  have p5391 := n5391 _v _q 
  have p8663 := n8663 _v _q 
  have p11375 := n11375 _v _q 
  have p8602 := n8602 _v _q h8038
  have p4016 := n4016 _v _q 
  exact FloorCertificate.node_15433 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p5391 p8663 p11375 p8602 p4016
theorem n15434 (_v : Vars) (_q : Query _v) (h8038 : (e8038 _v)) : (e3954 _v) := by
  have p14486 := n14486 _v _q 
  have p15433 := n15433 _v _q h8038
  simp only [e2805, e3944, e3945, e3946, e3947, e3948, e3954, e6792, e7438] at *
  tauto
theorem n15435 (_v : Vars) (_q : Query _v)  : (e11332 _v) := by
  have p14683 := n14683 _v _q 
  simp only [e2799, e4922, e4923, e4924, e4925, e6780, e8384, e8390, e8393, e8395, e8398, e8405, e8406, e8407, e8408, e8409, e11332, e11334, e11335, e11336] at *
  tauto
theorem n15436 (_v : Vars) (_q : Query _v) (h8038 : (e8038 _v)) : (e8408 _v) := by
  have p15435 := n15435 _v _q 
  have p12858 := n12858 _v _q h8038
  simp only [e2799, e6780, e8395, e8398, e8405, e8406, e8407, e8408, e11332] at *
  tauto
theorem n15437 (_v : Vars) (_q : Query _v) (h8038 : (e8038 _v)) : (e8398 _v) := by
  have p11470 := n11470 _v _q 
  have p15436 := n15436 _v _q h8038
  simp only [e8395, e8398, e8405, e8406, e8407, e8408, e8462] at *
  tauto
theorem n15438 (_v : Vars) (_q : Query _v) (h8038 : (e8038 _v)) : (e7517 _v) := by
  have p15196 := n15196 _v _q 
  have p12859 := n12859 _v _q h8038
  simp only [e2691, e6724, e7493, e7494, e7495, e7496, e7497, e7517, e10904] at *
  tauto
theorem n15439 (_v : Vars) (_q : Query _v) (h8038 : (e8038 _v)) : (e7493 _v) := by
  have p15195 := n15195 _v _q 
  have p15438 := n15438 _v _q h8038
  simp only [e7493, e7494, e7495, e7496, e7497, e7498, e7517] at *
  tauto
theorem n15440 (_v : Vars) (_q : Query _v) (h5093 : (e5093 _v)) : (e6780 _v) := by
  have p11449 := n11449 _v _q 
  have p11440 := n11440 _v _q h5093
  simp only [e13, e2799, e5093, e6780, e11448] at *
  tauto
theorem n15441 (_v : Vars) (_q : Query _v) (h5093 : (e5093 _v)) : (e8408 _v) := by
  have p15435 := n15435 _v _q 
  have p15440 := n15440 _v _q h5093
  simp only [e2799, e6780, e8395, e8398, e8405, e8406, e8407, e8408, e11332] at *
  tauto
theorem n15442 (_v : Vars) (_q : Query _v) (h6636 : (e6636 _v)) : (e7912 _v) := by
  have p14591 := n14591 _v _q 
  have p11031 := n11031 _v _q h6636
  simp only [e2482, e4392, e4393, e4394, e4395, e6636, e7904, e7912, e7915] at *
  tauto
theorem n15443 (_v : Vars) (_q : Query _v) (h6636 : (e6636 _v)) : (e4394 _v) := by
  have p14852 := n14852 _v _q 
  have p15442 := n15442 _v _q h6636
  simp only [e4392, e4393, e4394, e4395, e7904, e7905, e7912] at *
  tauto
theorem n15444 (_v : Vars) (_q : Query _v) (h5093 : (e5093 _v)) : (e7742 _v) := by
  have p5255 := n5255 _v _q 
  have p11440 := n11440 _v _q h5093
  exact FloorCertificate.node_15444 (e2 _v) (e7 _v) (e9 _v) (e110 _v) p5255 p11440
theorem n15445 (_v : Vars) (_q : Query _v) (h5093 : (e5093 _v)) : (e7754 _v) := by
  have p14942 := n14942 _v _q 
  have p15444 := n15444 _v _q h5093
  simp only [e2132, e7742, e7747, e7749, e7751, e7752, e7753, e7754, e11001] at *
  tauto
theorem n15446 (_v : Vars) (_q : Query _v) (h5093 : (e5093 _v)) : (e7742 _v) := by
  have p11440 := n11440 _v _q h5093
  have p5255 := n5255 _v _q 
  exact FloorCertificate.node_15446 (e2 _v) (e7 _v) (e9 _v) (e110 _v) p11440 p5255
theorem n15447 (_v : Vars) (_q : Query _v) (h5093 : (e5093 _v)) : (e7754 _v) := by
  have p14942 := n14942 _v _q 
  have p15446 := n15446 _v _q h5093
  simp only [e2132, e7742, e7747, e7749, e7751, e7752, e7753, e7754, e11001] at *
  tauto
theorem n15448 (_v : Vars) (_q : Query _v) (h2536 : (e2536 _v)) : (e2310 _v) := by
  have p11439 := n11439 _v _q 
  have p11132 := n11132 _v _q h2536
  simp only [e2310, e2536, e6656, e11438] at *
  tauto
theorem n15449 (_v : Vars) (_q : Query _v) (h2536 : (e2536 _v)) : (e3278 _v) := by
  have p14378 := n14378 _v _q 
  have p15448 := n15448 _v _q h2536
  simp only [e2310, e3270, e3271, e3275, e3276, e3277, e3278, e6555, e6979] at *
  tauto
theorem n15450 (_v : Vars) (_q : Query _v) (h2536 : (e2536 _v)) : (e3271 _v) := by
  have p6982 := n6982 _v _q 
  have p15449 := n15449 _v _q h2536
  simp only [e3270, e3271, e3275, e3276, e3277, e3278, e3288] at *
  tauto
theorem n15451 (_v : Vars) (_q : Query _v) (h2536 : (e2536 _v)) (h5093 : (e5093 _v)) : (e2793 _v) := by
  have p11132 := n11132 _v _q h2536
  have p11440 := n11440 _v _q h5093
  exact FloorCertificate.node_15451 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p11132 p11440
theorem n15452 (_v : Vars) (_q : Query _v) (h2536 : (e2536 _v)) (h5093 : (e5093 _v)) : (e4910 _v) := by
  have p14701 := n14701 _v _q 
  have p15451 := n15451 _v _q h2536 h5093
  simp only [e2793, e4902, e4903, e4907, e4908, e4909, e4910, e6784, e8381] at *
  tauto
theorem n15453 (_v : Vars) (_q : Query _v) (h5093 : (e5093 _v)) : (e2254 _v) := by
  have p8663 := n8663 _v _q 
  have p11440 := n11440 _v _q h5093
  exact FloorCertificate.node_15453 (e2 _v) (e7 _v) (e9 _v) (e17 _v) p8663 p11440
theorem n15454 (_v : Vars) (_q : Query _v) (h5093 : (e5093 _v)) : (e4731 _v) := by
  have p14698 := n14698 _v _q 
  have p15453 := n15453 _v _q h5093
  simp only [e2254, e4723, e4724, e4728, e4729, e4730, e4731, e6531, e8220] at *
  tauto
theorem n15455 (_v : Vars) (_q : Query _v) (h2536 : (e2536 _v)) : (e2482 _v) := by
  have p11135 := n11135 _v _q 
  have p11132 := n11132 _v _q h2536
  simp only [e2482, e2536, e6656, e11134] at *
  tauto
theorem n15456 (_v : Vars) (_q : Query _v) (h2536 : (e2536 _v)) : (e4405 _v) := by
  have p14702 := n14702 _v _q 
  have p15455 := n15455 _v _q h2536
  simp only [e2482, e4397, e4398, e4402, e4403, e4404, e4405, e6636, e7918] at *
  tauto
theorem n15457 (_v : Vars) (_q : Query _v) (h2536 : (e2536 _v)) : (e4398 _v) := by
  have p14976 := n14976 _v _q 
  have p15456 := n15456 _v _q h2536
  simp only [e4397, e4398, e4402, e4403, e4404, e4405, e4962] at *
  tauto
theorem n15458 (_v : Vars) (_q : Query _v) (h6555 : (e6555 _v)) : (e6700 _v) := by
  have p11365 := n11365 _v _q 
  have p11362 := n11362 _v _q h6555
  simp only [e2310, e2634, e6555, e6700, e11364] at *
  tauto
theorem n15459 (_v : Vars) (_q : Query _v) (h6555 : (e6555 _v)) : (e6896 _v) := by
  have p14360 := n14360 _v _q 
  have p15458 := n15458 _v _q h6555
  simp only [e2634, e3167, e3168, e3169, e3170, e6700, e6888, e6896, e6899] at *
  tauto
theorem n15460 (_v : Vars) (_q : Query _v) (h2475 : (e2475 _v)) (h6555 : (e6555 _v)) : (e6784 _v) := by
  have p11362 := n11362 _v _q h6555
  have p8457 := n8457 _v _q h2475
  exact FloorCertificate.node_15460 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p11362 p8457
theorem n15461 (_v : Vars) (_q : Query _v) (h2475 : (e2475 _v)) (h6555 : (e6555 _v)) : (e8375 _v) := by
  have p14675 := n14675 _v _q 
  have p15460 := n15460 _v _q h2475 h6555
  simp only [e2793, e4897, e4898, e4899, e4900, e6784, e8367, e8375, e8378] at *
  tauto
end
end Assembly
