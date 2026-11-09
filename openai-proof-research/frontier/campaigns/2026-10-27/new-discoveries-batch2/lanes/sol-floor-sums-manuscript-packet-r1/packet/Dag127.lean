import Dag126
import generated.th_lemma_8
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n15372 (_v : Vars) (_q : Query _v) (h7807 : (e7807 _v)) : (e7819 _v) := by
  have p14994 := n14994 _v _q 
  have p11350 := n11350 _v _q h7807
  simp only [e2303, e7807, e7812, e7814, e7816, e7817, e7818, e7819, e11046] at *
  tauto
theorem n15373 (_v : Vars) (_q : Query _v) (h7807 : (e7807 _v)) : (e7814 _v) := by
  have p15221 := n15221 _v _q 
  have p15372 := n15372 _v _q h7807
  simp only [e7812, e7814, e7816, e7817, e7818, e7819, e8456] at *
  tauto
theorem n15374 (_v : Vars) (_q : Query _v) (h4649 : (e4649 _v)) : (e4649 _v) := by
  exact h4649
theorem n15375 (_v : Vars) (_q : Query _v) (h4649 : (e4649 _v)) : (e8149 _v) := by
  have p15027 := n15027 _v _q 
  have p15374 := n15374 _v _q h4649
  simp only [e4648, e4649, e4650, e4651, e8149, e8150] at *
  tauto
theorem n15376 (_v : Vars) (_q : Query _v) (h4649 : (e4649 _v)) : (e2364 _v) := by
  have p14632 := n14632 _v _q 
  have p15375 := n15375 _v _q h4649
  simp only [e2364, e4648, e4649, e4650, e4651, e8149, e8157, e8160] at *
  tauto
theorem n15377 (_v : Vars) (_q : Query _v) (h4649 : (e4649 _v)) : (e4661 _v) := by
  have p14686 := n14686 _v _q 
  have p15376 := n15376 _v _q h4649
  simp only [e2364, e4653, e4654, e4658, e4659, e4660, e4661, e6583, e8163] at *
  tauto
theorem n15378 (_v : Vars) (_q : Query _v) (h6423 : (e6423 _v)) : (e8060 _v) := by
  have p14622 := n14622 _v _q 
  have p8452 := n8452 _v _q h6423
  simp only [e1995, e4562, e4563, e4564, e4565, e6423, e8052, e8060, e8063] at *
  tauto
theorem n15379 (_v : Vars) (_q : Query _v) (h6423 : (e6423 _v)) : (e4562 _v) := by
  have p15155 := n15155 _v _q 
  have p15378 := n15378 _v _q h6423
  simp only [e4562, e4563, e4564, e4565, e8052, e8053, e8060] at *
  tauto
theorem n15380 (_v : Vars) (_q : Query _v) (h6423 : (e6423 _v)) : (e7955 _v) := by
  have p14601 := n14601 _v _q 
  have p12853 := n12853 _v _q h6423
  simp only [e2061, e4434, e4435, e4436, e4437, e6454, e7947, e7955, e7958] at *
  tauto
theorem n15381 (_v : Vars) (_q : Query _v) (h6423 : (e6423 _v)) : (e7971 _v) := by
  have p14603 := n14603 _v _q 
  have p12854 := n12854 _v _q h6423
  simp only [e2125, e4475, e4477, e4480, e4481, e6480, e7970, e7971, e7974] at *
  tauto
theorem n15382 (_v : Vars) (_q : Query _v) (h6423 : (e6423 _v)) : (e4477 _v) := by
  have p14858 := n14858 _v _q 
  have p15381 := n15381 _v _q h6423
  simp only [e4475, e4477, e4480, e4481, e7970, e7971, e7980] at *
  tauto
theorem n15383 (_v : Vars) (_q : Query _v) (h6423 : (e6423 _v)) (h6555 : (e6555 _v)) : (e6676 _v) := by
  have p8663 := n8663 _v _q 
  have p5391 := n5391 _v _q 
  have p11362 := n11362 _v _q h6555
  have p8452 := n8452 _v _q h6423
  exact FloorCertificate.node_15383 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8663 p5391 p11362 p8452
theorem n15384 (_v : Vars) (_q : Query _v) (h6423 : (e6423 _v)) (h6555 : (e6555 _v)) : (e7830 _v) := by
  have p14579 := n14579 _v _q 
  have p15383 := n15383 _v _q h6423 h6555
  simp only [e2585, e4301, e4302, e4303, e4304, e6676, e7822, e7830, e7833] at *
  tauto
theorem n15385 (_v : Vars) (_q : Query _v) (h6423 : (e6423 _v)) (h6555 : (e6555 _v)) : (e6583 _v) := by
  have p8663 := n8663 _v _q 
  have p11362 := n11362 _v _q h6555
  have p8452 := n8452 _v _q h6423
  exact FloorCertificate.node_15385 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e110 _v) p8663 p11362 p8452
theorem n15386 (_v : Vars) (_q : Query _v) (h6423 : (e6423 _v)) (h6555 : (e6555 _v)) : (e8157 _v) := by
  have p14632 := n14632 _v _q 
  have p15385 := n15385 _v _q h6423 h6555
  simp only [e2364, e4648, e4649, e4650, e4651, e6583, e8149, e8157, e8160] at *
  tauto
theorem n15387 (_v : Vars) (_q : Query _v) (h5195 : (e5195 _v)) (h6423 : (e6423 _v)) : (e8310 _v) := by
  have p8452 := n8452 _v _q h6423
  have p8663 := n8663 _v _q 
  have p8549 := n8549 _v _q h5195
  exact FloorCertificate.node_15387 (e2 _v) (e7 _v) (e17 _v) (e45 _v) (e110 _v) p8452 p8663 p8549
theorem n15388 (_v : Vars) (_q : Query _v) (h5195 : (e5195 _v)) (h6423 : (e6423 _v)) : (e8322 _v) := by
  have p15218 := n15218 _v _q 
  have p15387 := n15387 _v _q h5195 h6423
  simp only [e2529, e8310, e8315, e8317, e8319, e8320, e8321, e8322, e11298] at *
  tauto
theorem n15389 (_v : Vars) (_q : Query _v) (h5195 : (e5195 _v)) (h6423 : (e6423 _v)) : (e7945 _v) := by
  have p15228 := n15228 _v _q 
  have p12855 := n12855 _v _q h5195 h6423
  simp only [e2787, e6772, e7932, e7935, e7942, e7943, e7944, e7945, e11111] at *
  tauto
theorem n15390 (_v : Vars) (_q : Query _v) (h5195 : (e5195 _v)) (h6423 : (e6423 _v)) : (e7935 _v) := by
  have p15266 := n15266 _v _q 
  have p15389 := n15389 _v _q h5195 h6423
  simp only [e7932, e7935, e7942, e7943, e7944, e7945, e8489] at *
  tauto
theorem n15391 (_v : Vars) (_q : Query _v) (h5195 : (e5195 _v)) : (e4661 _v) := by
  have p14686 := n14686 _v _q 
  have p14104 := n14104 _v _q h5195
  simp only [e2364, e4653, e4654, e4658, e4659, e4660, e4661, e6583, e8163] at *
  tauto
theorem n15392 (_v : Vars) (_q : Query _v) (h5195 : (e5195 _v)) : (e4653 _v) := by
  have p15168 := n15168 _v _q 
  have p15391 := n15391 _v _q h5195
  simp only [e4653, e4654, e4658, e4659, e4660, e4661, e4939] at *
  tauto
theorem n15393 (_v : Vars) (_q : Query _v) (h8310 : (e8310 _v)) : (e2536 _v) := by
  have p12781 := n12781 _v _q 
  have p11384 := n11384 _v _q h8310
  simp only [e2529, e2536, e8310, e12780] at *
  tauto
theorem n15394 (_v : Vars) (_q : Query _v) (h8310 : (e8310 _v)) : (e3573 _v) := by
  have p14426 := n14426 _v _q 
  have p15393 := n15393 _v _q h8310
  simp only [e2536, e3565, e3566, e3570, e3571, e3572, e3573, e6656, e7176] at *
  tauto
theorem n15395 (_v : Vars) (_q : Query _v) (h6571 : (e6571 _v)) : (e7630 _v) := by
  have p15152 := n15152 _v _q 
  have p12856 := n12856 _v _q h6571
  simp only [e2740, e6746, e7606, e7607, e7608, e7609, e7610, e7630, e10951] at *
  tauto
theorem n15396 (_v : Vars) (_q : Query _v) (h6571 : (e6571 _v)) : (e7606 _v) := by
  have p11418 := n11418 _v _q 
  have p15395 := n15395 _v _q h6571
  simp only [e7606, e7607, e7608, e7609, e7610, e7611, e7630] at *
  tauto
theorem n15397 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) (h8038 : (e8038 _v)) : (e6656 _v) := by
  have p5391 := n5391 _v _q 
  have p11473 := n11473 _v _q h6784
  have p8602 := n8602 _v _q h8038
  exact FloorCertificate.node_15397 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p5391 p11473 p8602
theorem n15398 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) (h8038 : (e8038 _v)) : (e7170 _v) := by
  have p14427 := n14427 _v _q 
  have p15397 := n15397 _v _q h6784 h8038
  simp only [e2536, e3583, e3585, e3588, e3589, e6656, e7169, e7170, e7173] at *
  tauto
theorem n15399 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) (h8038 : (e8038 _v)) : (e6700 _v) := by
  have p5255 := n5255 _v _q 
  have p11473 := n11473 _v _q h6784
  have p8602 := n8602 _v _q h8038
  have p5391 := n5391 _v _q 
  exact FloorCertificate.node_15399 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p5255 p11473 p8602 p5391
theorem n15400 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) (h8038 : (e8038 _v)) : (e6896 _v) := by
  have p14360 := n14360 _v _q 
  have p15399 := n15399 _v _q h6784 h8038
  simp only [e2634, e3167, e3168, e3169, e3170, e6700, e6888, e6896, e6899] at *
  tauto
theorem n15401 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) (h8038 : (e8038 _v)) : (e6776 _v) := by
  have p11473 := n11473 _v _q h6784
  have p8663 := n8663 _v _q 
  have p11375 := n11375 _v _q 
  have p8602 := n8602 _v _q h8038
  have p4016 := n4016 _v _q 
  have p5391 := n5391 _v _q 
  exact FloorCertificate.node_15401 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p11473 p8663 p11375 p8602 p4016 p5391
theorem n15402 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) (h8038 : (e8038 _v)) : (e7789 _v) := by
  have p14570 := n14570 _v _q 
  have p15401 := n15401 _v _q h6784 h8038
  simp only [e2781, e4258, e4259, e4260, e4261, e6776, e7781, e7789, e7792] at *
  tauto
theorem n15403 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e5108 _v) := by
  have p11473 := n11473 _v _q h6784
  have p11375 := n11375 _v _q 
  exact FloorCertificate.node_15403 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p11473 p11375
theorem n15404 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e5119 _v) := by
  have p14487 := n14487 _v _q 
  have p15403 := n15403 _v _q h6784
  simp only [e48, e70, e72, e75, e76, e5108, e5118, e5119, e5122] at *
  tauto
theorem n15405 (_v : Vars) (_q : Query _v) (h8038 : (e8038 _v)) : (e2377 _v) := by
  have p11375 := n11375 _v _q 
  have p5391 := n5391 _v _q 
  have p8602 := n8602 _v _q h8038
  have p8663 := n8663 _v _q 
  exact FloorCertificate.node_15405 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p11375 p5391 p8602 p8663
theorem n15406 (_v : Vars) (_q : Query _v) (h8038 : (e8038 _v)) : (e4755 _v) := by
  have p14687 := n14687 _v _q 
  have p15405 := n15405 _v _q h8038
  simp only [e2377, e4747, e4748, e4752, e4753, e4754, e4755, e6591, e8238] at *
  tauto
theorem n15407 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) (h8038 : (e8038 _v)) : (e6676 _v) := by
  have p8602 := n8602 _v _q h8038
  have p4016 := n4016 _v _q 
  have p5391 := n5391 _v _q 
  have p11473 := n11473 _v _q h6784
  exact FloorCertificate.node_15407 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8602 p4016 p5391 p11473
theorem n15408 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) (h8038 : (e8038 _v)) : (e7830 _v) := by
  have p14579 := n14579 _v _q 
  have p15407 := n15407 _v _q h6784 h8038
  simp only [e2585, e4301, e4302, e4303, e4304, e6676, e7822, e7830, e7833] at *
  tauto
theorem n15409 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) (h8038 : (e8038 _v)) : (e6575 _v) := by
  have p11473 := n11473 _v _q h6784
  have p4016 := n4016 _v _q 
  have p8602 := n8602 _v _q h8038
  have p8663 := n8663 _v _q 
  have p11375 := n11375 _v _q 
  have p5391 := n5391 _v _q 
  exact FloorCertificate.node_15409 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p11473 p4016 p8602 p8663 p11375 p5391
theorem n15410 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) (h8038 : (e8038 _v)) : (e7668 _v) := by
  have p14544 := n14544 _v _q 
  have p15409 := n15409 _v _q h6784 h8038
  simp only [e2351, e4156, e4157, e4158, e4159, e6575, e7660, e7668, e7671] at *
  tauto
theorem n15411 (_v : Vars) (_q : Query _v) (h6746 : (e6746 _v)) (h6784 : (e6784 _v)) : (e6423 _v) := by
  have p11458 := n11458 _v _q h6746
  have p11473 := n11473 _v _q h6784
  exact FloorCertificate.node_15411 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p11458 p11473
theorem n15412 (_v : Vars) (_q : Query _v) (h6746 : (e6746 _v)) (h6784 : (e6784 _v)) : (e8060 _v) := by
  have p14622 := n14622 _v _q 
  have p15411 := n15411 _v _q h6746 h6784
  simp only [e1995, e4562, e4563, e4564, e4565, e6423, e8052, e8060, e8063] at *
  tauto
theorem n15413 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) (h8038 : (e8038 _v)) : (e6480 _v) := by
  have p11473 := n11473 _v _q h6784
  have p5391 := n5391 _v _q 
  have p8602 := n8602 _v _q h8038
  have p4016 := n4016 _v _q 
  exact FloorCertificate.node_15413 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p11473 p5391 p8602 p4016
theorem n15414 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) (h8038 : (e8038 _v)) : (e7971 _v) := by
  have p14603 := n14603 _v _q 
  have p15413 := n15413 _v _q h6784 h8038
  simp only [e2125, e4475, e4477, e4480, e4481, e6480, e7970, e7971, e7974] at *
  tauto
theorem n15415 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) (h8038 : (e8038 _v)) : (e6555 _v) := by
  have p11473 := n11473 _v _q h6784
  have p8602 := n8602 _v _q h8038
  exact FloorCertificate.node_15415 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p11473 p8602
theorem n15416 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) (h8038 : (e8038 _v)) : (e6973 _v) := by
  have p14377 := n14377 _v _q 
  have p15415 := n15415 _v _q h6784 h8038
  simp only [e2310, e3265, e3266, e3267, e3268, e6555, e6965, e6973, e6976] at *
  tauto
end
end Assembly
