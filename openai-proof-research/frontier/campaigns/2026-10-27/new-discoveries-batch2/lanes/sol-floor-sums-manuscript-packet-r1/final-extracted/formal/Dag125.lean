import Dag124
import generated.th_lemma_7
import generated.th_lemma_8
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n15282 (_v : Vars) (_q : Query _v) (h2125 : (e2125 _v)) : (e2310 _v) := by
  have p8475 := n8475 _v _q h2125
  have p10896 := n10896 _v _q 
  have p4016 := n4016 _v _q 
  exact FloorCertificate.node_15282 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e110 _v) p8475 p10896 p4016
theorem n15283 (_v : Vars) (_q : Query _v) (h2125 : (e2125 _v)) : (e3278 _v) := by
  have p14378 := n14378 _v _q 
  have p15282 := n15282 _v _q h2125
  simp only [e2310, e3270, e3271, e3275, e3276, e3277, e3278, e6555, e6979] at *
  tauto
theorem n15284 (_v : Vars) (_q : Query _v) (h2125 : (e2125 _v)) : (e3271 _v) := by
  have p6982 := n6982 _v _q 
  have p15283 := n15283 _v _q h2125
  simp only [e3270, e3271, e3275, e3276, e3277, e3278, e3288] at *
  tauto
theorem n15285 (_v : Vars) (_q : Query _v) (h2125 : (e2125 _v)) : (e2364 _v) := by
  have p8475 := n8475 _v _q h2125
  have p10896 := n10896 _v _q 
  exact FloorCertificate.node_15285 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e110 _v) p8475 p10896
theorem n15286 (_v : Vars) (_q : Query _v) (h2125 : (e2125 _v)) : (e4661 _v) := by
  have p14686 := n14686 _v _q 
  have p15285 := n15285 _v _q h2125
  simp only [e2364, e4653, e4654, e4658, e4659, e4660, e4661, e6583, e8163] at *
  tauto
theorem n15287 (_v : Vars) (_q : Query _v) (h2125 : (e2125 _v)) : (e4653 _v) := by
  have p15168 := n15168 _v _q 
  have p15286 := n15286 _v _q h2125
  simp only [e4653, e4654, e4658, e4659, e4660, e4661, e4939] at *
  tauto
theorem n15288 (_v : Vars) (_q : Query _v) (h2125 : (e2125 _v)) : (e2536 _v) := by
  have p4016 := n4016 _v _q 
  have p10893 := n10893 _v _q 
  have p8475 := n8475 _v _q h2125
  exact FloorCertificate.node_15288 (e2 _v) (e7 _v) (e17 _v) (e45 _v) (e110 _v) p4016 p10893 p8475
theorem n15289 (_v : Vars) (_q : Query _v) (h2125 : (e2125 _v)) : (e3573 _v) := by
  have p14426 := n14426 _v _q 
  have p15288 := n15288 _v _q h2125
  simp only [e2536, e3565, e3566, e3570, e3571, e3572, e3573, e6656, e7176] at *
  tauto
theorem n15290 (_v : Vars) (_q : Query _v) (h2125 : (e2125 _v)) : (e3566 _v) := by
  have p7179 := n7179 _v _q 
  have p15289 := n15289 _v _q h2125
  simp only [e3565, e3566, e3570, e3571, e3572, e3573, e3590] at *
  tauto
theorem n15291 (_v : Vars) (_q : Query _v) (h196 : (e196 _v)) (h8310 : (e8310 _v)) : (e6746 _v) := by
  have p11384 := n11384 _v _q h8310
  have p5391 := n5391 _v _q 
  have p8140 := n8140 _v _q h196
  have p5257 := n5257 _v _q 
  exact FloorCertificate.node_15291 (e2 _v) (e7 _v) (e9 _v) (e45 _v) (e110 _v) p11384 p5391 p8140 p5257
theorem n15292 (_v : Vars) (_q : Query _v) (h196 : (e196 _v)) (h8310 : (e8310 _v)) : (e7630 _v) := by
  have p15152 := n15152 _v _q 
  have p15291 := n15291 _v _q h196 h8310
  simp only [e2740, e6746, e7606, e7607, e7608, e7609, e7610, e7630, e10951] at *
  tauto
theorem n15293 (_v : Vars) (_q : Query _v) (h196 : (e196 _v)) (h2125 : (e2125 _v)) (h8310 : (e8310 _v)) : (e2061 _v) := by
  have p11384 := n11384 _v _q h8310
  have p8140 := n8140 _v _q h196
  have p8475 := n8475 _v _q h2125
  exact FloorCertificate.node_15293 (e2 _v) (e7 _v) (e17 _v) (e45 _v) (e110 _v) p11384 p8140 p8475
theorem n15294 (_v : Vars) (_q : Query _v) (h196 : (e196 _v)) (h2125 : (e2125 _v)) (h8310 : (e8310 _v)) : (e4447 _v) := by
  have p14688 := n14688 _v _q 
  have p15293 := n15293 _v _q h196 h2125 h8310
  simp only [e2061, e4439, e4440, e4444, e4445, e4446, e4447, e6454, e7961] at *
  tauto
theorem n15295 (_v : Vars) (_q : Query _v) (h196 : (e196 _v)) (h2125 : (e2125 _v)) (h8310 : (e8310 _v)) : (e2310 _v) := by
  have p8475 := n8475 _v _q h2125
  have p11384 := n11384 _v _q h8310
  have p8140 := n8140 _v _q h196
  have p5391 := n5391 _v _q 
  have p5257 := n5257 _v _q 
  exact FloorCertificate.node_15295 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8475 p11384 p8140 p5391 p5257
theorem n15296 (_v : Vars) (_q : Query _v) (h196 : (e196 _v)) (h2125 : (e2125 _v)) (h8310 : (e8310 _v)) : (e3278 _v) := by
  have p14378 := n14378 _v _q 
  have p15295 := n15295 _v _q h196 h2125 h8310
  simp only [e2310, e3270, e3271, e3275, e3276, e3277, e3278, e6555, e6979] at *
  tauto
theorem n15297 (_v : Vars) (_q : Query _v) (h196 : (e196 _v)) (h2125 : (e2125 _v)) (h8310 : (e8310 _v)) : (e2364 _v) := by
  have p8475 := n8475 _v _q h2125
  have p5391 := n5391 _v _q 
  have p8140 := n8140 _v _q h196
  have p5257 := n5257 _v _q 
  have p11384 := n11384 _v _q h8310
  exact FloorCertificate.node_15297 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8475 p5391 p8140 p5257 p11384
theorem n15298 (_v : Vars) (_q : Query _v) (h196 : (e196 _v)) (h2125 : (e2125 _v)) (h8310 : (e8310 _v)) : (e4661 _v) := by
  have p14686 := n14686 _v _q 
  have p15297 := n15297 _v _q h196 h2125 h8310
  simp only [e2364, e4653, e4654, e4658, e4659, e4660, e4661, e6583, e8163] at *
  tauto
theorem n15299 (_v : Vars) (_q : Query _v) (h196 : (e196 _v)) (h2125 : (e2125 _v)) (h8310 : (e8310 _v)) : (e2536 _v) := by
  have p5257 := n5257 _v _q 
  have p11384 := n11384 _v _q h8310
  have p8475 := n8475 _v _q h2125
  have p8140 := n8140 _v _q h196
  exact FloorCertificate.node_15299 (e2 _v) (e7 _v) (e17 _v) (e45 _v) (e110 _v) p5257 p11384 p8475 p8140
theorem n15300 (_v : Vars) (_q : Query _v) (h196 : (e196 _v)) (h2125 : (e2125 _v)) (h8310 : (e8310 _v)) : (e3573 _v) := by
  have p14426 := n14426 _v _q 
  have p15299 := n15299 _v _q h196 h2125 h8310
  simp only [e2536, e3565, e3566, e3570, e3571, e3572, e3573, e6656, e7176] at *
  tauto
theorem n15301 (_v : Vars) (_q : Query _v) (h2125 : (e2125 _v)) : (e2061 _v) := by
  have p8478 := n8478 _v _q 
  have p8475 := n8475 _v _q h2125
  simp only [e2061, e2125, e6480, e8477] at *
  tauto
theorem n15302 (_v : Vars) (_q : Query _v) (h2125 : (e2125 _v)) (h8038 : (e8038 _v)) : (e2536 _v) := by
  have p4016 := n4016 _v _q 
  have p15301 := n15301 _v _q h2125
  have p8602 := n8602 _v _q h8038
  exact FloorCertificate.node_15302 (e2 _v) (e7 _v) (e17 _v) (e45 _v) (e110 _v) p4016 p15301 p8602
theorem n15303 (_v : Vars) (_q : Query _v) (h2125 : (e2125 _v)) (h8038 : (e8038 _v)) : (e3573 _v) := by
  have p14426 := n14426 _v _q 
  have p15302 := n15302 _v _q h2125 h8038
  simp only [e2536, e3565, e3566, e3570, e3571, e3572, e3573, e6656, e7176] at *
  tauto
theorem n15304 (_v : Vars) (_q : Query _v) (h2125 : (e2125 _v)) : (e4447 _v) := by
  have p14688 := n14688 _v _q 
  have p15301 := n15301 _v _q h2125
  simp only [e2061, e4439, e4440, e4444, e4445, e4446, e4447, e6454, e7961] at *
  tauto
theorem n15305 (_v : Vars) (_q : Query _v) (h2125 : (e2125 _v)) : (e4439 _v) := by
  have p14925 := n14925 _v _q 
  have p15304 := n15304 _v _q h2125
  simp only [e4439, e4440, e4444, e4445, e4446, e4447, e4941] at *
  tauto
theorem n15306 (_v : Vars) (_q : Query _v) (h6555 : (e6555 _v)) : (e7170 _v) := by
  have p14427 := n14427 _v _q 
  have p12851 := n12851 _v _q h6555
  simp only [e2536, e3583, e3585, e3588, e3589, e6656, e7169, e7170, e7173] at *
  tauto
theorem n15307 (_v : Vars) (_q : Query _v)  : (e7948 _v) := by
  simp only [e4434, e4435, e4436, e4437, e7947, e7948] at *
  tauto
theorem n15308 (_v : Vars) (_q : Query _v) (h4435 : (e4435 _v)) : (e4435 _v) := by
  exact h4435
theorem n15309 (_v : Vars) (_q : Query _v) (h4435 : (e4435 _v)) : (e7947 _v) := by
  have p15307 := n15307 _v _q 
  have p15308 := n15308 _v _q h4435
  simp only [e4434, e4435, e4436, e4437, e7947, e7948] at *
  tauto
theorem n15310 (_v : Vars) (_q : Query _v) (h4435 : (e4435 _v)) : (e2061 _v) := by
  have p14601 := n14601 _v _q 
  have p15309 := n15309 _v _q h4435
  simp only [e2061, e4434, e4435, e4436, e4437, e7947, e7955, e7958] at *
  tauto
theorem n15311 (_v : Vars) (_q : Query _v) (h4435 : (e4435 _v)) : (e4447 _v) := by
  have p14688 := n14688 _v _q 
  have p15310 := n15310 _v _q h4435
  simp only [e2061, e4439, e4440, e4444, e4445, e4446, e4447, e6454, e7961] at *
  tauto
theorem n15312 (_v : Vars) (_q : Query _v)  : (e11307 _v) := by
  have p14671 := n14671 _v _q 
  simp only [e2592, e4855, e4856, e4857, e4858, e6672, e8324, e8330, e8333, e8335, e8338, e8345, e8346, e8347, e8348, e8349, e11307, e11309, e11310, e11311] at *
  tauto
theorem n15313 (_v : Vars) (_q : Query _v) (h5093 : (e5093 _v)) : (e6672 _v) := by
  have p11443 := n11443 _v _q 
  have p11440 := n11440 _v _q h5093
  simp only [e13, e2592, e5093, e6672, e11442] at *
  tauto
theorem n15314 (_v : Vars) (_q : Query _v) (h5093 : (e5093 _v)) : (e8348 _v) := by
  have p15312 := n15312 _v _q 
  have p15313 := n15313 _v _q h5093
  simp only [e2592, e6672, e8335, e8338, e8345, e8346, e8347, e8348, e11307] at *
  tauto
theorem n15315 (_v : Vars) (_q : Query _v) (h5093 : (e5093 _v)) : (e6724 _v) := by
  have p11440 := n11440 _v _q h5093
  have p10893 := n10893 _v _q 
  exact FloorCertificate.node_15315 (e2 _v) (e7 _v) (e9 _v) (e45 _v) p11440 p10893
theorem n15316 (_v : Vars) (_q : Query _v) (h5093 : (e5093 _v)) : (e7517 _v) := by
  have p15196 := n15196 _v _q 
  have p15315 := n15315 _v _q h5093
  simp only [e2691, e6724, e7493, e7494, e7495, e7496, e7497, e7517, e10904] at *
  tauto
theorem n15317 (_v : Vars) (_q : Query _v) (h5093 : (e5093 _v)) : (e2805 _v) := by
  have p8663 := n8663 _v _q 
  have p10893 := n10893 _v _q 
  have p11375 := n11375 _v _q 
  have p11440 := n11440 _v _q h5093
  exact FloorCertificate.node_15317 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8663 p10893 p11375 p11440
theorem n15318 (_v : Vars) (_q : Query _v) (h5093 : (e5093 _v)) : (e3954 _v) := by
  have p14486 := n14486 _v _q 
  have p15317 := n15317 _v _q h5093
  simp only [e2805, e3944, e3945, e3946, e3947, e3948, e3954, e6792, e7438] at *
  tauto
theorem n15319 (_v : Vars) (_q : Query _v)  : (e8479 _v) := by
  simp only [e5098, e5100, e5102, e5103, e5104, e8479] at *
  tauto
theorem n15320 (_v : Vars) (_q : Query _v) (h5093 : (e5093 _v)) : (e5105 _v) := by
  have p15204 := n15204 _v _q 
  have p11440 := n11440 _v _q h5093
  simp only [e13, e5093, e5098, e5100, e5102, e5103, e5104, e5105, e8622] at *
  tauto
theorem n15321 (_v : Vars) (_q : Query _v) (h5093 : (e5093 _v)) : (e5100 _v) := by
  have p15319 := n15319 _v _q 
  have p15320 := n15320 _v _q h5093
  simp only [e5098, e5100, e5102, e5103, e5104, e5105, e8479] at *
  tauto
theorem n15322 (_v : Vars) (_q : Query _v) (h5093 : (e5093 _v)) : (e2377 _v) := by
  have p11375 := n11375 _v _q 
  have p8663 := n8663 _v _q 
  have p11440 := n11440 _v _q h5093
  exact FloorCertificate.node_15322 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e110 _v) p11375 p8663 p11440
theorem n15323 (_v : Vars) (_q : Query _v) (h5093 : (e5093 _v)) : (e4755 _v) := by
  have p14687 := n14687 _v _q 
  have p15322 := n15322 _v _q h5093
  simp only [e2377, e4747, e4748, e4752, e4753, e4754, e4755, e6591, e8238] at *
  tauto
theorem n15324 (_v : Vars) (_q : Query _v) (h5093 : (e5093 _v)) : (e2697 _v) := by
  have p8663 := n8663 _v _q 
  have p11440 := n11440 _v _q h5093
  have p10893 := n10893 _v _q 
  exact FloorCertificate.node_15324 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) p8663 p11440 p10893
theorem n15325 (_v : Vars) (_q : Query _v) (h5093 : (e5093 _v)) : (e4499 _v) := by
  have p14700 := n14700 _v _q 
  have p15324 := n15324 _v _q h5093
  simp only [e2697, e4491, e4492, e4496, e4497, e4498, e4499, e6732, e7998] at *
  tauto
theorem n15326 (_v : Vars) (_q : Query _v) (h5093 : (e5093 _v)) : (e2598 _v) := by
  have p8663 := n8663 _v _q 
  have p5255 := n5255 _v _q 
  have p10893 := n10893 _v _q 
  have p11440 := n11440 _v _q h5093
  exact FloorCertificate.node_15326 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8663 p5255 p10893 p11440
end
end Assembly
