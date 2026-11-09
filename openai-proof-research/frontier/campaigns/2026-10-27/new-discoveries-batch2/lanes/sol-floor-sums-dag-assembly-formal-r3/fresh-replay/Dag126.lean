import Dag125
import generated.th_lemma_8
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n15327 (_v : Vars) (_q : Query _v) (h5093 : (e5093 _v)) : (e4067 _v) := by
  have p14703 := n14703 _v _q 
  have p15326 := n15326 _v _q h5093
  simp only [e2598, e4059, e4060, e4064, e4065, e4066, e4067, e6684, e7560] at *
  tauto
theorem n15328 (_v : Vars) (_q : Query _v) (h6555 : (e6555 _v)) : (e6973 _v) := by
  have p14377 := n14377 _v _q 
  have p11362 := n11362 _v _q h6555
  simp only [e2310, e3265, e3266, e3267, e3268, e6555, e6965, e6973, e6976] at *
  tauto
theorem n15329 (_v : Vars) (_q : Query _v) (h6555 : (e6555 _v)) : (e3267 _v) := by
  have p14776 := n14776 _v _q 
  have p15328 := n15328 _v _q h6555
  simp only [e3265, e3266, e3267, e3268, e6965, e6966, e6973] at *
  tauto
theorem n15330 (_v : Vars) (_q : Query _v)  : (e10977 _v) := by
  have p14552 := n14552 _v _q 
  simp only [e2371, e4181, e4182, e4183, e4184, e6579, e7677, e7683, e7686, e7688, e7691, e7698, e7699, e7700, e7701, e7702, e10977, e10979, e10980, e10981] at *
  tauto
theorem n15331 (_v : Vars) (_q : Query _v) (h5093 : (e5093 _v)) : (e6579 _v) := by
  have p11375 := n11375 _v _q 
  have p11440 := n11440 _v _q h5093
  exact FloorCertificate.node_15331 (e2 _v) (e7 _v) (e9 _v) (e110 _v) p11375 p11440
theorem n15332 (_v : Vars) (_q : Query _v) (h5093 : (e5093 _v)) : (e7701 _v) := by
  have p15330 := n15330 _v _q 
  have p15331 := n15331 _v _q h5093
  simp only [e2371, e6579, e7688, e7691, e7698, e7699, e7700, e7701, e10977] at *
  tauto
theorem n15333 (_v : Vars) (_q : Query _v) (h6555 : (e6555 _v)) : (e6583 _v) := by
  have p11362 := n11362 _v _q h6555
  have p4016 := n4016 _v _q 
  exact FloorCertificate.node_15333 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e110 _v) p11362 p4016
theorem n15334 (_v : Vars) (_q : Query _v) (h6555 : (e6555 _v)) : (e8157 _v) := by
  have p14632 := n14632 _v _q 
  have p15333 := n15333 _v _q h6555
  simp only [e2364, e4648, e4649, e4650, e4651, e6583, e8149, e8157, e8160] at *
  tauto
theorem n15335 (_v : Vars) (_q : Query _v) (h8038 : (e8038 _v)) : (e8348 _v) := by
  have p15312 := n15312 _v _q 
  have p12846 := n12846 _v _q h8038
  simp only [e2592, e6672, e8335, e8338, e8345, e8346, e8347, e8348, e11307] at *
  tauto
theorem n15336 (_v : Vars) (_q : Query _v) (h8038 : (e8038 _v)) : (e8335 _v) := by
  have p11421 := n11421 _v _q 
  have p15335 := n15335 _v _q h8038
  simp only [e8335, e8338, e8345, e8346, e8347, e8348, e8482] at *
  tauto
theorem n15337 (_v : Vars) (_q : Query _v) (h6583 : (e6583 _v)) : (e8157 _v) := by
  have p14632 := n14632 _v _q 
  have p11340 := n11340 _v _q h6583
  simp only [e2364, e4648, e4649, e4650, e4651, e6583, e8149, e8157, e8160] at *
  tauto
theorem n15338 (_v : Vars) (_q : Query _v) (h6583 : (e6583 _v)) : (e4648 _v) := by
  have p15027 := n15027 _v _q 
  have p15337 := n15337 _v _q h6583
  simp only [e4648, e4649, e4650, e4651, e8149, e8150, e8157] at *
  tauto
theorem n15339 (_v : Vars) (_q : Query _v) (h8038 : (e8038 _v)) : (e7701 _v) := by
  have p15330 := n15330 _v _q 
  have p11444 := n11444 _v _q h8038
  simp only [e2371, e6579, e7688, e7691, e7698, e7699, e7700, e7701, e10977] at *
  tauto
theorem n15340 (_v : Vars) (_q : Query _v) (h8038 : (e8038 _v)) : (e7688 _v) := by
  have p11450 := n11450 _v _q 
  have p15339 := n15339 _v _q h8038
  simp only [e7688, e7691, e7698, e7699, e7700, e7701, e8495] at *
  tauto
theorem n15341 (_v : Vars) (_q : Query _v) (h6676 : (e6676 _v)) : (e7830 _v) := by
  have p14579 := n14579 _v _q 
  have p10943 := n10943 _v _q h6676
  simp only [e2585, e4301, e4302, e4303, e4304, e6676, e7822, e7830, e7833] at *
  tauto
theorem n15342 (_v : Vars) (_q : Query _v) (h6676 : (e6676 _v)) : (e4301 _v) := by
  have p14840 := n14840 _v _q 
  have p15341 := n15341 _v _q h6676
  simp only [e4301, e4302, e4303, e4304, e7822, e7823, e7830] at *
  tauto
theorem n15343 (_v : Vars) (_q : Query _v) (h6676 : (e6676 _v)) (h8038 : (e8038 _v)) : (e6454 _v) := by
  have p10943 := n10943 _v _q h6676
  have p8602 := n8602 _v _q h8038
  exact FloorCertificate.node_15343 (e2 _v) (e7 _v) (e17 _v) (e45 _v) (e110 _v) p10943 p8602
theorem n15344 (_v : Vars) (_q : Query _v) (h6676 : (e6676 _v)) (h8038 : (e8038 _v)) : (e7955 _v) := by
  have p14601 := n14601 _v _q 
  have p15343 := n15343 _v _q h6676 h8038
  simp only [e2061, e4434, e4435, e4436, e4437, e6454, e7947, e7955, e7958] at *
  tauto
theorem n15345 (_v : Vars) (_q : Query _v) (h6571 : (e6571 _v)) (h8038 : (e8038 _v)) : (e7945 _v) := by
  have p15228 := n15228 _v _q 
  have p11446 := n11446 _v _q h6571 h8038
  simp only [e2787, e6772, e7932, e7935, e7942, e7943, e7944, e7945, e11111] at *
  tauto
theorem n15346 (_v : Vars) (_q : Query _v) (h6571 : (e6571 _v)) (h8038 : (e8038 _v)) : (e7935 _v) := by
  have p15266 := n15266 _v _q 
  have p15345 := n15345 _v _q h6571 h8038
  simp only [e7932, e7935, e7942, e7943, e7944, e7945, e8489] at *
  tauto
theorem n15347 (_v : Vars) (_q : Query _v) (h6571 : (e6571 _v)) : (e4661 _v) := by
  have p14686 := n14686 _v _q 
  have p14142 := n14142 _v _q h6571
  simp only [e2364, e4653, e4654, e4658, e4659, e4660, e4661, e6583, e8163] at *
  tauto
theorem n15348 (_v : Vars) (_q : Query _v) (h6571 : (e6571 _v)) : (e2364 _v) := by
  have p8663 := n8663 _v _q 
  have p8447 := n8447 _v _q h6571
  exact FloorCertificate.node_15348 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e110 _v) p8663 p8447
theorem n15349 (_v : Vars) (_q : Query _v) (h6571 : (e6571 _v)) : (e4661 _v) := by
  have p14686 := n14686 _v _q 
  have p15348 := n15348 _v _q h6571
  simp only [e2364, e4653, e4654, e4658, e4659, e4660, e4661, e6583, e8163] at *
  tauto
theorem n15350 (_v : Vars) (_q : Query _v) (h6571 : (e6571 _v)) : (e3278 _v) := by
  have p14378 := n14378 _v _q 
  have p12850 := n12850 _v _q h6571
  simp only [e2310, e3270, e3271, e3275, e3276, e3277, e3278, e6555, e6979] at *
  tauto
theorem n15351 (_v : Vars) (_q : Query _v) (h6571 : (e6571 _v)) : (e3271 _v) := by
  have p6982 := n6982 _v _q 
  have p15350 := n15350 _v _q h6571
  simp only [e3270, e3271, e3275, e3276, e3277, e3278, e3288] at *
  tauto
theorem n15352 (_v : Vars) (_q : Query _v) (h8310 : (e8310 _v)) : (e2536 _v) := by
  have p11384 := n11384 _v _q h8310
  have p8663 := n8663 _v _q 
  exact FloorCertificate.node_15352 (e2 _v) (e17 _v) (e45 _v) (e110 _v) p11384 p8663
theorem n15353 (_v : Vars) (_q : Query _v) (h8310 : (e8310 _v)) : (e3573 _v) := by
  have p14426 := n14426 _v _q 
  have p15352 := n15352 _v _q h8310
  simp only [e2536, e3565, e3566, e3570, e3571, e3572, e3573, e6656, e7176] at *
  tauto
theorem n15354 (_v : Vars) (_q : Query _v) (h6571 : (e6571 _v)) : (e7819 _v) := by
  have p14994 := n14994 _v _q 
  have p11445 := n11445 _v _q h6571
  simp only [e2303, e7807, e7812, e7814, e7816, e7817, e7818, e7819, e11046] at *
  tauto
theorem n15355 (_v : Vars) (_q : Query _v) (h6656 : (e6656 _v)) : (e6676 _v) := by
  have p11499 := n11499 _v _q h6656
  have p4016 := n4016 _v _q 
  exact FloorCertificate.node_15355 (e2 _v) (e7 _v) (e17 _v) (e45 _v) (e110 _v) p11499 p4016
theorem n15356 (_v : Vars) (_q : Query _v) (h6656 : (e6656 _v)) : (e7830 _v) := by
  have p14579 := n14579 _v _q 
  have p15355 := n15355 _v _q h6656
  simp only [e2585, e4301, e4302, e4303, e4304, e6676, e7822, e7830, e7833] at *
  tauto
theorem n15357 (_v : Vars) (_q : Query _v) (h6656 : (e6656 _v)) (h8038 : (e8038 _v)) : (e6454 _v) := by
  have p8602 := n8602 _v _q h8038
  have p11499 := n11499 _v _q h6656
  have p4016 := n4016 _v _q 
  exact FloorCertificate.node_15357 (e2 _v) (e7 _v) (e17 _v) (e45 _v) (e110 _v) p8602 p11499 p4016
theorem n15358 (_v : Vars) (_q : Query _v) (h6656 : (e6656 _v)) (h8038 : (e8038 _v)) : (e7955 _v) := by
  have p14601 := n14601 _v _q 
  have p15357 := n15357 _v _q h6656 h8038
  simp only [e2061, e4434, e4435, e4436, e4437, e6454, e7947, e7955, e7958] at *
  tauto
theorem n15359 (_v : Vars) (_q : Query _v) (h6656 : (e6656 _v)) : (e7170 _v) := by
  have p14427 := n14427 _v _q 
  have p11499 := n11499 _v _q h6656
  simp only [e2536, e3583, e3585, e3588, e3589, e6656, e7169, e7170, e7173] at *
  tauto
theorem n15360 (_v : Vars) (_q : Query _v) (h6656 : (e6656 _v)) : (e3585 _v) := by
  have p14783 := n14783 _v _q 
  have p15359 := n15359 _v _q h6656
  simp only [e3583, e3585, e3588, e3589, e7169, e7170, e7182] at *
  tauto
theorem n15361 (_v : Vars) (_q : Query _v) (h6583 : (e6583 _v)) : (e7830 _v) := by
  have p14579 := n14579 _v _q 
  have p12887 := n12887 _v _q h6583
  simp only [e2585, e4301, e4302, e4303, e4304, e6676, e7822, e7830, e7833] at *
  tauto
theorem n15362 (_v : Vars) (_q : Query _v) (h2061 : (e2061 _v)) (h8310 : (e8310 _v)) : (e2364 _v) := by
  have p11384 := n11384 _v _q h8310
  have p5391 := n5391 _v _q 
  have p15235 := n15235 _v _q h2061
  exact FloorCertificate.node_15362 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p11384 p5391 p15235
theorem n15363 (_v : Vars) (_q : Query _v) (h2061 : (e2061 _v)) (h8310 : (e8310 _v)) : (e4661 _v) := by
  have p14686 := n14686 _v _q 
  have p15362 := n15362 _v _q h2061 h8310
  simp only [e2364, e4653, e4654, e4658, e4659, e4660, e4661, e6583, e8163] at *
  tauto
theorem n15364 (_v : Vars) (_q : Query _v) (h2061 : (e2061 _v)) (h8310 : (e8310 _v)) : (e2585 _v) := by
  have p15235 := n15235 _v _q h2061
  have p11384 := n11384 _v _q h8310
  exact FloorCertificate.node_15364 (e2 _v) (e7 _v) (e17 _v) (e45 _v) (e110 _v) p15235 p11384
theorem n15365 (_v : Vars) (_q : Query _v) (h2061 : (e2061 _v)) (h8310 : (e8310 _v)) : (e4314 _v) := by
  have p14704 := n14704 _v _q 
  have p15364 := n15364 _v _q h2061 h8310
  simp only [e2585, e4306, e4307, e4311, e4312, e4313, e4314, e6676, e7836] at *
  tauto
theorem n15366 (_v : Vars) (_q : Query _v) (h8310 : (e8310 _v)) : (e6772 _v) := by
  have p5391 := n5391 _v _q 
  have p5257 := n5257 _v _q 
  have p11384 := n11384 _v _q h8310
  exact FloorCertificate.node_15366 (e2 _v) (e7 _v) (e9 _v) (e45 _v) (e110 _v) p5391 p5257 p11384
theorem n15367 (_v : Vars) (_q : Query _v) (h8310 : (e8310 _v)) : (e7945 _v) := by
  have p15228 := n15228 _v _q 
  have p15366 := n15366 _v _q h8310
  simp only [e2787, e6772, e7932, e7935, e7942, e7943, e7944, e7945, e11111] at *
  tauto
theorem n15368 (_v : Vars) (_q : Query _v) (h6676 : (e6676 _v)) (h8038 : (e8038 _v)) : (e6454 _v) := by
  have p8602 := n8602 _v _q h8038
  have p10943 := n10943 _v _q h6676
  exact FloorCertificate.node_15368 (e2 _v) (e7 _v) (e17 _v) (e45 _v) (e110 _v) p8602 p10943
theorem n15369 (_v : Vars) (_q : Query _v) (h6676 : (e6676 _v)) (h8038 : (e8038 _v)) : (e7955 _v) := by
  have p14601 := n14601 _v _q 
  have p15368 := n15368 _v _q h6676 h8038
  simp only [e2061, e4434, e4435, e4436, e4437, e6454, e7947, e7955, e7958] at *
  tauto
theorem n15370 (_v : Vars) (_q : Query _v)  : (e8497 _v) := by
  simp only [e7688, e7691, e7698, e7699, e7700, e8497] at *
  tauto
theorem n15371 (_v : Vars) (_q : Query _v) (h8038 : (e8038 _v)) : (e7691 _v) := by
  have p15370 := n15370 _v _q 
  have p15339 := n15339 _v _q h8038
  simp only [e7688, e7691, e7698, e7699, e7700, e7701, e8497] at *
  tauto
end
end Assembly
