import Dag066
import generated.th_lemma_2
import generated.th_lemma_3
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n11496 (_v : Vars) (_q : Query _v) (h2787 : (e2787 _v)) (h6571 : (e6571 _v)) : (e7489 _v) := by
  have p8447 := n8447 _v _q h6571
  have p10893 := n10893 _v _q 
  have p11430 := n11430 _v _q h2787
  exact FloorCertificate.node_11496 (e2 _v) (e7 _v) (e9 _v) (e45 _v) (e110 _v) p8447 p10893 p11430
theorem n11498 (_v : Vars) (_q : Query _v)  : (e11497 _v) := by
  by_contra hc
  change ¬ ((¬ (e2787 _v)) ∨ (e2358 _v)) at hc
  have h2787 : (e2787 _v) := by
    tauto
  have h6571 : (e6571 _v) := by
    change (¬ (e2358 _v))
    tauto
  have p11496 := n11496 _v _q h2787 h6571
  exact p11496
theorem n11499 (_v : Vars) (_q : Query _v) (h6656 : (e6656 _v)) : (e6656 _v) := by
  exact h6656
theorem n11500 (_v : Vars) (_q : Query _v) (h2634 : (e2634 _v)) (h6656 : (e6656 _v)) : (e7489 _v) := by
  have p11499 := n11499 _v _q h6656
  have p5255 := n5255 _v _q 
  have p11032 := n11032 _v _q h2634
  exact FloorCertificate.node_11500 (e2 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p11499 p5255 p11032
theorem n11502 (_v : Vars) (_q : Query _v)  : (e11501 _v) := by
  by_contra hc
  change ¬ ((e2536 _v) ∨ (¬ (e2634 _v))) at hc
  have h2634 : (e2634 _v) := by
    tauto
  have h6656 : (e6656 _v) := by
    change (¬ (e2536 _v))
    tauto
  have p11500 := n11500 _v _q h2634 h6656
  exact p11500
theorem n11503 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h6758 : (e6758 _v)) : (e7489 _v) := by
  have p8425 := n8425 _v _q h6758
  have p4016 := n4016 _v _q 
  have p8464 := n8464 _v _q h2351
  have p10893 := n10893 _v _q 
  have p331 := n331 _v _q 
  exact FloorCertificate.node_11503 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8425 p4016 p8464 p10893 p331
theorem n11505 (_v : Vars) (_q : Query _v)  : (e11504 _v) := by
  by_contra hc
  change ¬ ((¬ (e2351 _v)) ∨ (e2746 _v)) at hc
  have h2351 : (e2351 _v) := by
    tauto
  have h6758 : (e6758 _v) := by
    change (¬ (e2746 _v))
    tauto
  have p11503 := n11503 _v _q h2351 h6758
  exact p11503
theorem n11506 (_v : Vars) (_q : Query _v) (h6758 : (e6758 _v)) : (e6600 _v) := by
  have p11375 := n11375 _v _q 
  have p8425 := n8425 _v _q h6758
  have p10896 := n10896 _v _q 
  exact FloorCertificate.node_11506 (e2 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p11375 p8425 p10896
theorem n11507 (_v : Vars) (_q : Query _v) (h6758 : (e6758 _v)) : (e6454 _v) := by
  have p8425 := n8425 _v _q h6758
  have p10896 := n10896 _v _q 
  have p10893 := n10893 _v _q 
  exact FloorCertificate.node_11507 (e2 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8425 p10896 p10893
theorem n11508 (_v : Vars) (_q : Query _v) (h2475 : (e2475 _v)) (h5138 : (e5138 _v)) : (e7489 _v) := by
  have p5255 := n5255 _v _q 
  have p5257 := n5257 _v _q 
  have p8457 := n8457 _v _q h2475
  have p11487 := n11487 _v _q h5138
  exact FloorCertificate.node_11508 (e2 _v) (e7 _v) (e9 _v) (e45 _v) (e110 _v) p5255 p5257 p8457 p11487
theorem n11510 (_v : Vars) (_q : Query _v)  : (e11509 _v) := by
  by_contra hc
  change ¬ ((e79 _v) ∨ (¬ (e2475 _v))) at hc
  have h2475 : (e2475 _v) := by
    tauto
  have h5138 : (e5138 _v) := by
    change (¬ (e79 _v))
    tauto
  have p11508 := n11508 _v _q h2475 h5138
  exact p11508
theorem n11511 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h6501 : (e6501 _v)) : (e7489 _v) := by
  have p5257 := n5257 _v _q 
  have p4016 := n4016 _v _q 
  have p8554 := n8554 _v _q h6501
  have p8464 := n8464 _v _q h2351
  exact FloorCertificate.node_11511 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e110 _v) p5257 p4016 p8554 p8464
theorem n11513 (_v : Vars) (_q : Query _v)  : (e11512 _v) := by
  by_contra hc
  change ¬ ((e2179 _v) ∨ (¬ (e2351 _v))) at hc
  have h2351 : (e2351 _v) := by
    tauto
  have h6501 : (e6501 _v) := by
    change (¬ (e2179 _v))
    tauto
  have p11511 := n11511 _v _q h2351 h6501
  exact p11511
theorem n11514 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) (h6423 : (e6423 _v)) : (e7489 _v) := by
  have p5255 := n5255 _v _q 
  have p8452 := n8452 _v _q h6423
  have p11374 := n11374 _v _q h251
  have p5257 := n5257 _v _q 
  have p4946 := n4946 _v _q 
  exact FloorCertificate.node_11514 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p5255 p8452 p11374 p5257 p4946
theorem n11516 (_v : Vars) (_q : Query _v)  : (e11515 _v) := by
  by_contra hc
  change ¬ ((e1995 _v) ∨ (¬ (e251 _v))) at hc
  have h251 : (e251 _v) := by
    tauto
  have h6423 : (e6423 _v) := by
    change (¬ (e1995 _v))
    tauto
  have p11514 := n11514 _v _q h251 h6423
  exact p11514
theorem n11517 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) (h6776 : (e6776 _v)) : (e7489 _v) := by
  have p5391 := n5391 _v _q 
  have p258 := n258 _v _q 
  have p8601 := n8601 _v _q h6776
  have p5257 := n5257 _v _q 
  have p5255 := n5255 _v _q 
  have p11374 := n11374 _v _q h251
  exact FloorCertificate.node_11517 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p5391 p258 p8601 p5257 p5255 p11374
theorem n11519 (_v : Vars) (_q : Query _v)  : (e11518 _v) := by
  by_contra hc
  change ¬ ((e2781 _v) ∨ (¬ (e251 _v))) at hc
  have h251 : (e251 _v) := by
    tauto
  have h6776 : (e6776 _v) := by
    change (¬ (e2781 _v))
    tauto
  have p11517 := n11517 _v _q h251 h6776
  exact p11517
theorem n11520 (_v : Vars) (_q : Query _v) (h5223 : (e5223 _v)) : (e5223 _v) := by
  exact h5223
theorem n11521 (_v : Vars) (_q : Query _v) (h196 : (e196 _v)) (h5223 : (e5223 _v)) : (e7489 _v) := by
  have p8140 := n8140 _v _q h196
  have p5255 := n5255 _v _q 
  have p11520 := n11520 _v _q h5223
  have p5257 := n5257 _v _q 
  exact FloorCertificate.node_11521 (e2 _v) (e7 _v) (e9 _v) (e45 _v) (e110 _v) p8140 p5255 p11520 p5257
theorem n11523 (_v : Vars) (_q : Query _v)  : (e11522 _v) := by
  by_contra hc
  change ¬ ((e214 _v) ∨ (¬ (e196 _v))) at hc
  have h196 : (e196 _v) := by
    tauto
  have h5223 : (e5223 _v) := by
    change (¬ (e214 _v))
    tauto
  have p11521 := n11521 _v _q h196 h5223
  exact p11521
theorem n11524 (_v : Vars) (_q : Query _v)  : (e7661 _v) := by
  simp only [e4156, e4157, e4158, e4159, e7660, e7661] at *
  tauto
theorem n11525 (_v : Vars) (_q : Query _v) (h7668 : (e7668 _v)) : (e7668 _v) := by
  exact h7668
theorem n11526 (_v : Vars) (_q : Query _v) (h7668 : (e7668 _v)) : (e4156 _v) := by
  have p11524 := n11524 _v _q 
  have p11525 := n11525 _v _q h7668
  simp only [e4156, e4157, e4158, e4159, e7660, e7661, e7668] at *
  tauto
theorem n11527 (_v : Vars) (_q : Query _v)  : (e8567 _v) := by
  simp only [e4156, e4157, e4158, e4159, e7660, e8567] at *
  tauto
theorem n11528 (_v : Vars) (_q : Query _v) (h7668 : (e7668 _v)) : (e4158 _v) := by
  have p11527 := n11527 _v _q 
  have p11525 := n11525 _v _q h7668
  simp only [e4156, e4157, e4158, e4159, e7660, e7668, e8567] at *
  tauto
theorem n11529 (_v : Vars) (_q : Query _v) (h474 : (e474 _v)) (h6776 : (e6776 _v)) : (e7489 _v) := by
  have p11414 := n11414 _v _q h474
  have p10896 := n10896 _v _q 
  have p8601 := n8601 _v _q h6776
  exact FloorCertificate.node_11529 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p11414 p10896 p8601
theorem n11531 (_v : Vars) (_q : Query _v)  : (e11530 _v) := by
  by_contra hc
  change ¬ ((e2781 _v) ∨ (¬ (e474 _v))) at hc
  have h474 : (e474 _v) := by
    tauto
  have h6776 : (e6776 _v) := by
    change (¬ (e2781 _v))
    tauto
  have p11529 := n11529 _v _q h474 h6776
  exact p11529
theorem n11532 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) : (e2781 _v) := by
  have p8464 := n8464 _v _q h2351
  have p10893 := n10893 _v _q 
  exact FloorCertificate.node_11532 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8464 p10893
theorem n11533 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) : (e2733 _v) := by
  have p8424 := n8424 _v _q 
  have p11532 := n11532 _v _q h2351
  simp only [e2733, e2781, e6776, e8423] at *
  tauto
theorem n11534 (_v : Vars) (_q : Query _v) (h2402 : (e2402 _v)) (h6750 : (e6750 _v)) : (e2303 _v) := by
  have p8420 := n8420 _v _q h6750
  have p8591 := n8591 _v _q h2402
  exact FloorCertificate.node_11534 (e2 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8420 p8591
theorem n11535 (_v : Vars) (_q : Query _v) (h2402 : (e2402 _v)) (h6750 : (e6750 _v)) (h6772 : (e6772 _v)) : (e8038 _v) := by
  have p8461 := n8461 _v _q 
  have p8458 := n8458 _v _q h6772
  have p11534 := n11534 _v _q h2402 h6750
  simp only [e2303, e2475, e2787, e6772, e7807, e8038, e8460] at *
  tauto
theorem n11536 (_v : Vars) (_q : Query _v) (h2402 : (e2402 _v)) (h6750 : (e6750 _v)) : (e2358 _v) := by
  have p8451 := n8451 _v _q 
  have p11534 := n11534 _v _q h2402 h6750
  simp only [e2303, e2358, e7807, e8450] at *
  tauto
theorem n11537 (_v : Vars) (_q : Query _v) (h6423 : (e6423 _v)) : (e6600 _v) := by
  have p5255 := n5255 _v _q 
  have p5257 := n5257 _v _q 
  have p5391 := n5391 _v _q 
  have p8452 := n8452 _v _q h6423
  exact FloorCertificate.node_11537 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p5255 p5257 p5391 p8452
theorem n11538 (_v : Vars) (_q : Query _v) (h6423 : (e6423 _v)) : (e6630 _v) := by
  have p8442 := n8442 _v _q 
  have p11537 := n11537 _v _q h6423
  simp only [e2402, e2468, e6600, e6630, e8441] at *
  tauto
theorem n11539 (_v : Vars) (_q : Query _v) (h6423 : (e6423 _v)) : (e6501 _v) := by
  have p8452 := n8452 _v _q h6423
  have p5255 := n5255 _v _q 
  have p5257 := n5257 _v _q 
  exact FloorCertificate.node_11539 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e110 _v) p8452 p5255 p5257
theorem n11540 (_v : Vars) (_q : Query _v) (h6423 : (e6423 _v)) : (e6525 _v) := by
  have p8557 := n8557 _v _q 
  have p11539 := n11539 _v _q h6423
  simp only [e2179, e2242, e6501, e6525, e8556] at *
  tauto
theorem n11541 (_v : Vars) (_q : Query _v)  : (e8491 _v) := by
  simp only [e8315, e8317, e8319, e8320, e8321, e8491] at *
  tauto
theorem n11542 (_v : Vars) (_q : Query _v) (h8320 : (e8320 _v)) : (e8320 _v) := by
  exact h8320
theorem n11543 (_v : Vars) (_q : Query _v) (h8320 : (e8320 _v)) : (e8321 _v) := by
  have p11541 := n11541 _v _q 
  have p11542 := n11542 _v _q h8320
  simp only [e8315, e8317, e8319, e8320, e8321, e8491] at *
  tauto
theorem n11544 (_v : Vars) (_q : Query _v) (h2132 : (e2132 _v)) (h2364 : (e2364 _v)) (h6454 : (e6454 _v)) : (e7489 _v) := by
  have p8527 := n8527 _v _q h2364
  have p5255 := n5255 _v _q 
  have p8430 := n8430 _v _q h6454
  have p11349 := n11349 _v _q h2132
  exact FloorCertificate.node_11544 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e110 _v) p8527 p5255 p8430 p11349
theorem n11546 (_v : Vars) (_q : Query _v)  : (e11545 _v) := by
  by_contra hc
  change ¬ ((¬ (e2132 _v)) ∨ (¬ (e2364 _v)) ∨ (e2061 _v)) at hc
  have h2132 : (e2132 _v) := by
    tauto
  have h2364 : (e2364 _v) := by
    tauto
  have h6454 : (e6454 _v) := by
    change (¬ (e2061 _v))
    tauto
  have p11544 := n11544 _v _q h2132 h2364 h6454
  exact p11544
theorem n11547 (_v : Vars) (_q : Query _v) (h48 : (e48 _v)) : (e48 _v) := by
  exact h48
theorem n11548 (_v : Vars) (_q : Query _v) (h48 : (e48 _v)) (h6676 : (e6676 _v)) : (e7489 _v) := by
  have p5255 := n5255 _v _q 
  have p11547 := n11547 _v _q h48
  have p10943 := n10943 _v _q h6676
  exact FloorCertificate.node_11548 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p5255 p11547 p10943
theorem n11550 (_v : Vars) (_q : Query _v)  : (e11549 _v) := by
  by_contra hc
  change ¬ ((e2585 _v) ∨ (¬ (e48 _v))) at hc
  have h48 : (e48 _v) := by
    tauto
  have h6676 : (e6676 _v) := by
    change (¬ (e2585 _v))
    tauto
  have p11548 := n11548 _v _q h48 h6676
  exact p11548
theorem n11551 (_v : Vars) (_q : Query _v) (h2303 : (e2303 _v)) (h2781 : (e2781 _v)) (h6525 : (e6525 _v)) : (e7489 _v) := by
  have p8421 := n8421 _v _q h2781
  have p8448 := n8448 _v _q h2303
  have p5391 := n5391 _v _q 
  have p8463 := n8463 _v _q h6525
  exact FloorCertificate.node_11551 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8421 p8448 p5391 p8463
end
end Assembly
