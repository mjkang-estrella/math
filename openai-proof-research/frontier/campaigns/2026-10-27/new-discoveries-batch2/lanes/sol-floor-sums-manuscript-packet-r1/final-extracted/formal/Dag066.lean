import Dag065
import generated.th_lemma_1
import generated.th_lemma_2
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n11437 (_v : Vars) (_q : Query _v) (h2536 : (e2536 _v)) (h6555 : (e6555 _v)) : (e7489 _v) := by
  have p5391 := n5391 _v _q 
  have p11362 := n11362 _v _q h6555
  have p11132 := n11132 _v _q h2536
  exact FloorCertificate.node_11437 (e2 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p5391 p11362 p11132
theorem n11439 (_v : Vars) (_q : Query _v)  : (e11438 _v) := by
  by_contra hc
  change ¬ ((¬ (e2536 _v)) ∨ (e2310 _v)) at hc
  have h2536 : (e2536 _v) := by
    tauto
  have h6555 : (e6555 _v) := by
    change (¬ (e2310 _v))
    tauto
  have p11437 := n11437 _v _q h2536 h6555
  exact p11437
theorem n11440 (_v : Vars) (_q : Query _v) (h5093 : (e5093 _v)) : (e5093 _v) := by
  exact h5093
theorem n11441 (_v : Vars) (_q : Query _v) (h2592 : (e2592 _v)) (h5093 : (e5093 _v)) : (e7489 _v) := by
  have p8536 := n8536 _v _q h2592
  have p5255 := n5255 _v _q 
  have p10893 := n10893 _v _q 
  have p11440 := n11440 _v _q h5093
  exact FloorCertificate.node_11441 (e2 _v) (e7 _v) (e9 _v) (e45 _v) (e110 _v) p8536 p5255 p10893 p11440
theorem n11443 (_v : Vars) (_q : Query _v)  : (e11442 _v) := by
  by_contra hc
  change ¬ ((¬ (e2592 _v)) ∨ (e13 _v)) at hc
  have h2592 : (e2592 _v) := by
    tauto
  have h5093 : (e5093 _v) := by
    change (¬ (e13 _v))
    tauto
  have p11441 := n11441 _v _q h2592 h5093
  exact p11441
theorem n11444 (_v : Vars) (_q : Query _v) (h8038 : (e8038 _v)) : (e6579 _v) := by
  have p11375 := n11375 _v _q 
  have p11424 := n11424 _v _q h8038
  exact FloorCertificate.node_11444 (e2 _v) (e7 _v) (e9 _v) (e110 _v) p11375 p11424
theorem n11445 (_v : Vars) (_q : Query _v) (h6571 : (e6571 _v)) : (e7807 _v) := by
  have p8451 := n8451 _v _q 
  have p8447 := n8447 _v _q h6571
  simp only [e2303, e2358, e6571, e7807, e8450] at *
  tauto
theorem n11446 (_v : Vars) (_q : Query _v) (h6571 : (e6571 _v)) (h8038 : (e8038 _v)) : (e6772 _v) := by
  have p8602 := n8602 _v _q h8038
  have p11445 := n11445 _v _q h6571
  exact FloorCertificate.node_11446 (e2 _v) (e7 _v) (e9 _v) (e45 _v) (e110 _v) p8602 p11445
theorem n11447 (_v : Vars) (_q : Query _v) (h2799 : (e2799 _v)) (h5093 : (e5093 _v)) : (e7489 _v) := by
  have p10893 := n10893 _v _q 
  have p11375 := n11375 _v _q 
  have p8511 := n8511 _v _q h2799
  have p11440 := n11440 _v _q h5093
  exact FloorCertificate.node_11447 (e2 _v) (e7 _v) (e9 _v) (e45 _v) (e110 _v) p10893 p11375 p8511 p11440
theorem n11449 (_v : Vars) (_q : Query _v)  : (e11448 _v) := by
  by_contra hc
  change ¬ ((¬ (e2799 _v)) ∨ (e13 _v)) at hc
  have h2799 : (e2799 _v) := by
    tauto
  have h5093 : (e5093 _v) := by
    change (¬ (e13 _v))
    tauto
  have p11447 := n11447 _v _q h2799 h5093
  exact p11447
theorem n11450 (_v : Vars) (_q : Query _v)  : (e8495 _v) := by
  simp only [e7688, e7691, e7698, e7699, e7700, e8495] at *
  tauto
theorem n11451 (_v : Vars) (_q : Query _v) (h7698 : (e7698 _v)) : (e7698 _v) := by
  exact h7698
theorem n11452 (_v : Vars) (_q : Query _v) (h7698 : (e7698 _v)) : (e7700 _v) := by
  have p11450 := n11450 _v _q 
  have p11451 := n11451 _v _q h7698
  simp only [e7688, e7691, e7698, e7699, e7700, e8495] at *
  tauto
theorem n11453 (_v : Vars) (_q : Query _v) (h2482 : (e2482 _v)) (h6531 : (e6531 _v)) : (e7489 _v) := by
  have p11358 := n11358 _v _q h6531
  have p5391 := n5391 _v _q 
  have p10888 := n10888 _v _q h2482
  exact FloorCertificate.node_11453 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) p11358 p5391 p10888
theorem n11455 (_v : Vars) (_q : Query _v)  : (e11454 _v) := by
  by_contra hc
  change ¬ ((¬ (e2482 _v)) ∨ (e2254 _v)) at hc
  have h2482 : (e2482 _v) := by
    tauto
  have h6531 : (e6531 _v) := by
    change (¬ (e2254 _v))
    tauto
  have p11453 := n11453 _v _q h2482 h6531
  exact p11453
theorem n11456 (_v : Vars) (_q : Query _v) (h6555 : (e6555 _v)) : (e6454 _v) := by
  have p11362 := n11362 _v _q h6555
  have p10896 := n10896 _v _q 
  exact FloorCertificate.node_11456 (e2 _v) (e9 _v) (e17 _v) (e110 _v) p11362 p10896
theorem n11457 (_v : Vars) (_q : Query _v) (h2691 : (e2691 _v)) : (e2691 _v) := by
  exact h2691
theorem n11458 (_v : Vars) (_q : Query _v) (h6746 : (e6746 _v)) : (e6746 _v) := by
  exact h6746
theorem n11459 (_v : Vars) (_q : Query _v) (h2691 : (e2691 _v)) (h6746 : (e6746 _v)) : (e7489 _v) := by
  have p5257 := n5257 _v _q 
  have p11457 := n11457 _v _q h2691
  have p11458 := n11458 _v _q h6746
  exact FloorCertificate.node_11459 (e2 _v) (e7 _v) (e9 _v) (e45 _v) (e110 _v) p5257 p11457 p11458
theorem n11461 (_v : Vars) (_q : Query _v)  : (e11460 _v) := by
  by_contra hc
  change ¬ ((¬ (e2691 _v)) ∨ (e2740 _v)) at hc
  have h2691 : (e2691 _v) := by
    tauto
  have h6746 : (e6746 _v) := by
    change (¬ (e2740 _v))
    tauto
  have p11459 := n11459 _v _q h2691 h6746
  exact p11459
theorem n11462 (_v : Vars) (_q : Query _v) (h7742 : (e7742 _v)) : (e7742 _v) := by
  exact h7742
theorem n11463 (_v : Vars) (_q : Query _v) (h2371 : (e2371 _v)) (h7742 : (e7742 _v)) : (e7489 _v) := by
  have p11462 := n11462 _v _q h7742
  have p10896 := n10896 _v _q 
  have p11400 := n11400 _v _q h2371
  exact FloorCertificate.node_11463 (e2 _v) (e7 _v) (e9 _v) (e110 _v) p11462 p10896 p11400
theorem n11465 (_v : Vars) (_q : Query _v)  : (e11464 _v) := by
  by_contra hc
  change ¬ ((e2132 _v) ∨ (¬ (e2371 _v))) at hc
  have h2371 : (e2371 _v) := by
    tauto
  have h7742 : (e7742 _v) := by
    change (¬ (e2132 _v))
    tauto
  have p11463 := n11463 _v _q h2371 h7742
  exact p11463
theorem n11466 (_v : Vars) (_q : Query _v) (h13 : (e13 _v)) (h7807 : (e7807 _v)) : (e7489 _v) := by
  have p11350 := n11350 _v _q h7807
  have p11396 := n11396 _v _q h13
  have p5257 := n5257 _v _q 
  exact FloorCertificate.node_11466 (e2 _v) (e7 _v) (e9 _v) (e110 _v) p11350 p11396 p5257
theorem n11468 (_v : Vars) (_q : Query _v)  : (e11467 _v) := by
  by_contra hc
  change ¬ ((¬ (e13 _v)) ∨ (e2303 _v)) at hc
  have h13 : (e13 _v) := by
    tauto
  have h7807 : (e7807 _v) := by
    change (¬ (e2303 _v))
    tauto
  have p11466 := n11466 _v _q h13 h7807
  exact p11466
theorem n11469 (_v : Vars) (_q : Query _v) (h7742 : (e7742 _v)) : (e6780 _v) := by
  have p11462 := n11462 _v _q h7742
  have p10893 := n10893 _v _q 
  have p10896 := n10896 _v _q 
  exact FloorCertificate.node_11469 (e2 _v) (e7 _v) (e9 _v) (e45 _v) (e110 _v) p11462 p10893 p10896
theorem n11470 (_v : Vars) (_q : Query _v)  : (e8462 _v) := by
  simp only [e8395, e8398, e8405, e8406, e8407, e8462] at *
  tauto
theorem n11471 (_v : Vars) (_q : Query _v) (h8406 : (e8406 _v)) : (e8406 _v) := by
  exact h8406
theorem n11472 (_v : Vars) (_q : Query _v) (h8406 : (e8406 _v)) : (e8407 _v) := by
  have p11470 := n11470 _v _q 
  have p11471 := n11471 _v _q h8406
  simp only [e8395, e8398, e8405, e8406, e8407, e8462] at *
  tauto
theorem n11473 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e6784 _v) := by
  exact h6784
theorem n11474 (_v : Vars) (_q : Query _v) (h2364 : (e2364 _v)) (h6784 : (e6784 _v)) : (e7489 _v) := by
  have p8527 := n8527 _v _q h2364
  have p11473 := n11473 _v _q h6784
  have p10893 := n10893 _v _q 
  exact FloorCertificate.node_11474 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8527 p11473 p10893
theorem n11476 (_v : Vars) (_q : Query _v)  : (e11475 _v) := by
  by_contra hc
  change ¬ ((e2793 _v) ∨ (¬ (e2364 _v))) at hc
  have h2364 : (e2364 _v) := by
    tauto
  have h6784 : (e6784 _v) := by
    change (¬ (e2793 _v))
    tauto
  have p11474 := n11474 _v _q h2364 h6784
  exact p11474
theorem n11477 (_v : Vars) (_q : Query _v) (h2132 : (e2132 _v)) (h5093 : (e5093 _v)) : (e7489 _v) := by
  have p5255 := n5255 _v _q 
  have p11440 := n11440 _v _q h5093
  have p11349 := n11349 _v _q h2132
  exact FloorCertificate.node_11477 (e2 _v) (e7 _v) (e9 _v) (e110 _v) p5255 p11440 p11349
theorem n11479 (_v : Vars) (_q : Query _v)  : (e11478 _v) := by
  by_contra hc
  change ¬ ((e13 _v) ∨ (¬ (e2132 _v))) at hc
  have h2132 : (e2132 _v) := by
    tauto
  have h5093 : (e5093 _v) := by
    change (¬ (e13 _v))
    tauto
  have p11477 := n11477 _v _q h2132 h5093
  exact p11477
theorem n11482 (_v : Vars) (_q : Query _v)  : (e11481 _v) := by
  have p8139 := n8139 _v _q 
  have p258 := n258 _v _q 
  exact FloorCertificate.node_11482 (e17 _v) p8139 p258
theorem n11483 (_v : Vars) (_q : Query _v) (h2793 : (e2793 _v)) (h2799 : (e2799 _v)) : (e7489 _v) := by
  have p8139 := n8139 _v _q 
  have p11482 := n11482 _v _q 
  have p8510 := n8510 _v _q h2793
  have p8514 := n8514 _v _q h2799
  exact FloorCertificate.node_11483 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8139 p11482 p8510 p8514
theorem n11484 (_v : Vars) (_q : Query _v) (h2592 : (e2592 _v)) (h6746 : (e6746 _v)) : (e7489 _v) := by
  have p8536 := n8536 _v _q h2592
  have p5257 := n5257 _v _q 
  have p5255 := n5255 _v _q 
  have p11458 := n11458 _v _q h6746
  exact FloorCertificate.node_11484 (e2 _v) (e7 _v) (e9 _v) (e45 _v) (e110 _v) p8536 p5257 p5255 p11458
theorem n11486 (_v : Vars) (_q : Query _v)  : (e11485 _v) := by
  by_contra hc
  change ¬ ((e2740 _v) ∨ (¬ (e2592 _v))) at hc
  have h2592 : (e2592 _v) := by
    tauto
  have h6746 : (e6746 _v) := by
    change (¬ (e2740 _v))
    tauto
  have p11484 := n11484 _v _q h2592 h6746
  exact p11484
theorem n11487 (_v : Vars) (_q : Query _v) (h5138 : (e5138 _v)) : (e5138 _v) := by
  exact h5138
theorem n11488 (_v : Vars) (_q : Query _v) (h2303 : (e2303 _v)) (h5138 : (e5138 _v)) : (e7489 _v) := by
  have p5255 := n5255 _v _q 
  have p8448 := n8448 _v _q h2303
  have p5391 := n5391 _v _q 
  have p11487 := n11487 _v _q h5138
  exact FloorCertificate.node_11488 (e2 _v) (e9 _v) (e45 _v) (e110 _v) p5255 p8448 p5391 p11487
theorem n11490 (_v : Vars) (_q : Query _v)  : (e11489 _v) := by
  by_contra hc
  change ¬ ((e79 _v) ∨ (¬ (e2303 _v))) at hc
  have h2303 : (e2303 _v) := by
    tauto
  have h5138 : (e5138 _v) := by
    change (¬ (e79 _v))
    tauto
  have p11488 := n11488 _v _q h2303 h5138
  exact p11488
theorem n11491 (_v : Vars) (_q : Query _v) (h2475 : (e2475 _v)) (h8310 : (e8310 _v)) : (e7489 _v) := by
  have p8457 := n8457 _v _q h2475
  have p11384 := n11384 _v _q h8310
  have p5257 := n5257 _v _q 
  exact FloorCertificate.node_11491 (e2 _v) (e7 _v) (e45 _v) (e110 _v) p8457 p11384 p5257
theorem n11493 (_v : Vars) (_q : Query _v)  : (e11492 _v) := by
  by_contra hc
  change ¬ ((e2529 _v) ∨ (¬ (e2475 _v))) at hc
  have h2475 : (e2475 _v) := by
    tauto
  have h8310 : (e8310 _v) := by
    change (¬ (e2529 _v))
    tauto
  have p11491 := n11491 _v _q h2475 h8310
  exact p11491
theorem n11494 (_v : Vars) (_q : Query _v) (h2585 : (e2585 _v)) (h2592 : (e2592 _v)) : (e7489 _v) := by
  have p8139 := n8139 _v _q 
  have p8535 := n8535 _v _q h2585
  have p8539 := n8539 _v _q h2592
  have p11482 := n11482 _v _q 
  exact FloorCertificate.node_11494 (e2 _v) (e7 _v) (e17 _v) (e45 _v) (e110 _v) p8139 p8535 p8539 p11482
theorem n11495 (_v : Vars) (_q : Query _v) (h6636 : (e6636 _v)) : (e6423 _v) := by
  have p11031 := n11031 _v _q h6636
  have p10893 := n10893 _v _q 
  exact FloorCertificate.node_11495 (e2 _v) (e7 _v) (e17 _v) (e45 _v) p11031 p10893
end
end Assembly
