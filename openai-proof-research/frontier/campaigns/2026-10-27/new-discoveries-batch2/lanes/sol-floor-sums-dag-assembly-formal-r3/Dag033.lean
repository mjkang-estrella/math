import Dag032
import generated.th_lemma_0
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n8448 (_v : Vars) (_q : Query _v) (h2303 : (e2303 _v)) : (e2303 _v) := by
  exact h2303
theorem n8449 (_v : Vars) (_q : Query _v) (h2303 : (e2303 _v)) (h6571 : (e6571 _v)) : (e7489 _v) := by
  have p8447 := n8447 _v _q h6571
  have p8448 := n8448 _v _q h2303
  have p4016 := n4016 _v _q 
  exact FloorCertificate.node_8449 (e2 _v) (e7 _v) (e9 _v) (e110 _v) p8447 p8448 p4016
theorem n8451 (_v : Vars) (_q : Query _v)  : (e8450 _v) := by
  by_contra hc
  change ¬ ((¬ (e2303 _v)) ∨ (e2358 _v)) at hc
  have h2303 : (e2303 _v) := by
    tauto
  have h6571 : (e6571 _v) := by
    change (¬ (e2358 _v))
    tauto
  have p8449 := n8449 _v _q h2303 h6571
  exact p8449
theorem n8452 (_v : Vars) (_q : Query _v) (h6423 : (e6423 _v)) : (e6423 _v) := by
  exact h6423
theorem n8453 (_v : Vars) (_q : Query _v) (h2771 : (e2771 _v)) (h6423 : (e6423 _v)) : (e7489 _v) := by
  have p4946 := n4946 _v _q 
  have p8415 := n8415 _v _q h2771
  have p8452 := n8452 _v _q h6423
  have p4951 := n4951 _v _q 
  have p3130 := n3130 _v _q 
  exact FloorCertificate.node_8453 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p4946 p8415 p8452 p4951 p3130
theorem n8455 (_v : Vars) (_q : Query _v)  : (e8454 _v) := by
  by_contra hc
  change ¬ ((e1995 _v) ∨ (¬ (e2771 _v))) at hc
  have h2771 : (e2771 _v) := by
    tauto
  have h6423 : (e6423 _v) := by
    change (¬ (e1995 _v))
    tauto
  have p8453 := n8453 _v _q h2771 h6423
  exact p8453
theorem n8457 (_v : Vars) (_q : Query _v) (h2475 : (e2475 _v)) : (e2475 _v) := by
  exact h2475
theorem n8458 (_v : Vars) (_q : Query _v) (h6772 : (e6772 _v)) : (e6772 _v) := by
  exact h6772
theorem n8459 (_v : Vars) (_q : Query _v) (h2303 : (e2303 _v)) (h2475 : (e2475 _v)) (h6772 : (e6772 _v)) : (e7489 _v) := by
  have p8448 := n8448 _v _q h2303
  have p8457 := n8457 _v _q h2475
  have p8458 := n8458 _v _q h6772
  exact FloorCertificate.node_8459 (e2 _v) (e7 _v) (e9 _v) (e45 _v) (e110 _v) p8448 p8457 p8458
theorem n8461 (_v : Vars) (_q : Query _v)  : (e8460 _v) := by
  by_contra hc
  change ¬ ((¬ (e2475 _v)) ∨ (¬ (e2303 _v)) ∨ (e2787 _v)) at hc
  have h2303 : (e2303 _v) := by
    tauto
  have h2475 : (e2475 _v) := by
    tauto
  have h6772 : (e6772 _v) := by
    change (¬ (e2787 _v))
    tauto
  have p8459 := n8459 _v _q h2303 h2475 h6772
  exact p8459
theorem n8463 (_v : Vars) (_q : Query _v) (h6525 : (e6525 _v)) : (e6525 _v) := by
  exact h6525
theorem n8464 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) : (e2351 _v) := by
  exact h2351
theorem n8465 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h6525 : (e6525 _v)) : (e7489 _v) := by
  have p8463 := n8463 _v _q h6525
  have p3130 := n3130 _v _q 
  have p8464 := n8464 _v _q h2351
  exact FloorCertificate.node_8465 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e110 _v) p8463 p3130 p8464
theorem n8467 (_v : Vars) (_q : Query _v)  : (e8466 _v) := by
  by_contra hc
  change ¬ ((e2242 _v) ∨ (¬ (e2351 _v))) at hc
  have h2351 : (e2351 _v) := by
    tauto
  have h6525 : (e6525 _v) := by
    change (¬ (e2242 _v))
    tauto
  have p8465 := n8465 _v _q h2351 h6525
  exact p8465
theorem n8469 (_v : Vars) (_q : Query _v) (h214 : (e214 _v)) : (e214 _v) := by
  exact h214
theorem n8470 (_v : Vars) (_q : Query _v) (h214 : (e214 _v)) (h5362 : (e5362 _v)) : (e7489 _v) := by
  have p7488 := n7488 _v _q h5362
  have p8469 := n8469 _v _q h214
  have p4016 := n4016 _v _q 
  exact FloorCertificate.node_8470 (e2 _v) (e7 _v) (e9 _v) (e45 _v) (e110 _v) p7488 p8469 p4016
theorem n8472 (_v : Vars) (_q : Query _v)  : (e8471 _v) := by
  by_contra hc
  change ¬ ((¬ (e214 _v)) ∨ (e436 _v)) at hc
  have h214 : (e214 _v) := by
    tauto
  have h5362 : (e5362 _v) := by
    change (¬ (e436 _v))
    tauto
  have p8470 := n8470 _v _q h214 h5362
  exact p8470
theorem n8475 (_v : Vars) (_q : Query _v) (h2125 : (e2125 _v)) : (e2125 _v) := by
  exact h2125
theorem n8476 (_v : Vars) (_q : Query _v) (h2125 : (e2125 _v)) (h6454 : (e6454 _v)) : (e7489 _v) := by
  have p4016 := n4016 _v _q 
  have p8475 := n8475 _v _q h2125
  have p8430 := n8430 _v _q h6454
  exact FloorCertificate.node_8476 (e2 _v) (e7 _v) (e17 _v) (e110 _v) p4016 p8475 p8430
theorem n8478 (_v : Vars) (_q : Query _v)  : (e8477 _v) := by
  by_contra hc
  change ¬ ((e2061 _v) ∨ (¬ (e2125 _v))) at hc
  have h2125 : (e2125 _v) := by
    tauto
  have h6454 : (e6454 _v) := by
    change (¬ (e2061 _v))
    tauto
  have p8476 := n8476 _v _q h2125 h6454
  exact p8476
theorem n8481 (_v : Vars) (_q : Query _v)  : (e8480 _v) := by
  simp only [e4236, e4237, e7756, e7757, e7758, e8480] at *
  tauto
theorem n8485 (_v : Vars) (_q : Query _v)  : (e4956 _v) := by
  simp only [e4567, e4568, e4572, e4573, e4574, e4956] at *
  tauto
theorem n8486 (_v : Vars) (_q : Query _v) (h4572 : (e4572 _v)) : (e4572 _v) := by
  exact h4572
theorem n8487 (_v : Vars) (_q : Query _v) (h4572 : (e4572 _v)) : (e4574 _v) := by
  have p8485 := n8485 _v _q 
  have p8486 := n8486 _v _q h4572
  simp only [e4567, e4568, e4572, e4573, e4574, e4956] at *
  tauto
theorem n8493 (_v : Vars) (_q : Query _v)  : (e8492 _v) := by
  simp only [e4627, e4628, e8112, e8113, e8114, e8492] at *
  tauto
theorem n8510 (_v : Vars) (_q : Query _v) (h2793 : (e2793 _v)) : (e8509 _v) := by
  have p8139 := n8139 _v _q 
  have p8426 := n8426 _v _q h2793
  exact FloorCertificate.node_8510 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8139 p8426
theorem n8511 (_v : Vars) (_q : Query _v) (h2799 : (e2799 _v)) : (e2799 _v) := by
  exact h2799
theorem n8514 (_v : Vars) (_q : Query _v) (h2799 : (e2799 _v)) : (e8513 _v) := by
  have p8139 := n8139 _v _q 
  have p8511 := n8511 _v _q h2799
  exact FloorCertificate.node_8514 (e2 _v) (e7 _v) (e9 _v) (e45 _v) (e110 _v) p8139 p8511
theorem n8521 (_v : Vars) (_q : Query _v) (h2680 : (e2680 _v)) : (e2680 _v) := by
  exact h2680
theorem n8522 (_v : Vars) (_q : Query _v) (h2680 : (e2680 _v)) (h5362 : (e5362 _v)) : (e7489 _v) := by
  have p7488 := n7488 _v _q h5362
  have p3130 := n3130 _v _q 
  have p8521 := n8521 _v _q h2680
  exact FloorCertificate.node_8522 (e2 _v) (e7 _v) (e9 _v) (e45 _v) (e110 _v) p7488 p3130 p8521
theorem n8524 (_v : Vars) (_q : Query _v)  : (e8523 _v) := by
  by_contra hc
  change ¬ ((¬ (e2680 _v)) ∨ (e436 _v)) at hc
  have h2680 : (e2680 _v) := by
    tauto
  have h5362 : (e5362 _v) := by
    change (¬ (e436 _v))
    tauto
  have p8522 := n8522 _v _q h2680 h5362
  exact p8522
theorem n8526 (_v : Vars) (_q : Query _v)  : (e8525 _v) := by
  simp only [e4587, e4588, e8070, e8071, e8072, e8525] at *
  tauto
theorem n8527 (_v : Vars) (_q : Query _v) (h2364 : (e2364 _v)) : (e2364 _v) := by
  exact h2364
theorem n8528 (_v : Vars) (_q : Query _v) (h2303 : (e2303 _v)) (h2364 : (e2364 _v)) (h6423 : (e6423 _v)) : (e7489 _v) := by
  have p8452 := n8452 _v _q h6423
  have p8527 := n8527 _v _q h2364
  have p8448 := n8448 _v _q h2303
  exact FloorCertificate.node_8528 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e110 _v) p8452 p8527 p8448
theorem n8530 (_v : Vars) (_q : Query _v)  : (e8529 _v) := by
  by_contra hc
  change ¬ ((¬ (e2303 _v)) ∨ (e1995 _v) ∨ (¬ (e2364 _v))) at hc
  have h2303 : (e2303 _v) := by
    tauto
  have h2364 : (e2364 _v) := by
    tauto
  have h6423 : (e6423 _v) := by
    change (¬ (e1995 _v))
    tauto
  have p8528 := n8528 _v _q h2303 h2364 h6423
  exact p8528
theorem n8532 (_v : Vars) (_q : Query _v) (h2585 : (e2585 _v)) : (e2585 _v) := by
  exact h2585
theorem n8535 (_v : Vars) (_q : Query _v) (h2585 : (e2585 _v)) : (e8534 _v) := by
  have p8139 := n8139 _v _q 
  have p8532 := n8532 _v _q h2585
  exact FloorCertificate.node_8535 (e2 _v) (e7 _v) (e17 _v) (e45 _v) (e110 _v) p8139 p8532
theorem n8536 (_v : Vars) (_q : Query _v) (h2592 : (e2592 _v)) : (e2592 _v) := by
  exact h2592
theorem n8539 (_v : Vars) (_q : Query _v) (h2592 : (e2592 _v)) : (e8538 _v) := by
  have p8139 := n8139 _v _q 
  have p8536 := n8536 _v _q h2592
  exact FloorCertificate.node_8539 (e2 _v) (e7 _v) (e45 _v) (e110 _v) p8139 p8536
theorem n8544 (_v : Vars) (_q : Query _v) (h6549 : (e6549 _v)) : (e6549 _v) := by
  exact h6549
theorem n8545 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h6549 : (e6549 _v)) : (e7489 _v) := by
  have p8544 := n8544 _v _q h6549
  have p4016 := n4016 _v _q 
  have p8464 := n8464 _v _q h2351
  exact FloorCertificate.node_8545 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e110 _v) p8544 p4016 p8464
theorem n8547 (_v : Vars) (_q : Query _v)  : (e8546 _v) := by
  by_contra hc
  change ¬ ((e2296 _v) ∨ (¬ (e2351 _v))) at hc
  have h2351 : (e2351 _v) := by
    tauto
  have h6549 : (e6549 _v) := by
    change (¬ (e2296 _v))
    tauto
  have p8545 := n8545 _v _q h2351 h6549
  exact p8545
theorem n8548 (_v : Vars) (_q : Query _v) (h2529 : (e2529 _v)) : (e2529 _v) := by
  exact h2529
theorem n8549 (_v : Vars) (_q : Query _v) (h5195 : (e5195 _v)) : (e5195 _v) := by
  exact h5195
theorem n8550 (_v : Vars) (_q : Query _v) (h2529 : (e2529 _v)) (h5195 : (e5195 _v)) : (e7489 _v) := by
  have p8548 := n8548 _v _q h2529
  have p4016 := n4016 _v _q 
  have p8549 := n8549 _v _q h5195
  exact FloorCertificate.node_8550 (e2 _v) (e7 _v) (e45 _v) (e110 _v) p8548 p4016 p8549
end
end Assembly
