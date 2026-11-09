import Dag064
import generated.th_lemma_1
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n11382 (_v : Vars) (_q : Query _v)  : (e11381 _v) := by
  by_contra hc
  change ¬ ((¬ (e2139 _v)) ∨ (e2377 _v)) at hc
  have h2139 : (e2139 _v) := by
    tauto
  have h6591 : (e6591 _v) := by
    change (¬ (e2377 _v))
    tauto
  have p11380 := n11380 _v _q h2139 h6591
  exact p11380
theorem n11383 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e6501 _v) := by
  have p11375 := n11375 _v _q 
  have p11376 := n11376 _v _q 
  have p11345 := n11345 _v _q h6591
  exact FloorCertificate.node_11383 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e110 _v) p11375 p11376 p11345
theorem n11384 (_v : Vars) (_q : Query _v) (h8310 : (e8310 _v)) : (e8310 _v) := by
  exact h8310
theorem n11385 (_v : Vars) (_q : Query _v) (h2303 : (e2303 _v)) (h8310 : (e8310 _v)) : (e7489 _v) := by
  have p11384 := n11384 _v _q h8310
  have p5391 := n5391 _v _q 
  have p8448 := n8448 _v _q h2303
  exact FloorCertificate.node_11385 (e2 _v) (e9 _v) (e45 _v) (e110 _v) p11384 p5391 p8448
theorem n11387 (_v : Vars) (_q : Query _v)  : (e11386 _v) := by
  by_contra hc
  change ¬ ((¬ (e2303 _v)) ∨ (e2529 _v)) at hc
  have h2303 : (e2303 _v) := by
    tauto
  have h8310 : (e8310 _v) := by
    change (¬ (e2529 _v))
    tauto
  have p11385 := n11385 _v _q h2303 h8310
  exact p11385
theorem n11388 (_v : Vars) (_q : Query _v) (h2254 : (e2254 _v)) : (e2254 _v) := by
  exact h2254
theorem n11389 (_v : Vars) (_q : Query _v) (h2254 : (e2254 _v)) (h6732 : (e6732 _v)) : (e7489 _v) := by
  have p11388 := n11388 _v _q h2254
  have p10893 := n10893 _v _q 
  have p11370 := n11370 _v _q h6732
  exact FloorCertificate.node_11389 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) p11388 p10893 p11370
theorem n11391 (_v : Vars) (_q : Query _v)  : (e11390 _v) := by
  by_contra hc
  change ¬ ((e2697 _v) ∨ (¬ (e2254 _v))) at hc
  have h2254 : (e2254 _v) := by
    tauto
  have h6732 : (e6732 _v) := by
    change (¬ (e2697 _v))
    tauto
  have p11389 := n11389 _v _q h2254 h6732
  exact p11389
theorem n11392 (_v : Vars) (_q : Query _v) (h2697 : (e2697 _v)) : (e2697 _v) := by
  exact h2697
theorem n11393 (_v : Vars) (_q : Query _v) (h2697 : (e2697 _v)) (h6591 : (e6591 _v)) : (e7489 _v) := by
  have p11392 := n11392 _v _q h2697
  have p5255 := n5255 _v _q 
  have p5391 := n5391 _v _q 
  have p11345 := n11345 _v _q h6591
  exact FloorCertificate.node_11393 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p11392 p5255 p5391 p11345
theorem n11395 (_v : Vars) (_q : Query _v)  : (e11394 _v) := by
  by_contra hc
  change ¬ ((e2377 _v) ∨ (¬ (e2697 _v))) at hc
  have h2697 : (e2697 _v) := by
    tauto
  have h6591 : (e6591 _v) := by
    change (¬ (e2377 _v))
    tauto
  have p11393 := n11393 _v _q h2697 h6591
  exact p11393
theorem n11396 (_v : Vars) (_q : Query _v) (h13 : (e13 _v)) : (e13 _v) := by
  exact h13
theorem n11397 (_v : Vars) (_q : Query _v) (h13 : (e13 _v)) (h8038 : (e8038 _v)) : (e7489 _v) := by
  have p11396 := n11396 _v _q h13
  have p5391 := n5391 _v _q 
  have p8602 := n8602 _v _q h8038
  exact FloorCertificate.node_11397 (e2 _v) (e7 _v) (e9 _v) (e45 _v) p11396 p5391 p8602
theorem n11399 (_v : Vars) (_q : Query _v)  : (e11398 _v) := by
  by_contra hc
  change ¬ ((¬ (e13 _v)) ∨ (e2475 _v)) at hc
  have h13 : (e13 _v) := by
    tauto
  have h8038 : (e8038 _v) := by
    change (¬ (e2475 _v))
    tauto
  have p11397 := n11397 _v _q h13 h8038
  exact p11397
theorem n11400 (_v : Vars) (_q : Query _v) (h2371 : (e2371 _v)) : (e2371 _v) := by
  exact h2371
theorem n11401 (_v : Vars) (_q : Query _v) (h6672 : (e6672 _v)) : (e6672 _v) := by
  exact h6672
theorem n11402 (_v : Vars) (_q : Query _v) (h2371 : (e2371 _v)) (h6672 : (e6672 _v)) : (e7489 _v) := by
  have p11400 := n11400 _v _q h2371
  have p5391 := n5391 _v _q 
  have p11401 := n11401 _v _q h6672
  exact FloorCertificate.node_11402 (e2 _v) (e7 _v) (e9 _v) (e45 _v) (e110 _v) p11400 p5391 p11401
theorem n11404 (_v : Vars) (_q : Query _v)  : (e11403 _v) := by
  by_contra hc
  change ¬ ((e2592 _v) ∨ (¬ (e2371 _v))) at hc
  have h2371 : (e2371 _v) := by
    tauto
  have h6672 : (e6672 _v) := by
    change (¬ (e2592 _v))
    tauto
  have p11402 := n11402 _v _q h2371 h6672
  exact p11402
theorem n11405 (_v : Vars) (_q : Query _v) (h2296 : (e2296 _v)) : (e2585 _v) := by
  have p8583 := n8583 _v _q h2296
  have p5257 := n5257 _v _q 
  have p5255 := n5255 _v _q 
  have p10893 := n10893 _v _q 
  exact FloorCertificate.node_11405 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8583 p5257 p5255 p10893
theorem n11406 (_v : Vars) (_q : Query _v)  : (e8474 _v) := by
  simp only [e7645, e7648, e7655, e7656, e7657, e8474] at *
  tauto
theorem n11407 (_v : Vars) (_q : Query _v) (h7655 : (e7655 _v)) : (e7655 _v) := by
  exact h7655
theorem n11408 (_v : Vars) (_q : Query _v) (h7655 : (e7655 _v)) : (e7657 _v) := by
  have p11406 := n11406 _v _q 
  have p11407 := n11407 _v _q h7655
  simp only [e7645, e7648, e7655, e7656, e7657, e8474] at *
  tauto
theorem n11409 (_v : Vars) (_q : Query _v) (h2061 : (e2061 _v)) : (e2061 _v) := by
  exact h2061
theorem n11410 (_v : Vars) (_q : Query _v) (h2061 : (e2061 _v)) (h6423 : (e6423 _v)) : (e7489 _v) := by
  have p11409 := n11409 _v _q h2061
  have p5257 := n5257 _v _q 
  have p8452 := n8452 _v _q h6423
  exact FloorCertificate.node_11410 (e2 _v) (e7 _v) (e17 _v) (e110 _v) p11409 p5257 p8452
theorem n11412 (_v : Vars) (_q : Query _v)  : (e11411 _v) := by
  by_contra hc
  change ¬ ((e1995 _v) ∨ (¬ (e2061 _v))) at hc
  have h2061 : (e2061 _v) := by
    tauto
  have h6423 : (e6423 _v) := by
    change (¬ (e1995 _v))
    tauto
  have p11410 := n11410 _v _q h2061 h6423
  exact p11410
theorem n11413 (_v : Vars) (_q : Query _v) (h6575 : (e6575 _v)) : (e6575 _v) := by
  exact h6575
theorem n11414 (_v : Vars) (_q : Query _v) (h474 : (e474 _v)) : (e474 _v) := by
  exact h474
theorem n11415 (_v : Vars) (_q : Query _v) (h474 : (e474 _v)) (h6575 : (e6575 _v)) : (e7489 _v) := by
  have p11413 := n11413 _v _q h6575
  have p5391 := n5391 _v _q 
  have p11414 := n11414 _v _q h474
  exact FloorCertificate.node_11415 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p11413 p5391 p11414
theorem n11417 (_v : Vars) (_q : Query _v)  : (e11416 _v) := by
  by_contra hc
  change ¬ ((e2351 _v) ∨ (¬ (e474 _v))) at hc
  have h474 : (e474 _v) := by
    tauto
  have h6575 : (e6575 _v) := by
    change (¬ (e2351 _v))
    tauto
  have p11415 := n11415 _v _q h474 h6575
  exact p11415
theorem n11418 (_v : Vars) (_q : Query _v)  : (e7611 _v) := by
  simp only [e7606, e7607, e7608, e7609, e7610, e7611] at *
  tauto
theorem n11419 (_v : Vars) (_q : Query _v) (h7607 : (e7607 _v)) : (e7607 _v) := by
  exact h7607
theorem n11420 (_v : Vars) (_q : Query _v) (h7607 : (e7607 _v)) : (e7610 _v) := by
  have p11418 := n11418 _v _q 
  have p11419 := n11419 _v _q h7607
  simp only [e7606, e7607, e7608, e7609, e7610, e7611] at *
  tauto
theorem n11421 (_v : Vars) (_q : Query _v)  : (e8482 _v) := by
  simp only [e8335, e8338, e8345, e8346, e8347, e8482] at *
  tauto
theorem n11422 (_v : Vars) (_q : Query _v) (h8345 : (e8345 _v)) : (e8345 _v) := by
  exact h8345
theorem n11423 (_v : Vars) (_q : Query _v) (h8345 : (e8345 _v)) : (e8347 _v) := by
  have p11421 := n11421 _v _q 
  have p11422 := n11422 _v _q h8345
  simp only [e8335, e8338, e8345, e8346, e8347, e8482] at *
  tauto
theorem n11424 (_v : Vars) (_q : Query _v) (h8038 : (e8038 _v)) : (e5093 _v) := by
  have p8602 := n8602 _v _q h8038
  have p5391 := n5391 _v _q 
  exact FloorCertificate.node_11424 (e2 _v) (e7 _v) (e9 _v) (e45 _v) p8602 p5391
theorem n11425 (_v : Vars) (_q : Query _v) (h8038 : (e8038 _v)) : (e6724 _v) := by
  have p11424 := n11424 _v _q h8038
  have p10893 := n10893 _v _q 
  exact FloorCertificate.node_11425 (e2 _v) (e7 _v) (e9 _v) (e45 _v) p11424 p10893
theorem n11426 (_v : Vars) (_q : Query _v) (h2740 : (e2740 _v)) : (e2740 _v) := by
  exact h2740
theorem n11427 (_v : Vars) (_q : Query _v) (h2740 : (e2740 _v)) (h7807 : (e7807 _v)) : (e7489 _v) := by
  have p10893 := n10893 _v _q 
  have p11350 := n11350 _v _q h7807
  have p11426 := n11426 _v _q h2740
  exact FloorCertificate.node_11427 (e2 _v) (e9 _v) (e45 _v) (e110 _v) p10893 p11350 p11426
theorem n11429 (_v : Vars) (_q : Query _v)  : (e11428 _v) := by
  by_contra hc
  change ¬ ((¬ (e2740 _v)) ∨ (e2303 _v)) at hc
  have h2740 : (e2740 _v) := by
    tauto
  have h7807 : (e7807 _v) := by
    change (¬ (e2303 _v))
    tauto
  have p11427 := n11427 _v _q h2740 h7807
  exact p11427
theorem n11430 (_v : Vars) (_q : Query _v) (h2787 : (e2787 _v)) : (e2787 _v) := by
  exact h2787
theorem n11431 (_v : Vars) (_q : Query _v) (h2787 : (e2787 _v)) (h6571 : (e6571 _v)) (h8310 : (e8310 _v)) : (e7489 _v) := by
  have p11384 := n11384 _v _q h8310
  have p4016 := n4016 _v _q 
  have p5257 := n5257 _v _q 
  have p11430 := n11430 _v _q h2787
  have p8447 := n8447 _v _q h6571
  exact FloorCertificate.node_11431 (e2 _v) (e7 _v) (e9 _v) (e45 _v) (e110 _v) p11384 p4016 p5257 p11430 p8447
theorem n11433 (_v : Vars) (_q : Query _v)  : (e11432 _v) := by
  by_contra hc
  change ¬ ((¬ (e2787 _v)) ∨ (e2529 _v) ∨ (e2358 _v)) at hc
  have h2787 : (e2787 _v) := by
    tauto
  have h6571 : (e6571 _v) := by
    change (¬ (e2358 _v))
    tauto
  have h8310 : (e8310 _v) := by
    change (¬ (e2529 _v))
    tauto
  have p11431 := n11431 _v _q h2787 h6571 h8310
  exact p11431
theorem n11434 (_v : Vars) (_q : Query _v) (h2125 : (e2125 _v)) (h6676 : (e6676 _v)) : (e7489 _v) := by
  have p10943 := n10943 _v _q h6676
  have p8475 := n8475 _v _q h2125
  have p10893 := n10893 _v _q 
  exact FloorCertificate.node_11434 (e2 _v) (e7 _v) (e17 _v) (e45 _v) (e110 _v) p10943 p8475 p10893
theorem n11436 (_v : Vars) (_q : Query _v)  : (e11435 _v) := by
  by_contra hc
  change ¬ ((e2585 _v) ∨ (¬ (e2125 _v))) at hc
  have h2125 : (e2125 _v) := by
    tauto
  have h6676 : (e6676 _v) := by
    change (¬ (e2585 _v))
    tauto
  have p11434 := n11434 _v _q h2125 h6676
  exact p11434
end
end Assembly
