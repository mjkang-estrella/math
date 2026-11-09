import Dag063
import generated.th_lemma_1
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n11296 (_v : Vars) (_q : Query _v)  : (e11295 _v) := by
  simp only [e5, e6, e12, e41, e46, e111, e4852, e8315, e8317, e8319, e8320, e8321, e8322, e11292, e11295] at *
  omega
theorem n11304 (_v : Vars) (_q : Query _v)  : (e11303 _v) := by
  have p8329 := n8329 _v _q 
  have p8332 := n8332 _v _q 
  exact (Iff.trans p8329 p8332)
theorem n11306 (_v : Vars) (_q : Query _v)  : (e11305 _v) := by
  simp only [e5, e6, e8, e12, e41, e43, e44, e46, e111, e4870, e8335, e8338, e8342, e8345, e8346, e8347, e8348, e11305] at *
  omega
theorem n11313 (_v : Vars) (_q : Query _v)  : (e11312 _v) := by
  have p4881 := n4881 _v _q 
  have p8353 := n8353 _v _q 
  exact (Iff.trans p4881 p8353)
theorem n11315 (_v : Vars) (_q : Query _v)  : (e11314 _v) := by
  have p11313 := n11313 _v _q 
  change ((e4876 _v) ↔ (e4885 _v)) at p11313
  simp only [e11314, e6743, e8364, p11313]
theorem n11317 (_v : Vars) (_q : Query _v)  : (e11316 _v) := by
  have p8357 := n8357 _v _q 
  have p8360 := n8360 _v _q 
  exact (Iff.trans p8357 p8360)
theorem n11321 (_v : Vars) (_q : Query _v)  : (e11320 _v) := by
  have p4906 := n4906 _v _q 
  have p8370 := n8370 _v _q 
  exact (Iff.trans p4906 p8370)
theorem n11323 (_v : Vars) (_q : Query _v)  : (e11322 _v) := by
  have p11321 := n11321 _v _q 
  change ((e4901 _v) ↔ (e4910 _v)) at p11321
  simp only [e11322, e6785, e8381, p11321]
theorem n11325 (_v : Vars) (_q : Query _v)  : (e11324 _v) := by
  have p8374 := n8374 _v _q 
  have p8377 := n8377 _v _q 
  exact (Iff.trans p8374 p8377)
theorem n11329 (_v : Vars) (_q : Query _v)  : (e11328 _v) := by
  have p8389 := n8389 _v _q 
  have p8392 := n8392 _v _q 
  exact (Iff.trans p8389 p8392)
theorem n11331 (_v : Vars) (_q : Query _v)  : (e11330 _v) := by
  simp only [e5, e6, e8, e10, e12, e41, e46, e111, e266, e267, e4937, e8395, e8398, e8402, e8405, e8406, e8407, e8408, e11330] at *
  omega
theorem n11337 (_v : Vars) (_q : Query _v) (h2402 : (e2402 _v)) (h6501 : (e6501 _v)) : (e7489 _v) := by
  have p5391 := n5391 _v _q 
  have p8554 := n8554 _v _q h6501
  have p8591 := n8591 _v _q h2402
  exact FloorCertificate.node_11337 (e2 _v) (e9 _v) (e17 _v) (e45 _v) p5391 p8554 p8591
theorem n11339 (_v : Vars) (_q : Query _v)  : (e11338 _v) := by
  by_contra hc
  change ¬ ((e2179 _v) ∨ (¬ (e2402 _v))) at hc
  have h2402 : (e2402 _v) := by
    tauto
  have h6501 : (e6501 _v) := by
    change (¬ (e2179 _v))
    tauto
  have p11337 := n11337 _v _q h2402 h6501
  exact p11337
theorem n11340 (_v : Vars) (_q : Query _v) (h6583 : (e6583 _v)) : (e6583 _v) := by
  exact h6583
theorem n11341 (_v : Vars) (_q : Query _v) (h2585 : (e2585 _v)) (h6583 : (e6583 _v)) : (e7489 _v) := by
  have p5391 := n5391 _v _q 
  have p8532 := n8532 _v _q h2585
  have p11340 := n11340 _v _q h6583
  exact FloorCertificate.node_11341 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p5391 p8532 p11340
theorem n11343 (_v : Vars) (_q : Query _v)  : (e11342 _v) := by
  by_contra hc
  change ¬ ((e2364 _v) ∨ (¬ (e2585 _v))) at hc
  have h2585 : (e2585 _v) := by
    tauto
  have h6583 : (e6583 _v) := by
    change (¬ (e2364 _v))
    tauto
  have p11341 := n11341 _v _q h2585 h6583
  exact p11341
theorem n11344 (_v : Vars) (_q : Query _v) (h2746 : (e2746 _v)) : (e2746 _v) := by
  exact h2746
theorem n11345 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e6591 _v) := by
  exact h6591
theorem n11346 (_v : Vars) (_q : Query _v) (h2746 : (e2746 _v)) (h6591 : (e6591 _v)) : (e7489 _v) := by
  have p11344 := n11344 _v _q h2746
  have p5257 := n5257 _v _q 
  have p5255 := n5255 _v _q 
  have p5391 := n5391 _v _q 
  have p11345 := n11345 _v _q h6591
  exact FloorCertificate.node_11346 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p11344 p5257 p5255 p5391 p11345
theorem n11348 (_v : Vars) (_q : Query _v)  : (e11347 _v) := by
  by_contra hc
  change ¬ ((e2377 _v) ∨ (¬ (e2746 _v))) at hc
  have h2746 : (e2746 _v) := by
    tauto
  have h6591 : (e6591 _v) := by
    change (¬ (e2377 _v))
    tauto
  have p11346 := n11346 _v _q h2746 h6591
  exact p11346
theorem n11349 (_v : Vars) (_q : Query _v) (h2132 : (e2132 _v)) : (e2132 _v) := by
  exact h2132
theorem n11350 (_v : Vars) (_q : Query _v) (h7807 : (e7807 _v)) : (e7807 _v) := by
  exact h7807
theorem n11351 (_v : Vars) (_q : Query _v) (h2132 : (e2132 _v)) (h7807 : (e7807 _v)) : (e7489 _v) := by
  have p5257 := n5257 _v _q 
  have p11349 := n11349 _v _q h2132
  have p11350 := n11350 _v _q h7807
  have p5255 := n5255 _v _q 
  exact FloorCertificate.node_11351 (e2 _v) (e7 _v) (e9 _v) (e110 _v) p5257 p11349 p11350 p5255
theorem n11353 (_v : Vars) (_q : Query _v)  : (e11352 _v) := by
  by_contra hc
  change ¬ ((¬ (e2132 _v)) ∨ (e2303 _v)) at hc
  have h2132 : (e2132 _v) := by
    tauto
  have h7807 : (e7807 _v) := by
    change (¬ (e2303 _v))
    tauto
  have p11351 := n11351 _v _q h2132 h7807
  exact p11351
theorem n11354 (_v : Vars) (_q : Query _v) (h2358 : (e2358 _v)) : (e2358 _v) := by
  exact h2358
theorem n11355 (_v : Vars) (_q : Query _v) (h2358 : (e2358 _v)) (h5195 : (e5195 _v)) : (e7489 _v) := by
  have p5391 := n5391 _v _q 
  have p8549 := n8549 _v _q h5195
  have p11354 := n11354 _v _q h2358
  exact FloorCertificate.node_11355 (e2 _v) (e7 _v) (e9 _v) (e45 _v) (e110 _v) p5391 p8549 p11354
theorem n11357 (_v : Vars) (_q : Query _v)  : (e11356 _v) := by
  by_contra hc
  change ¬ ((e196 _v) ∨ (¬ (e2358 _v))) at hc
  have h2358 : (e2358 _v) := by
    tauto
  have h5195 : (e5195 _v) := by
    change (¬ (e196 _v))
    tauto
  have p11355 := n11355 _v _q h2358 h5195
  exact p11355
theorem n11358 (_v : Vars) (_q : Query _v) (h6531 : (e6531 _v)) : (e6531 _v) := by
  exact h6531
theorem n11359 (_v : Vars) (_q : Query _v) (h2310 : (e2310 _v)) (h6531 : (e6531 _v)) : (e7489 _v) := by
  have p11358 := n11358 _v _q h6531
  have p5257 := n5257 _v _q 
  have p11059 := n11059 _v _q h2310
  exact FloorCertificate.node_11359 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e110 _v) p11358 p5257 p11059
theorem n11361 (_v : Vars) (_q : Query _v)  : (e11360 _v) := by
  by_contra hc
  change ¬ ((e2254 _v) ∨ (¬ (e2310 _v))) at hc
  have h2310 : (e2310 _v) := by
    tauto
  have h6531 : (e6531 _v) := by
    change (¬ (e2254 _v))
    tauto
  have p11359 := n11359 _v _q h2310 h6531
  exact p11359
theorem n11362 (_v : Vars) (_q : Query _v) (h6555 : (e6555 _v)) : (e6555 _v) := by
  exact h6555
theorem n11363 (_v : Vars) (_q : Query _v) (h2634 : (e2634 _v)) (h6555 : (e6555 _v)) : (e7489 _v) := by
  have p5391 := n5391 _v _q 
  have p5255 := n5255 _v _q 
  have p11032 := n11032 _v _q h2634
  have p11362 := n11362 _v _q h6555
  exact FloorCertificate.node_11363 (e2 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p5391 p5255 p11032 p11362
theorem n11365 (_v : Vars) (_q : Query _v)  : (e11364 _v) := by
  by_contra hc
  change ¬ ((e2310 _v) ∨ (¬ (e2634 _v))) at hc
  have h2634 : (e2634 _v) := by
    tauto
  have h6555 : (e6555 _v) := by
    change (¬ (e2310 _v))
    tauto
  have p11363 := n11363 _v _q h2634 h6555
  exact p11363
theorem n11366 (_v : Vars) (_q : Query _v) (h5108 : (e5108 _v)) : (e5108 _v) := by
  exact h5108
theorem n11367 (_v : Vars) (_q : Query _v) (h2733 : (e2733 _v)) (h5108 : (e5108 _v)) : (e7489 _v) := by
  have p5257 := n5257 _v _q 
  have p11366 := n11366 _v _q h5108
  have p8587 := n8587 _v _q h2733
  exact FloorCertificate.node_11367 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p5257 p11366 p8587
theorem n11369 (_v : Vars) (_q : Query _v)  : (e11368 _v) := by
  by_contra hc
  change ¬ ((e48 _v) ∨ (¬ (e2733 _v))) at hc
  have h2733 : (e2733 _v) := by
    tauto
  have h5108 : (e5108 _v) := by
    change (¬ (e48 _v))
    tauto
  have p11367 := n11367 _v _q h2733 h5108
  exact p11367
theorem n11370 (_v : Vars) (_q : Query _v) (h6732 : (e6732 _v)) : (e6732 _v) := by
  exact h6732
theorem n11371 (_v : Vars) (_q : Query _v) (h2746 : (e2746 _v)) (h6732 : (e6732 _v)) : (e7489 _v) := by
  have p11370 := n11370 _v _q h6732
  have p5257 := n5257 _v _q 
  have p11344 := n11344 _v _q h2746
  exact FloorCertificate.node_11371 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p11370 p5257 p11344
theorem n11373 (_v : Vars) (_q : Query _v)  : (e11372 _v) := by
  by_contra hc
  change ¬ ((e2697 _v) ∨ (¬ (e2746 _v))) at hc
  have h2746 : (e2746 _v) := by
    tauto
  have h6732 : (e6732 _v) := by
    change (¬ (e2697 _v))
    tauto
  have p11371 := n11371 _v _q h2746 h6732
  exact p11371
theorem n11374 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e251 _v) := by
  exact h251
theorem n11375 (_v : Vars) (_q : Query _v)  : (e176 _v) := by
  have p5183 := n5183 _v _q 
  have p5186 := n5186 _v _q 
  simp only [e167, e168, e174, e176, e5185] at *
  tauto
theorem n11376 (_v : Vars) (_q : Query _v)  : (e165 _v) := by
  have p5177 := n5177 _v _q 
  have p5180 := n5180 _v _q 
  simp only [e156, e157, e163, e165, e5179] at *
  tauto
theorem n11377 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) (h6591 : (e6591 _v)) : (e7489 _v) := by
  have p4946 := n4946 _v _q 
  have p11345 := n11345 _v _q h6591
  have p11374 := n11374 _v _q h251
  have p11375 := n11375 _v _q 
  have p11376 := n11376 _v _q 
  exact FloorCertificate.node_11377 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p4946 p11345 p11374 p11375 p11376
theorem n11379 (_v : Vars) (_q : Query _v)  : (e11378 _v) := by
  by_contra hc
  change ¬ ((¬ (e251 _v)) ∨ (e2377 _v)) at hc
  have h251 : (e251 _v) := by
    tauto
  have h6591 : (e6591 _v) := by
    change (¬ (e2377 _v))
    tauto
  have p11377 := n11377 _v _q h251 h6591
  exact p11377
theorem n11380 (_v : Vars) (_q : Query _v) (h2139 : (e2139 _v)) (h6591 : (e6591 _v)) : (e7489 _v) := by
  have p10896 := n10896 _v _q 
  have p10894 := n10894 _v _q h2139
  have p11345 := n11345 _v _q h6591
  exact FloorCertificate.node_11380 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e110 _v) p10896 p10894 p11345
end
end Assembly
