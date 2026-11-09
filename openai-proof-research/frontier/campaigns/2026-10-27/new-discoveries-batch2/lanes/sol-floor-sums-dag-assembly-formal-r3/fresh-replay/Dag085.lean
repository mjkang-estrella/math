import Dag084
import generated.th_lemma_4
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n12928 (_v : Vars) (_q : Query _v) (h2242 : (e2242 _v)) : (e2061 _v) := by
  have p8478 := n8478 _v _q 
  have p12927 := n12927 _v _q h2242
  simp only [e2061, e2125, e6480, e8477] at *
  tauto
theorem n12929 (_v : Vars) (_q : Query _v) (h2242 : (e2242 _v)) : (e1995 _v) := by
  have p11412 := n11412 _v _q 
  have p12928 := n12928 _v _q h2242
  simp only [e1995, e2061, e6454, e11411] at *
  tauto
theorem n12930 (_v : Vars) (_q : Query _v) (h2522 : (e2522 _v)) (h6423 : (e6423 _v)) : (e7489 _v) := by
  have p8663 := n8663 _v _q 
  have p5391 := n5391 _v _q 
  have p5257 := n5257 _v _q 
  have p8452 := n8452 _v _q h6423
  have p5255 := n5255 _v _q 
  have p12831 := n12831 _v _q h2522
  exact FloorCertificate.node_12930 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8663 p5391 p5257 p8452 p5255 p12831
theorem n12932 (_v : Vars) (_q : Query _v)  : (e12931 _v) := by
  by_contra hc
  change ¬ ((¬ (e2522 _v)) ∨ (e1995 _v)) at hc
  have h2522 : (e2522 _v) := by
    tauto
  have h6423 : (e6423 _v) := by
    change (¬ (e1995 _v))
    tauto
  have p12930 := n12930 _v _q h2522 h6423
  exact p12930
theorem n12933 (_v : Vars) (_q : Query _v) (h6583 : (e6583 _v)) : (e6750 _v) := by
  have p10946 := n10946 _v _q 
  have p12887 := n12887 _v _q h6583
  simp only [e2585, e2733, e6676, e6750, e10945] at *
  tauto
theorem n12934 (_v : Vars) (_q : Query _v) (h5195 : (e5195 _v)) : (e6772 _v) := by
  have p11498 := n11498 _v _q 
  have p12839 := n12839 _v _q h5195
  simp only [e2358, e2787, e6571, e6772, e11497] at *
  tauto
theorem n12935 (_v : Vars) (_q : Query _v) (h2781 : (e2781 _v)) : (e2634 _v) := by
  have p11030 := n11030 _v _q 
  have p8421 := n8421 _v _q h2781
  simp only [e2634, e2781, e6776, e11029] at *
  tauto
theorem n12936 (_v : Vars) (_q : Query _v) (h2781 : (e2781 _v)) : (e2310 _v) := by
  have p11365 := n11365 _v _q 
  have p12935 := n12935 _v _q h2781
  simp only [e2310, e2634, e6700, e11364] at *
  tauto
theorem n12937 (_v : Vars) (_q : Query _v) (h2781 : (e2781 _v)) : (e2254 _v) := by
  have p11361 := n11361 _v _q 
  have p12936 := n12936 _v _q h2781
  simp only [e2254, e2310, e6555, e11360] at *
  tauto
theorem n12938 (_v : Vars) (_q : Query _v) (h2132 : (e2132 _v)) (h6501 : (e6501 _v)) : (e6583 _v) := by
  have p8554 := n8554 _v _q h6501
  have p11349 := n11349 _v _q h2132
  exact FloorCertificate.node_12938 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e110 _v) p8554 p11349
theorem n12939 (_v : Vars) (_q : Query _v) (h2132 : (e2132 _v)) (h6501 : (e6501 _v)) : (e6676 _v) := by
  have p11343 := n11343 _v _q 
  have p12938 := n12938 _v _q h2132 h6501
  simp only [e2364, e2585, e6583, e6676, e11342] at *
  tauto
theorem n12940 (_v : Vars) (_q : Query _v) (h2132 : (e2132 _v)) : (e13 _v) := by
  have p11479 := n11479 _v _q 
  have p11349 := n11349 _v _q h2132
  simp only [e13, e2132, e7742, e11478] at *
  tauto
theorem n12941 (_v : Vars) (_q : Query _v) (h2132 : (e2132 _v)) : (e2475 _v) := by
  have p11399 := n11399 _v _q 
  have p12940 := n12940 _v _q h2132
  simp only [e13, e2475, e5093, e11398] at *
  tauto
theorem n12942 (_v : Vars) (_q : Query _v) (h2132 : (e2132 _v)) : (e2303 _v) := by
  have p11353 := n11353 _v _q 
  have p11349 := n11349 _v _q h2132
  simp only [e2132, e2303, e7742, e11352] at *
  tauto
theorem n12943 (_v : Vars) (_q : Query _v) (h2132 : (e2132 _v)) : (e2787 _v) := by
  have p8461 := n8461 _v _q 
  have p12941 := n12941 _v _q h2132
  have p12942 := n12942 _v _q h2132
  simp only [e2303, e2475, e2787, e7807, e8038, e8460] at *
  tauto
theorem n12944 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) : (e8038 _v) := by
  have p8438 := n8438 _v _q h2468
  have p258 := n258 _v _q 
  exact FloorCertificate.node_12944 (e2 _v) (e7 _v) (e17 _v) (e45 _v) p8438 p258
theorem n12945 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) : (e5093 _v) := by
  have p11399 := n11399 _v _q 
  have p12944 := n12944 _v _q h2468
  simp only [e13, e2475, e5093, e8038, e11398] at *
  tauto
theorem n12946 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) : (e7742 _v) := by
  have p11479 := n11479 _v _q 
  have p12945 := n12945 _v _q h2468
  simp only [e13, e2132, e5093, e7742, e11478] at *
  tauto
theorem n12947 (_v : Vars) (_q : Query _v) (h6423 : (e6423 _v)) : (e6501 _v) := by
  have p5257 := n5257 _v _q 
  have p5255 := n5255 _v _q 
  have p8452 := n8452 _v _q h6423
  exact FloorCertificate.node_12947 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e110 _v) p5257 p5255 p8452
theorem n12948 (_v : Vars) (_q : Query _v) (h6423 : (e6423 _v)) : (e6600 _v) := by
  have p11339 := n11339 _v _q 
  have p12947 := n12947 _v _q h6423
  simp only [e2179, e2402, e6501, e6600, e11338] at *
  tauto
theorem n12949 (_v : Vars) (_q : Query _v) (h6423 : (e6423 _v)) : (e6630 _v) := by
  have p11563 := n11563 _v _q 
  have p12853 := n12853 _v _q h6423
  simp only [e2061, e2468, e6454, e6630, e11562] at *
  tauto
theorem n12950 (_v : Vars) (_q : Query _v) (h5138 : (e5138 _v)) : (e7807 _v) := by
  have p11490 := n11490 _v _q 
  have p11487 := n11487 _v _q h5138
  simp only [e79, e2303, e5138, e7807, e11489] at *
  tauto
theorem n12951 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) (h5138 : (e5138 _v)) : (e2781 _v) := by
  have p12950 := n12950 _v _q h5138
  have p8438 := n8438 _v _q h2468
  exact FloorCertificate.node_12951 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p12950 p8438
theorem n12952 (_v : Vars) (_q : Query _v) (h6454 : (e6454 _v)) : (e6501 _v) := by
  have p5255 := n5255 _v _q 
  have p8430 := n8430 _v _q h6454
  exact FloorCertificate.node_12952 (e2 _v) (e9 _v) (e17 _v) (e110 _v) p5255 p8430
theorem n12953 (_v : Vars) (_q : Query _v) (h6454 : (e6454 _v)) : (e6600 _v) := by
  have p11339 := n11339 _v _q 
  have p12952 := n12952 _v _q h6454
  simp only [e2179, e2402, e6501, e6600, e11338] at *
  tauto
theorem n12954 (_v : Vars) (_q : Query _v) (h5138 : (e5138 _v)) : (e8038 _v) := by
  have p11510 := n11510 _v _q 
  have p11487 := n11487 _v _q h5138
  simp only [e79, e2475, e5138, e8038, e11509] at *
  tauto
theorem n12955 (_v : Vars) (_q : Query _v) (h2296 : (e2296 _v)) (h5138 : (e5138 _v)) : (e2781 _v) := by
  have p8583 := n8583 _v _q h2296
  have p12954 := n12954 _v _q h5138
  exact FloorCertificate.node_12955 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8583 p12954
theorem n12956 (_v : Vars) (_q : Query _v) (h2132 : (e2132 _v)) : (e4484 _v) := by
  have p8139 := n8139 _v _q 
  have p11349 := n11349 _v _q h2132
  exact FloorCertificate.node_12956 (e2 _v) (e7 _v) (e110 _v) p8139 p11349
theorem n12957 (_v : Vars) (_q : Query _v) (h2132 : (e2132 _v)) (h2242 : (e2242 _v)) : (e7489 _v) := by
  have p8139 := n8139 _v _q 
  have p11215 := n11215 _v _q 
  have p11482 := n11482 _v _q 
  have p12956 := n12956 _v _q h2132
  have p8608 := n8608 _v _q h2242
  exact FloorCertificate.node_12957 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e110 _v) p8139 p11215 p11482 p12956 p8608
theorem n12959 (_v : Vars) (_q : Query _v)  : (e12958 _v) := by
  simp only [e5, e6, e8, e10, e11, e12, e13, e41, e42, e5098, e5100, e5102, e5103, e5104, e5105, e8622, e12958] at *
theorem n12960 (_v : Vars) (_q : Query _v)  : (e11578 _v) := by
  have p11579 := n11579 _v _q 
  have p12959 := n12959 _v _q 
  exact (Iff.trans p11579 p12959)
theorem n12961 (_v : Vars) (_q : Query _v)  : (e5123 _v) := by
  have p11583 := n11583 _v _q 
  change ((e62 _v) ↔ (e5119 _v)) at p11583
  simp only [e5123, e5110, e5122, p11583]
theorem n12962 (_v : Vars) (_q : Query _v)  : (e5124 _v) := by
  simp only [e5, e6, e8, e10, e12, e41, e43, e44, e46, e47, e48, e68, e69, e70, e72, e75, e76, e5118, e5119, e5122, e5124] at *
theorem n12963 (_v : Vars) (_q : Query _v)  : (e5123 _v) := by
  have p12961 := n12961 _v _q 
  have p12962 := n12962 _v _q 
  exact (Iff.trans p12961 p12962)
theorem n12965 (_v : Vars) (_q : Query _v)  : (e12964 _v) := by
  have p8630 := n8630 _v _q 
  have p12963 := n12963 _v _q 
  change ((e5109 _v) ↔ (e5125 _v)) at p8630
  change ((e5110 _v) ↔ (e5122 _v)) at p12963
  simp only [e12964, e5111, e5126, p8630, p12963]
theorem n12968 (_v : Vars) (_q : Query _v)  : (e12967 _v) := by
  simp only [e5, e6, e8, e10, e12, e41, e43, e44, e46, e47, e48, e51, e52, e57, e58, e59, e60, e68, e69, e70, e72, e75, e76, e5108, e5118, e5119, e5122, e5125, e5126, e5127, e8633, e8634, e12966, e12967] at *
  omega
theorem n12970 (_v : Vars) (_q : Query _v)  : (e12969 _v) := by
  have p12965 := n12965 _v _q 
  have p12968 := n12968 _v _q 
  exact (Iff.trans p12965 p12968)
theorem n12972 (_v : Vars) (_q : Query _v)  : (e12971 _v) := by
  simp only [e5, e6, e10, e12, e41, e46, e78, e79, e100, e5143, e5145, e5147, e5148, e5149, e5150, e8647, e12971] at *
theorem n12973 (_v : Vars) (_q : Query _v)  : (e11590 _v) := by
  have p11591 := n11591 _v _q 
  have p12972 := n12972 _v _q 
  exact (Iff.trans p11591 p12972)
theorem n12974 (_v : Vars) (_q : Query _v)  : (e5168 _v) := by
  have p11595 := n11595 _v _q 
  change ((e120 _v) ↔ (e5164 _v)) at p11595
  simp only [e5168, e5155, e5167, p11595]
theorem n12975 (_v : Vars) (_q : Query _v)  : (e5169 _v) := by
  simp only [e5, e6, e8, e10, e12, e41, e108, e109, e111, e112, e113, e126, e127, e128, e130, e133, e134, e5163, e5164, e5167, e5169] at *
theorem n12976 (_v : Vars) (_q : Query _v)  : (e5168 _v) := by
  have p12974 := n12974 _v _q 
  have p12975 := n12975 _v _q 
  exact (Iff.trans p12974 p12975)
theorem n12978 (_v : Vars) (_q : Query _v)  : (e12977 _v) := by
  have p8655 := n8655 _v _q 
  have p12976 := n12976 _v _q 
  change ((e5154 _v) ↔ (e5170 _v)) at p8655
  change ((e5155 _v) ↔ (e5167 _v)) at p12976
  simp only [e12977, e5156, e5171, p8655, p12976]
theorem n12981 (_v : Vars) (_q : Query _v)  : (e12980 _v) := by
  simp only [e5, e6, e8, e10, e12, e41, e102, e103, e104, e105, e106, e108, e109, e111, e112, e113, e118, e126, e127, e128, e130, e133, e134, e5153, e5163, e5164, e5167, e5170, e5171, e5172, e8658, e8659, e12979, e12980] at *
  omega
theorem n12983 (_v : Vars) (_q : Query _v)  : (e12982 _v) := by
  have p12978 := n12978 _v _q 
  have p12981 := n12981 _v _q 
  exact (Iff.trans p12978 p12981)
end
end Assembly
