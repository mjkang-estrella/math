import Dag082
import generated.th_lemma_3
import generated.th_lemma_4
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n12832 (_v : Vars) (_q : Query _v) (h2522 : (e2522 _v)) : (e2468 _v) := by
  have p5257 := n5257 _v _q 
  have p12831 := n12831 _v _q h2522
  exact FloorCertificate.node_12832 (e2 _v) (e7 _v) (e17 _v) (e45 _v) (e110 _v) p5257 p12831
theorem n12833 (_v : Vars) (_q : Query _v) (h2522 : (e2522 _v)) : (e2402 _v) := by
  have p8442 := n8442 _v _q 
  have p12832 := n12832 _v _q h2522
  simp only [e2402, e2468, e6630, e8441] at *
  tauto
theorem n12834 (_v : Vars) (_q : Query _v) (h2522 : (e2522 _v)) : (e2179 _v) := by
  have p11339 := n11339 _v _q 
  have p12833 := n12833 _v _q h2522
  simp only [e2179, e2402, e6600, e11338] at *
  tauto
theorem n12835 (_v : Vars) (_q : Query _v) (h8038 : (e8038 _v)) : (e2598 _v) := by
  have p8663 := n8663 _v _q 
  have p5255 := n5255 _v _q 
  have p10893 := n10893 _v _q 
  have p11424 := n11424 _v _q h8038
  exact FloorCertificate.node_12835 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8663 p5255 p10893 p11424
theorem n12836 (_v : Vars) (_q : Query _v) (h8038 : (e8038 _v)) : (e2697 _v) := by
  have p8663 := n8663 _v _q 
  have p11424 := n11424 _v _q h8038
  have p10893 := n10893 _v _q 
  exact FloorCertificate.node_12836 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) p8663 p11424 p10893
theorem n12837 (_v : Vars) (_q : Query _v) (h8038 : (e8038 _v)) : (e2805 _v) := by
  have p8663 := n8663 _v _q 
  have p10893 := n10893 _v _q 
  have p11375 := n11375 _v _q 
  have p11424 := n11424 _v _q h8038
  exact FloorCertificate.node_12837 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8663 p10893 p11375 p11424
theorem n12838 (_v : Vars) (_q : Query _v) (h8038 : (e8038 _v)) : (e2377 _v) := by
  have p11375 := n11375 _v _q 
  have p8663 := n8663 _v _q 
  have p11424 := n11424 _v _q h8038
  exact FloorCertificate.node_12838 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e110 _v) p11375 p8663 p11424
theorem n12839 (_v : Vars) (_q : Query _v) (h5195 : (e5195 _v)) : (e6571 _v) := by
  have p11357 := n11357 _v _q 
  have p8549 := n8549 _v _q h5195
  simp only [e196, e2358, e5195, e6571, e11356] at *
  tauto
theorem n12840 (_v : Vars) (_q : Query _v) (h5195 : (e5195 _v)) : (e7807 _v) := by
  have p8451 := n8451 _v _q 
  have p12839 := n12839 _v _q h5195
  simp only [e2303, e2358, e6571, e7807, e8450] at *
  tauto
theorem n12841 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) (h6700 : (e6700 _v)) : (e7489 _v) := by
  have p11027 := n11027 _v _q h6700
  have p3130 := n3130 _v _q 
  have p4016 := n4016 _v _q 
  have p8663 := n8663 _v _q 
  have p7488 := n7488 _v _q h5362
  exact FloorCertificate.node_12841 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p11027 p3130 p4016 p8663 p7488
theorem n12843 (_v : Vars) (_q : Query _v)  : (e12842 _v) := by
  by_contra hc
  change ¬ ((e436 _v) ∨ (e2634 _v)) at hc
  have h5362 : (e5362 _v) := by
    change (¬ (e436 _v))
    tauto
  have h6700 : (e6700 _v) := by
    change (¬ (e2634 _v))
    tauto
  have p12841 := n12841 _v _q h5362 h6700
  exact p12841
theorem n12844 (_v : Vars) (_q : Query _v) (h5195 : (e5195 _v)) : (e2364 _v) := by
  have p12839 := n12839 _v _q h5195
  have p8663 := n8663 _v _q 
  exact FloorCertificate.node_12844 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e110 _v) p12839 p8663
theorem n12845 (_v : Vars) (_q : Query _v) (h5195 : (e5195 _v)) (h6480 : (e6480 _v)) : (e6772 _v) := by
  have p8549 := n8549 _v _q h5195
  have p12839 := n12839 _v _q h5195
  have p8663 := n8663 _v _q 
  have p8575 := n8575 _v _q h6480
  exact FloorCertificate.node_12845 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8549 p12839 p8663 p8575
theorem n12846 (_v : Vars) (_q : Query _v) (h8038 : (e8038 _v)) : (e6672 _v) := by
  have p11443 := n11443 _v _q 
  have p11424 := n11424 _v _q h8038
  simp only [e13, e2592, e5093, e6672, e11442] at *
  tauto
theorem n12847 (_v : Vars) (_q : Query _v) (h6571 : (e6571 _v)) (h6583 : (e6583 _v)) : (e7489 _v) := by
  have p8663 := n8663 _v _q 
  have p11340 := n11340 _v _q h6583
  have p8447 := n8447 _v _q h6571
  exact FloorCertificate.node_12847 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e110 _v) p8663 p11340 p8447
theorem n12849 (_v : Vars) (_q : Query _v)  : (e12848 _v) := by
  by_contra hc
  change ¬ ((e2364 _v) ∨ (e2358 _v)) at hc
  have h6571 : (e6571 _v) := by
    change (¬ (e2358 _v))
    tauto
  have h6583 : (e6583 _v) := by
    change (¬ (e2364 _v))
    tauto
  have p12847 := n12847 _v _q h6571 h6583
  exact p12847
theorem n12850 (_v : Vars) (_q : Query _v) (h6571 : (e6571 _v)) : (e2310 _v) := by
  have p11445 := n11445 _v _q h6571
  have p8663 := n8663 _v _q 
  exact FloorCertificate.node_12850 (e2 _v) (e9 _v) (e17 _v) (e110 _v) p11445 p8663
theorem n12851 (_v : Vars) (_q : Query _v) (h6555 : (e6555 _v)) : (e6656 _v) := by
  have p11439 := n11439 _v _q 
  have p11362 := n11362 _v _q h6555
  simp only [e2310, e2536, e6555, e6656, e11438] at *
  tauto
theorem n12852 (_v : Vars) (_q : Query _v) (h6555 : (e6555 _v)) : (e2529 _v) := by
  have p12851 := n12851 _v _q h6555
  have p8663 := n8663 _v _q 
  exact FloorCertificate.node_12852 (e2 _v) (e17 _v) (e45 _v) (e110 _v) p12851 p8663
theorem n12853 (_v : Vars) (_q : Query _v) (h6423 : (e6423 _v)) : (e6454 _v) := by
  have p11412 := n11412 _v _q 
  have p8452 := n8452 _v _q h6423
  simp only [e1995, e2061, e6423, e6454, e11411] at *
  tauto
theorem n12854 (_v : Vars) (_q : Query _v) (h6423 : (e6423 _v)) : (e6480 _v) := by
  have p8478 := n8478 _v _q 
  have p12853 := n12853 _v _q h6423
  simp only [e2061, e2125, e6454, e6480, e8477] at *
  tauto
theorem n12855 (_v : Vars) (_q : Query _v) (h5195 : (e5195 _v)) (h6423 : (e6423 _v)) : (e6772 _v) := by
  have p8663 := n8663 _v _q 
  have p12839 := n12839 _v _q h5195
  have p8452 := n8452 _v _q h6423
  have p8549 := n8549 _v _q h5195
  have p12853 := n12853 _v _q h6423
  exact FloorCertificate.node_12855 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8663 p12839 p8452 p8549 p12853
theorem n12856 (_v : Vars) (_q : Query _v) (h6571 : (e6571 _v)) : (e6746 _v) := by
  have p11429 := n11429 _v _q 
  have p11445 := n11445 _v _q h6571
  simp only [e2303, e2740, e6746, e7807, e11428] at *
  tauto
theorem n12857 (_v : Vars) (_q : Query _v) (h8038 : (e8038 _v)) : (e5093 _v) := by
  have p11399 := n11399 _v _q 
  have p8602 := n8602 _v _q h8038
  simp only [e13, e2475, e5093, e8038, e11398] at *
  tauto
theorem n12858 (_v : Vars) (_q : Query _v) (h8038 : (e8038 _v)) : (e6780 _v) := by
  have p11449 := n11449 _v _q 
  have p12857 := n12857 _v _q h8038
  simp only [e13, e2799, e5093, e6780, e11448] at *
  tauto
theorem n12859 (_v : Vars) (_q : Query _v) (h8038 : (e8038 _v)) : (e6724 _v) := by
  have p12857 := n12857 _v _q h8038
  have p10893 := n10893 _v _q 
  exact FloorCertificate.node_12859 (e2 _v) (e7 _v) (e9 _v) (e45 _v) p12857 p10893
theorem n12860 (_v : Vars) (_q : Query _v) (h6555 : (e6555 _v)) : (e2303 _v) := by
  have p11362 := n11362 _v _q h6555
  have p8663 := n8663 _v _q 
  exact FloorCertificate.node_12860 (e2 _v) (e9 _v) (e17 _v) (e110 _v) p11362 p8663
theorem n12861 (_v : Vars) (_q : Query _v) (h6555 : (e6555 _v)) : (e2358 _v) := by
  have p8451 := n8451 _v _q 
  have p12860 := n12860 _v _q h6555
  simp only [e2303, e2358, e7807, e8450] at *
  tauto
theorem n12862 (_v : Vars) (_q : Query _v) (h6531 : (e6531 _v)) : (e6555 _v) := by
  have p5257 := n5257 _v _q 
  have p11358 := n11358 _v _q h6531
  exact FloorCertificate.node_12862 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e110 _v) p5257 p11358
theorem n12863 (_v : Vars) (_q : Query _v) (h6531 : (e6531 _v)) : (e6656 _v) := by
  have p11439 := n11439 _v _q 
  have p12862 := n12862 _v _q h6531
  simp only [e2310, e2536, e6555, e6656, e11438] at *
  tauto
theorem n12864 (_v : Vars) (_q : Query _v) (h6531 : (e6531 _v)) : (e6636 _v) := by
  have p11455 := n11455 _v _q 
  have p11358 := n11358 _v _q h6531
  simp only [e2254, e2482, e6531, e6636, e11454] at *
  tauto
theorem n12865 (_v : Vars) (_q : Query _v) (h6531 : (e6531 _v)) : (e6656 _v) := by
  have p11135 := n11135 _v _q 
  have p12864 := n12864 _v _q h6531
  simp only [e2482, e2536, e6636, e6656, e11134] at *
  tauto
theorem n12866 (_v : Vars) (_q : Query _v) (h7807 : (e7807 _v)) : (e6746 _v) := by
  have p11429 := n11429 _v _q 
  have p11350 := n11350 _v _q h7807
  simp only [e2303, e2740, e6746, e7807, e11428] at *
  tauto
theorem n12867 (_v : Vars) (_q : Query _v) (h7807 : (e7807 _v)) : (e6724 _v) := by
  have p11461 := n11461 _v _q 
  have p12866 := n12866 _v _q h7807
  simp only [e2691, e2740, e6724, e6746, e11460] at *
  tauto
theorem n12868 (_v : Vars) (_q : Query _v) (h8038 : (e8038 _v)) : (e6672 _v) := by
  have p11443 := n11443 _v _q 
  have p12857 := n12857 _v _q h8038
  simp only [e13, e2592, e5093, e6672, e11442] at *
  tauto
theorem n12869 (_v : Vars) (_q : Query _v) (h7807 : (e7807 _v)) : (e7742 _v) := by
  have p11353 := n11353 _v _q 
  have p11350 := n11350 _v _q h7807
  simp only [e2132, e2303, e7742, e7807, e11352] at *
  tauto
theorem n12870 (_v : Vars) (_q : Query _v) (h7807 : (e7807 _v)) : (e6579 _v) := by
  have p11465 := n11465 _v _q 
  have p12869 := n12869 _v _q h7807
  simp only [e2132, e2371, e6579, e7742, e11464] at *
  tauto
theorem n12871 (_v : Vars) (_q : Query _v) (h8038 : (e8038 _v)) : (e7742 _v) := by
  have p12857 := n12857 _v _q h8038
  have p5255 := n5255 _v _q 
  exact FloorCertificate.node_12871 (e2 _v) (e7 _v) (e9 _v) (e110 _v) p12857 p5255
theorem n12872 (_v : Vars) (_q : Query _v) (h2691 : (e2691 _v)) (h8038 : (e8038 _v)) : (e7489 _v) := by
  have p4016 := n4016 _v _q 
  have p12857 := n12857 _v _q h8038
  have p8602 := n8602 _v _q h8038
  have p11457 := n11457 _v _q h2691
  exact FloorCertificate.node_12872 (e2 _v) (e7 _v) (e9 _v) (e45 _v) p4016 p12857 p8602 p11457
theorem n12873 (_v : Vars) (_q : Query _v) (h7807 : (e7807 _v)) : (e6672 _v) := by
  have p11486 := n11486 _v _q 
  have p12866 := n12866 _v _q h7807
  simp only [e2592, e2740, e6672, e6746, e11485] at *
  tauto
theorem n12874 (_v : Vars) (_q : Query _v) (h8038 : (e8038 _v)) : (e7742 _v) := by
  have p11479 := n11479 _v _q 
  have p12857 := n12857 _v _q h8038
  simp only [e13, e2132, e5093, e7742, e11478] at *
  tauto
theorem n12875 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) : (e5138 _v) := by
  have p7492 := n7492 _v _q 
  have p7488 := n7488 _v _q h5362
  simp only [e79, e436, e5138, e5362, e7491] at *
  tauto
theorem n12876 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) : (e7807 _v) := by
  have p11490 := n11490 _v _q 
  have p12875 := n12875 _v _q h5362
  simp only [e79, e2303, e5138, e7807, e11489] at *
  tauto
theorem n12877 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) (h6750 : (e6750 _v)) : (e7489 _v) := by
  have p4016 := n4016 _v _q 
  have p8663 := n8663 _v _q 
  have p8420 := n8420 _v _q h6750
  have p7488 := n7488 _v _q h5362
  exact FloorCertificate.node_12877 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p4016 p8663 p8420 p7488
theorem n12879 (_v : Vars) (_q : Query _v)  : (e12878 _v) := by
  by_contra hc
  change ¬ ((e2733 _v) ∨ (e436 _v)) at hc
  have h5362 : (e5362 _v) := by
    change (¬ (e436 _v))
    tauto
  have h6750 : (e6750 _v) := by
    change (¬ (e2733 _v))
    tauto
  have p12877 := n12877 _v _q h5362 h6750
  exact p12877
end
end Assembly
