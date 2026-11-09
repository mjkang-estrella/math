import Dag083
import generated.th_lemma_4
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n12880 (_v : Vars) (_q : Query _v) (h8310 : (e8310 _v)) : (e8038 _v) := by
  have p11493 := n11493 _v _q 
  have p11384 := n11384 _v _q h8310
  simp only [e2475, e2529, e8038, e8310, e11492] at *
  tauto
theorem n12881 (_v : Vars) (_q : Query _v) (h8310 : (e8310 _v)) : (e5093 _v) := by
  have p11399 := n11399 _v _q 
  have p12880 := n12880 _v _q h8310
  simp only [e13, e2475, e5093, e8038, e11398] at *
  tauto
theorem n12882 (_v : Vars) (_q : Query _v) (h5195 : (e5195 _v)) : (e6772 _v) := by
  have p10893 := n10893 _v _q 
  have p12839 := n12839 _v _q h5195
  exact FloorCertificate.node_12882 (e2 _v) (e7 _v) (e9 _v) (e45 _v) (e110 _v) p10893 p12839
theorem n12883 (_v : Vars) (_q : Query _v) (h6571 : (e6571 _v)) : (e5093 _v) := by
  have p11468 := n11468 _v _q 
  have p11445 := n11445 _v _q h6571
  simp only [e13, e2303, e5093, e7807, e11467] at *
  tauto
theorem n12884 (_v : Vars) (_q : Query _v) (h6571 : (e6571 _v)) : (e7742 _v) := by
  have p11353 := n11353 _v _q 
  have p11445 := n11445 _v _q h6571
  simp only [e2132, e2303, e7742, e7807, e11352] at *
  tauto
theorem n12885 (_v : Vars) (_q : Query _v) (h8310 : (e8310 _v)) : (e7807 _v) := by
  have p11387 := n11387 _v _q 
  have p11384 := n11384 _v _q h8310
  simp only [e2303, e2529, e7807, e8310, e11386] at *
  tauto
theorem n12886 (_v : Vars) (_q : Query _v) (h8310 : (e8310 _v)) : (e7742 _v) := by
  have p11353 := n11353 _v _q 
  have p12885 := n12885 _v _q h8310
  simp only [e2132, e2303, e7742, e7807, e11352] at *
  tauto
theorem n12887 (_v : Vars) (_q : Query _v) (h6583 : (e6583 _v)) : (e6676 _v) := by
  have p11343 := n11343 _v _q 
  have p11340 := n11340 _v _q h6583
  simp only [e2364, e2585, e6583, e6676, e11342] at *
  tauto
theorem n12888 (_v : Vars) (_q : Query _v) (h6583 : (e6583 _v)) (h8310 : (e8310 _v)) : (e6423 _v) := by
  have p11384 := n11384 _v _q h8310
  have p12887 := n12887 _v _q h6583
  exact FloorCertificate.node_12888 (e2 _v) (e7 _v) (e17 _v) (e45 _v) (e110 _v) p11384 p12887
theorem n12889 (_v : Vars) (_q : Query _v) (h6758 : (e6758 _v)) : (e6575 _v) := by
  have p11505 := n11505 _v _q 
  have p8425 := n8425 _v _q h6758
  simp only [e2351, e2746, e6575, e6758, e11504] at *
  tauto
theorem n12890 (_v : Vars) (_q : Query _v) (h6758 : (e6758 _v)) : (e5392 _v) := by
  have p11417 := n11417 _v _q 
  have p12889 := n12889 _v _q h6758
  simp only [e474, e2351, e5392, e6575, e11416] at *
  tauto
theorem n12891 (_v : Vars) (_q : Query _v) (h6758 : (e6758 _v)) : (e6784 _v) := by
  have p8429 := n8429 _v _q 
  have p8425 := n8425 _v _q h6758
  simp only [e2746, e2793, e6758, e6784, e8428] at *
  tauto
theorem n12892 (_v : Vars) (_q : Query _v) (h6758 : (e6758 _v)) : (e6583 _v) := by
  have p11476 := n11476 _v _q 
  have p12891 := n12891 _v _q h6758
  simp only [e2364, e2793, e6583, e6784, e11475] at *
  tauto
theorem n12893 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e6583 _v) := by
  have p11476 := n11476 _v _q 
  have p11473 := n11473 _v _q h6784
  simp only [e2364, e2793, e6583, e6784, e11475] at *
  tauto
theorem n12894 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e6676 _v) := by
  have p11343 := n11343 _v _q 
  have p12893 := n12893 _v _q h6784
  simp only [e2364, e2585, e6583, e6676, e11342] at *
  tauto
theorem n12895 (_v : Vars) (_q : Query _v) (h5223 : (e5223 _v)) (h6636 : (e6636 _v)) : (e7489 _v) := by
  have p4951 := n4951 _v _q 
  have p8663 := n8663 _v _q 
  have p11520 := n11520 _v _q h5223
  have p5257 := n5257 _v _q 
  have p11031 := n11031 _v _q h6636
  exact FloorCertificate.node_12895 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p4951 p8663 p11520 p5257 p11031
theorem n12897 (_v : Vars) (_q : Query _v)  : (e12896 _v) := by
  by_contra hc
  change ¬ ((e214 _v) ∨ (e2482 _v)) at hc
  have h5223 : (e5223 _v) := by
    change (¬ (e214 _v))
    tauto
  have h6636 : (e6636 _v) := by
    change (¬ (e2482 _v))
    tauto
  have p12895 := n12895 _v _q h5223 h6636
  exact p12895
theorem n12898 (_v : Vars) (_q : Query _v) (h5195 : (e5195 _v)) (h6676 : (e6676 _v)) : (e7489 _v) := by
  have p10943 := n10943 _v _q h6676
  have p8549 := n8549 _v _q h5195
  have p8663 := n8663 _v _q 
  exact FloorCertificate.node_12898 (e2 _v) (e7 _v) (e17 _v) (e45 _v) (e110 _v) p10943 p8549 p8663
theorem n12900 (_v : Vars) (_q : Query _v)  : (e12899 _v) := by
  by_contra hc
  change ¬ ((e2585 _v) ∨ (e196 _v)) at hc
  have h5195 : (e5195 _v) := by
    change (¬ (e196 _v))
    tauto
  have h6676 : (e6676 _v) := by
    change (¬ (e2585 _v))
    tauto
  have p12898 := n12898 _v _q h5195 h6676
  exact p12898
theorem n12901 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) : (e8038 _v) := by
  have p11510 := n11510 _v _q 
  have p12875 := n12875 _v _q h5362
  simp only [e79, e2475, e5138, e8038, e11509] at *
  tauto
theorem n12902 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) (h6454 : (e6454 _v)) : (e7489 _v) := by
  have p8663 := n8663 _v _q 
  have p4016 := n4016 _v _q 
  have p8464 := n8464 _v _q h2351
  have p8430 := n8430 _v _q h6454
  have p5255 := n5255 _v _q 
  exact FloorCertificate.node_12902 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e110 _v) p8663 p4016 p8464 p8430 p5255
theorem n12904 (_v : Vars) (_q : Query _v)  : (e12903 _v) := by
  by_contra hc
  change ¬ ((e2061 _v) ∨ (¬ (e2351 _v))) at hc
  have h2351 : (e2351 _v) := by
    tauto
  have h6454 : (e6454 _v) := by
    change (¬ (e2061 _v))
    tauto
  have p12902 := n12902 _v _q h2351 h6454
  exact p12902
theorem n12905 (_v : Vars) (_q : Query _v) (h6454 : (e6454 _v)) : (e6501 _v) := by
  have p8430 := n8430 _v _q h6454
  have p5255 := n5255 _v _q 
  exact FloorCertificate.node_12905 (e2 _v) (e9 _v) (e17 _v) (e110 _v) p8430 p5255
theorem n12906 (_v : Vars) (_q : Query _v) (h6454 : (e6454 _v)) : (e6600 _v) := by
  have p11339 := n11339 _v _q 
  have p12905 := n12905 _v _q h6454
  simp only [e2179, e2402, e6501, e6600, e11338] at *
  tauto
theorem n12907 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) (h6454 : (e6454 _v)) : (e5195 _v) := by
  have p7488 := n7488 _v _q h5362
  have p8663 := n8663 _v _q 
  have p5255 := n5255 _v _q 
  have p8430 := n8430 _v _q h6454
  exact FloorCertificate.node_12907 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p7488 p8663 p5255 p8430
theorem n12908 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) (h6454 : (e6454 _v)) : (e8310 _v) := by
  have p8552 := n8552 _v _q 
  have p12907 := n12907 _v _q h5362 h6454
  simp only [e196, e2529, e5195, e8310, e8551] at *
  tauto
theorem n12909 (_v : Vars) (_q : Query _v) (h6636 : (e6636 _v)) : (e6700 _v) := by
  have p11035 := n11035 _v _q 
  have p11031 := n11031 _v _q h6636
  simp only [e2482, e2634, e6636, e6700, e11034] at *
  tauto
theorem n12910 (_v : Vars) (_q : Query _v) (h6636 : (e6636 _v)) : (e6776 _v) := by
  have p11030 := n11030 _v _q 
  have p12909 := n12909 _v _q h6636
  simp only [e2634, e2781, e6700, e6776, e11029] at *
  tauto
theorem n12911 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e2125 _v) := by
  have p5257 := n5257 _v _q 
  have p5391 := n5391 _v _q 
  have p11374 := n11374 _v _q h251
  have p5255 := n5255 _v _q 
  exact FloorCertificate.node_12911 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p5257 p5391 p11374 p5255
theorem n12912 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e2585 _v) := by
  have p11436 := n11436 _v _q 
  have p12911 := n12911 _v _q h251
  simp only [e2125, e2585, e6480, e11435] at *
  tauto
theorem n12913 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e2781 _v) := by
  have p11519 := n11519 _v _q 
  have p11374 := n11374 _v _q h251
  simp only [e251, e2781, e6694, e11518] at *
  tauto
theorem n12914 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e2733 _v) := by
  have p8424 := n8424 _v _q 
  have p12913 := n12913 _v _q h251
  simp only [e2733, e2781, e6776, e8423] at *
  tauto
theorem n12915 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e48 _v) := by
  have p11369 := n11369 _v _q 
  have p12914 := n12914 _v _q h251
  simp only [e48, e2733, e6750, e11368] at *
  tauto
theorem n12916 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e2634 _v) := by
  have p11030 := n11030 _v _q 
  have p12913 := n12913 _v _q h251
  simp only [e2634, e2781, e6776, e11029] at *
  tauto
theorem n12917 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e2536 _v) := by
  have p11502 := n11502 _v _q 
  have p12916 := n12916 _v _q h251
  simp only [e2536, e2634, e6700, e11501] at *
  tauto
theorem n12918 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e2310 _v) := by
  have p11365 := n11365 _v _q 
  have p12916 := n12916 _v _q h251
  simp only [e2310, e2634, e6700, e11364] at *
  tauto
theorem n12919 (_v : Vars) (_q : Query _v) (h474 : (e474 _v)) : (e2781 _v) := by
  have p11531 := n11531 _v _q 
  have p11414 := n11414 _v _q h474
  simp only [e474, e2781, e5392, e11530] at *
  tauto
theorem n12920 (_v : Vars) (_q : Query _v) (h474 : (e474 _v)) : (e2733 _v) := by
  have p8424 := n8424 _v _q 
  have p12919 := n12919 _v _q h474
  simp only [e2733, e2781, e6776, e8423] at *
  tauto
theorem n12921 (_v : Vars) (_q : Query _v) (h474 : (e474 _v)) : (e2585 _v) := by
  have p10946 := n10946 _v _q 
  have p12920 := n12920 _v _q h474
  simp only [e2585, e2733, e6750, e10945] at *
  tauto
theorem n12922 (_v : Vars) (_q : Query _v) (h474 : (e474 _v)) : (e48 _v) := by
  have p11369 := n11369 _v _q 
  have p12920 := n12920 _v _q h474
  simp only [e48, e2733, e6750, e11368] at *
  tauto
theorem n12923 (_v : Vars) (_q : Query _v) (h5223 : (e5223 _v)) : (e5195 _v) := by
  have p11523 := n11523 _v _q 
  have p11520 := n11520 _v _q h5223
  simp only [e196, e214, e5195, e5223, e11522] at *
  tauto
theorem n12924 (_v : Vars) (_q : Query _v) (h5223 : (e5223 _v)) : (e8310 _v) := by
  have p8552 := n8552 _v _q 
  have p12923 := n12923 _v _q h5223
  simp only [e196, e2529, e5195, e8310, e8551] at *
  tauto
theorem n12925 (_v : Vars) (_q : Query _v) (h5195 : (e5195 _v)) : (e8310 _v) := by
  have p8552 := n8552 _v _q 
  have p8549 := n8549 _v _q h5195
  simp only [e196, e2529, e5195, e8310, e8551] at *
  tauto
theorem n12926 (_v : Vars) (_q : Query _v) (h5195 : (e5195 _v)) : (e8038 _v) := by
  have p11493 := n11493 _v _q 
  have p12925 := n12925 _v _q h5195
  simp only [e2475, e2529, e8038, e8310, e11492] at *
  tauto
theorem n12927 (_v : Vars) (_q : Query _v) (h2242 : (e2242 _v)) : (e2125 _v) := by
  have p8553 := n8553 _v _q h2242
  have p5255 := n5255 _v _q 
  exact FloorCertificate.node_12927 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e110 _v) p8553 p5255
end
end Assembly
