import Dag134
import generated.th_lemma_10
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n15733 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) : (e7814 _v) := by
  have p15221 := n15221 _v _q 
  have p15732 := n15732 _v _q h5362
  simp only [e7812, e7814, e7816, e7817, e7818, e7819, e8456] at *
  tauto
theorem n15734 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) : (e5093 _v) := by
  have p11399 := n11399 _v _q 
  have p12901 := n12901 _v _q h5362
  simp only [e13, e2475, e5093, e8038, e11398] at *
  tauto
theorem n15735 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) : (e5105 _v) := by
  have p15204 := n15204 _v _q 
  have p15734 := n15734 _v _q h5362
  simp only [e13, e5093, e5098, e5100, e5102, e5103, e5104, e5105, e8622] at *
  tauto
theorem n15736 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) : (e5100 _v) := by
  have p15319 := n15319 _v _q 
  have p15735 := n15735 _v _q h5362
  simp only [e5098, e5100, e5102, e5103, e5104, e5105, e8479] at *
  tauto
theorem n15737 (_v : Vars) (_q : Query _v) (h6423 : (e6423 _v)) : (e6525 _v) := by
  have p5257 := n5257 _v _q 
  have p5255 := n5255 _v _q 
  have p8452 := n8452 _v _q h6423
  have p8663 := n8663 _v _q 
  exact FloorCertificate.node_15737 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e110 _v) p5257 p5255 p8452 p8663
theorem n15738 (_v : Vars) (_q : Query _v) (h6423 : (e6423 _v)) : (e8174 _v) := by
  have p14634 := n14634 _v _q 
  have p15737 := n15737 _v _q h6423
  simp only [e2242, e4673, e4674, e4675, e4676, e6525, e8166, e8174, e8177] at *
  tauto
theorem n15739 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) (h6423 : (e6423 _v)) : (e8310 _v) := by
  have p5257 := n5257 _v _q 
  have p7488 := n7488 _v _q h5362
  have p8452 := n8452 _v _q h6423
  have p5255 := n5255 _v _q 
  have p8663 := n8663 _v _q 
  exact FloorCertificate.node_15739 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p5257 p7488 p8452 p5255 p8663
theorem n15740 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) (h6423 : (e6423 _v)) : (e8322 _v) := by
  have p15218 := n15218 _v _q 
  have p15739 := n15739 _v _q h5362 h6423
  simp only [e2529, e8310, e8315, e8317, e8319, e8320, e8321, e8322, e11298] at *
  tauto
theorem n15741 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) : (e8050 _v) := by
  have p15207 := n15207 _v _q 
  have p12901 := n12901 _v _q h5362
  simp only [e2475, e8038, e8043, e8045, e8047, e8048, e8049, e8050, e11165] at *
  tauto
theorem n15742 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) : (e8045 _v) := by
  have p15206 := n15206 _v _q 
  have p15741 := n15741 _v _q h5362
  simp only [e8043, e8045, e8047, e8048, e8049, e8050, e8490] at *
  tauto
theorem n15743 (_v : Vars) (_q : Query _v) (h6423 : (e6423 _v)) : (e7668 _v) := by
  have p14544 := n14544 _v _q 
  have p14136 := n14136 _v _q h6423
  simp only [e2351, e4156, e4157, e4158, e4159, e6575, e7660, e7668, e7671] at *
  tauto
theorem n15744 (_v : Vars) (_q : Query _v) (h6423 : (e6423 _v)) : (e4156 _v) := by
  have p11524 := n11524 _v _q 
  have p15743 := n15743 _v _q h6423
  simp only [e4156, e4157, e4158, e4159, e7660, e7661, e7668] at *
  tauto
theorem n15745 (_v : Vars) (_q : Query _v) (h6423 : (e6423 _v)) : (e8103 _v) := by
  have p14626 := n14626 _v _q 
  have p12947 := n12947 _v _q h6423
  simp only [e2179, e4608, e4609, e4610, e4611, e6501, e8095, e8103, e8106] at *
  tauto
theorem n15746 (_v : Vars) (_q : Query _v) (h6423 : (e6423 _v)) : (e6549 _v) := by
  have p5255 := n5255 _v _q 
  have p8452 := n8452 _v _q h6423
  have p8663 := n8663 _v _q 
  have p5257 := n5257 _v _q 
  exact FloorCertificate.node_15746 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e110 _v) p5255 p8452 p8663 p5257
theorem n15747 (_v : Vars) (_q : Query _v) (h6423 : (e6423 _v)) : (e6879 _v) := by
  have p14643 := n14643 _v _q 
  have p15746 := n15746 _v _q h6423
  simp only [e2296, e3150, e3152, e3155, e3156, e6549, e6878, e6879, e6882] at *
  tauto
theorem n15748 (_v : Vars) (_q : Query _v) (h6423 : (e6423 _v)) : (e6600 _v) := by
  have p5257 := n5257 _v _q 
  have p5255 := n5255 _v _q 
  have p5391 := n5391 _v _q 
  have p8452 := n8452 _v _q h6423
  exact FloorCertificate.node_15748 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p5257 p5255 p5391 p8452
theorem n15749 (_v : Vars) (_q : Query _v) (h6423 : (e6423 _v)) : (e7416 _v) := by
  have p14534 := n14534 _v _q 
  have p15748 := n15748 _v _q h6423
  simp only [e2402, e3937, e3939, e3942, e3943, e6600, e7415, e7416, e7419] at *
  tauto
theorem n15750 (_v : Vars) (_q : Query _v) (h2296 : (e2296 _v)) (h6575 : (e6575 _v)) : (e2179 _v) := by
  have p8583 := n8583 _v _q h2296
  have p5257 := n5257 _v _q 
  have p11413 := n11413 _v _q h6575
  exact FloorCertificate.node_15750 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e110 _v) p8583 p5257 p11413
theorem n15751 (_v : Vars) (_q : Query _v) (h2296 : (e2296 _v)) (h6575 : (e6575 _v)) : (e4616 _v) := by
  have p14684 := n14684 _v _q 
  have p15750 := n15750 _v _q h2296 h6575
  simp only [e2179, e3158, e3159, e3160, e3161, e3162, e4616, e6501, e8109] at *
  tauto
theorem n15752 (_v : Vars) (_q : Query _v) (h2296 : (e2296 _v)) : (e2242 _v) := by
  have p8583 := n8583 _v _q h2296
  have p5257 := n5257 _v _q 
  exact FloorCertificate.node_15752 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e110 _v) p8583 p5257
theorem n15753 (_v : Vars) (_q : Query _v) (h2296 : (e2296 _v)) : (e4686 _v) := by
  have p14708 := n14708 _v _q 
  have p15752 := n15752 _v _q h2296
  simp only [e2242, e4678, e4679, e4683, e4684, e4685, e4686, e6525, e8180] at *
  tauto
theorem n15754 (_v : Vars) (_q : Query _v) (h2296 : (e2296 _v)) : (e4679 _v) := by
  have p14989 := n14989 _v _q 
  have p15753 := n15753 _v _q h2296
  simp only [e4678, e4679, e4683, e4684, e4685, e4686, e4967] at *
  tauto
theorem n15755 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) : (e5223 _v) := by
  have p7488 := n7488 _v _q h5362
  have p4016 := n4016 _v _q 
  exact FloorCertificate.node_15755 (e2 _v) (e7 _v) (e9 _v) (e45 _v) (e110 _v) p7488 p4016
theorem n15756 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) : (e5250 _v) := by
  have p14996 := n14996 _v _q 
  have p15755 := n15755 _v _q h5362
  simp only [e214, e5223, e5237, e5240, e5247, e5248, e5249, e5250, e8677] at *
  tauto
theorem n15757 (_v : Vars) (_q : Query _v) (h1995 : (e1995 _v)) (h5362 : (e5362 _v)) (h6480 : (e6480 _v)) : (e48 _v) := by
  have p8575 := n8575 _v _q h6480
  have p15572 := n15572 _v _q h1995
  have p7488 := n7488 _v _q h5362
  have p8663 := n8663 _v _q 
  exact FloorCertificate.node_15757 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8575 p15572 p7488 p8663
theorem n15758 (_v : Vars) (_q : Query _v) (h1995 : (e1995 _v)) (h5362 : (e5362 _v)) (h6480 : (e6480 _v)) : (e60 _v) := by
  have p14152 := n14152 _v _q 
  have p15757 := n15757 _v _q h1995 h5362 h6480
  simp only [e48, e51, e52, e57, e58, e59, e60, e5108, e5125] at *
  tauto
theorem n15759 (_v : Vars) (_q : Query _v) (h1995 : (e1995 _v)) (h5362 : (e5362 _v)) (h6480 : (e6480 _v)) : (e6716 _v) := by
  have p7488 := n7488 _v _q h5362
  have p15572 := n15572 _v _q h1995
  have p8575 := n8575 _v _q h6480
  exact FloorCertificate.node_15759 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p7488 p15572 p8575
theorem n15760 (_v : Vars) (_q : Query _v) (h1995 : (e1995 _v)) (h5362 : (e5362 _v)) (h6480 : (e6480 _v)) : (e7727 _v) := by
  have p15077 := n15077 _v _q 
  have p15759 := n15759 _v _q h1995 h5362 h6480
  simp only [e2680, e6716, e7714, e7717, e7724, e7725, e7726, e7727, e10986] at *
  tauto
theorem n15761 (_v : Vars) (_q : Query _v) (h6454 : (e6454 _v)) : (e7416 _v) := by
  have p14534 := n14534 _v _q 
  have p12906 := n12906 _v _q h6454
  simp only [e2402, e3937, e3939, e3942, e3943, e6600, e7415, e7416, e7419] at *
  tauto
theorem n15762 (_v : Vars) (_q : Query _v) (h6454 : (e6454 _v)) : (e3937 _v) := by
  have p15012 := n15012 _v _q 
  have p15761 := n15761 _v _q h6454
  simp only [e3937, e3939, e3942, e3943, e7415, e7416, e7633] at *
  tauto
theorem n15763 (_v : Vars) (_q : Query _v) (h6454 : (e6454 _v)) : (e7955 _v) := by
  have p14601 := n14601 _v _q 
  have p8430 := n8430 _v _q h6454
  simp only [e2061, e4434, e4435, e4436, e4437, e6454, e7947, e7955, e7958] at *
  tauto
theorem n15764 (_v : Vars) (_q : Query _v) (h6454 : (e6454 _v)) : (e4434 _v) := by
  have p15307 := n15307 _v _q 
  have p15763 := n15763 _v _q h6454
  simp only [e4434, e4435, e4436, e4437, e7947, e7948, e7955] at *
  tauto
theorem n15765 (_v : Vars) (_q : Query _v) (h6454 : (e6454 _v)) : (e6549 _v) := by
  have p8663 := n8663 _v _q 
  have p8430 := n8430 _v _q h6454
  have p5255 := n5255 _v _q 
  exact FloorCertificate.node_15765 (e2 _v) (e9 _v) (e17 _v) (e110 _v) p8663 p8430 p5255
theorem n15766 (_v : Vars) (_q : Query _v) (h6454 : (e6454 _v)) : (e6879 _v) := by
  have p14643 := n14643 _v _q 
  have p15765 := n15765 _v _q h6454
  simp only [e2296, e3150, e3152, e3155, e3156, e6549, e6878, e6879, e6882] at *
  tauto
theorem n15767 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) (h6454 : (e6454 _v)) : (e8322 _v) := by
  have p15218 := n15218 _v _q 
  have p12908 := n12908 _v _q h5362 h6454
  simp only [e2529, e8310, e8315, e8317, e8319, e8320, e8321, e8322, e11298] at *
  tauto
theorem n15768 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) (h6454 : (e6454 _v)) : (e8317 _v) := by
  have p11541 := n11541 _v _q 
  have p15767 := n15767 _v _q h5362 h6454
  simp only [e8315, e8317, e8319, e8320, e8321, e8322, e8491] at *
  tauto
theorem n15769 (_v : Vars) (_q : Query _v) (h6454 : (e6454 _v)) : (e8103 _v) := by
  have p14626 := n14626 _v _q 
  have p12905 := n12905 _v _q h6454
  simp only [e2179, e4608, e4609, e4610, e4611, e6501, e8095, e8103, e8106] at *
  tauto
theorem n15770 (_v : Vars) (_q : Query _v) (h6575 : (e6575 _v)) : (e7668 _v) := by
  have p14544 := n14544 _v _q 
  have p11413 := n11413 _v _q h6575
  simp only [e2351, e4156, e4157, e4158, e4159, e6575, e7660, e7668, e7671] at *
  tauto
theorem n15771 (_v : Vars) (_q : Query _v) (h6575 : (e6575 _v)) : (e4156 _v) := by
  have p11524 := n11524 _v _q 
  have p15770 := n15770 _v _q h6575
  simp only [e4156, e4157, e4158, e4159, e7660, e7661, e7668] at *
  tauto
theorem n15772 (_v : Vars) (_q : Query _v) (h6501 : (e6501 _v)) : (e6525 _v) := by
  have p8557 := n8557 _v _q 
  have p8554 := n8554 _v _q h6501
  simp only [e2179, e2242, e6501, e6525, e8556] at *
  tauto
theorem n15773 (_v : Vars) (_q : Query _v) (h6501 : (e6501 _v)) : (e8174 _v) := by
  have p14634 := n14634 _v _q 
  have p15772 := n15772 _v _q h6501
  simp only [e2242, e4673, e4674, e4675, e4676, e6525, e8166, e8174, e8177] at *
  tauto
theorem n15774 (_v : Vars) (_q : Query _v) (h2242 : (e2242 _v)) : (e4686 _v) := by
  have p14708 := n14708 _v _q 
  have p8553 := n8553 _v _q h2242
  simp only [e2242, e4678, e4679, e4683, e4684, e4685, e4686, e6525, e8180] at *
  tauto
theorem n15775 (_v : Vars) (_q : Query _v) (h2242 : (e2242 _v)) : (e4679 _v) := by
  have p14989 := n14989 _v _q 
  have p15774 := n15774 _v _q h2242
  simp only [e4678, e4679, e4683, e4684, e4685, e4686, e4967] at *
  tauto
theorem n15776 (_v : Vars) (_q : Query _v)  : (e8223 _v) := by
  simp only [e3150, e3152, e3155, e3156, e6878, e8223] at *
  tauto
theorem n15777 (_v : Vars) (_q : Query _v) (h6549 : (e6549 _v)) : (e6879 _v) := by
  have p14643 := n14643 _v _q 
  have p8544 := n8544 _v _q h6549
  simp only [e2296, e3150, e3152, e3155, e3156, e6549, e6878, e6879, e6882] at *
  tauto
end
end Assembly
