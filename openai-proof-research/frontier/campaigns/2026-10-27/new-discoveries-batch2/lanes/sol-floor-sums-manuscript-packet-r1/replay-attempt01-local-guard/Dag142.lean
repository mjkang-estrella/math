import Dag141
import generated.th_lemma_12
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n16049 (_v : Vars) (_q : Query _v) (h2132 : (e2132 _v)) (h6501 : (e6501 _v)) : (e6750 _v) := by
  have p10946 := n10946 _v _q 
  have p12939 := n12939 _v _q h2132 h6501
  simp only [e2585, e2733, e6676, e6750, e10945] at *
  tauto
theorem n16050 (_v : Vars) (_q : Query _v) (h2132 : (e2132 _v)) (h6501 : (e6501 _v)) : (e7597 _v) := by
  have p14525 := n14525 _v _q 
  have p16049 := n16049 _v _q h2132 h6501
  simp only [e2733, e4096, e4097, e4098, e4099, e6750, e7589, e7597, e7600] at *
  tauto
theorem n16051 (_v : Vars) (_q : Query _v) (h2132 : (e2132 _v)) (h6501 : (e6501 _v)) : (e4096 _v) := by
  have p15703 := n15703 _v _q 
  have p16050 := n16050 _v _q h2132 h6501
  simp only [e4096, e4097, e4098, e4099, e7589, e7590, e7597] at *
  tauto
theorem n16052 (_v : Vars) (_q : Query _v) (h2132 : (e2132 _v)) (h6501 : (e6501 _v)) : (e8157 _v) := by
  have p14632 := n14632 _v _q 
  have p12938 := n12938 _v _q h2132 h6501
  simp only [e2364, e4648, e4649, e4650, e4651, e6583, e8149, e8157, e8160] at *
  tauto
theorem n16053 (_v : Vars) (_q : Query _v) (h2132 : (e2132 _v)) (h6501 : (e6501 _v)) : (e7830 _v) := by
  have p14579 := n14579 _v _q 
  have p12939 := n12939 _v _q h2132 h6501
  simp only [e2585, e4301, e4302, e4303, e4304, e6676, e7822, e7830, e7833] at *
  tauto
theorem n16054 (_v : Vars) (_q : Query _v) (h2132 : (e2132 _v)) (h6501 : (e6501 _v)) : (e4301 _v) := by
  have p14840 := n14840 _v _q 
  have p16053 := n16053 _v _q h2132 h6501
  simp only [e4301, e4302, e4303, e4304, e7822, e7823, e7830] at *
  tauto
theorem n16055 (_v : Vars) (_q : Query _v) (h2242 : (e2242 _v)) (h6600 : (e6600 _v)) : (e5093 _v) := by
  have p8553 := n8553 _v _q h2242
  have p10893 := n10893 _v _q 
  have p8439 := n8439 _v _q h6600
  exact FloorCertificate.node_16055 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) p8553 p10893 p8439
theorem n16056 (_v : Vars) (_q : Query _v) (h2242 : (e2242 _v)) (h6600 : (e6600 _v)) : (e5105 _v) := by
  have p15204 := n15204 _v _q 
  have p16055 := n16055 _v _q h2242 h6600
  simp only [e13, e5093, e5098, e5100, e5102, e5103, e5104, e5105, e8622] at *
  tauto
theorem n16057 (_v : Vars) (_q : Query _v) (h6525 : (e6525 _v)) : (e8174 _v) := by
  have p14634 := n14634 _v _q 
  have p8463 := n8463 _v _q h6525
  simp only [e2242, e4673, e4674, e4675, e4676, e6525, e8166, e8174, e8177] at *
  tauto
theorem n16058 (_v : Vars) (_q : Query _v) (h6525 : (e6525 _v)) : (e4675 _v) := by
  have p15965 := n15965 _v _q 
  have p16057 := n16057 _v _q h6525
  simp only [e4673, e4674, e4675, e4676, e8166, e8167, e8174] at *
  tauto
theorem n16059 (_v : Vars) (_q : Query _v) (h6525 : (e6525 _v)) : (e6549 _v) := by
  have p11560 := n11560 _v _q 
  have p8463 := n8463 _v _q h6525
  simp only [e2242, e2296, e6525, e6549, e11559] at *
  tauto
theorem n16060 (_v : Vars) (_q : Query _v) (h6525 : (e6525 _v)) : (e6879 _v) := by
  have p14643 := n14643 _v _q 
  have p16059 := n16059 _v _q h6525
  simp only [e2296, e3150, e3152, e3155, e3156, e6549, e6878, e6879, e6882] at *
  tauto
theorem n16061 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) : (e7754 _v) := by
  have p14942 := n14942 _v _q 
  have p12946 := n12946 _v _q h2468
  simp only [e2132, e7742, e7747, e7749, e7751, e7752, e7753, e7754, e11001] at *
  tauto
theorem n16062 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) : (e7749 _v) := by
  have p14941 := n14941 _v _q 
  have p16061 := n16061 _v _q h2468
  simp only [e7747, e7749, e7751, e7752, e7753, e7754, e8446] at *
  tauto
theorem n16063 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) (h6750 : (e6750 _v)) : (e6549 _v) := by
  have p8586 := n8586 _v _q 
  have p8420 := n8420 _v _q h6750
  have p8438 := n8438 _v _q h2468
  simp only [e2296, e2468, e2733, e6549, e6630, e6750, e8585] at *
  tauto
theorem n16064 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) (h6750 : (e6750 _v)) : (e6879 _v) := by
  have p14643 := n14643 _v _q 
  have p16063 := n16063 _v _q h2468 h6750
  simp only [e2296, e3150, e3152, e3155, e3156, e6549, e6878, e6879, e6882] at *
  tauto
theorem n16065 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) : (e2061 _v) := by
  have p11563 := n11563 _v _q 
  have p8438 := n8438 _v _q h2468
  simp only [e2061, e2468, e6630, e11562] at *
  tauto
theorem n16066 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) : (e4447 _v) := by
  have p14688 := n14688 _v _q 
  have p16065 := n16065 _v _q h2468
  simp only [e2061, e4439, e4440, e4444, e4445, e4446, e4447, e6454, e7961] at *
  tauto
theorem n16067 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) : (e4439 _v) := by
  have p14925 := n14925 _v _q 
  have p16066 := n16066 _v _q h2468
  simp only [e4439, e4440, e4444, e4445, e4446, e4447, e4941] at *
  tauto
theorem n16068 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) : (e1995 _v) := by
  have p11412 := n11412 _v _q 
  have p16065 := n16065 _v _q h2468
  simp only [e1995, e2061, e6454, e11411] at *
  tauto
theorem n16069 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) : (e4575 _v) := by
  have p14696 := n14696 _v _q 
  have p16068 := n16068 _v _q h2468
  simp only [e1995, e4567, e4568, e4572, e4573, e4574, e4575, e6423, e8066] at *
  tauto
theorem n16070 (_v : Vars) (_q : Query _v) (h6750 : (e6750 _v)) : (e6776 _v) := by
  have p8424 := n8424 _v _q 
  have p8420 := n8420 _v _q h6750
  simp only [e2733, e2781, e6750, e6776, e8423] at *
  tauto
theorem n16071 (_v : Vars) (_q : Query _v) (h6750 : (e6750 _v)) : (e7789 _v) := by
  have p14570 := n14570 _v _q 
  have p16070 := n16070 _v _q h6750
  simp only [e2781, e4258, e4259, e4260, e4261, e6776, e7781, e7789, e7792] at *
  tauto
theorem n16072 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) : (e2242 _v) := by
  have p11566 := n11566 _v _q 
  have p8438 := n8438 _v _q h2468
  simp only [e2242, e2468, e6630, e11565] at *
  tauto
theorem n16073 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) : (e4686 _v) := by
  have p14708 := n14708 _v _q 
  have p16072 := n16072 _v _q h2468
  simp only [e2242, e4678, e4679, e4683, e4684, e4685, e4686, e6525, e8180] at *
  tauto
theorem n16074 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) : (e4679 _v) := by
  have p14989 := n14989 _v _q 
  have p16073 := n16073 _v _q h2468
  simp only [e4678, e4679, e4683, e4684, e4685, e4686, e4967] at *
  tauto
theorem n16075 (_v : Vars) (_q : Query _v) (h2529 : (e2529 _v)) (h6525 : (e6525 _v)) : (e6776 _v) := by
  have p8548 := n8548 _v _q h2529
  have p8463 := n8463 _v _q h6525
  exact FloorCertificate.node_16075 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8548 p8463
theorem n16076 (_v : Vars) (_q : Query _v) (h2529 : (e2529 _v)) (h6525 : (e6525 _v)) : (e7789 _v) := by
  have p14570 := n14570 _v _q 
  have p16075 := n16075 _v _q h2529 h6525
  simp only [e2781, e4258, e4259, e4260, e4261, e6776, e7781, e7789, e7792] at *
  tauto
theorem n16077 (_v : Vars) (_q : Query _v) (h2179 : (e2179 _v)) (h6525 : (e6525 _v)) (h6571 : (e6571 _v)) (h6750 : (e6750 _v)) : (e6600 _v) := by
  have p8420 := n8420 _v _q h6750
  have p8447 := n8447 _v _q h6571
  have p15957 := n15957 _v _q h2179
  have p8463 := n8463 _v _q h6525
  exact FloorCertificate.node_16077 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8420 p8447 p15957 p8463
theorem n16078 (_v : Vars) (_q : Query _v) (h2179 : (e2179 _v)) (h6525 : (e6525 _v)) (h6571 : (e6571 _v)) (h6750 : (e6750 _v)) : (e7416 _v) := by
  have p14534 := n14534 _v _q 
  have p16077 := n16077 _v _q h2179 h6525 h6571 h6750
  simp only [e2402, e3937, e3939, e3942, e3943, e6600, e7415, e7416, e7419] at *
  tauto
theorem n16079 (_v : Vars) (_q : Query _v) (h2303 : (e2303 _v)) (h6772 : (e6772 _v)) : (e8038 _v) := by
  have p8461 := n8461 _v _q 
  have p8458 := n8458 _v _q h6772
  have p8448 := n8448 _v _q h2303
  simp only [e2303, e2475, e2787, e6772, e7807, e8038, e8460] at *
  tauto
theorem n16080 (_v : Vars) (_q : Query _v) (h2303 : (e2303 _v)) (h6772 : (e6772 _v)) : (e8050 _v) := by
  have p15207 := n15207 _v _q 
  have p16079 := n16079 _v _q h2303 h6772
  simp only [e2475, e8038, e8043, e8045, e8047, e8048, e8049, e8050, e11165] at *
  tauto
theorem n16081 (_v : Vars) (_q : Query _v) (h2529 : (e2529 _v)) (h6525 : (e6525 _v)) (h6571 : (e6571 _v)) : (e6600 _v) := by
  have p8594 := n8594 _v _q 
  have p8447 := n8447 _v _q h6571
  have p8463 := n8463 _v _q h6525
  have p8548 := n8548 _v _q h2529
  simp only [e2242, e2358, e2402, e2529, e6525, e6571, e6600, e8310, e8593] at *
  tauto
theorem n16082 (_v : Vars) (_q : Query _v) (h2529 : (e2529 _v)) (h6525 : (e6525 _v)) (h6571 : (e6571 _v)) : (e7416 _v) := by
  have p14534 := n14534 _v _q 
  have p16081 := n16081 _v _q h2529 h6525 h6571
  simp only [e2402, e3937, e3939, e3942, e3943, e6600, e7415, e7416, e7419] at *
  tauto
theorem n16083 (_v : Vars) (_q : Query _v) (h6423 : (e6423 _v)) : (e7416 _v) := by
  have p14534 := n14534 _v _q 
  have p12948 := n12948 _v _q h6423
  simp only [e2402, e3937, e3939, e3942, e3943, e6600, e7415, e7416, e7419] at *
  tauto
theorem n16084 (_v : Vars) (_q : Query _v) (h6423 : (e6423 _v)) : (e3937 _v) := by
  have p15012 := n15012 _v _q 
  have p16083 := n16083 _v _q h6423
  simp only [e3937, e3939, e3942, e3943, e7415, e7416, e7633] at *
  tauto
theorem n16085 (_v : Vars) (_q : Query _v) (h6423 : (e6423 _v)) : (e6525 _v) := by
  have p8452 := n8452 _v _q h6423
  have p5255 := n5255 _v _q 
  have p5257 := n5257 _v _q 
  have p8663 := n8663 _v _q 
  exact FloorCertificate.node_16085 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e110 _v) p8452 p5255 p5257 p8663
theorem n16086 (_v : Vars) (_q : Query _v) (h6423 : (e6423 _v)) : (e8174 _v) := by
  have p14634 := n14634 _v _q 
  have p16085 := n16085 _v _q h6423
  simp only [e2242, e4673, e4674, e4675, e4676, e6525, e8166, e8174, e8177] at *
  tauto
theorem n16087 (_v : Vars) (_q : Query _v) (h8320 : (e8320 _v)) : (e2529 _v) := by
  have p15218 := n15218 _v _q 
  have p11543 := n11543 _v _q h8320
  simp only [e2529, e8315, e8317, e8319, e8320, e8321, e8322, e11298] at *
  tauto
theorem n16088 (_v : Vars) (_q : Query _v) (h8320 : (e8320 _v)) : (e196 _v) := by
  have p8552 := n8552 _v _q 
  have p16087 := n16087 _v _q h8320
  simp only [e196, e2529, e8310, e8551] at *
  tauto
theorem n16089 (_v : Vars) (_q : Query _v) (h2781 : (e2781 _v)) (h6549 : (e6549 _v)) : (e8038 _v) := by
  have p8421 := n8421 _v _q h2781
  have p8544 := n8544 _v _q h6549
  exact FloorCertificate.node_16089 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8421 p8544
theorem n16090 (_v : Vars) (_q : Query _v) (h2781 : (e2781 _v)) (h6549 : (e6549 _v)) : (e8050 _v) := by
  have p15207 := n15207 _v _q 
  have p16089 := n16089 _v _q h2781 h6549
  simp only [e2475, e8038, e8043, e8045, e8047, e8048, e8049, e8050, e11165] at *
  tauto
theorem n16091 (_v : Vars) (_q : Query _v) (h2781 : (e2781 _v)) (h6630 : (e6630 _v)) : (e7807 _v) := by
  have p8581 := n8581 _v _q 
  have p8421 := n8421 _v _q h2781
  have p8434 := n8434 _v _q h6630
  simp only [e2303, e2468, e2781, e6630, e6776, e7807, e8580] at *
  tauto
theorem n16092 (_v : Vars) (_q : Query _v) (h2781 : (e2781 _v)) (h6630 : (e6630 _v)) : (e7819 _v) := by
  have p14994 := n14994 _v _q 
  have p16091 := n16091 _v _q h2781 h6630
  simp only [e2303, e7807, e7812, e7814, e7816, e7817, e7818, e7819, e11046] at *
  tauto
theorem n16093 (_v : Vars) (_q : Query _v) (h2733 : (e2733 _v)) (h6600 : (e6600 _v)) : (e7807 _v) := by
  have p8587 := n8587 _v _q h2733
  have p8439 := n8439 _v _q h6600
  exact FloorCertificate.node_16093 (e2 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8587 p8439
end
end Assembly
