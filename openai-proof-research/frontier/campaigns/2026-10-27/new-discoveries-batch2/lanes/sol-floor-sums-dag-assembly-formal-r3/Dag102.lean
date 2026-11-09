import Dag101
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n14104 (_v : Vars) (_q : Query _v) (h5195 : (e5195 _v)) : (e2364 _v) := by
  have p12849 := n12849 _v _q 
  have p12839 := n12839 _v _q h5195
  simp only [e2358, e2364, e6571, e12848] at *
  tauto
theorem n14105 (_v : Vars) (_q : Query _v) (h5195 : (e5195 _v)) : (e2536 _v) := by
  have p12689 := n12689 _v _q 
  have p8549 := n8549 _v _q h5195
  simp only [e196, e2536, e5195, e12688] at *
  tauto
theorem n14106 (_v : Vars) (_q : Query _v) (h5195 : (e5195 _v)) : (e2310 _v) := by
  have p11439 := n11439 _v _q 
  have p14105 := n14105 _v _q h5195
  simp only [e2310, e2536, e6656, e11438] at *
  tauto
theorem n14107 (_v : Vars) (_q : Query _v) (h6555 : (e6555 _v)) : (e2529 _v) := by
  have p12781 := n12781 _v _q 
  have p12851 := n12851 _v _q h6555
  simp only [e2529, e2536, e6656, e12780] at *
  tauto
theorem n14108 (_v : Vars) (_q : Query _v) (h6555 : (e6555 _v)) : (e196 _v) := by
  have p12689 := n12689 _v _q 
  have p12851 := n12851 _v _q h6555
  simp only [e196, e2536, e6656, e12688] at *
  tauto
theorem n14109 (_v : Vars) (_q : Query _v) (h7807 : (e7807 _v)) : (e5093 _v) := by
  have p11468 := n11468 _v _q 
  have p11350 := n11350 _v _q h7807
  simp only [e13, e2303, e5093, e7807, e11467] at *
  tauto
theorem n14110 (_v : Vars) (_q : Query _v) (h7807 : (e7807 _v)) : (e2254 _v) := by
  have p12820 := n12820 _v _q 
  have p14109 := n14109 _v _q h7807
  simp only [e13, e2254, e5093, e12819] at *
  tauto
theorem n14112 (_v : Vars) (_q : Query _v)  : (e14111 _v) := by
  by_contra hc
  change ¬ ((¬ (e2691 _v)) ∨ (e2475 _v)) at hc
  have h2691 : (e2691 _v) := by
    tauto
  have h8038 : (e8038 _v) := by
    change (¬ (e2475 _v))
    tauto
  have p12872 := n12872 _v _q h2691 h8038
  exact p12872
theorem n14113 (_v : Vars) (_q : Query _v) (h8038 : (e8038 _v)) : (e6724 _v) := by
  have p14112 := n14112 _v _q 
  have p8602 := n8602 _v _q h8038
  simp only [e2475, e2691, e6724, e8038, e14111] at *
  tauto
theorem n14114 (_v : Vars) (_q : Query _v) (h6684 : (e6684 _v)) : (e196 _v) := by
  have p12807 := n12807 _v _q 
  have p12804 := n12804 _v _q h6684
  simp only [e196, e2598, e6684, e12806] at *
  tauto
theorem n14115 (_v : Vars) (_q : Query _v) (h6684 : (e6684 _v)) : (e6720 _v) := by
  have p13991 := n13991 _v _q 
  have p14114 := n14114 _v _q h6684
  simp only [e196, e496, e5195, e6720, e13990] at *
  tauto
theorem n14116 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) : (e2733 _v) := by
  have p12879 := n12879 _v _q 
  have p7488 := n7488 _v _q h5362
  simp only [e436, e2733, e5362, e12878] at *
  tauto
theorem n14117 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) : (e2585 _v) := by
  have p10946 := n10946 _v _q 
  have p14116 := n14116 _v _q h5362
  simp only [e2585, e2733, e6750, e10945] at *
  tauto
theorem n14118 (_v : Vars) (_q : Query _v) (h6758 : (e6758 _v)) : (e2303 _v) := by
  have p12815 := n12815 _v _q 
  have p8425 := n8425 _v _q h6758
  simp only [e2303, e2746, e6758, e12814] at *
  tauto
theorem n14119 (_v : Vars) (_q : Query _v) (h6758 : (e6758 _v)) : (e2529 _v) := by
  have p11387 := n11387 _v _q 
  have p14118 := n14118 _v _q h6758
  simp only [e2303, e2529, e7807, e11386] at *
  tauto
theorem n14120 (_v : Vars) (_q : Query _v) (h8310 : (e8310 _v)) : (e6724 _v) := by
  have p14112 := n14112 _v _q 
  have p12880 := n12880 _v _q h8310
  simp only [e2475, e2691, e6724, e8038, e14111] at *
  tauto
theorem n14121 (_v : Vars) (_q : Query _v) (h6758 : (e6758 _v)) : (e2358 _v) := by
  have p8451 := n8451 _v _q 
  have p14118 := n14118 _v _q h6758
  simp only [e2303, e2358, e7807, e8450] at *
  tauto
theorem n14122 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e2358 _v) := by
  have p12849 := n12849 _v _q 
  have p12893 := n12893 _v _q h6784
  simp only [e2358, e2364, e6583, e12848] at *
  tauto
theorem n14123 (_v : Vars) (_q : Query _v) (h6636 : (e6636 _v)) : (e6656 _v) := by
  have p11135 := n11135 _v _q 
  have p11031 := n11031 _v _q h6636
  simp only [e2482, e2536, e6636, e6656, e11134] at *
  tauto
theorem n14124 (_v : Vars) (_q : Query _v) (h6636 : (e6636 _v)) : (e196 _v) := by
  have p12689 := n12689 _v _q 
  have p14123 := n14123 _v _q h6636
  simp only [e196, e2536, e6656, e12688] at *
  tauto
theorem n14125 (_v : Vars) (_q : Query _v) (h6636 : (e6636 _v)) : (e2529 _v) := by
  have p12781 := n12781 _v _q 
  have p14123 := n14123 _v _q h6636
  simp only [e2529, e2536, e6656, e12780] at *
  tauto
theorem n14126 (_v : Vars) (_q : Query _v) (h2691 : (e2691 _v)) : (e2475 _v) := by
  have p14112 := n14112 _v _q 
  have p11457 := n11457 _v _q h2691
  simp only [e2475, e2691, e6724, e14111] at *
  tauto
theorem n14127 (_v : Vars) (_q : Query _v) (h6758 : (e6758 _v)) : (e79 _v) := by
  have p11490 := n11490 _v _q 
  have p14118 := n14118 _v _q h6758
  simp only [e79, e2303, e7807, e11489] at *
  tauto
theorem n14128 (_v : Vars) (_q : Query _v) (h6636 : (e6636 _v)) : (e79 _v) := by
  have p12546 := n12546 _v _q 
  have p11031 := n11031 _v _q h6636
  simp only [e79, e2482, e6636, e12545] at *
  tauto
theorem n14129 (_v : Vars) (_q : Query _v) (h6636 : (e6636 _v)) : (e2680 _v) := by
  have p7732 := n7732 _v _q 
  have p14128 := n14128 _v _q h6636
  simp only [e79, e2680, e5138, e7731] at *
  tauto
theorem n14130 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e196 _v) := by
  have p12900 := n12900 _v _q 
  have p12894 := n12894 _v _q h6784
  simp only [e196, e2585, e6676, e12899] at *
  tauto
theorem n14131 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e6720 _v) := by
  have p13991 := n13991 _v _q 
  have p14130 := n14130 _v _q h6784
  simp only [e196, e496, e5195, e6720, e13990] at *
  tauto
theorem n14132 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) : (e48 _v) := by
  have p11369 := n11369 _v _q 
  have p14116 := n14116 _v _q h5362
  simp only [e48, e2733, e6750, e11368] at *
  tauto
theorem n14133 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) : (e2634 _v) := by
  have p12843 := n12843 _v _q 
  have p7488 := n7488 _v _q h5362
  simp only [e436, e2634, e5362, e12842] at *
  tauto
theorem n14134 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) : (e2482 _v) := by
  have p11035 := n11035 _v _q 
  have p14133 := n14133 _v _q h5362
  simp only [e2482, e2634, e6700, e11034] at *
  tauto
theorem n14135 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) : (e2310 _v) := by
  have p11365 := n11365 _v _q 
  have p14133 := n14133 _v _q h5362
  simp only [e2310, e2634, e6700, e11364] at *
  tauto
theorem n14136 (_v : Vars) (_q : Query _v) (h6423 : (e6423 _v)) : (e6575 _v) := by
  have p12904 := n12904 _v _q 
  have p12853 := n12853 _v _q h6423
  simp only [e2061, e2351, e6454, e6575, e12903] at *
  tauto
theorem n14137 (_v : Vars) (_q : Query _v) (h496 : (e496 _v)) : (e5195 _v) := by
  have p13991 := n13991 _v _q 
  have p8144 := n8144 _v _q h496
  simp only [e196, e496, e5195, e6720, e13990] at *
  tauto
theorem n14138 (_v : Vars) (_q : Query _v) (h6636 : (e6636 _v)) : (e6676 _v) := by
  have p12579 := n12579 _v _q 
  have p11031 := n11031 _v _q h6636
  simp only [e2482, e2585, e6636, e6676, e12578] at *
  tauto
theorem n14139 (_v : Vars) (_q : Query _v) (h6636 : (e6636 _v)) : (e6750 _v) := by
  have p10946 := n10946 _v _q 
  have p14138 := n14138 _v _q h6636
  simp only [e2585, e2733, e6676, e6750, e10945] at *
  tauto
theorem n14140 (_v : Vars) (_q : Query _v) (h6583 : (e6583 _v)) : (e196 _v) := by
  have p12900 := n12900 _v _q 
  have p12887 := n12887 _v _q h6583
  simp only [e196, e2585, e6676, e12899] at *
  tauto
theorem n14141 (_v : Vars) (_q : Query _v) (h6571 : (e6571 _v)) : (e2746 _v) := by
  have p12815 := n12815 _v _q 
  have p11445 := n11445 _v _q h6571
  simp only [e2303, e2746, e7807, e12814] at *
  tauto
theorem n14142 (_v : Vars) (_q : Query _v) (h6571 : (e6571 _v)) : (e2364 _v) := by
  have p12849 := n12849 _v _q 
  have p8447 := n8447 _v _q h6571
  simp only [e2358, e2364, e6571, e12848] at *
  tauto
theorem n14143 (_v : Vars) (_q : Query _v) (h6571 : (e6571 _v)) : (e2793 _v) := by
  have p11476 := n11476 _v _q 
  have p14142 := n14142 _v _q h6571
  simp only [e2364, e2793, e6583, e11475] at *
  tauto
theorem n14144 (_v : Vars) (_q : Query _v)  : (e5096 _v) := by
  have p11573 := n11573 _v _q 
  change ((e18 _v) ↔ (e5090 _v)) at p11573
  simp only [e5096, e5094, e5095, p11573]
theorem n14145 (_v : Vars) (_q : Query _v)  : (e11580 _v) := by
  have p14144 := n14144 _v _q 
  have p12960 := n12960 _v _q 
  change ((e5094 _v) ↔ (e5095 _v)) at p14144
  change ((e5084 _v) ↔ (e8622 _v)) at p12960
  simp only [e11580, e8610, e8623, p14144, p12960]
theorem n14147 (_v : Vars) (_q : Query _v)  : (e14146 _v) := by
  simp only [e5, e6, e8, e10, e11, e12, e13, e26, e27, e28, e30, e34, e35, e41, e42, e5089, e5090, e5093, e5095, e5098, e5100, e5102, e5103, e5104, e5105, e5106, e8622, e8623, e8624, e8625, e8626, e14146] at *
  omega
theorem n14148 (_v : Vars) (_q : Query _v)  : (e11581 _v) := by
  have p14145 := n14145 _v _q 
  have p14147 := n14147 _v _q 
  exact (Iff.trans p14145 p14147)
theorem n14149 (_v : Vars) (_q : Query _v)  : (e8626 _v) := by
  have p8611 := n8611 _v _q 
  have p14148 := n14148 _v _q 
  simp only [e13, e18, e28, e30, e34, e35, e5083, e5084, e5089, e5090, e5093, e5094, e5095, e5098, e5100, e5102, e5103, e5104, e5105, e5106, e8610, e8622, e8624, e8625, e8626, e11581] at *
  tauto
theorem n14151 (_v : Vars) (_q : Query _v)  : (e12966 _v) := by
  have p10426 := n10426 _v _q 
  have p12970 := n12970 _v _q 
  simp only [e48, e50, e51, e52, e57, e58, e59, e60, e62, e70, e72, e75, e76, e5108, e5109, e5110, e5111, e5118, e5119, e5122, e5125, e5127, e8633, e8634, e12966, e12969] at *
  tauto
end
end Assembly
