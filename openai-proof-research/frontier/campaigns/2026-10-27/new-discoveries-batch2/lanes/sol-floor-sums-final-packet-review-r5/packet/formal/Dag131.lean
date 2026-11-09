import Dag130
import generated.th_lemma_9
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n15552 (_v : Vars) (_q : Query _v) (h7742 : (e7742 _v)) : (e8408 _v) := by
  have p15435 := n15435 _v _q 
  have p11469 := n11469 _v _q h7742
  simp only [e2799, e6780, e8395, e8398, e8405, e8406, e8407, e8408, e11332] at *
  tauto
theorem n15553 (_v : Vars) (_q : Query _v) (h7742 : (e7742 _v)) : (e8398 _v) := by
  have p11470 := n11470 _v _q 
  have p15552 := n15552 _v _q h7742
  simp only [e8395, e8398, e8405, e8406, e8407, e8408, e8462] at *
  tauto
theorem n15554 (_v : Vars) (_q : Query _v) (h8038 : (e8038 _v)) : (e7754 _v) := by
  have p14942 := n14942 _v _q 
  have p12871 := n12871 _v _q h8038
  simp only [e2132, e7742, e7747, e7749, e7751, e7752, e7753, e7754, e11001] at *
  tauto
theorem n15555 (_v : Vars) (_q : Query _v) (h8038 : (e8038 _v)) : (e7749 _v) := by
  have p14941 := n14941 _v _q 
  have p15554 := n15554 _v _q h8038
  simp only [e7747, e7749, e7751, e7752, e7753, e7754, e8446] at *
  tauto
theorem n15556 (_v : Vars) (_q : Query _v) (h8038 : (e8038 _v)) : (e5105 _v) := by
  have p15204 := n15204 _v _q 
  have p12857 := n12857 _v _q h8038
  simp only [e13, e5093, e5098, e5100, e5102, e5103, e5104, e5105, e8622] at *
  tauto
theorem n15557 (_v : Vars) (_q : Query _v) (h2364 : (e2364 _v)) (h6656 : (e6656 _v)) : (e5093 _v) := by
  have p10893 := n10893 _v _q 
  have p11499 := n11499 _v _q h6656
  have p8527 := n8527 _v _q h2364
  exact FloorCertificate.node_15557 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p10893 p11499 p8527
theorem n15558 (_v : Vars) (_q : Query _v) (h2364 : (e2364 _v)) (h6656 : (e6656 _v)) : (e5105 _v) := by
  have p15204 := n15204 _v _q 
  have p15557 := n15557 _v _q h2364 h6656
  simp only [e13, e5093, e5098, e5100, e5102, e5103, e5104, e5105, e8622] at *
  tauto
theorem n15559 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e8375 _v) := by
  have p14675 := n14675 _v _q 
  have p11473 := n11473 _v _q h6784
  simp only [e2793, e4897, e4898, e4899, e4900, e6784, e8367, e8375, e8378] at *
  tauto
theorem n15560 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e4899 _v) := by
  have p15064 := n15064 _v _q 
  have p15559 := n15559 _v _q h6784
  simp only [e4897, e4898, e4899, e4900, e8367, e8368, e8375] at *
  tauto
theorem n15561 (_v : Vars) (_q : Query _v) (h7742 : (e7742 _v)) (h8406 : (e8406 _v)) : (e7489 _v) := by
  have p15435 := n15435 _v _q 
  have p11472 := n11472 _v _q h8406
  have p11469 := n11469 _v _q h7742
  simp only [e2799, e6780, e8395, e8398, e8405, e8406, e8407, e8408, e11332] at *
  tauto
theorem n15563 (_v : Vars) (_q : Query _v)  : (e15562 _v) := by
  by_contra hc
  change ¬ ((e8398 _v) ∨ (e2132 _v)) at hc
  have h7742 : (e7742 _v) := by
    change (¬ (e2132 _v))
    tauto
  have h8406 : (e8406 _v) := by
    change (¬ (e8398 _v))
    tauto
  have p15561 := n15561 _v _q h7742 h8406
  exact p15561
theorem n15564 (_v : Vars) (_q : Query _v) (h6758 : (e6758 _v)) : (e8375 _v) := by
  have p14675 := n14675 _v _q 
  have p12891 := n12891 _v _q h6758
  simp only [e2793, e4897, e4898, e4899, e4900, e6784, e8367, e8375, e8378] at *
  tauto
theorem n15565 (_v : Vars) (_q : Query _v) (h2364 : (e2364 _v)) : (e2793 _v) := by
  have p11476 := n11476 _v _q 
  have p8527 := n8527 _v _q h2364
  simp only [e2364, e2793, e6583, e11475] at *
  tauto
theorem n15566 (_v : Vars) (_q : Query _v) (h2364 : (e2364 _v)) : (e4910 _v) := by
  have p14701 := n14701 _v _q 
  have p15565 := n15565 _v _q h2364
  simp only [e2793, e4902, e4903, e4907, e4908, e4909, e4910, e6784, e8381] at *
  tauto
theorem n15567 (_v : Vars) (_q : Query _v) (h2364 : (e2364 _v)) : (e4903 _v) := by
  have p14973 := n14973 _v _q 
  have p15566 := n15566 _v _q h2364
  simp only [e4902, e4903, e4907, e4908, e4909, e4910, e4961] at *
  tauto
theorem n15568 (_v : Vars) (_q : Query _v) (h7807 : (e7807 _v)) : (e2746 _v) := by
  have p12815 := n12815 _v _q 
  have p11350 := n11350 _v _q h7807
  simp only [e2303, e2746, e7807, e12814] at *
  tauto
theorem n15569 (_v : Vars) (_q : Query _v) (h7807 : (e7807 _v)) : (e3984 _v) := by
  have p14691 := n14691 _v _q 
  have p15568 := n15568 _v _q h7807
  simp only [e2746, e3976, e3977, e3981, e3982, e3983, e3984, e6758, e7456] at *
  tauto
theorem n15570 (_v : Vars) (_q : Query _v) (h8038 : (e8038 _v)) : (e7517 _v) := by
  have p15196 := n15196 _v _q 
  have p14113 := n14113 _v _q h8038
  simp only [e2691, e6724, e7493, e7494, e7495, e7496, e7497, e7517, e10904] at *
  tauto
theorem n15571 (_v : Vars) (_q : Query _v) (h8038 : (e8038 _v)) : (e7493 _v) := by
  have p15195 := n15195 _v _q 
  have p15570 := n15570 _v _q h8038
  simp only [e7493, e7494, e7495, e7496, e7497, e7498, e7517] at *
  tauto
theorem n15572 (_v : Vars) (_q : Query _v) (h1995 : (e1995 _v)) : (e1995 _v) := by
  exact h1995
theorem n15573 (_v : Vars) (_q : Query _v) (h1995 : (e1995 _v)) : (e4575 _v) := by
  have p14696 := n14696 _v _q 
  have p15572 := n15572 _v _q h1995
  simp only [e1995, e4567, e4568, e4572, e4573, e4574, e4575, e6423, e8066] at *
  tauto
theorem n15574 (_v : Vars) (_q : Query _v) (h1995 : (e1995 _v)) : (e4567 _v) := by
  have p8485 := n8485 _v _q 
  have p15573 := n15573 _v _q h1995
  simp only [e4567, e4568, e4572, e4573, e4574, e4575, e4956] at *
  tauto
theorem n15575 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e8157 _v) := by
  have p14632 := n14632 _v _q 
  have p12893 := n12893 _v _q h6784
  simp only [e2364, e4648, e4649, e4650, e4651, e6583, e8149, e8157, e8160] at *
  tauto
theorem n15576 (_v : Vars) (_q : Query _v) (h2371 : (e2371 _v)) : (e5018 _v) := by
  have p14714 := n14714 _v _q 
  have p11400 := n11400 _v _q h2371
  simp only [e2371, e5018, e6579, e8500] at *
  tauto
theorem n15577 (_v : Vars) (_q : Query _v) (h4302 : (e4302 _v)) : (e4302 _v) := by
  exact h4302
theorem n15578 (_v : Vars) (_q : Query _v) (h4302 : (e4302 _v)) : (e7822 _v) := by
  have p14840 := n14840 _v _q 
  have p15577 := n15577 _v _q h4302
  simp only [e4301, e4302, e4303, e4304, e7822, e7823] at *
  tauto
theorem n15579 (_v : Vars) (_q : Query _v) (h4302 : (e4302 _v)) : (e2585 _v) := by
  have p14579 := n14579 _v _q 
  have p15578 := n15578 _v _q h4302
  simp only [e2585, e4301, e4302, e4303, e4304, e7822, e7830, e7833] at *
  tauto
theorem n15580 (_v : Vars) (_q : Query _v)  : (e8517 _v) := by
  simp only [e8335, e8338, e8345, e8346, e8347, e8517] at *
  tauto
theorem n15581 (_v : Vars) (_q : Query _v) (h7807 : (e7807 _v)) : (e8348 _v) := by
  have p15312 := n15312 _v _q 
  have p12873 := n12873 _v _q h7807
  simp only [e2592, e6672, e8335, e8338, e8345, e8346, e8347, e8348, e11307] at *
  tauto
theorem n15582 (_v : Vars) (_q : Query _v) (h7807 : (e7807 _v)) : (e8338 _v) := by
  have p15580 := n15580 _v _q 
  have p15581 := n15581 _v _q h7807
  simp only [e8335, e8338, e8345, e8346, e8347, e8348, e8517] at *
  tauto
theorem n15583 (_v : Vars) (_q : Query _v) (h8038 : (e8038 _v)) : (e8348 _v) := by
  have p15312 := n15312 _v _q 
  have p12868 := n12868 _v _q h8038
  simp only [e2592, e6672, e8335, e8338, e8345, e8346, e8347, e8348, e11307] at *
  tauto
theorem n15584 (_v : Vars) (_q : Query _v) (h8038 : (e8038 _v)) : (e8338 _v) := by
  have p15580 := n15580 _v _q 
  have p15583 := n15583 _v _q h8038
  simp only [e8335, e8338, e8345, e8346, e8347, e8348, e8517] at *
  tauto
theorem n15585 (_v : Vars) (_q : Query _v) (h8038 : (e8038 _v)) : (e7754 _v) := by
  have p14942 := n14942 _v _q 
  have p12874 := n12874 _v _q h8038
  simp only [e2132, e7742, e7747, e7749, e7751, e7752, e7753, e7754, e11001] at *
  tauto
theorem n15586 (_v : Vars) (_q : Query _v) (h8038 : (e8038 _v)) : (e7749 _v) := by
  have p14941 := n14941 _v _q 
  have p15585 := n15585 _v _q h8038
  simp only [e7747, e7749, e7751, e7752, e7753, e7754, e8446] at *
  tauto
theorem n15587 (_v : Vars) (_q : Query _v) (h6684 : (e6684 _v)) : (e6830 _v) := by
  have p14629 := n14629 _v _q 
  have p14115 := n14115 _v _q h6684
  simp only [e496, e3069, e3071, e3074, e3075, e6720, e6829, e6830, e6833] at *
  tauto
theorem n15588 (_v : Vars) (_q : Query _v) (h6684 : (e6684 _v)) : (e3069 _v) := by
  have p14878 := n14878 _v _q 
  have p15587 := n15587 _v _q h6684
  simp only [e3069, e3071, e3074, e3075, e6829, e6830, e8137] at *
  tauto
theorem n15589 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) : (e7742 _v) := by
  have p11353 := n11353 _v _q 
  have p12876 := n12876 _v _q h5362
  simp only [e2132, e2303, e7742, e7807, e11352] at *
  tauto
theorem n15590 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) : (e7754 _v) := by
  have p14942 := n14942 _v _q 
  have p15589 := n15589 _v _q h5362
  simp only [e2132, e7742, e7747, e7749, e7751, e7752, e7753, e7754, e11001] at *
  tauto
theorem n15591 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) : (e7749 _v) := by
  have p14941 := n14941 _v _q 
  have p15590 := n15590 _v _q h5362
  simp only [e7747, e7749, e7751, e7752, e7753, e7754, e8446] at *
  tauto
theorem n15592 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) : (e6716 _v) := by
  have p8524 := n8524 _v _q 
  have p7488 := n7488 _v _q h5362
  simp only [e436, e2680, e5362, e6716, e8523] at *
  tauto
theorem n15593 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) : (e7727 _v) := by
  have p15077 := n15077 _v _q 
  have p15592 := n15592 _v _q h5362
  simp only [e2680, e6716, e7714, e7717, e7724, e7725, e7726, e7727, e10986] at *
  tauto
theorem n15594 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) : (e4314 _v) := by
  have p14704 := n14704 _v _q 
  have p14117 := n14117 _v _q h5362
  simp only [e2585, e4306, e4307, e4311, e4312, e4313, e4314, e6676, e7836] at *
  tauto
theorem n15595 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) : (e4306 _v) := by
  have p14984 := n14984 _v _q 
  have p15594 := n15594 _v _q h5362
  simp only [e4306, e4307, e4311, e4312, e4313, e4314, e4964] at *
  tauto
theorem n15596 (_v : Vars) (_q : Query _v) (h2364 : (e2364 _v)) (h6423 : (e6423 _v)) : (e7807 _v) := by
  have p8530 := n8530 _v _q 
  have p8452 := n8452 _v _q h6423
  have p8527 := n8527 _v _q h2364
  simp only [e1995, e2303, e2364, e6423, e6583, e7807, e8529] at *
  tauto
theorem n15597 (_v : Vars) (_q : Query _v) (h2364 : (e2364 _v)) (h6423 : (e6423 _v)) : (e7819 _v) := by
  have p14994 := n14994 _v _q 
  have p15596 := n15596 _v _q h2364 h6423
  simp only [e2303, e7807, e7812, e7814, e7816, e7817, e7818, e7819, e11046] at *
  tauto
end
end Assembly
