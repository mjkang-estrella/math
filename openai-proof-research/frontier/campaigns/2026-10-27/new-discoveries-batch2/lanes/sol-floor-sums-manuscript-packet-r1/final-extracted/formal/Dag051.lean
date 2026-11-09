import Dag050
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n9875 (_v : Vars) (_q : Query _v)  : (e9874 _v) := by
  have p2672 := n2672 _v _q 
  change ((e1458 _v) = (e2670 _v)) at p2672
  simp only [e9874, e1461, e2673, p2672]
theorem n9877 (_v : Vars) (_q : Query _v)  : (e9876 _v) := by
  simp only [e5, e6, e8, e10, e12, e36, e41, e46, e495, e496, e2670, e2673, e9876] at *
  omega
theorem n9879 (_v : Vars) (_q : Query _v)  : (e9878 _v) := by
  have p9875 := n9875 _v _q 
  have p9877 := n9877 _v _q 
  exact (Iff.trans p9875 p9877)
theorem n9880 (_v : Vars) (_q : Query _v)  : (e2678 _v) := by
  have p2676 := n2676 _v _q 
  change ((e1463 _v) = (e2674 _v)) at p2676
  simp only [e2678, e1464, e2677, p2676]
theorem n9881 (_v : Vars) (_q : Query _v)  : (e6373 _v) := by
  simp only [e5, e6, e8, e10, e12, e36, e46, e2674, e2677, e2679, e2680, e6373] at *
  omega
theorem n9882 (_v : Vars) (_q : Query _v)  : (e6374 _v) := by
  have p9880 := n9880 _v _q 
  have p9881 := n9881 _v _q 
  exact (Iff.trans p9880 p9881)
theorem n9884 (_v : Vars) (_q : Query _v)  : (e9883 _v) := by
  have p9882 := n9882 _v _q 
  have p2672 := n2672 _v _q 
  change ((e1464 _v) ↔ (e2680 _v)) at p9882
  change ((e1458 _v) = (e2670 _v)) at p2672
  simp only [e9883, e1465, e6375, p9882, p2672]
theorem n9887 (_v : Vars) (_q : Query _v)  : (e9886 _v) := by
  have p9879 := n9879 _v _q 
  have p9884 := n9884 _v _q 
  change ((e1461 _v) ↔ (e496 _v)) at p9879
  change ((e1465 _v) = (e6375 _v)) at p9884
  simp only [e9886, e5984, e9885, p9879, p9884]
theorem n9889 (_v : Vars) (_q : Query _v)  : (e9888 _v) := by
  have p2683 := n2683 _v _q 
  change ((e1468 _v) = (e2681 _v)) at p2683
  simp only [e9888, e1471, e2684, p2683]
theorem n9891 (_v : Vars) (_q : Query _v)  : (e9890 _v) := by
  simp only [e5, e6, e8, e10, e12, e41, e43, e44, e46, e47, e48, e760, e761, e2681, e2684, e9890] at *
  omega
theorem n9893 (_v : Vars) (_q : Query _v)  : (e9892 _v) := by
  have p9889 := n9889 _v _q 
  have p9891 := n9891 _v _q 
  exact (Iff.trans p9889 p9891)
theorem n9894 (_v : Vars) (_q : Query _v)  : (e2689 _v) := by
  have p2687 := n2687 _v _q 
  change ((e1473 _v) = (e2685 _v)) at p2687
  simp only [e2689, e1474, e2688, p2687]
theorem n9895 (_v : Vars) (_q : Query _v)  : (e6376 _v) := by
  simp only [e5, e6, e8, e10, e12, e43, e44, e46, e760, e761, e2685, e2688, e2690, e2691, e6376] at *
  omega
theorem n9896 (_v : Vars) (_q : Query _v)  : (e6377 _v) := by
  have p9894 := n9894 _v _q 
  have p9895 := n9895 _v _q 
  exact (Iff.trans p9894 p9895)
theorem n9898 (_v : Vars) (_q : Query _v)  : (e9897 _v) := by
  have p9896 := n9896 _v _q 
  have p2683 := n2683 _v _q 
  change ((e1474 _v) ↔ (e2691 _v)) at p9896
  change ((e1468 _v) = (e2681 _v)) at p2683
  simp only [e9897, e1475, e6378, p9896, p2683]
theorem n9901 (_v : Vars) (_q : Query _v)  : (e9900 _v) := by
  have p9893 := n9893 _v _q 
  have p9898 := n9898 _v _q 
  change ((e1471 _v) ↔ (e48 _v)) at p9893
  change ((e1475 _v) = (e6378 _v)) at p9898
  simp only [e9900, e5985, e9899, p9893, p9898]
theorem n9903 (_v : Vars) (_q : Query _v)  : (e9902 _v) := by
  have p2694 := n2694 _v _q 
  change ((e1478 _v) = (e2692 _v)) at p2694
  simp only [e9902, e1481, e2695, p2694]
theorem n9905 (_v : Vars) (_q : Query _v)  : (e9904 _v) := by
  simp only [e5, e6, e8, e10, e12, e41, e46, e266, e267, e781, e782, e2692, e2695, e2696, e2697, e9904] at *
  omega
theorem n9907 (_v : Vars) (_q : Query _v)  : (e9906 _v) := by
  have p9903 := n9903 _v _q 
  have p9905 := n9905 _v _q 
  exact (Iff.trans p9903 p9905)
theorem n9908 (_v : Vars) (_q : Query _v)  : (e2702 _v) := by
  have p2700 := n2700 _v _q 
  change ((e1483 _v) = (e2698 _v)) at p2700
  simp only [e2702, e1484, e2701, p2700]
theorem n9909 (_v : Vars) (_q : Query _v)  : (e6379 _v) := by
  simp only [e5, e6, e8, e10, e12, e46, e266, e267, e781, e782, e2698, e2701, e2703, e2704, e6379] at *
  omega
theorem n9910 (_v : Vars) (_q : Query _v)  : (e6380 _v) := by
  have p9908 := n9908 _v _q 
  have p9909 := n9909 _v _q 
  exact (Iff.trans p9908 p9909)
theorem n9912 (_v : Vars) (_q : Query _v)  : (e9911 _v) := by
  have p9910 := n9910 _v _q 
  have p2694 := n2694 _v _q 
  change ((e1484 _v) ↔ (e2704 _v)) at p9910
  change ((e1478 _v) = (e2692 _v)) at p2694
  simp only [e9911, e1485, e6381, p9910, p2694]
theorem n9915 (_v : Vars) (_q : Query _v)  : (e9914 _v) := by
  have p9907 := n9907 _v _q 
  have p9912 := n9912 _v _q 
  change ((e1481 _v) ↔ (e2697 _v)) at p9907
  change ((e1485 _v) = (e6381 _v)) at p9912
  simp only [e9914, e5986, e9913, p9907, p9912]
theorem n9917 (_v : Vars) (_q : Query _v)  : (e9916 _v) := by
  have p2707 := n2707 _v _q 
  change ((e1488 _v) = (e2705 _v)) at p2707
  simp only [e9916, e1491, e2708, p2707]
theorem n9919 (_v : Vars) (_q : Query _v)  : (e9918 _v) := by
  simp only [e5, e6, e8, e10, e12, e41, e46, e108, e109, e802, e803, e2705, e2708, e2709, e2710, e9918] at *
  omega
theorem n9921 (_v : Vars) (_q : Query _v)  : (e9920 _v) := by
  have p9917 := n9917 _v _q 
  have p9919 := n9919 _v _q 
  exact (Iff.trans p9917 p9919)
theorem n9922 (_v : Vars) (_q : Query _v)  : (e2715 _v) := by
  have p2713 := n2713 _v _q 
  change ((e1493 _v) = (e2711 _v)) at p2713
  simp only [e2715, e1494, e2714, p2713]
theorem n9923 (_v : Vars) (_q : Query _v)  : (e6382 _v) := by
  simp only [e5, e6, e8, e10, e12, e46, e108, e109, e802, e803, e2711, e2714, e2716, e2717, e6382] at *
  omega
theorem n9924 (_v : Vars) (_q : Query _v)  : (e6383 _v) := by
  have p9922 := n9922 _v _q 
  have p9923 := n9923 _v _q 
  exact (Iff.trans p9922 p9923)
theorem n9926 (_v : Vars) (_q : Query _v)  : (e9925 _v) := by
  have p9924 := n9924 _v _q 
  have p2707 := n2707 _v _q 
  change ((e1494 _v) ↔ (e2717 _v)) at p9924
  change ((e1488 _v) = (e2705 _v)) at p2707
  simp only [e9925, e1495, e6384, p9924, p2707]
theorem n9929 (_v : Vars) (_q : Query _v)  : (e9928 _v) := by
  have p9921 := n9921 _v _q 
  have p9926 := n9926 _v _q 
  change ((e1491 _v) ↔ (e2710 _v)) at p9921
  change ((e1495 _v) = (e6384 _v)) at p9926
  simp only [e9928, e5987, e9927, p9921, p9926]
theorem n9931 (_v : Vars) (_q : Query _v)  : (e9930 _v) := by
  have p2719 := n2719 _v _q 
  change ((e1502 _v) = (e215 _v)) at p2719
  simp only [e9930, e1505, e2720, p2719]
theorem n9933 (_v : Vars) (_q : Query _v)  : (e9932 _v) := by
  simp only [e5, e6, e10, e12, e36, e41, e46, e111, e215, e2720, e2721, e2722, e9932] at *
  omega
theorem n9935 (_v : Vars) (_q : Query _v)  : (e9934 _v) := by
  have p9931 := n9931 _v _q 
  have p9933 := n9933 _v _q 
  exact (Iff.trans p9931 p9933)
theorem n9936 (_v : Vars) (_q : Query _v)  : (e2727 _v) := by
  have p2725 := n2725 _v _q 
  change ((e1507 _v) = (e2723 _v)) at p2725
  simp only [e2727, e1508, e2726, p2725]
theorem n9937 (_v : Vars) (_q : Query _v)  : (e6385 _v) := by
  simp only [e5, e6, e10, e12, e36, e46, e111, e213, e214, e2723, e2726, e6385] at *
  omega
theorem n9938 (_v : Vars) (_q : Query _v)  : (e6386 _v) := by
  have p9936 := n9936 _v _q 
  have p9937 := n9937 _v _q 
  exact (Iff.trans p9936 p9937)
theorem n9940 (_v : Vars) (_q : Query _v)  : (e9939 _v) := by
  have p9938 := n9938 _v _q 
  have p2719 := n2719 _v _q 
  change ((e1508 _v) ↔ (e214 _v)) at p9938
  change ((e1502 _v) = (e215 _v)) at p2719
  simp only [e9939, e1509, e6387, p9938, p2719]
theorem n9943 (_v : Vars) (_q : Query _v)  : (e9942 _v) := by
  have p9935 := n9935 _v _q 
  have p9940 := n9940 _v _q 
  change ((e1505 _v) ↔ (e2722 _v)) at p9935
  change ((e1509 _v) = (e6387 _v)) at p9940
  simp only [e9942, e6022, e9941, p9935, p9940]
theorem n9945 (_v : Vars) (_q : Query _v)  : (e9944 _v) := by
  have p2730 := n2730 _v _q 
  change ((e1512 _v) = (e2728 _v)) at p2730
  simp only [e9944, e1515, e2731, p2730]
theorem n9947 (_v : Vars) (_q : Query _v)  : (e9946 _v) := by
  simp only [e5, e6, e10, e12, e41, e43, e44, e46, e111, e760, e761, e2728, e2731, e2732, e2733, e9946] at *
  omega
theorem n9949 (_v : Vars) (_q : Query _v)  : (e9948 _v) := by
  have p9945 := n9945 _v _q 
  have p9947 := n9947 _v _q 
  exact (Iff.trans p9945 p9947)
theorem n9950 (_v : Vars) (_q : Query _v)  : (e2738 _v) := by
  have p2736 := n2736 _v _q 
  change ((e1517 _v) = (e2734 _v)) at p2736
  simp only [e2738, e1518, e2737, p2736]
theorem n9951 (_v : Vars) (_q : Query _v)  : (e6388 _v) := by
  simp only [e5, e6, e10, e12, e43, e44, e46, e111, e760, e761, e2734, e2737, e2739, e2740, e6388] at *
  omega
end
end Assembly
