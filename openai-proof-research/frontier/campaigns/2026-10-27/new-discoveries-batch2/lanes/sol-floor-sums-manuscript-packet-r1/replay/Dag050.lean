import Dag049
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n9808 (_v : Vars) (_q : Query _v)  : (e2603 _v) := by
  have p2601 := n2601 _v _q 
  change ((e1395 _v) = (e2599 _v)) at p2601
  simp only [e2603, e1396, e2602, p2601]
theorem n9809 (_v : Vars) (_q : Query _v)  : (e6347 _v) := by
  simp only [e5, e6, e8, e12, e46, e111, e266, e267, e781, e782, e2599, e2602, e2604, e2605, e6347] at *
  omega
theorem n9810 (_v : Vars) (_q : Query _v)  : (e6348 _v) := by
  have p9808 := n9808 _v _q 
  have p9809 := n9809 _v _q 
  exact (Iff.trans p9808 p9809)
theorem n9812 (_v : Vars) (_q : Query _v)  : (e9811 _v) := by
  have p9810 := n9810 _v _q 
  have p2595 := n2595 _v _q 
  change ((e1396 _v) ↔ (e2605 _v)) at p9810
  change ((e1390 _v) = (e2593 _v)) at p2595
  simp only [e9811, e1397, e6349, p9810, p2595]
theorem n9815 (_v : Vars) (_q : Query _v)  : (e9814 _v) := by
  have p9807 := n9807 _v _q 
  have p9812 := n9812 _v _q 
  change ((e1393 _v) ↔ (e2598 _v)) at p9807
  change ((e1397 _v) = (e6349 _v)) at p9812
  simp only [e9814, e5912, e9813, p9807, p9812]
theorem n9817 (_v : Vars) (_q : Query _v)  : (e9816 _v) := by
  have p2608 := n2608 _v _q 
  change ((e1400 _v) = (e2606 _v)) at p2608
  simp only [e9816, e1403, e2609, p2608]
theorem n9819 (_v : Vars) (_q : Query _v)  : (e9818 _v) := by
  simp only [e5, e6, e8, e12, e41, e46, e108, e109, e111, e802, e803, e2606, e2609, e2610, e2611, e9818] at *
  omega
theorem n9821 (_v : Vars) (_q : Query _v)  : (e9820 _v) := by
  have p9817 := n9817 _v _q 
  have p9819 := n9819 _v _q 
  exact (Iff.trans p9817 p9819)
theorem n9822 (_v : Vars) (_q : Query _v)  : (e2616 _v) := by
  have p2614 := n2614 _v _q 
  change ((e1405 _v) = (e2612 _v)) at p2614
  simp only [e2616, e1406, e2615, p2614]
theorem n9823 (_v : Vars) (_q : Query _v)  : (e6350 _v) := by
  simp only [e5, e6, e8, e12, e46, e108, e109, e111, e802, e803, e2612, e2615, e2617, e2618, e6350] at *
  omega
theorem n9824 (_v : Vars) (_q : Query _v)  : (e6351 _v) := by
  have p9822 := n9822 _v _q 
  have p9823 := n9823 _v _q 
  exact (Iff.trans p9822 p9823)
theorem n9826 (_v : Vars) (_q : Query _v)  : (e9825 _v) := by
  have p9824 := n9824 _v _q 
  have p2608 := n2608 _v _q 
  change ((e1406 _v) ↔ (e2618 _v)) at p9824
  change ((e1400 _v) = (e2606 _v)) at p2608
  simp only [e9825, e1407, e6352, p9824, p2608]
theorem n9829 (_v : Vars) (_q : Query _v)  : (e9828 _v) := by
  have p9821 := n9821 _v _q 
  have p9826 := n9826 _v _q 
  change ((e1403 _v) ↔ (e2611 _v)) at p9821
  change ((e1407 _v) = (e6352 _v)) at p9826
  simp only [e9828, e5913, e9827, p9821, p9826]
theorem n9830 (_v : Vars) (_q : Query _v)  : (e2622 _v) := by
  have p2620 := n2620 _v _q 
  change ((e1414 _v) = (e96 _v)) at p2620
  simp only [e2622, e1880, e2621, p2620]
theorem n9831 (_v : Vars) (_q : Query _v)  : (e6353 _v) := by
  simp only [e5, e6, e10, e12, e36, e41, e46, e96, e250, e251, e2621, e6353] at *
  omega
theorem n9832 (_v : Vars) (_q : Query _v)  : (e6354 _v) := by
  have p9830 := n9830 _v _q 
  have p9831 := n9831 _v _q 
  exact (Iff.trans p9830 p9831)
theorem n9833 (_v : Vars) (_q : Query _v)  : (e2627 _v) := by
  have p2625 := n2625 _v _q 
  change ((e1418 _v) = (e2623 _v)) at p2625
  simp only [e2627, e1419, e2626, p2625]
theorem n9834 (_v : Vars) (_q : Query _v)  : (e6355 _v) := by
  simp only [e5, e6, e10, e12, e36, e46, e78, e79, e2623, e2626, e6355] at *
  omega
theorem n9835 (_v : Vars) (_q : Query _v)  : (e6356 _v) := by
  have p9833 := n9833 _v _q 
  have p9834 := n9834 _v _q 
  exact (Iff.trans p9833 p9834)
theorem n9837 (_v : Vars) (_q : Query _v)  : (e9836 _v) := by
  have p9835 := n9835 _v _q 
  have p2620 := n2620 _v _q 
  change ((e1419 _v) ↔ (e79 _v)) at p9835
  change ((e1414 _v) = (e96 _v)) at p2620
  simp only [e9836, e1421, e6357, p9835, p2620]
theorem n9840 (_v : Vars) (_q : Query _v)  : (e9839 _v) := by
  have p9832 := n9832 _v _q 
  have p9837 := n9837 _v _q 
  change ((e1880 _v) ↔ (e251 _v)) at p9832
  change ((e1421 _v) = (e6357 _v)) at p9837
  simp only [e9839, e5925, e9838, p9832, p9837]
theorem n9841 (_v : Vars) (_q : Query _v)  : (e2632 _v) := by
  have p2630 := n2630 _v _q 
  change ((e1424 _v) = (e2628 _v)) at p2630
  simp only [e2632, e1887, e2631, p2630]
theorem n9842 (_v : Vars) (_q : Query _v)  : (e6358 _v) := by
  simp only [e5, e6, e10, e12, e41, e43, e44, e46, e760, e761, e2628, e2631, e2633, e2634, e6358] at *
  omega
theorem n9843 (_v : Vars) (_q : Query _v)  : (e6359 _v) := by
  have p9841 := n9841 _v _q 
  have p9842 := n9842 _v _q 
  exact (Iff.trans p9841 p9842)
theorem n9844 (_v : Vars) (_q : Query _v)  : (e2639 _v) := by
  have p2637 := n2637 _v _q 
  change ((e1428 _v) = (e2635 _v)) at p2637
  simp only [e2639, e1429, e2638, p2637]
theorem n9845 (_v : Vars) (_q : Query _v)  : (e6360 _v) := by
  simp only [e5, e6, e10, e12, e43, e44, e46, e760, e761, e2635, e2638, e2640, e2641, e6360] at *
  omega
theorem n9846 (_v : Vars) (_q : Query _v)  : (e6361 _v) := by
  have p9844 := n9844 _v _q 
  have p9845 := n9845 _v _q 
  exact (Iff.trans p9844 p9845)
theorem n9848 (_v : Vars) (_q : Query _v)  : (e9847 _v) := by
  have p9846 := n9846 _v _q 
  have p2630 := n2630 _v _q 
  change ((e1429 _v) ↔ (e2641 _v)) at p9846
  change ((e1424 _v) = (e2628 _v)) at p2630
  simp only [e9847, e1431, e6362, p9846, p2630]
theorem n9851 (_v : Vars) (_q : Query _v)  : (e9850 _v) := by
  have p9843 := n9843 _v _q 
  have p9848 := n9848 _v _q 
  change ((e1887 _v) ↔ (e2634 _v)) at p9843
  change ((e1431 _v) = (e6362 _v)) at p9848
  simp only [e9850, e5935, e9849, p9843, p9848]
theorem n9852 (_v : Vars) (_q : Query _v)  : (e2646 _v) := by
  have p2644 := n2644 _v _q 
  change ((e1434 _v) = (e2642 _v)) at p2644
  simp only [e2646, e1894, e2645, p2644]
theorem n9853 (_v : Vars) (_q : Query _v)  : (e6363 _v) := by
  simp only [e5, e6, e10, e12, e41, e46, e266, e267, e781, e782, e2642, e2645, e2647, e2648, e6363] at *
  omega
theorem n9854 (_v : Vars) (_q : Query _v)  : (e6364 _v) := by
  have p9852 := n9852 _v _q 
  have p9853 := n9853 _v _q 
  exact (Iff.trans p9852 p9853)
theorem n9855 (_v : Vars) (_q : Query _v)  : (e2653 _v) := by
  have p2651 := n2651 _v _q 
  change ((e1438 _v) = (e2649 _v)) at p2651
  simp only [e2653, e1439, e2652, p2651]
theorem n9856 (_v : Vars) (_q : Query _v)  : (e6365 _v) := by
  simp only [e5, e6, e10, e12, e46, e266, e267, e781, e782, e2649, e2652, e2654, e2655, e6365] at *
  omega
theorem n9857 (_v : Vars) (_q : Query _v)  : (e6366 _v) := by
  have p9855 := n9855 _v _q 
  have p9856 := n9856 _v _q 
  exact (Iff.trans p9855 p9856)
theorem n9859 (_v : Vars) (_q : Query _v)  : (e9858 _v) := by
  have p9857 := n9857 _v _q 
  have p2644 := n2644 _v _q 
  change ((e1439 _v) ↔ (e2655 _v)) at p9857
  change ((e1434 _v) = (e2642 _v)) at p2644
  simp only [e9858, e1441, e6367, p9857, p2644]
theorem n9862 (_v : Vars) (_q : Query _v)  : (e9861 _v) := by
  have p9854 := n9854 _v _q 
  have p9859 := n9859 _v _q 
  change ((e1894 _v) ↔ (e2648 _v)) at p9854
  change ((e1441 _v) = (e6367 _v)) at p9859
  simp only [e9861, e5945, e9860, p9854, p9859]
theorem n9863 (_v : Vars) (_q : Query _v)  : (e2660 _v) := by
  have p2658 := n2658 _v _q 
  change ((e1444 _v) = (e2656 _v)) at p2658
  simp only [e2660, e1901, e2659, p2658]
theorem n9864 (_v : Vars) (_q : Query _v)  : (e6368 _v) := by
  simp only [e5, e6, e10, e12, e41, e46, e108, e109, e802, e803, e2656, e2659, e2661, e2662, e6368] at *
  omega
theorem n9865 (_v : Vars) (_q : Query _v)  : (e6369 _v) := by
  have p9863 := n9863 _v _q 
  have p9864 := n9864 _v _q 
  exact (Iff.trans p9863 p9864)
theorem n9866 (_v : Vars) (_q : Query _v)  : (e2667 _v) := by
  have p2665 := n2665 _v _q 
  change ((e1448 _v) = (e2663 _v)) at p2665
  simp only [e2667, e1449, e2666, p2665]
theorem n9867 (_v : Vars) (_q : Query _v)  : (e6370 _v) := by
  simp only [e5, e6, e10, e12, e46, e108, e109, e802, e803, e2663, e2666, e2668, e2669, e6370] at *
  omega
theorem n9868 (_v : Vars) (_q : Query _v)  : (e6371 _v) := by
  have p9866 := n9866 _v _q 
  have p9867 := n9867 _v _q 
  exact (Iff.trans p9866 p9867)
theorem n9870 (_v : Vars) (_q : Query _v)  : (e9869 _v) := by
  have p9868 := n9868 _v _q 
  have p2658 := n2658 _v _q 
  change ((e1449 _v) ↔ (e2669 _v)) at p9868
  change ((e1444 _v) = (e2656 _v)) at p2658
  simp only [e9869, e1451, e6372, p9868, p2658]
theorem n9873 (_v : Vars) (_q : Query _v)  : (e9872 _v) := by
  have p9865 := n9865 _v _q 
  have p9870 := n9870 _v _q 
  change ((e1901 _v) ↔ (e2662 _v)) at p9865
  change ((e1451 _v) = (e6372 _v)) at p9870
  simp only [e9872, e5955, e9871, p9865, p9870]
end
end Assembly
