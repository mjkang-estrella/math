import Dag048
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n9737 (_v : Vars) (_q : Query _v)  : (e9736 _v) := by
  have p9735 := n9735 _v _q 
  have p2518 := n2518 _v _q 
  change ((e1331 _v) ↔ (e2529 _v)) at p9735
  change ((e1326 _v) = (e2516 _v)) at p2518
  simp only [e9736, e1333, e6325, p9735, p2518]
theorem n9740 (_v : Vars) (_q : Query _v)  : (e9739 _v) := by
  have p9732 := n9732 _v _q 
  have p9737 := n9737 _v _q 
  change ((e1832 _v) ↔ (e2522 _v)) at p9732
  change ((e1333 _v) = (e6325 _v)) at p9737
  simp only [e9739, e5851, e9738, p9732, p9737]
theorem n9741 (_v : Vars) (_q : Query _v)  : (e2534 _v) := by
  have p2532 := n2532 _v _q 
  change ((e1336 _v) = (e2530 _v)) at p2532
  simp only [e2534, e1839, e2533, p2532]
theorem n9742 (_v : Vars) (_q : Query _v)  : (e6326 _v) := by
  simp only [e5, e6, e12, e41, e43, e44, e46, e111, e760, e761, e2530, e2533, e2535, e2536, e6326] at *
  omega
theorem n9743 (_v : Vars) (_q : Query _v)  : (e6327 _v) := by
  have p9741 := n9741 _v _q 
  have p9742 := n9742 _v _q 
  exact (Iff.trans p9741 p9742)
theorem n9744 (_v : Vars) (_q : Query _v)  : (e2541 _v) := by
  have p2539 := n2539 _v _q 
  change ((e1340 _v) = (e2537 _v)) at p2539
  simp only [e2541, e1341, e2540, p2539]
theorem n9745 (_v : Vars) (_q : Query _v)  : (e6328 _v) := by
  simp only [e5, e6, e12, e43, e44, e46, e111, e760, e761, e2537, e2540, e2542, e2543, e6328] at *
  omega
theorem n9746 (_v : Vars) (_q : Query _v)  : (e6329 _v) := by
  have p9744 := n9744 _v _q 
  have p9745 := n9745 _v _q 
  exact (Iff.trans p9744 p9745)
theorem n9748 (_v : Vars) (_q : Query _v)  : (e9747 _v) := by
  have p9746 := n9746 _v _q 
  have p2532 := n2532 _v _q 
  change ((e1341 _v) ↔ (e2543 _v)) at p9746
  change ((e1336 _v) = (e2530 _v)) at p2532
  simp only [e9747, e1343, e6330, p9746, p2532]
theorem n9751 (_v : Vars) (_q : Query _v)  : (e9750 _v) := by
  have p9743 := n9743 _v _q 
  have p9748 := n9748 _v _q 
  change ((e1839 _v) ↔ (e2536 _v)) at p9743
  change ((e1343 _v) = (e6330 _v)) at p9748
  simp only [e9750, e5861, e9749, p9743, p9748]
theorem n9752 (_v : Vars) (_q : Query _v)  : (e2548 _v) := by
  have p2546 := n2546 _v _q 
  change ((e1346 _v) = (e2544 _v)) at p2546
  simp only [e2548, e1846, e2547, p2546]
theorem n9753 (_v : Vars) (_q : Query _v)  : (e6331 _v) := by
  simp only [e5, e6, e12, e41, e46, e111, e266, e267, e781, e782, e2544, e2547, e2549, e2550, e6331] at *
  omega
theorem n9754 (_v : Vars) (_q : Query _v)  : (e6332 _v) := by
  have p9752 := n9752 _v _q 
  have p9753 := n9753 _v _q 
  exact (Iff.trans p9752 p9753)
theorem n9755 (_v : Vars) (_q : Query _v)  : (e2555 _v) := by
  have p2553 := n2553 _v _q 
  change ((e1350 _v) = (e2551 _v)) at p2553
  simp only [e2555, e1351, e2554, p2553]
theorem n9756 (_v : Vars) (_q : Query _v)  : (e6333 _v) := by
  simp only [e5, e6, e12, e46, e111, e266, e267, e781, e782, e2551, e2554, e2556, e2557, e6333] at *
  omega
theorem n9757 (_v : Vars) (_q : Query _v)  : (e6334 _v) := by
  have p9755 := n9755 _v _q 
  have p9756 := n9756 _v _q 
  exact (Iff.trans p9755 p9756)
theorem n9759 (_v : Vars) (_q : Query _v)  : (e9758 _v) := by
  have p9757 := n9757 _v _q 
  have p2546 := n2546 _v _q 
  change ((e1351 _v) ↔ (e2557 _v)) at p9757
  change ((e1346 _v) = (e2544 _v)) at p2546
  simp only [e9758, e1353, e6335, p9757, p2546]
theorem n9762 (_v : Vars) (_q : Query _v)  : (e9761 _v) := by
  have p9754 := n9754 _v _q 
  have p9759 := n9759 _v _q 
  change ((e1846 _v) ↔ (e2550 _v)) at p9754
  change ((e1353 _v) = (e6335 _v)) at p9759
  simp only [e9761, e5871, e9760, p9754, p9759]
theorem n9763 (_v : Vars) (_q : Query _v)  : (e2562 _v) := by
  have p2560 := n2560 _v _q 
  change ((e1356 _v) = (e2558 _v)) at p2560
  simp only [e2562, e1853, e2561, p2560]
theorem n9764 (_v : Vars) (_q : Query _v)  : (e6336 _v) := by
  simp only [e5, e6, e12, e41, e46, e108, e109, e111, e802, e803, e2558, e2561, e2563, e2564, e6336] at *
  omega
theorem n9765 (_v : Vars) (_q : Query _v)  : (e6337 _v) := by
  have p9763 := n9763 _v _q 
  have p9764 := n9764 _v _q 
  exact (Iff.trans p9763 p9764)
theorem n9766 (_v : Vars) (_q : Query _v)  : (e2569 _v) := by
  have p2567 := n2567 _v _q 
  change ((e1360 _v) = (e2565 _v)) at p2567
  simp only [e2569, e1361, e2568, p2567]
theorem n9767 (_v : Vars) (_q : Query _v)  : (e6338 _v) := by
  simp only [e5, e6, e12, e46, e108, e109, e111, e802, e803, e2565, e2568, e2570, e2571, e6338] at *
  omega
theorem n9768 (_v : Vars) (_q : Query _v)  : (e6339 _v) := by
  have p9766 := n9766 _v _q 
  have p9767 := n9767 _v _q 
  exact (Iff.trans p9766 p9767)
theorem n9770 (_v : Vars) (_q : Query _v)  : (e9769 _v) := by
  have p9768 := n9768 _v _q 
  have p2560 := n2560 _v _q 
  change ((e1361 _v) ↔ (e2571 _v)) at p9768
  change ((e1356 _v) = (e2558 _v)) at p2560
  simp only [e9769, e1363, e6340, p9768, p2560]
theorem n9773 (_v : Vars) (_q : Query _v)  : (e9772 _v) := by
  have p9765 := n9765 _v _q 
  have p9770 := n9770 _v _q 
  change ((e1853 _v) ↔ (e2564 _v)) at p9765
  change ((e1363 _v) = (e6340 _v)) at p9770
  simp only [e9772, e5881, e9771, p9765, p9770]
theorem n9775 (_v : Vars) (_q : Query _v)  : (e9774 _v) := by
  have p2573 := n2573 _v _q 
  change ((e1370 _v) = (e197 _v)) at p2573
  simp only [e9774, e1373, e2574, p2573]
theorem n9777 (_v : Vars) (_q : Query _v)  : (e9776 _v) := by
  simp only [e5, e6, e8, e12, e36, e41, e46, e111, e197, e473, e474, e2574, e9776] at *
  omega
theorem n9779 (_v : Vars) (_q : Query _v)  : (e9778 _v) := by
  have p9775 := n9775 _v _q 
  have p9777 := n9777 _v _q 
  exact (Iff.trans p9775 p9777)
theorem n9780 (_v : Vars) (_q : Query _v)  : (e2579 _v) := by
  have p2577 := n2577 _v _q 
  change ((e1375 _v) = (e2575 _v)) at p2577
  simp only [e2579, e1376, e2578, p2577]
theorem n9781 (_v : Vars) (_q : Query _v)  : (e6341 _v) := by
  simp only [e5, e6, e8, e12, e36, e46, e111, e195, e196, e2575, e2578, e6341] at *
  omega
theorem n9782 (_v : Vars) (_q : Query _v)  : (e6342 _v) := by
  have p9780 := n9780 _v _q 
  have p9781 := n9781 _v _q 
  exact (Iff.trans p9780 p9781)
theorem n9784 (_v : Vars) (_q : Query _v)  : (e9783 _v) := by
  have p9782 := n9782 _v _q 
  have p2573 := n2573 _v _q 
  change ((e1376 _v) ↔ (e196 _v)) at p9782
  change ((e1370 _v) = (e197 _v)) at p2573
  simp only [e9783, e1377, e6343, p9782, p2573]
theorem n9787 (_v : Vars) (_q : Query _v)  : (e9786 _v) := by
  have p9779 := n9779 _v _q 
  have p9784 := n9784 _v _q 
  change ((e1373 _v) ↔ (e474 _v)) at p9779
  change ((e1377 _v) = (e6343 _v)) at p9784
  simp only [e9786, e5910, e9785, p9779, p9784]
theorem n9789 (_v : Vars) (_q : Query _v)  : (e9788 _v) := by
  have p2582 := n2582 _v _q 
  change ((e1380 _v) = (e2580 _v)) at p2582
  simp only [e9788, e1383, e2583, p2582]
theorem n9791 (_v : Vars) (_q : Query _v)  : (e9790 _v) := by
  simp only [e5, e6, e8, e12, e41, e43, e44, e46, e111, e760, e761, e2580, e2583, e2584, e2585, e9790] at *
  omega
theorem n9793 (_v : Vars) (_q : Query _v)  : (e9792 _v) := by
  have p9789 := n9789 _v _q 
  have p9791 := n9791 _v _q 
  exact (Iff.trans p9789 p9791)
theorem n9794 (_v : Vars) (_q : Query _v)  : (e2590 _v) := by
  have p2588 := n2588 _v _q 
  change ((e1385 _v) = (e2586 _v)) at p2588
  simp only [e2590, e1386, e2589, p2588]
theorem n9795 (_v : Vars) (_q : Query _v)  : (e6344 _v) := by
  simp only [e5, e6, e8, e12, e43, e44, e46, e111, e760, e761, e2586, e2589, e2591, e2592, e6344] at *
  omega
theorem n9796 (_v : Vars) (_q : Query _v)  : (e6345 _v) := by
  have p9794 := n9794 _v _q 
  have p9795 := n9795 _v _q 
  exact (Iff.trans p9794 p9795)
theorem n9798 (_v : Vars) (_q : Query _v)  : (e9797 _v) := by
  have p9796 := n9796 _v _q 
  have p2582 := n2582 _v _q 
  change ((e1386 _v) ↔ (e2592 _v)) at p9796
  change ((e1380 _v) = (e2580 _v)) at p2582
  simp only [e9797, e1387, e6346, p9796, p2582]
theorem n9801 (_v : Vars) (_q : Query _v)  : (e9800 _v) := by
  have p9793 := n9793 _v _q 
  have p9798 := n9798 _v _q 
  change ((e1383 _v) ↔ (e2585 _v)) at p9793
  change ((e1387 _v) = (e6346 _v)) at p9798
  simp only [e9800, e5911, e9799, p9793, p9798]
theorem n9803 (_v : Vars) (_q : Query _v)  : (e9802 _v) := by
  have p2595 := n2595 _v _q 
  change ((e1390 _v) = (e2593 _v)) at p2595
  simp only [e9802, e1393, e2596, p2595]
theorem n9805 (_v : Vars) (_q : Query _v)  : (e9804 _v) := by
  simp only [e5, e6, e8, e12, e41, e46, e111, e266, e267, e781, e782, e2593, e2596, e2597, e2598, e9804] at *
  omega
theorem n9807 (_v : Vars) (_q : Query _v)  : (e9806 _v) := by
  have p9803 := n9803 _v _q 
  have p9805 := n9805 _v _q 
  exact (Iff.trans p9803 p9805)
end
end Assembly
