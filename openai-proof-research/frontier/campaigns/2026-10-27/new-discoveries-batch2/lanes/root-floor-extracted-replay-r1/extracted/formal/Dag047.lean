import Dag046
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n9607 (_v : Vars) (_q : Query _v)  : (e6284 _v) := by
  simp only [e5, e6, e8, e10, e12, e43, e44, e111, e760, e761, e2365, e2368, e2370, e2371, e6284] at *
  omega
theorem n9608 (_v : Vars) (_q : Query _v)  : (e6285 _v) := by
  have p9606 := n9606 _v _q 
  have p9607 := n9607 _v _q 
  exact (Iff.trans p9606 p9607)
theorem n9610 (_v : Vars) (_q : Query _v)  : (e9609 _v) := by
  have p9608 := n9608 _v _q 
  have p2361 := n2361 _v _q 
  change ((e1183 _v) ↔ (e2371 _v)) at p9608
  change ((e1177 _v) = (e2359 _v)) at p2361
  simp only [e9609, e1184, e6286, p9608, p2361]
theorem n9613 (_v : Vars) (_q : Query _v)  : (e9612 _v) := by
  have p9605 := n9605 _v _q 
  have p9610 := n9610 _v _q 
  change ((e1180 _v) ↔ (e2364 _v)) at p9605
  change ((e1184 _v) = (e6286 _v)) at p9610
  simp only [e9612, e5766, e9611, p9605, p9610]
theorem n9615 (_v : Vars) (_q : Query _v)  : (e9614 _v) := by
  have p2374 := n2374 _v _q 
  change ((e1187 _v) = (e2372 _v)) at p2374
  simp only [e9614, e1190, e2375, p2374]
theorem n9617 (_v : Vars) (_q : Query _v)  : (e9616 _v) := by
  simp only [e5, e6, e8, e10, e12, e41, e111, e266, e267, e781, e782, e2372, e2375, e2376, e2377, e9616] at *
  omega
theorem n9619 (_v : Vars) (_q : Query _v)  : (e9618 _v) := by
  have p9615 := n9615 _v _q 
  have p9617 := n9617 _v _q 
  exact (Iff.trans p9615 p9617)
theorem n9620 (_v : Vars) (_q : Query _v)  : (e2382 _v) := by
  have p2380 := n2380 _v _q 
  change ((e1192 _v) = (e2378 _v)) at p2380
  simp only [e2382, e1193, e2381, p2380]
theorem n9621 (_v : Vars) (_q : Query _v)  : (e6287 _v) := by
  simp only [e5, e6, e8, e10, e12, e111, e266, e267, e781, e782, e2378, e2381, e2383, e2384, e6287] at *
  omega
theorem n9622 (_v : Vars) (_q : Query _v)  : (e6288 _v) := by
  have p9620 := n9620 _v _q 
  have p9621 := n9621 _v _q 
  exact (Iff.trans p9620 p9621)
theorem n9624 (_v : Vars) (_q : Query _v)  : (e9623 _v) := by
  have p9622 := n9622 _v _q 
  have p2374 := n2374 _v _q 
  change ((e1193 _v) ↔ (e2384 _v)) at p9622
  change ((e1187 _v) = (e2372 _v)) at p2374
  simp only [e9623, e1194, e6289, p9622, p2374]
theorem n9627 (_v : Vars) (_q : Query _v)  : (e9626 _v) := by
  have p9619 := n9619 _v _q 
  have p9624 := n9624 _v _q 
  change ((e1190 _v) ↔ (e2377 _v)) at p9619
  change ((e1194 _v) = (e6289 _v)) at p9624
  simp only [e9626, e5767, e9625, p9619, p9624]
theorem n9629 (_v : Vars) (_q : Query _v)  : (e9628 _v) := by
  have p2387 := n2387 _v _q 
  change ((e1197 _v) = (e2385 _v)) at p2387
  simp only [e9628, e1200, e2388, p2387]
theorem n9631 (_v : Vars) (_q : Query _v)  : (e9630 _v) := by
  simp only [e5, e6, e8, e10, e12, e41, e108, e109, e111, e112, e113, e802, e803, e2385, e2388, e9630] at *
  omega
theorem n9633 (_v : Vars) (_q : Query _v)  : (e9632 _v) := by
  have p9629 := n9629 _v _q 
  have p9631 := n9631 _v _q 
  exact (Iff.trans p9629 p9631)
theorem n9634 (_v : Vars) (_q : Query _v)  : (e2393 _v) := by
  have p2391 := n2391 _v _q 
  change ((e1202 _v) = (e2389 _v)) at p2391
  simp only [e2393, e1203, e2392, p2391]
theorem n9635 (_v : Vars) (_q : Query _v)  : (e6290 _v) := by
  simp only [e5, e6, e8, e10, e12, e108, e109, e111, e802, e803, e2389, e2392, e2394, e2395, e6290] at *
  omega
theorem n9636 (_v : Vars) (_q : Query _v)  : (e6291 _v) := by
  have p9634 := n9634 _v _q 
  have p9635 := n9635 _v _q 
  exact (Iff.trans p9634 p9635)
theorem n9638 (_v : Vars) (_q : Query _v)  : (e9637 _v) := by
  have p9636 := n9636 _v _q 
  have p2387 := n2387 _v _q 
  change ((e1203 _v) ↔ (e2395 _v)) at p9636
  change ((e1197 _v) = (e2385 _v)) at p2387
  simp only [e9637, e1204, e6292, p9636, p2387]
theorem n9641 (_v : Vars) (_q : Query _v)  : (e9640 _v) := by
  have p9633 := n9633 _v _q 
  have p9638 := n9638 _v _q 
  change ((e1200 _v) ↔ (e113 _v)) at p9633
  change ((e1204 _v) = (e6292 _v)) at p9638
  simp only [e9640, e5768, e9639, p9633, p9638]
theorem n9642 (_v : Vars) (_q : Query _v)  : (e2400 _v) := by
  have p2398 := n2398 _v _q 
  change ((e1216 _v) = (e2396 _v)) at p2398
  simp only [e2400, e1776, e2399, p2398]
theorem n9643 (_v : Vars) (_q : Query _v)  : (e6293 _v) := by
  simp only [e5, e6, e12, e36, e41, e46, e2396, e2399, e2401, e2402, e6293] at *
  omega
theorem n9644 (_v : Vars) (_q : Query _v)  : (e6294 _v) := by
  have p9642 := n9642 _v _q 
  have p9643 := n9643 _v _q 
  exact (Iff.trans p9642 p9643)
theorem n9645 (_v : Vars) (_q : Query _v)  : (e2407 _v) := by
  have p2405 := n2405 _v _q 
  change ((e1221 _v) = (e2403 _v)) at p2405
  simp only [e2407, e1222, e2406, p2405]
theorem n9646 (_v : Vars) (_q : Query _v)  : (e2408 _v) := by
  simp only [e5, e6, e12, e36, e46, e399, e400, e2403, e2406, e2408] at *
  omega
theorem n9647 (_v : Vars) (_q : Query _v)  : (e2409 _v) := by
  have p9645 := n9645 _v _q 
  have p9646 := n9646 _v _q 
  exact (Iff.trans p9645 p9646)
theorem n9649 (_v : Vars) (_q : Query _v)  : (e9648 _v) := by
  have p9647 := n9647 _v _q 
  have p2398 := n2398 _v _q 
  change ((e1222 _v) ↔ (e400 _v)) at p9647
  change ((e1216 _v) = (e2396 _v)) at p2398
  simp only [e9648, e1224, e2410, p9647, p2398]
theorem n9652 (_v : Vars) (_q : Query _v)  : (e9651 _v) := by
  have p9644 := n9644 _v _q 
  have p9649 := n9649 _v _q 
  change ((e1776 _v) ↔ (e2402 _v)) at p9644
  change ((e1224 _v) = (e2410 _v)) at p9649
  simp only [e9651, e5779, e9650, p9644, p9649]
theorem n9653 (_v : Vars) (_q : Query _v)  : (e2415 _v) := by
  have p2413 := n2413 _v _q 
  change ((e1232 _v) = (e2411 _v)) at p2413
  simp only [e2415, e1783, e2414, p2413]
theorem n9654 (_v : Vars) (_q : Query _v)  : (e6295 _v) := by
  simp only [e5, e6, e12, e41, e43, e44, e46, e760, e761, e2411, e2414, e2416, e2417, e6295] at *
  omega
theorem n9655 (_v : Vars) (_q : Query _v)  : (e6296 _v) := by
  have p9653 := n9653 _v _q 
  have p9654 := n9654 _v _q 
  exact (Iff.trans p9653 p9654)
theorem n9656 (_v : Vars) (_q : Query _v)  : (e2422 _v) := by
  have p2420 := n2420 _v _q 
  change ((e1238 _v) = (e2418 _v)) at p2420
  simp only [e2422, e1239, e2421, p2420]
theorem n9657 (_v : Vars) (_q : Query _v)  : (e2425 _v) := by
  simp only [e5, e6, e12, e43, e44, e46, e760, e761, e2418, e2421, e2423, e2424, e2425] at *
  omega
theorem n9658 (_v : Vars) (_q : Query _v)  : (e2426 _v) := by
  have p9656 := n9656 _v _q 
  have p9657 := n9657 _v _q 
  exact (Iff.trans p9656 p9657)
theorem n9660 (_v : Vars) (_q : Query _v)  : (e9659 _v) := by
  have p9658 := n9658 _v _q 
  have p2413 := n2413 _v _q 
  change ((e1239 _v) ↔ (e2424 _v)) at p9658
  change ((e1232 _v) = (e2411 _v)) at p2413
  simp only [e9659, e1241, e2427, p9658, p2413]
theorem n9663 (_v : Vars) (_q : Query _v)  : (e9662 _v) := by
  have p9655 := n9655 _v _q 
  have p9660 := n9660 _v _q 
  change ((e1783 _v) ↔ (e2417 _v)) at p9655
  change ((e1241 _v) = (e2427 _v)) at p9660
  simp only [e9662, e5789, e9661, p9655, p9660]
theorem n9664 (_v : Vars) (_q : Query _v)  : (e2432 _v) := by
  have p2430 := n2430 _v _q 
  change ((e1249 _v) = (e2428 _v)) at p2430
  simp only [e2432, e1790, e2431, p2430]
theorem n9665 (_v : Vars) (_q : Query _v)  : (e6297 _v) := by
  simp only [e5, e6, e12, e41, e46, e266, e267, e781, e782, e2428, e2431, e2433, e2434, e6297] at *
  omega
theorem n9666 (_v : Vars) (_q : Query _v)  : (e6298 _v) := by
  have p9664 := n9664 _v _q 
  have p9665 := n9665 _v _q 
  exact (Iff.trans p9664 p9665)
theorem n9667 (_v : Vars) (_q : Query _v)  : (e2439 _v) := by
  have p2437 := n2437 _v _q 
  change ((e1255 _v) = (e2435 _v)) at p2437
  simp only [e2439, e1256, e2438, p2437]
theorem n9668 (_v : Vars) (_q : Query _v)  : (e2442 _v) := by
  simp only [e5, e6, e12, e46, e266, e267, e781, e782, e2435, e2438, e2440, e2441, e2442] at *
  omega
theorem n9669 (_v : Vars) (_q : Query _v)  : (e2443 _v) := by
  have p9667 := n9667 _v _q 
  have p9668 := n9668 _v _q 
  exact (Iff.trans p9667 p9668)
theorem n9671 (_v : Vars) (_q : Query _v)  : (e9670 _v) := by
  have p9669 := n9669 _v _q 
  have p2430 := n2430 _v _q 
  change ((e1256 _v) ↔ (e2441 _v)) at p9669
  change ((e1249 _v) = (e2428 _v)) at p2430
  simp only [e9670, e1258, e2444, p9669, p2430]
theorem n9674 (_v : Vars) (_q : Query _v)  : (e9673 _v) := by
  have p9666 := n9666 _v _q 
  have p9671 := n9671 _v _q 
  change ((e1790 _v) ↔ (e2434 _v)) at p9666
  change ((e1258 _v) = (e2444 _v)) at p9671
  simp only [e9673, e5799, e9672, p9666, p9671]
theorem n9675 (_v : Vars) (_q : Query _v)  : (e2449 _v) := by
  have p2447 := n2447 _v _q 
  change ((e1266 _v) = (e2445 _v)) at p2447
  simp only [e2449, e1797, e2448, p2447]
end
end Assembly
