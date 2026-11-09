import Dag081
import generated.th_lemma_3
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n12768 (_v : Vars) (_q : Query _v)  : (e12767 _v) := by
  have p4830 := n4830 _v _q 
  have p11285 := n11285 _v _q 
  exact (Iff.trans p4830 p11285)
theorem n12770 (_v : Vars) (_q : Query _v)  : (e12769 _v) := by
  have p4845 := n4845 _v _q 
  have p11289 := n11289 _v _q 
  exact (Iff.trans p4845 p11289)
theorem n12771 (_v : Vars) (_q : Query _v)  : (e8314 _v) := by
  simp only [e5, e6, e36, e2516, e4849, e4850, e4851, e6648, e8314] at *
  omega
theorem n12773 (_v : Vars) (_q : Query _v)  : (e12772 _v) := by
  have p11294 := n11294 _v _q 
  have p11296 := n11296 _v _q 
  exact (Iff.trans p11294 p11296)
theorem n12774 (_v : Vars) (_q : Query _v)  : (e11297 _v) := by
  have p12771 := n12771 _v _q 
  have p12773 := n12773 _v _q 
  exact (Iff.trans p12771 p12773)
theorem n12776 (_v : Vars) (_q : Query _v)  : (e12775 _v) := by
  have p12774 := n12774 _v _q 
  change ((e6648 _v) ↔ (e8322 _v)) at p12774
  simp only [e12775, e6649, e11298, p12774]
theorem n12779 (_v : Vars) (_q : Query _v) (h6656 : (e6656 _v)) (h8310 : (e8310 _v)) : (e7489 _v) := by
  have p11384 := n11384 _v _q h8310
  have p8663 := n8663 _v _q 
  have p11499 := n11499 _v _q h6656
  exact FloorCertificate.node_12779 (e2 _v) (e17 _v) (e45 _v) (e110 _v) p11384 p8663 p11499
theorem n12781 (_v : Vars) (_q : Query _v)  : (e12780 _v) := by
  by_contra hc
  change ¬ ((e2536 _v) ∨ (e2529 _v)) at hc
  have h6656 : (e6656 _v) := by
    change (¬ (e2536 _v))
    tauto
  have h8310 : (e8310 _v) := by
    change (¬ (e2529 _v))
    tauto
  have p12779 := n12779 _v _q h6656 h8310
  exact p12779
theorem n12783 (_v : Vars) (_q : Query _v)  : (e12782 _v) := by
  have p4864 := n4864 _v _q 
  have p11304 := n11304 _v _q 
  exact (Iff.trans p4864 p11304)
theorem n12785 (_v : Vars) (_q : Query _v)  : (e12784 _v) := by
  simp only [e43, e760, e761, e2580, e2899, e4868, e4869, e8341, e12784] at *
  omega
theorem n12787 (_v : Vars) (_q : Query _v)  : (e12786 _v) := by
  have p8344 := n8344 _v _q 
  have p11306 := n11306 _v _q 
  exact (Iff.trans p8344 p11306)
theorem n12789 (_v : Vars) (_q : Query _v)  : (e12788 _v) := by
  have p12785 := n12785 _v _q 
  have p12787 := n12787 _v _q 
  exact (Iff.trans p12785 p12787)
theorem n12791 (_v : Vars) (_q : Query _v)  : (e12790 _v) := by
  have p4891 := n4891 _v _q 
  have p11317 := n11317 _v _q 
  exact (Iff.trans p4891 p11317)
theorem n12793 (_v : Vars) (_q : Query _v)  : (e12792 _v) := by
  have p4916 := n4916 _v _q 
  have p11325 := n11325 _v _q 
  exact (Iff.trans p4916 p11325)
theorem n12795 (_v : Vars) (_q : Query _v)  : (e12794 _v) := by
  have p4931 := n4931 _v _q 
  have p11329 := n11329 _v _q 
  exact (Iff.trans p4931 p11329)
theorem n12797 (_v : Vars) (_q : Query _v)  : (e12796 _v) := by
  simp only [e266, e781, e782, e2788, e2914, e4935, e4936, e8401, e12796] at *
  omega
theorem n12799 (_v : Vars) (_q : Query _v)  : (e12798 _v) := by
  have p8404 := n8404 _v _q 
  have p11331 := n11331 _v _q 
  exact (Iff.trans p8404 p11331)
theorem n12801 (_v : Vars) (_q : Query _v)  : (e12800 _v) := by
  have p12797 := n12797 _v _q 
  have p12799 := n12799 _v _q 
  exact (Iff.trans p12797 p12799)
theorem n12802 (_v : Vars) (_q : Query _v) (h2771 : (e2771 _v)) : (e2781 _v) := by
  have p11375 := n11375 _v _q 
  have p8663 := n8663 _v _q 
  have p11376 := n11376 _v _q 
  have p10893 := n10893 _v _q 
  have p10896 := n10896 _v _q 
  have p8415 := n8415 _v _q h2771
  exact FloorCertificate.node_12802 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p11375 p8663 p11376 p10893 p10896 p8415
theorem n12803 (_v : Vars) (_q : Query _v) (h2771 : (e2771 _v)) : (e2793 _v) := by
  have p10893 := n10893 _v _q 
  have p11375 := n11375 _v _q 
  have p8663 := n8663 _v _q 
  have p11376 := n11376 _v _q 
  have p10896 := n10896 _v _q 
  have p8415 := n8415 _v _q h2771
  exact FloorCertificate.node_12803 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p10893 p11375 p8663 p11376 p10896 p8415
theorem n12804 (_v : Vars) (_q : Query _v) (h6684 : (e6684 _v)) : (e6684 _v) := by
  exact h6684
theorem n12805 (_v : Vars) (_q : Query _v) (h5195 : (e5195 _v)) (h6684 : (e6684 _v)) : (e7489 _v) := by
  have p8549 := n8549 _v _q h5195
  have p12804 := n12804 _v _q h6684
  have p8663 := n8663 _v _q 
  have p331 := n331 _v _q 
  exact FloorCertificate.node_12805 (e2 _v) (e7 _v) (e17 _v) (e45 _v) (e110 _v) p8549 p12804 p8663 p331
theorem n12807 (_v : Vars) (_q : Query _v)  : (e12806 _v) := by
  by_contra hc
  change ¬ ((e2598 _v) ∨ (e196 _v)) at hc
  have h5195 : (e5195 _v) := by
    change (¬ (e196 _v))
    tauto
  have h6684 : (e6684 _v) := by
    change (¬ (e2598 _v))
    tauto
  have p12805 := n12805 _v _q h5195 h6684
  exact p12805
theorem n12808 (_v : Vars) (_q : Query _v) (h2771 : (e2771 _v)) : (e2468 _v) := by
  have p8437 := n8437 _v _q 
  have p8415 := n8415 _v _q h2771
  simp only [e2468, e2771, e6768, e8436] at *
  tauto
theorem n12809 (_v : Vars) (_q : Query _v) (h2771 : (e2771 _v)) : (e2402 _v) := by
  have p8442 := n8442 _v _q 
  have p12808 := n12808 _v _q h2771
  simp only [e2402, e2468, e6630, e8441] at *
  tauto
theorem n12810 (_v : Vars) (_q : Query _v) (h2771 : (e2771 _v)) : (e2179 _v) := by
  have p11339 := n11339 _v _q 
  have p12809 := n12809 _v _q h2771
  simp only [e2179, e2402, e6600, e11338] at *
  tauto
theorem n12811 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e6694 _v) := by
  have p11379 := n11379 _v _q 
  have p11345 := n11345 _v _q h6591
  simp only [e251, e2377, e6591, e6694, e11378] at *
  tauto
theorem n12812 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e6742 _v) := by
  have p8414 := n8414 _v _q 
  have p12811 := n12811 _v _q h6591
  simp only [e251, e2722, e6694, e6742, e8413] at *
  tauto
theorem n12813 (_v : Vars) (_q : Query _v) (h6758 : (e6758 _v)) (h7807 : (e7807 _v)) : (e7489 _v) := by
  have p11350 := n11350 _v _q h7807
  have p8663 := n8663 _v _q 
  have p8425 := n8425 _v _q h6758
  have p10893 := n10893 _v _q 
  exact FloorCertificate.node_12813 (e2 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p11350 p8663 p8425 p10893
theorem n12815 (_v : Vars) (_q : Query _v)  : (e12814 _v) := by
  by_contra hc
  change ¬ ((e2746 _v) ∨ (e2303 _v)) at hc
  have h6758 : (e6758 _v) := by
    change (¬ (e2746 _v))
    tauto
  have h7807 : (e7807 _v) := by
    change (¬ (e2303 _v))
    tauto
  have p12813 := n12813 _v _q h6758 h7807
  exact p12813
theorem n12816 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e6486 _v) := by
  have p11382 := n11382 _v _q 
  have p11345 := n11345 _v _q h6591
  simp only [e2139, e2377, e6486, e6591, e11381] at *
  tauto
theorem n12817 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e6636 _v) := by
  have p10892 := n10892 _v _q 
  have p12816 := n12816 _v _q h6591
  simp only [e2139, e2482, e6486, e6636, e10891] at *
  tauto
theorem n12818 (_v : Vars) (_q : Query _v) (h5093 : (e5093 _v)) (h6531 : (e6531 _v)) : (e7489 _v) := by
  have p8663 := n8663 _v _q 
  have p11440 := n11440 _v _q h5093
  have p11358 := n11358 _v _q h6531
  exact FloorCertificate.node_12818 (e2 _v) (e7 _v) (e9 _v) (e17 _v) p8663 p11440 p11358
theorem n12820 (_v : Vars) (_q : Query _v)  : (e12819 _v) := by
  by_contra hc
  change ¬ ((e13 _v) ∨ (e2254 _v)) at hc
  have h5093 : (e5093 _v) := by
    change (¬ (e13 _v))
    tauto
  have h6531 : (e6531 _v) := by
    change (¬ (e2254 _v))
    tauto
  have p12818 := n12818 _v _q h5093 h6531
  exact p12818
theorem n12821 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e6732 _v) := by
  have p11395 := n11395 _v _q 
  have p11345 := n11345 _v _q h6591
  simp only [e2377, e2697, e6591, e6732, e11394] at *
  tauto
theorem n12822 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e6531 _v) := by
  have p11391 := n11391 _v _q 
  have p12821 := n12821 _v _q h6591
  simp only [e2254, e2697, e6531, e6732, e11390] at *
  tauto
theorem n12823 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e6555 _v) := by
  have p11062 := n11062 _v _q 
  have p12816 := n12816 _v _q h6591
  simp only [e2139, e2310, e6486, e6555, e11061] at *
  tauto
theorem n12824 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e2371 _v) := by
  have p8663 := n8663 _v _q 
  have p11345 := n11345 _v _q h6591
  exact FloorCertificate.node_12824 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e110 _v) p8663 p11345
theorem n12825 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e2592 _v) := by
  have p11404 := n11404 _v _q 
  have p12824 := n12824 _v _q h6591
  simp only [e2371, e2592, e6579, e11403] at *
  tauto
theorem n12826 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e6758 _v) := by
  have p11348 := n11348 _v _q 
  have p11345 := n11345 _v _q h6591
  simp only [e2377, e2746, e6591, e6758, e11347] at *
  tauto
theorem n12827 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e6784 _v) := by
  have p8429 := n8429 _v _q 
  have p12826 := n12826 _v _q h6591
  simp only [e2746, e2793, e6758, e6784, e8428] at *
  tauto
theorem n12828 (_v : Vars) (_q : Query _v) (h2296 : (e2296 _v)) : (e2125 _v) := by
  have p5255 := n5255 _v _q 
  have p8583 := n8583 _v _q h2296
  have p5257 := n5257 _v _q 
  exact FloorCertificate.node_12828 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e110 _v) p5255 p8583 p5257
theorem n12829 (_v : Vars) (_q : Query _v) (h2296 : (e2296 _v)) : (e2061 _v) := by
  have p8478 := n8478 _v _q 
  have p12828 := n12828 _v _q h2296
  simp only [e2061, e2125, e6480, e8477] at *
  tauto
theorem n12830 (_v : Vars) (_q : Query _v) (h2296 : (e2296 _v)) : (e1995 _v) := by
  have p11412 := n11412 _v _q 
  have p12829 := n12829 _v _q h2296
  simp only [e1995, e2061, e6454, e11411] at *
  tauto
theorem n12831 (_v : Vars) (_q : Query _v) (h2522 : (e2522 _v)) : (e2522 _v) := by
  exact h2522
end
end Assembly
