import Dag079
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n12597 (_v : Vars) (_q : Query _v)  : (e12596 _v) := by
  have p4175 := n4175 _v _q 
  have p10970 := n10970 _v _q 
  exact (Iff.trans p4175 p10970)
theorem n12599 (_v : Vars) (_q : Query _v)  : (e12598 _v) := by
  have p4190 := n4190 _v _q 
  have p10974 := n10974 _v _q 
  exact (Iff.trans p4190 p10974)
theorem n12601 (_v : Vars) (_q : Query _v)  : (e12600 _v) := by
  simp only [e43, e760, e761, e2359, e2880, e4194, e4195, e7694, e12600] at *
  omega
theorem n12603 (_v : Vars) (_q : Query _v)  : (e12602 _v) := by
  have p7697 := n7697 _v _q 
  have p10976 := n10976 _v _q 
  exact (Iff.trans p7697 p10976)
theorem n12605 (_v : Vars) (_q : Query _v)  : (e12604 _v) := by
  have p12601 := n12601 _v _q 
  have p12603 := n12603 _v _q 
  exact (Iff.trans p12601 p12603)
theorem n12607 (_v : Vars) (_q : Query _v)  : (e12606 _v) := by
  have p4208 := n4208 _v _q 
  have p10983 := n10983 _v _q 
  exact (Iff.trans p4208 p10983)
theorem n12609 (_v : Vars) (_q : Query _v)  : (e12608 _v) := by
  simp only [e5, e6, e36, e2670, e2903, e4212, e4213, e7720, e12608] at *
  omega
theorem n12611 (_v : Vars) (_q : Query _v)  : (e12610 _v) := by
  have p7723 := n7723 _v _q 
  have p10985 := n10985 _v _q 
  exact (Iff.trans p7723 p10985)
theorem n12613 (_v : Vars) (_q : Query _v)  : (e12612 _v) := by
  have p12609 := n12609 _v _q 
  have p12611 := n12611 _v _q 
  exact (Iff.trans p12609 p12611)
theorem n12615 (_v : Vars) (_q : Query _v)  : (e12614 _v) := by
  have p4227 := n4227 _v _q 
  have p10992 := n10992 _v _q 
  exact (Iff.trans p4227 p10992)
theorem n12616 (_v : Vars) (_q : Query _v)  : (e7746 _v) := by
  simp only [e5, e6, e36, e2119, e4231, e4232, e4233, e6478, e7746] at *
  omega
theorem n12618 (_v : Vars) (_q : Query _v)  : (e12617 _v) := by
  have p10997 := n10997 _v _q 
  have p10999 := n10999 _v _q 
  exact (Iff.trans p10997 p10999)
theorem n12619 (_v : Vars) (_q : Query _v)  : (e11000 _v) := by
  have p12616 := n12616 _v _q 
  have p12618 := n12618 _v _q 
  exact (Iff.trans p12616 p12618)
theorem n12621 (_v : Vars) (_q : Query _v)  : (e12620 _v) := by
  have p12619 := n12619 _v _q 
  change ((e6478 _v) ↔ (e7754 _v)) at p12619
  simp only [e12620, e6479, e11001, p12619]
theorem n12625 (_v : Vars) (_q : Query _v)  : (e12624 _v) := by
  have p4243 := n4243 _v _q 
  have p11007 := n11007 _v _q 
  exact (Iff.trans p4243 p11007)
theorem n12626 (_v : Vars) (_q : Query _v)  : (e7771 _v) := by
  simp only [e5, e6, e36, e1989, e2835, e4253, e4254, e4255, e7771] at *
  omega
theorem n12627 (_v : Vars) (_q : Query _v)  : (e7778 _v) := by
  have p12626 := n12626 _v _q 
  have p11013 := n11013 _v _q 
  exact (Iff.trans p12626 p11013)
theorem n12629 (_v : Vars) (_q : Query _v)  : (e12628 _v) := by
  have p12627 := n12627 _v _q 
  change ((e2835 _v) ↔ (e7775 _v)) at p12627
  simp only [e12628, e2836, e7779, p12627]
theorem n12631 (_v : Vars) (_q : Query _v)  : (e12630 _v) := by
  simp only [e5, e6, e8, e12, e41, e162, e163, e4235, e4236, e4237, e7756, e7757, e7758, e7775, e7779, e12630] at *
theorem n12632 (_v : Vars) (_q : Query _v)  : (e12628 _v) := by
  have p12629 := n12629 _v _q 
  have p12631 := n12631 _v _q 
  exact (Iff.trans p12629 p12631)
theorem n12636 (_v : Vars) (_q : Query _v)  : (e12635 _v) := by
  have p4277 := n4277 _v _q 
  have p11024 := n11024 _v _q 
  exact (Iff.trans p4277 p11024)
theorem n12638 (_v : Vars) (_q : Query _v)  : (e12637 _v) := by
  have p4292 := n4292 _v _q 
  have p11037 := n11037 _v _q 
  exact (Iff.trans p4292 p11037)
theorem n12639 (_v : Vars) (_q : Query _v)  : (e7811 _v) := by
  simp only [e5, e6, e36, e2290, e4296, e4297, e4298, e6547, e7811] at *
  omega
theorem n12641 (_v : Vars) (_q : Query _v)  : (e12640 _v) := by
  have p11042 := n11042 _v _q 
  have p11044 := n11044 _v _q 
  exact (Iff.trans p11042 p11044)
theorem n12642 (_v : Vars) (_q : Query _v)  : (e11045 _v) := by
  have p12639 := n12639 _v _q 
  have p12641 := n12641 _v _q 
  exact (Iff.trans p12639 p12641)
theorem n12644 (_v : Vars) (_q : Query _v)  : (e12643 _v) := by
  have p12642 := n12642 _v _q 
  change ((e6547 _v) ↔ (e7819 _v)) at p12642
  simp only [e12643, e6548, e11046, p12642]
theorem n12648 (_v : Vars) (_q : Query _v)  : (e12647 _v) := by
  have p4320 := n4320 _v _q 
  have p11056 := n11056 _v _q 
  exact (Iff.trans p4320 p11056)
theorem n12649 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e6555 _v) := by
  have p11062 := n11062 _v _q 
  have p12547 := n12547 _v _q h6792
  simp only [e2139, e2310, e6486, e6555, e11061] at *
  tauto
theorem n12651 (_v : Vars) (_q : Query _v)  : (e12650 _v) := by
  have p4331 := n4331 _v _q 
  have p11064 := n11064 _v _q 
  exact (Iff.trans p4331 p11064)
theorem n12652 (_v : Vars) (_q : Query _v)  : (e7857 _v) := by
  simp only [e43, e760, e761, e2476, e4341, e4342, e4343, e6634, e7857] at *
  omega
theorem n12654 (_v : Vars) (_q : Query _v)  : (e12653 _v) := by
  have p11069 := n11069 _v _q 
  have p11071 := n11071 _v _q 
  exact (Iff.trans p11069 p11071)
theorem n12655 (_v : Vars) (_q : Query _v)  : (e11072 _v) := by
  have p12652 := n12652 _v _q 
  have p12654 := n12654 _v _q 
  exact (Iff.trans p12652 p12654)
theorem n12657 (_v : Vars) (_q : Query _v)  : (e12656 _v) := by
  have p12655 := n12655 _v _q 
  change ((e6634 _v) ↔ (e7860 _v)) at p12655
  simp only [e12656, e6635, e11073, p12655]
theorem n12661 (_v : Vars) (_q : Query _v)  : (e12660 _v) := by
  have p4352 := n4352 _v _q 
  have p11079 := n11079 _v _q 
  exact (Iff.trans p4352 p11079)
theorem n12662 (_v : Vars) (_q : Query _v)  : (e7877 _v) := by
  simp only [e5, e6, e36, e2396, e2884, e4362, e4363, e4364, e7877] at *
  omega
theorem n12663 (_v : Vars) (_q : Query _v)  : (e7884 _v) := by
  have p12662 := n12662 _v _q 
  have p11085 := n11085 _v _q 
  exact (Iff.trans p12662 p11085)
theorem n12665 (_v : Vars) (_q : Query _v)  : (e12664 _v) := by
  have p12663 := n12663 _v _q 
  change ((e2884 _v) ↔ (e7881 _v)) at p12663
  simp only [e12664, e2885, e7885, p12663]
theorem n12667 (_v : Vars) (_q : Query _v)  : (e12666 _v) := by
  simp only [e5, e6, e12, e41, e46, e399, e400, e4344, e4345, e4346, e7862, e7863, e7864, e7881, e7885, e12666] at *
theorem n12668 (_v : Vars) (_q : Query _v)  : (e12664 _v) := by
  have p12665 := n12665 _v _q 
  have p12667 := n12667 _v _q 
  exact (Iff.trans p12665 p12667)
theorem n12672 (_v : Vars) (_q : Query _v)  : (e12671 _v) := by
  have p4386 := n4386 _v _q 
  have p11096 := n11096 _v _q 
  exact (Iff.trans p4386 p11096)
theorem n12674 (_v : Vars) (_q : Query _v)  : (e12673 _v) := by
  have p4411 := n4411 _v _q 
  have p11104 := n11104 _v _q 
  exact (Iff.trans p4411 p11104)
theorem n12676 (_v : Vars) (_q : Query _v)  : (e12675 _v) := by
  have p4426 := n4426 _v _q 
  have p11108 := n11108 _v _q 
  exact (Iff.trans p4426 p11108)
theorem n12678 (_v : Vars) (_q : Query _v)  : (e12677 _v) := by
  simp only [e43, e760, e761, e2776, e2912, e4430, e4431, e7938, e12677] at *
  omega
theorem n12680 (_v : Vars) (_q : Query _v)  : (e12679 _v) := by
  have p7941 := n7941 _v _q 
  have p11110 := n11110 _v _q 
  exact (Iff.trans p7941 p11110)
theorem n12682 (_v : Vars) (_q : Query _v)  : (e12681 _v) := by
  have p12678 := n12678 _v _q 
  have p12680 := n12680 _v _q 
  exact (Iff.trans p12678 p12680)
end
end Assembly
