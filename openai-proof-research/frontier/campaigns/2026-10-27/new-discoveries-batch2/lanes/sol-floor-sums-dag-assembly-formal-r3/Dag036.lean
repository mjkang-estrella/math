import Dag035
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n8841 (_v : Vars) (_q : Query _v)  : (e768 _v) := by
  have p5510 := n5510 _v _q 
  change ((e535 _v) = (e764 _v)) at p5510
  simp only [e768, e766, e767, p5510]
theorem n8842 (_v : Vars) (_q : Query _v)  : (e770 _v) := by
  have p5510 := n5510 _v _q 
  change ((e535 _v) = (e764 _v)) at p5510
  simp only [e770, e536, e769, p5510]
theorem n8843 (_v : Vars) (_q : Query _v)  : (e771 _v) := by
  simp only [e12, e43, e749, e760, e761, e764, e769, e771] at *
  omega
theorem n8844 (_v : Vars) (_q : Query _v)  : (e772 _v) := by
  have p8842 := n8842 _v _q 
  have p8843 := n8843 _v _q 
  exact (Iff.trans p8842 p8843)
theorem n8846 (_v : Vars) (_q : Query _v)  : (e8845 _v) := by
  have p8844 := n8844 _v _q 
  have p5510 := n5510 _v _q 
  change ((e536 _v) ↔ (e749 _v)) at p8844
  change ((e535 _v) = (e764 _v)) at p5510
  simp only [e8845, e537, e773, p8844, p5510]
theorem n8848 (_v : Vars) (_q : Query _v)  : (e8847 _v) := by
  have p8841 := n8841 _v _q 
  have p8846 := n8846 _v _q 
  change ((e766 _v) ↔ (e767 _v)) at p8841
  change ((e537 _v) = (e773 _v)) at p8846
  simp only [e8847, e5427, e5511, p8841, p8846]
theorem n8849 (_v : Vars) (_q : Query _v)  : (e789 _v) := by
  have p5516 := n5516 _v _q 
  change ((e538 _v) = (e785 _v)) at p5516
  simp only [e789, e787, e788, p5516]
theorem n8850 (_v : Vars) (_q : Query _v)  : (e791 _v) := by
  have p5516 := n5516 _v _q 
  change ((e538 _v) = (e785 _v)) at p5516
  simp only [e791, e539, e790, p5516]
theorem n8851 (_v : Vars) (_q : Query _v)  : (e792 _v) := by
  simp only [e12, e266, e749, e781, e782, e785, e790, e792] at *
  omega
theorem n8852 (_v : Vars) (_q : Query _v)  : (e793 _v) := by
  have p8850 := n8850 _v _q 
  have p8851 := n8851 _v _q 
  exact (Iff.trans p8850 p8851)
theorem n8854 (_v : Vars) (_q : Query _v)  : (e8853 _v) := by
  have p8852 := n8852 _v _q 
  have p5516 := n5516 _v _q 
  change ((e539 _v) ↔ (e749 _v)) at p8852
  change ((e538 _v) = (e785 _v)) at p5516
  simp only [e8853, e540, e794, p8852, p5516]
theorem n8856 (_v : Vars) (_q : Query _v)  : (e8855 _v) := by
  have p8849 := n8849 _v _q 
  have p8854 := n8854 _v _q 
  change ((e787 _v) ↔ (e788 _v)) at p8849
  change ((e540 _v) = (e794 _v)) at p8854
  simp only [e8855, e5428, e5517, p8849, p8854]
theorem n8857 (_v : Vars) (_q : Query _v)  : (e810 _v) := by
  have p5522 := n5522 _v _q 
  change ((e541 _v) = (e806 _v)) at p5522
  simp only [e810, e808, e809, p5522]
theorem n8858 (_v : Vars) (_q : Query _v)  : (e812 _v) := by
  have p5522 := n5522 _v _q 
  change ((e541 _v) = (e806 _v)) at p5522
  simp only [e812, e542, e811, p5522]
theorem n8859 (_v : Vars) (_q : Query _v)  : (e813 _v) := by
  simp only [e12, e108, e749, e802, e803, e806, e811, e813] at *
  omega
theorem n8860 (_v : Vars) (_q : Query _v)  : (e814 _v) := by
  have p8858 := n8858 _v _q 
  have p8859 := n8859 _v _q 
  exact (Iff.trans p8858 p8859)
theorem n8862 (_v : Vars) (_q : Query _v)  : (e8861 _v) := by
  have p8860 := n8860 _v _q 
  have p5522 := n5522 _v _q 
  change ((e542 _v) ↔ (e749 _v)) at p8860
  change ((e541 _v) = (e806 _v)) at p5522
  simp only [e8861, e543, e815, p8860, p5522]
theorem n8864 (_v : Vars) (_q : Query _v)  : (e8863 _v) := by
  have p8857 := n8857 _v _q 
  have p8862 := n8862 _v _q 
  change ((e808 _v) ↔ (e809 _v)) at p8857
  change ((e543 _v) = (e815 _v)) at p8862
  simp only [e8863, e5429, e5523, p8857, p8862]
theorem n8868 (_v : Vars) (_q : Query _v)  : (e8867 _v) := by
  simp only [e5, e8865, e8866, e8867] at *
  omega
theorem n8869 (_v : Vars) (_q : Query _v)  : (e826 _v) := by
  have p5524 := n5524 _v _q 
  have p825 := n825 _v _q 
  exact (Eq.trans p5524 p825)
theorem n8870 (_v : Vars) (_q : Query _v)  : (e830 _v) := by
  have p8869 := n8869 _v _q 
  have p829 := n829 _v _q 
  exact (Eq.trans p8869 p829)
theorem n8871 (_v : Vars) (_q : Query _v)  : (e5526 _v) := by
  have p8870 := n8870 _v _q 
  change ((e546 _v) = (e827 _v)) at p8870
  simp only [e5526, e548, e831, p8870]
theorem n8872 (_v : Vars) (_q : Query _v)  : (e834 _v) := by
  simp only [e5, e6, e12, e36, e827, e831, e832, e833, e834] at *
  omega
theorem n8873 (_v : Vars) (_q : Query _v)  : (e5527 _v) := by
  have p8871 := n8871 _v _q 
  have p8872 := n8872 _v _q 
  exact (Iff.trans p8871 p8872)
theorem n8874 (_v : Vars) (_q : Query _v)  : (e5535 _v) := by
  have p5534 := n5534 _v _q 
  change ((e549 _v) = (e843 _v)) at p5534
  simp only [e5535, e550, e1595, p5534]
theorem n8875 (_v : Vars) (_q : Query _v)  : (e5536 _v) := by
  have p5534 := n5534 _v _q 
  change ((e549 _v) = (e843 _v)) at p5534
  simp only [e5536, e551, e848, p5534]
theorem n8876 (_v : Vars) (_q : Query _v)  : (e851 _v) := by
  simp only [e12, e43, e760, e761, e843, e848, e849, e850, e851] at *
  omega
theorem n8877 (_v : Vars) (_q : Query _v)  : (e5537 _v) := by
  have p8875 := n8875 _v _q 
  have p8876 := n8876 _v _q 
  exact (Iff.trans p8875 p8876)
theorem n8879 (_v : Vars) (_q : Query _v)  : (e8878 _v) := by
  have p8877 := n8877 _v _q 
  have p5534 := n5534 _v _q 
  change ((e551 _v) ↔ (e850 _v)) at p8877
  change ((e549 _v) = (e843 _v)) at p5534
  simp only [e8878, e5431, e852, p8877, p5534]
theorem n8881 (_v : Vars) (_q : Query _v)  : (e8880 _v) := by
  have p8874 := n8874 _v _q 
  have p8879 := n8879 _v _q 
  change ((e550 _v) ↔ (e1595 _v)) at p8874
  change ((e5431 _v) = (e852 _v)) at p8879
  simp only [e8880, e8764, e5538, p8874, p8879]
theorem n8882 (_v : Vars) (_q : Query _v)  : (e5545 _v) := by
  have p5544 := n5544 _v _q 
  change ((e552 _v) = (e860 _v)) at p5544
  simp only [e5545, e553, e1602, p5544]
theorem n8883 (_v : Vars) (_q : Query _v)  : (e5546 _v) := by
  have p5544 := n5544 _v _q 
  change ((e552 _v) = (e860 _v)) at p5544
  simp only [e5546, e554, e865, p5544]
theorem n8884 (_v : Vars) (_q : Query _v)  : (e868 _v) := by
  simp only [e12, e266, e781, e782, e860, e865, e866, e867, e868] at *
  omega
theorem n8885 (_v : Vars) (_q : Query _v)  : (e5547 _v) := by
  have p8883 := n8883 _v _q 
  have p8884 := n8884 _v _q 
  exact (Iff.trans p8883 p8884)
theorem n8887 (_v : Vars) (_q : Query _v)  : (e8886 _v) := by
  have p8885 := n8885 _v _q 
  have p5544 := n5544 _v _q 
  change ((e554 _v) ↔ (e867 _v)) at p8885
  change ((e552 _v) = (e860 _v)) at p5544
  simp only [e8886, e5432, e869, p8885, p5544]
theorem n8889 (_v : Vars) (_q : Query _v)  : (e8888 _v) := by
  have p8882 := n8882 _v _q 
  have p8887 := n8887 _v _q 
  change ((e553 _v) ↔ (e1602 _v)) at p8882
  change ((e5432 _v) = (e869 _v)) at p8887
  simp only [e8888, e8765, e5548, p8882, p8887]
theorem n8890 (_v : Vars) (_q : Query _v)  : (e5555 _v) := by
  have p5554 := n5554 _v _q 
  change ((e555 _v) = (e877 _v)) at p5554
  simp only [e5555, e556, e1609, p5554]
theorem n8891 (_v : Vars) (_q : Query _v)  : (e5556 _v) := by
  have p5554 := n5554 _v _q 
  change ((e555 _v) = (e877 _v)) at p5554
  simp only [e5556, e557, e882, p5554]
theorem n8892 (_v : Vars) (_q : Query _v)  : (e885 _v) := by
  simp only [e12, e108, e802, e803, e877, e882, e883, e884, e885] at *
  omega
theorem n8893 (_v : Vars) (_q : Query _v)  : (e5557 _v) := by
  have p8891 := n8891 _v _q 
  have p8892 := n8892 _v _q 
  exact (Iff.trans p8891 p8892)
theorem n8895 (_v : Vars) (_q : Query _v)  : (e8894 _v) := by
  have p8893 := n8893 _v _q 
  have p5554 := n5554 _v _q 
  change ((e557 _v) ↔ (e884 _v)) at p8893
  change ((e555 _v) = (e877 _v)) at p5554
  simp only [e8894, e5433, e886, p8893, p5554]
theorem n8897 (_v : Vars) (_q : Query _v)  : (e8896 _v) := by
  have p8890 := n8890 _v _q 
  have p8895 := n8895 _v _q 
  change ((e556 _v) ↔ (e1609 _v)) at p8890
  change ((e5433 _v) = (e886 _v)) at p8895
  simp only [e8896, e8766, e5558, p8890, p8895]
theorem n8903 (_v : Vars) (_q : Query _v)  : (e897 _v) := by
  have p5559 := n5559 _v _q 
  have p896 := n896 _v _q 
  exact (Eq.trans p5559 p896)
theorem n8904 (_v : Vars) (_q : Query _v)  : (e901 _v) := by
  have p8903 := n8903 _v _q 
  have p900 := n900 _v _q 
  exact (Eq.trans p8903 p900)
theorem n8905 (_v : Vars) (_q : Query _v)  : (e5561 _v) := by
  have p8904 := n8904 _v _q 
  change ((e560 _v) = (e898 _v)) at p8904
  simp only [e5561, e562, e902, p8904]
end
end Assembly
