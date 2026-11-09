import Dag000
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n425 (_v : Vars) (_q : Query _v)  : (e424 _v) := by
  simp only [e414, e421, e422, e423, e424] at *
  omega
theorem n451 (_v : Vars) (_q : Query _v)  : (e450 _v) := by
  simp only [e446, e447, e448, e449, e450] at *
  omega
theorem n459 (_v : Vars) (_q : Query _v)  : (e458 _v) := by
  exact (((((((_q).2).2).2).2).2).2).1
theorem n461 (_v : Vars) (_q : Query _v)  : (e460 _v) := by
  simp only [e458, e460] at *
theorem n462 (_v : Vars) (_q : Query _v)  : (e458 _v) := by
  have p459 := n459 _v _q 
  have p461 := n461 _v _q 
  simp only [e458, e460] at *
  tauto
theorem n478 (_v : Vars) (_q : Query _v)  : (e477 _v) := by
  simp only [e12, e467, e469, e475, e476, e477] at *
  omega
theorem n485 (_v : Vars) (_q : Query _v)  : (e484 _v) := by
  simp only [e480, e481, e482, e483, e484] at *
  omega
theorem n513 (_v : Vars) (_q : Query _v)  : (e512 _v) := by
  simp only [e12, e498, e500, e510, e511, e512] at *
  omega
theorem n519 (_v : Vars) (_q : Query _v)  : (e518 _v) := by
  simp only [e508, e515, e516, e517, e518] at *
  omega
theorem n737 (_v : Vars) (_q : Query _v)  : (e736 _v) := by
  simp only [e12, e530, e736] at *
  omega
theorem n739 (_v : Vars) (_q : Query _v)  : (e738 _v) := by
  simp only [e5, e531, e738] at *
  omega
theorem n742 (_v : Vars) (_q : Query _v)  : (e741 _v) := by
  have p737 := n737 _v _q 
  have p739 := n739 _v _q 
  change ((e530 _v) = (e17 _v)) at p737
  change ((e531 _v) = (e2 _v)) at p739
  simp only [e741, e532, e740, p737, p739]
theorem n744 (_v : Vars) (_q : Query _v)  : (e743 _v) := by
  simp only [e5, e6, e36, e142, e740, e743] at *
  omega
theorem n755 (_v : Vars) (_q : Query _v)  : (e754 _v) := by
  have p737 := n737 _v _q 
  change ((e530 _v) = (e17 _v)) at p737
  simp only [e754, e535, e753, p737]
theorem n763 (_v : Vars) (_q : Query _v)  : (e762 _v) := by
  simp only [e5, e6, e43, e44, e756, e760, e761, e762] at *
  omega
theorem n776 (_v : Vars) (_q : Query _v)  : (e775 _v) := by
  have p737 := n737 _v _q 
  change ((e530 _v) = (e17 _v)) at p737
  simp only [e775, e538, e774, p737]
theorem n784 (_v : Vars) (_q : Query _v)  : (e783 _v) := by
  simp only [e5, e6, e266, e267, e777, e781, e782, e783] at *
  omega
theorem n797 (_v : Vars) (_q : Query _v)  : (e796 _v) := by
  have p737 := n737 _v _q 
  change ((e530 _v) = (e17 _v)) at p737
  simp only [e796, e541, e795, p737]
theorem n805 (_v : Vars) (_q : Query _v)  : (e804 _v) := by
  simp only [e5, e6, e108, e109, e798, e802, e803, e804] at *
  omega
theorem n817 (_v : Vars) (_q : Query _v)  : (e816 _v) := by
  simp only [e544, e816] at *
theorem n820 (_v : Vars) (_q : Query _v)  : (e819 _v) := by
  have p817 := n817 _v _q 
  change ((e544 _v) = (e7 _v)) at p817
  simp only [e819, e545, e818, p817]
theorem n825 (_v : Vars) (_q : Query _v)  : (e824 _v) := by
  simp only [e5, e6, e36, e818, e821, e823, e824] at *
  omega
theorem n829 (_v : Vars) (_q : Query _v)  : (e828 _v) := by
  simp only [e5, e6, e36, e818, e823, e827, e828] at *
theorem n845 (_v : Vars) (_q : Query _v)  : (e844 _v) := by
  simp only [e43, e760, e761, e818, e841, e843, e844] at *
theorem n862 (_v : Vars) (_q : Query _v)  : (e861 _v) := by
  simp only [e266, e781, e782, e818, e858, e860, e861] at *
theorem n879 (_v : Vars) (_q : Query _v)  : (e878 _v) := by
  simp only [e108, e802, e803, e818, e875, e877, e878] at *
theorem n888 (_v : Vars) (_q : Query _v)  : (e887 _v) := by
  simp only [e558, e887] at *
theorem n891 (_v : Vars) (_q : Query _v)  : (e890 _v) := by
  have p888 := n888 _v _q 
  change ((e558 _v) = (e110 _v)) at p888
  simp only [e890, e559, e889, p888]
theorem n896 (_v : Vars) (_q : Query _v)  : (e895 _v) := by
  simp only [e5, e6, e36, e889, e892, e894, e895] at *
  omega
theorem n900 (_v : Vars) (_q : Query _v)  : (e899 _v) := by
  simp only [e5, e6, e36, e889, e894, e898, e899] at *
theorem n916 (_v : Vars) (_q : Query _v)  : (e915 _v) := by
  simp only [e43, e760, e761, e889, e912, e914, e915] at *
theorem n933 (_v : Vars) (_q : Query _v)  : (e932 _v) := by
  simp only [e266, e781, e782, e889, e929, e931, e932] at *
theorem n950 (_v : Vars) (_q : Query _v)  : (e949 _v) := by
  simp only [e108, e802, e803, e889, e946, e948, e949] at *
theorem n959 (_v : Vars) (_q : Query _v)  : (e958 _v) := by
  simp only [e572, e958] at *
theorem n963 (_v : Vars) (_q : Query _v)  : (e962 _v) := by
  simp only [e5, e6, e36, e572, e960, e961, e962] at *
  omega
theorem n966 (_v : Vars) (_q : Query _v)  : (e965 _v) := by
  simp only [e5, e6, e36, e572, e961, e964, e965] at *
theorem n976 (_v : Vars) (_q : Query _v)  : (e975 _v) := by
  simp only [e43, e572, e760, e761, e973, e974, e975] at *
theorem n986 (_v : Vars) (_q : Query _v)  : (e985 _v) := by
  simp only [e266, e572, e781, e782, e983, e984, e985] at *
theorem n996 (_v : Vars) (_q : Query _v)  : (e995 _v) := by
  simp only [e108, e572, e802, e803, e993, e994, e995] at *
theorem n1003 (_v : Vars) (_q : Query _v)  : (e1002 _v) := by
  simp only [e585, e1002] at *
theorem n1006 (_v : Vars) (_q : Query _v)  : (e1005 _v) := by
  have p1003 := n1003 _v _q 
  change ((e585 _v) = (e9 _v)) at p1003
  simp only [e1005, e586, e1004, p1003]
theorem n1011 (_v : Vars) (_q : Query _v)  : (e1010 _v) := by
  simp only [e5, e6, e36, e1004, e1007, e1009, e1010] at *
  omega
theorem n1015 (_v : Vars) (_q : Query _v)  : (e1014 _v) := by
  simp only [e5, e6, e36, e1004, e1009, e1013, e1014] at *
theorem n1031 (_v : Vars) (_q : Query _v)  : (e1030 _v) := by
  simp only [e43, e760, e761, e1004, e1027, e1029, e1030] at *
theorem n1048 (_v : Vars) (_q : Query _v)  : (e1047 _v) := by
  simp only [e266, e781, e782, e1004, e1044, e1046, e1047] at *
end
end Assembly
