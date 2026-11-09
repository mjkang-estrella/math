import Dag037
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n8973 (_v : Vars) (_q : Query _v)  : (e5661 _v) := by
  have p5660 := n5660 _v _q 
  change ((e596 _v) = (e1063 _v)) at p5660
  simp only [e5661, e597, e1693, p5660]
theorem n8974 (_v : Vars) (_q : Query _v)  : (e5662 _v) := by
  have p5660 := n5660 _v _q 
  change ((e596 _v) = (e1063 _v)) at p5660
  simp only [e5662, e598, e1068, p5660]
theorem n8975 (_v : Vars) (_q : Query _v)  : (e1071 _v) := by
  simp only [e12, e108, e802, e803, e1063, e1068, e1069, e1070, e1071] at *
  omega
theorem n8976 (_v : Vars) (_q : Query _v)  : (e5663 _v) := by
  have p8974 := n8974 _v _q 
  have p8975 := n8975 _v _q 
  exact (Iff.trans p8974 p8975)
theorem n8978 (_v : Vars) (_q : Query _v)  : (e8977 _v) := by
  have p8976 := n8976 _v _q 
  have p5660 := n5660 _v _q 
  change ((e598 _v) ↔ (e1070 _v)) at p8976
  change ((e596 _v) = (e1063 _v)) at p5660
  simp only [e8977, e5445, e1072, p8976, p5660]
theorem n8980 (_v : Vars) (_q : Query _v)  : (e8979 _v) := by
  have p8973 := n8973 _v _q 
  have p8978 := n8978 _v _q 
  change ((e597 _v) ↔ (e1693 _v)) at p8973
  change ((e5445 _v) = (e1072 _v)) at p8978
  simp only [e8979, e8781, e5664, p8973, p8978]
theorem n8987 (_v : Vars) (_q : Query _v)  : (e8986 _v) := by
  have p5666 := n5666 _v _q 
  have p1078 := n1078 _v _q 
  exact (Eq.trans p5666 p1078)
theorem n8988 (_v : Vars) (_q : Query _v)  : (e5673 _v) := by
  have p5672 := n5672 _v _q 
  have p5674 := n5674 _v _q 
  exact (Eq.trans p5672 p5674)
theorem n8990 (_v : Vars) (_q : Query _v)  : (e8989 _v) := by
  have p5676 := n5676 _v _q 
  have p1091 := n1091 _v _q 
  exact (Eq.trans p5676 p1091)
theorem n8991 (_v : Vars) (_q : Query _v)  : (e5683 _v) := by
  have p5682 := n5682 _v _q 
  have p5684 := n5684 _v _q 
  exact (Eq.trans p5682 p5684)
theorem n8993 (_v : Vars) (_q : Query _v)  : (e8992 _v) := by
  have p5686 := n5686 _v _q 
  have p1101 := n1101 _v _q 
  exact (Eq.trans p5686 p1101)
theorem n8994 (_v : Vars) (_q : Query _v)  : (e5693 _v) := by
  have p5692 := n5692 _v _q 
  have p5694 := n5694 _v _q 
  exact (Eq.trans p5692 p5694)
theorem n8996 (_v : Vars) (_q : Query _v)  : (e8995 _v) := by
  have p5696 := n5696 _v _q 
  have p1111 := n1111 _v _q 
  exact (Eq.trans p5696 p1111)
theorem n9000 (_v : Vars) (_q : Query _v)  : (e8999 _v) := by
  simp only [e5, e8997, e8998, e8999] at *
  omega
theorem n9002 (_v : Vars) (_q : Query _v)  : (e9001 _v) := by
  have p5702 := n5702 _v _q 
  have p1122 := n1122 _v _q 
  exact (Eq.trans p5702 p1122)
theorem n9003 (_v : Vars) (_q : Query _v)  : (e5709 _v) := by
  have p5708 := n5708 _v _q 
  have p5710 := n5710 _v _q 
  exact (Eq.trans p5708 p5710)
theorem n9005 (_v : Vars) (_q : Query _v)  : (e9004 _v) := by
  have p5712 := n5712 _v _q 
  have p1135 := n1135 _v _q 
  exact (Eq.trans p5712 p1135)
theorem n9006 (_v : Vars) (_q : Query _v)  : (e5719 _v) := by
  have p5718 := n5718 _v _q 
  have p5720 := n5720 _v _q 
  exact (Eq.trans p5718 p5720)
theorem n9008 (_v : Vars) (_q : Query _v)  : (e9007 _v) := by
  have p5722 := n5722 _v _q 
  have p1145 := n1145 _v _q 
  exact (Eq.trans p5722 p1145)
theorem n9009 (_v : Vars) (_q : Query _v)  : (e5729 _v) := by
  have p5728 := n5728 _v _q 
  have p5730 := n5730 _v _q 
  exact (Eq.trans p5728 p5730)
theorem n9011 (_v : Vars) (_q : Query _v)  : (e9010 _v) := by
  have p5732 := n5732 _v _q 
  have p1155 := n1155 _v _q 
  exact (Eq.trans p5732 p1155)
theorem n9015 (_v : Vars) (_q : Query _v)  : (e9014 _v) := by
  simp only [e5, e9012, e9013, e9014] at *
  omega
theorem n9017 (_v : Vars) (_q : Query _v)  : (e9016 _v) := by
  have p5738 := n5738 _v _q 
  have p1166 := n1166 _v _q 
  exact (Eq.trans p5738 p1166)
theorem n9018 (_v : Vars) (_q : Query _v)  : (e5743 _v) := by
  have p5742 := n5742 _v _q 
  have p5744 := n5744 _v _q 
  exact (Eq.trans p5742 p5744)
theorem n9020 (_v : Vars) (_q : Query _v)  : (e9019 _v) := by
  have p5746 := n5746 _v _q 
  have p1179 := n1179 _v _q 
  exact (Eq.trans p5746 p1179)
theorem n9021 (_v : Vars) (_q : Query _v)  : (e5751 _v) := by
  have p5750 := n5750 _v _q 
  have p5752 := n5752 _v _q 
  exact (Eq.trans p5750 p5752)
theorem n9023 (_v : Vars) (_q : Query _v)  : (e9022 _v) := by
  have p5754 := n5754 _v _q 
  have p1189 := n1189 _v _q 
  exact (Eq.trans p5754 p1189)
theorem n9024 (_v : Vars) (_q : Query _v)  : (e5759 _v) := by
  have p5758 := n5758 _v _q 
  have p5760 := n5760 _v _q 
  exact (Eq.trans p5758 p5760)
theorem n9026 (_v : Vars) (_q : Query _v)  : (e9025 _v) := by
  have p5762 := n5762 _v _q 
  have p1199 := n1199 _v _q 
  exact (Eq.trans p5762 p1199)
theorem n9027 (_v : Vars) (_q : Query _v)  : (e1215 _v) := by
  have p5775 := n5775 _v _q 
  have p1214 := n1214 _v _q 
  exact (Eq.trans p5775 p1214)
theorem n9028 (_v : Vars) (_q : Query _v)  : (e1219 _v) := by
  have p9027 := n9027 _v _q 
  have p1218 := n1218 _v _q 
  exact (Eq.trans p9027 p1218)
theorem n9029 (_v : Vars) (_q : Query _v)  : (e5777 _v) := by
  have p9028 := n9028 _v _q 
  change ((e640 _v) = (e1216 _v)) at p9028
  simp only [e5777, e642, e1220, p9028]
theorem n9030 (_v : Vars) (_q : Query _v)  : (e1223 _v) := by
  simp only [e5, e6, e12, e36, e1216, e1220, e1221, e1222, e1223] at *
  omega
theorem n9031 (_v : Vars) (_q : Query _v)  : (e5778 _v) := by
  have p9029 := n9029 _v _q 
  have p9030 := n9030 _v _q 
  exact (Iff.trans p9029 p9030)
theorem n9032 (_v : Vars) (_q : Query _v)  : (e5786 _v) := by
  have p5785 := n5785 _v _q 
  change ((e643 _v) = (e1232 _v)) at p5785
  simp only [e5786, e644, e1783, p5785]
theorem n9033 (_v : Vars) (_q : Query _v)  : (e5787 _v) := by
  have p5785 := n5785 _v _q 
  change ((e643 _v) = (e1232 _v)) at p5785
  simp only [e5787, e645, e1237, p5785]
theorem n9034 (_v : Vars) (_q : Query _v)  : (e1240 _v) := by
  simp only [e12, e43, e760, e761, e1232, e1237, e1238, e1239, e1240] at *
  omega
theorem n9035 (_v : Vars) (_q : Query _v)  : (e5788 _v) := by
  have p9033 := n9033 _v _q 
  have p9034 := n9034 _v _q 
  exact (Iff.trans p9033 p9034)
theorem n9037 (_v : Vars) (_q : Query _v)  : (e9036 _v) := by
  have p9035 := n9035 _v _q 
  have p5785 := n5785 _v _q 
  change ((e645 _v) ↔ (e1239 _v)) at p9035
  change ((e643 _v) = (e1232 _v)) at p5785
  simp only [e9036, e5459, e1241, p9035, p5785]
theorem n9039 (_v : Vars) (_q : Query _v)  : (e9038 _v) := by
  have p9032 := n9032 _v _q 
  have p9037 := n9037 _v _q 
  change ((e644 _v) ↔ (e1783 _v)) at p9032
  change ((e5459 _v) = (e1241 _v)) at p9037
  simp only [e9038, e8799, e5789, p9032, p9037]
theorem n9040 (_v : Vars) (_q : Query _v)  : (e5796 _v) := by
  have p5795 := n5795 _v _q 
  change ((e646 _v) = (e1249 _v)) at p5795
  simp only [e5796, e647, e1790, p5795]
theorem n9041 (_v : Vars) (_q : Query _v)  : (e5797 _v) := by
  have p5795 := n5795 _v _q 
  change ((e646 _v) = (e1249 _v)) at p5795
  simp only [e5797, e648, e1254, p5795]
theorem n9042 (_v : Vars) (_q : Query _v)  : (e1257 _v) := by
  simp only [e12, e266, e781, e782, e1249, e1254, e1255, e1256, e1257] at *
  omega
theorem n9043 (_v : Vars) (_q : Query _v)  : (e5798 _v) := by
  have p9041 := n9041 _v _q 
  have p9042 := n9042 _v _q 
  exact (Iff.trans p9041 p9042)
theorem n9045 (_v : Vars) (_q : Query _v)  : (e9044 _v) := by
  have p9043 := n9043 _v _q 
  have p5795 := n5795 _v _q 
  change ((e648 _v) ↔ (e1256 _v)) at p9043
  change ((e646 _v) = (e1249 _v)) at p5795
  simp only [e9044, e5460, e1258, p9043, p5795]
end
end Assembly
