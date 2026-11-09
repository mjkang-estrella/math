import Dag017
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n5738 (_v : Vars) (_q : Query _v)  : (e5737 _v) := by
  have p1162 := n1162 _v _q 
  have p739 := n739 _v _q 
  change ((e625 _v) = (e625 _v)) at p1162
  change ((e531 _v) = (e2 _v)) at p739
  simp only [e5737, e626, e1163, p1162, p739]
theorem n5742 (_v : Vars) (_q : Query _v)  : (e5741 _v) := by
  have p1162 := n1162 _v _q 
  change ((e625 _v) = (e625 _v)) at p1162
  simp only [e5741, e629, p1162]
theorem n5744 (_v : Vars) (_q : Query _v)  : (e5743 _v) := by
  simp only [e5, e6, e43, e44, e625, e629, e756, e1175, e5743] at *
  omega
theorem n5746 (_v : Vars) (_q : Query _v)  : (e5745 _v) := by
  have p763 := n763 _v _q 
  change ((e756 _v) = (e761 _v)) at p763
  simp only [e5745, e1175, e1176, p763]
theorem n5750 (_v : Vars) (_q : Query _v)  : (e5749 _v) := by
  have p1162 := n1162 _v _q 
  change ((e625 _v) = (e625 _v)) at p1162
  simp only [e5749, e632, p1162]
theorem n5752 (_v : Vars) (_q : Query _v)  : (e5751 _v) := by
  simp only [e5, e6, e266, e267, e625, e632, e777, e1185, e5751] at *
  omega
theorem n5754 (_v : Vars) (_q : Query _v)  : (e5753 _v) := by
  have p784 := n784 _v _q 
  change ((e777 _v) = (e782 _v)) at p784
  simp only [e5753, e1185, e1186, p784]
theorem n5758 (_v : Vars) (_q : Query _v)  : (e5757 _v) := by
  have p1162 := n1162 _v _q 
  change ((e625 _v) = (e625 _v)) at p1162
  simp only [e5757, e635, p1162]
theorem n5760 (_v : Vars) (_q : Query _v)  : (e5759 _v) := by
  simp only [e5, e6, e108, e109, e625, e635, e798, e1195, e5759] at *
  omega
theorem n5762 (_v : Vars) (_q : Query _v)  : (e5761 _v) := by
  have p805 := n805 _v _q 
  change ((e798 _v) = (e803 _v)) at p805
  simp only [e5761, e1195, e1196, p805]
theorem n5775 (_v : Vars) (_q : Query _v)  : (e1211 _v) := by
  have p1209 := n1209 _v _q 
  have p739 := n739 _v _q 
  change ((e639 _v) = (e1207 _v)) at p1209
  change ((e531 _v) = (e2 _v)) at p739
  simp only [e1211, e640, e1210, p1209, p739]
theorem n5780 (_v : Vars) (_q : Query _v)  : (e1226 _v) := by
  have p1209 := n1209 _v _q 
  change ((e639 _v) = (e1207 _v)) at p1209
  simp only [e1226, e643, e1225, p1209]
theorem n5781 (_v : Vars) (_q : Query _v)  : (e1228 _v) := by
  simp only [e5, e6, e43, e44, e756, e1207, e1225, e1227, e1228] at *
  omega
theorem n5782 (_v : Vars) (_q : Query _v)  : (e1229 _v) := by
  have p5780 := n5780 _v _q 
  have p5781 := n5781 _v _q 
  exact (Eq.trans p5780 p5781)
theorem n5783 (_v : Vars) (_q : Query _v)  : (e1231 _v) := by
  have p763 := n763 _v _q 
  change ((e756 _v) = (e761 _v)) at p763
  simp only [e1231, e1227, e1230, p763]
theorem n5784 (_v : Vars) (_q : Query _v)  : (e1235 _v) := by
  have p5783 := n5783 _v _q 
  have p1234 := n1234 _v _q 
  exact (Eq.trans p5783 p1234)
theorem n5785 (_v : Vars) (_q : Query _v)  : (e1236 _v) := by
  have p5782 := n5782 _v _q 
  have p5784 := n5784 _v _q 
  exact (Eq.trans p5782 p5784)
theorem n5790 (_v : Vars) (_q : Query _v)  : (e1243 _v) := by
  have p1209 := n1209 _v _q 
  change ((e639 _v) = (e1207 _v)) at p1209
  simp only [e1243, e646, e1242, p1209]
theorem n5791 (_v : Vars) (_q : Query _v)  : (e1245 _v) := by
  simp only [e5, e6, e266, e267, e777, e1207, e1242, e1244, e1245] at *
  omega
theorem n5792 (_v : Vars) (_q : Query _v)  : (e1246 _v) := by
  have p5790 := n5790 _v _q 
  have p5791 := n5791 _v _q 
  exact (Eq.trans p5790 p5791)
theorem n5793 (_v : Vars) (_q : Query _v)  : (e1248 _v) := by
  have p784 := n784 _v _q 
  change ((e777 _v) = (e782 _v)) at p784
  simp only [e1248, e1244, e1247, p784]
theorem n5794 (_v : Vars) (_q : Query _v)  : (e1252 _v) := by
  have p5793 := n5793 _v _q 
  have p1251 := n1251 _v _q 
  exact (Eq.trans p5793 p1251)
theorem n5795 (_v : Vars) (_q : Query _v)  : (e1253 _v) := by
  have p5792 := n5792 _v _q 
  have p5794 := n5794 _v _q 
  exact (Eq.trans p5792 p5794)
theorem n5800 (_v : Vars) (_q : Query _v)  : (e1260 _v) := by
  have p1209 := n1209 _v _q 
  change ((e639 _v) = (e1207 _v)) at p1209
  simp only [e1260, e649, e1259, p1209]
theorem n5801 (_v : Vars) (_q : Query _v)  : (e1262 _v) := by
  simp only [e5, e6, e108, e109, e798, e1207, e1259, e1261, e1262] at *
  omega
theorem n5802 (_v : Vars) (_q : Query _v)  : (e1263 _v) := by
  have p5800 := n5800 _v _q 
  have p5801 := n5801 _v _q 
  exact (Eq.trans p5800 p5801)
theorem n5803 (_v : Vars) (_q : Query _v)  : (e1265 _v) := by
  have p805 := n805 _v _q 
  change ((e798 _v) = (e803 _v)) at p805
  simp only [e1265, e1261, e1264, p805]
theorem n5804 (_v : Vars) (_q : Query _v)  : (e1269 _v) := by
  have p5803 := n5803 _v _q 
  have p1268 := n1268 _v _q 
  exact (Eq.trans p5803 p1268)
theorem n5805 (_v : Vars) (_q : Query _v)  : (e1270 _v) := by
  have p5802 := n5802 _v _q 
  have p5804 := n5804 _v _q 
  exact (Eq.trans p5802 p5804)
theorem n5811 (_v : Vars) (_q : Query _v)  : (e5810 _v) := by
  have p1277 := n1277 _v _q 
  have p739 := n739 _v _q 
  change ((e652 _v) = (e652 _v)) at p1277
  change ((e531 _v) = (e2 _v)) at p739
  simp only [e5810, e653, e1278, p1277, p739]
theorem n5817 (_v : Vars) (_q : Query _v)  : (e5816 _v) := by
  have p1277 := n1277 _v _q 
  change ((e652 _v) = (e652 _v)) at p1277
  simp only [e5816, e656, p1277]
theorem n5819 (_v : Vars) (_q : Query _v)  : (e5818 _v) := by
  simp only [e5, e6, e43, e44, e652, e656, e756, e1290, e5818] at *
  omega
theorem n5821 (_v : Vars) (_q : Query _v)  : (e5820 _v) := by
  have p763 := n763 _v _q 
  change ((e756 _v) = (e761 _v)) at p763
  simp only [e5820, e1290, e1291, p763]
theorem n5827 (_v : Vars) (_q : Query _v)  : (e5826 _v) := by
  have p1277 := n1277 _v _q 
  change ((e652 _v) = (e652 _v)) at p1277
  simp only [e5826, e659, p1277]
theorem n5829 (_v : Vars) (_q : Query _v)  : (e5828 _v) := by
  simp only [e5, e6, e266, e267, e652, e659, e777, e1300, e5828] at *
  omega
theorem n5831 (_v : Vars) (_q : Query _v)  : (e5830 _v) := by
  have p784 := n784 _v _q 
  change ((e777 _v) = (e782 _v)) at p784
  simp only [e5830, e1300, e1301, p784]
theorem n5837 (_v : Vars) (_q : Query _v)  : (e5836 _v) := by
  have p1277 := n1277 _v _q 
  change ((e652 _v) = (e652 _v)) at p1277
  simp only [e5836, e662, p1277]
theorem n5839 (_v : Vars) (_q : Query _v)  : (e5838 _v) := by
  simp only [e5, e6, e108, e109, e652, e662, e798, e1310, e5838] at *
  omega
theorem n5841 (_v : Vars) (_q : Query _v)  : (e5840 _v) := by
  have p805 := n805 _v _q 
  change ((e798 _v) = (e803 _v)) at p805
  simp only [e5840, e1310, e1311, p805]
theorem n5847 (_v : Vars) (_q : Query _v)  : (e5846 _v) := by
  have p1321 := n1321 _v _q 
  have p739 := n739 _v _q 
  change ((e665 _v) = (e665 _v)) at p1321
  change ((e531 _v) = (e2 _v)) at p739
  simp only [e5846, e666, e1322, p1321, p739]
theorem n5853 (_v : Vars) (_q : Query _v)  : (e5852 _v) := by
  have p1321 := n1321 _v _q 
  change ((e665 _v) = (e665 _v)) at p1321
  simp only [e5852, e669, p1321]
theorem n5855 (_v : Vars) (_q : Query _v)  : (e5854 _v) := by
  simp only [e5, e6, e43, e44, e665, e669, e756, e1334, e5854] at *
  omega
theorem n5857 (_v : Vars) (_q : Query _v)  : (e5856 _v) := by
  have p763 := n763 _v _q 
  change ((e756 _v) = (e761 _v)) at p763
  simp only [e5856, e1334, e1335, p763]
theorem n5863 (_v : Vars) (_q : Query _v)  : (e5862 _v) := by
  have p1321 := n1321 _v _q 
  change ((e665 _v) = (e665 _v)) at p1321
  simp only [e5862, e672, p1321]
theorem n5865 (_v : Vars) (_q : Query _v)  : (e5864 _v) := by
  simp only [e5, e6, e266, e267, e665, e672, e777, e1344, e5864] at *
  omega
end
end Assembly
