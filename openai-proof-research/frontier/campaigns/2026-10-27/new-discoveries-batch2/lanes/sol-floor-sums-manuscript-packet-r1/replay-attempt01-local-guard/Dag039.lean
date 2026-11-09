import Dag038
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n9047 (_v : Vars) (_q : Query _v)  : (e9046 _v) := by
  have p9040 := n9040 _v _q 
  have p9045 := n9045 _v _q 
  change ((e647 _v) ↔ (e1790 _v)) at p9040
  change ((e5460 _v) = (e1258 _v)) at p9045
  simp only [e9046, e8800, e5799, p9040, p9045]
theorem n9048 (_v : Vars) (_q : Query _v)  : (e5806 _v) := by
  have p5805 := n5805 _v _q 
  change ((e649 _v) = (e1266 _v)) at p5805
  simp only [e5806, e650, e1797, p5805]
theorem n9049 (_v : Vars) (_q : Query _v)  : (e5807 _v) := by
  have p5805 := n5805 _v _q 
  change ((e649 _v) = (e1266 _v)) at p5805
  simp only [e5807, e651, e1271, p5805]
theorem n9050 (_v : Vars) (_q : Query _v)  : (e1274 _v) := by
  simp only [e12, e108, e802, e803, e1266, e1271, e1272, e1273, e1274] at *
  omega
theorem n9051 (_v : Vars) (_q : Query _v)  : (e5808 _v) := by
  have p9049 := n9049 _v _q 
  have p9050 := n9050 _v _q 
  exact (Iff.trans p9049 p9050)
theorem n9053 (_v : Vars) (_q : Query _v)  : (e9052 _v) := by
  have p9051 := n9051 _v _q 
  have p5805 := n5805 _v _q 
  change ((e651 _v) ↔ (e1273 _v)) at p9051
  change ((e649 _v) = (e1266 _v)) at p5805
  simp only [e9052, e5461, e1275, p9051, p5805]
theorem n9055 (_v : Vars) (_q : Query _v)  : (e9054 _v) := by
  have p9048 := n9048 _v _q 
  have p9053 := n9053 _v _q 
  change ((e650 _v) ↔ (e1797 _v)) at p9048
  change ((e5461 _v) = (e1275 _v)) at p9053
  simp only [e9054, e8801, e5809, p9048, p9053]
theorem n9062 (_v : Vars) (_q : Query _v)  : (e9061 _v) := by
  have p5811 := n5811 _v _q 
  have p1281 := n1281 _v _q 
  exact (Eq.trans p5811 p1281)
theorem n9063 (_v : Vars) (_q : Query _v)  : (e5818 _v) := by
  have p5817 := n5817 _v _q 
  have p5819 := n5819 _v _q 
  exact (Eq.trans p5817 p5819)
theorem n9065 (_v : Vars) (_q : Query _v)  : (e9064 _v) := by
  have p5821 := n5821 _v _q 
  have p1294 := n1294 _v _q 
  exact (Eq.trans p5821 p1294)
theorem n9066 (_v : Vars) (_q : Query _v)  : (e5828 _v) := by
  have p5827 := n5827 _v _q 
  have p5829 := n5829 _v _q 
  exact (Eq.trans p5827 p5829)
theorem n9068 (_v : Vars) (_q : Query _v)  : (e9067 _v) := by
  have p5831 := n5831 _v _q 
  have p1304 := n1304 _v _q 
  exact (Eq.trans p5831 p1304)
theorem n9069 (_v : Vars) (_q : Query _v)  : (e5838 _v) := by
  have p5837 := n5837 _v _q 
  have p5839 := n5839 _v _q 
  exact (Eq.trans p5837 p5839)
theorem n9071 (_v : Vars) (_q : Query _v)  : (e9070 _v) := by
  have p5841 := n5841 _v _q 
  have p1314 := n1314 _v _q 
  exact (Eq.trans p5841 p1314)
theorem n9075 (_v : Vars) (_q : Query _v)  : (e9074 _v) := by
  simp only [e5, e9072, e9073, e9074] at *
  omega
theorem n9077 (_v : Vars) (_q : Query _v)  : (e9076 _v) := by
  have p5847 := n5847 _v _q 
  have p1325 := n1325 _v _q 
  exact (Eq.trans p5847 p1325)
theorem n9078 (_v : Vars) (_q : Query _v)  : (e5854 _v) := by
  have p5853 := n5853 _v _q 
  have p5855 := n5855 _v _q 
  exact (Eq.trans p5853 p5855)
theorem n9080 (_v : Vars) (_q : Query _v)  : (e9079 _v) := by
  have p5857 := n5857 _v _q 
  have p1338 := n1338 _v _q 
  exact (Eq.trans p5857 p1338)
theorem n9081 (_v : Vars) (_q : Query _v)  : (e5864 _v) := by
  have p5863 := n5863 _v _q 
  have p5865 := n5865 _v _q 
  exact (Eq.trans p5863 p5865)
theorem n9083 (_v : Vars) (_q : Query _v)  : (e9082 _v) := by
  have p5867 := n5867 _v _q 
  have p1348 := n1348 _v _q 
  exact (Eq.trans p5867 p1348)
theorem n9084 (_v : Vars) (_q : Query _v)  : (e5874 _v) := by
  have p5873 := n5873 _v _q 
  have p5875 := n5875 _v _q 
  exact (Eq.trans p5873 p5875)
theorem n9086 (_v : Vars) (_q : Query _v)  : (e9085 _v) := by
  have p5877 := n5877 _v _q 
  have p1358 := n1358 _v _q 
  exact (Eq.trans p5877 p1358)
theorem n9090 (_v : Vars) (_q : Query _v)  : (e9089 _v) := by
  simp only [e5, e9087, e9088, e9089] at *
  omega
theorem n9092 (_v : Vars) (_q : Query _v)  : (e9091 _v) := by
  have p5883 := n5883 _v _q 
  have p1369 := n1369 _v _q 
  exact (Eq.trans p5883 p1369)
theorem n9093 (_v : Vars) (_q : Query _v)  : (e5888 _v) := by
  have p5887 := n5887 _v _q 
  have p5889 := n5889 _v _q 
  exact (Eq.trans p5887 p5889)
theorem n9095 (_v : Vars) (_q : Query _v)  : (e9094 _v) := by
  have p5891 := n5891 _v _q 
  have p1382 := n1382 _v _q 
  exact (Eq.trans p5891 p1382)
theorem n9096 (_v : Vars) (_q : Query _v)  : (e5896 _v) := by
  have p5895 := n5895 _v _q 
  have p5897 := n5897 _v _q 
  exact (Eq.trans p5895 p5897)
theorem n9098 (_v : Vars) (_q : Query _v)  : (e9097 _v) := by
  have p5899 := n5899 _v _q 
  have p1392 := n1392 _v _q 
  exact (Eq.trans p5899 p1392)
theorem n9099 (_v : Vars) (_q : Query _v)  : (e5904 _v) := by
  have p5903 := n5903 _v _q 
  have p5905 := n5905 _v _q 
  exact (Eq.trans p5903 p5905)
theorem n9101 (_v : Vars) (_q : Query _v)  : (e9100 _v) := by
  have p5907 := n5907 _v _q 
  have p1402 := n1402 _v _q 
  exact (Eq.trans p5907 p1402)
theorem n9103 (_v : Vars) (_q : Query _v)  : (e9102 _v) := by
  have p5921 := n5921 _v _q 
  have p1413 := n1413 _v _q 
  exact (Eq.trans p5921 p1413)
theorem n9104 (_v : Vars) (_q : Query _v)  : (e5928 _v) := by
  have p5927 := n5927 _v _q 
  have p5929 := n5929 _v _q 
  exact (Eq.trans p5927 p5929)
theorem n9106 (_v : Vars) (_q : Query _v)  : (e9105 _v) := by
  have p5931 := n5931 _v _q 
  have p1426 := n1426 _v _q 
  exact (Eq.trans p5931 p1426)
theorem n9107 (_v : Vars) (_q : Query _v)  : (e5938 _v) := by
  have p5937 := n5937 _v _q 
  have p5939 := n5939 _v _q 
  exact (Eq.trans p5937 p5939)
theorem n9109 (_v : Vars) (_q : Query _v)  : (e9108 _v) := by
  have p5941 := n5941 _v _q 
  have p1436 := n1436 _v _q 
  exact (Eq.trans p5941 p1436)
theorem n9110 (_v : Vars) (_q : Query _v)  : (e5948 _v) := by
  have p5947 := n5947 _v _q 
  have p5949 := n5949 _v _q 
  exact (Eq.trans p5947 p5949)
theorem n9112 (_v : Vars) (_q : Query _v)  : (e9111 _v) := by
  have p5951 := n5951 _v _q 
  have p1446 := n1446 _v _q 
  exact (Eq.trans p5951 p1446)
theorem n9116 (_v : Vars) (_q : Query _v)  : (e9115 _v) := by
  simp only [e5, e9113, e9114, e9115] at *
  omega
theorem n9118 (_v : Vars) (_q : Query _v)  : (e9117 _v) := by
  have p5957 := n5957 _v _q 
  have p1457 := n1457 _v _q 
  exact (Eq.trans p5957 p1457)
theorem n9119 (_v : Vars) (_q : Query _v)  : (e5962 _v) := by
  have p5961 := n5961 _v _q 
  have p5963 := n5963 _v _q 
  exact (Eq.trans p5961 p5963)
theorem n9121 (_v : Vars) (_q : Query _v)  : (e9120 _v) := by
  have p5965 := n5965 _v _q 
  have p1470 := n1470 _v _q 
  exact (Eq.trans p5965 p1470)
theorem n9122 (_v : Vars) (_q : Query _v)  : (e5970 _v) := by
  have p5969 := n5969 _v _q 
  have p5971 := n5971 _v _q 
  exact (Eq.trans p5969 p5971)
theorem n9124 (_v : Vars) (_q : Query _v)  : (e9123 _v) := by
  have p5973 := n5973 _v _q 
  have p1480 := n1480 _v _q 
  exact (Eq.trans p5973 p1480)
theorem n9125 (_v : Vars) (_q : Query _v)  : (e5978 _v) := by
  have p5977 := n5977 _v _q 
  have p5979 := n5979 _v _q 
  exact (Eq.trans p5977 p5979)
theorem n9127 (_v : Vars) (_q : Query _v)  : (e9126 _v) := by
  have p5981 := n5981 _v _q 
  have p1490 := n1490 _v _q 
  exact (Eq.trans p5981 p1490)
end
end Assembly
