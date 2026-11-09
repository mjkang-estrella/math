import Dag070
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n11835 (_v : Vars) (_q : Query _v)  : (e1648 _v) := by
  have p1647 := n1647 _v _q 
  change ((e968 _v) = (e968 _v)) at p1647
  simp only [e1648, e969, p1647]
theorem n11837 (_v : Vars) (_q : Query _v)  : (e11836 _v) := by
  have p11835 := n11835 _v _q 
  have p1643 := n1643 _v _q 
  change ((e969 _v) ↔ (e969 _v)) at p11835
  change ((e964 _v) = (e964 _v)) at p1643
  simp only [e11836, e971, p11835, p1643]
theorem n11839 (_v : Vars) (_q : Query _v)  : (e11838 _v) := by
  have p11834 := n11834 _v _q 
  have p11837 := n11837 _v _q 
  change ((e1644 _v) ↔ (e1644 _v)) at p11834
  change ((e971 _v) = (e971 _v)) at p11837
  simp only [e11838, e5599, p11834, p11837]
theorem n11840 (_v : Vars) (_q : Query _v)  : (e1652 _v) := by
  have p1650 := n1650 _v _q 
  change ((e974 _v) = (e974 _v)) at p1650
  simp only [e1652, e1651, p1650]
theorem n11841 (_v : Vars) (_q : Query _v)  : (e1655 _v) := by
  have p1654 := n1654 _v _q 
  change ((e978 _v) = (e978 _v)) at p1654
  simp only [e1655, e979, p1654]
theorem n11843 (_v : Vars) (_q : Query _v)  : (e11842 _v) := by
  have p11841 := n11841 _v _q 
  have p1650 := n1650 _v _q 
  change ((e979 _v) ↔ (e979 _v)) at p11841
  change ((e974 _v) = (e974 _v)) at p1650
  simp only [e11842, e981, p11841, p1650]
theorem n11845 (_v : Vars) (_q : Query _v)  : (e11844 _v) := by
  have p11840 := n11840 _v _q 
  have p11843 := n11843 _v _q 
  change ((e1651 _v) ↔ (e1651 _v)) at p11840
  change ((e981 _v) = (e981 _v)) at p11843
  simp only [e11844, e5609, p11840, p11843]
theorem n11846 (_v : Vars) (_q : Query _v)  : (e1659 _v) := by
  have p1657 := n1657 _v _q 
  change ((e984 _v) = (e984 _v)) at p1657
  simp only [e1659, e1658, p1657]
theorem n11847 (_v : Vars) (_q : Query _v)  : (e1662 _v) := by
  have p1661 := n1661 _v _q 
  change ((e988 _v) = (e988 _v)) at p1661
  simp only [e1662, e989, p1661]
theorem n11849 (_v : Vars) (_q : Query _v)  : (e11848 _v) := by
  have p11847 := n11847 _v _q 
  have p1657 := n1657 _v _q 
  change ((e989 _v) ↔ (e989 _v)) at p11847
  change ((e984 _v) = (e984 _v)) at p1657
  simp only [e11848, e991, p11847, p1657]
theorem n11851 (_v : Vars) (_q : Query _v)  : (e11850 _v) := by
  have p11846 := n11846 _v _q 
  have p11849 := n11849 _v _q 
  change ((e1658 _v) ↔ (e1658 _v)) at p11846
  change ((e991 _v) = (e991 _v)) at p11849
  simp only [e11850, e5619, p11846, p11849]
theorem n11852 (_v : Vars) (_q : Query _v)  : (e1666 _v) := by
  have p1664 := n1664 _v _q 
  change ((e994 _v) = (e994 _v)) at p1664
  simp only [e1666, e1665, p1664]
theorem n11853 (_v : Vars) (_q : Query _v)  : (e1669 _v) := by
  have p1668 := n1668 _v _q 
  change ((e998 _v) = (e998 _v)) at p1668
  simp only [e1669, e999, p1668]
theorem n11855 (_v : Vars) (_q : Query _v)  : (e11854 _v) := by
  have p11853 := n11853 _v _q 
  have p1664 := n1664 _v _q 
  change ((e999 _v) ↔ (e999 _v)) at p11853
  change ((e994 _v) = (e994 _v)) at p1664
  simp only [e11854, e1001, p11853, p1664]
theorem n11857 (_v : Vars) (_q : Query _v)  : (e11856 _v) := by
  have p11852 := n11852 _v _q 
  have p11855 := n11855 _v _q 
  change ((e1665 _v) ↔ (e1665 _v)) at p11852
  change ((e1001 _v) = (e1001 _v)) at p11855
  simp only [e11856, e5629, p11852, p11855]
theorem n11858 (_v : Vars) (_q : Query _v)  : (e1701 _v) := by
  have p1699 := n1699 _v _q 
  change ((e1079 _v) = (e1079 _v)) at p1699
  simp only [e1701, e1700, p1699]
theorem n11859 (_v : Vars) (_q : Query _v)  : (e1704 _v) := by
  have p1703 := n1703 _v _q 
  change ((e1083 _v) = (e1083 _v)) at p1703
  simp only [e1704, e1084, p1703]
theorem n11861 (_v : Vars) (_q : Query _v)  : (e11860 _v) := by
  have p11859 := n11859 _v _q 
  have p1699 := n1699 _v _q 
  change ((e1084 _v) ↔ (e1084 _v)) at p11859
  change ((e1079 _v) = (e1079 _v)) at p1699
  simp only [e11860, e1086, p11859, p1699]
theorem n11863 (_v : Vars) (_q : Query _v)  : (e11862 _v) := by
  have p11858 := n11858 _v _q 
  have p11861 := n11861 _v _q 
  change ((e1700 _v) ↔ (e1700 _v)) at p11858
  change ((e1086 _v) = (e1086 _v)) at p11861
  simp only [e11862, e5670, p11858, p11861]
theorem n11864 (_v : Vars) (_q : Query _v)  : (e1708 _v) := by
  have p1706 := n1706 _v _q 
  change ((e1089 _v) = (e1089 _v)) at p1706
  simp only [e1708, e1707, p1706]
theorem n11865 (_v : Vars) (_q : Query _v)  : (e1711 _v) := by
  have p1710 := n1710 _v _q 
  change ((e1093 _v) = (e1093 _v)) at p1710
  simp only [e1711, e1094, p1710]
theorem n11867 (_v : Vars) (_q : Query _v)  : (e11866 _v) := by
  have p11865 := n11865 _v _q 
  have p1706 := n1706 _v _q 
  change ((e1094 _v) ↔ (e1094 _v)) at p11865
  change ((e1089 _v) = (e1089 _v)) at p1706
  simp only [e11866, e1096, p11865, p1706]
theorem n11869 (_v : Vars) (_q : Query _v)  : (e11868 _v) := by
  have p11864 := n11864 _v _q 
  have p11867 := n11867 _v _q 
  change ((e1707 _v) ↔ (e1707 _v)) at p11864
  change ((e1096 _v) = (e1096 _v)) at p11867
  simp only [e11868, e5680, p11864, p11867]
theorem n11870 (_v : Vars) (_q : Query _v)  : (e1715 _v) := by
  have p1713 := n1713 _v _q 
  change ((e1099 _v) = (e1099 _v)) at p1713
  simp only [e1715, e1714, p1713]
theorem n11871 (_v : Vars) (_q : Query _v)  : (e1718 _v) := by
  have p1717 := n1717 _v _q 
  change ((e1103 _v) = (e1103 _v)) at p1717
  simp only [e1718, e1104, p1717]
theorem n11873 (_v : Vars) (_q : Query _v)  : (e11872 _v) := by
  have p11871 := n11871 _v _q 
  have p1713 := n1713 _v _q 
  change ((e1104 _v) ↔ (e1104 _v)) at p11871
  change ((e1099 _v) = (e1099 _v)) at p1713
  simp only [e11872, e1106, p11871, p1713]
theorem n11875 (_v : Vars) (_q : Query _v)  : (e11874 _v) := by
  have p11870 := n11870 _v _q 
  have p11873 := n11873 _v _q 
  change ((e1714 _v) ↔ (e1714 _v)) at p11870
  change ((e1106 _v) = (e1106 _v)) at p11873
  simp only [e11874, e5690, p11870, p11873]
theorem n11876 (_v : Vars) (_q : Query _v)  : (e1722 _v) := by
  have p1720 := n1720 _v _q 
  change ((e1109 _v) = (e1109 _v)) at p1720
  simp only [e1722, e1721, p1720]
theorem n11877 (_v : Vars) (_q : Query _v)  : (e1725 _v) := by
  have p1724 := n1724 _v _q 
  change ((e1113 _v) = (e1113 _v)) at p1724
  simp only [e1725, e1114, p1724]
theorem n11879 (_v : Vars) (_q : Query _v)  : (e11878 _v) := by
  have p11877 := n11877 _v _q 
  have p1720 := n1720 _v _q 
  change ((e1114 _v) ↔ (e1114 _v)) at p11877
  change ((e1109 _v) = (e1109 _v)) at p1720
  simp only [e11878, e1116, p11877, p1720]
theorem n11881 (_v : Vars) (_q : Query _v)  : (e11880 _v) := by
  have p11876 := n11876 _v _q 
  have p11879 := n11879 _v _q 
  change ((e1721 _v) ↔ (e1721 _v)) at p11876
  change ((e1116 _v) = (e1116 _v)) at p11879
  simp only [e11880, e5700, p11876, p11879]
theorem n11882 (_v : Vars) (_q : Query _v)  : (e1729 _v) := by
  have p1727 := n1727 _v _q 
  change ((e1123 _v) = (e1123 _v)) at p1727
  simp only [e1729, e1728, p1727]
theorem n11883 (_v : Vars) (_q : Query _v)  : (e1732 _v) := by
  have p1731 := n1731 _v _q 
  change ((e1127 _v) = (e1127 _v)) at p1731
  simp only [e1732, e1128, p1731]
theorem n11885 (_v : Vars) (_q : Query _v)  : (e11884 _v) := by
  have p11883 := n11883 _v _q 
  have p1727 := n1727 _v _q 
  change ((e1128 _v) ↔ (e1128 _v)) at p11883
  change ((e1123 _v) = (e1123 _v)) at p1727
  simp only [e11884, e1130, p11883, p1727]
theorem n11887 (_v : Vars) (_q : Query _v)  : (e11886 _v) := by
  have p11882 := n11882 _v _q 
  have p11885 := n11885 _v _q 
  change ((e1728 _v) ↔ (e1728 _v)) at p11882
  change ((e1130 _v) = (e1130 _v)) at p11885
  simp only [e11886, e5706, p11882, p11885]
theorem n11888 (_v : Vars) (_q : Query _v)  : (e1736 _v) := by
  have p1734 := n1734 _v _q 
  change ((e1133 _v) = (e1133 _v)) at p1734
  simp only [e1736, e1735, p1734]
theorem n11889 (_v : Vars) (_q : Query _v)  : (e1739 _v) := by
  have p1738 := n1738 _v _q 
  change ((e1137 _v) = (e1137 _v)) at p1738
  simp only [e1739, e1138, p1738]
theorem n11891 (_v : Vars) (_q : Query _v)  : (e11890 _v) := by
  have p11889 := n11889 _v _q 
  have p1734 := n1734 _v _q 
  change ((e1138 _v) ↔ (e1138 _v)) at p11889
  change ((e1133 _v) = (e1133 _v)) at p1734
  simp only [e11890, e1140, p11889, p1734]
theorem n11893 (_v : Vars) (_q : Query _v)  : (e11892 _v) := by
  have p11888 := n11888 _v _q 
  have p11891 := n11891 _v _q 
  change ((e1735 _v) ↔ (e1735 _v)) at p11888
  change ((e1140 _v) = (e1140 _v)) at p11891
  simp only [e11892, e5716, p11888, p11891]
theorem n11894 (_v : Vars) (_q : Query _v)  : (e1743 _v) := by
  have p1741 := n1741 _v _q 
  change ((e1143 _v) = (e1143 _v)) at p1741
  simp only [e1743, e1742, p1741]
theorem n11895 (_v : Vars) (_q : Query _v)  : (e1746 _v) := by
  have p1745 := n1745 _v _q 
  change ((e1147 _v) = (e1147 _v)) at p1745
  simp only [e1746, e1148, p1745]
theorem n11897 (_v : Vars) (_q : Query _v)  : (e11896 _v) := by
  have p11895 := n11895 _v _q 
  have p1741 := n1741 _v _q 
  change ((e1148 _v) ↔ (e1148 _v)) at p11895
  change ((e1143 _v) = (e1143 _v)) at p1741
  simp only [e11896, e1150, p11895, p1741]
theorem n11899 (_v : Vars) (_q : Query _v)  : (e11898 _v) := by
  have p11894 := n11894 _v _q 
  have p11897 := n11897 _v _q 
  change ((e1742 _v) ↔ (e1742 _v)) at p11894
  change ((e1150 _v) = (e1150 _v)) at p11897
  simp only [e11898, e5726, p11894, p11897]
theorem n11900 (_v : Vars) (_q : Query _v)  : (e1750 _v) := by
  have p1748 := n1748 _v _q 
  change ((e1153 _v) = (e1153 _v)) at p1748
  simp only [e1750, e1749, p1748]
theorem n11901 (_v : Vars) (_q : Query _v)  : (e1753 _v) := by
  have p1752 := n1752 _v _q 
  change ((e1157 _v) = (e1157 _v)) at p1752
  simp only [e1753, e1158, p1752]
end
end Assembly
