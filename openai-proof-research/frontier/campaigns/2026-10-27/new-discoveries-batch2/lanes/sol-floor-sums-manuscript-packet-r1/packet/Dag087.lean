import Dag086
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n13059 (_v : Vars) (_q : Query _v)  : (e13055 _v) := by
  have p13056 := n13056 _v _q 
  have p13058 := n13058 _v _q 
  exact (Iff.trans p13056 p13058)
theorem n13060 (_v : Vars) (_q : Query _v)  : (e8758 _v) := by
  have p8754 := n8754 _v _q 
  have p13059 := n13059 _v _q 
  change ((e5412 _v) ↔ (e8752 _v)) at p8754
  change ((e509 _v) ↔ (e5425 _v)) at p13059
  simp only [e8758, e5413, e8757, p8754, p13059]
theorem n13062 (_v : Vars) (_q : Query _v)  : (e13061 _v) := by
  exact ((((((((((((((((_q).2).2).2).2).2).2).2).2).2).2).2).2).2).2).2).2
theorem n13064 (_v : Vars) (_q : Query _v)  : (e13063 _v) := by
  have p11664 := n11664 _v _q 
  have p8868 := n8868 _v _q 
  exact (Eq.trans p11664 p8868)
theorem n13066 (_v : Vars) (_q : Query _v)  : (e13065 _v) := by
  simp only [e5, e6, e13065] at *
theorem n13068 (_v : Vars) (_q : Query _v)  : (e13067 _v) := by
  have p11669 := n11669 _v _q 
  have p8881 := n8881 _v _q 
  have p8889 := n8889 _v _q 
  have p8897 := n8897 _v _q 
  change ((e8763 _v) = (e5528 _v)) at p11669
  change ((e8764 _v) = (e5538 _v)) at p8881
  change ((e8765 _v) = (e5548 _v)) at p8889
  change ((e8766 _v) = (e5558 _v)) at p8897
  simp only [e13067, e8767, e11670, p11669, p8881, p8889, p8897]
theorem n13070 (_v : Vars) (_q : Query _v)  : (e13069 _v) := by
  have p13066 := n13066 _v _q 
  have p13068 := n13068 _v _q 
  change ((e6 _v) = (e6 _v)) at p13066
  change ((e8767 _v) = (e11670 _v)) at p13068
  simp only [e13069, e11644, e11671, p13068]
theorem n13072 (_v : Vars) (_q : Query _v)  : (e13071 _v) := by
  have p11678 := n11678 _v _q 
  have p8915 := n8915 _v _q 
  have p8923 := n8923 _v _q 
  have p8931 := n8931 _v _q 
  change ((e8768 _v) = (e5563 _v)) at p11678
  change ((e8769 _v) = (e5573 _v)) at p8915
  change ((e8770 _v) = (e5583 _v)) at p8923
  change ((e8771 _v) = (e5593 _v)) at p8931
  simp only [e13071, e8772, e11679, p11678, p8915, p8923, p8931]
theorem n13074 (_v : Vars) (_q : Query _v)  : (e13073 _v) := by
  have p13066 := n13066 _v _q 
  have p13072 := n13072 _v _q 
  change ((e6 _v) = (e6 _v)) at p13066
  change ((e8772 _v) = (e11679 _v)) at p13072
  simp only [e13073, e11645, e11680, p13072]
theorem n13075 (_v : Vars) (_q : Query _v)  : (e5596 _v) := by
  have p11684 := n11684 _v _q 
  change ((e573 _v) = (e964 _v)) at p11684
  simp only [e5596, e574, e1644, p11684]
theorem n13076 (_v : Vars) (_q : Query _v)  : (e5597 _v) := by
  have p11684 := n11684 _v _q 
  change ((e573 _v) = (e964 _v)) at p11684
  simp only [e5597, e575, e967, p11684]
theorem n13077 (_v : Vars) (_q : Query _v)  : (e970 _v) := by
  simp only [e5, e6, e12, e36, e964, e967, e968, e969, e970] at *
  omega
theorem n13078 (_v : Vars) (_q : Query _v)  : (e5598 _v) := by
  have p13076 := n13076 _v _q 
  have p13077 := n13077 _v _q 
  exact (Iff.trans p13076 p13077)
theorem n13080 (_v : Vars) (_q : Query _v)  : (e13079 _v) := by
  have p13078 := n13078 _v _q 
  have p11684 := n11684 _v _q 
  change ((e575 _v) ↔ (e969 _v)) at p13078
  change ((e573 _v) = (e964 _v)) at p11684
  simp only [e13079, e5438, e971, p13078, p11684]
theorem n13082 (_v : Vars) (_q : Query _v)  : (e13081 _v) := by
  have p13075 := n13075 _v _q 
  have p13080 := n13080 _v _q 
  change ((e574 _v) ↔ (e1644 _v)) at p13075
  change ((e5438 _v) = (e971 _v)) at p13080
  simp only [e13081, e8773, e5599, p13075, p13080]
theorem n13083 (_v : Vars) (_q : Query _v)  : (e5606 _v) := by
  have p11686 := n11686 _v _q 
  change ((e576 _v) = (e974 _v)) at p11686
  simp only [e5606, e577, e1651, p11686]
theorem n13084 (_v : Vars) (_q : Query _v)  : (e5607 _v) := by
  have p11686 := n11686 _v _q 
  change ((e576 _v) = (e974 _v)) at p11686
  simp only [e5607, e578, e977, p11686]
theorem n13085 (_v : Vars) (_q : Query _v)  : (e980 _v) := by
  simp only [e12, e43, e760, e761, e974, e977, e978, e979, e980] at *
  omega
theorem n13086 (_v : Vars) (_q : Query _v)  : (e5608 _v) := by
  have p13084 := n13084 _v _q 
  have p13085 := n13085 _v _q 
  exact (Iff.trans p13084 p13085)
theorem n13088 (_v : Vars) (_q : Query _v)  : (e13087 _v) := by
  have p13086 := n13086 _v _q 
  have p11686 := n11686 _v _q 
  change ((e578 _v) ↔ (e979 _v)) at p13086
  change ((e576 _v) = (e974 _v)) at p11686
  simp only [e13087, e5439, e981, p13086, p11686]
theorem n13090 (_v : Vars) (_q : Query _v)  : (e13089 _v) := by
  have p13083 := n13083 _v _q 
  have p13088 := n13088 _v _q 
  change ((e577 _v) ↔ (e1651 _v)) at p13083
  change ((e5439 _v) = (e981 _v)) at p13088
  simp only [e13089, e8774, e5609, p13083, p13088]
theorem n13091 (_v : Vars) (_q : Query _v)  : (e5616 _v) := by
  have p11688 := n11688 _v _q 
  change ((e579 _v) = (e984 _v)) at p11688
  simp only [e5616, e580, e1658, p11688]
theorem n13092 (_v : Vars) (_q : Query _v)  : (e5617 _v) := by
  have p11688 := n11688 _v _q 
  change ((e579 _v) = (e984 _v)) at p11688
  simp only [e5617, e581, e987, p11688]
theorem n13093 (_v : Vars) (_q : Query _v)  : (e990 _v) := by
  simp only [e12, e266, e781, e782, e984, e987, e988, e989, e990] at *
  omega
theorem n13094 (_v : Vars) (_q : Query _v)  : (e5618 _v) := by
  have p13092 := n13092 _v _q 
  have p13093 := n13093 _v _q 
  exact (Iff.trans p13092 p13093)
theorem n13096 (_v : Vars) (_q : Query _v)  : (e13095 _v) := by
  have p13094 := n13094 _v _q 
  have p11688 := n11688 _v _q 
  change ((e581 _v) ↔ (e989 _v)) at p13094
  change ((e579 _v) = (e984 _v)) at p11688
  simp only [e13095, e5440, e991, p13094, p11688]
theorem n13098 (_v : Vars) (_q : Query _v)  : (e13097 _v) := by
  have p13091 := n13091 _v _q 
  have p13096 := n13096 _v _q 
  change ((e580 _v) ↔ (e1658 _v)) at p13091
  change ((e5440 _v) = (e991 _v)) at p13096
  simp only [e13097, e8775, e5619, p13091, p13096]
theorem n13099 (_v : Vars) (_q : Query _v)  : (e5626 _v) := by
  have p11690 := n11690 _v _q 
  change ((e582 _v) = (e994 _v)) at p11690
  simp only [e5626, e583, e1665, p11690]
theorem n13100 (_v : Vars) (_q : Query _v)  : (e5627 _v) := by
  have p11690 := n11690 _v _q 
  change ((e582 _v) = (e994 _v)) at p11690
  simp only [e5627, e584, e997, p11690]
theorem n13101 (_v : Vars) (_q : Query _v)  : (e1000 _v) := by
  simp only [e12, e108, e802, e803, e994, e997, e998, e999, e1000] at *
  omega
theorem n13102 (_v : Vars) (_q : Query _v)  : (e5628 _v) := by
  have p13100 := n13100 _v _q 
  have p13101 := n13101 _v _q 
  exact (Iff.trans p13100 p13101)
theorem n13104 (_v : Vars) (_q : Query _v)  : (e13103 _v) := by
  have p13102 := n13102 _v _q 
  have p11690 := n11690 _v _q 
  change ((e584 _v) ↔ (e999 _v)) at p13102
  change ((e582 _v) = (e994 _v)) at p11690
  simp only [e13103, e5441, e1001, p13102, p11690]
theorem n13106 (_v : Vars) (_q : Query _v)  : (e13105 _v) := by
  have p13099 := n13099 _v _q 
  have p13104 := n13104 _v _q 
  change ((e583 _v) ↔ (e1665 _v)) at p13099
  change ((e5441 _v) = (e1001 _v)) at p13104
  simp only [e13105, e8776, e5629, p13099, p13104]
theorem n13108 (_v : Vars) (_q : Query _v)  : (e13107 _v) := by
  have p11695 := n11695 _v _q 
  have p8964 := n8964 _v _q 
  have p8972 := n8972 _v _q 
  have p8980 := n8980 _v _q 
  change ((e8778 _v) = (e5634 _v)) at p11695
  change ((e8779 _v) = (e5644 _v)) at p8964
  change ((e8780 _v) = (e5654 _v)) at p8972
  change ((e8781 _v) = (e5664 _v)) at p8980
  simp only [e13107, e8782, e11696, p11695, p8964, p8972, p8980]
theorem n13110 (_v : Vars) (_q : Query _v)  : (e13109 _v) := by
  have p13066 := n13066 _v _q 
  have p13108 := n13108 _v _q 
  change ((e6 _v) = (e6 _v)) at p13066
  change ((e8782 _v) = (e11696 _v)) at p13108
  simp only [e13109, e11647, e11697, p13108]
theorem n13111 (_v : Vars) (_q : Query _v)  : (e5667 _v) := by
  have p11701 := n11701 _v _q 
  change ((e600 _v) = (e1079 _v)) at p11701
  simp only [e5667, e601, e1700, p11701]
theorem n13112 (_v : Vars) (_q : Query _v)  : (e5668 _v) := by
  have p11701 := n11701 _v _q 
  change ((e600 _v) = (e1079 _v)) at p11701
  simp only [e5668, e602, e1082, p11701]
theorem n13113 (_v : Vars) (_q : Query _v)  : (e1085 _v) := by
  simp only [e5, e6, e12, e36, e1079, e1082, e1083, e1084, e1085] at *
  omega
theorem n13114 (_v : Vars) (_q : Query _v)  : (e5669 _v) := by
  have p13112 := n13112 _v _q 
  have p13113 := n13113 _v _q 
  exact (Iff.trans p13112 p13113)
theorem n13116 (_v : Vars) (_q : Query _v)  : (e13115 _v) := by
  have p13114 := n13114 _v _q 
  have p11701 := n11701 _v _q 
  change ((e602 _v) ↔ (e1084 _v)) at p13114
  change ((e600 _v) = (e1079 _v)) at p11701
  simp only [e13115, e5446, e1086, p13114, p11701]
theorem n13118 (_v : Vars) (_q : Query _v)  : (e13117 _v) := by
  have p13111 := n13111 _v _q 
  have p13116 := n13116 _v _q 
  change ((e601 _v) ↔ (e1700 _v)) at p13111
  change ((e5446 _v) = (e1086 _v)) at p13116
  simp only [e13117, e8783, e5670, p13111, p13116]
theorem n13119 (_v : Vars) (_q : Query _v)  : (e5677 _v) := by
  have p11703 := n11703 _v _q 
  change ((e603 _v) = (e1089 _v)) at p11703
  simp only [e5677, e604, e1707, p11703]
theorem n13120 (_v : Vars) (_q : Query _v)  : (e5678 _v) := by
  have p11703 := n11703 _v _q 
  change ((e603 _v) = (e1089 _v)) at p11703
  simp only [e5678, e605, e1092, p11703]
theorem n13121 (_v : Vars) (_q : Query _v)  : (e1095 _v) := by
  simp only [e12, e43, e760, e761, e1089, e1092, e1093, e1094, e1095] at *
  omega
theorem n13122 (_v : Vars) (_q : Query _v)  : (e5679 _v) := by
  have p13120 := n13120 _v _q 
  have p13121 := n13121 _v _q 
  exact (Iff.trans p13120 p13121)
end
end Assembly
