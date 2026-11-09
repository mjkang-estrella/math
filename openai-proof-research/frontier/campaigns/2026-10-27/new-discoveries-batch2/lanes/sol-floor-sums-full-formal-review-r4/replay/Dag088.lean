import Dag087
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n13124 (_v : Vars) (_q : Query _v)  : (e13123 _v) := by
  have p13122 := n13122 _v _q 
  have p11703 := n11703 _v _q 
  change ((e605 _v) ↔ (e1094 _v)) at p13122
  change ((e603 _v) = (e1089 _v)) at p11703
  simp only [e13123, e5447, e1096, p13122, p11703]
theorem n13126 (_v : Vars) (_q : Query _v)  : (e13125 _v) := by
  have p13119 := n13119 _v _q 
  have p13124 := n13124 _v _q 
  change ((e604 _v) ↔ (e1707 _v)) at p13119
  change ((e5447 _v) = (e1096 _v)) at p13124
  simp only [e13125, e8784, e5680, p13119, p13124]
theorem n13127 (_v : Vars) (_q : Query _v)  : (e5687 _v) := by
  have p11705 := n11705 _v _q 
  change ((e606 _v) = (e1099 _v)) at p11705
  simp only [e5687, e607, e1714, p11705]
theorem n13128 (_v : Vars) (_q : Query _v)  : (e5688 _v) := by
  have p11705 := n11705 _v _q 
  change ((e606 _v) = (e1099 _v)) at p11705
  simp only [e5688, e608, e1102, p11705]
theorem n13129 (_v : Vars) (_q : Query _v)  : (e1105 _v) := by
  simp only [e12, e266, e781, e782, e1099, e1102, e1103, e1104, e1105] at *
  omega
theorem n13130 (_v : Vars) (_q : Query _v)  : (e5689 _v) := by
  have p13128 := n13128 _v _q 
  have p13129 := n13129 _v _q 
  exact (Iff.trans p13128 p13129)
theorem n13132 (_v : Vars) (_q : Query _v)  : (e13131 _v) := by
  have p13130 := n13130 _v _q 
  have p11705 := n11705 _v _q 
  change ((e608 _v) ↔ (e1104 _v)) at p13130
  change ((e606 _v) = (e1099 _v)) at p11705
  simp only [e13131, e5448, e1106, p13130, p11705]
theorem n13134 (_v : Vars) (_q : Query _v)  : (e13133 _v) := by
  have p13127 := n13127 _v _q 
  have p13132 := n13132 _v _q 
  change ((e607 _v) ↔ (e1714 _v)) at p13127
  change ((e5448 _v) = (e1106 _v)) at p13132
  simp only [e13133, e8785, e5690, p13127, p13132]
theorem n13135 (_v : Vars) (_q : Query _v)  : (e5697 _v) := by
  have p11707 := n11707 _v _q 
  change ((e609 _v) = (e1109 _v)) at p11707
  simp only [e5697, e610, e1721, p11707]
theorem n13136 (_v : Vars) (_q : Query _v)  : (e5698 _v) := by
  have p11707 := n11707 _v _q 
  change ((e609 _v) = (e1109 _v)) at p11707
  simp only [e5698, e611, e1112, p11707]
theorem n13137 (_v : Vars) (_q : Query _v)  : (e1115 _v) := by
  simp only [e12, e108, e802, e803, e1109, e1112, e1113, e1114, e1115] at *
  omega
theorem n13138 (_v : Vars) (_q : Query _v)  : (e5699 _v) := by
  have p13136 := n13136 _v _q 
  have p13137 := n13137 _v _q 
  exact (Iff.trans p13136 p13137)
theorem n13140 (_v : Vars) (_q : Query _v)  : (e13139 _v) := by
  have p13138 := n13138 _v _q 
  have p11707 := n11707 _v _q 
  change ((e611 _v) ↔ (e1114 _v)) at p13138
  change ((e609 _v) = (e1109 _v)) at p11707
  simp only [e13139, e5449, e1116, p13138, p11707]
theorem n13142 (_v : Vars) (_q : Query _v)  : (e13141 _v) := by
  have p13135 := n13135 _v _q 
  have p13140 := n13140 _v _q 
  change ((e610 _v) ↔ (e1721 _v)) at p13135
  change ((e5449 _v) = (e1116 _v)) at p13140
  simp only [e13141, e8786, e5700, p13135, p13140]
theorem n13143 (_v : Vars) (_q : Query _v)  : (e5703 _v) := by
  have p11709 := n11709 _v _q 
  change ((e613 _v) = (e1123 _v)) at p11709
  simp only [e5703, e614, e1728, p11709]
theorem n13144 (_v : Vars) (_q : Query _v)  : (e5704 _v) := by
  have p11709 := n11709 _v _q 
  change ((e613 _v) = (e1123 _v)) at p11709
  simp only [e5704, e615, e1126, p11709]
theorem n13145 (_v : Vars) (_q : Query _v)  : (e1129 _v) := by
  simp only [e5, e6, e12, e36, e1123, e1126, e1127, e1128, e1129] at *
  omega
theorem n13146 (_v : Vars) (_q : Query _v)  : (e5705 _v) := by
  have p13144 := n13144 _v _q 
  have p13145 := n13145 _v _q 
  exact (Iff.trans p13144 p13145)
theorem n13148 (_v : Vars) (_q : Query _v)  : (e13147 _v) := by
  have p13146 := n13146 _v _q 
  have p11709 := n11709 _v _q 
  change ((e615 _v) ↔ (e1128 _v)) at p13146
  change ((e613 _v) = (e1123 _v)) at p11709
  simp only [e13147, e5450, e1130, p13146, p11709]
theorem n13150 (_v : Vars) (_q : Query _v)  : (e13149 _v) := by
  have p13143 := n13143 _v _q 
  have p13148 := n13148 _v _q 
  change ((e614 _v) ↔ (e1728 _v)) at p13143
  change ((e5450 _v) = (e1130 _v)) at p13148
  simp only [e13149, e8788, e5706, p13143, p13148]
theorem n13151 (_v : Vars) (_q : Query _v)  : (e5713 _v) := by
  have p11711 := n11711 _v _q 
  change ((e616 _v) = (e1133 _v)) at p11711
  simp only [e5713, e617, e1735, p11711]
theorem n13152 (_v : Vars) (_q : Query _v)  : (e5714 _v) := by
  have p11711 := n11711 _v _q 
  change ((e616 _v) = (e1133 _v)) at p11711
  simp only [e5714, e618, e1136, p11711]
theorem n13153 (_v : Vars) (_q : Query _v)  : (e1139 _v) := by
  simp only [e12, e43, e760, e761, e1133, e1136, e1137, e1138, e1139] at *
  omega
theorem n13154 (_v : Vars) (_q : Query _v)  : (e5715 _v) := by
  have p13152 := n13152 _v _q 
  have p13153 := n13153 _v _q 
  exact (Iff.trans p13152 p13153)
theorem n13156 (_v : Vars) (_q : Query _v)  : (e13155 _v) := by
  have p13154 := n13154 _v _q 
  have p11711 := n11711 _v _q 
  change ((e618 _v) ↔ (e1138 _v)) at p13154
  change ((e616 _v) = (e1133 _v)) at p11711
  simp only [e13155, e5451, e1140, p13154, p11711]
theorem n13158 (_v : Vars) (_q : Query _v)  : (e13157 _v) := by
  have p13151 := n13151 _v _q 
  have p13156 := n13156 _v _q 
  change ((e617 _v) ↔ (e1735 _v)) at p13151
  change ((e5451 _v) = (e1140 _v)) at p13156
  simp only [e13157, e8789, e5716, p13151, p13156]
theorem n13159 (_v : Vars) (_q : Query _v)  : (e5723 _v) := by
  have p11713 := n11713 _v _q 
  change ((e619 _v) = (e1143 _v)) at p11713
  simp only [e5723, e620, e1742, p11713]
theorem n13160 (_v : Vars) (_q : Query _v)  : (e5724 _v) := by
  have p11713 := n11713 _v _q 
  change ((e619 _v) = (e1143 _v)) at p11713
  simp only [e5724, e621, e1146, p11713]
theorem n13161 (_v : Vars) (_q : Query _v)  : (e1149 _v) := by
  simp only [e12, e266, e781, e782, e1143, e1146, e1147, e1148, e1149] at *
  omega
theorem n13162 (_v : Vars) (_q : Query _v)  : (e5725 _v) := by
  have p13160 := n13160 _v _q 
  have p13161 := n13161 _v _q 
  exact (Iff.trans p13160 p13161)
theorem n13164 (_v : Vars) (_q : Query _v)  : (e13163 _v) := by
  have p13162 := n13162 _v _q 
  have p11713 := n11713 _v _q 
  change ((e621 _v) ↔ (e1148 _v)) at p13162
  change ((e619 _v) = (e1143 _v)) at p11713
  simp only [e13163, e5452, e1150, p13162, p11713]
theorem n13166 (_v : Vars) (_q : Query _v)  : (e13165 _v) := by
  have p13159 := n13159 _v _q 
  have p13164 := n13164 _v _q 
  change ((e620 _v) ↔ (e1742 _v)) at p13159
  change ((e5452 _v) = (e1150 _v)) at p13164
  simp only [e13165, e8790, e5726, p13159, p13164]
theorem n13167 (_v : Vars) (_q : Query _v)  : (e5733 _v) := by
  have p11715 := n11715 _v _q 
  change ((e622 _v) = (e1153 _v)) at p11715
  simp only [e5733, e623, e1749, p11715]
theorem n13168 (_v : Vars) (_q : Query _v)  : (e5734 _v) := by
  have p11715 := n11715 _v _q 
  change ((e622 _v) = (e1153 _v)) at p11715
  simp only [e5734, e624, e1156, p11715]
theorem n13169 (_v : Vars) (_q : Query _v)  : (e1159 _v) := by
  simp only [e12, e108, e802, e803, e1153, e1156, e1157, e1158, e1159] at *
  omega
theorem n13170 (_v : Vars) (_q : Query _v)  : (e5735 _v) := by
  have p13168 := n13168 _v _q 
  have p13169 := n13169 _v _q 
  exact (Iff.trans p13168 p13169)
theorem n13172 (_v : Vars) (_q : Query _v)  : (e13171 _v) := by
  have p13170 := n13170 _v _q 
  have p11715 := n11715 _v _q 
  change ((e624 _v) ↔ (e1158 _v)) at p13170
  change ((e622 _v) = (e1153 _v)) at p11715
  simp only [e13171, e5453, e1160, p13170, p11715]
theorem n13174 (_v : Vars) (_q : Query _v)  : (e13173 _v) := by
  have p13167 := n13167 _v _q 
  have p13172 := n13172 _v _q 
  change ((e623 _v) ↔ (e1749 _v)) at p13167
  change ((e5453 _v) = (e1160 _v)) at p13172
  simp only [e13173, e8791, e5736, p13167, p13172]
theorem n13176 (_v : Vars) (_q : Query _v)  : (e13175 _v) := by
  have p11717 := n11717 _v _q 
  change ((e626 _v) = (e1167 _v)) at p11717
  simp only [e13175, e628, e1171, p11717]
theorem n13177 (_v : Vars) (_q : Query _v)  : (e5739 _v) := by
  simp only [e5, e6, e12, e36, e1167, e1171, e1172, e1173, e5739] at *
  omega
theorem n13178 (_v : Vars) (_q : Query _v)  : (e5740 _v) := by
  have p13176 := n13176 _v _q 
  have p13177 := n13177 _v _q 
  exact (Iff.trans p13176 p13177)
theorem n13180 (_v : Vars) (_q : Query _v)  : (e13179 _v) := by
  have p13178 := n13178 _v _q 
  have p11717 := n11717 _v _q 
  change ((e628 _v) ↔ (e1173 _v)) at p13178
  change ((e626 _v) = (e1167 _v)) at p11717
  simp only [e13179, e5454, e1174, p13178, p11717]
theorem n13182 (_v : Vars) (_q : Query _v)  : (e13181 _v) := by
  have p11719 := n11719 _v _q 
  change ((e629 _v) = (e1177 _v)) at p11719
  simp only [e13181, e631, e1181, p11719]
theorem n13183 (_v : Vars) (_q : Query _v)  : (e5747 _v) := by
  simp only [e12, e43, e760, e761, e1177, e1181, e1182, e1183, e5747] at *
  omega
theorem n13184 (_v : Vars) (_q : Query _v)  : (e5748 _v) := by
  have p13182 := n13182 _v _q 
  have p13183 := n13183 _v _q 
  exact (Iff.trans p13182 p13183)
end
end Assembly
