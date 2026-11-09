import Dag040
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n9209 (_v : Vars) (_q : Query _v)  : (e1631 _v) := by
  have p1629 := n1629 _v _q 
  change ((e931 _v) = (e931 _v)) at p1629
  simp only [e1631, e1630]
theorem n9210 (_v : Vars) (_q : Query _v)  : (e1634 _v) := by
  have p1633 := n1633 _v _q 
  change ((e937 _v) = (e937 _v)) at p1633
  simp only [e1634, e938]
theorem n9212 (_v : Vars) (_q : Query _v)  : (e9211 _v) := by
  have p9210 := n9210 _v _q 
  have p1629 := n1629 _v _q 
  change ((e938 _v) ↔ (e938 _v)) at p9210
  change ((e931 _v) = (e931 _v)) at p1629
  simp only [e9211, e940]
theorem n9214 (_v : Vars) (_q : Query _v)  : (e9213 _v) := by
  have p9209 := n9209 _v _q 
  have p9212 := n9212 _v _q 
  change ((e1630 _v) ↔ (e1630 _v)) at p9209
  change ((e940 _v) = (e940 _v)) at p9212
  simp only [e9213, e5583]
theorem n9216 (_v : Vars) (_q : Query _v)  : (e9215 _v) := by
  have p9214 := n9214 _v _q 
  change ((e5583 _v) = (e5583 _v)) at p9214
  simp only [e9215, e8934]
theorem n9217 (_v : Vars) (_q : Query _v)  : (e1638 _v) := by
  have p1636 := n1636 _v _q 
  change ((e948 _v) = (e948 _v)) at p1636
  simp only [e1638, e1637]
theorem n9218 (_v : Vars) (_q : Query _v)  : (e1641 _v) := by
  have p1640 := n1640 _v _q 
  change ((e954 _v) = (e954 _v)) at p1640
  simp only [e1641, e955]
theorem n9220 (_v : Vars) (_q : Query _v)  : (e9219 _v) := by
  have p9218 := n9218 _v _q 
  have p1636 := n1636 _v _q 
  change ((e955 _v) ↔ (e955 _v)) at p9218
  change ((e948 _v) = (e948 _v)) at p1636
  simp only [e9219, e957]
theorem n9222 (_v : Vars) (_q : Query _v)  : (e9221 _v) := by
  have p9217 := n9217 _v _q 
  have p9220 := n9220 _v _q 
  change ((e1637 _v) ↔ (e1637 _v)) at p9217
  change ((e957 _v) = (e957 _v)) at p9220
  simp only [e9221, e5593]
theorem n9224 (_v : Vars) (_q : Query _v)  : (e9223 _v) := by
  have p9222 := n9222 _v _q 
  change ((e5593 _v) = (e5593 _v)) at p9222
  simp only [e9223, e8935]
theorem n9225 (_v : Vars) (_q : Query _v)  : (e1673 _v) := by
  have p1671 := n1671 _v _q 
  change ((e1013 _v) = (e1013 _v)) at p1671
  simp only [e1673, e1672]
theorem n9226 (_v : Vars) (_q : Query _v)  : (e1676 _v) := by
  have p1675 := n1675 _v _q 
  change ((e1018 _v) = (e1018 _v)) at p1675
  simp only [e1676, e1019]
theorem n9228 (_v : Vars) (_q : Query _v)  : (e9227 _v) := by
  have p9226 := n9226 _v _q 
  have p1671 := n1671 _v _q 
  change ((e1019 _v) ↔ (e1019 _v)) at p9226
  change ((e1013 _v) = (e1013 _v)) at p1671
  simp only [e9227, e1021]
theorem n9230 (_v : Vars) (_q : Query _v)  : (e9229 _v) := by
  have p9225 := n9225 _v _q 
  have p9228 := n9228 _v _q 
  change ((e1672 _v) ↔ (e1672 _v)) at p9225
  change ((e1021 _v) = (e1021 _v)) at p9228
  simp only [e9229, e5634]
theorem n9232 (_v : Vars) (_q : Query _v)  : (e9231 _v) := by
  have p9230 := n9230 _v _q 
  change ((e5634 _v) = (e5634 _v)) at p9230
  simp only [e9231, e8981]
theorem n9233 (_v : Vars) (_q : Query _v)  : (e1680 _v) := by
  have p1678 := n1678 _v _q 
  change ((e1029 _v) = (e1029 _v)) at p1678
  simp only [e1680, e1679]
theorem n9234 (_v : Vars) (_q : Query _v)  : (e1683 _v) := by
  have p1682 := n1682 _v _q 
  change ((e1035 _v) = (e1035 _v)) at p1682
  simp only [e1683, e1036]
theorem n9236 (_v : Vars) (_q : Query _v)  : (e9235 _v) := by
  have p9234 := n9234 _v _q 
  have p1678 := n1678 _v _q 
  change ((e1036 _v) ↔ (e1036 _v)) at p9234
  change ((e1029 _v) = (e1029 _v)) at p1678
  simp only [e9235, e1038]
theorem n9238 (_v : Vars) (_q : Query _v)  : (e9237 _v) := by
  have p9233 := n9233 _v _q 
  have p9236 := n9236 _v _q 
  change ((e1679 _v) ↔ (e1679 _v)) at p9233
  change ((e1038 _v) = (e1038 _v)) at p9236
  simp only [e9237, e5644]
theorem n9240 (_v : Vars) (_q : Query _v)  : (e9239 _v) := by
  have p9238 := n9238 _v _q 
  change ((e5644 _v) = (e5644 _v)) at p9238
  simp only [e9239, e8982]
theorem n9241 (_v : Vars) (_q : Query _v)  : (e1687 _v) := by
  have p1685 := n1685 _v _q 
  change ((e1046 _v) = (e1046 _v)) at p1685
  simp only [e1687, e1686]
theorem n9242 (_v : Vars) (_q : Query _v)  : (e1690 _v) := by
  have p1689 := n1689 _v _q 
  change ((e1052 _v) = (e1052 _v)) at p1689
  simp only [e1690, e1053]
theorem n9244 (_v : Vars) (_q : Query _v)  : (e9243 _v) := by
  have p9242 := n9242 _v _q 
  have p1685 := n1685 _v _q 
  change ((e1053 _v) ↔ (e1053 _v)) at p9242
  change ((e1046 _v) = (e1046 _v)) at p1685
  simp only [e9243, e1055]
theorem n9246 (_v : Vars) (_q : Query _v)  : (e9245 _v) := by
  have p9241 := n9241 _v _q 
  have p9244 := n9244 _v _q 
  change ((e1686 _v) ↔ (e1686 _v)) at p9241
  change ((e1055 _v) = (e1055 _v)) at p9244
  simp only [e9245, e5654]
theorem n9248 (_v : Vars) (_q : Query _v)  : (e9247 _v) := by
  have p9246 := n9246 _v _q 
  change ((e5654 _v) = (e5654 _v)) at p9246
  simp only [e9247, e8983]
theorem n9249 (_v : Vars) (_q : Query _v)  : (e1694 _v) := by
  have p1692 := n1692 _v _q 
  change ((e1063 _v) = (e1063 _v)) at p1692
  simp only [e1694, e1693]
theorem n9250 (_v : Vars) (_q : Query _v)  : (e1697 _v) := by
  have p1696 := n1696 _v _q 
  change ((e1069 _v) = (e1069 _v)) at p1696
  simp only [e1697, e1070]
theorem n9252 (_v : Vars) (_q : Query _v)  : (e9251 _v) := by
  have p9250 := n9250 _v _q 
  have p1692 := n1692 _v _q 
  change ((e1070 _v) ↔ (e1070 _v)) at p9250
  change ((e1063 _v) = (e1063 _v)) at p1692
  simp only [e9251, e1072]
theorem n9254 (_v : Vars) (_q : Query _v)  : (e9253 _v) := by
  have p9249 := n9249 _v _q 
  have p9252 := n9252 _v _q 
  change ((e1693 _v) ↔ (e1693 _v)) at p9249
  change ((e1072 _v) = (e1072 _v)) at p9252
  simp only [e9253, e5664]
theorem n9256 (_v : Vars) (_q : Query _v)  : (e9255 _v) := by
  have p9254 := n9254 _v _q 
  change ((e5664 _v) = (e5664 _v)) at p9254
  simp only [e9255, e8984]
theorem n9257 (_v : Vars) (_q : Query _v)  : (e1777 _v) := by
  have p1775 := n1775 _v _q 
  change ((e1216 _v) = (e1216 _v)) at p1775
  simp only [e1777, e1776]
theorem n9258 (_v : Vars) (_q : Query _v)  : (e1780 _v) := by
  have p1779 := n1779 _v _q 
  change ((e1221 _v) = (e1221 _v)) at p1779
  simp only [e1780, e1222]
theorem n9260 (_v : Vars) (_q : Query _v)  : (e9259 _v) := by
  have p9258 := n9258 _v _q 
  have p1775 := n1775 _v _q 
  change ((e1222 _v) ↔ (e1222 _v)) at p9258
  change ((e1216 _v) = (e1216 _v)) at p1775
  simp only [e9259, e1224]
theorem n9262 (_v : Vars) (_q : Query _v)  : (e9261 _v) := by
  have p9257 := n9257 _v _q 
  have p9260 := n9260 _v _q 
  change ((e1776 _v) ↔ (e1776 _v)) at p9257
  change ((e1224 _v) = (e1224 _v)) at p9260
  simp only [e9261, e5779]
theorem n9264 (_v : Vars) (_q : Query _v)  : (e9263 _v) := by
  have p9262 := n9262 _v _q 
  change ((e5779 _v) = (e5779 _v)) at p9262
  simp only [e9263, e9056]
theorem n9265 (_v : Vars) (_q : Query _v)  : (e1784 _v) := by
  have p1782 := n1782 _v _q 
  change ((e1232 _v) = (e1232 _v)) at p1782
  simp only [e1784, e1783]
theorem n9266 (_v : Vars) (_q : Query _v)  : (e1787 _v) := by
  have p1786 := n1786 _v _q 
  change ((e1238 _v) = (e1238 _v)) at p1786
  simp only [e1787, e1239]
theorem n9268 (_v : Vars) (_q : Query _v)  : (e9267 _v) := by
  have p9266 := n9266 _v _q 
  have p1782 := n1782 _v _q 
  change ((e1239 _v) ↔ (e1239 _v)) at p9266
  change ((e1232 _v) = (e1232 _v)) at p1782
  simp only [e9267, e1241]
theorem n9270 (_v : Vars) (_q : Query _v)  : (e9269 _v) := by
  have p9265 := n9265 _v _q 
  have p9268 := n9268 _v _q 
  change ((e1783 _v) ↔ (e1783 _v)) at p9265
  change ((e1241 _v) = (e1241 _v)) at p9268
  simp only [e9269, e5789]
theorem n9272 (_v : Vars) (_q : Query _v)  : (e9271 _v) := by
  have p9270 := n9270 _v _q 
  change ((e5789 _v) = (e5789 _v)) at p9270
  simp only [e9271, e9057]
theorem n9273 (_v : Vars) (_q : Query _v)  : (e1791 _v) := by
  have p1789 := n1789 _v _q 
  change ((e1249 _v) = (e1249 _v)) at p1789
  simp only [e1791, e1790]
theorem n9274 (_v : Vars) (_q : Query _v)  : (e1794 _v) := by
  have p1793 := n1793 _v _q 
  change ((e1255 _v) = (e1255 _v)) at p1793
  simp only [e1794, e1256]
theorem n9276 (_v : Vars) (_q : Query _v)  : (e9275 _v) := by
  have p9274 := n9274 _v _q 
  have p1789 := n1789 _v _q 
  change ((e1256 _v) ↔ (e1256 _v)) at p9274
  change ((e1249 _v) = (e1249 _v)) at p1789
  simp only [e9275, e1258]
theorem n9278 (_v : Vars) (_q : Query _v)  : (e9277 _v) := by
  have p9273 := n9273 _v _q 
  have p9276 := n9276 _v _q 
  change ((e1790 _v) ↔ (e1790 _v)) at p9273
  change ((e1258 _v) = (e1258 _v)) at p9276
  simp only [e9277, e5799]
theorem n9280 (_v : Vars) (_q : Query _v)  : (e9279 _v) := by
  have p9278 := n9278 _v _q 
  change ((e5799 _v) = (e5799 _v)) at p9278
  simp only [e9279, e9058]
end
end Assembly
