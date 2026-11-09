import Dag068
import generated.th_lemma_3
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n11635 (_v : Vars) (_q : Query _v)  : (e11634 _v) := by
  have p485 := n485 _v _q 
  have p8747 := n8747 _v _q 
  exact (Iff.trans p485 p8747)
theorem n11637 (_v : Vars) (_q : Query _v)  : (e11636 _v) := by
  have p519 := n519 _v _q 
  have p8756 := n8756 _v _q 
  exact (Iff.trans p519 p8756)
theorem n11639 (_v : Vars) (_q : Query _v)  : (e11638 _v) := by
  simp only [e5, e6, e12, e41, e43, e44, e498, e499, e500, e501, e502, e504, e505, e506, e514, e520, e521, e522, e524, e527, e528, e5421, e5422, e5425, e8752, e8757, e8759, e8760, e8761, e8762, e11638] at *
  omega
theorem n11641 (_v : Vars) (_q : Query _v)  : (e505 _v) := by
  have p8663 := n8663 _v _q 
  have p331 := n331 _v _q 
  exact FloorCertificate.node_11641 (e2 _v) (e17 _v) p8663 p331
theorem n11662 (_v : Vars) (_q : Query _v)  : (e11661 _v) := by
  have p8840 := n8840 _v _q 
  have p8848 := n8848 _v _q 
  have p8856 := n8856 _v _q 
  have p8864 := n8864 _v _q 
  change ((e5426 _v) = (e5505 _v)) at p8840
  change ((e5427 _v) = (e5511 _v)) at p8848
  change ((e5428 _v) = (e5517 _v)) at p8856
  change ((e5429 _v) = (e5523 _v)) at p8864
  simp only [e11661, e11642, e8865, p8840, p8848, p8856, p8864]
theorem n11664 (_v : Vars) (_q : Query _v)  : (e11663 _v) := by
  have p11662 := n11662 _v _q 
  change ((e11642 _v) = (e8865 _v)) at p11662
  simp only [e11663, e11643, e8866, p11662]
theorem n11665 (_v : Vars) (_q : Query _v)  : (e5525 _v) := by
  have p8870 := n8870 _v _q 
  change ((e546 _v) = (e827 _v)) at p8870
  simp only [e5525, e547, e1588, p8870]
theorem n11667 (_v : Vars) (_q : Query _v)  : (e11666 _v) := by
  have p8873 := n8873 _v _q 
  have p8870 := n8870 _v _q 
  change ((e548 _v) ↔ (e833 _v)) at p8873
  change ((e546 _v) = (e827 _v)) at p8870
  simp only [e11666, e5430, e835, p8873, p8870]
theorem n11669 (_v : Vars) (_q : Query _v)  : (e11668 _v) := by
  have p11665 := n11665 _v _q 
  have p11667 := n11667 _v _q 
  change ((e547 _v) ↔ (e1588 _v)) at p11665
  change ((e5430 _v) = (e835 _v)) at p11667
  simp only [e11668, e8763, e5528, p11665, p11667]
theorem n11673 (_v : Vars) (_q : Query _v)  : (e11672 _v) := by
  simp only [e5, e6, e8898, e8899, e8900, e8901, e8902, e11670, e11671, e11672] at *
  omega
theorem n11674 (_v : Vars) (_q : Query _v)  : (e5560 _v) := by
  have p8904 := n8904 _v _q 
  change ((e560 _v) = (e898 _v)) at p8904
  simp only [e5560, e561, e1616, p8904]
theorem n11676 (_v : Vars) (_q : Query _v)  : (e11675 _v) := by
  have p8907 := n8907 _v _q 
  have p8904 := n8904 _v _q 
  change ((e562 _v) ↔ (e904 _v)) at p8907
  change ((e560 _v) = (e898 _v)) at p8904
  simp only [e11675, e5434, e906, p8907, p8904]
theorem n11678 (_v : Vars) (_q : Query _v)  : (e11677 _v) := by
  have p11674 := n11674 _v _q 
  have p11676 := n11676 _v _q 
  change ((e561 _v) ↔ (e1616 _v)) at p11674
  change ((e5434 _v) = (e906 _v)) at p11676
  simp only [e11677, e8768, e5563, p11674, p11676]
theorem n11682 (_v : Vars) (_q : Query _v)  : (e11681 _v) := by
  simp only [e5, e6, e8932, e8933, e8934, e8935, e8936, e11679, e11680, e11681] at *
  omega
theorem n11684 (_v : Vars) (_q : Query _v)  : (e11683 _v) := by
  have p8938 := n8938 _v _q 
  have p966 := n966 _v _q 
  exact (Eq.trans p8938 p966)
theorem n11686 (_v : Vars) (_q : Query _v)  : (e11685 _v) := by
  have p8939 := n8939 _v _q 
  have p8941 := n8941 _v _q 
  exact (Eq.trans p8939 p8941)
theorem n11688 (_v : Vars) (_q : Query _v)  : (e11687 _v) := by
  have p8942 := n8942 _v _q 
  have p8944 := n8944 _v _q 
  exact (Eq.trans p8942 p8944)
theorem n11690 (_v : Vars) (_q : Query _v)  : (e11689 _v) := by
  have p8945 := n8945 _v _q 
  have p8947 := n8947 _v _q 
  exact (Eq.trans p8945 p8947)
theorem n11691 (_v : Vars) (_q : Query _v)  : (e5631 _v) := by
  have p8953 := n8953 _v _q 
  change ((e587 _v) = (e1013 _v)) at p8953
  simp only [e5631, e588, e1672, p8953]
theorem n11693 (_v : Vars) (_q : Query _v)  : (e11692 _v) := by
  have p8956 := n8956 _v _q 
  have p8953 := n8953 _v _q 
  change ((e589 _v) ↔ (e1019 _v)) at p8956
  change ((e587 _v) = (e1013 _v)) at p8953
  simp only [e11692, e5442, e1021, p8956, p8953]
theorem n11695 (_v : Vars) (_q : Query _v)  : (e11694 _v) := by
  have p11691 := n11691 _v _q 
  have p11693 := n11693 _v _q 
  change ((e588 _v) ↔ (e1672 _v)) at p11691
  change ((e5442 _v) = (e1021 _v)) at p11693
  simp only [e11694, e8778, e5634, p11691, p11693]
theorem n11699 (_v : Vars) (_q : Query _v)  : (e11698 _v) := by
  simp only [e5, e6, e8981, e8982, e8983, e8984, e8985, e11696, e11697, e11698] at *
  omega
theorem n11701 (_v : Vars) (_q : Query _v)  : (e11700 _v) := by
  have p8987 := n8987 _v _q 
  have p1081 := n1081 _v _q 
  exact (Eq.trans p8987 p1081)
theorem n11703 (_v : Vars) (_q : Query _v)  : (e11702 _v) := by
  have p8988 := n8988 _v _q 
  have p8990 := n8990 _v _q 
  exact (Eq.trans p8988 p8990)
theorem n11705 (_v : Vars) (_q : Query _v)  : (e11704 _v) := by
  have p8991 := n8991 _v _q 
  have p8993 := n8993 _v _q 
  exact (Eq.trans p8991 p8993)
theorem n11707 (_v : Vars) (_q : Query _v)  : (e11706 _v) := by
  have p8994 := n8994 _v _q 
  have p8996 := n8996 _v _q 
  exact (Eq.trans p8994 p8996)
theorem n11709 (_v : Vars) (_q : Query _v)  : (e11708 _v) := by
  have p9002 := n9002 _v _q 
  have p1125 := n1125 _v _q 
  exact (Eq.trans p9002 p1125)
theorem n11711 (_v : Vars) (_q : Query _v)  : (e11710 _v) := by
  have p9003 := n9003 _v _q 
  have p9005 := n9005 _v _q 
  exact (Eq.trans p9003 p9005)
theorem n11713 (_v : Vars) (_q : Query _v)  : (e11712 _v) := by
  have p9006 := n9006 _v _q 
  have p9008 := n9008 _v _q 
  exact (Eq.trans p9006 p9008)
theorem n11715 (_v : Vars) (_q : Query _v)  : (e11714 _v) := by
  have p9009 := n9009 _v _q 
  have p9011 := n9011 _v _q 
  exact (Eq.trans p9009 p9011)
theorem n11717 (_v : Vars) (_q : Query _v)  : (e11716 _v) := by
  have p9017 := n9017 _v _q 
  have p1169 := n1169 _v _q 
  exact (Eq.trans p9017 p1169)
theorem n11719 (_v : Vars) (_q : Query _v)  : (e11718 _v) := by
  have p9018 := n9018 _v _q 
  have p9020 := n9020 _v _q 
  exact (Eq.trans p9018 p9020)
theorem n11721 (_v : Vars) (_q : Query _v)  : (e11720 _v) := by
  have p9021 := n9021 _v _q 
  have p9023 := n9023 _v _q 
  exact (Eq.trans p9021 p9023)
theorem n11723 (_v : Vars) (_q : Query _v)  : (e11722 _v) := by
  have p9024 := n9024 _v _q 
  have p9026 := n9026 _v _q 
  exact (Eq.trans p9024 p9026)
theorem n11724 (_v : Vars) (_q : Query _v)  : (e5776 _v) := by
  have p9028 := n9028 _v _q 
  change ((e640 _v) = (e1216 _v)) at p9028
  simp only [e5776, e641, e1776, p9028]
theorem n11726 (_v : Vars) (_q : Query _v)  : (e11725 _v) := by
  have p9031 := n9031 _v _q 
  have p9028 := n9028 _v _q 
  change ((e642 _v) ↔ (e1222 _v)) at p9031
  change ((e640 _v) = (e1216 _v)) at p9028
  simp only [e11725, e5458, e1224, p9031, p9028]
theorem n11728 (_v : Vars) (_q : Query _v)  : (e11727 _v) := by
  have p11724 := n11724 _v _q 
  have p11726 := n11726 _v _q 
  change ((e641 _v) ↔ (e1776 _v)) at p11724
  change ((e5458 _v) = (e1224 _v)) at p11726
  simp only [e11727, e8798, e5779, p11724, p11726]
theorem n11732 (_v : Vars) (_q : Query _v)  : (e11731 _v) := by
  simp only [e5, e6, e9056, e9057, e9058, e9059, e9060, e11729, e11730, e11731] at *
  omega
theorem n11734 (_v : Vars) (_q : Query _v)  : (e11733 _v) := by
  have p9062 := n9062 _v _q 
  have p1284 := n1284 _v _q 
  exact (Eq.trans p9062 p1284)
theorem n11736 (_v : Vars) (_q : Query _v)  : (e11735 _v) := by
  have p9063 := n9063 _v _q 
  have p9065 := n9065 _v _q 
  exact (Eq.trans p9063 p9065)
theorem n11738 (_v : Vars) (_q : Query _v)  : (e11737 _v) := by
  have p9066 := n9066 _v _q 
  have p9068 := n9068 _v _q 
  exact (Eq.trans p9066 p9068)
theorem n11740 (_v : Vars) (_q : Query _v)  : (e11739 _v) := by
  have p9069 := n9069 _v _q 
  have p9071 := n9071 _v _q 
  exact (Eq.trans p9069 p9071)
theorem n11742 (_v : Vars) (_q : Query _v)  : (e11741 _v) := by
  have p9077 := n9077 _v _q 
  have p1328 := n1328 _v _q 
  exact (Eq.trans p9077 p1328)
theorem n11744 (_v : Vars) (_q : Query _v)  : (e11743 _v) := by
  have p9078 := n9078 _v _q 
  have p9080 := n9080 _v _q 
  exact (Eq.trans p9078 p9080)
theorem n11746 (_v : Vars) (_q : Query _v)  : (e11745 _v) := by
  have p9081 := n9081 _v _q 
  have p9083 := n9083 _v _q 
  exact (Eq.trans p9081 p9083)
end
end Assembly
