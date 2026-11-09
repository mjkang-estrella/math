import Dag060
import generated.th_lemma_1
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n10940 (_v : Vars) (_q : Query _v)  : (e10939 _v) := by
  have p7596 := n7596 _v _q 
  have p7599 := n7599 _v _q 
  exact (Iff.trans p7596 p7599)
theorem n10943 (_v : Vars) (_q : Query _v) (h6676 : (e6676 _v)) : (e6676 _v) := by
  exact h6676
theorem n10944 (_v : Vars) (_q : Query _v) (h2733 : (e2733 _v)) (h6676 : (e6676 _v)) : (e7489 _v) := by
  have p10943 := n10943 _v _q h6676
  have p5257 := n5257 _v _q 
  have p8587 := n8587 _v _q h2733
  have p5255 := n5255 _v _q 
  exact FloorCertificate.node_10944 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p10943 p5257 p8587 p5255
theorem n10946 (_v : Vars) (_q : Query _v)  : (e10945 _v) := by
  by_contra hc
  change ¬ ((e2585 _v) ∨ (¬ (e2733 _v))) at hc
  have h2733 : (e2733 _v) := by
    tauto
  have h6676 : (e6676 _v) := by
    change (¬ (e2585 _v))
    tauto
  have p10944 := n10944 _v _q h2733 h6676
  exact p10944
theorem n10948 (_v : Vars) (_q : Query _v)  : (e10947 _v) := by
  have p7615 := n7615 _v _q 
  have p7619 := n7619 _v _q 
  exact (Iff.trans p7615 p7619)
theorem n10950 (_v : Vars) (_q : Query _v)  : (e10949 _v) := by
  simp only [e5, e6, e10, e12, e41, e43, e44, e46, e111, e4119, e7606, e7607, e7608, e7609, e7610, e7627, e7630, e10949] at *
  omega
theorem n10957 (_v : Vars) (_q : Query _v)  : (e10956 _v) := by
  have p7639 := n7639 _v _q 
  have p7642 := n7642 _v _q 
  exact (Iff.trans p7639 p7642)
theorem n10959 (_v : Vars) (_q : Query _v)  : (e10958 _v) := by
  simp only [e5, e6, e8, e10, e12, e41, e111, e4154, e7645, e7648, e7652, e7655, e7656, e7657, e7658, e10958] at *
  omega
theorem n10966 (_v : Vars) (_q : Query _v)  : (e10965 _v) := by
  have p4165 := n4165 _v _q 
  have p7663 := n7663 _v _q 
  exact (Iff.trans p4165 p7663)
theorem n10968 (_v : Vars) (_q : Query _v)  : (e10967 _v) := by
  have p10966 := n10966 _v _q 
  change ((e4160 _v) ↔ (e4169 _v)) at p10966
  simp only [e10967, e6576, e7674, p10966]
theorem n10970 (_v : Vars) (_q : Query _v)  : (e10969 _v) := by
  have p7667 := n7667 _v _q 
  have p7670 := n7670 _v _q 
  exact (Iff.trans p7667 p7670)
theorem n10974 (_v : Vars) (_q : Query _v)  : (e10973 _v) := by
  have p7682 := n7682 _v _q 
  have p7685 := n7685 _v _q 
  exact (Iff.trans p7682 p7685)
theorem n10976 (_v : Vars) (_q : Query _v)  : (e10975 _v) := by
  simp only [e5, e6, e8, e10, e12, e41, e43, e44, e111, e4196, e7688, e7691, e7695, e7698, e7699, e7700, e7701, e10975] at *
  omega
theorem n10983 (_v : Vars) (_q : Query _v)  : (e10982 _v) := by
  have p7708 := n7708 _v _q 
  have p7711 := n7711 _v _q 
  exact (Iff.trans p7708 p7711)
theorem n10985 (_v : Vars) (_q : Query _v)  : (e10984 _v) := by
  simp only [e5, e6, e8, e10, e12, e41, e46, e4214, e7714, e7717, e7721, e7724, e7725, e7726, e7727, e10984] at *
  omega
theorem n10992 (_v : Vars) (_q : Query _v)  : (e10991 _v) := by
  have p7738 := n7738 _v _q 
  have p7741 := n7741 _v _q 
  exact (Iff.trans p7738 p7741)
theorem n10993 (_v : Vars) (_q : Query _v)  : (e7748 _v) := by
  simp only [e5, e6, e8, e12, e36, e41, e111, e2119, e4231, e4234, e7747, e7748] at *
  omega
theorem n10994 (_v : Vars) (_q : Query _v)  : (e7750 _v) := by
  simp only [e5, e6, e8, e12, e36, e41, e111, e2119, e4232, e4234, e7749, e7750] at *
  omega
theorem n10997 (_v : Vars) (_q : Query _v)  : (e10996 _v) := by
  have p10993 := n10993 _v _q 
  have p10994 := n10994 _v _q 
  change ((e4231 _v) ↔ (e7747 _v)) at p10993
  change ((e4232 _v) ↔ (e7749 _v)) at p10994
  simp only [e10996, e4233, e10995, p10993, p10994]
theorem n10999 (_v : Vars) (_q : Query _v)  : (e10998 _v) := by
  simp only [e5, e6, e8, e12, e41, e111, e4234, e7747, e7749, e7751, e7752, e7753, e7754, e10995, e10998] at *
  omega
theorem n11007 (_v : Vars) (_q : Query _v)  : (e11006 _v) := by
  have p7764 := n7764 _v _q 
  have p7768 := n7768 _v _q 
  exact (Iff.trans p7764 p7768)
theorem n11008 (_v : Vars) (_q : Query _v)  : (e7772 _v) := by
  simp only [e5, e6, e8, e12, e36, e41, e1989, e4235, e4236, e4253, e7772] at *
  omega
theorem n11009 (_v : Vars) (_q : Query _v)  : (e7773 _v) := by
  simp only [e5, e6, e8, e12, e36, e41, e1989, e4235, e4237, e4254, e7773] at *
  omega
theorem n11011 (_v : Vars) (_q : Query _v)  : (e11010 _v) := by
  have p11008 := n11008 _v _q 
  have p11009 := n11009 _v _q 
  change ((e4253 _v) ↔ (e4236 _v)) at p11008
  change ((e4254 _v) ↔ (e4237 _v)) at p11009
  simp only [e11010, e4255, e7774, p11008, p11009]
theorem n11012 (_v : Vars) (_q : Query _v)  : (e7776 _v) := by
  simp only [e5, e6, e8, e12, e41, e4235, e4236, e4237, e7756, e7757, e7758, e7774, e7775, e7776] at *
  omega
theorem n11013 (_v : Vars) (_q : Query _v)  : (e7777 _v) := by
  have p11011 := n11011 _v _q 
  have p11012 := n11012 _v _q 
  exact (Iff.trans p11011 p11012)
theorem n11020 (_v : Vars) (_q : Query _v)  : (e11019 _v) := by
  have p4267 := n4267 _v _q 
  have p7784 := n7784 _v _q 
  exact (Iff.trans p4267 p7784)
theorem n11022 (_v : Vars) (_q : Query _v)  : (e11021 _v) := by
  have p11020 := n11020 _v _q 
  change ((e4262 _v) ↔ (e4271 _v)) at p11020
  simp only [e11021, e6777, e7795, p11020]
theorem n11024 (_v : Vars) (_q : Query _v)  : (e11023 _v) := by
  have p7788 := n7788 _v _q 
  have p7791 := n7791 _v _q 
  exact (Iff.trans p7788 p7791)
theorem n11027 (_v : Vars) (_q : Query _v) (h6700 : (e6700 _v)) : (e6700 _v) := by
  exact h6700
theorem n11028 (_v : Vars) (_q : Query _v) (h2781 : (e2781 _v)) (h6700 : (e6700 _v)) : (e7489 _v) := by
  have p4016 := n4016 _v _q 
  have p11027 := n11027 _v _q h6700
  have p8421 := n8421 _v _q h2781
  have p5257 := n5257 _v _q 
  exact FloorCertificate.node_11028 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p4016 p11027 p8421 p5257
theorem n11030 (_v : Vars) (_q : Query _v)  : (e11029 _v) := by
  by_contra hc
  change ¬ ((e2634 _v) ∨ (¬ (e2781 _v))) at hc
  have h2781 : (e2781 _v) := by
    tauto
  have h6700 : (e6700 _v) := by
    change (¬ (e2634 _v))
    tauto
  have p11028 := n11028 _v _q h2781 h6700
  exact p11028
theorem n11031 (_v : Vars) (_q : Query _v) (h6636 : (e6636 _v)) : (e6636 _v) := by
  exact h6636
theorem n11032 (_v : Vars) (_q : Query _v) (h2634 : (e2634 _v)) : (e2634 _v) := by
  exact h2634
theorem n11033 (_v : Vars) (_q : Query _v) (h2634 : (e2634 _v)) (h6636 : (e6636 _v)) : (e7489 _v) := by
  have p5255 := n5255 _v _q 
  have p5257 := n5257 _v _q 
  have p11031 := n11031 _v _q h6636
  have p11032 := n11032 _v _q h2634
  exact FloorCertificate.node_11033 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p5255 p5257 p11031 p11032
theorem n11035 (_v : Vars) (_q : Query _v)  : (e11034 _v) := by
  by_contra hc
  change ¬ ((¬ (e2634 _v)) ∨ (e2482 _v)) at hc
  have h2634 : (e2634 _v) := by
    tauto
  have h6636 : (e6636 _v) := by
    change (¬ (e2482 _v))
    tauto
  have p11033 := n11033 _v _q h2634 h6636
  exact p11033
theorem n11037 (_v : Vars) (_q : Query _v)  : (e11036 _v) := by
  have p7803 := n7803 _v _q 
  have p7806 := n7806 _v _q 
  exact (Iff.trans p7803 p7806)
theorem n11038 (_v : Vars) (_q : Query _v)  : (e7813 _v) := by
  simp only [e5, e6, e10, e12, e36, e41, e111, e2290, e4296, e4299, e7812, e7813] at *
  omega
theorem n11039 (_v : Vars) (_q : Query _v)  : (e7815 _v) := by
  simp only [e5, e6, e10, e12, e36, e41, e111, e2290, e4297, e4299, e7814, e7815] at *
  omega
theorem n11042 (_v : Vars) (_q : Query _v)  : (e11041 _v) := by
  have p11038 := n11038 _v _q 
  have p11039 := n11039 _v _q 
  change ((e4296 _v) ↔ (e7812 _v)) at p11038
  change ((e4297 _v) ↔ (e7814 _v)) at p11039
  simp only [e11041, e4298, e11040, p11038, p11039]
theorem n11044 (_v : Vars) (_q : Query _v)  : (e11043 _v) := by
  simp only [e5, e6, e10, e12, e41, e111, e4299, e7812, e7814, e7816, e7817, e7818, e7819, e11040, e11043] at *
  omega
theorem n11052 (_v : Vars) (_q : Query _v)  : (e11051 _v) := by
  have p4310 := n4310 _v _q 
  have p7825 := n7825 _v _q 
  exact (Iff.trans p4310 p7825)
theorem n11054 (_v : Vars) (_q : Query _v)  : (e11053 _v) := by
  have p11052 := n11052 _v _q 
  change ((e4305 _v) ↔ (e4314 _v)) at p11052
  simp only [e11053, e6677, e7836, p11052]
theorem n11056 (_v : Vars) (_q : Query _v)  : (e11055 _v) := by
  have p7829 := n7829 _v _q 
  have p7832 := n7832 _v _q 
  exact (Iff.trans p7829 p7832)
theorem n11059 (_v : Vars) (_q : Query _v) (h2310 : (e2310 _v)) : (e2310 _v) := by
  exact h2310
end
end Assembly
