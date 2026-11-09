import Dag051
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n9952 (_v : Vars) (_q : Query _v)  : (e6389 _v) := by
  have p9950 := n9950 _v _q 
  have p9951 := n9951 _v _q 
  exact (Iff.trans p9950 p9951)
theorem n9954 (_v : Vars) (_q : Query _v)  : (e9953 _v) := by
  have p9952 := n9952 _v _q 
  have p2730 := n2730 _v _q 
  change ((e1518 _v) ↔ (e2740 _v)) at p9952
  change ((e1512 _v) = (e2728 _v)) at p2730
  simp only [e9953, e1519, e6390, p9952, p2730]
theorem n9957 (_v : Vars) (_q : Query _v)  : (e9956 _v) := by
  have p9949 := n9949 _v _q 
  have p9954 := n9954 _v _q 
  change ((e1515 _v) ↔ (e2733 _v)) at p9949
  change ((e1519 _v) = (e6390 _v)) at p9954
  simp only [e9956, e6023, e9955, p9949, p9954]
theorem n9959 (_v : Vars) (_q : Query _v)  : (e9958 _v) := by
  have p2743 := n2743 _v _q 
  change ((e1522 _v) = (e2741 _v)) at p2743
  simp only [e9958, e1525, e2744, p2743]
theorem n9961 (_v : Vars) (_q : Query _v)  : (e9960 _v) := by
  simp only [e5, e6, e10, e12, e41, e46, e111, e266, e267, e781, e782, e2741, e2744, e2745, e2746, e9960] at *
  omega
theorem n9963 (_v : Vars) (_q : Query _v)  : (e9962 _v) := by
  have p9959 := n9959 _v _q 
  have p9961 := n9961 _v _q 
  exact (Iff.trans p9959 p9961)
theorem n9964 (_v : Vars) (_q : Query _v)  : (e2751 _v) := by
  have p2749 := n2749 _v _q 
  change ((e1527 _v) = (e2747 _v)) at p2749
  simp only [e2751, e1528, e2750, p2749]
theorem n9965 (_v : Vars) (_q : Query _v)  : (e6391 _v) := by
  simp only [e5, e6, e10, e12, e46, e111, e266, e267, e781, e782, e2747, e2750, e2752, e2753, e6391] at *
  omega
theorem n9966 (_v : Vars) (_q : Query _v)  : (e6392 _v) := by
  have p9964 := n9964 _v _q 
  have p9965 := n9965 _v _q 
  exact (Iff.trans p9964 p9965)
theorem n9968 (_v : Vars) (_q : Query _v)  : (e9967 _v) := by
  have p9966 := n9966 _v _q 
  have p2743 := n2743 _v _q 
  change ((e1528 _v) ↔ (e2753 _v)) at p9966
  change ((e1522 _v) = (e2741 _v)) at p2743
  simp only [e9967, e1529, e6393, p9966, p2743]
theorem n9971 (_v : Vars) (_q : Query _v)  : (e9970 _v) := by
  have p9963 := n9963 _v _q 
  have p9968 := n9968 _v _q 
  change ((e1525 _v) ↔ (e2746 _v)) at p9963
  change ((e1529 _v) = (e6393 _v)) at p9968
  simp only [e9970, e6024, e9969, p9963, p9968]
theorem n9973 (_v : Vars) (_q : Query _v)  : (e9972 _v) := by
  have p2756 := n2756 _v _q 
  change ((e1532 _v) = (e2754 _v)) at p2756
  simp only [e9972, e1535, e2757, p2756]
theorem n9975 (_v : Vars) (_q : Query _v)  : (e9974 _v) := by
  simp only [e5, e6, e10, e12, e41, e46, e108, e109, e111, e802, e803, e2754, e2757, e2758, e2759, e9974] at *
  omega
theorem n9977 (_v : Vars) (_q : Query _v)  : (e9976 _v) := by
  have p9973 := n9973 _v _q 
  have p9975 := n9975 _v _q 
  exact (Iff.trans p9973 p9975)
theorem n9978 (_v : Vars) (_q : Query _v)  : (e2764 _v) := by
  have p2762 := n2762 _v _q 
  change ((e1537 _v) = (e2760 _v)) at p2762
  simp only [e2764, e1538, e2763, p2762]
theorem n9979 (_v : Vars) (_q : Query _v)  : (e6394 _v) := by
  simp only [e5, e6, e10, e12, e46, e108, e109, e111, e802, e803, e2760, e2763, e2765, e2766, e6394] at *
  omega
theorem n9980 (_v : Vars) (_q : Query _v)  : (e6395 _v) := by
  have p9978 := n9978 _v _q 
  have p9979 := n9979 _v _q 
  exact (Iff.trans p9978 p9979)
theorem n9982 (_v : Vars) (_q : Query _v)  : (e9981 _v) := by
  have p9980 := n9980 _v _q 
  have p2756 := n2756 _v _q 
  change ((e1538 _v) ↔ (e2766 _v)) at p9980
  change ((e1532 _v) = (e2754 _v)) at p2756
  simp only [e9981, e1539, e6396, p9980, p2756]
theorem n9985 (_v : Vars) (_q : Query _v)  : (e9984 _v) := by
  have p9977 := n9977 _v _q 
  have p9982 := n9982 _v _q 
  change ((e1535 _v) ↔ (e2759 _v)) at p9977
  change ((e1539 _v) = (e6396 _v)) at p9982
  simp only [e9984, e6025, e9983, p9977, p9982]
theorem n9987 (_v : Vars) (_q : Query _v)  : (e9986 _v) := by
  have p2774 := n2774 _v _q 
  change ((e1546 _v) = (e2772 _v)) at p2774
  simp only [e9986, e1547, e2775, p2774]
theorem n9989 (_v : Vars) (_q : Query _v)  : (e9988 _v) := by
  simp only [e5, e6, e8, e10, e12, e36, e46, e111, e435, e436, e2772, e2775, e9988] at *
  omega
theorem n9991 (_v : Vars) (_q : Query _v)  : (e9990 _v) := by
  have p9987 := n9987 _v _q 
  have p9989 := n9989 _v _q 
  exact (Iff.trans p9987 p9989)
theorem n9993 (_v : Vars) (_q : Query _v)  : (e9992 _v) := by
  have p9991 := n9991 _v _q 
  have p2768 := n2768 _v _q 
  change ((e1547 _v) ↔ (e436 _v)) at p9991
  change ((e1543 _v) = (e444 _v)) at p2768
  simp only [e9992, e6039, e6397, p9991, p2768]
theorem n9995 (_v : Vars) (_q : Query _v)  : (e9994 _v) := by
  have p2784 := n2784 _v _q 
  change ((e1553 _v) = (e2782 _v)) at p2784
  simp only [e9994, e1554, e2785, p2784]
theorem n9997 (_v : Vars) (_q : Query _v)  : (e9996 _v) := by
  simp only [e5, e6, e8, e10, e12, e43, e44, e46, e111, e760, e761, e2782, e2785, e2786, e2787, e9996] at *
  omega
theorem n9999 (_v : Vars) (_q : Query _v)  : (e9998 _v) := by
  have p9995 := n9995 _v _q 
  have p9997 := n9997 _v _q 
  exact (Iff.trans p9995 p9997)
theorem n10001 (_v : Vars) (_q : Query _v)  : (e10000 _v) := by
  have p9999 := n9999 _v _q 
  have p2778 := n2778 _v _q 
  change ((e1554 _v) ↔ (e2787 _v)) at p9999
  change ((e1550 _v) = (e2776 _v)) at p2778
  simp only [e10000, e6042, e6398, p9999, p2778]
theorem n10003 (_v : Vars) (_q : Query _v)  : (e10002 _v) := by
  have p2796 := n2796 _v _q 
  change ((e1560 _v) = (e2794 _v)) at p2796
  simp only [e10002, e1561, e2797, p2796]
theorem n10005 (_v : Vars) (_q : Query _v)  : (e10004 _v) := by
  simp only [e5, e6, e8, e10, e12, e46, e111, e266, e267, e781, e782, e2794, e2797, e2798, e2799, e10004] at *
  omega
theorem n10007 (_v : Vars) (_q : Query _v)  : (e10006 _v) := by
  have p10003 := n10003 _v _q 
  have p10005 := n10005 _v _q 
  exact (Iff.trans p10003 p10005)
theorem n10009 (_v : Vars) (_q : Query _v)  : (e10008 _v) := by
  have p10007 := n10007 _v _q 
  have p2790 := n2790 _v _q 
  change ((e1561 _v) ↔ (e2799 _v)) at p10007
  change ((e1557 _v) = (e2788 _v)) at p2790
  simp only [e10008, e6045, e6399, p10007, p2790]
theorem n10011 (_v : Vars) (_q : Query _v)  : (e10010 _v) := by
  have p2808 := n2808 _v _q 
  change ((e1567 _v) = (e2806 _v)) at p2808
  simp only [e10010, e1568, e2809, p2808]
theorem n10013 (_v : Vars) (_q : Query _v)  : (e10012 _v) := by
  simp only [e5, e6, e8, e10, e12, e46, e108, e109, e111, e802, e803, e2806, e2809, e2810, e2811, e10012] at *
  omega
theorem n10015 (_v : Vars) (_q : Query _v)  : (e10014 _v) := by
  have p10011 := n10011 _v _q 
  have p10013 := n10013 _v _q 
  exact (Iff.trans p10011 p10013)
theorem n10017 (_v : Vars) (_q : Query _v)  : (e10016 _v) := by
  have p10015 := n10015 _v _q 
  have p2802 := n2802 _v _q 
  change ((e1568 _v) ↔ (e2811 _v)) at p10015
  change ((e1564 _v) = (e2800 _v)) at p2802
  simp only [e10016, e6048, e6400, p10015, p2802]
theorem n10056 (_v : Vars) (_q : Query _v)  : (e6404 _v) := by
  simp only [e749, e2812, e2813, e2814, e6401, e6402, e6403, e6404] at *
  by_cases hc : ((e2 _v) ≤ (e12 _v)) <;> simp [hc]
theorem n10059 (_v : Vars) (_q : Query _v)  : (e10058 _v) := by
  have p10056 := n10056 _v _q 
  simp only [e749, e1962, e2812, e2813, e2814, e6401, e6402, e6403, e6404, e10058] at *
theorem n10061 (_v : Vars) (_q : Query _v)  : (e10060 _v) := by
  have p10059 := n10059 _v _q 
  change ((e1962 _v) = (e2812 _v)) at p10059
  simp only [e10060, e6193, e2815, p10059]
theorem n10063 (_v : Vars) (_q : Query _v)  : (e10062 _v) := by
  have p6407 := n6407 _v _q 
  simp only [e151, e2812, e2815, e2816, e2817, e2818, e2819, e3032, e6405, e6406, e10062] at *
theorem n10065 (_v : Vars) (_q : Query _v)  : (e10064 _v) := by
  have p10061 := n10061 _v _q 
  have p10063 := n10063 _v _q 
  exact (Eq.trans p10061 p10063)
theorem n10066 (_v : Vars) (_q : Query _v)  : (e6410 _v) := by
  simp only [e507, e749, e2820, e2821, e6401, e6408, e6409, e6410] at *
  by_cases hc : ((e2 _v) ≤ (e12 _v)) <;> simp [hc]
theorem n10068 (_v : Vars) (_q : Query _v)  : (e10067 _v) := by
  have p10066 := n10066 _v _q 
  simp only [e507, e749, e1970, e2820, e2821, e6401, e6408, e6409, e6410, e10067] at *
theorem n10070 (_v : Vars) (_q : Query _v)  : (e10069 _v) := by
  have p10068 := n10068 _v _q 
  change ((e1970 _v) = (e507 _v)) at p10068
  simp only [e10069, e6194, e2822, p10068]
theorem n10072 (_v : Vars) (_q : Query _v)  : (e10071 _v) := by
  have p5414 := n5414 _v _q 
  simp only [e497, e505, e506, e507, e508, e509, e510, e2822, e5412, e5413, e10071] at *
theorem n10074 (_v : Vars) (_q : Query _v)  : (e10073 _v) := by
  have p10070 := n10070 _v _q 
  have p10072 := n10072 _v _q 
  exact (Eq.trans p10070 p10072)
end
end Assembly
