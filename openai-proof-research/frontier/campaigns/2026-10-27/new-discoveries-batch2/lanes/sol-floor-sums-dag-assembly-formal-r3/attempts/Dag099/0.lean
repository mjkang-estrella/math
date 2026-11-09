import Dag098
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n13895 (_v : Vars) (_q : Query _v)  : (e7899 _v) := by
  have p12672 := n12672 _v _q 
  change ((e4381 _v) ↔ (e7895 _v)) at p12672
  simp only [e7899, e6696, e7898, p12672]
theorem n13896 (_v : Vars) (_q : Query _v)  : (e7900 _v) := by
  simp only [e5, e6, e10, e12, e41, e46, e250, e251, e4365, e4366, e4367, e4368, e4369, e4370, e7887, e7895, e7898, e7900] at *
  omega
theorem n13897 (_v : Vars) (_q : Query _v)  : (e7899 _v) := by
  have p13895 := n13895 _v _q 
  have p13896 := n13896 _v _q 
  exact (Iff.trans p13895 p13896)
theorem n13899 (_v : Vars) (_q : Query _v)  : (e13898 _v) := by
  have p11094 := n11094 _v _q 
  have p13897 := n13897 _v _q 
  change ((e6695 _v) ↔ (e7901 _v)) at p11094
  change ((e6696 _v) ↔ (e7898 _v)) at p13897
  simp only [e13898, e6697, e7902, p11094, p13897]
theorem n13902 (_v : Vars) (_q : Query _v)  : (e13901 _v) := by
  simp only [e5, e6, e10, e12, e41, e46, e250, e251, e4365, e4366, e4367, e4368, e4369, e4370, e4372, e4373, e4377, e4378, e4379, e4380, e6694, e7887, e7895, e7898, e7901, e7902, e7903, e11097, e11098, e13900, e13901] at *
  omega
theorem n13904 (_v : Vars) (_q : Query _v)  : (e13903 _v) := by
  have p13899 := n13899 _v _q 
  have p13902 := n13902 _v _q 
  exact (Iff.trans p13899 p13902)
theorem n13905 (_v : Vars) (_q : Query _v)  : (e7916 _v) := by
  have p12674 := n12674 _v _q 
  change ((e4406 _v) ↔ (e7912 _v)) at p12674
  simp only [e7916, e6638, e7915, p12674]
theorem n13906 (_v : Vars) (_q : Query _v)  : (e7917 _v) := by
  simp only [e5, e6, e8, e12, e41, e43, e44, e46, e2481, e2482, e4390, e4391, e4392, e4393, e4394, e4395, e7904, e7912, e7915, e7917] at *
  omega
theorem n13907 (_v : Vars) (_q : Query _v)  : (e7916 _v) := by
  have p13905 := n13905 _v _q 
  have p13906 := n13906 _v _q 
  exact (Iff.trans p13905 p13906)
theorem n13909 (_v : Vars) (_q : Query _v)  : (e13908 _v) := by
  have p11102 := n11102 _v _q 
  have p13907 := n13907 _v _q 
  change ((e6637 _v) ↔ (e7918 _v)) at p11102
  change ((e6638 _v) ↔ (e7915 _v)) at p13907
  simp only [e13908, e6639, e7919, p11102, p13907]
theorem n13912 (_v : Vars) (_q : Query _v)  : (e13911 _v) := by
  simp only [e5, e6, e8, e12, e41, e43, e44, e46, e2481, e2482, e4390, e4391, e4392, e4393, e4394, e4395, e4397, e4398, e4402, e4403, e4404, e4405, e6636, e7904, e7912, e7915, e7918, e7919, e7920, e11105, e11106, e13910, e13911] at *
  omega
theorem n13914 (_v : Vars) (_q : Query _v)  : (e13913 _v) := by
  have p13909 := n13909 _v _q 
  have p13912 := n13912 _v _q 
  exact (Iff.trans p13909 p13912)
theorem n13916 (_v : Vars) (_q : Query _v)  : (e13915 _v) := by
  have p12682 := n12682 _v _q 
  change ((e2912 _v) ↔ (e7945 _v)) at p12682
  simp only [e13915, e6774, e11111, p12682]
theorem n13918 (_v : Vars) (_q : Query _v)  : (e13917 _v) := by
  simp only [e5, e6, e8, e10, e12, e41, e43, e44, e46, e111, e2786, e2787, e4432, e7932, e7935, e7942, e7943, e7944, e7945, e11111, e13917] at *
  omega
theorem n13919 (_v : Vars) (_q : Query _v)  : (e13915 _v) := by
  have p13916 := n13916 _v _q 
  have p13918 := n13918 _v _q 
  exact (Iff.trans p13916 p13918)
theorem n13920 (_v : Vars) (_q : Query _v)  : (e7959 _v) := by
  have p12684 := n12684 _v _q 
  change ((e4448 _v) ↔ (e7955 _v)) at p12684
  simp only [e7959, e6456, e7958, p12684]
theorem n13921 (_v : Vars) (_q : Query _v)  : (e7960 _v) := by
  simp only [e5, e6, e12, e41, e111, e2060, e2061, e2927, e4433, e4434, e4435, e4436, e4437, e7947, e7955, e7958, e7960] at *
  omega
theorem n13922 (_v : Vars) (_q : Query _v)  : (e7959 _v) := by
  have p13920 := n13920 _v _q 
  have p13921 := n13921 _v _q 
  exact (Iff.trans p13920 p13921)
theorem n13924 (_v : Vars) (_q : Query _v)  : (e13923 _v) := by
  have p11119 := n11119 _v _q 
  have p13922 := n13922 _v _q 
  change ((e6455 _v) ↔ (e7961 _v)) at p11119
  change ((e6456 _v) ↔ (e7958 _v)) at p13922
  simp only [e13923, e6457, e7962, p11119, p13922]
theorem n13927 (_v : Vars) (_q : Query _v)  : (e13926 _v) := by
  simp only [e5, e6, e12, e41, e111, e2060, e2061, e2927, e4433, e4434, e4435, e4436, e4437, e4439, e4440, e4444, e4445, e4446, e4447, e6454, e7947, e7955, e7958, e7961, e7962, e7963, e11122, e11123, e13925, e13926] at *
  omega
theorem n13929 (_v : Vars) (_q : Query _v)  : (e13928 _v) := by
  have p13924 := n13924 _v _q 
  have p13927 := n13927 _v _q 
  exact (Iff.trans p13924 p13927)
theorem n13930 (_v : Vars) (_q : Query _v)  : (e7975 _v) := by
  have p12686 := n12686 _v _q 
  change ((e4467 _v) ↔ (e7971 _v)) at p12686
  simp only [e7975, e6482, e7974, p12686]
theorem n13931 (_v : Vars) (_q : Query _v)  : (e7976 _v) := by
  simp only [e5, e6, e8, e12, e41, e111, e2124, e2125, e4473, e4474, e4475, e4477, e4480, e4481, e7970, e7971, e7974, e7976] at *
  omega
theorem n13932 (_v : Vars) (_q : Query _v)  : (e7975 _v) := by
  have p13930 := n13930 _v _q 
  have p13931 := n13931 _v _q 
  exact (Iff.trans p13930 p13931)
theorem n13934 (_v : Vars) (_q : Query _v)  : (e13933 _v) := by
  have p11127 := n11127 _v _q 
  have p13932 := n13932 _v _q 
  change ((e6481 _v) ↔ (e7977 _v)) at p11127
  change ((e6482 _v) ↔ (e7974 _v)) at p13932
  simp only [e13933, e6483, e7978, p11127, p13932]
theorem n13937 (_v : Vars) (_q : Query _v)  : (e13936 _v) := by
  simp only [e5, e6, e8, e12, e41, e111, e2124, e2125, e4458, e4459, e4463, e4464, e4465, e4466, e4473, e4474, e4475, e4477, e4480, e4481, e6480, e7970, e7971, e7974, e7977, e7978, e7979, e11130, e11131, e13935, e13936] at *
  omega
theorem n13939 (_v : Vars) (_q : Query _v)  : (e13938 _v) := by
  have p13934 := n13934 _v _q 
  have p13937 := n13937 _v _q 
  exact (Iff.trans p13934 p13937)
theorem n13940 (_v : Vars) (_q : Query _v)  : (e7996 _v) := by
  have p12691 := n12691 _v _q 
  change ((e4500 _v) ↔ (e7992 _v)) at p12691
  simp only [e7996, e6734, e7995, p12691]
theorem n13941 (_v : Vars) (_q : Query _v)  : (e7997 _v) := by
  simp only [e5, e6, e8, e10, e12, e41, e46, e266, e267, e2696, e2697, e2983, e4485, e4486, e4487, e4488, e4489, e7984, e7992, e7995, e7997] at *
  omega
theorem n13942 (_v : Vars) (_q : Query _v)  : (e7996 _v) := by
  have p13940 := n13940 _v _q 
  have p13941 := n13941 _v _q 
  exact (Iff.trans p13940 p13941)
theorem n13944 (_v : Vars) (_q : Query _v)  : (e13943 _v) := by
  have p11139 := n11139 _v _q 
  have p13942 := n13942 _v _q 
  change ((e6733 _v) ↔ (e7998 _v)) at p11139
  change ((e6734 _v) ↔ (e7995 _v)) at p13942
  simp only [e13943, e6735, e7999, p11139, p13942]
theorem n13947 (_v : Vars) (_q : Query _v)  : (e13946 _v) := by
  simp only [e5, e6, e8, e10, e12, e41, e46, e266, e267, e2696, e2697, e2983, e4485, e4486, e4487, e4488, e4489, e4491, e4492, e4496, e4497, e4498, e4499, e6732, e7984, e7992, e7995, e7998, e7999, e8000, e11142, e11143, e13945, e13946] at *
  omega
theorem n13949 (_v : Vars) (_q : Query _v)  : (e13948 _v) := by
  have p13944 := n13944 _v _q 
  have p13947 := n13947 _v _q 
  exact (Iff.trans p13944 p13947)
theorem n13950 (_v : Vars) (_q : Query _v)  : (e4522 _v) := by
  simp only [e43, e266, e781, e1571, e2917, e4512, e4515, e4520, e4521, e4522] at *
  omega
theorem n13951 (_v : Vars) (_q : Query _v)  : (e4521 _v) := by
  have p12693 := n12693 _v _q 
  have p13950 := n13950 _v _q 
  simp only [e4515, e4521, e4522] at *
  tauto
theorem n13953 (_v : Vars) (_q : Query _v)  : (e13952 _v) := by
  have p12701 := n12701 _v _q 
  change ((e2916 _v) ↔ (e8027 _v)) at p12701
  simp only [e13952, e6790, e11150, p12701]
theorem n13955 (_v : Vars) (_q : Query _v)  : (e13954 _v) := by
  simp only [e5, e6, e8, e10, e12, e41, e46, e108, e109, e111, e2810, e2811, e4523, e8003, e8004, e8005, e8006, e8007, e8027, e11150, e13954] at *
  omega
theorem n13956 (_v : Vars) (_q : Query _v)  : (e13952 _v) := by
  have p13953 := n13953 _v _q 
  have p13955 := n13955 _v _q 
  exact (Iff.trans p13953 p13955)
theorem n13958 (_v : Vars) (_q : Query _v)  : (e13957 _v) := by
  simp only [e5, e6, e8, e12, e41, e46, e2474, e2475, e4560, e8043, e8045, e8047, e8048, e8049, e8050, e11165, e13957] at *
  omega
theorem n13959 (_v : Vars) (_q : Query _v)  : (e12708 _v) := by
  have p12709 := n12709 _v _q 
  have p13958 := n13958 _v _q 
  exact (Iff.trans p12709 p13958)
theorem n13960 (_v : Vars) (_q : Query _v)  : (e8064 _v) := by
  have p12713 := n12713 _v _q 
  change ((e4576 _v) ↔ (e8060 _v)) at p12713
  simp only [e8064, e6425, e8063, p12713]
theorem n13961 (_v : Vars) (_q : Query _v)  : (e8065 _v) := by
  simp only [e5, e6, e8, e12, e41, e1994, e1995, e2919, e4561, e4562, e4563, e4564, e4565, e8052, e8060, e8063, e8065] at *
  omega
theorem n13962 (_v : Vars) (_q : Query _v)  : (e8064 _v) := by
  have p13960 := n13960 _v _q 
  have p13961 := n13961 _v _q 
  exact (Iff.trans p13960 p13961)
theorem n13964 (_v : Vars) (_q : Query _v)  : (e13963 _v) := by
  have p11173 := n11173 _v _q 
  have p13962 := n13962 _v _q 
  change ((e6424 _v) ↔ (e8066 _v)) at p11173
  change ((e6425 _v) ↔ (e8063 _v)) at p13962
  simp only [e13963, e6426, e8067, p11173, p13962]
theorem n13967 (_v : Vars) (_q : Query _v)  : (e13966 _v) := by
  simp only [e5, e6, e8, e12, e41, e1994, e1995, e2919, e4561, e4562, e4563, e4564, e4565, e4567, e4568, e4572, e4573, e4574, e4575, e6423, e8052, e8060, e8063, e8066, e8067, e8068, e11176, e11177, e13965, e13966] at *
  omega
end
end Assembly
