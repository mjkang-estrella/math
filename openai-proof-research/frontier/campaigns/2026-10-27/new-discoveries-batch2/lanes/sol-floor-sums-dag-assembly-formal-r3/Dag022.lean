import Dag021
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n6446 (_v : Vars) (_q : Query _v)  : (e6445 _v) := by
  simp only [e2051, e2845, e2846, e2847, e2848, e6443, e6444, e6445] at *
  by_cases hc : ((e2050 _v) ≤ (e12 _v)) <;> simp [hc]
theorem n6453 (_v : Vars) (_q : Query _v)  : (e6452 _v) := by
  simp only [e174, e176, e2849, e2850, e2851, e4629, e6451, e6452] at *
  by_cases hc : ((e173 _v) ≤ (e12 _v)) <;> simp [hc]
theorem n6461 (_v : Vars) (_q : Query _v)  : (e6460 _v) := by
  simp only [e2083, e2852, e2853, e2854, e2855, e6458, e6459, e6460] at *
  by_cases hc : ((e2082 _v) ≤ (e12 _v)) <;> simp [hc]
theorem n6469 (_v : Vars) (_q : Query _v)  : (e6468 _v) := by
  simp only [e346, e2098, e2856, e2857, e2858, e6466, e6467, e6468] at *
  by_cases hc : ((e2097 _v) ≤ (e12 _v)) <;> simp [hc]
theorem n6473 (_v : Vars) (_q : Query _v)  : (e6472 _v) := by
  simp only [e2115, e2859, e2860, e2861, e2862, e6470, e6471, e6472] at *
  by_cases hc : ((e2114 _v) ≤ (e12 _v)) <;> simp [hc]
theorem n6500 (_v : Vars) (_q : Query _v)  : (e6499 _v) := by
  simp only [e185, e187, e2863, e2864, e2865, e4589, e6498, e6499] at *
  by_cases hc : ((e184 _v) ≤ (e12 _v)) <;> simp [hc]
theorem n6508 (_v : Vars) (_q : Query _v)  : (e6507 _v) := by
  simp only [e2201, e2866, e2867, e2868, e2869, e6505, e6506, e6507] at *
  by_cases hc : ((e2200 _v) ≤ (e12 _v)) <;> simp [hc]
theorem n6516 (_v : Vars) (_q : Query _v)  : (e6515 _v) := by
  simp only [e311, e2216, e2870, e2871, e2872, e6513, e6514, e6515] at *
  by_cases hc : ((e2215 _v) ≤ (e12 _v)) <;> simp [hc]
theorem n6520 (_v : Vars) (_q : Query _v)  : (e6519 _v) := by
  simp only [e2233, e2873, e2874, e2875, e2876, e6517, e6518, e6519] at *
  by_cases hc : ((e2232 _v) ≤ (e12 _v)) <;> simp [hc]
theorem n6599 (_v : Vars) (_q : Query _v)  : (e6598 _v) := by
  simp only [e400, e402, e2883, e2884, e2885, e4347, e6597, e6598] at *
  by_cases hc : ((e399 _v) ≤ (e12 _v)) <;> simp [hc]
theorem n6607 (_v : Vars) (_q : Query _v)  : (e6606 _v) := by
  simp only [e2424, e2886, e2887, e2888, e2889, e6604, e6605, e6606] at *
  by_cases hc : ((e2423 _v) ≤ (e12 _v)) <;> simp [hc]
theorem n6615 (_v : Vars) (_q : Query _v)  : (e6614 _v) := by
  simp only [e2441, e2890, e2891, e2892, e2893, e6612, e6613, e6614] at *
  by_cases hc : ((e2440 _v) ≤ (e12 _v)) <;> simp [hc]
theorem n6623 (_v : Vars) (_q : Query _v)  : (e6622 _v) := by
  simp only [e2458, e2894, e2895, e2896, e2897, e6620, e6621, e6622] at *
  by_cases hc : ((e2457 _v) ≤ (e12 _v)) <;> simp [hc]
theorem n6797 (_v : Vars) (_q : Query _v)  : (e6796 _v) := by
  simp only [e12, e2999, e3000, e3001, e3002, e3003, e3006, e3009, e6796] at *
  omega
theorem n6798 (_v : Vars) (_q : Query _v)  : (e3020 _v) := by
  simp only [e5, e6, e12, e3012, e3017, e3018, e3019, e3020] at *
  omega
theorem n6799 (_v : Vars) (_q : Query _v)  : (e3022 _v) := by
  simp only [e5, e6, e12, e3013, e3017, e3018, e3021, e3022] at *
  omega
theorem n6801 (_v : Vars) (_q : Query _v)  : (e6800 _v) := by
  have p6798 := n6798 _v _q 
  have p6799 := n6799 _v _q 
  change ((e3012 _v) ↔ (e3019 _v)) at p6798
  change ((e3013 _v) ↔ (e3021 _v)) at p6799
  simp only [e6800, e3014, e3023, p6798, p6799]
theorem n6805 (_v : Vars) (_q : Query _v)  : (e6804 _v) := by
  simp only [e5, e6, e12, e3017, e3018, e3019, e3021, e3023, e3024, e3025, e6802, e6803, e6804] at *
  omega
theorem n6813 (_v : Vars) (_q : Query _v)  : (e6812 _v) := by
  simp only [e12, e3026, e3027, e3028, e3029, e3030, e3033, e3036, e6812] at *
  omega
theorem n6814 (_v : Vars) (_q : Query _v)  : (e3045 _v) := by
  simp only [e5, e6, e12, e3037, e3042, e3043, e3044, e3045] at *
  omega
theorem n6815 (_v : Vars) (_q : Query _v)  : (e3047 _v) := by
  simp only [e5, e6, e12, e3038, e3042, e3043, e3046, e3047] at *
  omega
theorem n6817 (_v : Vars) (_q : Query _v)  : (e6816 _v) := by
  have p6814 := n6814 _v _q 
  have p6815 := n6815 _v _q 
  change ((e3037 _v) ↔ (e3044 _v)) at p6814
  change ((e3038 _v) ↔ (e3046 _v)) at p6815
  simp only [e6816, e3039, e3048, p6814, p6815]
theorem n6821 (_v : Vars) (_q : Query _v)  : (e6820 _v) := by
  simp only [e5, e6, e12, e3042, e3043, e3044, e3046, e3048, e3049, e3050, e6818, e6819, e6820] at *
  omega
theorem n6824 (_v : Vars) (_q : Query _v)  : (e6823 _v) := by
  simp only [e12, e3051, e3052, e3053, e3054, e3055, e3058, e3061, e6823] at *
  omega
theorem n6825 (_v : Vars) (_q : Query _v)  : (e3070 _v) := by
  simp only [e5, e6, e12, e2981, e3063, e3068, e3069, e3070] at *
  omega
theorem n6826 (_v : Vars) (_q : Query _v)  : (e3072 _v) := by
  simp only [e5, e6, e12, e2981, e3064, e3068, e3071, e3072] at *
  omega
theorem n6828 (_v : Vars) (_q : Query _v)  : (e6827 _v) := by
  have p6825 := n6825 _v _q 
  have p6826 := n6826 _v _q 
  change ((e3063 _v) ↔ (e3069 _v)) at p6825
  change ((e3064 _v) ↔ (e3071 _v)) at p6826
  simp only [e6827, e3065, e3073, p6825, p6826]
theorem n6832 (_v : Vars) (_q : Query _v)  : (e6831 _v) := by
  simp only [e5, e6, e12, e2981, e3068, e3069, e3071, e3073, e3074, e3075, e6829, e6830, e6831] at *
  omega
theorem n6840 (_v : Vars) (_q : Query _v)  : (e6839 _v) := by
  simp only [e12, e3076, e3077, e3078, e3079, e3080, e3083, e3086, e6839] at *
  omega
theorem n6841 (_v : Vars) (_q : Query _v)  : (e3095 _v) := by
  simp only [e5, e6, e12, e2923, e3088, e3093, e3094, e3095] at *
  omega
theorem n6842 (_v : Vars) (_q : Query _v)  : (e3097 _v) := by
  simp only [e5, e6, e12, e2923, e3089, e3093, e3096, e3097] at *
  omega
theorem n6844 (_v : Vars) (_q : Query _v)  : (e6843 _v) := by
  have p6841 := n6841 _v _q 
  have p6842 := n6842 _v _q 
  change ((e3088 _v) ↔ (e3094 _v)) at p6841
  change ((e3089 _v) ↔ (e3096 _v)) at p6842
  simp only [e6843, e3090, e3098, p6841, p6842]
theorem n6848 (_v : Vars) (_q : Query _v)  : (e6847 _v) := by
  simp only [e5, e6, e12, e2923, e3093, e3094, e3096, e3098, e3099, e3100, e6845, e6846, e6847] at *
  omega
theorem n6858 (_v : Vars) (_q : Query _v)  : (e6857 _v) := by
  simp only [e12, e3108, e3109, e3110, e3113, e3114, e3115, e3116, e6857] at *
  omega
theorem n6859 (_v : Vars) (_q : Query _v)  : (e3123 _v) := by
  simp only [e5, e6, e12, e3101, e3102, e3103, e3118, e3123] at *
  omega
theorem n6860 (_v : Vars) (_q : Query _v)  : (e3124 _v) := by
  simp only [e5, e6, e12, e3101, e3102, e3105, e3119, e3124] at *
  omega
theorem n6862 (_v : Vars) (_q : Query _v)  : (e6861 _v) := by
  have p6859 := n6859 _v _q 
  have p6860 := n6860 _v _q 
  change ((e3118 _v) ↔ (e3103 _v)) at p6859
  change ((e3119 _v) ↔ (e3105 _v)) at p6860
  simp only [e6861, e3120, e3125, p6859, p6860]
theorem n6865 (_v : Vars) (_q : Query _v)  : (e6864 _v) := by
  simp only [e5, e6, e12, e3101, e3102, e3103, e3104, e3105, e3106, e3125, e6855, e6863, e6864] at *
  omega
theorem n6873 (_v : Vars) (_q : Query _v)  : (e6872 _v) := by
  simp only [e12, e3132, e3133, e3134, e3137, e3138, e3139, e3140, e6872] at *
  omega
theorem n6874 (_v : Vars) (_q : Query _v)  : (e3151 _v) := by
  simp only [e5, e6, e12, e3143, e3148, e3149, e3150, e3151] at *
  omega
theorem n6875 (_v : Vars) (_q : Query _v)  : (e3153 _v) := by
  simp only [e5, e6, e12, e3144, e3148, e3149, e3152, e3153] at *
  omega
theorem n6877 (_v : Vars) (_q : Query _v)  : (e6876 _v) := by
  have p6874 := n6874 _v _q 
  have p6875 := n6875 _v _q 
  change ((e3143 _v) ↔ (e3150 _v)) at p6874
  change ((e3144 _v) ↔ (e3152 _v)) at p6875
  simp only [e6876, e3145, e3154, p6874, p6875]
theorem n6881 (_v : Vars) (_q : Query _v)  : (e6880 _v) := by
  simp only [e5, e6, e12, e3148, e3149, e3150, e3152, e3154, e3155, e3156, e6878, e6879, e6880] at *
  omega
theorem n6891 (_v : Vars) (_q : Query _v)  : (e6890 _v) := by
  simp only [e12, e3172, e3173, e3174, e3177, e3178, e3179, e3180, e6890] at *
  omega
theorem n6892 (_v : Vars) (_q : Query _v)  : (e3187 _v) := by
  simp only [e5, e6, e12, e3165, e3166, e3167, e3182, e3187] at *
  omega
end
end Assembly
