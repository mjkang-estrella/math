import Dag022
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n6893 (_v : Vars) (_q : Query _v)  : (e3188 _v) := by
  simp only [e5, e6, e12, e3165, e3166, e3169, e3183, e3188] at *
  omega
theorem n6895 (_v : Vars) (_q : Query _v)  : (e6894 _v) := by
  have p6892 := n6892 _v _q 
  have p6893 := n6893 _v _q 
  change ((e3182 _v) ↔ (e3167 _v)) at p6892
  change ((e3183 _v) ↔ (e3169 _v)) at p6893
  simp only [e6894, e3184, e3189, p6892, p6893]
theorem n6898 (_v : Vars) (_q : Query _v)  : (e6897 _v) := by
  simp only [e5, e6, e12, e3165, e3166, e3167, e3168, e3169, e3170, e3189, e6888, e6896, e6897] at *
  omega
theorem n6907 (_v : Vars) (_q : Query _v)  : (e3190 _v) := by
  simp only [e3172, e3173, e3177, e3178, e3179, e3190] at *
  tauto
theorem n6908 (_v : Vars) (_q : Query _v) (h3178 : (e3178 _v)) : (e3178 _v) := by
  exact h3178
theorem n6909 (_v : Vars) (_q : Query _v) (h3178 : (e3178 _v)) : (e3179 _v) := by
  have p6907 := n6907 _v _q 
  have p6908 := n6908 _v _q h3178
  simp only [e3172, e3173, e3177, e3178, e3179, e3190] at *
  tauto
theorem n6916 (_v : Vars) (_q : Query _v)  : (e3201 _v) := by
  simp only [e5, e6, e12, e3193, e3198, e3199, e3200, e3201] at *
  omega
theorem n6917 (_v : Vars) (_q : Query _v)  : (e3203 _v) := by
  simp only [e5, e6, e12, e3194, e3198, e3199, e3202, e3203] at *
  omega
theorem n6919 (_v : Vars) (_q : Query _v)  : (e6918 _v) := by
  have p6916 := n6916 _v _q 
  have p6917 := n6917 _v _q 
  change ((e3193 _v) ↔ (e3200 _v)) at p6916
  change ((e3194 _v) ↔ (e3202 _v)) at p6917
  simp only [e6918, e3195, e3204, p6916, p6917]
theorem n6923 (_v : Vars) (_q : Query _v)  : (e6922 _v) := by
  simp only [e5, e6, e12, e3198, e3199, e3200, e3202, e3204, e3205, e3206, e6920, e6921, e6922] at *
  omega
theorem n6934 (_v : Vars) (_q : Query _v)  : (e6933 _v) := by
  simp only [e12, e3210, e3211, e3212, e3213, e3214, e3217, e3220, e6933] at *
  omega
theorem n6935 (_v : Vars) (_q : Query _v)  : (e3230 _v) := by
  simp only [e5, e6, e12, e2975, e3223, e3228, e3229, e3230] at *
  omega
theorem n6936 (_v : Vars) (_q : Query _v)  : (e3232 _v) := by
  simp only [e5, e6, e12, e2975, e3224, e3228, e3231, e3232] at *
  omega
theorem n6938 (_v : Vars) (_q : Query _v)  : (e6937 _v) := by
  have p6935 := n6935 _v _q 
  have p6936 := n6936 _v _q 
  change ((e3223 _v) ↔ (e3229 _v)) at p6935
  change ((e3224 _v) ↔ (e3231 _v)) at p6936
  simp only [e6937, e3225, e3233, p6935, p6936]
theorem n6942 (_v : Vars) (_q : Query _v)  : (e6941 _v) := by
  simp only [e5, e6, e12, e2975, e3228, e3229, e3231, e3233, e3234, e3235, e6939, e6940, e6941] at *
  omega
theorem n6950 (_v : Vars) (_q : Query _v)  : (e6949 _v) := by
  simp only [e12, e3236, e3237, e3238, e3239, e3240, e3243, e3246, e6949] at *
  omega
theorem n6951 (_v : Vars) (_q : Query _v)  : (e3256 _v) := by
  simp only [e5, e6, e12, e2985, e3249, e3254, e3255, e3256] at *
  omega
theorem n6952 (_v : Vars) (_q : Query _v)  : (e3258 _v) := by
  simp only [e5, e6, e12, e2985, e3250, e3254, e3257, e3258] at *
  omega
theorem n6954 (_v : Vars) (_q : Query _v)  : (e6953 _v) := by
  have p6951 := n6951 _v _q 
  have p6952 := n6952 _v _q 
  change ((e3249 _v) ↔ (e3255 _v)) at p6951
  change ((e3250 _v) ↔ (e3257 _v)) at p6952
  simp only [e6953, e3251, e3259, p6951, p6952]
theorem n6958 (_v : Vars) (_q : Query _v)  : (e6957 _v) := by
  simp only [e5, e6, e12, e2985, e3254, e3255, e3257, e3259, e3260, e3261, e6955, e6956, e6957] at *
  omega
theorem n6968 (_v : Vars) (_q : Query _v)  : (e6967 _v) := by
  simp only [e12, e3270, e3271, e3272, e3275, e3276, e3277, e3278, e6967] at *
  omega
theorem n6969 (_v : Vars) (_q : Query _v)  : (e3285 _v) := by
  simp only [e5, e6, e12, e3263, e3264, e3265, e3280, e3285] at *
  omega
theorem n6970 (_v : Vars) (_q : Query _v)  : (e3286 _v) := by
  simp only [e5, e6, e12, e3263, e3264, e3267, e3281, e3286] at *
  omega
theorem n6972 (_v : Vars) (_q : Query _v)  : (e6971 _v) := by
  have p6969 := n6969 _v _q 
  have p6970 := n6970 _v _q 
  change ((e3280 _v) ↔ (e3265 _v)) at p6969
  change ((e3281 _v) ↔ (e3267 _v)) at p6970
  simp only [e6971, e3282, e3287, p6969, p6970]
theorem n6975 (_v : Vars) (_q : Query _v)  : (e6974 _v) := by
  simp only [e5, e6, e12, e3263, e3264, e3265, e3266, e3267, e3268, e3287, e6965, e6973, e6974] at *
  omega
theorem n6982 (_v : Vars) (_q : Query _v)  : (e3288 _v) := by
  simp only [e3270, e3271, e3275, e3276, e3277, e3288] at *
  tauto
theorem n6983 (_v : Vars) (_q : Query _v) (h3276 : (e3276 _v)) : (e3276 _v) := by
  exact h3276
theorem n6984 (_v : Vars) (_q : Query _v) (h3276 : (e3276 _v)) : (e3277 _v) := by
  have p6982 := n6982 _v _q 
  have p6983 := n6983 _v _q h3276
  simp only [e3270, e3271, e3275, e3276, e3277, e3288] at *
  tauto
theorem n6991 (_v : Vars) (_q : Query _v)  : (e3299 _v) := by
  simp only [e5, e6, e12, e3291, e3296, e3297, e3298, e3299] at *
  omega
theorem n6992 (_v : Vars) (_q : Query _v)  : (e3301 _v) := by
  simp only [e5, e6, e12, e3292, e3296, e3297, e3300, e3301] at *
  omega
theorem n6994 (_v : Vars) (_q : Query _v)  : (e6993 _v) := by
  have p6991 := n6991 _v _q 
  have p6992 := n6992 _v _q 
  change ((e3291 _v) ↔ (e3298 _v)) at p6991
  change ((e3292 _v) ↔ (e3300 _v)) at p6992
  simp only [e6993, e3293, e3302, p6991, p6992]
theorem n6998 (_v : Vars) (_q : Query _v)  : (e6997 _v) := by
  simp only [e5, e6, e12, e3296, e3297, e3298, e3300, e3302, e3303, e3304, e6995, e6996, e6997] at *
  omega
theorem n7009 (_v : Vars) (_q : Query _v)  : (e7008 _v) := by
  simp only [e12, e3308, e3309, e3310, e3311, e3312, e3315, e3318, e7008] at *
  omega
theorem n7010 (_v : Vars) (_q : Query _v)  : (e3327 _v) := by
  simp only [e5, e6, e12, e2921, e3320, e3325, e3326, e3327] at *
  omega
theorem n7011 (_v : Vars) (_q : Query _v)  : (e3329 _v) := by
  simp only [e5, e6, e12, e2921, e3321, e3325, e3328, e3329] at *
  omega
theorem n7013 (_v : Vars) (_q : Query _v)  : (e7012 _v) := by
  have p7010 := n7010 _v _q 
  have p7011 := n7011 _v _q 
  change ((e3320 _v) ↔ (e3326 _v)) at p7010
  change ((e3321 _v) ↔ (e3328 _v)) at p7011
  simp only [e7012, e3322, e3330, p7010, p7011]
theorem n7017 (_v : Vars) (_q : Query _v)  : (e7016 _v) := by
  simp only [e5, e6, e12, e2921, e3325, e3326, e3328, e3330, e3331, e3332, e7014, e7015, e7016] at *
  omega
theorem n7025 (_v : Vars) (_q : Query _v)  : (e7024 _v) := by
  simp only [e12, e3333, e3334, e3335, e3336, e3337, e3340, e3343, e7024] at *
  omega
theorem n7026 (_v : Vars) (_q : Query _v)  : (e3354 _v) := by
  simp only [e5, e6, e12, e3346, e3351, e3352, e3353, e3354] at *
  omega
theorem n7027 (_v : Vars) (_q : Query _v)  : (e3356 _v) := by
  simp only [e5, e6, e12, e3347, e3351, e3352, e3355, e3356] at *
  omega
theorem n7029 (_v : Vars) (_q : Query _v)  : (e7028 _v) := by
  have p7026 := n7026 _v _q 
  have p7027 := n7027 _v _q 
  change ((e3346 _v) ↔ (e3353 _v)) at p7026
  change ((e3347 _v) ↔ (e3355 _v)) at p7027
  simp only [e7028, e3348, e3357, p7026, p7027]
theorem n7033 (_v : Vars) (_q : Query _v)  : (e7032 _v) := by
  simp only [e5, e6, e12, e3351, e3352, e3353, e3355, e3357, e3358, e3359, e7030, e7031, e7032] at *
  omega
theorem n7041 (_v : Vars) (_q : Query _v)  : (e7040 _v) := by
  simp only [e12, e3360, e3361, e3362, e3363, e3364, e3367, e3370, e7040] at *
  omega
theorem n7042 (_v : Vars) (_q : Query _v)  : (e3381 _v) := by
  simp only [e5, e6, e12, e3373, e3378, e3379, e3380, e3381] at *
  omega
theorem n7043 (_v : Vars) (_q : Query _v)  : (e3383 _v) := by
  simp only [e5, e6, e12, e3374, e3378, e3379, e3382, e3383] at *
  omega
end
end Assembly
