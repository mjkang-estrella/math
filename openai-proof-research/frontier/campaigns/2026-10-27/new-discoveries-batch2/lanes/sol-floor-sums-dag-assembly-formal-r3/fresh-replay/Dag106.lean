import Dag105
import generated.th_lemma_4
import generated.th_lemma_5
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n14363 (_v : Vars) (_q : Query _v)  : (e12442 _v) := by
  have p14362 := n14362 _v _q 
  have p13500 := n13500 _v _q 
  change ((e6925 _v) ↔ (e6926 _v)) at p14362
  change ((e6699 _v) ↔ (e10600 _v)) at p13500
  simp only [e12442, e10397, e10601, p14362, p13500]
theorem n14365 (_v : Vars) (_q : Query _v)  : (e14364 _v) := by
  simp only [e5, e6, e10, e12, e41, e43, e44, e46, e2640, e2641, e3191, e3198, e3199, e3200, e3202, e3205, e3206, e6910, e6911, e6912, e6913, e6914, e6920, e6921, e6924, e6926, e6931, e6932, e10600, e10601, e10602, e10603, e10604, e14364] at *
  omega
theorem n14366 (_v : Vars) (_q : Query _v)  : (e12443 _v) := by
  have p14363 := n14363 _v _q 
  have p14365 := n14365 _v _q 
  exact (Iff.trans p14363 p14365)
theorem n14367 (_v : Vars) (_q : Query _v)  : (e10604 _v) := by
  have p10398 := n10398 _v _q 
  have p14366 := n14366 _v _q 
  simp only [e2641, e3192, e3200, e3202, e3205, e3206, e6698, e6699, e6910, e6911, e6912, e6913, e6914, e6920, e6921, e6924, e6925, e6926, e6931, e6932, e10397, e10600, e10602, e10603, e10604, e12443] at *
  tauto
theorem n14368 (_v : Vars) (_q : Query _v)  : (e13506 _v) := by
  have p12340 := n12340 _v _q 
  have p13510 := n13510 _v _q 
  simp only [e2611, e3210, e3211, e3212, e3213, e3214, e3216, e3220, e3222, e3229, e3231, e3234, e3235, e6690, e6691, e6692, e6693, e6939, e6940, e6943, e6946, e6948, e10611, e10612, e13506, e13509] at *
  tauto
theorem n14369 (_v : Vars) (_q : Query _v)  : (e6946 _v) := by
  have p14368 := n14368 _v _q 
  simp only [e2611, e3210, e3211, e3212, e3213, e3214, e3220, e3229, e3231, e3234, e3235, e6690, e6939, e6940, e6943, e6946, e6948, e10611, e10612, e13506] at *
  tauto
theorem n14370 (_v : Vars) (_q : Query _v)  : (e2611 _v) := by
  have p8663 := n8663 _v _q 
  have p11376 := n11376 _v _q 
  have p11375 := n11375 _v _q 
  have p10893 := n10893 _v _q 
  exact FloorCertificate.node_14370 (e2 _v) (e7 _v) (e17 _v) (e45 _v) (e110 _v) p8663 p11376 p11375 p10893
theorem n14371 (_v : Vars) (_q : Query _v)  : (e3220 _v) := by
  have p14369 := n14369 _v _q 
  have p14370 := n14370 _v _q 
  simp only [e2611, e3210, e3211, e3212, e3213, e3214, e3220, e6690, e6946] at *
  tauto
theorem n14372 (_v : Vars) (_q : Query _v)  : (e13516 _v) := by
  have p12396 := n12396 _v _q 
  have p13520 := n13520 _v _q 
  simp only [e2710, e3236, e3237, e3238, e3239, e3240, e3242, e3246, e3248, e3255, e3257, e3260, e3261, e6738, e6739, e6740, e6741, e6955, e6956, e6959, e6962, e6964, e10619, e10620, e13516, e13519] at *
  tauto
theorem n14373 (_v : Vars) (_q : Query _v)  : (e6962 _v) := by
  have p14372 := n14372 _v _q 
  simp only [e2710, e3236, e3237, e3238, e3239, e3240, e3246, e3255, e3257, e3260, e3261, e6738, e6955, e6956, e6959, e6962, e6964, e10619, e10620, e13516] at *
  tauto
theorem n14374 (_v : Vars) (_q : Query _v)  : (e2710 _v) := by
  have p8663 := n8663 _v _q 
  have p11376 := n11376 _v _q 
  have p10896 := n10896 _v _q 
  have p10893 := n10893 _v _q 
  exact FloorCertificate.node_14374 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) p8663 p11376 p10896 p10893
theorem n14375 (_v : Vars) (_q : Query _v)  : (e3246 _v) := by
  have p14373 := n14373 _v _q 
  have p14374 := n14374 _v _q 
  simp only [e2710, e3236, e3237, e3238, e3239, e3240, e3246, e6738, e6962] at *
  tauto
theorem n14376 (_v : Vars) (_q : Query _v)  : (e13526 _v) := by
  have p12200 := n12200 _v _q 
  have p13530 := n13530 _v _q 
  simp only [e2310, e3265, e3266, e3267, e3268, e3269, e3270, e3271, e3275, e3276, e3277, e3278, e3279, e6555, e6556, e6557, e6558, e6965, e6973, e6976, e6979, e6981, e10627, e10628, e13526, e13529] at *
  tauto
theorem n14377 (_v : Vars) (_q : Query _v)  : (e6976 _v) := by
  have p14376 := n14376 _v _q 
  simp only [e2310, e3265, e3266, e3267, e3268, e3270, e3271, e3275, e3276, e3277, e3278, e6555, e6965, e6973, e6976, e6979, e6981, e10627, e10628, e13526] at *
  tauto
theorem n14378 (_v : Vars) (_q : Query _v)  : (e6979 _v) := by
  have p14376 := n14376 _v _q 
  simp only [e2310, e3265, e3266, e3267, e3268, e3270, e3271, e3275, e3276, e3277, e3278, e6555, e6965, e6973, e6976, e6979, e6981, e10627, e10628, e13526] at *
  tauto
theorem n14379 (_v : Vars) (_q : Query _v)  : (e7002 _v) := by
  have p12451 := n12451 _v _q 
  change ((e3290 _v) ↔ (e6996 _v)) at p12451
  simp only [e7002, e7000, e7001, p12451]
theorem n14380 (_v : Vars) (_q : Query _v)  : (e12458 _v) := by
  have p14379 := n14379 _v _q 
  have p13533 := n13533 _v _q 
  change ((e7000 _v) ↔ (e7001 _v)) at p14379
  change ((e6554 _v) ↔ (e10639 _v)) at p13533
  simp only [e12458, e10241, e10640, p14379, p13533]
theorem n14382 (_v : Vars) (_q : Query _v)  : (e14381 _v) := by
  simp only [e5, e6, e10, e12, e41, e43, e44, e111, e2316, e2317, e3289, e3296, e3297, e3298, e3300, e3303, e3304, e6985, e6986, e6987, e6988, e6989, e6995, e6996, e6999, e7001, e7006, e7007, e10639, e10640, e10641, e10642, e10643, e14381] at *
  omega
theorem n14383 (_v : Vars) (_q : Query _v)  : (e12459 _v) := by
  have p14380 := n14380 _v _q 
  have p14382 := n14382 _v _q 
  exact (Iff.trans p14380 p14382)
theorem n14384 (_v : Vars) (_q : Query _v)  : (e10643 _v) := by
  have p10242 := n10242 _v _q 
  have p14383 := n14383 _v _q 
  simp only [e2317, e3290, e3298, e3300, e3303, e3304, e6553, e6554, e6985, e6986, e6987, e6988, e6989, e6995, e6996, e6999, e7000, e7001, e7006, e7007, e10241, e10639, e10641, e10642, e10643, e12459] at *
  tauto
theorem n14385 (_v : Vars) (_q : Query _v)  : (e13539 _v) := by
  have p10108 := n10108 _v _q 
  have p13543 := n13543 _v _q 
  simp only [e2010, e3308, e3309, e3310, e3311, e3312, e3314, e3318, e3319, e3326, e3328, e3331, e3332, e6431, e6432, e6433, e6434, e7014, e7015, e7018, e7021, e7023, e10650, e10651, e13539, e13542] at *
  tauto
theorem n14386 (_v : Vars) (_q : Query _v)  : (e7021 _v) := by
  have p14385 := n14385 _v _q 
  simp only [e2010, e3308, e3309, e3310, e3311, e3312, e3318, e3326, e3328, e3331, e3332, e6431, e7014, e7015, e7018, e7021, e7023, e10650, e10651, e13539] at *
  tauto
theorem n14387 (_v : Vars) (_q : Query _v)  : (e2010 _v) := by
  have p8663 := n8663 _v _q 
  have p11376 := n11376 _v _q 
  exact FloorCertificate.node_14387 (e2 _v) (e7 _v) (e17 _v) p8663 p11376
theorem n14388 (_v : Vars) (_q : Query _v)  : (e3318 _v) := by
  have p14386 := n14386 _v _q 
  have p14387 := n14387 _v _q 
  simp only [e2010, e3308, e3309, e3310, e3311, e3312, e3318, e6431, e7021] at *
  tauto
theorem n14389 (_v : Vars) (_q : Query _v)  : (e13549 _v) := by
  have p12324 := n12324 _v _q 
  have p13553 := n13553 _v _q 
  simp only [e2564, e3333, e3334, e3335, e3336, e3337, e3339, e3343, e3345, e3353, e3355, e3358, e3359, e6668, e6669, e6670, e6671, e7030, e7031, e7034, e7037, e7039, e10658, e10659, e13549, e13552] at *
  tauto
theorem n14390 (_v : Vars) (_q : Query _v)  : (e7037 _v) := by
  have p14389 := n14389 _v _q 
  simp only [e2564, e3333, e3334, e3335, e3336, e3337, e3343, e3353, e3355, e3358, e3359, e6668, e7030, e7031, e7034, e7037, e7039, e10658, e10659, e13549] at *
  tauto
theorem n14391 (_v : Vars) (_q : Query _v)  : (e2564 _v) := by
  have p11375 := n11375 _v _q 
  have p8663 := n8663 _v _q 
  have p10893 := n10893 _v _q 
  have p331 := n331 _v _q 
  exact FloorCertificate.node_14391 (e2 _v) (e17 _v) (e45 _v) (e110 _v) p11375 p8663 p10893 p331
theorem n14392 (_v : Vars) (_q : Query _v)  : (e3343 _v) := by
  have p14390 := n14390 _v _q 
  have p14391 := n14391 _v _q 
  simp only [e2564, e3333, e3334, e3335, e3336, e3337, e3343, e6668, e7037] at *
  tauto
theorem n14393 (_v : Vars) (_q : Query _v)  : (e13559 _v) := by
  have p12170 := n12170 _v _q 
  have p13563 := n13563 _v _q 
  simp only [e2268, e3360, e3361, e3362, e3363, e3364, e3366, e3370, e3372, e3380, e3382, e3385, e3386, e6537, e6538, e6539, e6540, e7046, e7047, e7050, e7053, e7055, e10666, e10667, e13559, e13562] at *
  tauto
theorem n14394 (_v : Vars) (_q : Query _v)  : (e7053 _v) := by
  have p14393 := n14393 _v _q 
  simp only [e2268, e3360, e3361, e3362, e3363, e3364, e3370, e3380, e3382, e3385, e3386, e6537, e7046, e7047, e7050, e7053, e7055, e10666, e10667, e13559] at *
  tauto
theorem n14395 (_v : Vars) (_q : Query _v)  : (e2268 _v) := by
  have p11376 := n11376 _v _q 
  have p10896 := n10896 _v _q 
  have p8663 := n8663 _v _q 
  exact FloorCertificate.node_14395 (e2 _v) (e7 _v) (e9 _v) (e17 _v) p11376 p10896 p8663
theorem n14396 (_v : Vars) (_q : Query _v)  : (e3370 _v) := by
  have p14394 := n14394 _v _q 
  have p14395 := n14395 _v _q 
  simp only [e2268, e3360, e3361, e3362, e3363, e3364, e3370, e6537, e7053] at *
  tauto
theorem n14397 (_v : Vars) (_q : Query _v)  : (e12470 _v) := by
  have p13569 := n13569 _v _q 
  have p12469 := n12469 _v _q 
  exact (Iff.trans p13569 p12469)
theorem n14398 (_v : Vars) (_q : Query _v)  : (e10680 _v) := by
  have p6419 := n6419 _v _q 
  have p14397 := n14397 _v _q 
  simp only [e1985, e2830, e2832, e2833, e3387, e3388, e3389, e3390, e3391, e3393, e3397, e3405, e3407, e3410, e3411, e6417, e6418, e7062, e7063, e7066, e10670, e10677, e10678, e10679, e10680, e12470] at *
  tauto
theorem n14399 (_v : Vars) (_q : Query _v)  : (e10670 _v) := by
  have p14398 := n14398 _v _q 
  simp only [e1985, e2830, e3387, e3388, e3389, e3390, e3391, e3397, e3405, e3407, e3410, e3411, e7062, e7063, e7066, e10670, e10677, e10678, e10679, e10680] at *
  tauto
theorem n14400 (_v : Vars) (_q : Query _v)  : (e3397 _v) := by
  have p14399 := n14399 _v _q 
  have p12473 := n12473 _v _q 
  simp only [e1985, e2830, e3387, e3388, e3389, e3390, e3391, e3397, e10670] at *
  tauto
theorem n14401 (_v : Vars) (_q : Query _v)  : (e13575 _v) := by
  have p10168 := n10168 _v _q 
  have p13579 := n13579 _v _q 
  simp only [e2108, e3412, e3413, e3414, e3415, e3416, e3418, e3422, e3423, e3430, e3432, e3435, e3436, e6474, e6475, e6476, e6477, e7073, e7074, e7077, e7080, e7082, e10687, e10688, e13575, e13578] at *
  tauto
theorem n14402 (_v : Vars) (_q : Query _v)  : (e7080 _v) := by
  have p14401 := n14401 _v _q 
  simp only [e2108, e3412, e3413, e3414, e3415, e3416, e3422, e3430, e3432, e3435, e3436, e6474, e7073, e7074, e7077, e7080, e7082, e10687, e10688, e13575] at *
  tauto
theorem n14403 (_v : Vars) (_q : Query _v)  : (e2108 _v) := by
  have p8663 := n8663 _v _q 
  have p11375 := n11375 _v _q 
  have p331 := n331 _v _q 
  exact FloorCertificate.node_14403 (e2 _v) (e17 _v) (e110 _v) p8663 p11375 p331
theorem n14404 (_v : Vars) (_q : Query _v)  : (e3422 _v) := by
  have p14402 := n14402 _v _q 
  have p14403 := n14403 _v _q 
  simp only [e2108, e3412, e3413, e3414, e3415, e3416, e3422, e6474, e7080] at *
  tauto
theorem n14405 (_v : Vars) (_q : Query _v)  : (e13585 _v) := by
  have p10222 := n10222 _v _q 
  have p13589 := n13589 _v _q 
  simp only [e2226, e3437, e3438, e3439, e3440, e3441, e3443, e3447, e3448, e3455, e3457, e3460, e3461, e6521, e6522, e6523, e6524, e7089, e7090, e7093, e7096, e7098, e10695, e10696, e13585, e13588] at *
  tauto
theorem n14406 (_v : Vars) (_q : Query _v)  : (e7096 _v) := by
  have p14405 := n14405 _v _q 
  simp only [e2226, e3437, e3438, e3439, e3440, e3441, e3447, e3455, e3457, e3460, e3461, e6521, e7089, e7090, e7093, e7096, e7098, e10695, e10696, e13585] at *
  tauto
theorem n14407 (_v : Vars) (_q : Query _v)  : (e2226 _v) := by
  have p8663 := n8663 _v _q 
  have p10896 := n10896 _v _q 
  have p331 := n331 _v _q 
  exact FloorCertificate.node_14407 (e2 _v) (e9 _v) (e17 _v) p8663 p10896 p331
theorem n14408 (_v : Vars) (_q : Query _v)  : (e3447 _v) := by
  have p14406 := n14406 _v _q 
  have p14407 := n14407 _v _q 
  simp only [e2226, e3437, e3438, e3439, e3440, e3441, e3447, e6521, e7096] at *
  tauto
theorem n14409 (_v : Vars) (_q : Query _v)  : (e13595 _v) := by
  have p10306 := n10306 _v _q 
  have p13599 := n13599 _v _q 
  simp only [e2417, e3462, e3463, e3464, e3465, e3466, e3468, e3472, e3473, e3480, e3482, e3485, e3486, e6608, e6609, e6610, e6611, e7105, e7106, e7109, e7112, e7114, e10703, e10704, e13595, e13598] at *
  tauto
end
end Assembly
