import Dag123
import generated.th_lemma_7
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n15237 (_v : Vars) (_q : Query _v) (h2061 : (e2061 _v)) : (e4567 _v) := by
  have p8485 := n8485 _v _q 
  have p15236 := n15236 _v _q h2061
  simp only [e4567, e4568, e4572, e4573, e4574, e4575, e4956] at *
  tauto
theorem n15238 (_v : Vars) (_q : Query _v) (h6700 : (e6700 _v)) : (e5108 _v) := by
  have p11027 := n11027 _v _q h6700
  have p4016 := n4016 _v _q 
  exact FloorCertificate.node_15238 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) p11027 p4016
theorem n15239 (_v : Vars) (_q : Query _v) (h6700 : (e6700 _v)) : (e5119 _v) := by
  have p14487 := n14487 _v _q 
  have p15238 := n15238 _v _q h6700
  simp only [e48, e70, e72, e75, e76, e5108, e5118, e5119, e5122] at *
  tauto
theorem n15240 (_v : Vars) (_q : Query _v) (h6700 : (e6700 _v)) : (e6501 _v) := by
  have p11027 := n11027 _v _q h6700
  have p10893 := n10893 _v _q 
  exact FloorCertificate.node_15240 (e2 _v) (e9 _v) (e17 _v) (e45 _v) p11027 p10893
theorem n15241 (_v : Vars) (_q : Query _v) (h6700 : (e6700 _v)) : (e8103 _v) := by
  have p14626 := n14626 _v _q 
  have p15240 := n15240 _v _q h6700
  simp only [e2179, e4608, e4609, e4610, e4611, e6501, e8095, e8103, e8106] at *
  tauto
theorem n15242 (_v : Vars) (_q : Query _v) (h2125 : (e2125 _v)) : (e4466 _v) := by
  have p14604 := n14604 _v _q 
  have p8475 := n8475 _v _q h2125
  simp only [e2125, e4458, e4459, e4463, e4464, e4465, e4466, e6480, e7977] at *
  tauto
theorem n15243 (_v : Vars) (_q : Query _v) (h2125 : (e2125 _v)) : (e4459 _v) := by
  have p8443 := n8443 _v _q 
  have p15242 := n15242 _v _q h2125
  simp only [e4458, e4459, e4463, e4464, e4465, e4466, e4482] at *
  tauto
theorem n15244 (_v : Vars) (_q : Query _v) (h2125 : (e2125 _v)) : (e2585 _v) := by
  have p11436 := n11436 _v _q 
  have p8475 := n8475 _v _q h2125
  simp only [e2125, e2585, e6480, e11435] at *
  tauto
theorem n15245 (_v : Vars) (_q : Query _v) (h2125 : (e2125 _v)) : (e4314 _v) := by
  have p14704 := n14704 _v _q 
  have p15244 := n15244 _v _q h2125
  simp only [e2585, e4306, e4307, e4311, e4312, e4313, e4314, e6676, e7836] at *
  tauto
theorem n15246 (_v : Vars) (_q : Query _v) (h2125 : (e2125 _v)) : (e4306 _v) := by
  have p14984 := n14984 _v _q 
  have p15245 := n15245 _v _q h2125
  simp only [e4306, e4307, e4311, e4312, e4313, e4314, e4964] at *
  tauto
theorem n15247 (_v : Vars) (_q : Query _v) (h8310 : (e8310 _v)) : (e8322 _v) := by
  have p15218 := n15218 _v _q 
  have p11384 := n11384 _v _q h8310
  simp only [e2529, e8310, e8315, e8317, e8319, e8320, e8321, e8322, e11298] at *
  tauto
theorem n15248 (_v : Vars) (_q : Query _v) (h8310 : (e8310 _v)) : (e8317 _v) := by
  have p11541 := n11541 _v _q 
  have p15247 := n15247 _v _q h8310
  simp only [e8315, e8317, e8319, e8320, e8321, e8322, e8491] at *
  tauto
theorem n15249 (_v : Vars) (_q : Query _v)  : (e10960 _v) := by
  have p14542 := n14542 _v _q 
  simp only [e2358, e4139, e4140, e4141, e4142, e6571, e7634, e7640, e7643, e7645, e7648, e7655, e7656, e7657, e7658, e7659, e10960, e10962, e10963, e10964] at *
  tauto
theorem n15250 (_v : Vars) (_q : Query _v) (h6571 : (e6571 _v)) : (e7658 _v) := by
  have p15249 := n15249 _v _q 
  have p8447 := n8447 _v _q h6571
  simp only [e2358, e6571, e7645, e7648, e7655, e7656, e7657, e7658, e10960] at *
  tauto
theorem n15251 (_v : Vars) (_q : Query _v) (h6571 : (e6571 _v)) : (e7645 _v) := by
  have p11406 := n11406 _v _q 
  have p15250 := n15250 _v _q h6571
  simp only [e7645, e7648, e7655, e7656, e7657, e7658, e8474] at *
  tauto
theorem n15252 (_v : Vars) (_q : Query _v) (h6571 : (e6571 _v)) : (e7807 _v) := by
  have p4016 := n4016 _v _q 
  have p8447 := n8447 _v _q h6571
  exact FloorCertificate.node_15252 (e2 _v) (e7 _v) (e9 _v) (e110 _v) p4016 p8447
theorem n15253 (_v : Vars) (_q : Query _v) (h6571 : (e6571 _v)) : (e7819 _v) := by
  have p14994 := n14994 _v _q 
  have p15252 := n15252 _v _q h6571
  simp only [e2303, e7807, e7812, e7814, e7816, e7817, e7818, e7819, e11046] at *
  tauto
theorem n15254 (_v : Vars) (_q : Query _v) (h6571 : (e6571 _v)) (h8310 : (e8310 _v)) : (e6746 _v) := by
  have p8447 := n8447 _v _q h6571
  have p11384 := n11384 _v _q h8310
  have p5257 := n5257 _v _q 
  have p4016 := n4016 _v _q 
  exact FloorCertificate.node_15254 (e2 _v) (e7 _v) (e9 _v) (e45 _v) (e110 _v) p8447 p11384 p5257 p4016
theorem n15255 (_v : Vars) (_q : Query _v) (h6571 : (e6571 _v)) (h8310 : (e8310 _v)) : (e7630 _v) := by
  have p15152 := n15152 _v _q 
  have p15254 := n15254 _v _q h6571 h8310
  simp only [e2740, e6746, e7606, e7607, e7608, e7609, e7610, e7630, e10951] at *
  tauto
theorem n15256 (_v : Vars) (_q : Query _v) (h2061 : (e2061 _v)) : (e2536 _v) := by
  have p10893 := n10893 _v _q 
  have p11409 := n11409 _v _q h2061
  exact FloorCertificate.node_15256 (e2 _v) (e17 _v) (e45 _v) (e110 _v) p10893 p11409
theorem n15257 (_v : Vars) (_q : Query _v) (h2061 : (e2061 _v)) : (e3573 _v) := by
  have p14426 := n14426 _v _q 
  have p15256 := n15256 _v _q h2061
  simp only [e2536, e3565, e3566, e3570, e3571, e3572, e3573, e6656, e7176] at *
  tauto
theorem n15258 (_v : Vars) (_q : Query _v) (h2061 : (e2061 _v)) : (e3566 _v) := by
  have p7179 := n7179 _v _q 
  have p15257 := n15257 _v _q h2061
  simp only [e3565, e3566, e3570, e3571, e3572, e3573, e3590] at *
  tauto
theorem n15259 (_v : Vars) (_q : Query _v) (h5195 : (e5195 _v)) : (e4661 _v) := by
  have p14686 := n14686 _v _q 
  have p12844 := n12844 _v _q h5195
  simp only [e2364, e4653, e4654, e4658, e4659, e4660, e4661, e6583, e8163] at *
  tauto
theorem n15260 (_v : Vars) (_q : Query _v) (h5195 : (e5195 _v)) : (e4653 _v) := by
  have p15168 := n15168 _v _q 
  have p15259 := n15259 _v _q h5195
  simp only [e4653, e4654, e4658, e4659, e4660, e4661, e4939] at *
  tauto
theorem n15261 (_v : Vars) (_q : Query _v) (h5195 : (e5195 _v)) : (e2310 _v) := by
  have p12840 := n12840 _v _q h5195
  have p8663 := n8663 _v _q 
  exact FloorCertificate.node_15261 (e2 _v) (e9 _v) (e17 _v) (e110 _v) p12840 p8663
theorem n15262 (_v : Vars) (_q : Query _v) (h5195 : (e5195 _v)) : (e3278 _v) := by
  have p14378 := n14378 _v _q 
  have p15261 := n15261 _v _q h5195
  simp only [e2310, e3270, e3271, e3275, e3276, e3277, e3278, e6555, e6979] at *
  tauto
theorem n15263 (_v : Vars) (_q : Query _v) (h5195 : (e5195 _v)) : (e3271 _v) := by
  have p6982 := n6982 _v _q 
  have p15262 := n15262 _v _q h5195
  simp only [e3270, e3271, e3275, e3276, e3277, e3278, e3288] at *
  tauto
theorem n15264 (_v : Vars) (_q : Query _v) (h5195 : (e5195 _v)) : (e2585 _v) := by
  have p8663 := n8663 _v _q 
  have p8549 := n8549 _v _q h5195
  exact FloorCertificate.node_15264 (e2 _v) (e7 _v) (e17 _v) (e45 _v) (e110 _v) p8663 p8549
theorem n15265 (_v : Vars) (_q : Query _v) (h5195 : (e5195 _v)) : (e4314 _v) := by
  have p14704 := n14704 _v _q 
  have p15264 := n15264 _v _q h5195
  simp only [e2585, e4306, e4307, e4311, e4312, e4313, e4314, e6676, e7836] at *
  tauto
theorem n15266 (_v : Vars) (_q : Query _v)  : (e8489 _v) := by
  simp only [e7932, e7935, e7942, e7943, e7944, e8489] at *
  tauto
theorem n15267 (_v : Vars) (_q : Query _v) (h5195 : (e5195 _v)) (h6480 : (e6480 _v)) : (e7945 _v) := by
  have p15228 := n15228 _v _q 
  have p12845 := n12845 _v _q h5195 h6480
  simp only [e2787, e6772, e7932, e7935, e7942, e7943, e7944, e7945, e11111] at *
  tauto
theorem n15268 (_v : Vars) (_q : Query _v) (h5195 : (e5195 _v)) (h6480 : (e6480 _v)) : (e7935 _v) := by
  have p15266 := n15266 _v _q 
  have p15267 := n15267 _v _q h5195 h6480
  simp only [e7932, e7935, e7942, e7943, e7944, e7945, e8489] at *
  tauto
theorem n15269 (_v : Vars) (_q : Query _v) (h5195 : (e5195 _v)) : (e3573 _v) := by
  have p14426 := n14426 _v _q 
  have p14105 := n14105 _v _q h5195
  simp only [e2536, e3565, e3566, e3570, e3571, e3572, e3573, e6656, e7176] at *
  tauto
theorem n15270 (_v : Vars) (_q : Query _v) (h5195 : (e5195 _v)) : (e7658 _v) := by
  have p15249 := n15249 _v _q 
  have p12839 := n12839 _v _q h5195
  simp only [e2358, e6571, e7645, e7648, e7655, e7656, e7657, e7658, e10960] at *
  tauto
theorem n15271 (_v : Vars) (_q : Query _v) (h6480 : (e6480 _v)) : (e7971 _v) := by
  have p14603 := n14603 _v _q 
  have p8575 := n8575 _v _q h6480
  simp only [e2125, e4475, e4477, e4480, e4481, e6480, e7970, e7971, e7974] at *
  tauto
theorem n15272 (_v : Vars) (_q : Query _v) (h6480 : (e6480 _v)) : (e4477 _v) := by
  have p14858 := n14858 _v _q 
  have p15271 := n15271 _v _q h6480
  simp only [e4475, e4477, e4480, e4481, e7970, e7971, e7980] at *
  tauto
theorem n15273 (_v : Vars) (_q : Query _v) (h5195 : (e5195 _v)) : (e5221 _v) := by
  have p14732 := n14732 _v _q 
  have p8549 := n8549 _v _q h5195
  simp only [e196, e5195, e5208, e5211, e5218, e5219, e5220, e5221, e8668] at *
  tauto
theorem n15274 (_v : Vars) (_q : Query _v) (h5195 : (e5195 _v)) : (e5208 _v) := by
  have p8685 := n8685 _v _q 
  have p15273 := n15273 _v _q h5195
  simp only [e5208, e5211, e5218, e5219, e5220, e5221, e5258] at *
  tauto
theorem n15275 (_v : Vars) (_q : Query _v) (h8310 : (e8310 _v)) : (e7807 _v) := by
  have p11384 := n11384 _v _q h8310
  have p5391 := n5391 _v _q 
  exact FloorCertificate.node_15275 (e2 _v) (e9 _v) (e45 _v) (e110 _v) p11384 p5391
theorem n15276 (_v : Vars) (_q : Query _v) (h8310 : (e8310 _v)) : (e7819 _v) := by
  have p14994 := n14994 _v _q 
  have p15275 := n15275 _v _q h8310
  simp only [e2303, e7807, e7812, e7814, e7816, e7817, e7818, e7819, e11046] at *
  tauto
theorem n15277 (_v : Vars) (_q : Query _v) (h8310 : (e8310 _v)) : (e6772 _v) := by
  have p11384 := n11384 _v _q h8310
  have p5391 := n5391 _v _q 
  have p5257 := n5257 _v _q 
  exact FloorCertificate.node_15277 (e2 _v) (e7 _v) (e9 _v) (e45 _v) (e110 _v) p11384 p5391 p5257
theorem n15278 (_v : Vars) (_q : Query _v) (h8310 : (e8310 _v)) : (e7945 _v) := by
  have p15228 := n15228 _v _q 
  have p15277 := n15277 _v _q h8310
  simp only [e2787, e6772, e7932, e7935, e7942, e7943, e7944, e7945, e11111] at *
  tauto
theorem n15279 (_v : Vars) (_q : Query _v) (h2125 : (e2125 _v)) : (e2061 _v) := by
  have p4016 := n4016 _v _q 
  have p8475 := n8475 _v _q h2125
  exact FloorCertificate.node_15279 (e2 _v) (e7 _v) (e17 _v) (e110 _v) p4016 p8475
theorem n15280 (_v : Vars) (_q : Query _v) (h2125 : (e2125 _v)) : (e4447 _v) := by
  have p14688 := n14688 _v _q 
  have p15279 := n15279 _v _q h2125
  simp only [e2061, e4439, e4440, e4444, e4445, e4446, e4447, e6454, e7961] at *
  tauto
theorem n15281 (_v : Vars) (_q : Query _v) (h2125 : (e2125 _v)) : (e4439 _v) := by
  have p14925 := n14925 _v _q 
  have p15280 := n15280 _v _q h2125
  simp only [e4439, e4440, e4444, e4445, e4446, e4447, e4941] at *
  tauto
end
end Assembly
