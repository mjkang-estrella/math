import Dag102
import generated.th_lemma_4
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n14152 (_v : Vars) (_q : Query _v)  : (e5125 _v) := by
  have p14151 := n14151 _v _q 
  simp only [e48, e51, e52, e57, e58, e59, e60, e70, e72, e75, e76, e5108, e5118, e5119, e5122, e5125, e5127, e8633, e8634, e12966] at *
  tauto
theorem n14153 (_v : Vars) (_q : Query _v)  : (e5141 _v) := by
  have p11585 := n11585 _v _q 
  change ((e81 _v) ↔ (e5135 _v)) at p11585
  simp only [e5141, e5139, e5140, p11585]
theorem n14154 (_v : Vars) (_q : Query _v)  : (e11592 _v) := by
  have p14153 := n14153 _v _q 
  have p12973 := n12973 _v _q 
  change ((e5139 _v) ↔ (e5140 _v)) at p14153
  change ((e5129 _v) ↔ (e8647 _v)) at p12973
  simp only [e11592, e8635, e8648, p14153, p12973]
theorem n14156 (_v : Vars) (_q : Query _v)  : (e14155 _v) := by
  simp only [e5, e6, e10, e12, e41, e46, e78, e79, e87, e88, e89, e91, e94, e95, e100, e5134, e5135, e5138, e5140, e5143, e5145, e5147, e5148, e5149, e5150, e5151, e8647, e8648, e8649, e8650, e8651, e14155] at *
  omega
theorem n14157 (_v : Vars) (_q : Query _v)  : (e11593 _v) := by
  have p14154 := n14154 _v _q 
  have p14156 := n14156 _v _q 
  exact (Iff.trans p14154 p14156)
theorem n14158 (_v : Vars) (_q : Query _v)  : (e8651 _v) := by
  have p8636 := n8636 _v _q 
  have p14157 := n14157 _v _q 
  simp only [e79, e81, e89, e91, e94, e95, e5128, e5129, e5134, e5135, e5138, e5139, e5140, e5143, e5145, e5147, e5148, e5149, e5150, e5151, e8635, e8647, e8649, e8650, e8651, e11593] at *
  tauto
theorem n14159 (_v : Vars) (_q : Query _v)  : (e12979 _v) := by
  have p12236 := n12236 _v _q 
  have p12983 := n12983 _v _q 
  simp only [e102, e103, e104, e105, e106, e113, e114, e118, e120, e128, e130, e133, e134, e5153, e5154, e5155, e5156, e5163, e5164, e5167, e5170, e5172, e8658, e8659, e12979, e12982] at *
  tauto
theorem n14160 (_v : Vars) (_q : Query _v)  : (e5170 _v) := by
  have p14159 := n14159 _v _q 
  simp only [e102, e103, e104, e105, e106, e113, e118, e128, e130, e133, e134, e5153, e5163, e5164, e5167, e5170, e5172, e8658, e8659, e12979] at *
  tauto
theorem n14161 (_v : Vars) (_q : Query _v)  : (e113 _v) := by
  have p8663 := n8663 _v _q 
  have p11376 := n11376 _v _q 
  have p11375 := n11375 _v _q 
  have p10896 := n10896 _v _q 
  exact FloorCertificate.node_14161 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e110 _v) p8663 p11376 p11375 p10896
theorem n14162 (_v : Vars) (_q : Query _v)  : (e118 _v) := by
  have p14160 := n14160 _v _q 
  have p14161 := n14161 _v _q 
  simp only [e102, e103, e104, e105, e106, e113, e118, e5153, e5170] at *
  tauto
theorem n14163 (_v : Vars) (_q : Query _v)  : (e5207 _v) := by
  have p11597 := n11597 _v _q 
  change ((e199 _v) ↔ (e5203 _v)) at p11597
  simp only [e5207, e5196, e5206, p11597]
theorem n14165 (_v : Vars) (_q : Query _v)  : (e14164 _v) := by
  have p14163 := n14163 _v _q 
  have p12988 := n12988 _v _q 
  change ((e5196 _v) ↔ (e5206 _v)) at p14163
  change ((e5197 _v) ↔ (e8668 _v)) at p12988
  simp only [e14164, e5198, e8669, p14163, p12988]
theorem n14167 (_v : Vars) (_q : Query _v)  : (e14166 _v) := by
  simp only [e5, e6, e8, e12, e41, e46, e111, e189, e190, e191, e192, e193, e194, e195, e196, e210, e5193, e5195, e5203, e5206, e5208, e5211, e5218, e5219, e5220, e5221, e5222, e8668, e8669, e8670, e8671, e8672, e14166] at *
  omega
theorem n14169 (_v : Vars) (_q : Query _v)  : (e14168 _v) := by
  have p14165 := n14165 _v _q 
  have p14167 := n14167 _v _q 
  exact (Iff.trans p14165 p14167)
theorem n14170 (_v : Vars) (_q : Query _v)  : (e8672 _v) := by
  have p10359 := n10359 _v _q 
  have p14169 := n14169 _v _q 
  simp only [e191, e192, e193, e194, e196, e198, e199, e5193, e5195, e5196, e5197, e5198, e5203, e5206, e5208, e5211, e5218, e5219, e5220, e5221, e5222, e8668, e8670, e8671, e8672, e14168] at *
  tauto
theorem n14171 (_v : Vars) (_q : Query _v)  : (e5236 _v) := by
  have p11605 := n11605 _v _q 
  change ((e217 _v) ↔ (e5232 _v)) at p11605
  simp only [e5236, e5224, e5235, p11605]
theorem n14173 (_v : Vars) (_q : Query _v)  : (e14172 _v) := by
  have p14171 := n14171 _v _q 
  have p12993 := n12993 _v _q 
  change ((e5224 _v) ↔ (e5235 _v)) at p14171
  change ((e5225 _v) ↔ (e8677 _v)) at p12993
  simp only [e14172, e5226, e8678, p14171, p12993]
theorem n14175 (_v : Vars) (_q : Query _v)  : (e14174 _v) := by
  simp only [e5, e6, e10, e12, e41, e46, e111, e212, e213, e214, e223, e224, e225, e227, e230, e231, e5223, e5231, e5232, e5235, e5237, e5240, e5247, e5248, e5249, e5250, e5251, e8677, e8678, e8679, e8680, e8681, e14174] at *
  omega
theorem n14177 (_v : Vars) (_q : Query _v)  : (e14176 _v) := by
  have p14173 := n14173 _v _q 
  have p14175 := n14175 _v _q 
  exact (Iff.trans p14173 p14175)
theorem n14178 (_v : Vars) (_q : Query _v)  : (e8681 _v) := by
  have p10447 := n10447 _v _q 
  have p14177 := n14177 _v _q 
  simp only [e214, e216, e217, e225, e227, e230, e231, e5223, e5224, e5225, e5226, e5231, e5232, e5235, e5237, e5240, e5247, e5248, e5249, e5250, e5251, e8677, e8679, e8680, e8681, e14176] at *
  tauto
theorem n14179 (_v : Vars) (_q : Query _v)  : (e12999 _v) := by
  have p12122 := n12122 _v _q 
  have p13003 := n13003 _v _q 
  simp only [e260, e261, e262, e263, e264, e269, e270, e274, e276, e284, e286, e289, e290, e5259, e5260, e5261, e5262, e5269, e5270, e5273, e5276, e5278, e8694, e8695, e12999, e13002] at *
  tauto
theorem n14180 (_v : Vars) (_q : Query _v)  : (e5276 _v) := by
  have p14179 := n14179 _v _q 
  simp only [e260, e261, e262, e263, e264, e269, e274, e284, e286, e289, e290, e5259, e5269, e5270, e5273, e5276, e5278, e8694, e8695, e12999] at *
  tauto
theorem n14181 (_v : Vars) (_q : Query _v)  : (e269 _v) := by
  have p11376 := n11376 _v _q 
  have p11375 := n11375 _v _q 
  have p8663 := n8663 _v _q 
  exact FloorCertificate.node_14181 (e2 _v) (e7 _v) (e17 _v) (e110 _v) p11376 p11375 p8663
theorem n14182 (_v : Vars) (_q : Query _v)  : (e274 _v) := by
  have p14180 := n14180 _v _q 
  have p14181 := n14181 _v _q 
  simp only [e260, e261, e262, e263, e264, e269, e274, e5259, e5276] at *
  tauto
theorem n14183 (_v : Vars) (_q : Query _v)  : (e13009 _v) := by
  have p10212 := n10212 _v _q 
  have p13013 := n13013 _v _q 
  simp only [e298, e299, e300, e301, e302, e305, e306, e310, e312, e320, e322, e325, e326, e5279, e5280, e5281, e5282, e5289, e5290, e5293, e5296, e5298, e8702, e8703, e13009, e13012] at *
  tauto
theorem n14184 (_v : Vars) (_q : Query _v)  : (e5296 _v) := by
  have p14183 := n14183 _v _q 
  simp only [e298, e299, e300, e301, e302, e305, e310, e320, e322, e325, e326, e5279, e5289, e5290, e5293, e5296, e5298, e8702, e8703, e13009] at *
  tauto
theorem n14185 (_v : Vars) (_q : Query _v)  : (e305 _v) := by
  have p8663 := n8663 _v _q 
  have p10896 := n10896 _v _q 
  have p331 := n331 _v _q 
  exact FloorCertificate.node_14185 (e2 _v) (e9 _v) (e17 _v) p8663 p10896 p331
theorem n14186 (_v : Vars) (_q : Query _v)  : (e310 _v) := by
  have p14184 := n14184 _v _q 
  have p14185 := n14185 _v _q 
  simp only [e298, e299, e300, e301, e302, e305, e310, e5279, e5296] at *
  tauto
theorem n14187 (_v : Vars) (_q : Query _v)  : (e13019 _v) := by
  have p10158 := n10158 _v _q 
  have p13023 := n13023 _v _q 
  simp only [e333, e334, e335, e336, e337, e340, e341, e345, e347, e355, e357, e360, e361, e5299, e5300, e5301, e5302, e5309, e5310, e5313, e5316, e5318, e8710, e8711, e13019, e13022] at *
  tauto
theorem n14188 (_v : Vars) (_q : Query _v)  : (e5316 _v) := by
  have p14187 := n14187 _v _q 
  simp only [e333, e334, e335, e336, e337, e340, e345, e355, e357, e360, e361, e5299, e5309, e5310, e5313, e5316, e5318, e8710, e8711, e13019] at *
  tauto
theorem n14189 (_v : Vars) (_q : Query _v)  : (e340 _v) := by
  have p8663 := n8663 _v _q 
  have p11375 := n11375 _v _q 
  have p331 := n331 _v _q 
  exact FloorCertificate.node_14189 (e2 _v) (e17 _v) (e110 _v) p8663 p11375 p331
theorem n14190 (_v : Vars) (_q : Query _v)  : (e345 _v) := by
  have p14188 := n14188 _v _q 
  have p14189 := n14189 _v _q 
  simp only [e333, e334, e335, e336, e337, e340, e345, e5299, e5316] at *
  tauto
theorem n14191 (_v : Vars) (_q : Query _v)  : (e13029 _v) := by
  have p12284 := n12284 _v _q 
  have p13033 := n13033 _v _q 
  simp only [e363, e364, e365, e366, e367, e370, e371, e375, e377, e385, e387, e390, e391, e5319, e5320, e5321, e5322, e5329, e5330, e5333, e5336, e5338, e8718, e8719, e13029, e13032] at *
  tauto
theorem n14192 (_v : Vars) (_q : Query _v)  : (e5336 _v) := by
  have p14191 := n14191 _v _q 
  simp only [e363, e364, e365, e366, e367, e370, e375, e385, e387, e390, e391, e5319, e5329, e5330, e5333, e5336, e5338, e8718, e8719, e13029] at *
  tauto
theorem n14193 (_v : Vars) (_q : Query _v)  : (e370 _v) := by
  have p10893 := n10893 _v _q 
  have p8663 := n8663 _v _q 
  have p11376 := n11376 _v _q 
  have p331 := n331 _v _q 
  exact FloorCertificate.node_14193 (e2 _v) (e7 _v) (e17 _v) (e45 _v) p10893 p8663 p11376 p331
theorem n14194 (_v : Vars) (_q : Query _v)  : (e375 _v) := by
  have p14192 := n14192 _v _q 
  have p14193 := n14193 _v _q 
  simp only [e363, e364, e365, e366, e367, e370, e375, e5319, e5336] at *
  tauto
theorem n14195 (_v : Vars) (_q : Query _v)  : (e11624 _v) := by
  have p13039 := n13039 _v _q 
  have p11623 := n11623 _v _q 
  exact (Iff.trans p13039 p11623)
theorem n14196 (_v : Vars) (_q : Query _v)  : (e8732 _v) := by
  have p5348 := n5348 _v _q 
  have p14195 := n14195 _v _q 
  simp only [e404, e405, e406, e407, e408, e411, e412, e414, e415, e416, e420, e428, e430, e433, e434, e5346, e5347, e5355, e5356, e5359, e8722, e8729, e8730, e8731, e8732, e11624] at *
  tauto
theorem n14197 (_v : Vars) (_q : Query _v)  : (e8722 _v) := by
  have p14196 := n14196 _v _q 
  simp only [e404, e405, e406, e407, e408, e411, e412, e420, e428, e430, e433, e434, e5355, e5356, e5359, e8722, e8729, e8730, e8731, e8732] at *
  tauto
theorem n14198 (_v : Vars) (_q : Query _v)  : (e420 _v) := by
  have p14197 := n14197 _v _q 
  have p11625 := n11625 _v _q 
  simp only [e404, e405, e406, e407, e408, e411, e412, e420, e8722] at *
  tauto
theorem n14199 (_v : Vars) (_q : Query _v)  : (e5374 _v) := by
  have p11627 := n11627 _v _q 
  change ((e446 _v) ↔ (e5370 _v)) at p11627
  simp only [e5374, e5363, e5373, p11627]
theorem n14201 (_v : Vars) (_q : Query _v)  : (e14200 _v) := by
  have p14199 := n14199 _v _q 
  have p13044 := n13044 _v _q 
  change ((e5363 _v) ↔ (e5373 _v)) at p14199
  change ((e5364 _v) ↔ (e8737 _v)) at p13044
  simp only [e14200, e5365, e8738, p14199, p13044]
theorem n14203 (_v : Vars) (_q : Query _v)  : (e14202 _v) := by
  simp only [e5, e6, e8, e10, e12, e41, e46, e111, e435, e436, e438, e439, e440, e441, e442, e443, e457, e5360, e5362, e5370, e5373, e5375, e5378, e5385, e5386, e5387, e5388, e5389, e8737, e8738, e8739, e8740, e8741, e14202] at *
  omega
theorem n14205 (_v : Vars) (_q : Query _v)  : (e14204 _v) := by
  have p14201 := n14201 _v _q 
  have p14203 := n14203 _v _q 
  exact (Iff.trans p14201 p14203)
theorem n14206 (_v : Vars) (_q : Query _v)  : (e8741 _v) := by
  have p10485 := n10485 _v _q 
  have p14205 := n14205 _v _q 
  simp only [e436, e440, e441, e442, e443, e445, e446, e5360, e5362, e5363, e5364, e5365, e5370, e5373, e5375, e5378, e5385, e5386, e5387, e5388, e5389, e8737, e8739, e8740, e8741, e14204] at *
  tauto
end
end Assembly
