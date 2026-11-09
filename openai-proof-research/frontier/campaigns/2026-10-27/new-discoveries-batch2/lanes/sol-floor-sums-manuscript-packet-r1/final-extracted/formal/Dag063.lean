import Dag062
import generated.th_lemma_1
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n11179 (_v : Vars) (_q : Query _v)  : (e11178 _v) := by
  have p8078 := n8078 _v _q 
  have p8082 := n8082 _v _q 
  exact (Iff.trans p8078 p8082)
theorem n11180 (_v : Vars) (_q : Query _v)  : (e8086 _v) := by
  simp only [e5, e6, e10, e12, e36, e41, e2173, e4586, e4587, e4604, e8086] at *
  omega
theorem n11181 (_v : Vars) (_q : Query _v)  : (e8087 _v) := by
  simp only [e5, e6, e10, e12, e36, e41, e2173, e4586, e4588, e4605, e8087] at *
  omega
theorem n11183 (_v : Vars) (_q : Query _v)  : (e11182 _v) := by
  have p11180 := n11180 _v _q 
  have p11181 := n11181 _v _q 
  change ((e4604 _v) ↔ (e4587 _v)) at p11180
  change ((e4605 _v) ↔ (e4588 _v)) at p11181
  simp only [e11182, e4606, e8088, p11180, p11181]
theorem n11184 (_v : Vars) (_q : Query _v)  : (e8090 _v) := by
  simp only [e5, e6, e10, e12, e41, e4586, e4587, e4588, e8070, e8071, e8072, e8088, e8089, e8090] at *
  omega
theorem n11185 (_v : Vars) (_q : Query _v)  : (e8091 _v) := by
  have p11183 := n11183 _v _q 
  have p11184 := n11184 _v _q 
  exact (Iff.trans p11183 p11184)
theorem n11192 (_v : Vars) (_q : Query _v)  : (e11191 _v) := by
  have p4615 := n4615 _v _q 
  have p8098 := n8098 _v _q 
  exact (Iff.trans p4615 p8098)
theorem n11194 (_v : Vars) (_q : Query _v)  : (e11193 _v) := by
  have p11192 := n11192 _v _q 
  change ((e4612 _v) ↔ (e4616 _v)) at p11192
  simp only [e11193, e6502, e8109, p11192]
theorem n11196 (_v : Vars) (_q : Query _v)  : (e11195 _v) := by
  have p8102 := n8102 _v _q 
  have p8105 := n8105 _v _q 
  exact (Iff.trans p8102 p8105)
theorem n11200 (_v : Vars) (_q : Query _v)  : (e11199 _v) := by
  have p8120 := n8120 _v _q 
  have p8124 := n8124 _v _q 
  exact (Iff.trans p8120 p8124)
theorem n11201 (_v : Vars) (_q : Query _v)  : (e8128 _v) := by
  simp only [e5, e6, e12, e36, e41, e111, e2055, e4626, e4627, e4644, e8128] at *
  omega
theorem n11202 (_v : Vars) (_q : Query _v)  : (e8129 _v) := by
  simp only [e5, e6, e12, e36, e41, e111, e2055, e4626, e4628, e4645, e8129] at *
  omega
theorem n11204 (_v : Vars) (_q : Query _v)  : (e11203 _v) := by
  have p11201 := n11201 _v _q 
  have p11202 := n11202 _v _q 
  change ((e4644 _v) ↔ (e4627 _v)) at p11201
  change ((e4645 _v) ↔ (e4628 _v)) at p11202
  simp only [e11203, e4646, e8130, p11201, p11202]
theorem n11205 (_v : Vars) (_q : Query _v)  : (e8132 _v) := by
  simp only [e5, e6, e12, e41, e111, e4626, e4627, e4628, e8112, e8113, e8114, e8130, e8131, e8132] at *
  omega
theorem n11206 (_v : Vars) (_q : Query _v)  : (e8133 _v) := by
  have p11204 := n11204 _v _q 
  have p11205 := n11205 _v _q 
  exact (Iff.trans p11204 p11205)
theorem n11215 (_v : Vars) (_q : Query _v)  : (e11214 _v) := by
  have p8139 := n8139 _v _q 
  have p5255 := n5255 _v _q 
  exact FloorCertificate.node_11215 (e9 _v) (e110 _v) p8139 p5255
theorem n11217 (_v : Vars) (_q : Query _v)  : (e11216 _v) := by
  have p4657 := n4657 _v _q 
  have p8152 := n8152 _v _q 
  exact (Iff.trans p4657 p8152)
theorem n11219 (_v : Vars) (_q : Query _v)  : (e11218 _v) := by
  have p11217 := n11217 _v _q 
  change ((e4652 _v) ↔ (e4661 _v)) at p11217
  simp only [e11218, e6584, e8163, p11217]
theorem n11221 (_v : Vars) (_q : Query _v)  : (e11220 _v) := by
  have p8156 := n8156 _v _q 
  have p8159 := n8159 _v _q 
  exact (Iff.trans p8156 p8159)
theorem n11225 (_v : Vars) (_q : Query _v)  : (e11224 _v) := by
  have p4682 := n4682 _v _q 
  have p8169 := n8169 _v _q 
  exact (Iff.trans p4682 p8169)
theorem n11227 (_v : Vars) (_q : Query _v)  : (e11226 _v) := by
  have p11225 := n11225 _v _q 
  change ((e4677 _v) ↔ (e4686 _v)) at p11225
  simp only [e11226, e6526, e8180, p11225]
theorem n11229 (_v : Vars) (_q : Query _v)  : (e11228 _v) := by
  have p8173 := n8173 _v _q 
  have p8176 := n8176 _v _q 
  exact (Iff.trans p8173 p8176)
theorem n11233 (_v : Vars) (_q : Query _v)  : (e11232 _v) := by
  have p8192 := n8192 _v _q 
  have p8196 := n8196 _v _q 
  exact (Iff.trans p8192 p8196)
theorem n11234 (_v : Vars) (_q : Query _v)  : (e8202 _v) := by
  simp only [e5, e6, e8, e10, e12, e41, e43, e44, e760, e761, e2248, e4697, e4713, e8183, e8202] at *
  omega
theorem n11235 (_v : Vars) (_q : Query _v)  : (e8203 _v) := by
  simp only [e5, e6, e8, e10, e12, e41, e43, e44, e760, e761, e2248, e4697, e4714, e8185, e8203] at *
  omega
theorem n11238 (_v : Vars) (_q : Query _v)  : (e11237 _v) := by
  have p11234 := n11234 _v _q 
  have p11235 := n11235 _v _q 
  change ((e4713 _v) ↔ (e8183 _v)) at p11234
  change ((e4714 _v) ↔ (e8185 _v)) at p11235
  simp only [e11237, e4715, e11236, p11234, p11235]
theorem n11240 (_v : Vars) (_q : Query _v)  : (e11239 _v) := by
  simp only [e5, e6, e8, e10, e12, e41, e43, e44, e4697, e8183, e8184, e8185, e8186, e8187, e8204, e11236, e11239] at *
  omega
theorem n11248 (_v : Vars) (_q : Query _v)  : (e11247 _v) := by
  have p4727 := n4727 _v _q 
  have p8209 := n8209 _v _q 
  exact (Iff.trans p4727 p8209)
theorem n11250 (_v : Vars) (_q : Query _v)  : (e11249 _v) := by
  have p11248 := n11248 _v _q 
  change ((e4722 _v) ↔ (e4731 _v)) at p11248
  simp only [e11249, e6532, e8220, p11248]
theorem n11252 (_v : Vars) (_q : Query _v)  : (e11251 _v) := by
  have p8213 := n8213 _v _q 
  have p8216 := n8216 _v _q 
  exact (Iff.trans p8213 p8216)
theorem n11256 (_v : Vars) (_q : Query _v)  : (e11255 _v) := by
  have p4751 := n4751 _v _q 
  have p8227 := n8227 _v _q 
  exact (Iff.trans p4751 p8227)
theorem n11258 (_v : Vars) (_q : Query _v)  : (e11257 _v) := by
  have p11256 := n11256 _v _q 
  change ((e4746 _v) ↔ (e4755 _v)) at p11256
  simp only [e11257, e6592, e8238, p11256]
theorem n11260 (_v : Vars) (_q : Query _v)  : (e11259 _v) := by
  have p8231 := n8231 _v _q 
  have p8234 := n8234 _v _q 
  exact (Iff.trans p8231 p8234)
theorem n11264 (_v : Vars) (_q : Query _v)  : (e11263 _v) := by
  have p8250 := n8250 _v _q 
  have p8254 := n8254 _v _q 
  exact (Iff.trans p8250 p8254)
theorem n11266 (_v : Vars) (_q : Query _v)  : (e11265 _v) := by
  simp only [e5, e6, e8, e10, e12, e41, e111, e266, e267, e4765, e8241, e8242, e8243, e8244, e8245, e8262, e8265, e11265] at *
  omega
theorem n11273 (_v : Vars) (_q : Query _v)  : (e11272 _v) := by
  have p4794 := n4794 _v _q 
  have p8270 := n8270 _v _q 
  exact (Iff.trans p4794 p8270)
theorem n11275 (_v : Vars) (_q : Query _v)  : (e11274 _v) := by
  have p11273 := n11273 _v _q 
  change ((e4789 _v) ↔ (e4798 _v)) at p11273
  simp only [e11274, e6631, e8281, p11273]
theorem n11277 (_v : Vars) (_q : Query _v)  : (e11276 _v) := by
  have p8274 := n8274 _v _q 
  have p8277 := n8277 _v _q 
  exact (Iff.trans p8274 p8277)
theorem n11281 (_v : Vars) (_q : Query _v)  : (e11280 _v) := by
  have p4820 := n4820 _v _q 
  have p8287 := n8287 _v _q 
  exact (Iff.trans p4820 p8287)
theorem n11283 (_v : Vars) (_q : Query _v)  : (e11282 _v) := by
  have p11281 := n11281 _v _q 
  change ((e4815 _v) ↔ (e4824 _v)) at p11281
  simp only [e11282, e6651, e8298, p11281]
theorem n11285 (_v : Vars) (_q : Query _v)  : (e11284 _v) := by
  have p8291 := n8291 _v _q 
  have p8294 := n8294 _v _q 
  exact (Iff.trans p8291 p8294)
theorem n11289 (_v : Vars) (_q : Query _v)  : (e11288 _v) := by
  have p8306 := n8306 _v _q 
  have p8309 := n8309 _v _q 
  exact (Iff.trans p8306 p8309)
theorem n11290 (_v : Vars) (_q : Query _v)  : (e8316 _v) := by
  simp only [e5, e6, e12, e36, e41, e46, e111, e2516, e4849, e4852, e8315, e8316] at *
  omega
theorem n11291 (_v : Vars) (_q : Query _v)  : (e8318 _v) := by
  simp only [e5, e6, e12, e36, e41, e46, e111, e2516, e4850, e4852, e8317, e8318] at *
  omega
theorem n11294 (_v : Vars) (_q : Query _v)  : (e11293 _v) := by
  have p11290 := n11290 _v _q 
  have p11291 := n11291 _v _q 
  change ((e4849 _v) ↔ (e8315 _v)) at p11290
  change ((e4850 _v) ↔ (e8317 _v)) at p11291
  simp only [e11293, e4851, e11292, p11290, p11291]
end
end Assembly
