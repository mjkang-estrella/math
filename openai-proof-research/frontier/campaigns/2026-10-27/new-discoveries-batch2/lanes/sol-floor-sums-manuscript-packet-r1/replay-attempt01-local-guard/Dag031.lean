import Dag030
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n8176 (_v : Vars) (_q : Query _v)  : (e8175 _v) := by
  simp only [e5, e6, e12, e4671, e4672, e4673, e4674, e4675, e4676, e4695, e8166, e8174, e8175] at *
  omega
theorem n8189 (_v : Vars) (_q : Query _v)  : (e4707 _v) := by
  simp only [e5, e6, e12, e4699, e4704, e4705, e4706, e4707] at *
  omega
theorem n8190 (_v : Vars) (_q : Query _v)  : (e4709 _v) := by
  simp only [e5, e6, e12, e4700, e4704, e4705, e4708, e4709] at *
  omega
theorem n8192 (_v : Vars) (_q : Query _v)  : (e8191 _v) := by
  have p8189 := n8189 _v _q 
  have p8190 := n8190 _v _q 
  change ((e4699 _v) ↔ (e4706 _v)) at p8189
  change ((e4700 _v) ↔ (e4708 _v)) at p8190
  simp only [e8191, e4701, e4710, p8189, p8190]
theorem n8196 (_v : Vars) (_q : Query _v)  : (e8195 _v) := by
  simp only [e5, e6, e12, e4704, e4705, e4706, e4708, e4710, e4711, e4712, e8193, e8194, e8195] at *
  omega
theorem n8209 (_v : Vars) (_q : Query _v)  : (e8208 _v) := by
  simp only [e12, e4723, e4724, e4725, e4728, e4729, e4730, e4731, e8208] at *
  omega
theorem n8210 (_v : Vars) (_q : Query _v)  : (e4738 _v) := by
  simp only [e5, e6, e12, e4716, e4717, e4718, e4733, e4738] at *
  omega
theorem n8211 (_v : Vars) (_q : Query _v)  : (e4739 _v) := by
  simp only [e5, e6, e12, e4716, e4717, e4720, e4734, e4739] at *
  omega
theorem n8213 (_v : Vars) (_q : Query _v)  : (e8212 _v) := by
  have p8210 := n8210 _v _q 
  have p8211 := n8211 _v _q 
  change ((e4733 _v) ↔ (e4718 _v)) at p8210
  change ((e4734 _v) ↔ (e4720 _v)) at p8211
  simp only [e8212, e4735, e4740, p8210, p8211]
theorem n8216 (_v : Vars) (_q : Query _v)  : (e8215 _v) := by
  simp only [e5, e6, e12, e4716, e4717, e4718, e4719, e4720, e4721, e4740, e8206, e8214, e8215] at *
  omega
theorem n8227 (_v : Vars) (_q : Query _v)  : (e8226 _v) := by
  simp only [e12, e4747, e4748, e4749, e4752, e4753, e4754, e4755, e8226] at *
  omega
theorem n8228 (_v : Vars) (_q : Query _v)  : (e4762 _v) := by
  simp only [e5, e6, e12, e2954, e4741, e4742, e4757, e4762] at *
  omega
theorem n8229 (_v : Vars) (_q : Query _v)  : (e4763 _v) := by
  simp only [e5, e6, e12, e2954, e4741, e4744, e4758, e4763] at *
  omega
theorem n8231 (_v : Vars) (_q : Query _v)  : (e8230 _v) := by
  have p8228 := n8228 _v _q 
  have p8229 := n8229 _v _q 
  change ((e4757 _v) ↔ (e4742 _v)) at p8228
  change ((e4758 _v) ↔ (e4744 _v)) at p8229
  simp only [e8230, e4759, e4764, p8228, p8229]
theorem n8234 (_v : Vars) (_q : Query _v)  : (e8233 _v) := by
  simp only [e5, e6, e12, e2954, e4741, e4742, e4743, e4744, e4745, e4764, e8224, e8232, e8233] at *
  omega
theorem n8247 (_v : Vars) (_q : Query _v)  : (e4775 _v) := by
  simp only [e5, e6, e12, e4767, e4772, e4773, e4774, e4775] at *
  omega
theorem n8248 (_v : Vars) (_q : Query _v)  : (e4777 _v) := by
  simp only [e5, e6, e12, e4768, e4772, e4773, e4776, e4777] at *
  omega
theorem n8250 (_v : Vars) (_q : Query _v)  : (e8249 _v) := by
  have p8247 := n8247 _v _q 
  have p8248 := n8248 _v _q 
  change ((e4767 _v) ↔ (e4774 _v)) at p8247
  change ((e4768 _v) ↔ (e4776 _v)) at p8248
  simp only [e8249, e4769, e4778, p8247, p8248]
theorem n8254 (_v : Vars) (_q : Query _v)  : (e8253 _v) := by
  simp only [e5, e6, e12, e4772, e4773, e4774, e4776, e4778, e4779, e4780, e8251, e8252, e8253] at *
  omega
theorem n8258 (_v : Vars) (_q : Query _v)  : (e8257 _v) := by
  simp only [e5, e6, e8, e10, e12, e41, e111, e266, e267, e781, e782, e2372, e4765, e4781, e8241, e8257] at *
  omega
theorem n8260 (_v : Vars) (_q : Query _v)  : (e8259 _v) := by
  simp only [e5, e6, e8, e10, e12, e41, e111, e266, e267, e781, e782, e2372, e4765, e4782, e8243, e8259] at *
  omega
theorem n8264 (_v : Vars) (_q : Query _v)  : (e8263 _v) := by
  have p8258 := n8258 _v _q 
  have p8260 := n8260 _v _q 
  change ((e4781 _v) ↔ (e8241 _v)) at p8258
  change ((e4782 _v) ↔ (e8243 _v)) at p8260
  simp only [e8263, e8261, e8262, p8258, p8260]
theorem n8270 (_v : Vars) (_q : Query _v)  : (e8269 _v) := by
  simp only [e12, e4790, e4791, e4792, e4795, e4796, e4797, e4798, e8269] at *
  omega
theorem n8271 (_v : Vars) (_q : Query _v)  : (e4805 _v) := by
  simp only [e5, e6, e12, e4783, e4784, e4785, e4800, e4805] at *
  omega
theorem n8272 (_v : Vars) (_q : Query _v)  : (e4806 _v) := by
  simp only [e5, e6, e12, e4783, e4784, e4787, e4801, e4806] at *
  omega
theorem n8274 (_v : Vars) (_q : Query _v)  : (e8273 _v) := by
  have p8271 := n8271 _v _q 
  have p8272 := n8272 _v _q 
  change ((e4800 _v) ↔ (e4785 _v)) at p8271
  change ((e4801 _v) ↔ (e4787 _v)) at p8272
  simp only [e8273, e4802, e4807, p8271, p8272]
theorem n8277 (_v : Vars) (_q : Query _v)  : (e8276 _v) := by
  simp only [e5, e6, e12, e4783, e4784, e4785, e4786, e4787, e4788, e4807, e8267, e8275, e8276] at *
  omega
theorem n8287 (_v : Vars) (_q : Query _v)  : (e8286 _v) := by
  simp only [e12, e4816, e4817, e4818, e4821, e4822, e4823, e4824, e8286] at *
  omega
theorem n8288 (_v : Vars) (_q : Query _v)  : (e4831 _v) := by
  simp only [e5, e6, e12, e4809, e4810, e4811, e4826, e4831] at *
  omega
theorem n8289 (_v : Vars) (_q : Query _v)  : (e4832 _v) := by
  simp only [e5, e6, e12, e4809, e4810, e4813, e4827, e4832] at *
  omega
theorem n8291 (_v : Vars) (_q : Query _v)  : (e8290 _v) := by
  have p8288 := n8288 _v _q 
  have p8289 := n8289 _v _q 
  change ((e4826 _v) ↔ (e4811 _v)) at p8288
  change ((e4827 _v) ↔ (e4813 _v)) at p8289
  simp only [e8290, e4828, e4833, p8288, p8289]
theorem n8294 (_v : Vars) (_q : Query _v)  : (e8293 _v) := by
  simp only [e5, e6, e12, e4809, e4810, e4811, e4812, e4813, e4814, e4833, e8284, e8292, e8293] at *
  omega
theorem n8303 (_v : Vars) (_q : Query _v)  : (e4846 _v) := by
  simp only [e5, e6, e12, e4834, e4835, e4836, e4841, e4846] at *
  omega
theorem n8304 (_v : Vars) (_q : Query _v)  : (e4847 _v) := by
  simp only [e5, e6, e12, e4834, e4835, e4838, e4842, e4847] at *
  omega
theorem n8306 (_v : Vars) (_q : Query _v)  : (e8305 _v) := by
  have p8303 := n8303 _v _q 
  have p8304 := n8304 _v _q 
  change ((e4841 _v) ↔ (e4836 _v)) at p8303
  change ((e4842 _v) ↔ (e4838 _v)) at p8304
  simp only [e8305, e4843, e4848, p8303, p8304]
theorem n8309 (_v : Vars) (_q : Query _v)  : (e8308 _v) := by
  simp only [e5, e6, e12, e4834, e4835, e4836, e4837, e4838, e4839, e4848, e8301, e8307, e8308] at *
  omega
theorem n8326 (_v : Vars) (_q : Query _v)  : (e4865 _v) := by
  simp only [e5, e6, e12, e4853, e4854, e4855, e4860, e4865] at *
  omega
theorem n8327 (_v : Vars) (_q : Query _v)  : (e4866 _v) := by
  simp only [e5, e6, e12, e4853, e4854, e4857, e4861, e4866] at *
  omega
theorem n8329 (_v : Vars) (_q : Query _v)  : (e8328 _v) := by
  have p8326 := n8326 _v _q 
  have p8327 := n8327 _v _q 
  change ((e4860 _v) ↔ (e4855 _v)) at p8326
  change ((e4861 _v) ↔ (e4857 _v)) at p8327
  simp only [e8328, e4862, e4867, p8326, p8327]
theorem n8332 (_v : Vars) (_q : Query _v)  : (e8331 _v) := by
  simp only [e5, e6, e12, e4853, e4854, e4855, e4856, e4857, e4858, e4867, e8324, e8330, e8331] at *
  omega
theorem n8337 (_v : Vars) (_q : Query _v)  : (e8336 _v) := by
  simp only [e5, e6, e8, e12, e41, e43, e44, e46, e111, e760, e761, e2580, e4868, e4870, e8335, e8336] at *
  omega
theorem n8340 (_v : Vars) (_q : Query _v)  : (e8339 _v) := by
  simp only [e5, e6, e8, e12, e41, e43, e44, e46, e111, e760, e761, e2580, e4869, e4870, e8338, e8339] at *
  omega
theorem n8344 (_v : Vars) (_q : Query _v)  : (e8343 _v) := by
  have p8337 := n8337 _v _q 
  have p8340 := n8340 _v _q 
  change ((e4868 _v) ↔ (e8335 _v)) at p8337
  change ((e4869 _v) ↔ (e8338 _v)) at p8340
  simp only [e8343, e8341, e8342, p8337, p8340]
theorem n8353 (_v : Vars) (_q : Query _v)  : (e8352 _v) := by
  simp only [e12, e4877, e4878, e4879, e4882, e4883, e4884, e4885, e8352] at *
  omega
theorem n8354 (_v : Vars) (_q : Query _v)  : (e4892 _v) := by
  simp only [e5, e6, e12, e2987, e4871, e4872, e4887, e4892] at *
  omega
end
end Assembly
