import Dag014
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n5325 (_v : Vars) (_q : Query _v)  : (e386 _v) := by
  simp only [e5, e6, e12, e378, e383, e384, e385, e386] at *
  omega
theorem n5326 (_v : Vars) (_q : Query _v)  : (e388 _v) := by
  simp only [e5, e6, e12, e379, e383, e384, e387, e388] at *
  omega
theorem n5328 (_v : Vars) (_q : Query _v)  : (e5327 _v) := by
  have p5325 := n5325 _v _q 
  have p5326 := n5326 _v _q 
  change ((e378 _v) ↔ (e385 _v)) at p5325
  change ((e379 _v) ↔ (e387 _v)) at p5326
  simp only [e5327, e380, e389, p5325, p5326]
theorem n5332 (_v : Vars) (_q : Query _v)  : (e5331 _v) := by
  simp only [e5, e6, e12, e383, e384, e385, e387, e389, e390, e391, e5329, e5330, e5331] at *
  omega
theorem n5339 (_v : Vars) (_q : Query _v)  : (e392 _v) := by
  exact ((((((((((((((((_q).2).2).2).2).2).2).2).2).2).2).2).2).2).2).2).1
theorem n5340 (_v : Vars) (_q : Query _v)  : (e394 _v) := by
  have p5339 := n5339 _v _q 
  have p396 := n396 _v _q 
  simp only [e392, e393, e394, e395] at *
  tauto
theorem n5341 (_v : Vars) (_q : Query _v)  : (e394 _v) := by
  have p5340 := n5340 _v _q 
  have p398 := n398 _v _q 
  simp only [e393, e394, e397] at *
  tauto
theorem n5342 (_v : Vars) (_q : Query _v)  : (e401 _v) := by
  simp only [e5, e6, e12, e46, e393, e399, e400, e401] at *
  omega
theorem n5344 (_v : Vars) (_q : Query _v)  : (e5343 _v) := by
  have p5342 := n5342 _v _q 
  change ((e393 _v) ↔ (e400 _v)) at p5342
  simp only [e5343, e394, e402, p5342]
theorem n5348 (_v : Vars) (_q : Query _v)  : (e5347 _v) := by
  simp only [e403, e411, e412, e413, e414, e415, e416, e5346, e5347] at *
  by_cases hc : ((e410 _v) ≥ (e12 _v)) <;> simp [hc]
theorem n5350 (_v : Vars) (_q : Query _v)  : (e5349 _v) := by
  simp only [e12, e404, e405, e406, e407, e408, e417, e420, e5349] at *
  omega
theorem n5351 (_v : Vars) (_q : Query _v)  : (e429 _v) := by
  simp only [e5, e6, e12, e421, e426, e427, e428, e429] at *
  omega
theorem n5352 (_v : Vars) (_q : Query _v)  : (e431 _v) := by
  simp only [e5, e6, e12, e422, e426, e427, e430, e431] at *
  omega
theorem n5354 (_v : Vars) (_q : Query _v)  : (e5353 _v) := by
  have p5351 := n5351 _v _q 
  have p5352 := n5352 _v _q 
  change ((e421 _v) ↔ (e428 _v)) at p5351
  change ((e422 _v) ↔ (e430 _v)) at p5352
  simp only [e5353, e423, e432, p5351, p5352]
theorem n5358 (_v : Vars) (_q : Query _v)  : (e5357 _v) := by
  simp only [e5, e6, e12, e426, e427, e428, e430, e432, e433, e434, e5355, e5356, e5357] at *
  omega
theorem n5366 (_v : Vars) (_q : Query _v)  : (e452 _v) := by
  simp only [e5, e6, e12, e438, e439, e440, e447, e452] at *
  omega
theorem n5367 (_v : Vars) (_q : Query _v)  : (e453 _v) := by
  simp only [e5, e6, e12, e438, e439, e442, e448, e453] at *
  omega
theorem n5369 (_v : Vars) (_q : Query _v)  : (e5368 _v) := by
  have p5366 := n5366 _v _q 
  have p5367 := n5367 _v _q 
  change ((e447 _v) ↔ (e440 _v)) at p5366
  change ((e448 _v) ↔ (e442 _v)) at p5367
  simp only [e5368, e449, e454, p5366, p5367]
theorem n5372 (_v : Vars) (_q : Query _v)  : (e5371 _v) := by
  simp only [e5, e6, e12, e438, e439, e440, e441, e442, e443, e454, e5360, e5370, e5371] at *
  omega
theorem n5377 (_v : Vars) (_q : Query _v)  : (e5376 _v) := by
  simp only [e5, e6, e8, e10, e12, e36, e41, e46, e111, e444, e455, e457, e5375, e5376] at *
  omega
theorem n5380 (_v : Vars) (_q : Query _v)  : (e5379 _v) := by
  simp only [e5, e6, e8, e10, e12, e36, e41, e46, e111, e444, e456, e457, e5378, e5379] at *
  omega
theorem n5384 (_v : Vars) (_q : Query _v)  : (e5383 _v) := by
  have p5377 := n5377 _v _q 
  have p5380 := n5380 _v _q 
  change ((e455 _v) ↔ (e5375 _v)) at p5377
  change ((e456 _v) ↔ (e5378 _v)) at p5380
  simp only [e5383, e5381, e5382, p5377, p5380]
theorem n5390 (_v : Vars) (_q : Query _v)  : (e465 _v) := by
  simp only [e5, e6, e12, e46, e458, e463, e464, e465] at *
  omega
theorem n5391 (_v : Vars) (_q : Query _v)  : (e464 _v) := by
  have p462 := n462 _v _q 
  have p5390 := n5390 _v _q 
  simp only [e458, e464, e465] at *
  tauto
theorem n5397 (_v : Vars) (_q : Query _v)  : (e5396 _v) := by
  simp only [e12, e467, e468, e469, e470, e471, e476, e479, e5396] at *
  omega
theorem n5398 (_v : Vars) (_q : Query _v)  : (e489 _v) := by
  simp only [e5, e6, e12, e481, e486, e487, e488, e489] at *
  omega
theorem n5399 (_v : Vars) (_q : Query _v)  : (e491 _v) := by
  simp only [e5, e6, e12, e482, e486, e487, e490, e491] at *
  omega
theorem n5401 (_v : Vars) (_q : Query _v)  : (e5400 _v) := by
  have p5398 := n5398 _v _q 
  have p5399 := n5399 _v _q 
  change ((e481 _v) ↔ (e488 _v)) at p5398
  change ((e482 _v) ↔ (e490 _v)) at p5399
  simp only [e5400, e483, e492, p5398, p5399]
theorem n5405 (_v : Vars) (_q : Query _v)  : (e5404 _v) := by
  simp only [e5, e6, e12, e486, e487, e488, e490, e492, e493, e494, e5402, e5403, e5404] at *
  omega
theorem n5414 (_v : Vars) (_q : Query _v)  : (e5413 _v) := by
  simp only [e497, e505, e506, e507, e508, e509, e510, e5412, e5413] at *
  by_cases hc : ((e504 _v) ≥ (e12 _v)) <;> simp [hc]
theorem n5416 (_v : Vars) (_q : Query _v)  : (e5415 _v) := by
  simp only [e12, e498, e499, e500, e501, e502, e511, e514, e5415] at *
  omega
theorem n5417 (_v : Vars) (_q : Query _v)  : (e523 _v) := by
  simp only [e5, e6, e12, e515, e520, e521, e522, e523] at *
  omega
theorem n5418 (_v : Vars) (_q : Query _v)  : (e525 _v) := by
  simp only [e5, e6, e12, e516, e520, e521, e524, e525] at *
  omega
theorem n5420 (_v : Vars) (_q : Query _v)  : (e5419 _v) := by
  have p5417 := n5417 _v _q 
  have p5418 := n5418 _v _q 
  change ((e515 _v) ↔ (e522 _v)) at p5417
  change ((e516 _v) ↔ (e524 _v)) at p5418
  simp only [e5419, e517, e526, p5417, p5418]
theorem n5424 (_v : Vars) (_q : Query _v)  : (e5423 _v) := by
  simp only [e5, e6, e12, e520, e521, e522, e524, e526, e527, e528, e5421, e5422, e5423] at *
  omega
theorem n5504 (_v : Vars) (_q : Query _v)  : (e5503 _v) := by
  have p742 := n742 _v _q 
  have p744 := n744 _v _q 
  exact (Eq.trans p742 p744)
theorem n5506 (_v : Vars) (_q : Query _v)  : (e758 _v) := by
  simp only [e5, e6, e43, e44, e753, e756, e757, e758] at *
  omega
theorem n5507 (_v : Vars) (_q : Query _v)  : (e759 _v) := by
  have p755 := n755 _v _q 
  have p5506 := n5506 _v _q 
  exact (Eq.trans p755 p5506)
theorem n5508 (_v : Vars) (_q : Query _v)  : (e765 _v) := by
  have p763 := n763 _v _q 
  change ((e756 _v) = (e761 _v)) at p763
  simp only [e765, e757, e764, p763]
theorem n5510 (_v : Vars) (_q : Query _v)  : (e5509 _v) := by
  have p5507 := n5507 _v _q 
  have p5508 := n5508 _v _q 
  exact (Eq.trans p5507 p5508)
theorem n5512 (_v : Vars) (_q : Query _v)  : (e779 _v) := by
  simp only [e5, e6, e266, e267, e774, e777, e778, e779] at *
  omega
theorem n5513 (_v : Vars) (_q : Query _v)  : (e780 _v) := by
  have p776 := n776 _v _q 
  have p5512 := n5512 _v _q 
  exact (Eq.trans p776 p5512)
theorem n5514 (_v : Vars) (_q : Query _v)  : (e786 _v) := by
  have p784 := n784 _v _q 
  change ((e777 _v) = (e782 _v)) at p784
  simp only [e786, e778, e785, p784]
theorem n5516 (_v : Vars) (_q : Query _v)  : (e5515 _v) := by
  have p5513 := n5513 _v _q 
  have p5514 := n5514 _v _q 
  exact (Eq.trans p5513 p5514)
theorem n5518 (_v : Vars) (_q : Query _v)  : (e800 _v) := by
  simp only [e5, e6, e108, e109, e795, e798, e799, e800] at *
  omega
end
end Assembly
