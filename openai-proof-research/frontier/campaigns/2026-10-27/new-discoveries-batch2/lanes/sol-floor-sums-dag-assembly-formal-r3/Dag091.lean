import Dag090
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n13310 (_v : Vars) (_q : Query _v)  : (e5944 _v) := by
  have p13308 := n13308 _v _q 
  have p13309 := n13309 _v _q 
  exact (Iff.trans p13308 p13309)
theorem n13312 (_v : Vars) (_q : Query _v)  : (e13311 _v) := by
  have p13310 := n13310 _v _q 
  have p11762 := n11762 _v _q 
  change ((e700 _v) ↔ (e1439 _v)) at p13310
  change ((e698 _v) = (e1434 _v)) at p11762
  simp only [e13311, e5476, e1441, p13310, p11762]
theorem n13314 (_v : Vars) (_q : Query _v)  : (e13313 _v) := by
  have p13307 := n13307 _v _q 
  have p13312 := n13312 _v _q 
  change ((e699 _v) ↔ (e1894 _v)) at p13307
  change ((e5476 _v) = (e1441 _v)) at p13312
  simp only [e13313, e8820, e5945, p13307, p13312]
theorem n13315 (_v : Vars) (_q : Query _v)  : (e5952 _v) := by
  have p11764 := n11764 _v _q 
  change ((e701 _v) = (e1444 _v)) at p11764
  simp only [e5952, e702, e1901, p11764]
theorem n13316 (_v : Vars) (_q : Query _v)  : (e5953 _v) := by
  have p11764 := n11764 _v _q 
  change ((e701 _v) = (e1444 _v)) at p11764
  simp only [e5953, e703, e1447, p11764]
theorem n13317 (_v : Vars) (_q : Query _v)  : (e1450 _v) := by
  simp only [e12, e108, e802, e803, e1444, e1447, e1448, e1449, e1450] at *
  omega
theorem n13318 (_v : Vars) (_q : Query _v)  : (e5954 _v) := by
  have p13316 := n13316 _v _q 
  have p13317 := n13317 _v _q 
  exact (Iff.trans p13316 p13317)
theorem n13320 (_v : Vars) (_q : Query _v)  : (e13319 _v) := by
  have p13318 := n13318 _v _q 
  have p11764 := n11764 _v _q 
  change ((e703 _v) ↔ (e1449 _v)) at p13318
  change ((e701 _v) = (e1444 _v)) at p11764
  simp only [e13319, e5477, e1451, p13318, p11764]
theorem n13322 (_v : Vars) (_q : Query _v)  : (e13321 _v) := by
  have p13315 := n13315 _v _q 
  have p13320 := n13320 _v _q 
  change ((e702 _v) ↔ (e1901 _v)) at p13315
  change ((e5477 _v) = (e1451 _v)) at p13320
  simp only [e13321, e8821, e5955, p13315, p13320]
theorem n13324 (_v : Vars) (_q : Query _v)  : (e13323 _v) := by
  have p11766 := n11766 _v _q 
  change ((e705 _v) = (e1458 _v)) at p11766
  simp only [e13323, e707, e1462, p11766]
theorem n13325 (_v : Vars) (_q : Query _v)  : (e5958 _v) := by
  simp only [e5, e6, e12, e36, e1458, e1462, e1463, e1464, e5958] at *
  omega
theorem n13326 (_v : Vars) (_q : Query _v)  : (e5959 _v) := by
  have p13324 := n13324 _v _q 
  have p13325 := n13325 _v _q 
  exact (Iff.trans p13324 p13325)
theorem n13328 (_v : Vars) (_q : Query _v)  : (e13327 _v) := by
  have p13326 := n13326 _v _q 
  have p11766 := n11766 _v _q 
  change ((e707 _v) ↔ (e1464 _v)) at p13326
  change ((e705 _v) = (e1458 _v)) at p11766
  simp only [e13327, e5478, e1465, p13326, p11766]
theorem n13330 (_v : Vars) (_q : Query _v)  : (e13329 _v) := by
  have p11768 := n11768 _v _q 
  change ((e708 _v) = (e1468 _v)) at p11768
  simp only [e13329, e710, e1472, p11768]
theorem n13331 (_v : Vars) (_q : Query _v)  : (e5966 _v) := by
  simp only [e12, e43, e760, e761, e1468, e1472, e1473, e1474, e5966] at *
  omega
theorem n13332 (_v : Vars) (_q : Query _v)  : (e5967 _v) := by
  have p13330 := n13330 _v _q 
  have p13331 := n13331 _v _q 
  exact (Iff.trans p13330 p13331)
theorem n13334 (_v : Vars) (_q : Query _v)  : (e13333 _v) := by
  have p13332 := n13332 _v _q 
  have p11768 := n11768 _v _q 
  change ((e710 _v) ↔ (e1474 _v)) at p13332
  change ((e708 _v) = (e1468 _v)) at p11768
  simp only [e13333, e5479, e1475, p13332, p11768]
theorem n13336 (_v : Vars) (_q : Query _v)  : (e13335 _v) := by
  have p11770 := n11770 _v _q 
  change ((e711 _v) = (e1478 _v)) at p11770
  simp only [e13335, e713, e1482, p11770]
theorem n13337 (_v : Vars) (_q : Query _v)  : (e5974 _v) := by
  simp only [e12, e266, e781, e782, e1478, e1482, e1483, e1484, e5974] at *
  omega
theorem n13338 (_v : Vars) (_q : Query _v)  : (e5975 _v) := by
  have p13336 := n13336 _v _q 
  have p13337 := n13337 _v _q 
  exact (Iff.trans p13336 p13337)
theorem n13340 (_v : Vars) (_q : Query _v)  : (e13339 _v) := by
  have p13338 := n13338 _v _q 
  have p11770 := n11770 _v _q 
  change ((e713 _v) ↔ (e1484 _v)) at p13338
  change ((e711 _v) = (e1478 _v)) at p11770
  simp only [e13339, e5480, e1485, p13338, p11770]
theorem n13342 (_v : Vars) (_q : Query _v)  : (e13341 _v) := by
  have p11772 := n11772 _v _q 
  change ((e714 _v) = (e1488 _v)) at p11772
  simp only [e13341, e716, e1492, p11772]
theorem n13343 (_v : Vars) (_q : Query _v)  : (e5982 _v) := by
  simp only [e12, e108, e802, e803, e1488, e1492, e1493, e1494, e5982] at *
  omega
theorem n13344 (_v : Vars) (_q : Query _v)  : (e5983 _v) := by
  have p13342 := n13342 _v _q 
  have p13343 := n13343 _v _q 
  exact (Iff.trans p13342 p13343)
theorem n13346 (_v : Vars) (_q : Query _v)  : (e13345 _v) := by
  have p13344 := n13344 _v _q 
  have p11772 := n11772 _v _q 
  change ((e716 _v) ↔ (e1494 _v)) at p13344
  change ((e714 _v) = (e1488 _v)) at p11772
  simp only [e13345, e5481, e1495, p13344, p11772]
theorem n13348 (_v : Vars) (_q : Query _v)  : (e13347 _v) := by
  have p11774 := n11774 _v _q 
  change ((e718 _v) = (e1502 _v)) at p11774
  simp only [e13347, e720, e1506, p11774]
theorem n13349 (_v : Vars) (_q : Query _v)  : (e5996 _v) := by
  simp only [e5, e6, e12, e36, e1502, e1506, e1507, e1508, e5996] at *
  omega
theorem n13350 (_v : Vars) (_q : Query _v)  : (e5997 _v) := by
  have p13348 := n13348 _v _q 
  have p13349 := n13349 _v _q 
  exact (Iff.trans p13348 p13349)
theorem n13352 (_v : Vars) (_q : Query _v)  : (e13351 _v) := by
  have p13350 := n13350 _v _q 
  have p11774 := n11774 _v _q 
  change ((e720 _v) ↔ (e1508 _v)) at p13350
  change ((e718 _v) = (e1502 _v)) at p11774
  simp only [e13351, e5482, e1509, p13350, p11774]
theorem n13354 (_v : Vars) (_q : Query _v)  : (e13353 _v) := by
  have p11776 := n11776 _v _q 
  change ((e721 _v) = (e1512 _v)) at p11776
  simp only [e13353, e723, e1516, p11776]
theorem n13355 (_v : Vars) (_q : Query _v)  : (e6004 _v) := by
  simp only [e12, e43, e760, e761, e1512, e1516, e1517, e1518, e6004] at *
  omega
theorem n13356 (_v : Vars) (_q : Query _v)  : (e6005 _v) := by
  have p13354 := n13354 _v _q 
  have p13355 := n13355 _v _q 
  exact (Iff.trans p13354 p13355)
theorem n13358 (_v : Vars) (_q : Query _v)  : (e13357 _v) := by
  have p13356 := n13356 _v _q 
  have p11776 := n11776 _v _q 
  change ((e723 _v) ↔ (e1518 _v)) at p13356
  change ((e721 _v) = (e1512 _v)) at p11776
  simp only [e13357, e5483, e1519, p13356, p11776]
theorem n13360 (_v : Vars) (_q : Query _v)  : (e13359 _v) := by
  have p11778 := n11778 _v _q 
  change ((e724 _v) = (e1522 _v)) at p11778
  simp only [e13359, e726, e1526, p11778]
theorem n13361 (_v : Vars) (_q : Query _v)  : (e6012 _v) := by
  simp only [e12, e266, e781, e782, e1522, e1526, e1527, e1528, e6012] at *
  omega
theorem n13362 (_v : Vars) (_q : Query _v)  : (e6013 _v) := by
  have p13360 := n13360 _v _q 
  have p13361 := n13361 _v _q 
  exact (Iff.trans p13360 p13361)
theorem n13364 (_v : Vars) (_q : Query _v)  : (e13363 _v) := by
  have p13362 := n13362 _v _q 
  have p11778 := n11778 _v _q 
  change ((e726 _v) ↔ (e1528 _v)) at p13362
  change ((e724 _v) = (e1522 _v)) at p11778
  simp only [e13363, e5484, e1529, p13362, p11778]
theorem n13366 (_v : Vars) (_q : Query _v)  : (e13365 _v) := by
  have p11780 := n11780 _v _q 
  change ((e727 _v) = (e1532 _v)) at p11780
  simp only [e13365, e729, e1536, p11780]
theorem n13367 (_v : Vars) (_q : Query _v)  : (e6020 _v) := by
  simp only [e12, e108, e802, e803, e1532, e1536, e1537, e1538, e6020] at *
  omega
theorem n13368 (_v : Vars) (_q : Query _v)  : (e6021 _v) := by
  have p13366 := n13366 _v _q 
  have p13367 := n13367 _v _q 
  exact (Iff.trans p13366 p13367)
theorem n13370 (_v : Vars) (_q : Query _v)  : (e13369 _v) := by
  have p13368 := n13368 _v _q 
  have p11780 := n11780 _v _q 
  change ((e729 _v) ↔ (e1538 _v)) at p13368
  change ((e727 _v) = (e1532 _v)) at p11780
  simp only [e13369, e5485, e1539, p13368, p11780]
theorem n13372 (_v : Vars) (_q : Query _v)  : (e13371 _v) := by
  have p11786 := n11786 _v _q 
  have p9142 := n9142 _v _q 
  change ((e5487 _v) ↔ (e1547 _v)) at p11786
  change ((e731 _v) = (e1543 _v)) at p9142
  simp only [e13371, e5488, e6039, p11786, p9142]
theorem n13374 (_v : Vars) (_q : Query _v)  : (e13373 _v) := by
  have p11793 := n11793 _v _q 
  change ((e732 _v) = (e1550 _v)) at p11793
  simp only [e13373, e5491, e1552, p11793]
theorem n13376 (_v : Vars) (_q : Query _v)  : (e13375 _v) := by
  simp only [e12, e43, e760, e761, e1550, e1552, e1553, e1554, e13375] at *
  omega
theorem n13378 (_v : Vars) (_q : Query _v)  : (e13377 _v) := by
  have p13374 := n13374 _v _q 
  have p13376 := n13376 _v _q 
  exact (Iff.trans p13374 p13376)
end
end Assembly
