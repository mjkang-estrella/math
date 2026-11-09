import Dag128
import generated.th_lemma_9
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n15462 (_v : Vars) (_q : Query _v) (h6531 : (e6531 _v)) : (e8214 _v) := by
  have p14642 := n14642 _v _q 
  have p11358 := n11358 _v _q h6531
  simp only [e2254, e4718, e4719, e4720, e4721, e6531, e8206, e8214, e8217] at *
  tauto
theorem n15463 (_v : Vars) (_q : Query _v) (h6531 : (e6531 _v)) : (e4720 _v) := by
  have p15030 := n15030 _v _q 
  have p15462 := n15462 _v _q h6531
  simp only [e4718, e4719, e4720, e4721, e8206, e8207, e8214] at *
  tauto
theorem n15464 (_v : Vars) (_q : Query _v) (h6531 : (e6531 _v)) : (e6555 _v) := by
  have p11358 := n11358 _v _q h6531
  have p5257 := n5257 _v _q 
  exact FloorCertificate.node_15464 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e110 _v) p11358 p5257
theorem n15465 (_v : Vars) (_q : Query _v) (h6531 : (e6531 _v)) : (e6973 _v) := by
  have p14377 := n14377 _v _q 
  have p15464 := n15464 _v _q h6531
  simp only [e2310, e3265, e3266, e3267, e3268, e6555, e6965, e6973, e6976] at *
  tauto
theorem n15466 (_v : Vars) (_q : Query _v) (h6531 : (e6531 _v)) : (e7912 _v) := by
  have p14591 := n14591 _v _q 
  have p12864 := n12864 _v _q h6531
  simp only [e2482, e4392, e4393, e4394, e4395, e6636, e7904, e7912, e7915] at *
  tauto
theorem n15467 (_v : Vars) (_q : Query _v) (h6555 : (e6555 _v)) : (e6480 _v) := by
  have p8478 := n8478 _v _q 
  have p11456 := n11456 _v _q h6555
  simp only [e2061, e2125, e6454, e6480, e8477] at *
  tauto
theorem n15468 (_v : Vars) (_q : Query _v) (h6555 : (e6555 _v)) : (e7971 _v) := by
  have p14603 := n14603 _v _q 
  have p15467 := n15467 _v _q h6555
  simp only [e2125, e4475, e4477, e4480, e4481, e6480, e7970, e7971, e7974] at *
  tauto
theorem n15469 (_v : Vars) (_q : Query _v) (h6555 : (e6555 _v)) : (e4477 _v) := by
  have p14858 := n14858 _v _q 
  have p15468 := n15468 _v _q h6555
  simp only [e4475, e4477, e4480, e4481, e7970, e7971, e7980] at *
  tauto
theorem n15470 (_v : Vars) (_q : Query _v) (h6555 : (e6555 _v)) : (e7955 _v) := by
  have p14601 := n14601 _v _q 
  have p11456 := n11456 _v _q h6555
  simp only [e2061, e4434, e4435, e4436, e4437, e6454, e7947, e7955, e7958] at *
  tauto
theorem n15471 (_v : Vars) (_q : Query _v) (h6555 : (e6555 _v)) : (e4434 _v) := by
  have p15307 := n15307 _v _q 
  have p15470 := n15470 _v _q h6555
  simp only [e4434, e4435, e4436, e4437, e7947, e7948, e7955] at *
  tauto
theorem n15472 (_v : Vars) (_q : Query _v) (h2634 : (e2634 _v)) : (e3180 _v) := by
  have p14361 := n14361 _v _q 
  have p11032 := n11032 _v _q h2634
  simp only [e2634, e3172, e3173, e3177, e3178, e3179, e3180, e6700, e6902] at *
  tauto
theorem n15473 (_v : Vars) (_q : Query _v) (h2634 : (e2634 _v)) : (e3173 _v) := by
  have p6907 := n6907 _v _q 
  have p15472 := n15472 _v _q h2634
  simp only [e3172, e3173, e3177, e3178, e3179, e3180, e3190] at *
  tauto
theorem n15474 (_v : Vars) (_q : Query _v) (h6672 : (e6672 _v)) : (e8348 _v) := by
  have p15312 := n15312 _v _q 
  have p11401 := n11401 _v _q h6672
  simp only [e2592, e6672, e8335, e8338, e8345, e8346, e8347, e8348, e11307] at *
  tauto
theorem n15475 (_v : Vars) (_q : Query _v) (h6672 : (e6672 _v)) : (e8335 _v) := by
  have p11421 := n11421 _v _q 
  have p15474 := n15474 _v _q h6672
  simp only [e8335, e8338, e8345, e8346, e8347, e8348, e8482] at *
  tauto
theorem n15476 (_v : Vars) (_q : Query _v) (h6531 : (e6531 _v)) : (e7170 _v) := by
  have p14427 := n14427 _v _q 
  have p12863 := n12863 _v _q h6531
  simp only [e2536, e3583, e3585, e3588, e3589, e6656, e7169, e7170, e7173] at *
  tauto
theorem n15477 (_v : Vars) (_q : Query _v) (h6531 : (e6531 _v)) : (e3585 _v) := by
  have p14783 := n14783 _v _q 
  have p15476 := n15476 _v _q h6531
  simp only [e3583, e3585, e3588, e3589, e7169, e7170, e7182] at *
  tauto
theorem n15478 (_v : Vars) (_q : Query _v) (h6531 : (e6531 _v)) : (e6973 _v) := by
  have p14377 := n14377 _v _q 
  have p12862 := n12862 _v _q h6531
  simp only [e2310, e3265, e3266, e3267, e3268, e6555, e6965, e6973, e6976] at *
  tauto
theorem n15479 (_v : Vars) (_q : Query _v) (h6531 : (e6531 _v)) : (e7170 _v) := by
  have p14427 := n14427 _v _q 
  have p12865 := n12865 _v _q h6531
  simp only [e2536, e3583, e3585, e3588, e3589, e6656, e7169, e7170, e7173] at *
  tauto
theorem n15480 (_v : Vars) (_q : Query _v) (h6531 : (e6531 _v)) : (e3585 _v) := by
  have p14783 := n14783 _v _q 
  have p15479 := n15479 _v _q h6531
  simp only [e3583, e3585, e3588, e3589, e7169, e7170, e7182] at *
  tauto
theorem n15481 (_v : Vars) (_q : Query _v) (h6636 : (e6636 _v)) : (e7170 _v) := by
  have p14427 := n14427 _v _q 
  have p14123 := n14123 _v _q h6636
  simp only [e2536, e3583, e3585, e3588, e3589, e6656, e7169, e7170, e7173] at *
  tauto
theorem n15482 (_v : Vars) (_q : Query _v) (h2482 : (e2482 _v)) : (e4405 _v) := by
  have p14702 := n14702 _v _q 
  have p10888 := n10888 _v _q h2482
  simp only [e2482, e4397, e4398, e4402, e4403, e4404, e4405, e6636, e7918] at *
  tauto
theorem n15483 (_v : Vars) (_q : Query _v) (h2482 : (e2482 _v)) : (e4398 _v) := by
  have p14976 := n14976 _v _q 
  have p15482 := n15482 _v _q h2482
  simp only [e4397, e4398, e4402, e4403, e4404, e4405, e4962] at *
  tauto
theorem n15484 (_v : Vars) (_q : Query _v) (h7807 : (e7807 _v)) : (e7517 _v) := by
  have p15196 := n15196 _v _q 
  have p12867 := n12867 _v _q h7807
  simp only [e2691, e6724, e7493, e7494, e7495, e7496, e7497, e7517, e10904] at *
  tauto
theorem n15485 (_v : Vars) (_q : Query _v) (h7807 : (e7807 _v)) : (e7493 _v) := by
  have p15195 := n15195 _v _q 
  have p15484 := n15484 _v _q h7807
  simp only [e7493, e7494, e7495, e7496, e7497, e7498, e7517] at *
  tauto
theorem n15486 (_v : Vars) (_q : Query _v)  : (e7443 _v) := by
  simp only [e3971, e3972, e3973, e3974, e7442, e7443] at *
  tauto
theorem n15487 (_v : Vars) (_q : Query _v) (h6758 : (e6758 _v)) : (e7450 _v) := by
  have p14489 := n14489 _v _q 
  have p8425 := n8425 _v _q h6758
  simp only [e2746, e3971, e3972, e3973, e3974, e6758, e7442, e7450, e7453] at *
  tauto
theorem n15488 (_v : Vars) (_q : Query _v) (h6758 : (e6758 _v)) : (e3971 _v) := by
  have p15486 := n15486 _v _q 
  have p15487 := n15487 _v _q h6758
  simp only [e3971, e3972, e3973, e3974, e7442, e7443, e7450] at *
  tauto
theorem n15489 (_v : Vars) (_q : Query _v) (h6758 : (e6758 _v)) : (e6656 _v) := by
  have p8425 := n8425 _v _q h6758
  have p10896 := n10896 _v _q 
  exact FloorCertificate.node_15489 (e2 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8425 p10896
theorem n15490 (_v : Vars) (_q : Query _v) (h6758 : (e6758 _v)) : (e7170 _v) := by
  have p14427 := n14427 _v _q 
  have p15489 := n15489 _v _q h6758
  simp only [e2536, e3583, e3585, e3588, e3589, e6656, e7169, e7170, e7173] at *
  tauto
theorem n15491 (_v : Vars) (_q : Query _v) (h6758 : (e6758 _v)) : (e6555 _v) := by
  have p8425 := n8425 _v _q h6758
  have p10893 := n10893 _v _q 
  exact FloorCertificate.node_15491 (e2 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8425 p10893
theorem n15492 (_v : Vars) (_q : Query _v) (h6758 : (e6758 _v)) : (e6973 _v) := by
  have p14377 := n14377 _v _q 
  have p15491 := n15491 _v _q h6758
  simp only [e2310, e3265, e3266, e3267, e3268, e6555, e6965, e6973, e6976] at *
  tauto
theorem n15493 (_v : Vars) (_q : Query _v) (h6732 : (e6732 _v)) : (e6531 _v) := by
  have p11370 := n11370 _v _q h6732
  have p10893 := n10893 _v _q 
  exact FloorCertificate.node_15493 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) p11370 p10893
theorem n15494 (_v : Vars) (_q : Query _v) (h6732 : (e6732 _v)) : (e8214 _v) := by
  have p14642 := n14642 _v _q 
  have p15493 := n15493 _v _q h6732
  simp only [e2254, e4718, e4719, e4720, e4721, e6531, e8206, e8214, e8217] at *
  tauto
theorem n15495 (_v : Vars) (_q : Query _v)  : (e7547 _v) := by
  simp only [e4054, e4055, e4056, e4057, e7546, e7547] at *
  tauto
theorem n15496 (_v : Vars) (_q : Query _v) (h6684 : (e6684 _v)) : (e7554 _v) := by
  have p14515 := n14515 _v _q 
  have p12804 := n12804 _v _q h6684
  simp only [e2598, e4054, e4055, e4056, e4057, e6684, e7546, e7554, e7557] at *
  tauto
theorem n15497 (_v : Vars) (_q : Query _v) (h6684 : (e6684 _v)) : (e4054 _v) := by
  have p15495 := n15495 _v _q 
  have p15496 := n15496 _v _q h6684
  simp only [e4054, e4055, e4056, e4057, e7546, e7547, e7554] at *
  tauto
theorem n15498 (_v : Vars) (_q : Query _v) (h6684 : (e6684 _v)) : (e6486 _v) := by
  have p12804 := n12804 _v _q h6684
  have p10893 := n10893 _v _q 
  exact FloorCertificate.node_15498 (e2 _v) (e7 _v) (e17 _v) (e45 _v) (e110 _v) p12804 p10893
theorem n15499 (_v : Vars) (_q : Query _v) (h6684 : (e6684 _v)) : (e7358 _v) := by
  have p14471 := n14471 _v _q 
  have p15498 := n15498 _v _q h6684
  simp only [e2139, e3849, e3850, e3851, e3852, e6486, e7350, e7358, e7361] at *
  tauto
theorem n15500 (_v : Vars) (_q : Query _v) (h6684 : (e6684 _v)) : (e6531 _v) := by
  have p12804 := n12804 _v _q h6684
  have p5255 := n5255 _v _q 
  have p10893 := n10893 _v _q 
  exact FloorCertificate.node_15500 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p12804 p5255 p10893
theorem n15501 (_v : Vars) (_q : Query _v) (h6684 : (e6684 _v)) : (e8214 _v) := by
  have p14642 := n14642 _v _q 
  have p15500 := n15500 _v _q h6684
  simp only [e2254, e4718, e4719, e4720, e4721, e6531, e8206, e8214, e8217] at *
  tauto
theorem n15502 (_v : Vars) (_q : Query _v)  : (e7985 _v) := by
  simp only [e4486, e4487, e4488, e4489, e7984, e7985] at *
  tauto
theorem n15503 (_v : Vars) (_q : Query _v) (h6732 : (e6732 _v)) : (e7992 _v) := by
  have p14606 := n14606 _v _q 
  have p11370 := n11370 _v _q h6732
  simp only [e2697, e4486, e4487, e4488, e4489, e6732, e7984, e7992, e7995] at *
  tauto
theorem n15504 (_v : Vars) (_q : Query _v) (h6732 : (e6732 _v)) : (e4486 _v) := by
  have p15502 := n15502 _v _q 
  have p15503 := n15503 _v _q h6732
  simp only [e4486, e4487, e4488, e4489, e7984, e7985, e7992] at *
  tauto
theorem n15505 (_v : Vars) (_q : Query _v) (h5093 : (e5093 _v)) : (e6724 _v) := by
  have p10893 := n10893 _v _q 
  have p11440 := n11440 _v _q h5093
  exact FloorCertificate.node_15505 (e2 _v) (e7 _v) (e9 _v) (e45 _v) p10893 p11440
theorem n15506 (_v : Vars) (_q : Query _v) (h5093 : (e5093 _v)) : (e7517 _v) := by
  have p15196 := n15196 _v _q 
  have p15505 := n15505 _v _q h5093
  simp only [e2691, e6724, e7493, e7494, e7495, e7496, e7497, e7517, e10904] at *
  tauto
end
end Assembly
