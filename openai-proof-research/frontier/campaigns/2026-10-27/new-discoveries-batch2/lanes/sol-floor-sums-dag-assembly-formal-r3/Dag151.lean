import Dag150
import generated.th_lemma_13
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n16468 (_v : Vars) (_q : Query _v) (h2799 : (e2799 _v)) : (e2132 _v) := by
  have p10896 := n10896 _v _q 
  have p10893 := n10893 _v _q 
  have p8511 := n8511 _v _q h2799
  exact FloorCertificate.node_16468 (e2 _v) (e7 _v) (e9 _v) (e45 _v) (e110 _v) p10896 p10893 p8511
theorem n16469 (_v : Vars) (_q : Query _v) (h2799 : (e2799 _v)) : (e7739 _v) := by
  have p14833 := n14833 _v _q 
  have p16468 := n16468 _v _q h2799
  simp only [e2132, e4218, e4219, e4220, e4221, e7733, e7739, e7742, e7744] at *
  tauto
theorem n16470 (_v : Vars) (_q : Query _v) (h2799 : (e2799 _v)) : (e4220 _v) := by
  have p16334 := n16334 _v _q 
  have p16469 := n16469 _v _q h2799
  simp only [e4218, e4219, e4220, e4221, e7733, e7734, e7739] at *
  tauto
theorem n16471 (_v : Vars) (_q : Query _v) (h2592 : (e2592 _v)) : (e8330 _v) := by
  have p14907 := n14907 _v _q 
  have p8536 := n8536 _v _q h2592
  simp only [e2592, e4855, e4856, e4857, e4858, e6672, e8324, e8330, e8333] at *
  tauto
theorem n16472 (_v : Vars) (_q : Query _v) (h2592 : (e2592 _v)) : (e4855 _v) := by
  have p16317 := n16317 _v _q 
  have p16471 := n16471 _v _q h2592
  simp only [e4855, e4856, e4857, e4858, e8324, e8325, e8330] at *
  tauto
theorem n16473 (_v : Vars) (_q : Query _v) (h2592 : (e2592 _v)) : (e13 _v) := by
  have p11443 := n11443 _v _q 
  have p8536 := n8536 _v _q h2592
  simp only [e13, e2592, e6672, e11442] at *
  tauto
theorem n16474 (_v : Vars) (_q : Query _v) (h2592 : (e2592 _v)) : (e5090 _v) := by
  have p14728 := n14728 _v _q 
  have p16473 := n16473 _v _q h2592
  simp only [e13, e28, e30, e34, e35, e5089, e5090, e5093, e5095] at *
  tauto
theorem n16475 (_v : Vars) (_q : Query _v) (h2592 : (e2592 _v)) : (e30 _v) := by
  have p16290 := n16290 _v _q 
  have p16474 := n16474 _v _q h2592
  simp only [e28, e30, e34, e35, e5089, e5090, e5107] at *
  tauto
theorem n16476 (_v : Vars) (_q : Query _v) (h2592 : (e2592 _v)) : (e2691 _v) := by
  have p5255 := n5255 _v _q 
  have p8536 := n8536 _v _q h2592
  exact FloorCertificate.node_16476 (e2 _v) (e7 _v) (e9 _v) (e45 _v) (e110 _v) p5255 p8536
theorem n16477 (_v : Vars) (_q : Query _v) (h2592 : (e2592 _v)) : (e7504 _v) := by
  have p14811 := n14811 _v _q 
  have p16476 := n16476 _v _q h2592
  simp only [e2691, e4026, e4028, e4031, e4032, e6724, e7503, e7504, e7507] at *
  tauto
theorem n16478 (_v : Vars) (_q : Query _v) (h2592 : (e2592 _v)) : (e4026 _v) := by
  have p16194 := n16194 _v _q 
  have p16477 := n16477 _v _q h2592
  simp only [e4026, e4028, e4031, e4032, e7503, e7504, e7519] at *
  tauto
theorem n16479 (_v : Vars) (_q : Query _v) (h2592 : (e2592 _v)) : (e2132 _v) := by
  have p10893 := n10893 _v _q 
  have p8536 := n8536 _v _q h2592
  exact FloorCertificate.node_16479 (e2 _v) (e7 _v) (e45 _v) (e110 _v) p10893 p8536
theorem n16480 (_v : Vars) (_q : Query _v) (h2592 : (e2592 _v)) : (e7739 _v) := by
  have p14833 := n14833 _v _q 
  have p16479 := n16479 _v _q h2592
  simp only [e2132, e4218, e4219, e4220, e4221, e7733, e7739, e7742, e7744] at *
  tauto
theorem n16481 (_v : Vars) (_q : Query _v) (h2592 : (e2592 _v)) : (e4220 _v) := by
  have p16334 := n16334 _v _q 
  have p16480 := n16480 _v _q h2592
  simp only [e4218, e4219, e4220, e4221, e7733, e7734, e7739] at *
  tauto
theorem n16482 (_v : Vars) (_q : Query _v) (h2799 : (e2799 _v)) : (e2592 _v) := by
  have p8511 := n8511 _v _q h2799
  have p10896 := n10896 _v _q 
  exact FloorCertificate.node_16482 (e2 _v) (e7 _v) (e9 _v) (e45 _v) (e110 _v) p8511 p10896
theorem n16483 (_v : Vars) (_q : Query _v) (h2799 : (e2799 _v)) : (e8330 _v) := by
  have p14907 := n14907 _v _q 
  have p16482 := n16482 _v _q h2799
  simp only [e2592, e4855, e4856, e4857, e4858, e6672, e8324, e8330, e8333] at *
  tauto
theorem n16484 (_v : Vars) (_q : Query _v) (h2799 : (e2799 _v)) : (e4855 _v) := by
  have p16317 := n16317 _v _q 
  have p16483 := n16483 _v _q h2799
  simp only [e4855, e4856, e4857, e4858, e8324, e8325, e8330] at *
  tauto
theorem n16485 (_v : Vars) (_q : Query _v) (h2799 : (e2799 _v)) : (e2592 _v) := by
  have p11404 := n11404 _v _q 
  have p16459 := n16459 _v _q h2799
  simp only [e2371, e2592, e6579, e11403] at *
  tauto
theorem n16486 (_v : Vars) (_q : Query _v) (h2799 : (e2799 _v)) : (e8330 _v) := by
  have p14907 := n14907 _v _q 
  have p16485 := n16485 _v _q h2799
  simp only [e2592, e4855, e4856, e4857, e4858, e6672, e8324, e8330, e8333] at *
  tauto
theorem n16487 (_v : Vars) (_q : Query _v) (h6531 : (e6531 _v)) : (e3267 _v) := by
  have p14776 := n14776 _v _q 
  have p15478 := n15478 _v _q h6531
  simp only [e3265, e3266, e3267, e3268, e6965, e6966, e6973] at *
  tauto
theorem n16488 (_v : Vars) (_q : Query _v) (h6636 : (e6636 _v)) : (e3585 _v) := by
  have p14783 := n14783 _v _q 
  have p15481 := n15481 _v _q h6636
  simp only [e3583, e3585, e3588, e3589, e7169, e7170, e7182] at *
  tauto
theorem n16489 (_v : Vars) (_q : Query _v) (h2799 : (e2799 _v)) : (e2592 _v) := by
  have p10896 := n10896 _v _q 
  have p8511 := n8511 _v _q h2799
  exact FloorCertificate.node_16489 (e2 _v) (e7 _v) (e9 _v) (e45 _v) (e110 _v) p10896 p8511
theorem n16490 (_v : Vars) (_q : Query _v) (h2799 : (e2799 _v)) : (e8330 _v) := by
  have p14907 := n14907 _v _q 
  have p16489 := n16489 _v _q h2799
  simp only [e2592, e4855, e4856, e4857, e4858, e6672, e8324, e8330, e8333] at *
  tauto
theorem n16491 (_v : Vars) (_q : Query _v) (h2799 : (e2799 _v)) : (e4855 _v) := by
  have p16317 := n16317 _v _q 
  have p16490 := n16490 _v _q h2799
  simp only [e4855, e4856, e4857, e4858, e8324, e8325, e8330] at *
  tauto
theorem n16492 (_v : Vars) (_q : Query _v) (h2799 : (e2799 _v)) : (e2132 _v) := by
  have p10893 := n10893 _v _q 
  have p8511 := n8511 _v _q h2799
  have p10896 := n10896 _v _q 
  exact FloorCertificate.node_16492 (e2 _v) (e7 _v) (e9 _v) (e45 _v) (e110 _v) p10893 p8511 p10896
theorem n16493 (_v : Vars) (_q : Query _v) (h2799 : (e2799 _v)) : (e7739 _v) := by
  have p14833 := n14833 _v _q 
  have p16492 := n16492 _v _q h2799
  simp only [e2132, e4218, e4219, e4220, e4221, e7733, e7739, e7742, e7744] at *
  tauto
theorem n16494 (_v : Vars) (_q : Query _v) (h2799 : (e2799 _v)) : (e4220 _v) := by
  have p16334 := n16334 _v _q 
  have p16493 := n16493 _v _q h2799
  simp only [e4218, e4219, e4220, e4221, e7733, e7734, e7739] at *
  tauto
theorem n16495 (_v : Vars) (_q : Query _v) (h2799 : (e2799 _v)) : (e13 _v) := by
  have p11449 := n11449 _v _q 
  have p8511 := n8511 _v _q h2799
  simp only [e13, e2799, e6780, e11448] at *
  tauto
theorem n16496 (_v : Vars) (_q : Query _v) (h2799 : (e2799 _v)) : (e5090 _v) := by
  have p14728 := n14728 _v _q 
  have p16495 := n16495 _v _q h2799
  simp only [e13, e28, e30, e34, e35, e5089, e5090, e5093, e5095] at *
  tauto
theorem n16497 (_v : Vars) (_q : Query _v) (h2799 : (e2799 _v)) : (e30 _v) := by
  have p16290 := n16290 _v _q 
  have p16496 := n16496 _v _q h2799
  simp only [e28, e30, e34, e35, e5089, e5090, e5107] at *
  tauto
theorem n16498 (_v : Vars) (_q : Query _v) (h2799 : (e2799 _v)) : (e2371 _v) := by
  have p8511 := n8511 _v _q h2799
  have p10893 := n10893 _v _q 
  exact FloorCertificate.node_16498 (e2 _v) (e7 _v) (e9 _v) (e45 _v) (e110 _v) p8511 p10893
theorem n16499 (_v : Vars) (_q : Query _v) (h2799 : (e2799 _v)) : (e7683 _v) := by
  have p14831 := n14831 _v _q 
  have p16498 := n16498 _v _q h2799
  simp only [e2371, e4181, e4182, e4183, e4184, e6579, e7677, e7683, e7686] at *
  tauto
theorem n16500 (_v : Vars) (_q : Query _v) (h2799 : (e2799 _v)) : (e4181 _v) := by
  have p16453 := n16453 _v _q 
  have p16499 := n16499 _v _q h2799
  simp only [e4181, e4182, e4183, e4184, e7677, e7678, e7683] at *
  tauto
theorem n16501 (_v : Vars) (_q : Query _v) (h6758 : (e6758 _v)) : (e2303 _v) := by
  have p8663 := n8663 _v _q 
  have p10893 := n10893 _v _q 
  have p8425 := n8425 _v _q h6758
  exact FloorCertificate.node_16501 (e2 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8663 p10893 p8425
theorem n16502 (_v : Vars) (_q : Query _v) (h6758 : (e6758 _v)) : (e7804 _v) := by
  have p14837 := n14837 _v _q 
  have p16501 := n16501 _v _q h6758
  simp only [e2303, e4283, e4284, e4285, e4286, e7798, e7804, e7807, e7809] at *
  tauto
theorem n16503 (_v : Vars) (_q : Query _v) (h6758 : (e6758 _v)) : (e3585 _v) := by
  have p14783 := n14783 _v _q 
  have p15490 := n15490 _v _q h6758
  simp only [e3583, e3585, e3588, e3589, e7169, e7170, e7182] at *
  tauto
theorem n16504 (_v : Vars) (_q : Query _v) (h6758 : (e6758 _v)) : (e3267 _v) := by
  have p14776 := n14776 _v _q 
  have p15492 := n15492 _v _q h6758
  simp only [e3265, e3266, e3267, e3268, e6965, e6966, e6973] at *
  tauto
theorem n16505 (_v : Vars) (_q : Query _v) (h6531 : (e6531 _v)) : (e5090 _v) := by
  have p14728 := n14728 _v _q 
  have p14102 := n14102 _v _q h6531
  simp only [e13, e28, e30, e34, e35, e5089, e5090, e5093, e5095] at *
  tauto
theorem n16506 (_v : Vars) (_q : Query _v) (h6732 : (e6732 _v)) : (e4720 _v) := by
  have p15030 := n15030 _v _q 
  have p15494 := n15494 _v _q h6732
  simp only [e4718, e4719, e4720, e4721, e8206, e8207, e8214] at *
  tauto
theorem n16507 (_v : Vars) (_q : Query _v) (h6684 : (e6684 _v)) : (e3851 _v) := by
  have p14790 := n14790 _v _q 
  have p15499 := n15499 _v _q h6684
  simp only [e3849, e3850, e3851, e3852, e7350, e7351, e7358] at *
  tauto
theorem n16508 (_v : Vars) (_q : Query _v) (h6684 : (e6684 _v)) : (e4720 _v) := by
  have p15030 := n15030 _v _q 
  have p15501 := n15501 _v _q h6684
  simp only [e4718, e4719, e4720, e4721, e8206, e8207, e8214] at *
  tauto
theorem n16509 (_v : Vars) (_q : Query _v)  : (e8504 _v) := by
  simp only [e7932, e7935, e7942, e7943, e7944, e8504] at *
  tauto
theorem n16510 (_v : Vars) (_q : Query _v) (h4419 : (e4419 _v)) (h7807 : (e7807 _v)) (h8038 : (e8038 _v)) : (e7942 _v) := by
  have p4971 := n4971 _v _q h4419
  have p11350 := n11350 _v _q h7807
  have p8602 := n8602 _v _q h8038
  exact FloorCertificate.node_16510 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) (e2911 _v) p4971 p11350 p8602
theorem n16511 (_v : Vars) (_q : Query _v) (h4419 : (e4419 _v)) (h7807 : (e7807 _v)) (h8038 : (e8038 _v)) : (e7489 _v) := by
  have p16509 := n16509 _v _q 
  have p15523 := n15523 _v _q h7807 h8038
  have p16510 := n16510 _v _q h4419 h7807 h8038
  simp only [e7932, e7935, e7942, e7943, e7944, e7945, e8504] at *
  tauto
theorem n16512 (_v : Vars) (_q : Query _v) (h6758 : (e6758 _v)) : (e4899 _v) := by
  have p15064 := n15064 _v _q 
  have p15564 := n15564 _v _q h6758
  simp only [e4897, e4898, e4899, e4900, e8367, e8368, e8375] at *
  tauto
end
end Assembly
