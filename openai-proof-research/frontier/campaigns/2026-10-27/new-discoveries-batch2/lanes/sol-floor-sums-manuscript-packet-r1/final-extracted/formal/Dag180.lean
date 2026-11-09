import Dag179
import generated.th_lemma_19
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n17916 (_v : Vars) (_q : Query _v) (h6684 : (e6684 _v)) : (e5108 _v) := by
  have p8663 := n8663 _v _q 
  have p12804 := n12804 _v _q h6684
  have p17872 := n17872 _v _q 
  have p5255 := n5255 _v _q 
  have p10893 := n10893 _v _q 
  have p5257 := n5257 _v _q 
  exact FloorCertificate.node_17916 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8663 p12804 p17872 p5255 p10893 p5257
theorem n17917 (_v : Vars) (_q : Query _v) (h6684 : (e6684 _v)) : (e5119 _v) := by
  have p14487 := n14487 _v _q 
  have p17916 := n17916 _v _q h6684
  change (e48 _v) ∨ (¬ (e5118 _v)) at p14487
  change (¬ (e48 _v)) at p17916
  rcases p14487 with hlit | hlit
  · exact (False.elim (p17916 hlit))
  · exact hlit
theorem n17918 (_v : Vars) (_q : Query _v) (h6684 : (e6684 _v)) : (e2358 _v) := by
  have p10893 := n10893 _v _q 
  have p8663 := n8663 _v _q 
  have p12804 := n12804 _v _q h6684
  have p5255 := n5255 _v _q 
  have p5257 := n5257 _v _q 
  have p17872 := n17872 _v _q 
  exact FloorCertificate.node_17918 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p10893 p8663 p12804 p5255 p5257 p17872
theorem n17919 (_v : Vars) (_q : Query _v) (h6684 : (e6684 _v)) : (e7640 _v) := by
  have p14828 := n14828 _v _q 
  have p17918 := n17918 _v _q h6684
  change (¬ (e2358 _v)) ∨ (¬ (e7634 _v)) at p14828
  rcases p14828 with hlit | hlit
  · exact (False.elim (hlit p17918))
  · exact hlit
theorem n17920 (_v : Vars) (_q : Query _v) (h6684 : (e6684 _v)) : (e5392 _v) := by
  have p12804 := n12804 _v _q h6684
  have p10893 := n10893 _v _q 
  have p8663 := n8663 _v _q 
  have p5255 := n5255 _v _q 
  have p17872 := n17872 _v _q 
  have p5257 := n5257 _v _q 
  exact FloorCertificate.node_17920 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p12804 p10893 p8663 p5255 p17872 p5257
theorem n17921 (_v : Vars) (_q : Query _v) (h6684 : (e6684 _v)) : (e5403 _v) := by
  have p14577 := n14577 _v _q 
  have p17920 := n17920 _v _q h6684
  change (e474 _v) ∨ (¬ (e5402 _v)) at p14577
  change (¬ (e474 _v)) at p17920
  rcases p14577 with hlit | hlit
  · exact (False.elim (p17920 hlit))
  · exact hlit
theorem n17922 (_v : Vars) (_q : Query _v) (h6684 : (e6684 _v)) : (e6549 _v) := by
  have p10893 := n10893 _v _q 
  have p12804 := n12804 _v _q h6684
  have p8663 := n8663 _v _q 
  have p5255 := n5255 _v _q 
  have p5257 := n5257 _v _q 
  have p17872 := n17872 _v _q 
  exact FloorCertificate.node_17922 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p10893 p12804 p8663 p5255 p5257 p17872
theorem n17923 (_v : Vars) (_q : Query _v) (h6684 : (e6684 _v)) : (e6879 _v) := by
  have p14643 := n14643 _v _q 
  have p17922 := n17922 _v _q h6684
  change (e2296 _v) ∨ (¬ (e6878 _v)) at p14643
  change (¬ (e2296 _v)) at p17922
  rcases p14643 with hlit | hlit
  · exact (False.elim (p17922 hlit))
  · exact hlit
theorem n17924 (_v : Vars) (_q : Query _v) (h6684 : (e6684 _v)) : (e2787 _v) := by
  have p12804 := n12804 _v _q h6684
  have p8663 := n8663 _v _q 
  have p10893 := n10893 _v _q 
  have p5255 := n5255 _v _q 
  have p5257 := n5257 _v _q 
  have p17872 := n17872 _v _q 
  exact FloorCertificate.node_17924 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p12804 p8663 p10893 p5255 p5257 p17872
theorem n17925 (_v : Vars) (_q : Query _v) (h6684 : (e6684 _v)) : (e7927 _v) := by
  have p14855 := n14855 _v _q 
  have p17924 := n17924 _v _q h6684
  change (¬ (e2787 _v)) ∨ (¬ (e7921 _v)) at p14855
  rcases p14855 with hlit | hlit
  · exact (False.elim (hlit p17924))
  · exact hlit
theorem n17926 (_v : Vars) (_q : Query _v) (h6684 : (e6684 _v)) : (e2529 _v) := by
  have p8663 := n8663 _v _q 
  have p12804 := n12804 _v _q h6684
  have p5257 := n5257 _v _q 
  have p10893 := n10893 _v _q 
  have p17872 := n17872 _v _q 
  have p5255 := n5255 _v _q 
  exact FloorCertificate.node_17926 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8663 p12804 p5257 p10893 p17872 p5255
theorem n17927 (_v : Vars) (_q : Query _v) (h6684 : (e6684 _v)) : (e8307 _v) := by
  have p14906 := n14906 _v _q 
  have p17926 := n17926 _v _q h6684
  change (¬ (e2529 _v)) ∨ (¬ (e8301 _v)) at p14906
  rcases p14906 with hlit | hlit
  · exact (False.elim (hlit p17926))
  · exact hlit
theorem n17928 (_v : Vars) (_q : Query _v) (h6684 : (e6684 _v)) : (e6650 _v) := by
  have p12804 := n12804 _v _q h6684
  have p5255 := n5255 _v _q 
  have p10893 := n10893 _v _q 
  have p8663 := n8663 _v _q 
  have p17872 := n17872 _v _q 
  have p5257 := n5257 _v _q 
  exact FloorCertificate.node_17928 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p12804 p5255 p10893 p8663 p17872 p5257
theorem n17929 (_v : Vars) (_q : Query _v) (h6684 : (e6684 _v)) : (e8292 _v) := by
  have p14657 := n14657 _v _q 
  have p17928 := n17928 _v _q h6684
  change (e2522 _v) ∨ (¬ (e8284 _v)) at p14657
  change (¬ (e2522 _v)) at p17928
  rcases p14657 with hlit | hlit
  · exact (False.elim (p17928 hlit))
  · exact hlit
theorem n17930 (_v : Vars) (_q : Query _v) (h6684 : (e6684 _v)) : (e436 _v) := by
  have p8663 := n8663 _v _q 
  have p12804 := n12804 _v _q h6684
  have p17872 := n17872 _v _q 
  have p10893 := n10893 _v _q 
  have p5255 := n5255 _v _q 
  have p5257 := n5257 _v _q 
  exact FloorCertificate.node_17930 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8663 p12804 p17872 p10893 p5255 p5257
theorem n17931 (_v : Vars) (_q : Query _v) (h6684 : (e6684 _v)) : (e5370 _v) := by
  have p14735 := n14735 _v _q 
  have p17930 := n17930 _v _q h6684
  change (¬ (e436 _v)) ∨ (¬ (e5360 _v)) at p14735
  rcases p14735 with hlit | hlit
  · exact (False.elim (hlit p17930))
  · exact hlit
theorem n17932 (_v : Vars) (_q : Query _v) (h6684 : (e6684 _v)) : (e6742 _v) := by
  have p5255 := n5255 _v _q 
  have p17872 := n17872 _v _q 
  have p12804 := n12804 _v _q h6684
  have p10893 := n10893 _v _q 
  have p8663 := n8663 _v _q 
  have p5257 := n5257 _v _q 
  exact FloorCertificate.node_17932 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p5255 p17872 p12804 p10893 p8663 p5257
theorem n17933 (_v : Vars) (_q : Query _v) (h6684 : (e6684 _v)) : (e8358 _v) := by
  have p14673 := n14673 _v _q 
  have p17932 := n17932 _v _q h6684
  change (e2722 _v) ∨ (¬ (e8350 _v)) at p14673
  change (¬ (e2722 _v)) at p17932
  rcases p14673 with hlit | hlit
  · exact (False.elim (p17932 hlit))
  · exact hlit
theorem n17934 (_v : Vars) (_q : Query _v) (h6684 : (e6684 _v)) : (e6501 _v) := by
  have p12804 := n12804 _v _q h6684
  have p10893 := n10893 _v _q 
  have p5255 := n5255 _v _q 
  have p5257 := n5257 _v _q 
  have p17872 := n17872 _v _q 
  exact FloorCertificate.node_17934 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p12804 p10893 p5255 p5257 p17872
theorem n17935 (_v : Vars) (_q : Query _v) (h6684 : (e6684 _v)) : (e8103 _v) := by
  have p14626 := n14626 _v _q 
  have p17934 := n17934 _v _q h6684
  change (e2179 _v) ∨ (¬ (e8095 _v)) at p14626
  change (¬ (e2179 _v)) at p17934
  rcases p14626 with hlit | hlit
  · exact (False.elim (p17934 hlit))
  · exact hlit
theorem n17936 (_v : Vars) (_q : Query _v) (h6684 : (e6684 _v)) : (e6750 _v) := by
  have p8663 := n8663 _v _q 
  have p12804 := n12804 _v _q h6684
  have p5255 := n5255 _v _q 
  have p10893 := n10893 _v _q 
  have p5257 := n5257 _v _q 
  have p17872 := n17872 _v _q 
  exact FloorCertificate.node_17936 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8663 p12804 p5255 p10893 p5257 p17872
theorem n17937 (_v : Vars) (_q : Query _v) (h6684 : (e6684 _v)) : (e7597 _v) := by
  have p14525 := n14525 _v _q 
  have p17936 := n17936 _v _q h6684
  change (e2733 _v) ∨ (¬ (e7589 _v)) at p14525
  change (¬ (e2733 _v)) at p17936
  rcases p14525 with hlit | hlit
  · exact (False.elim (p17936 hlit))
  · exact hlit
theorem n17938 (_v : Vars) (_q : Query _v) (h6684 : (e6684 _v)) : (e6600 _v) := by
  have p5255 := n5255 _v _q 
  have p12804 := n12804 _v _q h6684
  have p10893 := n10893 _v _q 
  have p17872 := n17872 _v _q 
  have p5257 := n5257 _v _q 
  exact FloorCertificate.node_17938 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p5255 p12804 p10893 p17872 p5257
theorem n17939 (_v : Vars) (_q : Query _v) (h6684 : (e6684 _v)) : (e7416 _v) := by
  have p14534 := n14534 _v _q 
  have p17938 := n17938 _v _q h6684
  change (e2402 _v) ∨ (¬ (e7415 _v)) at p14534
  change (¬ (e2402 _v)) at p17938
  rcases p14534 with hlit | hlit
  · exact (False.elim (p17938 hlit))
  · exact hlit
theorem n17940 (_v : Vars) (_q : Query _v) (h6684 : (e6684 _v)) : (e79 _v) := by
  have p12804 := n12804 _v _q h6684
  have p8663 := n8663 _v _q 
  have p5255 := n5255 _v _q 
  have p5257 := n5257 _v _q 
  have p10893 := n10893 _v _q 
  have p17872 := n17872 _v _q 
  exact FloorCertificate.node_17940 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p12804 p8663 p5255 p5257 p10893 p17872
theorem n17941 (_v : Vars) (_q : Query _v) (h6684 : (e6684 _v)) : (e5135 _v) := by
  have p14729 := n14729 _v _q 
  have p17940 := n17940 _v _q h6684
  change (¬ (e79 _v)) ∨ (¬ (e5134 _v)) at p14729
  rcases p14729 with hlit | hlit
  · exact (False.elim (hlit p17940))
  · exact hlit
theorem n17942 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h225 : (e225 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h4096 : (e4096 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h6758 : (e6758 _v)) : (e2475 _v) := by
  have p17852 := n17852 _v _q 
  have p16520 := n16520 _v _q h6758
  have p4986 := n4986 _v _q h3105
  have p4983 := n4983 _v _q h4813
  have p4994 := n4994 _v _q h3069
  have p4984 := n4984 _v _q h4872
  have p4991 := n4991 _v _q h4608
  have p4988 := n4988 _v _q h488
  have p4998 := n4998 _v _q h3152
  have p4995 := n4995 _v _q h4369
  have p4999 := n4999 _v _q h91
  have p5001 := n5001 _v _q h4096
  have p12891 := n12891 _v _q h6758
  have p4996 := n4996 _v _q h3937
  have p5007 := n5007 _v _q h225
  have p4987 := n4987 _v _q h4434
  have p5008 := n5008 _v _q h4787
  change (e2793 _v) ∨ (¬ (e488 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (e2475 _v) ∨ (¬ (e3152 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e4787 _v)) at p17852
  change (¬ (e2793 _v)) at p12891
  rcases p17852 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact (False.elim (p12891 hlit))
  · exact (False.elim (hlit p4988))
  · exact (False.elim (hlit p4986))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p4994))
  · exact (False.elim (hlit p4984))
  · exact (False.elim (hlit p4991))
  · exact hlit
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p4995))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p5001))
  · exact (False.elim (hlit p16520))
  · exact (False.elim (hlit p4996))
  · exact (False.elim (hlit p5007))
  · exact (False.elim (hlit p4987))
  · exact (False.elim (hlit p5008))
theorem n17943 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h436 : (e436 _v)) (h496 : (e496 _v)) (h3133 : (e3133 _v)) (h3158 : (e3158 _v)) (h3919 : (e3919 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4101 : (e4101 _v)) (h4264 : (e4264 _v)) (h4306 : (e4306 _v)) (h4373 : (e4373 _v)) (h4398 : (e4398 _v)) (h4439 : (e4439 _v)) (h4459 : (e4459 _v)) (h4491 : (e4491 _v)) (h4567 : (e4567 _v)) (h4653 : (e4653 _v)) (h4679 : (e4679 _v)) (h4724 : (e4724 _v)) (h4791 : (e4791 _v)) (h4817 : (e4817 _v)) (h4903 : (e4903 _v)) (h5223 : (e5223 _v)) (h6742 : (e6742 _v)) : (e7489 _v) := by
  have p16150 := n16150 _v _q h436
  have p16152 := n16152 _v _q h436
  have p5391 := n5391 _v _q 
  have p14739 := n14739 _v _q h496
  have p8144 := n8144 _v _q h496
  have p5255 := n5255 _v _q 
  have p11520 := n11520 _v _q h5223
  have p17085 := n17085 _v _q h4373
  have p17078 := n17078 _v _q 
  have p17080 := n17080 _v _q 
  have p17083 := n17083 _v _q 
  have p17074 := n17074 _v _q 
  have p14766 := n14766 _v _q h496
  have p17087 := n17087 _v _q 
  have p17758 := n17758 _v _q 
  have p17091 := n17091 _v _q 
  have p17093 := n17093 _v _q 
  have p14998 := n14998 _v _q h5223
  have p15001 := n15001 _v _q h6742
  have p17138 := n17138 _v _q h4306
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p17100 := n17100 _v _q 
  have p17102 := n17102 _v _q 
  have p16885 := n16885 _v _q h3158
  have p17104 := n17104 _v _q 
  have p15004 := n15004 _v _q h496
  have p17096 := n17096 _v _q 
  have p17111 := n17111 _v _q 
  have p17051 := n17051 _v _q h4459
  have p17113 := n17113 _v _q 
  have p17060 := n17060 _v _q h4653
  have p17137 := n17137 _v _q h4059
  have p17079 := n17079 _v _q h3919
  have p16729 := n16729 _v _q h51
  have p17062 := n17062 _v _q h3133
  have p17122 := n17122 _v _q 
  have p17117 := n17117 _v _q 
  have p17124 := n17124 _v _q 
  have p17115 := n17115 _v _q 
  have p17120 := n17120 _v _q 
  have p17128 := n17128 _v _q h4491
  have p17127 := n17127 _v _q 
  have p16778 := n16778 _v _q 
  have p17874 := n17874 _v _q 
  have p17131 := n17131 _v _q 
  have p17110 := n17110 _v _q 
  have p17133 := n17133 _v _q 
  have p17094 := n17094 _v _q h4724
  have p17143 := n17143 _v _q h4567
  have p17050 := n17050 _v _q 
  have p17059 := n17059 _v _q h4791
  have p17294 := n17294 _v _q 
  have p17136 := n17136 _v _q 
  have p17141 := n17141 _v _q 
  have p17134 := n17134 _v _q h4398
  have p17070 := n17070 _v _q h4679
  have p17088 := n17088 _v _q h4817
  have p17118 := n17118 _v _q h4264
  have p17065 := n17065 _v _q h4101
  have p17129 := n17129 _v _q h4903
  have p17053 := n17053 _v _q 
  have p17089 := n17089 _v _q 
  have p17055 := n17055 _v _q 
  have p17108 := n17108 _v _q 
  have p17075 := n17075 _v _q h4439
  have p17058 := n17058 _v _q 
  have p17076 := n17076 _v _q h3976
  have p17064 := n17064 _v _q 
  have p17067 := n17067 _v _q 
  have p17069 := n17069 _v _q 
  have p17072 := n17072 _v _q 
  have p13951 := n13951 _v _q 
  have p8416 := n8416 _v _q h6742
  exact FloorCertificate.node_17943 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e101 _v) (e110 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) p16150 p16152 p5391 p14739 p8144 p5255 p11520 p17085 p17078 p17080 p17083 p17074 p14766 p17087 p17758 p17091 p17093 p14998 p15001 p17138 p17098 p17106 p17100 p17102 p16885 p17104 p15004 p17096 p17111 p17051 p17113 p17060 p17137 p17079 p16729 p17062 p17122 p17117 p17124 p17115 p17120 p17128 p17127 p16778 p17874 p17131 p17110 p17133 p17094 p17143 p17050 p17059 p17294 p17136 p17141 p17134 p17070 p17088 p17118 p17065 p17129 p17053 p17089 p17055 p17108 p17075 p17058 p17076 p17064 p17067 p17069 p17072 p13951 p8416
theorem n17944 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) (h5362 : (e5362 _v)) (h5392 : (e5392 _v)) : (e7714 _v) := by
  have p16861 := n16861 _v _q 
  have p15079 := n15079 _v _q h2468 h5362 h5392
  change (e7726 _v) ∨ (e7714 _v) at p16861
  change (¬ (e7726 _v)) at p15079
  rcases p16861 with hlit | hlit
  · exact (False.elim (p15079 hlit))
  · exact hlit
theorem n17945 (_v : Vars) (_q : Query _v) (h5362 : (e5362 _v)) : (e5237 _v) := by
  have p8682 := n8682 _v _q 
  have p15081 := n15081 _v _q h5362
  change (e5249 _v) ∨ (e5237 _v) at p8682
  change (¬ (e5249 _v)) at p15081
  rcases p8682 with hlit | hlit
  · exact (False.elim (p15081 hlit))
  · exact hlit
theorem n17946 (_v : Vars) (_q : Query _v) (h2296 : (e2296 _v)) : (e4653 _v) := by
  have p15168 := n15168 _v _q 
  have p17681 := n17681 _v _q h2296
  change (e4660 _v) ∨ (e4653 _v) at p15168
  change (¬ (e4660 _v)) at p17681
  rcases p15168 with hlit | hlit
  · exact (False.elim (p17681 hlit))
  · exact hlit
theorem n17947 (_v : Vars) (_q : Query _v) (h2296 : (e2296 _v)) : (e4059 _v) := by
  have p14980 := n14980 _v _q 
  have p17683 := n17683 _v _q h2296
  change (e4066 _v) ∨ (e4059 _v) at p14980
  change (¬ (e4066 _v)) at p17683
  rcases p14980 with hlit | hlit
  · exact (False.elim (p17683 hlit))
  · exact hlit
theorem n17948 (_v : Vars) (_q : Query _v) (h2296 : (e2296 _v)) : (e4491 _v) := by
  have p14969 := n14969 _v _q 
  have p17685 := n17685 _v _q h2296
  change (e4498 _v) ∨ (e4491 _v) at p14969
  change (¬ (e4498 _v)) at p17685
  rcases p14969 with hlit | hlit
  · exact (False.elim (p17685 hlit))
  · exact hlit
theorem n17949 (_v : Vars) (_q : Query _v) (h2296 : (e2296 _v)) : (e4724 _v) := by
  have p15518 := n15518 _v _q 
  have p17687 := n17687 _v _q h2296
  change (e4730 _v) ∨ (e4724 _v) at p15518
  change (¬ (e4730 _v)) at p17687
  rcases p15518 with hlit | hlit
  · exact (False.elim (p17687 hlit))
  · exact hlit
theorem n17950 (_v : Vars) (_q : Query _v) (h2296 : (e2296 _v)) : (e4903 _v) := by
  have p14973 := n14973 _v _q 
  have p17689 := n17689 _v _q h2296
  change (e4909 _v) ∨ (e4903 _v) at p14973
  change (¬ (e4909 _v)) at p17689
  rcases p14973 with hlit | hlit
  · exact (False.elim (p17689 hlit))
  · exact hlit
theorem n17951 (_v : Vars) (_q : Query _v) (h2296 : (e2296 _v)) : (e4439 _v) := by
  have p14925 := n14925 _v _q 
  have p15114 := n15114 _v _q h2296
  change (e4446 _v) ∨ (e4439 _v) at p14925
  change (¬ (e4446 _v)) at p15114
  rcases p14925 with hlit | hlit
  · exact (False.elim (p15114 hlit))
  · exact hlit
theorem n17952 (_v : Vars) (_q : Query _v) (h2296 : (e2296 _v)) : (e3976 _v) := by
  have p14935 := n14935 _v _q 
  have p17691 := n17691 _v _q h2296
  change (e3983 _v) ∨ (e3976 _v) at p14935
  change (¬ (e3983 _v)) at p17691
  rcases p14935 with hlit | hlit
  · exact (False.elim (p17691 hlit))
  · exact hlit
theorem n17953 (_v : Vars) (_q : Query _v)  : (e5208 _v) := by
  by_contra hc
  change ¬ (e5208 _v) at hc
  have h5218 : (e5218 _v) := (fun hn => hc hn)
  have p16756 := n16756 _v _q h5218
  exact p16756
theorem n17954 (_v : Vars) (_q : Query _v) (h2296 : (e2296 _v)) (h2468 : (e2468 _v)) (h4264 : (e4264 _v)) (h4373 : (e4373 _v)) (h4817 : (e4817 _v)) (h4872 : (e4872 _v)) (h5362 : (e5362 _v)) (h5392 : (e5392 _v)) : (e4157 _v) := by
  have p17256 := n17256 _v _q 
  have p8583 := n8583 _v _q h2296
  have p8438 := n8438 _v _q h2468
  have p15092 := n15092 _v _q h5392
  have p15074 := n15074 _v _q h5392
  have p15075 := n15075 _v _q h5392
  have p17085 := n17085 _v _q h4373
  have p7488 := n7488 _v _q h5362
  have p16326 := n16326 _v _q h5392
  have p17944 := n17944 _v _q h2468 h5362 h5392
  have p17087 := n17087 _v _q 
  have p17758 := n17758 _v _q 
  have p17091 := n17091 _v _q 
  have p17093 := n17093 _v _q 
  have p17945 := n17945 _v _q h5362
  have p4984 := n4984 _v _q h4872
  have p15083 := n15083 _v _q h2296
  have p15087 := n15087 _v _q h5362
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p17100 := n17100 _v _q 
  have p17102 := n17102 _v _q 
  have p16859 := n16859 _v _q h2468
  have p17104 := n17104 _v _q 
  have p17096 := n17096 _v _q 
  have p17111 := n17111 _v _q 
  have p15094 := n15094 _v _q h2296
  have p17113 := n17113 _v _q 
  have p17946 := n17946 _v _q h2296
  have p17947 := n17947 _v _q h2296
  have p15073 := n15073 _v _q h2468
  have p15097 := n15097 _v _q h2296
  have p15100 := n15100 _v _q h2296
  have p17122 := n17122 _v _q 
  have p17117 := n17117 _v _q 
  have p17124 := n17124 _v _q 
  have p17115 := n17115 _v _q 
  have p17120 := n17120 _v _q 
  have p17948 := n17948 _v _q h2296
  have p17127 := n17127 _v _q 
  have p16778 := n16778 _v _q 
  have p17874 := n17874 _v _q 
  have p17131 := n17131 _v _q 
  have p17110 := n17110 _v _q 
  have p17133 := n17133 _v _q 
  have p17949 := n17949 _v _q h2296
  have p15102 := n15102 _v _q h2296
  have p17050 := n17050 _v _q 
  have p15104 := n15104 _v _q h2468
  have p17294 := n17294 _v _q 
  have p17136 := n17136 _v _q 
  have p17141 := n17141 _v _q 
  have p15107 := n15107 _v _q h2296
  have p15110 := n15110 _v _q h2296
  have p17088 := n17088 _v _q h4817
  have p17118 := n17118 _v _q h4264
  have p15113 := n15113 _v _q h2296
  have p17950 := n17950 _v _q h2296
  have p17053 := n17053 _v _q 
  have p17089 := n17089 _v _q 
  have p17055 := n17055 _v _q 
  have p17108 := n17108 _v _q 
  have p17951 := n17951 _v _q h2296
  have p17058 := n17058 _v _q 
  have p17952 := n17952 _v _q h2296
  have p17064 := n17064 _v _q 
  have p17067 := n17067 _v _q 
  have p17069 := n17069 _v _q 
  have p17072 := n17072 _v _q 
  have p17074 := n17074 _v _q 
  have p17078 := n17078 _v _q 
  have p17080 := n17080 _v _q 
  have p17083 := n17083 _v _q 
  have p13951 := n13951 _v _q 
  have p17953 := n17953 _v _q 
  exact FloorCertificate.node_17954 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2902 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) p17256 p8583 p8438 p15092 p15074 p15075 p17085 p7488 p16326 p17944 p17087 p17758 p17091 p17093 p17945 p4984 p15083 p15087 p17098 p17106 p17100 p17102 p16859 p17104 p17096 p17111 p15094 p17113 p17946 p17947 p15073 p15097 p15100 p17122 p17117 p17124 p17115 p17120 p17948 p17127 p16778 p17874 p17131 p17110 p17133 p17949 p15102 p17050 p15104 p17294 p17136 p17141 p15107 p15110 p17088 p17118 p15113 p17950 p17053 p17089 p17055 p17108 p17951 p17058 p17952 p17064 p17067 p17069 p17072 p17074 p17078 p17080 p17083 p13951 p17953
theorem n17955 (_v : Vars) (_q : Query _v) (h2522 : (e2522 _v)) : (e3919 _v) := by
  have p14797 := n14797 _v _q 
  have p15120 := n15120 _v _q h2522
  change (e3923 _v) ∨ (e3919 _v) at p14797
  change (¬ (e3923 _v)) at p15120
  rcases p14797 with hlit | hlit
  · exact (False.elim (p15120 hlit))
  · exact hlit
theorem n17956 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) (h467 : (e467 _v)) (h2296 : (e2296 _v)) (h2522 : (e2522 _v)) (h3051 : (e3051 _v)) (h4161 : (e4161 _v)) (h4264 : (e4264 _v)) (h5362 : (e5362 _v)) (h6742 : (e6742 _v)) : (e5247 _v) := by
  have p15001 := n15001 _v _q h6742
  have p8416 := n8416 _v _q h6742
  have p15087 := n15087 _v _q h5362
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p17100 := n17100 _v _q 
  have p17102 := n17102 _v _q 
  have p17678 := n17678 _v _q 
  have p17125 := n17125 _v _q h3051
  have p17104 := n17104 _v _q 
  have p17081 := n17081 _v _q h4161
  have p17096 := n17096 _v _q 
  have p17111 := n17111 _v _q 
  have p15094 := n15094 _v _q h2296
  have p17084 := n17084 _v _q h467
  have p17113 := n17113 _v _q 
  have p15119 := n15119 _v _q h251
  have p17946 := n17946 _v _q h2296
  have p17947 := n17947 _v _q h2296
  have p17955 := n17955 _v _q h2522
  have p15097 := n15097 _v _q h2296
  have p15100 := n15100 _v _q h2296
  have p17122 := n17122 _v _q 
  have p17117 := n17117 _v _q 
  have p17124 := n17124 _v _q 
  have p17115 := n17115 _v _q 
  have p17120 := n17120 _v _q 
  have p17948 := n17948 _v _q h2296
  have p17127 := n17127 _v _q 
  have p16778 := n16778 _v _q 
  have p17874 := n17874 _v _q 
  have p17131 := n17131 _v _q 
  have p17110 := n17110 _v _q 
  have p17133 := n17133 _v _q 
  have p17949 := n17949 _v _q h2296
  have p15102 := n15102 _v _q h2296
  have p17050 := n17050 _v _q 
  have p15122 := n15122 _v _q h2522
  have p17294 := n17294 _v _q 
  have p17136 := n17136 _v _q 
  have p17141 := n17141 _v _q 
  have p15107 := n15107 _v _q h2296
  have p15110 := n15110 _v _q h2296
  have p15125 := n15125 _v _q h2522
  have p17118 := n17118 _v _q h4264
  have p15113 := n15113 _v _q h2296
  have p17950 := n17950 _v _q h2296
  have p17053 := n17053 _v _q 
  have p17089 := n17089 _v _q 
  have p17055 := n17055 _v _q 
  have p17108 := n17108 _v _q 
  have p17951 := n17951 _v _q h2296
  have p17058 := n17058 _v _q 
  have p17952 := n17952 _v _q h2296
  have p17064 := n17064 _v _q 
  have p17067 := n17067 _v _q 
  have p17069 := n17069 _v _q 
  have p17072 := n17072 _v _q 
  have p17074 := n17074 _v _q 
  have p17078 := n17078 _v _q 
  have p17080 := n17080 _v _q 
  have p17083 := n17083 _v _q 
  have p15128 := n15128 _v _q h2522
  have p17087 := n17087 _v _q 
  have p17758 := n17758 _v _q 
  have p17091 := n17091 _v _q 
  have p17093 := n17093 _v _q 
  have p15083 := n15083 _v _q h2296
  have p13951 := n13951 _v _q 
  have p12831 := n12831 _v _q h2522
  have p8583 := n8583 _v _q h2296
  have p11374 := n11374 _v _q h251
  have p7488 := n7488 _v _q h5362
  exact FloorCertificate.node_17956 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e101 _v) (e110 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) p15001 p8416 p15087 p17098 p17106 p17100 p17102 p17678 p17125 p17104 p17081 p17096 p17111 p15094 p17084 p17113 p15119 p17946 p17947 p17955 p15097 p15100 p17122 p17117 p17124 p17115 p17120 p17948 p17127 p16778 p17874 p17131 p17110 p17133 p17949 p15102 p17050 p15122 p17294 p17136 p17141 p15107 p15110 p15125 p17118 p15113 p17950 p17053 p17089 p17055 p17108 p17951 p17058 p17952 p17064 p17067 p17069 p17072 p17074 p17078 p17080 p17083 p15128 p17087 p17758 p17091 p17093 p15083 p13951 p12831 p8583 p11374 p7488
theorem n17957 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) (h467 : (e467 _v)) (h2296 : (e2296 _v)) (h2522 : (e2522 _v)) (h3051 : (e3051 _v)) (h4161 : (e4161 _v)) (h4264 : (e4264 _v)) (h5362 : (e5362 _v)) (h6742 : (e6742 _v)) : (e230 _v) := by
  have p15001 := n15001 _v _q h6742
  have p17678 := n17678 _v _q 
  have p11374 := n11374 _v _q h251
  have p15087 := n15087 _v _q h5362
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p17100 := n17100 _v _q 
  have p17102 := n17102 _v _q 
  have p17125 := n17125 _v _q h3051
  have p17104 := n17104 _v _q 
  have p17081 := n17081 _v _q h4161
  have p17096 := n17096 _v _q 
  have p17111 := n17111 _v _q 
  have p15094 := n15094 _v _q h2296
  have p17084 := n17084 _v _q h467
  have p17113 := n17113 _v _q 
  have p15119 := n15119 _v _q h251
  have p17946 := n17946 _v _q h2296
  have p17947 := n17947 _v _q h2296
  have p17955 := n17955 _v _q h2522
  have p15097 := n15097 _v _q h2296
  have p15100 := n15100 _v _q h2296
  have p17122 := n17122 _v _q 
  have p17117 := n17117 _v _q 
  have p17124 := n17124 _v _q 
  have p17115 := n17115 _v _q 
  have p17120 := n17120 _v _q 
  have p17948 := n17948 _v _q h2296
  have p17127 := n17127 _v _q 
  have p16778 := n16778 _v _q 
  have p17874 := n17874 _v _q 
  have p17131 := n17131 _v _q 
  have p17110 := n17110 _v _q 
  have p17133 := n17133 _v _q 
  have p17949 := n17949 _v _q h2296
  have p15102 := n15102 _v _q h2296
  have p17050 := n17050 _v _q 
  have p15122 := n15122 _v _q h2522
  have p17294 := n17294 _v _q 
  have p17136 := n17136 _v _q 
  have p17141 := n17141 _v _q 
  have p15107 := n15107 _v _q h2296
  have p15110 := n15110 _v _q h2296
  have p15125 := n15125 _v _q h2522
  have p17118 := n17118 _v _q h4264
  have p15113 := n15113 _v _q h2296
  have p17950 := n17950 _v _q h2296
  have p17053 := n17053 _v _q 
  have p17089 := n17089 _v _q 
  have p17055 := n17055 _v _q 
  have p17108 := n17108 _v _q 
  have p17951 := n17951 _v _q h2296
  have p17058 := n17058 _v _q 
  have p17952 := n17952 _v _q h2296
  have p17064 := n17064 _v _q 
  have p17067 := n17067 _v _q 
  have p17069 := n17069 _v _q 
  have p17072 := n17072 _v _q 
  have p17074 := n17074 _v _q 
  have p17078 := n17078 _v _q 
  have p17080 := n17080 _v _q 
  have p17083 := n17083 _v _q 
  have p15128 := n15128 _v _q h2522
  have p17087 := n17087 _v _q 
  have p17758 := n17758 _v _q 
  have p17091 := n17091 _v _q 
  have p17093 := n17093 _v _q 
  have p15083 := n15083 _v _q h2296
  have p13951 := n13951 _v _q 
  have p12831 := n12831 _v _q h2522
  have p8416 := n8416 _v _q h6742
  have p8583 := n8583 _v _q h2296
  exact FloorCertificate.node_17957 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e101 _v) (e110 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) p15001 p17678 p11374 p15087 p17098 p17106 p17100 p17102 p17125 p17104 p17081 p17096 p17111 p15094 p17084 p17113 p15119 p17946 p17947 p17955 p15097 p15100 p17122 p17117 p17124 p17115 p17120 p17948 p17127 p16778 p17874 p17131 p17110 p17133 p17949 p15102 p17050 p15122 p17294 p17136 p17141 p15107 p15110 p15125 p17118 p15113 p17950 p17053 p17089 p17055 p17108 p17951 p17058 p17952 p17064 p17067 p17069 p17072 p17074 p17078 p17080 p17083 p15128 p17087 p17758 p17091 p17093 p15083 p13951 p12831 p8416 p8583
theorem n17958 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2722 : (e2722 _v)) (h3133 : (e3133 _v)) (h3158 : (e3158 _v)) (h3919 : (e3919 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4101 : (e4101 _v)) (h4161 : (e4161 _v)) (h4264 : (e4264 _v)) (h4306 : (e4306 _v)) (h4398 : (e4398 _v)) (h4439 : (e4439 _v)) (h4459 : (e4459 _v)) (h4491 : (e4491 _v)) (h4567 : (e4567 _v)) (h4653 : (e4653 _v)) (h4679 : (e4679 _v)) (h4724 : (e4724 _v)) (h4791 : (e4791 _v)) (h4817 : (e4817 _v)) (h4903 : (e4903 _v)) (h5195 : (e5195 _v)) : (e5386 _v) := by
  have p5257 := n5257 _v _q 
  have p17106 := n17106 _v _q 
  have p8410 := n8410 _v _q h2722
  have p5255 := n5255 _v _q 
  have p17678 := n17678 _v _q 
  have p15140 := n15140 _v _q h2722
  have p13951 := n13951 _v _q 
  have p17081 := n17081 _v _q h4161
  have p12839 := n12839 _v _q h5195
  have p17111 := n17111 _v _q 
  have p17051 := n17051 _v _q h4459
  have p15143 := n15143 _v _q h2722
  have p17113 := n17113 _v _q 
  have p15146 := n15146 _v _q h2722
  have p17060 := n17060 _v _q h4653
  have p17137 := n17137 _v _q h4059
  have p17079 := n17079 _v _q h3919
  have p16729 := n16729 _v _q h51
  have p17062 := n17062 _v _q h3133
  have p17122 := n17122 _v _q 
  have p17117 := n17117 _v _q 
  have p17124 := n17124 _v _q 
  have p17115 := n17115 _v _q 
  have p17120 := n17120 _v _q 
  have p17128 := n17128 _v _q h4491
  have p17127 := n17127 _v _q 
  have p16778 := n16778 _v _q 
  have p17874 := n17874 _v _q 
  have p15148 := n15148 _v _q h2722
  have p17131 := n17131 _v _q 
  have p17110 := n17110 _v _q 
  have p17133 := n17133 _v _q 
  have p17094 := n17094 _v _q h4724
  have p17143 := n17143 _v _q h4567
  have p17050 := n17050 _v _q 
  have p17059 := n17059 _v _q h4791
  have p17294 := n17294 _v _q 
  have p17136 := n17136 _v _q 
  have p17141 := n17141 _v _q 
  have p17134 := n17134 _v _q h4398
  have p17070 := n17070 _v _q h4679
  have p17088 := n17088 _v _q h4817
  have p17118 := n17118 _v _q h4264
  have p17065 := n17065 _v _q h4101
  have p17129 := n17129 _v _q h4903
  have p17053 := n17053 _v _q 
  have p17089 := n17089 _v _q 
  have p17055 := n17055 _v _q 
  have p17108 := n17108 _v _q 
  have p17075 := n17075 _v _q h4439
  have p17058 := n17058 _v _q 
  have p17076 := n17076 _v _q h3976
  have p17064 := n17064 _v _q 
  have p17067 := n17067 _v _q 
  have p17069 := n17069 _v _q 
  have p17072 := n17072 _v _q 
  have p17074 := n17074 _v _q 
  have p17078 := n17078 _v _q 
  have p17080 := n17080 _v _q 
  have p17083 := n17083 _v _q 
  have p16885 := n16885 _v _q h3158
  have p17087 := n17087 _v _q 
  have p17758 := n17758 _v _q 
  have p17091 := n17091 _v _q 
  have p17093 := n17093 _v _q 
  have p17138 := n17138 _v _q h4306
  have p17096 := n17096 _v _q 
  have p17098 := n17098 _v _q 
  have p17100 := n17100 _v _q 
  have p17102 := n17102 _v _q 
  have p17104 := n17104 _v _q 
  exact FloorCertificate.node_17958 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e101 _v) (e110 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) p5257 p17106 p8410 p5255 p17678 p15140 p13951 p17081 p12839 p17111 p17051 p15143 p17113 p15146 p17060 p17137 p17079 p16729 p17062 p17122 p17117 p17124 p17115 p17120 p17128 p17127 p16778 p17874 p15148 p17131 p17110 p17133 p17094 p17143 p17050 p17059 p17294 p17136 p17141 p17134 p17070 p17088 p17118 p17065 p17129 p17053 p17089 p17055 p17108 p17075 p17058 p17076 p17064 p17067 p17069 p17072 p17074 p17078 p17080 p17083 p16885 p17087 p17758 p17091 p17093 p17138 p17096 p17098 p17100 p17102 p17104
theorem n17959 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2722 : (e2722 _v)) (h3133 : (e3133 _v)) (h3158 : (e3158 _v)) (h3919 : (e3919 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4101 : (e4101 _v)) (h4161 : (e4161 _v)) (h4264 : (e4264 _v)) (h4306 : (e4306 _v)) (h4398 : (e4398 _v)) (h4439 : (e4439 _v)) (h4459 : (e4459 _v)) (h4491 : (e4491 _v)) (h4567 : (e4567 _v)) (h4653 : (e4653 _v)) (h4679 : (e4679 _v)) (h4724 : (e4724 _v)) (h4791 : (e4791 _v)) (h4817 : (e4817 _v)) (h4903 : (e4903 _v)) (h5195 : (e5195 _v)) : (e443 _v) := by
  have p15140 := n15140 _v _q h2722
  have p13951 := n13951 _v _q 
  have p17081 := n17081 _v _q h4161
  have p17678 := n17678 _v _q 
  have p12839 := n12839 _v _q h5195
  have p8410 := n8410 _v _q h2722
  have p5257 := n5257 _v _q 
  have p17111 := n17111 _v _q 
  have p17051 := n17051 _v _q h4459
  have p15143 := n15143 _v _q h2722
  have p17113 := n17113 _v _q 
  have p15146 := n15146 _v _q h2722
  have p17060 := n17060 _v _q h4653
  have p17137 := n17137 _v _q h4059
  have p17079 := n17079 _v _q h3919
  have p16729 := n16729 _v _q h51
  have p17062 := n17062 _v _q h3133
  have p17122 := n17122 _v _q 
  have p17117 := n17117 _v _q 
  have p17124 := n17124 _v _q 
  have p17115 := n17115 _v _q 
  have p17120 := n17120 _v _q 
  have p17128 := n17128 _v _q h4491
  have p17127 := n17127 _v _q 
  have p16778 := n16778 _v _q 
  have p17874 := n17874 _v _q 
  have p15148 := n15148 _v _q h2722
  have p17131 := n17131 _v _q 
  have p17110 := n17110 _v _q 
  have p17133 := n17133 _v _q 
  have p17094 := n17094 _v _q h4724
  have p17143 := n17143 _v _q h4567
  have p17050 := n17050 _v _q 
  have p17059 := n17059 _v _q h4791
  have p17294 := n17294 _v _q 
  have p17136 := n17136 _v _q 
  have p17141 := n17141 _v _q 
  have p17134 := n17134 _v _q h4398
  have p17070 := n17070 _v _q h4679
  have p17088 := n17088 _v _q h4817
  have p17118 := n17118 _v _q h4264
  have p8549 := n8549 _v _q h5195
  have p17065 := n17065 _v _q h4101
  have p17129 := n17129 _v _q h4903
  have p17053 := n17053 _v _q 
  have p17089 := n17089 _v _q 
  have p17055 := n17055 _v _q 
  have p17108 := n17108 _v _q 
  have p17075 := n17075 _v _q h4439
  have p17058 := n17058 _v _q 
  have p17076 := n17076 _v _q h3976
  have p17064 := n17064 _v _q 
  have p17067 := n17067 _v _q 
  have p17069 := n17069 _v _q 
  have p17072 := n17072 _v _q 
  have p17074 := n17074 _v _q 
  have p17078 := n17078 _v _q 
  have p17080 := n17080 _v _q 
  have p17083 := n17083 _v _q 
  have p16885 := n16885 _v _q h3158
  have p17087 := n17087 _v _q 
  have p17758 := n17758 _v _q 
  have p17091 := n17091 _v _q 
  have p17093 := n17093 _v _q 
  have p17138 := n17138 _v _q h4306
  have p17096 := n17096 _v _q 
  have p17098 := n17098 _v _q 
  have p17100 := n17100 _v _q 
  have p17102 := n17102 _v _q 
  have p17104 := n17104 _v _q 
  have p17106 := n17106 _v _q 
  exact FloorCertificate.node_17959 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e101 _v) (e110 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) p15140 p13951 p17081 p17678 p12839 p8410 p5257 p17111 p17051 p15143 p17113 p15146 p17060 p17137 p17079 p16729 p17062 p17122 p17117 p17124 p17115 p17120 p17128 p17127 p16778 p17874 p15148 p17131 p17110 p17133 p17094 p17143 p17050 p17059 p17294 p17136 p17141 p17134 p17070 p17088 p17118 p8549 p17065 p17129 p17053 p17089 p17055 p17108 p17075 p17058 p17076 p17064 p17067 p17069 p17072 p17074 p17078 p17080 p17083 p16885 p17087 p17758 p17091 p17093 p17138 p17096 p17098 p17100 p17102 p17104 p17106
theorem n17961 (_v : Vars) (_q : Query _v)  : (e17960 _v) := by
  by_contra hc
  change ¬ ((e2358 _v) ∨ (¬ (e7493 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e2061 _v)) ∨ (e2634 _v) ∨ (¬ (e3946 _v)) ∨ (¬ (e3271 _v)) ∨ (¬ (e5100 _v)) ∨ (¬ (e4903 _v)) ∨ (¬ (e3976 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e8045 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4724 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e4398 _v)) ∨ (¬ (e3855 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e4491 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e7749 _v)) ∨ (e2529 _v)) at hc
  have h225 : (e225 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h488 : (e488 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))
  have h2061 : (e2061 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h3069 : (e3069 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))
  have h3105 : (e3105 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))
  have h3271 : (e3271 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h3855 : (e3855 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))
  have h3946 : (e3946 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h3976 : (e3976 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h4059 : (e4059 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))
  have h4096 : (e4096 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4156 : (e4156 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))
  have h4260 : (e4260 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h4369 : (e4369 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))
  have h4398 : (e4398 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))
  have h4491 : (e4491 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))
  have h4724 : (e4724 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))
  have h4747 : (e4747 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))
  have h4872 : (e4872 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))
  have h4903 : (e4903 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h5100 : (e5100 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h6571 : (e6571 _v) := (fun hn => hc (Or.inl hn))
  have h6700 : (e6700 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h7493 : (e7493 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h7749 : (e7749 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))
  have h8045 : (e8045 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h8310 : (e8310 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))))))))))))))))))))))))))))
  have p17875 := n17875 _v _q h225 h488 h2061 h3069 h3105 h3152 h3271 h3855 h3937 h3946 h3976 h4059 h4096 h4156 h4260 h4369 h4398 h4491 h4653 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h6571 h6700 h7493 h7749 h8045 h8310
  exact p17875
end
end Assembly
