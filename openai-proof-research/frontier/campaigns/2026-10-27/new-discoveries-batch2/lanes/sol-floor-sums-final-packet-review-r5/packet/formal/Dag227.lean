import Dag226
import generated.th_lemma_29
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n20230 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4306 : (e4306 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4434 : (e4434 _v)) (h4491 : (e4491 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5100 : (e5100 _v)) (h5208 : (e5208 _v)) (h6571 : (e6571 _v)) (h7807 : (e7807 _v)) (h8038 : (e8038 _v)) (h8045 : (e8045 _v)) : (e7597 _v) := by
  have p14525 := n14525 _v _q 
  have p20227 := n20227 _v _q h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h3976 h4059 h4156 h4199 h4306 h4369 h4398 h4434 h4491 h4567 h4608 h4653 h4675 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h5208 h6571 h7807 h8038 h8045
  change (e2733 _v) ∨ (¬ (e7589 _v)) at p14525
  change (¬ (e2733 _v)) at p20227
  rcases p14525 with hlit | hlit
  · exact (False.elim (p20227 hlit))
  · exact hlit
theorem n20231 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4306 : (e4306 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4434 : (e4434 _v)) (h4491 : (e4491 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5100 : (e5100 _v)) (h5208 : (e5208 _v)) (h6571 : (e6571 _v)) (h7807 : (e7807 _v)) (h8038 : (e8038 _v)) (h8045 : (e8045 _v)) : (e4096 _v) := by
  have p15703 := n15703 _v _q 
  have p20230 := n20230 _v _q h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h3976 h4059 h4156 h4199 h4306 h4369 h4398 h4434 h4491 h4567 h4608 h4653 h4675 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h5208 h6571 h7807 h8038 h8045
  change (e7589 _v) ∨ (e4096 _v) at p15703
  change (¬ (e7589 _v)) at p20230
  rcases p15703 with hlit | hlit
  · exact (False.elim (p20230 hlit))
  · exact hlit
theorem n20232 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4306 : (e4306 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4434 : (e4434 _v)) (h4491 : (e4491 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5100 : (e5100 _v)) (h5208 : (e5208 _v)) (h6571 : (e6571 _v)) (h7807 : (e7807 _v)) (h8038 : (e8038 _v)) (h8045 : (e8045 _v)) : (e6776 _v) := by
  have p8424 := n8424 _v _q 
  have p20227 := n20227 _v _q h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h3976 h4059 h4156 h4199 h4306 h4369 h4398 h4434 h4491 h4567 h4608 h4653 h4675 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h5208 h6571 h7807 h8038 h8045
  change (e2733 _v) ∨ (¬ (e2781 _v)) at p8424
  change (¬ (e2733 _v)) at p20227
  rcases p8424 with hlit | hlit
  · exact (False.elim (p20227 hlit))
  · exact hlit
theorem n20233 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4306 : (e4306 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4434 : (e4434 _v)) (h4491 : (e4491 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5100 : (e5100 _v)) (h5208 : (e5208 _v)) (h6571 : (e6571 _v)) (h7807 : (e7807 _v)) (h8038 : (e8038 _v)) (h8045 : (e8045 _v)) : (e7789 _v) := by
  have p14570 := n14570 _v _q 
  have p20232 := n20232 _v _q h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h3976 h4059 h4156 h4199 h4306 h4369 h4398 h4434 h4491 h4567 h4608 h4653 h4675 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h5208 h6571 h7807 h8038 h8045
  change (e2781 _v) ∨ (¬ (e7781 _v)) at p14570
  change (¬ (e2781 _v)) at p20232
  rcases p14570 with hlit | hlit
  · exact (False.elim (p20232 hlit))
  · exact hlit
theorem n20234 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4306 : (e4306 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4434 : (e4434 _v)) (h4491 : (e4491 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5100 : (e5100 _v)) (h5208 : (e5208 _v)) (h6571 : (e6571 _v)) (h7807 : (e7807 _v)) (h8038 : (e8038 _v)) (h8045 : (e8045 _v)) : (e4260 _v) := by
  have p15824 := n15824 _v _q 
  have p20233 := n20233 _v _q h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h3976 h4059 h4156 h4199 h4306 h4369 h4398 h4434 h4491 h4567 h4608 h4653 h4675 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h5208 h6571 h7807 h8038 h8045
  change (e7781 _v) ∨ (e4260 _v) at p15824
  change (¬ (e7781 _v)) at p20233
  rcases p15824 with hlit | hlit
  · exact (False.elim (p20233 hlit))
  · exact hlit
theorem n20235 (_v : Vars) (_q : Query _v) (h2061 : (e2061 _v)) (h6784 : (e6784 _v)) : (e3920 _v) := by
  have p20229 := n20229 _v _q 
  have p11409 := n11409 _v _q h2061
  have p11473 := n11473 _v _q h6784
  change (¬ (e3919 _v)) ∨ (¬ (e2061 _v)) ∨ (e2793 _v) at p20229
  change (¬ (e2793 _v)) at p11473
  rcases p20229 with hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p11409))
  · exact (False.elim (p11473 hlit))
theorem n20236 (_v : Vars) (_q : Query _v) (h2061 : (e2061 _v)) (h6784 : (e6784 _v)) : (e3923 _v) := by
  have p14797 := n14797 _v _q 
  have p20235 := n20235 _v _q h2061 h6784
  change (e3923 _v) ∨ (e3919 _v) at p14797
  change (¬ (e3919 _v)) at p20235
  rcases p14797 with hlit | hlit
  · exact hlit
  · exact (False.elim (p20235 hlit))
theorem n20237 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4306 : (e4306 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4434 : (e4434 _v)) (h4491 : (e4491 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5100 : (e5100 _v)) (h5208 : (e5208 _v)) (h6571 : (e6571 _v)) (h7807 : (e7807 _v)) (h8038 : (e8038 _v)) (h8045 : (e8045 _v)) : (e75 _v) := by
  have p20040 := n20040 _v _q 
  have p20234 := n20234 _v _q h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h3976 h4059 h4156 h4199 h4306 h4369 h4398 h4434 h4491 h4567 h4608 h4653 h4675 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h5208 h6571 h7807 h8038 h8045
  have p17056 := n17056 _v _q h3946
  have p17061 := n17061 _v _q h4747
  have p4985 := n4985 _v _q h4156
  have p4988 := n4988 _v _q h488
  have p4986 := n4986 _v _q h3105
  have p4984 := n4984 _v _q h4872
  have p17137 := n17137 _v _q h4059
  have p5008 := n5008 _v _q h4787
  have p4994 := n4994 _v _q h3069
  have p5006 := n5006 _v _q h4675
  have p4991 := n4991 _v _q h4608
  have p4999 := n4999 _v _q h91
  have p20231 := n20231 _v _q h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h3976 h4059 h4156 h4199 h4306 h4369 h4398 h4434 h4491 h4567 h4608 h4653 h4675 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h5208 h6571 h7807 h8038 h8045
  have p5003 := n5003 _v _q h4199
  have p5007 := n5007 _v _q h225
  have p4992 := n4992 _v _q h442
  have p4996 := n4996 _v _q h3937
  have p4987 := n4987 _v _q h4434
  have p4983 := n4983 _v _q h4813
  have p4995 := n4995 _v _q h4369
  have p4998 := n4998 _v _q h3152
  change (¬ (e4059 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e3152 _v)) at p20040
  rcases p20040 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact (False.elim (hlit p17137))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p17056))
  · exact (False.elim (hlit p17061))
  · exact (False.elim (hlit p4985))
  · exact (False.elim (hlit p4988))
  · exact (False.elim (hlit p4986))
  · exact (False.elim (hlit p4984))
  · exact (False.elim (hlit p4991))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p4994))
  · exact (False.elim (hlit p20234))
  · exact (False.elim (hlit p20231))
  · exact (False.elim (hlit p4999))
  · exact hlit
  · exact (False.elim (hlit p5003))
  · exact (False.elim (hlit p5007))
  · exact (False.elim (hlit p4992))
  · exact (False.elim (hlit p4996))
  · exact (False.elim (hlit p4987))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p4995))
  · exact (False.elim (hlit p4998))
theorem n20238 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4306 : (e4306 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4434 : (e4434 _v)) (h4491 : (e4491 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5100 : (e5100 _v)) (h5208 : (e5208 _v)) (h6571 : (e6571 _v)) (h7807 : (e7807 _v)) (h8038 : (e8038 _v)) (h8045 : (e8045 _v)) : (e5118 _v) := by
  have p15648 := n15648 _v _q 
  have p20237 := n20237 _v _q h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h3976 h4059 h4156 h4199 h4306 h4369 h4398 h4434 h4491 h4567 h4608 h4653 h4675 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h5208 h6571 h7807 h8038 h8045
  change (e5118 _v) ∨ (e70 _v) at p15648
  change (¬ (e70 _v)) at p20237
  rcases p15648 with hlit | hlit
  · exact hlit
  · exact (False.elim (p20237 hlit))
theorem n20239 (_v : Vars) (_q : Query _v) (h2061 : (e2061 _v)) (h6784 : (e6784 _v)) : (e6600 _v) := by
  have p14484 := n14484 _v _q 
  have p20236 := n20236 _v _q h2061 h6784
  change (¬ (e2402 _v)) ∨ (¬ (e3923 _v)) at p14484
  rcases p14484 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p20236))
theorem n20240 (_v : Vars) (_q : Query _v) (h2061 : (e2061 _v)) (h6784 : (e6784 _v)) : (e7416 _v) := by
  have p14534 := n14534 _v _q 
  have p20239 := n20239 _v _q h2061 h6784
  change (e2402 _v) ∨ (¬ (e7415 _v)) at p14534
  change (¬ (e2402 _v)) at p20239
  rcases p14534 with hlit | hlit
  · exact (False.elim (p20239 hlit))
  · exact hlit
theorem n20241 (_v : Vars) (_q : Query _v) (h2061 : (e2061 _v)) (h6784 : (e6784 _v)) : (e3937 _v) := by
  have p15012 := n15012 _v _q 
  have p20240 := n20240 _v _q h2061 h6784
  change (e7415 _v) ∨ (e3937 _v) at p15012
  change (¬ (e7415 _v)) at p20240
  rcases p15012 with hlit | hlit
  · exact (False.elim (p20240 hlit))
  · exact hlit
theorem n20242 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4306 : (e4306 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4434 : (e4434 _v)) (h4491 : (e4491 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5100 : (e5100 _v)) (h5208 : (e5208 _v)) (h6571 : (e6571 _v)) (h7807 : (e7807 _v)) (h8038 : (e8038 _v)) (h8045 : (e8045 _v)) : (e48 _v) := by
  have p14487 := n14487 _v _q 
  have p20238 := n20238 _v _q h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h3976 h4059 h4156 h4199 h4306 h4369 h4398 h4434 h4491 h4567 h4608 h4653 h4675 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h5208 h6571 h7807 h8038 h8045
  change (e48 _v) ∨ (¬ (e5118 _v)) at p14487
  rcases p14487 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p20238))
theorem n20243 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4306 : (e4306 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4434 : (e4434 _v)) (h4491 : (e4491 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5100 : (e5100 _v)) (h5208 : (e5208 _v)) (h6571 : (e6571 _v)) (h7807 : (e7807 _v)) (h8038 : (e8038 _v)) (h8045 : (e8045 _v)) : (e60 _v) := by
  have p14152 := n14152 _v _q 
  have p20242 := n20242 _v _q h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h3976 h4059 h4156 h4199 h4306 h4369 h4398 h4434 h4491 h4567 h4608 h4653 h4675 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h5208 h6571 h7807 h8038 h8045
  change (¬ (e48 _v)) ∨ (¬ (e59 _v)) at p14152
  rcases p14152 with hlit | hlit
  · exact (False.elim (hlit p20242))
  · exact hlit
theorem n20244 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4306 : (e4306 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4434 : (e4434 _v)) (h4491 : (e4491 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5100 : (e5100 _v)) (h5208 : (e5208 _v)) (h6571 : (e6571 _v)) (h7807 : (e7807 _v)) (h8038 : (e8038 _v)) (h8045 : (e8045 _v)) : (e51 _v) := by
  have p14962 := n14962 _v _q 
  have p20243 := n20243 _v _q h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h3976 h4059 h4156 h4199 h4306 h4369 h4398 h4434 h4491 h4567 h4608 h4653 h4675 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h5208 h6571 h7807 h8038 h8045
  change (e59 _v) ∨ (e51 _v) at p14962
  change (¬ (e59 _v)) at p20243
  rcases p14962 with hlit | hlit
  · exact (False.elim (p20243 hlit))
  · exact hlit
theorem n20245 (_v : Vars) (_q : Query _v) (h2061 : (e2061 _v)) (h6784 : (e6784 _v)) (h8398 : (e8398 _v)) : (e7489 _v) := by
  have p17147 := n17147 _v _q 
  have p20241 := n20241 _v _q h2061 h6784
  have p20239 := n20239 _v _q h2061 h6784
  have p16578 := n16578 _v _q 
  have p19762 := n19762 _v _q h6784
  have p17050 := n17050 _v _q 
  have p11473 := n11473 _v _q h6784
  have p16858 := n16858 _v _q 
  have p20193 := n20193 _v _q h2061 h6784
  have p17208 := n17208 _v _q h8398
  have p17089 := n17089 _v _q 
  have p19665 := n19665 _v _q 
  have p20111 := n20111 _v _q h6784
  have p11409 := n11409 _v _q h2061
  have p16513 := n16513 _v _q h6784
  have p20120 := n20120 _v _q h6784
  have p17108 := n17108 _v _q 
  have p15560 := n15560 _v _q h6784
  have p16598 := n16598 _v _q h6784
  have p16549 := n16549 _v _q h6784
  have p20206 := n20206 _v _q h2061 h6784
  have p20126 := n20126 _v _q 
  have p13951 := n13951 _v _q 
  have p17009 := n17009 _v _q 
  have p19771 := n19771 _v _q h6784
  have p16607 := n16607 _v _q h6784
  have p16619 := n16619 _v _q h6784
  have p16911 := n16911 _v _q 
  have p16620 := n16620 _v _q h6784
  have p16856 := n16856 _v _q h6784
  have p15705 := n15705 _v _q h6784
  have p19747 := n19747 _v _q h6784
  have p19750 := n19750 _v _q h6784
  have p15702 := n15702 _v _q h6784
  have p20208 := n20208 _v _q h2061 h6784
  have p19752 := n19752 _v _q h6784
  have p20169 := n20169 _v _q h6784
  have p17058 := n17058 _v _q 
  have p17064 := n17064 _v _q 
  have p17067 := n17067 _v _q 
  have p17069 := n17069 _v _q 
  have p17072 := n17072 _v _q 
  have p16854 := n16854 _v _q h6784
  have p19772 := n19772 _v _q h6784
  have p17078 := n17078 _v _q 
  have p17080 := n17080 _v _q 
  have p17083 := n17083 _v _q 
  have p17074 := n17074 _v _q 
  have p17087 := n17087 _v _q 
  have p17758 := n17758 _v _q 
  have p17091 := n17091 _v _q 
  have p17093 := n17093 _v _q 
  have p15713 := n15713 _v _q h6784
  have p17221 := n17221 _v _q 
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p17100 := n17100 _v _q 
  have p17102 := n17102 _v _q 
  have p19610 := n19610 _v _q 
  have p17104 := n17104 _v _q 
  have p17096 := n17096 _v _q 
  have p16625 := n16625 _v _q h6784
  have p16626 := n16626 _v _q h6784
  have p17113 := n17113 _v _q 
  have p19758 := n19758 _v _q h6784
  have p17122 := n17122 _v _q 
  have p17117 := n17117 _v _q 
  have p17124 := n17124 _v _q 
  have p17115 := n17115 _v _q 
  have p17120 := n17120 _v _q 
  have p19760 := n19760 _v _q h6784
  have p17127 := n17127 _v _q 
  have p16778 := n16778 _v _q 
  have p17874 := n17874 _v _q 
  have p17131 := n17131 _v _q 
  have p17110 := n17110 _v _q 
  have p17133 := n17133 _v _q 
  have p16603 := n16603 _v _q h6784
  have p16816 := n16816 _v _q h6784
  have p17111 := n17111 _v _q 
  have p17294 := n17294 _v _q 
  have p17136 := n17136 _v _q 
  have p17141 := n17141 _v _q 
  have p16913 := n16913 _v _q 
  have p20209 := n20209 _v _q h2061 h6784
  have p20096 := n20096 _v _q 
  have p17053 := n17053 _v _q 
  have p15217 := n15217 _v _q h2061
  have p17055 := n17055 _v _q 
  have p20202 := n20202 _v _q h2061 h6784
  have p10893 := n10893 _v _q 
  exact FloorCertificate.node_20245 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e61 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2863 _v) (e2877 _v) (e2879 _v) (e2883 _v) (e2898 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2913 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p17147 p20241 p20239 p16578 p19762 p17050 p11473 p16858 p20193 p17208 p17089 p19665 p20111 p11409 p16513 p20120 p17108 p15560 p16598 p16549 p20206 p20126 p13951 p17009 p19771 p16607 p16619 p16911 p16620 p16856 p15705 p19747 p19750 p15702 p20208 p19752 p20169 p17058 p17064 p17067 p17069 p17072 p16854 p19772 p17078 p17080 p17083 p17074 p17087 p17758 p17091 p17093 p15713 p17221 p17098 p17106 p17100 p17102 p19610 p17104 p17096 p16625 p16626 p17113 p19758 p17122 p17117 p17124 p17115 p17120 p19760 p17127 p16778 p17874 p17131 p17110 p17133 p16603 p16816 p17111 p17294 p17136 p17141 p16913 p20209 p20096 p17053 p15217 p17055 p20202 p10893
theorem n20246 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4306 : (e4306 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4434 : (e4434 _v)) (h4491 : (e4491 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5100 : (e5100 _v)) (h5208 : (e5208 _v)) (h6571 : (e6571 _v)) (h7807 : (e7807 _v)) (h8038 : (e8038 _v)) (h8045 : (e8045 _v)) : (e4839 _v) := by
  have p17370 := n17370 _v _q 
  have p20244 := n20244 _v _q h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h3976 h4059 h4156 h4199 h4306 h4369 h4398 h4434 h4491 h4567 h4608 h4653 h4675 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h5208 h6571 h7807 h8038 h8045
  have p8447 := n8447 _v _q h6571
  have p20231 := n20231 _v _q h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h3976 h4059 h4156 h4199 h4306 h4369 h4398 h4434 h4491 h4567 h4608 h4653 h4675 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h5208 h6571 h7807 h8038 h8045
  have p4994 := n4994 _v _q h3069
  have p4987 := n4987 _v _q h4434
  have p17786 := n17786 _v _q h7807
  have p4991 := n4991 _v _q h4608
  have p4999 := n4999 _v _q h91
  have p4996 := n4996 _v _q h3937
  have p20234 := n20234 _v _q h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h3976 h4059 h4156 h4199 h4306 h4369 h4398 h4434 h4491 h4567 h4608 h4653 h4675 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h5208 h6571 h7807 h8038 h8045
  have p5003 := n5003 _v _q h4199
  have p4998 := n4998 _v _q h3152
  have p17128 := n17128 _v _q h4491
  have p4983 := n4983 _v _q h4813
  have p5008 := n5008 _v _q h4787
  have p17129 := n17129 _v _q h4903
  have p17175 := n17175 _v _q h5208
  have p5006 := n5006 _v _q h4675
  have p17159 := n17159 _v _q h5100
  have p15373 := n15373 _v _q h7807
  have p17134 := n17134 _v _q h4398
  have p17157 := n17157 _v _q h8045
  have p17137 := n17137 _v _q h4059
  have p17138 := n17138 _v _q h4306
  have p5007 := n5007 _v _q h225
  have p4992 := n4992 _v _q h442
  have p17143 := n17143 _v _q h4567
  have p17056 := n17056 _v _q h3946
  have p17060 := n17060 _v _q h4653
  have p17061 := n17061 _v _q h4747
  have p4995 := n4995 _v _q h4369
  have p17076 := n17076 _v _q h3976
  have p4985 := n4985 _v _q h4156
  have p4988 := n4988 _v _q h488
  have p4986 := n4986 _v _q h3105
  have p4984 := n4984 _v _q h4872
  have p17094 := n17094 _v _q h4724
  change (¬ (e4838 _v)) ∨ (e2358 _v) ∨ (¬ (e4096 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e7749 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4491 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4903 _v)) ∨ (¬ (e5208 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e5100 _v)) ∨ (¬ (e7814 _v)) ∨ (¬ (e4398 _v)) ∨ (¬ (e8045 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e4567 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e3976 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4724 _v)) at p17370
  change (¬ (e2358 _v)) at p8447
  rcases p17370 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (p8447 hlit))
  · exact (False.elim (hlit p20231))
  · exact (False.elim (hlit p20244))
  · exact (False.elim (hlit p4994))
  · exact (False.elim (hlit p4987))
  · exact (False.elim (hlit p17786))
  · exact (False.elim (hlit p4991))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p4996))
  · exact (False.elim (hlit p20234))
  · exact (False.elim (hlit p5003))
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p17128))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p17129))
  · exact (False.elim (hlit p17175))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p17159))
  · exact (False.elim (hlit p15373))
  · exact (False.elim (hlit p17134))
  · exact (False.elim (hlit p17157))
  · exact (False.elim (hlit p17137))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p5007))
  · exact (False.elim (hlit p4992))
  · exact (False.elim (hlit p17143))
  · exact (False.elim (hlit p17056))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p17061))
  · exact (False.elim (hlit p4995))
  · exact (False.elim (hlit p17076))
  · exact (False.elim (hlit p4985))
  · exact (False.elim (hlit p4988))
  · exact (False.elim (hlit p4986))
  · exact (False.elim (hlit p4984))
  · exact (False.elim (hlit p17094))
theorem n20247 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4306 : (e4306 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4434 : (e4434 _v)) (h4491 : (e4491 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5100 : (e5100 _v)) (h5208 : (e5208 _v)) (h6571 : (e6571 _v)) (h7807 : (e7807 _v)) (h8038 : (e8038 _v)) (h8045 : (e8045 _v)) : (e8301 _v) := by
  have p16285 := n16285 _v _q 
  have p20246 := n20246 _v _q h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h3976 h4059 h4156 h4199 h4306 h4369 h4398 h4434 h4491 h4567 h4608 h4653 h4675 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h5208 h6571 h7807 h8038 h8045
  change (e8301 _v) ∨ (e4838 _v) at p16285
  change (¬ (e4838 _v)) at p20246
  rcases p16285 with hlit | hlit
  · exact hlit
  · exact (False.elim (p20246 hlit))
theorem n20249 (_v : Vars) (_q : Query _v)  : (e20248 _v) := by
  by_contra hc
  change ¬ ((¬ (e8398 _v)) ∨ (e2793 _v) ∨ (¬ (e2061 _v))) at hc
  have h2061 : (e2061 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr hn)))
  have h6784 : (e6784 _v) := (fun hn => hc (Or.inr (Or.inl hn)))
  have h8398 : (e8398 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have p20245 := n20245 _v _q h2061 h6784 h8398
  exact p20245
theorem n20250 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4306 : (e4306 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4434 : (e4434 _v)) (h4491 : (e4491 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5100 : (e5100 _v)) (h5208 : (e5208 _v)) (h6571 : (e6571 _v)) (h7807 : (e7807 _v)) (h8038 : (e8038 _v)) (h8045 : (e8045 _v)) : (e8310 _v) := by
  have p14906 := n14906 _v _q 
  have p20247 := n20247 _v _q h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h3976 h4059 h4156 h4199 h4306 h4369 h4398 h4434 h4491 h4567 h4608 h4653 h4675 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h5208 h6571 h7807 h8038 h8045
  change (¬ (e2529 _v)) ∨ (¬ (e8301 _v)) at p14906
  rcases p14906 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p20247))
theorem n20251 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4306 : (e4306 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4434 : (e4434 _v)) (h4491 : (e4491 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5100 : (e5100 _v)) (h5208 : (e5208 _v)) (h6571 : (e6571 _v)) (h7807 : (e7807 _v)) (h8038 : (e8038 _v)) (h8045 : (e8045 _v)) : (e8322 _v) := by
  have p15218 := n15218 _v _q 
  have p20250 := n20250 _v _q h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h3976 h4059 h4156 h4199 h4306 h4369 h4398 h4434 h4491 h4567 h4608 h4653 h4675 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h5208 h6571 h7807 h8038 h8045
  change (e2529 _v) ∨ (¬ (e8321 _v)) at p15218
  change (¬ (e2529 _v)) at p20250
  rcases p15218 with hlit | hlit
  · exact (False.elim (p20250 hlit))
  · exact hlit
theorem n20252 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4306 : (e4306 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4434 : (e4434 _v)) (h4491 : (e4491 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5100 : (e5100 _v)) (h5208 : (e5208 _v)) (h6571 : (e6571 _v)) (h7807 : (e7807 _v)) (h8038 : (e8038 _v)) (h8045 : (e8045 _v)) : (e8317 _v) := by
  have p11541 := n11541 _v _q 
  have p20251 := n20251 _v _q h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h3976 h4059 h4156 h4199 h4306 h4369 h4398 h4434 h4491 h4567 h4608 h4653 h4675 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h5208 h6571 h7807 h8038 h8045
  change (e8321 _v) ∨ (e8317 _v) at p11541
  change (¬ (e8321 _v)) at p20251
  rcases p11541 with hlit | hlit
  · exact (False.elim (p20251 hlit))
  · exact hlit
theorem n20253 (_v : Vars) (_q : Query _v) (h2061 : (e2061 _v)) (h6784 : (e6784 _v)) : (e8406 _v) := by
  have p20249 := n20249 _v _q 
  have p11409 := n11409 _v _q h2061
  have p11473 := n11473 _v _q h6784
  change (¬ (e8398 _v)) ∨ (e2793 _v) ∨ (¬ (e2061 _v)) at p20249
  change (¬ (e2793 _v)) at p11473
  rcases p20249 with hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (p11473 hlit))
  · exact (False.elim (hlit p11409))
theorem n20254 (_v : Vars) (_q : Query _v) (h2061 : (e2061 _v)) (h6784 : (e6784 _v)) : (e8407 _v) := by
  have p11470 := n11470 _v _q 
  have p20253 := n20253 _v _q h2061 h6784
  change (e8407 _v) ∨ (e8398 _v) at p11470
  change (¬ (e8398 _v)) at p20253
  rcases p11470 with hlit | hlit
  · exact hlit
  · exact (False.elim (p20253 hlit))
theorem n20255 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4306 : (e4306 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4434 : (e4434 _v)) (h4491 : (e4491 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5100 : (e5100 _v)) (h5208 : (e5208 _v)) (h6571 : (e6571 _v)) (h7807 : (e7807 _v)) (h8045 : (e8045 _v)) : (e4439 _v) := by
  have p14925 := n14925 _v _q 
  have p20129 := n20129 _v _q h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h3976 h4059 h4156 h4199 h4306 h4369 h4398 h4434 h4491 h4567 h4608 h4653 h4675 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h5208 h6571 h7807 h8045
  change (e4446 _v) ∨ (e4439 _v) at p14925
  change (¬ (e4446 _v)) at p20129
  rcases p14925 with hlit | hlit
  · exact (False.elim (p20129 hlit))
  · exact hlit
theorem n20256 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4306 : (e4306 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4434 : (e4434 _v)) (h4491 : (e4491 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5100 : (e5100 _v)) (h5208 : (e5208 _v)) (h6571 : (e6571 _v)) (h7807 : (e7807 _v)) (h8038 : (e8038 _v)) (h8045 : (e8045 _v)) : (e7489 _v) := by
  have p16977 := n16977 _v _q 
  have p20255 := n20255 _v _q h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h3976 h4059 h4156 h4199 h4306 h4369 h4398 h4434 h4491 h4567 h4608 h4653 h4675 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h5208 h6571 h7807 h8045
  have p20231 := n20231 _v _q h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h3976 h4059 h4156 h4199 h4306 h4369 h4398 h4434 h4491 h4567 h4608 h4653 h4675 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h5208 h6571 h7807 h8038 h8045
  have p17096 := n17096 _v _q 
  have p20250 := n20250 _v _q h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h3976 h4059 h4156 h4199 h4306 h4369 h4398 h4434 h4491 h4567 h4608 h4653 h4675 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h5208 h6571 h7807 h8038 h8045
  have p17098 := n17098 _v _q 
  have p20227 := n20227 _v _q h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h3976 h4059 h4156 h4199 h4306 h4369 h4398 h4434 h4491 h4567 h4608 h4653 h4675 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h5208 h6571 h7807 h8038 h8045
  have p20252 := n20252 _v _q h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h3976 h4059 h4156 h4199 h4306 h4369 h4398 h4434 h4491 h4567 h4608 h4653 h4675 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h5208 h6571 h7807 h8038 h8045
  have p8447 := n8447 _v _q h6571
  have p20186 := n20186 _v _q h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h3976 h4059 h4156 h4199 h4306 h4369 h4398 h4434 h4491 h4567 h4608 h4653 h4675 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h5208 h6571 h7807 h8045
  have p17100 := n17100 _v _q 
  have p20244 := n20244 _v _q h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h3976 h4059 h4156 h4199 h4306 h4369 h4398 h4434 h4491 h4567 h4608 h4653 h4675 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h5208 h6571 h7807 h8038 h8045
  have p17102 := n17102 _v _q 
  have p17104 := n17104 _v _q 
  have p17106 := n17106 _v _q 
  have p17108 := n17108 _v _q 
  have p17110 := n17110 _v _q 
  have p13951 := n13951 _v _q 
  have p17113 := n17113 _v _q 
  have p4994 := n4994 _v _q h3069
  have p17117 := n17117 _v _q 
  have p17255 := n17255 _v _q h6571
  have p17120 := n17120 _v _q 
  have p17786 := n17786 _v _q h7807
  have p17009 := n17009 _v _q 
  have p17122 := n17122 _v _q 
  have p4991 := n4991 _v _q h4608
  have p16576 := n16576 _v _q 
  have p17124 := n17124 _v _q 
  have p4999 := n4999 _v _q h91
  have p4996 := n4996 _v _q h3937
  have p20234 := n20234 _v _q h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h3976 h4059 h4156 h4199 h4306 h4369 h4398 h4434 h4491 h4567 h4608 h4653 h4675 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h5208 h6571 h7807 h8038 h8045
  have p17147 := n17147 _v _q 
  have p5003 := n5003 _v _q h4199
  have p4998 := n4998 _v _q h3152
  have p17127 := n17127 _v _q 
  have p17128 := n17128 _v _q h4491
  have p4983 := n4983 _v _q h4813
  have p5008 := n5008 _v _q h4787
  have p17256 := n17256 _v _q 
  have p17129 := n17129 _v _q h4903
  have p17175 := n17175 _v _q h5208
  have p5006 := n5006 _v _q h4675
  have p17159 := n17159 _v _q h5100
  have p17131 := n17131 _v _q 
  have p15373 := n15373 _v _q h7807
  have p17133 := n17133 _v _q 
  have p17134 := n17134 _v _q h4398
  have p17136 := n17136 _v _q 
  have p17157 := n17157 _v _q h8045
  have p17137 := n17137 _v _q h4059
  have p17138 := n17138 _v _q h4306
  have p5007 := n5007 _v _q h225
  have p16778 := n16778 _v _q 
  have p17141 := n17141 _v _q 
  have p4992 := n4992 _v _q h442
  have p17143 := n17143 _v _q h4567
  have p17050 := n17050 _v _q 
  have p17053 := n17053 _v _q 
  have p17055 := n17055 _v _q 
  have p17056 := n17056 _v _q h3946
  have p17058 := n17058 _v _q 
  have p17060 := n17060 _v _q h4653
  have p17061 := n17061 _v _q h4747
  have p17064 := n17064 _v _q 
  have p4995 := n4995 _v _q h4369
  have p17067 := n17067 _v _q 
  have p17069 := n17069 _v _q 
  have p17072 := n17072 _v _q 
  have p17074 := n17074 _v _q 
  have p17076 := n17076 _v _q h3976
  have p4985 := n4985 _v _q h4156
  have p4988 := n4988 _v _q h488
  have p17078 := n17078 _v _q 
  have p4986 := n4986 _v _q h3105
  have p17080 := n17080 _v _q 
  have p17083 := n17083 _v _q 
  have p4984 := n4984 _v _q h4872
  have p17087 := n17087 _v _q 
  have p17091 := n17091 _v _q 
  have p17094 := n17094 _v _q h4724
  have p17093 := n17093 _v _q 
  have p17111 := n17111 _v _q 
  have p17115 := n17115 _v _q 
  have p17089 := n17089 _v _q 
  have p20242 := n20242 _v _q h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h3976 h4059 h4156 h4199 h4306 h4369 h4398 h4434 h4491 h4567 h4608 h4653 h4675 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h5208 h6571 h7807 h8038 h8045
  exact FloorCertificate.node_20256 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2863 _v) (e2877 _v) (e2883 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p16977 p20255 p20231 p17096 p20250 p17098 p20227 p20252 p8447 p20186 p17100 p20244 p17102 p17104 p17106 p17108 p17110 p13951 p17113 p4994 p17117 p17255 p17120 p17786 p17009 p17122 p4991 p16576 p17124 p4999 p4996 p20234 p17147 p5003 p4998 p17127 p17128 p4983 p5008 p17256 p17129 p17175 p5006 p17159 p17131 p15373 p17133 p17134 p17136 p17157 p17137 p17138 p5007 p16778 p17141 p4992 p17143 p17050 p17053 p17055 p17056 p17058 p17060 p17061 p17064 p4995 p17067 p17069 p17072 p17074 p17076 p4985 p4988 p17078 p4986 p17080 p17083 p4984 p17087 p17091 p17094 p17093 p17111 p17115 p17089 p20242
theorem n20257 (_v : Vars) (_q : Query _v) (h2061 : (e2061 _v)) (h6784 : (e6784 _v)) : (e2799 _v) := by
  have p15435 := n15435 _v _q 
  have p20254 := n20254 _v _q h2061 h6784
  change (e2799 _v) ∨ (¬ (e8407 _v)) at p15435
  rcases p15435 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p20254))
theorem n20258 (_v : Vars) (_q : Query _v) (h2061 : (e2061 _v)) (h6784 : (e6784 _v)) : (e8390 _v) := by
  have p14912 := n14912 _v _q 
  have p20257 := n20257 _v _q h2061 h6784
  change (¬ (e2799 _v)) ∨ (¬ (e8384 _v)) at p14912
  rcases p14912 with hlit | hlit
  · exact (False.elim (hlit p20257))
  · exact hlit
theorem n20260 (_v : Vars) (_q : Query _v)  : (e20259 _v) := by
  by_contra hc
  change ¬ ((¬ (e4567 _v)) ∨ (e2358 _v) ∨ (¬ (e3069 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4491 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4903 _v)) ∨ (¬ (e5208 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e5100 _v)) ∨ (¬ (e4398 _v)) ∨ (¬ (e8045 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e3976 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4724 _v)) ∨ (¬ (e4434 _v)) ∨ (e2475 _v) ∨ (e2303 _v)) at hc
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h225 : (e225 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))
  have h442 : (e442 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))
  have h488 : (e488 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))
  have h3069 : (e3069 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h3105 : (e3105 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h3946 : (e3946 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))
  have h3976 : (e3976 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))
  have h4059 : (e4059 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))
  have h4156 : (e4156 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))
  have h4199 : (e4199 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))
  have h4369 : (e4369 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))
  have h4398 : (e4398 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))
  have h4434 : (e4434 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))))
  have h4491 : (e4491 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h4567 : (e4567 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h4608 : (e4608 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))
  have h4675 : (e4675 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h4724 : (e4724 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))
  have h4747 : (e4747 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h4872 : (e4872 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))
  have h4903 : (e4903 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h5100 : (e5100 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h5208 : (e5208 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h6571 : (e6571 _v) := (fun hn => hc (Or.inr (Or.inl hn)))
  have h7807 : (e7807 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))))))))))))))))))))))))))))))
  have h8038 : (e8038 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))))
  have h8045 : (e8045 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))
  have p20256 := n20256 _v _q h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h3976 h4059 h4156 h4199 h4306 h4369 h4398 h4434 h4491 h4567 h4608 h4653 h4675 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h5208 h6571 h7807 h8038 h8045
  exact p20256
theorem n20261 (_v : Vars) (_q : Query _v) (h2061 : (e2061 _v)) (h6784 : (e6784 _v)) : (e4924 _v) := by
  have p16462 := n16462 _v _q 
  have p20258 := n20258 _v _q h2061 h6784
  change (e8384 _v) ∨ (e4924 _v) at p16462
  change (¬ (e8384 _v)) at p20258
  rcases p16462 with hlit | hlit
  · exact (False.elim (p20258 hlit))
  · exact hlit
theorem n20262 (_v : Vars) (_q : Query _v) (h2061 : (e2061 _v)) (h6784 : (e6784 _v)) : (e7489 _v) := by
  have p20261 := n20261 _v _q h2061 h6784
  have p20202 := n20202 _v _q h2061 h6784
  have p20239 := n20239 _v _q h2061 h6784
  have p10893 := n10893 _v _q 
  have p17147 := n17147 _v _q 
  have p20241 := n20241 _v _q h2061 h6784
  have p16578 := n16578 _v _q 
  have p19762 := n19762 _v _q h6784
  have p17050 := n17050 _v _q 
  have p16858 := n16858 _v _q 
  have p20193 := n20193 _v _q h2061 h6784
  have p17089 := n17089 _v _q 
  have p19665 := n19665 _v _q 
  have p20111 := n20111 _v _q h6784
  have p11409 := n11409 _v _q h2061
  have p16513 := n16513 _v _q h6784
  have p20120 := n20120 _v _q h6784
  have p17108 := n17108 _v _q 
  have p15560 := n15560 _v _q h6784
  have p16598 := n16598 _v _q h6784
  have p16549 := n16549 _v _q h6784
  have p20206 := n20206 _v _q h2061 h6784
  have p20126 := n20126 _v _q 
  have p13951 := n13951 _v _q 
  have p17009 := n17009 _v _q 
  have p19771 := n19771 _v _q h6784
  have p16607 := n16607 _v _q h6784
  have p16619 := n16619 _v _q h6784
  have p16911 := n16911 _v _q 
  have p16620 := n16620 _v _q h6784
  have p16856 := n16856 _v _q h6784
  have p15705 := n15705 _v _q h6784
  have p19747 := n19747 _v _q h6784
  have p19750 := n19750 _v _q h6784
  have p15702 := n15702 _v _q h6784
  have p20208 := n20208 _v _q h2061 h6784
  have p19752 := n19752 _v _q h6784
  have p20169 := n20169 _v _q h6784
  have p17058 := n17058 _v _q 
  have p17064 := n17064 _v _q 
  have p17067 := n17067 _v _q 
  have p17069 := n17069 _v _q 
  have p17072 := n17072 _v _q 
  have p16854 := n16854 _v _q h6784
  have p19772 := n19772 _v _q h6784
  have p17078 := n17078 _v _q 
  have p17080 := n17080 _v _q 
  have p17083 := n17083 _v _q 
  have p17074 := n17074 _v _q 
  have p17087 := n17087 _v _q 
  have p17758 := n17758 _v _q 
  have p17091 := n17091 _v _q 
  have p17093 := n17093 _v _q 
  have p15713 := n15713 _v _q h6784
  have p17221 := n17221 _v _q 
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p17100 := n17100 _v _q 
  have p17102 := n17102 _v _q 
  have p19610 := n19610 _v _q 
  have p17104 := n17104 _v _q 
  have p17096 := n17096 _v _q 
  have p16625 := n16625 _v _q h6784
  have p16626 := n16626 _v _q h6784
  have p17113 := n17113 _v _q 
  have p19758 := n19758 _v _q h6784
  have p17122 := n17122 _v _q 
  have p17117 := n17117 _v _q 
  have p17124 := n17124 _v _q 
  have p17115 := n17115 _v _q 
  have p17120 := n17120 _v _q 
  have p19760 := n19760 _v _q h6784
  have p17127 := n17127 _v _q 
  have p16778 := n16778 _v _q 
  have p17874 := n17874 _v _q 
  have p17131 := n17131 _v _q 
  have p17110 := n17110 _v _q 
  have p17133 := n17133 _v _q 
  have p16603 := n16603 _v _q h6784
  have p16816 := n16816 _v _q h6784
  have p17111 := n17111 _v _q 
  have p17294 := n17294 _v _q 
  have p17136 := n17136 _v _q 
  have p17141 := n17141 _v _q 
  have p16913 := n16913 _v _q 
  have p20209 := n20209 _v _q h2061 h6784
  have p20096 := n20096 _v _q 
  have p17053 := n17053 _v _q 
  have p15217 := n15217 _v _q h2061
  have p17055 := n17055 _v _q 
  exact FloorCertificate.node_20262 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e61 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2863 _v) (e2877 _v) (e2879 _v) (e2883 _v) (e2898 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2913 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p20261 p20202 p20239 p10893 p17147 p20241 p16578 p19762 p17050 p16858 p20193 p17089 p19665 p20111 p11409 p16513 p20120 p17108 p15560 p16598 p16549 p20206 p20126 p13951 p17009 p19771 p16607 p16619 p16911 p16620 p16856 p15705 p19747 p19750 p15702 p20208 p19752 p20169 p17058 p17064 p17067 p17069 p17072 p16854 p19772 p17078 p17080 p17083 p17074 p17087 p17758 p17091 p17093 p15713 p17221 p17098 p17106 p17100 p17102 p19610 p17104 p17096 p16625 p16626 p17113 p19758 p17122 p17117 p17124 p17115 p17120 p19760 p17127 p16778 p17874 p17131 p17110 p17133 p16603 p16816 p17111 p17294 p17136 p17141 p16913 p20209 p20096 p17053 p15217 p17055
theorem n20264 (_v : Vars) (_q : Query _v)  : (e20263 _v) := by
  by_contra hc
  change ¬ ((¬ (e2061 _v)) ∨ (e2793 _v)) at hc
  have h2061 : (e2061 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h6784 : (e6784 _v) := (fun hn => hc (Or.inr hn))
  have p20262 := n20262 _v _q h2061 h6784
  exact p20262
theorem n20265 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e6454 _v) := by
  have p20264 := n20264 _v _q 
  have p11473 := n11473 _v _q h6784
  change (¬ (e2061 _v)) ∨ (e2793 _v) at p20264
  change (¬ (e2793 _v)) at p11473
  rcases p20264 with hlit | hlit
  · exact hlit
  · exact (False.elim (p11473 hlit))
theorem n20266 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e7955 _v) := by
  have p14601 := n14601 _v _q 
  have p20265 := n20265 _v _q h6784
  change (e2061 _v) ∨ (¬ (e7947 _v)) at p14601
  change (¬ (e2061 _v)) at p20265
  rcases p14601 with hlit | hlit
  · exact (False.elim (p20265 hlit))
  · exact hlit
theorem n20267 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e4434 _v) := by
  have p15307 := n15307 _v _q 
  have p20266 := n20266 _v _q h6784
  change (e7947 _v) ∨ (e4434 _v) at p15307
  change (¬ (e7947 _v)) at p20266
  rcases p15307 with hlit | hlit
  · exact (False.elim (p20266 hlit))
  · exact hlit
theorem n20268 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e2179 _v) := by
  have p20056 := n20056 _v _q 
  have p20267 := n20267 _v _q h6784
  have p16619 := n16619 _v _q h6784
  have p16626 := n16626 _v _q h6784
  have p15702 := n15702 _v _q h6784
  have p19760 := n19760 _v _q h6784
  have p19762 := n19762 _v _q h6784
  have p16598 := n16598 _v _q h6784
  have p15705 := n15705 _v _q h6784
  have p16856 := n16856 _v _q h6784
  have p19747 := n19747 _v _q h6784
  have p16854 := n16854 _v _q h6784
  have p19772 := n19772 _v _q h6784
  have p16603 := n16603 _v _q h6784
  have p16625 := n16625 _v _q h6784
  have p16620 := n16620 _v _q h6784
  have p19771 := n19771 _v _q h6784
  change (e2179 _v) ∨ (¬ (e4260 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e3152 _v)) at p20056
  rcases p20056 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p16603))
  · exact (False.elim (hlit p16619))
  · exact (False.elim (hlit p16626))
  · exact (False.elim (hlit p15702))
  · exact (False.elim (hlit p19760))
  · exact (False.elim (hlit p19762))
  · exact (False.elim (hlit p16598))
  · exact (False.elim (hlit p15705))
  · exact (False.elim (hlit p16856))
  · exact (False.elim (hlit p19747))
  · exact (False.elim (hlit p16854))
  · exact (False.elim (hlit p19772))
  · exact (False.elim (hlit p20267))
  · exact (False.elim (hlit p16625))
  · exact (False.elim (hlit p16620))
  · exact (False.elim (hlit p19771))
theorem n20269 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e4616 _v) := by
  have p14684 := n14684 _v _q 
  have p20268 := n20268 _v _q h6784
  change (¬ (e2179 _v)) ∨ (¬ (e3162 _v)) at p14684
  rcases p14684 with hlit | hlit
  · exact (False.elim (hlit p20268))
  · exact hlit
theorem n20270 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e3158 _v) := by
  have p15126 := n15126 _v _q 
  have p20269 := n20269 _v _q h6784
  change (e3162 _v) ∨ (e3158 _v) at p15126
  change (¬ (e3162 _v)) at p20269
  rcases p15126 with hlit | hlit
  · exact (False.elim (p20269 hlit))
  · exact hlit
theorem n20271 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e7489 _v) := by
  have p20265 := n20265 _v _q h6784
  have p5255 := n5255 _v _q 
  have p20270 := n20270 _v _q h6784
  have p16578 := n16578 _v _q 
  have p16858 := n16858 _v _q 
  exact FloorCertificate.node_20271 (e2 _v) (e9 _v) (e17 _v) (e110 _v) (e2863 _v) (e2935 _v) p20265 p5255 p20270 p16578 p16858
theorem n20272 (_v : Vars) (_q : Query _v)  : (e2793 _v) := by
  by_contra hc
  change ¬ (e2793 _v) at hc
  have h6784 : (e6784 _v) := (fun hn => hc hn)
  have p20271 := n20271 _v _q h6784
  exact p20271
theorem n20273 (_v : Vars) (_q : Query _v)  : (e4910 _v) := by
  have p14701 := n14701 _v _q 
  have p20272 := n20272 _v _q 
  change (¬ (e2793 _v)) ∨ (¬ (e4909 _v)) at p14701
  rcases p14701 with hlit | hlit
  · exact (False.elim (hlit p20272))
  · exact hlit
theorem n20274 (_v : Vars) (_q : Query _v)  : (e4903 _v) := by
  have p14973 := n14973 _v _q 
  have p20273 := n20273 _v _q 
  change (e4909 _v) ∨ (e4903 _v) at p14973
  change (¬ (e4909 _v)) at p20273
  rcases p14973 with hlit | hlit
  · exact (False.elim (p20273 hlit))
  · exact hlit
theorem n20275 (_v : Vars) (_q : Query _v) (h6636 : (e6636 _v)) : (e6600 _v) := by
  have p11031 := n11031 _v _q h6636
  have p5257 := n5257 _v _q 
  have p5255 := n5255 _v _q 
  have p20272 := n20272 _v _q 
  have p10893 := n10893 _v _q 
  have p8663 := n8663 _v _q 
  exact FloorCertificate.node_20275 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p11031 p5257 p5255 p20272 p10893 p8663
theorem n20276 (_v : Vars) (_q : Query _v) (h6636 : (e6636 _v)) : (e7416 _v) := by
  have p14534 := n14534 _v _q 
  have p20275 := n20275 _v _q h6636
  change (e2402 _v) ∨ (¬ (e7415 _v)) at p14534
  change (¬ (e2402 _v)) at p20275
  rcases p14534 with hlit | hlit
  · exact (False.elim (p20275 hlit))
  · exact hlit
theorem n20277 (_v : Vars) (_q : Query _v) (h6636 : (e6636 _v)) : (e6650 _v) := by
  have p10893 := n10893 _v _q 
  have p20272 := n20272 _v _q 
  have p11031 := n11031 _v _q h6636
  have p8663 := n8663 _v _q 
  have p5255 := n5255 _v _q 
  have p5257 := n5257 _v _q 
  exact FloorCertificate.node_20277 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p10893 p20272 p11031 p8663 p5255 p5257
end
end Assembly
