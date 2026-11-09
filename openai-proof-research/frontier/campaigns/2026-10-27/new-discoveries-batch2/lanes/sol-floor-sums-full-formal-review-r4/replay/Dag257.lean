import Dag256
import generated.th_lemma_34
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n21706 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h8320 : (e8320 _v)) : (e4260 _v) := by
  have p15824 := n15824 _v _q 
  have p21705 := n21705 _v _q h51 h4306 h4653 h4813 h8320
  change (e7781 _v) ∨ (e4260 _v) at p15824
  change (¬ (e7781 _v)) at p21705
  rcases p15824 with hlit | hlit
  · exact (False.elim (p21705 hlit))
  · exact hlit
theorem n21707 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h8320 : (e8320 _v)) : (e2402 _v) := by
  have p21168 := n21168 _v _q 
  have p21561 := n21561 _v _q h51 h4306 h4653 h4813 h8320
  have p17024 := n17024 _v _q h8320
  have p16724 := n16724 _v _q h8320
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p16868 := n16868 _v _q h8320
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p21192 := n21192 _v _q h51 h4306 h4653 h4813 h8320
  have p21699 := n21699 _v _q h51 h4306 h4653 h4813 h8320
  have p21703 := n21703 _v _q h51 h4306 h4653 h4813 h8320
  have p21704 := n21704 _v _q h51 h4306 h4653 h4813 h8320
  change (e2402 _v) ∨ (¬ (e2242 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4787 _v)) ∨ (e2296 _v) ∨ (e2781 _v) ∨ (¬ (e2733 _v)) at p21168
  change (¬ (e2296 _v)) at p21699
  change (¬ (e2781 _v)) at p21703
  rcases p21168 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p21561))
  · exact (False.elim (hlit p17024))
  · exact (False.elim (hlit p16724))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p16868))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p21192))
  · exact (False.elim (p21699 hlit))
  · exact (False.elim (p21703 hlit))
  · exact (False.elim (hlit p21704))
theorem n21708 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h8320 : (e8320 _v)) : (e4109 _v) := by
  have p14689 := n14689 _v _q 
  have p21704 := n21704 _v _q h51 h4306 h4653 h4813 h8320
  change (¬ (e2733 _v)) ∨ (¬ (e4108 _v)) at p14689
  rcases p14689 with hlit | hlit
  · exact (False.elim (hlit p21704))
  · exact hlit
theorem n21709 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h8320 : (e8320 _v)) : (e4101 _v) := by
  have p14929 := n14929 _v _q 
  have p21708 := n21708 _v _q h51 h4306 h4653 h4813 h8320
  change (e4108 _v) ∨ (e4101 _v) at p14929
  change (¬ (e4108 _v)) at p21708
  rcases p14929 with hlit | hlit
  · exact (False.elim (p21708 hlit))
  · exact hlit
theorem n21710 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h8320 : (e8320 _v)) : (e2475 _v) := by
  have p21450 := n21450 _v _q 
  have p21561 := n21561 _v _q h51 h4306 h4653 h4813 h8320
  have p21701 := n21701 _v _q h51 h4306 h4653 h4813 h8320
  have p17024 := n17024 _v _q h8320
  have p16724 := n16724 _v _q h8320
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p16868 := n16868 _v _q h8320
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p21182 := n21182 _v _q h51 h4306 h4653 h4813 h8320
  have p21703 := n21703 _v _q h51 h4306 h4653 h4813 h8320
  have p21707 := n21707 _v _q h51 h4306 h4653 h4813 h8320
  change (e2475 _v) ∨ (¬ (e2242 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (e2468 _v) ∨ (e2781 _v) ∨ (¬ (e2402 _v)) at p21450
  change (¬ (e2468 _v)) at p21182
  change (¬ (e2781 _v)) at p21703
  rcases p21450 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p21561))
  · exact (False.elim (hlit p21701))
  · exact (False.elim (hlit p17024))
  · exact (False.elim (hlit p16724))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p16868))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (p21182 hlit))
  · exact (False.elim (p21703 hlit))
  · exact (False.elim (hlit p21707))
theorem n21711 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h8320 : (e8320 _v)) : (e8035 _v) := by
  have p14871 := n14871 _v _q 
  have p21710 := n21710 _v _q h51 h4306 h4653 h4813 h8320
  change (¬ (e2475 _v)) ∨ (¬ (e8029 _v)) at p14871
  rcases p14871 with hlit | hlit
  · exact (False.elim (hlit p21710))
  · exact hlit
theorem n21712 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h8320 : (e8320 _v)) : (e4546 _v) := by
  have p16307 := n16307 _v _q 
  have p21711 := n21711 _v _q h51 h4306 h4653 h4813 h8320
  change (e8029 _v) ∨ (e4546 _v) at p16307
  change (¬ (e8029 _v)) at p21711
  rcases p16307 with hlit | hlit
  · exact (False.elim (p21711 hlit))
  · exact hlit
theorem n21713 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h8320 : (e8320 _v)) : (e2358 _v) := by
  have p8597 := n8597 _v _q 
  have p21707 := n21707 _v _q h51 h4306 h4653 h4813 h8320
  have p21710 := n21710 _v _q h51 h4306 h4653 h4813 h8320
  have p21699 := n21699 _v _q h51 h4306 h4653 h4813 h8320
  change (e2358 _v) ∨ (¬ (e2402 _v)) ∨ (¬ (e2475 _v)) ∨ (e2296 _v) at p8597
  change (¬ (e2296 _v)) at p21699
  rcases p8597 with hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p21707))
  · exact (False.elim (hlit p21710))
  · exact (False.elim (p21699 hlit))
theorem n21714 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h8320 : (e8320 _v)) : (e7640 _v) := by
  have p14828 := n14828 _v _q 
  have p21713 := n21713 _v _q h51 h4306 h4653 h4813 h8320
  change (¬ (e2358 _v)) ∨ (¬ (e7634 _v)) at p14828
  rcases p14828 with hlit | hlit
  · exact (False.elim (hlit p21713))
  · exact hlit
theorem n21715 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h8320 : (e8320 _v)) : (e4139 _v) := by
  have p16281 := n16281 _v _q 
  have p21714 := n21714 _v _q h51 h4306 h4653 h4813 h8320
  change (e7634 _v) ∨ (e4139 _v) at p16281
  change (¬ (e7634 _v)) at p21714
  rcases p16281 with hlit | hlit
  · exact (False.elim (p21714 hlit))
  · exact hlit
theorem n21716 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h8320 : (e8320 _v)) : (e2303 _v) := by
  have p21007 := n21007 _v _q 
  have p21712 := n21712 _v _q h51 h4306 h4653 h4813 h8320
  have p21699 := n21699 _v _q h51 h4306 h4653 h4813 h8320
  have p21715 := n21715 _v _q h51 h4306 h4653 h4813 h8320
  have p21709 := n21709 _v _q h51 h4306 h4653 h4813 h8320
  have p21706 := n21706 _v _q h51 h4306 h4653 h4813 h8320
  have p17024 := n17024 _v _q h8320
  have p16724 := n16724 _v _q h8320
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p16868 := n16868 _v _q h8320
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p21192 := n21192 _v _q h51 h4306 h4653 h4813 h8320
  have p21707 := n21707 _v _q h51 h4306 h4653 h4813 h8320
  have p21561 := n21561 _v _q h51 h4306 h4653 h4813 h8320
  change (e2303 _v) ∨ (¬ (e4546 _v)) ∨ (e2296 _v) ∨ (¬ (e4139 _v)) ∨ (¬ (e4101 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e2402 _v)) ∨ (¬ (e2242 _v)) at p21007
  change (¬ (e2296 _v)) at p21699
  rcases p21007 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p21712))
  · exact (False.elim (p21699 hlit))
  · exact (False.elim (hlit p21715))
  · exact (False.elim (hlit p21709))
  · exact (False.elim (hlit p21706))
  · exact (False.elim (hlit p17024))
  · exact (False.elim (hlit p16724))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p16868))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p21192))
  · exact (False.elim (hlit p21707))
  · exact (False.elim (hlit p21561))
theorem n21717 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h8320 : (e8320 _v)) : (e7804 _v) := by
  have p14837 := n14837 _v _q 
  have p21716 := n21716 _v _q h51 h4306 h4653 h4813 h8320
  change (¬ (e2303 _v)) ∨ (¬ (e7798 _v)) at p14837
  rcases p14837 with hlit | hlit
  · exact (False.elim (hlit p21716))
  · exact hlit
theorem n21718 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h8320 : (e8320 _v)) : (e4285 _v) := by
  have p16274 := n16274 _v _q 
  have p21717 := n21717 _v _q h51 h4306 h4653 h4813 h8320
  change (e7798 _v) ∨ (e4285 _v) at p16274
  change (¬ (e7798 _v)) at p21717
  rcases p16274 with hlit | hlit
  · exact (False.elim (p21717 hlit))
  · exact hlit
theorem n21719 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h8320 : (e8320 _v)) : (e2787 _v) := by
  have p8461 := n8461 _v _q 
  have p21716 := n21716 _v _q h51 h4306 h4653 h4813 h8320
  have p21710 := n21710 _v _q h51 h4306 h4653 h4813 h8320
  change (¬ (e2475 _v)) ∨ (¬ (e2303 _v)) ∨ (e2787 _v) at p8461
  rcases p8461 with hlit | hlit | hlit
  · exact (False.elim (hlit p21710))
  · exact (False.elim (hlit p21716))
  · exact hlit
theorem n21720 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h8320 : (e8320 _v)) : (e7927 _v) := by
  have p14855 := n14855 _v _q 
  have p21719 := n21719 _v _q h51 h4306 h4653 h4813 h8320
  change (¬ (e2787 _v)) ∨ (¬ (e7921 _v)) at p14855
  rcases p14855 with hlit | hlit
  · exact (False.elim (hlit p21719))
  · exact hlit
theorem n21721 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h8320 : (e8320 _v)) : (e4419 _v) := by
  have p16347 := n16347 _v _q 
  have p21720 := n21720 _v _q h51 h4306 h4653 h4813 h8320
  change (e7921 _v) ∨ (e4419 _v) at p16347
  change (¬ (e7921 _v)) at p21720
  rcases p16347 with hlit | hlit
  · exact (False.elim (p21720 hlit))
  · exact hlit
theorem n21722 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h8320 : (e8320 _v)) : (e3929 _v) := by
  have p14484 := n14484 _v _q 
  have p21707 := n21707 _v _q h51 h4306 h4653 h4813 h8320
  change (¬ (e2402 _v)) ∨ (¬ (e3923 _v)) at p14484
  rcases p14484 with hlit | hlit
  · exact (False.elim (hlit p21707))
  · exact hlit
theorem n21723 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h8320 : (e8320 _v)) : (e3919 _v) := by
  have p14797 := n14797 _v _q 
  have p21722 := n21722 _v _q h51 h4306 h4653 h4813 h8320
  change (e3923 _v) ∨ (e3919 _v) at p14797
  change (¬ (e3923 _v)) at p21722
  rcases p14797 with hlit | hlit
  · exact (False.elim (p21722 hlit))
  · exact hlit
theorem n21724 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h8320 : (e8320 _v)) : (e7489 _v) := by
  have p21718 := n21718 _v _q h51 h4306 h4653 h4813 h8320
  have p258 := n258 _v _q 
  have p21699 := n21699 _v _q h51 h4306 h4653 h4813 h8320
  have p17758 := n17758 _v _q 
  have p13951 := n13951 _v _q 
  have p21721 := n21721 _v _q h51 h4306 h4653 h4813 h8320
  have p17124 := n17124 _v _q 
  have p17111 := n17111 _v _q 
  have p17115 := n17115 _v _q 
  have p21715 := n21715 _v _q h51 h4306 h4653 h4813 h8320
  have p21712 := n21712 _v _q h51 h4306 h4653 h4813 h8320
  have p17113 := n17113 _v _q 
  have p17117 := n17117 _v _q 
  have p20467 := n20467 _v _q 
  have p21723 := n21723 _v _q h51 h4306 h4653 h4813 h8320
  have p21709 := n21709 _v _q h51 h4306 h4653 h4813 h8320
  have p19665 := n19665 _v _q 
  have p17133 := n17133 _v _q 
  have p17120 := n17120 _v _q 
  have p21706 := n21706 _v _q h51 h4306 h4653 h4813 h8320
  have p17104 := n17104 _v _q 
  have p17874 := n17874 _v _q 
  have p17127 := n17127 _v _q 
  have p17089 := n17089 _v _q 
  have p21701 := n21701 _v _q h51 h4306 h4653 h4813 h8320
  have p17024 := n17024 _v _q h8320
  have p16724 := n16724 _v _q h8320
  have p21702 := n21702 _v _q h51 h4306 h4653 h4813 h8320
  have p17020 := n17020 _v _q 
  have p17138 := n17138 _v _q h4306
  have p20274 := n20274 _v _q 
  have p17060 := n17060 _v _q h4653
  have p20470 := n20470 _v _q 
  have p16868 := n16868 _v _q h8320
  have p17050 := n17050 _v _q 
  have p16778 := n16778 _v _q 
  have p17122 := n17122 _v _q 
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p20829 := n20829 _v _q 
  have p21587 := n21587 _v _q h51 h4306 h4653 h4813 h8320
  have p20426 := n20426 _v _q 
  have p20126 := n20126 _v _q 
  have p17110 := n17110 _v _q 
  have p17053 := n17053 _v _q 
  have p20096 := n20096 _v _q 
  have p17131 := n17131 _v _q 
  have p17108 := n17108 _v _q 
  have p17294 := n17294 _v _q 
  have p16943 := n16943 _v _q 
  have p17058 := n17058 _v _q 
  have p17064 := n17064 _v _q 
  have p17067 := n17067 _v _q 
  have p17080 := n17080 _v _q 
  have p17072 := n17072 _v _q 
  have p17074 := n17074 _v _q 
  have p17069 := n17069 _v _q 
  have p20461 := n20461 _v _q 
  have p20836 := n20836 _v _q 
  have p20653 := n20653 _v _q 
  have p17078 := n17078 _v _q 
  have p17136 := n17136 _v _q 
  have p17087 := n17087 _v _q 
  have p17083 := n17083 _v _q 
  have p17055 := n17055 _v _q 
  have p17093 := n17093 _v _q 
  have p17091 := n17091 _v _q 
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p21590 := n21590 _v _q h51 h4306 h4653 h4813 h8320
  have p21592 := n21592 _v _q h51 h4306 h4653 h4813 h8320
  have p17141 := n17141 _v _q 
  have p17100 := n17100 _v _q 
  have p19610 := n19610 _v _q 
  have p17102 := n17102 _v _q 
  have p21192 := n21192 _v _q h51 h4306 h4653 h4813 h8320
  have p21594 := n21594 _v _q h51 h4306 h4653 h4813 h8320
  have p17096 := n17096 _v _q 
  have p5255 := n5255 _v _q 
  have p10893 := n10893 _v _q 
  have p21561 := n21561 _v _q h51 h4306 h4653 h4813 h8320
  have p21710 := n21710 _v _q h51 h4306 h4653 h4813 h8320
  exact FloorCertificate.node_21724 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2902 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4541 _v) (e4808 _v) p21718 p258 p21699 p17758 p13951 p21721 p17124 p17111 p17115 p21715 p21712 p17113 p17117 p20467 p21723 p21709 p19665 p17133 p17120 p21706 p17104 p17874 p17127 p17089 p21701 p17024 p16724 p21702 p17020 p17138 p20274 p17060 p20470 p16868 p17050 p16778 p17122 p4983 p16729 p20829 p21587 p20426 p20126 p17110 p17053 p20096 p17131 p17108 p17294 p16943 p17058 p17064 p17067 p17080 p17072 p17074 p17069 p20461 p20836 p20653 p17078 p17136 p17087 p17083 p17055 p17093 p17091 p17098 p17106 p21590 p21592 p17141 p17100 p19610 p17102 p21192 p21594 p17096 p5255 p10893 p21561 p21710
theorem n21726 (_v : Vars) (_q : Query _v)  : (e21725 _v) := by
  by_contra hc
  change ¬ ((e8317 _v) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v))) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr hn)))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h8320 : (e8320 _v) := (fun hn => hc (Or.inl hn))
  have p21724 := n21724 _v _q h51 h4306 h4653 h4813 h8320
  exact p21724
theorem n21727 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e8317 _v) := by
  have p21726 := n21726 _v _q 
  have p16729 := n16729 _v _q h51
  have p17060 := n17060 _v _q h4653
  have p4983 := n4983 _v _q h4813
  have p17138 := n17138 _v _q h4306
  change (e8317 _v) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) at p21726
  rcases p21726 with hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p16729))
theorem n21728 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e8317 _v) := by
  have p21726 := n21726 _v _q 
  have p17138 := n17138 _v _q h4306
  have p16729 := n16729 _v _q h51
  have p4983 := n4983 _v _q h4813
  have p17060 := n17060 _v _q h4653
  change (e8317 _v) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) at p21726
  rcases p21726 with hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p16729))
theorem n21729 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6423 : (e6423 _v)) (h6571 : (e6571 _v)) (h8045 : (e8045 _v)) : (e7489 _v) := by
  have p17376 := n17376 _v _q 
  have p16084 := n16084 _v _q h6423
  have p16718 := n16718 _v _q h6423
  have p20426 := n20426 _v _q 
  have p20653 := n20653 _v _q 
  have p17953 := n17953 _v _q 
  have p20829 := n20829 _v _q 
  have p4983 := n4983 _v _q h4813
  have p17294 := n17294 _v _q 
  have p17874 := n17874 _v _q 
  have p21727 := n21727 _v _q h51 h4306 h4653 h4813
  have p21152 := n21152 _v _q h51 h4306 h4653 h4813 h6423
  have p17138 := n17138 _v _q h4306
  have p17157 := n17157 _v _q h8045
  have p8447 := n8447 _v _q h6571
  have p20836 := n20836 _v _q 
  have p17758 := n17758 _v _q 
  have p19665 := n19665 _v _q 
  have p16096 := n16096 _v _q h6423
  have p20461 := n20461 _v _q 
  have p16725 := n16725 _v _q h6423
  have p16628 := n16628 _v _q h6423
  have p20467 := n20467 _v _q 
  have p16396 := n16396 _v _q h6423
  have p8452 := n8452 _v _q h6423
  change (e1995 _v) ∨ (¬ (e4813 _v)) ∨ (e2358 _v) ∨ (¬ (e442 _v)) ∨ (¬ (e5208 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e8317 _v)) ∨ (¬ (e8045 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e4398 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e2781 _v)) at p17376
  change (¬ (e2358 _v)) at p8447
  change (¬ (e1995 _v)) at p8452
  rcases p17376 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact (False.elim (p8452 hlit))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (p8447 hlit))
  · exact (False.elim (hlit p20426))
  · exact (False.elim (hlit p17953))
  · exact (False.elim (hlit p16096))
  · exact (False.elim (hlit p16718))
  · exact (False.elim (hlit p17294))
  · exact (False.elim (hlit p17874))
  · exact (False.elim (hlit p20653))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p21727))
  · exact (False.elim (hlit p17157))
  · exact (False.elim (hlit p20829))
  · exact (False.elim (hlit p20836))
  · exact (False.elim (hlit p17758))
  · exact (False.elim (hlit p19665))
  · exact (False.elim (hlit p16628))
  · exact (False.elim (hlit p20461))
  · exact (False.elim (hlit p16725))
  · exact (False.elim (hlit p16084))
  · exact (False.elim (hlit p20467))
  · exact (False.elim (hlit p16396))
  · exact (False.elim (hlit p21152))
theorem n21731 (_v : Vars) (_q : Query _v)  : (e21730 _v) := by
  by_contra hc
  change ¬ ((e1995 _v) ∨ (¬ (e4813 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e8045 _v)) ∨ (e2358 _v) ∨ (¬ (e4653 _v)) ∨ (¬ (e51 _v))) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn)))))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h6423 : (e6423 _v) := (fun hn => hc (Or.inl hn))
  have h6571 : (e6571 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h8045 : (e8045 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have p21729 := n21729 _v _q h51 h4306 h4653 h4813 h6423 h6571 h8045
  exact p21729
theorem n21732 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5195 : (e5195 _v)) : (e1995 _v) := by
  have p21731 := n21731 _v _q 
  have p15938 := n15938 _v _q h5195
  have p17138 := n17138 _v _q h4306
  have p4983 := n4983 _v _q h4813
  have p12839 := n12839 _v _q h5195
  have p17060 := n17060 _v _q h4653
  have p16729 := n16729 _v _q h51
  change (e1995 _v) ∨ (¬ (e4813 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e8045 _v)) ∨ (e2358 _v) ∨ (¬ (e4653 _v)) ∨ (¬ (e51 _v)) at p21731
  change (¬ (e2358 _v)) at p12839
  rcases p21731 with hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p15938))
  · exact (False.elim (p12839 hlit))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p16729))
theorem n21733 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6423 : (e6423 _v)) : (e8045 _v) := by
  have p15206 := n15206 _v _q 
  have p21155 := n21155 _v _q h51 h4306 h4653 h4813 h6423
  change (e8049 _v) ∨ (e8045 _v) at p15206
  change (¬ (e8049 _v)) at p21155
  rcases p15206 with hlit | hlit
  · exact (False.elim (p21155 hlit))
  · exact hlit
theorem n21734 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6423 : (e6423 _v)) : (e2358 _v) := by
  have p21731 := n21731 _v _q 
  have p21733 := n21733 _v _q h51 h4306 h4653 h4813 h6423
  have p17138 := n17138 _v _q h4306
  have p4983 := n4983 _v _q h4813
  have p8452 := n8452 _v _q h6423
  have p17060 := n17060 _v _q h4653
  have p16729 := n16729 _v _q h51
  change (e1995 _v) ∨ (¬ (e4813 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e8045 _v)) ∨ (e2358 _v) ∨ (¬ (e4653 _v)) ∨ (¬ (e51 _v)) at p21731
  change (¬ (e1995 _v)) at p8452
  rcases p21731 with hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact (False.elim (p8452 hlit))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p21733))
  · exact hlit
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p16729))
theorem n21735 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h6423 : (e6423 _v)) : (e7489 _v) := by
  have p5255 := n5255 _v _q 
  have p21734 := n21734 _v _q h51 h4306 h4653 h4813 h6423
  have p8452 := n8452 _v _q h6423
  have p5257 := n5257 _v _q 
  have p5391 := n5391 _v _q 
  have p21152 := n21152 _v _q h51 h4306 h4653 h4813 h6423
  exact FloorCertificate.node_21735 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p5255 p21734 p8452 p5257 p5391 p21152
theorem n21736 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5195 : (e5195 _v)) : (e4575 _v) := by
  have p14696 := n14696 _v _q 
  have p21732 := n21732 _v _q h51 h4306 h4653 h4813 h5195
  change (¬ (e1995 _v)) ∨ (¬ (e4574 _v)) at p14696
  rcases p14696 with hlit | hlit
  · exact (False.elim (hlit p21732))
  · exact hlit
theorem n21737 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5195 : (e5195 _v)) : (e4567 _v) := by
  have p8485 := n8485 _v _q 
  have p21736 := n21736 _v _q h51 h4306 h4653 h4813 h5195
  change (e4574 _v) ∨ (e4567 _v) at p8485
  change (¬ (e4574 _v)) at p21736
  rcases p8485 with hlit | hlit
  · exact (False.elim (p21736 hlit))
  · exact hlit
theorem n21739 (_v : Vars) (_q : Query _v)  : (e21738 _v) := by
  by_contra hc
  change ¬ ((e1995 _v) ∨ (¬ (e4306 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e51 _v))) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr hn)))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h6423 : (e6423 _v) := (fun hn => hc (Or.inl hn))
  have p21735 := n21735 _v _q h51 h4306 h4653 h4813 h6423
  exact p21735
theorem n21740 (_v : Vars) (_q : Query _v) (h5195 : (e5195 _v)) : (e4459 _v) := by
  have p16784 := n16784 _v _q 
  have p16101 := n16101 _v _q h5195
  change (e4459 _v) ∨ (¬ (e7749 _v)) at p16784
  rcases p16784 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p16101))
theorem n21741 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2242 : (e2242 _v)) (h2296 : (e2296 _v)) (h3158 : (e3158 _v)) (h3919 : (e3919 _v)) (h4306 : (e4306 _v)) (h4439 : (e4439 _v)) (h4653 : (e4653 _v)) (h4791 : (e4791 _v)) (h4813 : (e4813 _v)) (h5145 : (e5145 _v)) (h5195 : (e5195 _v)) : (e7489 _v) := by
  have p17096 := n17096 _v _q 
  have p17059 := n17059 _v _q h4791
  have p15100 := n15100 _v _q h2296
  have p17758 := n17758 _v _q 
  have p17256 := n17256 _v _q 
  have p17953 := n17953 _v _q 
  have p17124 := n17124 _v _q 
  have p17111 := n17111 _v _q 
  have p17115 := n17115 _v _q 
  have p17075 := n17075 _v _q h4439
  have p8549 := n8549 _v _q h5195
  have p17113 := n17113 _v _q 
  have p17117 := n17117 _v _q 
  have p20467 := n20467 _v _q 
  have p17079 := n17079 _v _q h3919
  have p16959 := n16959 _v _q h3158 h5195
  have p19665 := n19665 _v _q 
  have p17133 := n17133 _v _q 
  have p17120 := n17120 _v _q 
  have p17245 := n17245 _v _q h5145
  have p17104 := n17104 _v _q 
  have p17874 := n17874 _v _q 
  have p17127 := n17127 _v _q 
  have p17089 := n17089 _v _q 
  have p13951 := n13951 _v _q 
  have p21727 := n21727 _v _q h51 h4306 h4653 h4813
  have p16961 := n16961 _v _q h3158 h5195
  have p8583 := n8583 _v _q h2296
  have p17138 := n17138 _v _q h4306
  have p20274 := n20274 _v _q 
  have p17060 := n17060 _v _q h4653
  have p20470 := n20470 _v _q 
  have p16992 := n16992 _v _q 
  have p17050 := n17050 _v _q 
  have p16778 := n16778 _v _q 
  have p17122 := n17122 _v _q 
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p20829 := n20829 _v _q 
  have p15775 := n15775 _v _q h2242
  have p20426 := n20426 _v _q 
  have p20126 := n20126 _v _q 
  have p17110 := n17110 _v _q 
  have p17053 := n17053 _v _q 
  have p20096 := n20096 _v _q 
  have p17131 := n17131 _v _q 
  have p17108 := n17108 _v _q 
  have p17294 := n17294 _v _q 
  have p16943 := n16943 _v _q 
  have p17058 := n17058 _v _q 
  have p17064 := n17064 _v _q 
  have p17067 := n17067 _v _q 
  have p17080 := n17080 _v _q 
  have p17072 := n17072 _v _q 
  have p17074 := n17074 _v _q 
  have p17069 := n17069 _v _q 
  have p20461 := n20461 _v _q 
  have p20836 := n20836 _v _q 
  have p20653 := n20653 _v _q 
  have p17078 := n17078 _v _q 
  have p17136 := n17136 _v _q 
  have p17087 := n17087 _v _q 
  have p17083 := n17083 _v _q 
  have p17055 := n17055 _v _q 
  have p17093 := n17093 _v _q 
  have p17091 := n17091 _v _q 
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p16885 := n16885 _v _q h3158
  have p21737 := n21737 _v _q h51 h4306 h4653 h4813 h5195
  have p17141 := n17141 _v _q 
  have p17100 := n17100 _v _q 
  have p19610 := n19610 _v _q 
  have p17102 := n17102 _v _q 
  have p21740 := n21740 _v _q h5195
  have p8553 := n8553 _v _q h2242
  have p20651 := n20651 _v _q 
  exact FloorCertificate.node_21741 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2902 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e4808 _v) p17096 p17059 p15100 p17758 p17256 p17953 p17124 p17111 p17115 p17075 p8549 p17113 p17117 p20467 p17079 p16959 p19665 p17133 p17120 p17245 p17104 p17874 p17127 p17089 p13951 p21727 p16961 p8583 p17138 p20274 p17060 p20470 p16992 p17050 p16778 p17122 p4983 p16729 p20829 p15775 p20426 p20126 p17110 p17053 p20096 p17131 p17108 p17294 p16943 p17058 p17064 p17067 p17080 p17072 p17074 p17069 p20461 p20836 p20653 p17078 p17136 p17087 p17083 p17055 p17093 p17091 p17098 p17106 p16885 p21737 p17141 p17100 p19610 p17102 p21740 p8553 p20651
theorem n21742 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e1995 _v) := by
  have p21739 := n21739 _v _q 
  have p16729 := n16729 _v _q h51
  have p4983 := n4983 _v _q h4813
  have p17060 := n17060 _v _q h4653
  have p17138 := n17138 _v _q h4306
  change (e1995 _v) ∨ (¬ (e4306 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e51 _v)) at p21739
  rcases p21739 with hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p16729))
theorem n21743 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e1995 _v) := by
  have p21739 := n21739 _v _q 
  have p17138 := n17138 _v _q h4306
  have p16729 := n16729 _v _q h51
  have p4983 := n4983 _v _q h4813
  have p17060 := n17060 _v _q h4653
  change (e1995 _v) ∨ (¬ (e4306 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e51 _v)) at p21739
  rcases p21739 with hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p16729))
theorem n21744 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e4575 _v) := by
  have p14696 := n14696 _v _q 
  have p21743 := n21743 _v _q h51 h4306 h4653 h4813
  change (¬ (e1995 _v)) ∨ (¬ (e4574 _v)) at p14696
  rcases p14696 with hlit | hlit
  · exact (False.elim (hlit p21743))
  · exact hlit
theorem n21746 (_v : Vars) (_q : Query _v)  : (e21745 _v) := by
  by_contra hc
  change ¬ ((¬ (e2296 _v)) ∨ (¬ (e4791 _v)) ∨ (¬ (e4439 _v)) ∨ (e196 _v) ∨ (¬ (e3919 _v)) ∨ (¬ (e5145 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e3158 _v)) ∨ (¬ (e2242 _v))) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h2242 : (e2242 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))))))))
  have h2296 : (e2296 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h3158 : (e3158 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h3919 : (e3919 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h4439 : (e4439 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h4791 : (e4791 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h5145 : (e5145 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h5195 : (e5195 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have p21741 := n21741 _v _q h51 h2242 h2296 h3158 h3919 h4306 h4439 h4653 h4791 h4813 h5145 h5195
  exact p21741
theorem n21747 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e4575 _v) := by
  have p14696 := n14696 _v _q 
  have p21742 := n21742 _v _q h51 h4306 h4653 h4813
  change (¬ (e1995 _v)) ∨ (¬ (e4574 _v)) at p14696
  rcases p14696 with hlit | hlit
  · exact (False.elim (hlit p21742))
  · exact hlit
theorem n21748 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) : (e4567 _v) := by
  have p8485 := n8485 _v _q 
  have p21747 := n21747 _v _q h51 h4306 h4653 h4813
  change (e4574 _v) ∨ (e4567 _v) at p8485
  change (¬ (e4574 _v)) at p21747
  rcases p8485 with hlit | hlit
  · exact (False.elim (p21747 hlit))
  · exact hlit
theorem n21749 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2242 : (e2242 _v)) (h3158 : (e3158 _v)) (h3919 : (e3919 _v)) (h4306 : (e4306 _v)) (h4439 : (e4439 _v)) (h4653 : (e4653 _v)) (h4791 : (e4791 _v)) (h4813 : (e4813 _v)) (h5145 : (e5145 _v)) (h5195 : (e5195 _v)) : (e6549 _v) := by
  have p21746 := n21746 _v _q 
  have p17245 := n17245 _v _q h5145
  have p17075 := n17075 _v _q h4439
  have p8549 := n8549 _v _q h5195
  have p17079 := n17079 _v _q h3919
  have p17059 := n17059 _v _q h4791
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p16885 := n16885 _v _q h3158
  have p8553 := n8553 _v _q h2242
  change (¬ (e2296 _v)) ∨ (¬ (e4791 _v)) ∨ (¬ (e4439 _v)) ∨ (e196 _v) ∨ (¬ (e3919 _v)) ∨ (¬ (e5145 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e3158 _v)) ∨ (¬ (e2242 _v)) at p21746
  change (¬ (e196 _v)) at p8549
  rcases p21746 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p17059))
  · exact (False.elim (hlit p17075))
  · exact (False.elim (p8549 hlit))
  · exact (False.elim (hlit p17079))
  · exact (False.elim (hlit p17245))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p16885))
  · exact (False.elim (hlit p8553))
theorem n21750 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2242 : (e2242 _v)) (h3158 : (e3158 _v)) (h3919 : (e3919 _v)) (h4306 : (e4306 _v)) (h4439 : (e4439 _v)) (h4653 : (e4653 _v)) (h4791 : (e4791 _v)) (h4813 : (e4813 _v)) (h5145 : (e5145 _v)) (h5195 : (e5195 _v)) : (e6879 _v) := by
  have p14643 := n14643 _v _q 
  have p21749 := n21749 _v _q h51 h2242 h3158 h3919 h4306 h4439 h4653 h4791 h4813 h5145 h5195
  change (e2296 _v) ∨ (¬ (e6878 _v)) at p14643
  change (¬ (e2296 _v)) at p21749
  rcases p14643 with hlit | hlit
  · exact (False.elim (p21749 hlit))
  · exact hlit
theorem n21751 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2242 : (e2242 _v)) (h3158 : (e3158 _v)) (h3919 : (e3919 _v)) (h4306 : (e4306 _v)) (h4439 : (e4439 _v)) (h4653 : (e4653 _v)) (h4791 : (e4791 _v)) (h4813 : (e4813 _v)) (h5145 : (e5145 _v)) (h5195 : (e5195 _v)) : (e3152 _v) := by
  have p15776 := n15776 _v _q 
  have p21750 := n21750 _v _q h51 h2242 h3158 h3919 h4306 h4439 h4653 h4791 h4813 h5145 h5195
  change (e6878 _v) ∨ (e3152 _v) at p15776
  change (¬ (e6878 _v)) at p21750
  rcases p15776 with hlit | hlit
  · exact (False.elim (p21750 hlit))
  · exact hlit
theorem n21752 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2242 : (e2242 _v)) (h3158 : (e3158 _v)) (h3919 : (e3919 _v)) (h4306 : (e4306 _v)) (h4439 : (e4439 _v)) (h4653 : (e4653 _v)) (h4791 : (e4791 _v)) (h4813 : (e4813 _v)) (h5145 : (e5145 _v)) (h5195 : (e5195 _v)) : (e7489 _v) := by
  have p17758 := n17758 _v _q 
  have p21737 := n21737 _v _q h51 h4306 h4653 h4813 h5195
  have p13951 := n13951 _v _q 
  have p17124 := n17124 _v _q 
  have p15223 := n15223 _v _q h5195
  have p17111 := n17111 _v _q 
  have p17115 := n17115 _v _q 
  have p16992 := n16992 _v _q 
  have p17256 := n17256 _v _q 
  have p8553 := n8553 _v _q h2242
  have p17113 := n17113 _v _q 
  have p17117 := n17117 _v _q 
  have p20467 := n20467 _v _q 
  have p17079 := n17079 _v _q h3919
  have p16959 := n16959 _v _q h3158 h5195
  have p19665 := n19665 _v _q 
  have p17133 := n17133 _v _q 
  have p17120 := n17120 _v _q 
  have p17245 := n17245 _v _q h5145
  have p17104 := n17104 _v _q 
  have p17874 := n17874 _v _q 
  have p17127 := n17127 _v _q 
  have p17089 := n17089 _v _q 
  have p21751 := n21751 _v _q h51 h2242 h3158 h3919 h4306 h4439 h4653 h4791 h4813 h5145 h5195
  have p16885 := n16885 _v _q h3158
  have p21727 := n21727 _v _q h51 h4306 h4653 h4813
  have p16961 := n16961 _v _q h3158 h5195
  have p17059 := n17059 _v _q h4791
  have p17138 := n17138 _v _q h4306
  have p20274 := n20274 _v _q 
  have p17060 := n17060 _v _q h4653
  have p20470 := n20470 _v _q 
  have p17953 := n17953 _v _q 
  have p17050 := n17050 _v _q 
  have p16778 := n16778 _v _q 
  have p17122 := n17122 _v _q 
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p20829 := n20829 _v _q 
  have p15775 := n15775 _v _q h2242
  have p20426 := n20426 _v _q 
  have p20126 := n20126 _v _q 
  have p17110 := n17110 _v _q 
  have p17053 := n17053 _v _q 
  have p20096 := n20096 _v _q 
  have p17131 := n17131 _v _q 
  have p17108 := n17108 _v _q 
  have p17294 := n17294 _v _q 
  have p16943 := n16943 _v _q 
  have p17058 := n17058 _v _q 
  have p17064 := n17064 _v _q 
  have p17067 := n17067 _v _q 
  have p17080 := n17080 _v _q 
  have p17072 := n17072 _v _q 
  have p17074 := n17074 _v _q 
  have p17069 := n17069 _v _q 
  have p20461 := n20461 _v _q 
  have p20836 := n20836 _v _q 
  have p20653 := n20653 _v _q 
  have p17078 := n17078 _v _q 
  have p17136 := n17136 _v _q 
  have p17087 := n17087 _v _q 
  have p17083 := n17083 _v _q 
  have p17055 := n17055 _v _q 
  have p17093 := n17093 _v _q 
  have p17091 := n17091 _v _q 
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p20651 := n20651 _v _q 
  have p17075 := n17075 _v _q h4439
  have p17141 := n17141 _v _q 
  have p17100 := n17100 _v _q 
  have p19610 := n19610 _v _q 
  have p17102 := n17102 _v _q 
  have p17096 := n17096 _v _q 
  have p8549 := n8549 _v _q h5195
  have p21740 := n21740 _v _q h5195
  exact FloorCertificate.node_21752 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2877 _v) (e2902 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4808 _v) p17758 p21737 p13951 p17124 p15223 p17111 p17115 p16992 p17256 p8553 p17113 p17117 p20467 p17079 p16959 p19665 p17133 p17120 p17245 p17104 p17874 p17127 p17089 p21751 p16885 p21727 p16961 p17059 p17138 p20274 p17060 p20470 p17953 p17050 p16778 p17122 p4983 p16729 p20829 p15775 p20426 p20126 p17110 p17053 p20096 p17131 p17108 p17294 p16943 p17058 p17064 p17067 p17080 p17072 p17074 p17069 p20461 p20836 p20653 p17078 p17136 p17087 p17083 p17055 p17093 p17091 p17098 p17106 p20651 p17075 p17141 p17100 p19610 p17102 p17096 p8549 p21740
theorem n21754 (_v : Vars) (_q : Query _v)  : (e21753 _v) := by
  by_contra hc
  change ¬ ((¬ (e5145 _v)) ∨ (¬ (e2242 _v)) ∨ (¬ (e3919 _v)) ∨ (¬ (e3158 _v)) ∨ (¬ (e4791 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4439 _v)) ∨ (e196 _v)) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h2242 : (e2242 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h3158 : (e3158 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h3919 : (e3919 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h4439 : (e4439 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h4791 : (e4791 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h5145 : (e5145 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h5195 : (e5195 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn)))))))))))
  have p21752 := n21752 _v _q h51 h2242 h3158 h3919 h4306 h4439 h4653 h4791 h4813 h5145 h5195
  exact p21752
theorem n21755 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h2468 : (e2468 _v)) (h4306 : (e4306 _v)) (h4653 : (e4653 _v)) (h4813 : (e4813 _v)) (h5195 : (e5195 _v)) : (e5148 _v) := by
  have p21754 := n21754 _v _q 
  have p16072 := n16072 _v _q h2468
  have p15073 := n15073 _v _q h2468
  have p16859 := n16859 _v _q h2468
  have p15104 := n15104 _v _q h2468
  have p17138 := n17138 _v _q h4306
  have p17060 := n17060 _v _q h4653
  have p4983 := n4983 _v _q h4813
  have p16729 := n16729 _v _q h51
  have p16067 := n16067 _v _q h2468
  have p8549 := n8549 _v _q h5195
  change (¬ (e5145 _v)) ∨ (¬ (e2242 _v)) ∨ (¬ (e3919 _v)) ∨ (¬ (e3158 _v)) ∨ (¬ (e4791 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e4439 _v)) ∨ (e196 _v) at p21754
  change (¬ (e196 _v)) at p8549
  rcases p21754 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p16072))
  · exact (False.elim (hlit p15073))
  · exact (False.elim (hlit p16859))
  · exact (False.elim (hlit p15104))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17060))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p16729))
  · exact (False.elim (hlit p16067))
  · exact (False.elim (p8549 hlit))
end
end Assembly
