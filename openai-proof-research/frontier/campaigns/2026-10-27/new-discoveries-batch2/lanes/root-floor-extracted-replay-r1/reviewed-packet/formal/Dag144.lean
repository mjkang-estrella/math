import Dag143
import generated.th_lemma_12
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n16139 (_v : Vars) (_q : Query _v) (h5108 : (e5108 _v)) : (e6750 _v) := by
  have p11369 := n11369 _v _q 
  have p11366 := n11366 _v _q h5108
  simp only [e48, e2733, e5108, e6750, e11368] at *
  tauto
theorem n16140 (_v : Vars) (_q : Query _v) (h5108 : (e5108 _v)) : (e7597 _v) := by
  have p14525 := n14525 _v _q 
  have p16139 := n16139 _v _q h5108
  simp only [e2733, e4096, e4097, e4098, e4099, e6750, e7589, e7597, e7600] at *
  tauto
theorem n16141 (_v : Vars) (_q : Query _v) (h6583 : (e6583 _v)) : (e6525 _v) := by
  have p11340 := n11340 _v _q h6583
  have p11375 := n11375 _v _q 
  exact FloorCertificate.node_16141 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e110 _v) p11340 p11375
theorem n16142 (_v : Vars) (_q : Query _v) (h6583 : (e6583 _v)) : (e8174 _v) := by
  have p14634 := n14634 _v _q 
  have p16141 := n16141 _v _q h6583
  simp only [e2242, e4673, e4674, e4675, e4676, e6525, e8166, e8174, e8177] at *
  tauto
theorem n16143 (_v : Vars) (_q : Query _v) (h6772 : (e6772 _v)) : (e6724 _v) := by
  have p15988 := n15988 _v _q 
  have p8458 := n8458 _v _q h6772
  simp only [e2691, e2787, e6724, e6772, e15987] at *
  tauto
theorem n16144 (_v : Vars) (_q : Query _v) (h5247 : (e5247 _v)) : (e214 _v) := by
  have p14996 := n14996 _v _q 
  have p8684 := n8684 _v _q h5247
  simp only [e214, e5237, e5240, e5247, e5248, e5249, e5250, e8677] at *
  tauto
theorem n16145 (_v : Vars) (_q : Query _v) (h5247 : (e5247 _v)) : (e5232 _v) := by
  have p14731 := n14731 _v _q 
  have p16144 := n16144 _v _q h5247
  simp only [e214, e225, e227, e230, e231, e5223, e5231, e5232, e5235] at *
  tauto
theorem n16147 (_v : Vars) (_q : Query _v)  : (e16146 _v) := by
  by_contra hc
  change ¬ ((e5208 _v) ∨ (¬ (e191 _v))) at hc
  have h191 : (e191 _v) := by
    tauto
  have h5218 : (e5218 _v) := by
    change (¬ (e5208 _v))
    tauto
  have p14734 := n14734 _v _q h191 h5218
  exact p14734
theorem n16148 (_v : Vars) (_q : Query _v) (h5218 : (e5218 _v)) : (e192 _v) := by
  have p16147 := n16147 _v _q 
  have p8686 := n8686 _v _q h5218
  simp only [e191, e192, e5208, e5218, e16146] at *
  tauto
theorem n16149 (_v : Vars) (_q : Query _v)  : (e5361 _v) := by
  simp only [e440, e441, e442, e443, e5360, e5361] at *
  tauto
theorem n16150 (_v : Vars) (_q : Query _v) (h436 : (e436 _v)) : (e436 _v) := by
  exact h436
theorem n16151 (_v : Vars) (_q : Query _v) (h436 : (e436 _v)) : (e5370 _v) := by
  have p14735 := n14735 _v _q 
  have p16150 := n16150 _v _q h436
  simp only [e436, e440, e441, e442, e443, e5360, e5362, e5370, e5373] at *
  tauto
theorem n16152 (_v : Vars) (_q : Query _v) (h436 : (e436 _v)) : (e442 _v) := by
  have p16149 := n16149 _v _q 
  have p16151 := n16151 _v _q h436
  simp only [e440, e441, e442, e443, e5360, e5361, e5370] at *
  tauto
theorem n16154 (_v : Vars) (_q : Query _v)  : (e16153 _v) := by
  simp only [e5, e6, e5769, e5770, e5771, e5772, e5773, e5774, e14740, e16153] at *
  omega
theorem n16156 (_v : Vars) (_q : Query _v)  : (e16155 _v) := by
  have p14742 := n14742 _v _q 
  have p16154 := n16154 _v _q 
  exact (Eq.trans p14742 p16154)
theorem n16158 (_v : Vars) (_q : Query _v)  : (e16157 _v) := by
  simp only [e5, e6, e5914, e5915, e5916, e5917, e5918, e5919, e14743, e16157] at *
  omega
theorem n16160 (_v : Vars) (_q : Query _v)  : (e16159 _v) := by
  have p14745 := n14745 _v _q 
  have p16158 := n16158 _v _q 
  exact (Eq.trans p14745 p16158)
theorem n16162 (_v : Vars) (_q : Query _v)  : (e16161 _v) := by
  simp only [e5, e6, e5988, e5989, e5990, e5991, e5992, e5993, e14746, e16161] at *
  omega
theorem n16164 (_v : Vars) (_q : Query _v)  : (e16163 _v) := by
  have p14748 := n14748 _v _q 
  have p16162 := n16162 _v _q 
  exact (Eq.trans p14748 p16162)
theorem n16166 (_v : Vars) (_q : Query _v)  : (e16165 _v) := by
  simp only [e5, e6, e6026, e6027, e6028, e6029, e6030, e6031, e14749, e16165] at *
  omega
theorem n16168 (_v : Vars) (_q : Query _v)  : (e16167 _v) := by
  have p14751 := n14751 _v _q 
  have p16166 := n16166 _v _q 
  exact (Eq.trans p14751 p16166)
theorem n16170 (_v : Vars) (_q : Query _v)  : (e16169 _v) := by
  have p14320 := n14320 _v _q 
  have p14755 := n14755 _v _q 
  have p14759 := n14759 _v _q 
  have p14763 := n14763 _v _q 
  change ((e5489 _v) = (e9155 _v)) at p14320
  change ((e5493 _v) = (e9156 _v)) at p14755
  change ((e5497 _v) = (e9157 _v)) at p14759
  change ((e5501 _v) = (e9158 _v)) at p14763
  simp only [e16169, e11658, e9159, p14320, p14755, p14759, p14763]
theorem n16173 (_v : Vars) (_q : Query _v)  : (e16172 _v) := by
  have p16170 := n16170 _v _q 
  change ((e11658 _v) = (e9159 _v)) at p16170
  simp only [e16172, e11659, e16171, p16170]
theorem n16174 (_v : Vars) (_q : Query _v)  : (e6915 _v) := by
  simp only [e6910, e6911, e6912, e6913, e6914, e6915] at *
  tauto
theorem n16175 (_v : Vars) (_q : Query _v)  : (e6912 _v) := by
  have p16174 := n16174 _v _q 
  have p14775 := n14775 _v _q 
  simp only [e6910, e6911, e6912, e6913, e6914, e6915, e6931] at *
  tauto
theorem n16176 (_v : Vars) (_q : Query _v) (h3178 : (e3178 _v)) : (e7489 _v) := by
  have p14772 := n14772 _v _q h3178
  have p6908 := n6908 _v _q h3178
  have p16175 := n16175 _v _q 
  have p14770 := n14770 _v _q h3178
  exact FloorCertificate.node_16176 (e2 _v) (e9 _v) (e17 _v) (e45 _v) (e2977 _v) (e3164 _v) p14772 p6908 p16175 p14770
theorem n16177 (_v : Vars) (_q : Query _v)  : (e6990 _v) := by
  simp only [e6985, e6986, e6987, e6988, e6989, e6990] at *
  tauto
theorem n16178 (_v : Vars) (_q : Query _v)  : (e6987 _v) := by
  have p16177 := n16177 _v _q 
  have p14782 := n14782 _v _q 
  simp only [e6985, e6986, e6987, e6988, e6989, e6990, e7006] at *
  tauto
theorem n16179 (_v : Vars) (_q : Query _v) (h3276 : (e3276 _v)) : (e7489 _v) := by
  have p14779 := n14779 _v _q h3276
  have p16178 := n16178 _v _q 
  have p6983 := n6983 _v _q h3276
  have p14777 := n14777 _v _q h3276
  exact FloorCertificate.node_16179 (e2 _v) (e9 _v) (e17 _v) (e110 _v) (e2946 _v) (e3262 _v) p14779 p16178 p6983 p14777
theorem n16180 (_v : Vars) (_q : Query _v)  : (e7188 _v) := by
  simp only [e7183, e7184, e7185, e7186, e7187, e7188] at *
  tauto
theorem n16181 (_v : Vars) (_q : Query _v)  : (e7185 _v) := by
  have p16180 := n16180 _v _q 
  have p14789 := n14789 _v _q 
  simp only [e7183, e7184, e7185, e7186, e7187, e7188, e7204] at *
  tauto
theorem n16182 (_v : Vars) (_q : Query _v) (h3571 : (e3571 _v)) : (e7489 _v) := by
  have p14784 := n14784 _v _q h3571
  have p14786 := n14786 _v _q h3571
  have p16181 := n16181 _v _q 
  have p7180 := n7180 _v _q h3571
  exact FloorCertificate.node_16182 (e2 _v) (e17 _v) (e45 _v) (e110 _v) (e2967 _v) (e3574 _v) p14784 p14786 p16181 p7180
theorem n16183 (_v : Vars) (_q : Query _v)  : (e7375 _v) := by
  simp only [e7370, e7371, e7372, e7373, e7374, e7375] at *
  tauto
theorem n16184 (_v : Vars) (_q : Query _v)  : (e7372 _v) := by
  have p16183 := n16183 _v _q 
  have p14796 := n14796 _v _q 
  simp only [e7370, e7371, e7372, e7373, e7374, e7375, e7391] at *
  tauto
theorem n16185 (_v : Vars) (_q : Query _v) (h3860 : (e3860 _v)) : (e7489 _v) := by
  have p14793 := n14793 _v _q h3860
  have p14791 := n14791 _v _q h3860
  have p16184 := n16184 _v _q 
  have p7368 := n7368 _v _q h3860
  exact FloorCertificate.node_16185 (e2 _v) (e7 _v) (e17 _v) (e110 _v) (e2933 _v) (e3846 _v) p14793 p14791 p16184 p7368
theorem n16186 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e70 _v) := by
  have p15648 := n15648 _v _q 
  have p14801 := n14801 _v _q h6792
  simp only [e70, e72, e75, e76, e5118, e5119, e7441] at *
  tauto
theorem n16187 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e3971 _v) := by
  have p15486 := n15486 _v _q 
  have p14803 := n14803 _v _q h6792
  simp only [e3971, e3972, e3973, e3974, e7442, e7443, e7450] at *
  tauto
theorem n16188 (_v : Vars) (_q : Query _v)  : (e6856 _v) := by
  simp only [e3103, e3104, e3105, e3106, e6855, e6856] at *
  tauto
theorem n16189 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e3105 _v) := by
  have p16188 := n16188 _v _q 
  have p14805 := n14805 _v _q h6792
  simp only [e3103, e3104, e3105, e3106, e6855, e6856, e6863] at *
  tauto
theorem n16190 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e79 _v) := by
  have p12546 := n12546 _v _q 
  have p12548 := n12548 _v _q h6792
  simp only [e79, e2482, e6636, e12545] at *
  tauto
theorem n16191 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e436 _v) := by
  have p7492 := n7492 _v _q 
  have p16190 := n16190 _v _q h6792
  simp only [e79, e436, e5138, e7491] at *
  tauto
theorem n16192 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e5370 _v) := by
  have p14735 := n14735 _v _q 
  have p16191 := n16191 _v _q h6792
  simp only [e436, e440, e441, e442, e443, e5360, e5362, e5370, e5373] at *
  tauto
theorem n16193 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e442 _v) := by
  have p16149 := n16149 _v _q 
  have p16192 := n16192 _v _q h6792
  simp only [e440, e441, e442, e443, e5360, e5361, e5370] at *
  tauto
theorem n16194 (_v : Vars) (_q : Query _v)  : (e7519 _v) := by
  simp only [e4026, e4028, e4031, e4032, e7503, e7519] at *
  tauto
theorem n16195 (_v : Vars) (_q : Query _v) (h4031 : (e4031 _v)) : (e4031 _v) := by
  exact h4031
end
end Assembly
