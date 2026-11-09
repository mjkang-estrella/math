import Dag162
import generated.th_lemma_15
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n17035 (_v : Vars) (_q : Query _v) (h4302 : (e4302 _v)) (h4434 : (e4434 _v)) : (e7517 _v) := by
  have p15196 := n15196 _v _q 
  have p17014 := n17014 _v _q h4302 h4434
  simp only [e2691, e6724, e7493, e7494, e7495, e7496, e7497, e7517, e10904] at *
  tauto
theorem n17036 (_v : Vars) (_q : Query _v) (h4302 : (e4302 _v)) (h4434 : (e4434 _v)) : (e7493 _v) := by
  have p15195 := n15195 _v _q 
  have p17035 := n17035 _v _q h4302 h4434
  simp only [e7493, e7494, e7495, e7496, e7497, e7498, e7517] at *
  tauto
theorem n17039 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) : (e17038 _v) := by
  have p8139 := n8139 _v _q 
  have p16729 := n16729 _v _q h51
  exact FloorCertificate.node_17039 (e49 _v) p8139 p16729
theorem n17040 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h5108 : (e5108 _v)) : (e7489 _v) := by
  have p8139 := n8139 _v _q 
  have p17039 := n17039 _v _q h51
  have p11482 := n11482 _v _q 
  have p16743 := n16743 _v _q h5108
  have p17027 := n17027 _v _q h51 h5108
  exact FloorCertificate.node_17040 (e17 _v) (e49 _v) (e61 _v) p8139 p17039 p11482 p16743 p17027
theorem n17041 (_v : Vars) (_q : Query _v)  : (e11813 _v) := by
  have p13396 := n13396 _v _q 
  change ((e11810 _v) ↔ (e11810 _v)) at p13396
  simp only [e11813, e11811, p13396]
theorem n17042 (_v : Vars) (_q : Query _v)  : (e11811 _v) := by
  have p17029 := n17029 _v _q 
  have p17041 := n17041 _v _q 
  simp only [e11810, e11811, e11813] at *
  tauto
theorem n17044 (_v : Vars) (_q : Query _v)  : (e17043 _v) := by
  by_contra hc
  change ¬ ((e48 _v) ∨ (¬ (e51 _v))) at hc
  have h51 : (e51 _v) := by
    tauto
  have h5108 : (e5108 _v) := by
    change (¬ (e48 _v))
    tauto
  have p17040 := n17040 _v _q h51 h5108
  exact p17040
theorem n17045 (_v : Vars) (_q : Query _v)  : (e11984 _v) := by
  have p11982 := n11982 _v _q 
  change ((e11810 _v) ↔ (e11980 _v)) at p11982
  simp only [e11984, e11811, e11983, p11982]
theorem n17046 (_v : Vars) (_q : Query _v)  : (e11983 _v) := by
  have p17042 := n17042 _v _q 
  have p17045 := n17045 _v _q 
  simp only [e11810, e11811, e11980, e11983, e11984] at *
  tauto
theorem n17047 (_v : Vars) (_q : Query _v)  : (e14330 _v) := by
  have p17046 := n17046 _v _q 
  have p14332 := n14332 _v _q 
  simp only [e11980, e11983, e14327, e14330, e14331] at *
  tauto
theorem n17048 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) : (e48 _v) := by
  have p17044 := n17044 _v _q 
  have p16729 := n16729 _v _q h51
  simp only [e48, e51, e57, e17043] at *
  tauto
theorem n17049 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) : (e2585 _v) := by
  have p11550 := n11550 _v _q 
  have p17048 := n17048 _v _q h51
  simp only [e48, e2585, e5108, e11549] at *
  tauto
theorem n17050 (_v : Vars) (_q : Query _v)  : (e3173 _v) := by
  by_contra hc
  change ¬ (e3173 _v) at hc
  have h3178 : (e3178 _v) := by
    change (¬ (e3173 _v))
    tauto
  have p16176 := n16176 _v _q h3178
  exact p16176
theorem n17051 (_v : Vars) (_q : Query _v) (h4459 : (e4459 _v)) : (e4459 _v) := by
  exact h4459
theorem n17052 (_v : Vars) (_q : Query _v)  : (e3215 _v) := by
  simp only [e3210, e3211, e3212, e3213, e3214, e3215] at *
  tauto
theorem n17053 (_v : Vars) (_q : Query _v)  : (e3210 _v) := by
  have p17052 := n17052 _v _q 
  have p14371 := n14371 _v _q 
  simp only [e3210, e3211, e3212, e3213, e3214, e3215, e3220] at *
  tauto
theorem n17054 (_v : Vars) (_q : Query _v)  : (e3241 _v) := by
  simp only [e3236, e3237, e3238, e3239, e3240, e3241] at *
  tauto
theorem n17055 (_v : Vars) (_q : Query _v)  : (e3236 _v) := by
  have p17054 := n17054 _v _q 
  have p14375 := n14375 _v _q 
  simp only [e3236, e3237, e3238, e3239, e3240, e3241, e3246] at *
  tauto
theorem n17056 (_v : Vars) (_q : Query _v) (h3946 : (e3946 _v)) : (e3946 _v) := by
  exact h3946
theorem n17057 (_v : Vars) (_q : Query _v)  : (e265 _v) := by
  simp only [e260, e261, e262, e263, e264, e265] at *
  tauto
theorem n17058 (_v : Vars) (_q : Query _v)  : (e262 _v) := by
  have p17057 := n17057 _v _q 
  have p14182 := n14182 _v _q 
  simp only [e260, e261, e262, e263, e264, e265, e274] at *
  tauto
theorem n17059 (_v : Vars) (_q : Query _v) (h4791 : (e4791 _v)) : (e4791 _v) := by
  exact h4791
theorem n17060 (_v : Vars) (_q : Query _v) (h4653 : (e4653 _v)) : (e4653 _v) := by
  exact h4653
theorem n17061 (_v : Vars) (_q : Query _v) (h4747 : (e4747 _v)) : (e4747 _v) := by
  exact h4747
theorem n17062 (_v : Vars) (_q : Query _v) (h3133 : (e3133 _v)) : (e3133 _v) := by
  exact h3133
theorem n17063 (_v : Vars) (_q : Query _v)  : (e303 _v) := by
  simp only [e298, e299, e300, e301, e302, e303] at *
  tauto
theorem n17064 (_v : Vars) (_q : Query _v)  : (e298 _v) := by
  have p17063 := n17063 _v _q 
  have p14186 := n14186 _v _q 
  simp only [e298, e299, e300, e301, e302, e303, e310] at *
  tauto
theorem n17065 (_v : Vars) (_q : Query _v) (h4101 : (e4101 _v)) : (e4101 _v) := by
  exact h4101
theorem n17066 (_v : Vars) (_q : Query _v)  : (e338 _v) := by
  simp only [e333, e334, e335, e336, e337, e338] at *
  tauto
theorem n17067 (_v : Vars) (_q : Query _v)  : (e333 _v) := by
  have p17066 := n17066 _v _q 
  have p14190 := n14190 _v _q 
  simp only [e333, e334, e335, e336, e337, e338, e345] at *
  tauto
theorem n17068 (_v : Vars) (_q : Query _v)  : (e368 _v) := by
  simp only [e363, e364, e365, e366, e367, e368] at *
  tauto
theorem n17069 (_v : Vars) (_q : Query _v)  : (e365 _v) := by
  have p17068 := n17068 _v _q 
  have p14194 := n14194 _v _q 
  simp only [e363, e364, e365, e366, e367, e368, e375] at *
  tauto
theorem n17070 (_v : Vars) (_q : Query _v) (h4679 : (e4679 _v)) : (e4679 _v) := by
  exact h4679
theorem n17071 (_v : Vars) (_q : Query _v)  : (e409 _v) := by
  simp only [e404, e405, e406, e407, e408, e409] at *
  tauto
theorem n17072 (_v : Vars) (_q : Query _v)  : (e406 _v) := by
  have p17071 := n17071 _v _q 
  have p14198 := n14198 _v _q 
  simp only [e404, e405, e406, e407, e408, e409, e420] at *
  tauto
theorem n17073 (_v : Vars) (_q : Query _v)  : (e3031 _v) := by
  simp only [e3026, e3027, e3028, e3029, e3030, e3031] at *
  tauto
theorem n17074 (_v : Vars) (_q : Query _v)  : (e3028 _v) := by
  have p17073 := n17073 _v _q 
  have p14348 := n14348 _v _q 
  simp only [e3026, e3027, e3028, e3029, e3030, e3031, e3036] at *
  tauto
theorem n17075 (_v : Vars) (_q : Query _v) (h4439 : (e4439 _v)) : (e4439 _v) := by
  exact h4439
theorem n17076 (_v : Vars) (_q : Query _v) (h3976 : (e3976 _v)) : (e3976 _v) := by
  exact h3976
theorem n17077 (_v : Vars) (_q : Query _v)  : (e503 _v) := by
  simp only [e498, e499, e500, e501, e502, e503] at *
  tauto
theorem n17078 (_v : Vars) (_q : Query _v)  : (e500 _v) := by
  have p17077 := n17077 _v _q 
  have p14212 := n14212 _v _q 
  simp only [e498, e499, e500, e501, e502, e503, e514] at *
  tauto
theorem n17079 (_v : Vars) (_q : Query _v) (h3919 : (e3919 _v)) : (e3919 _v) := by
  exact h3919
theorem n17080 (_v : Vars) (_q : Query _v)  : (e14338 _v) := by
  have p17047 := n17047 _v _q 
  have p14340 := n14340 _v _q 
  simp only [e14327, e14330, e14335, e14338, e14339] at *
  tauto
theorem n17081 (_v : Vars) (_q : Query _v) (h4161 : (e4161 _v)) : (e4161 _v) := by
  exact h4161
theorem n17082 (_v : Vars) (_q : Query _v)  : (e3004 _v) := by
  simp only [e2999, e3000, e3001, e3002, e3003, e3004] at *
  tauto
end
end Assembly
