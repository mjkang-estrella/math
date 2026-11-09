import Dag156
import generated.th_lemma_14
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n16743 (_v : Vars) (_q : Query _v) (h5108 : (e5108 _v)) : (e16742 _v) := by
  have p8139 := n8139 _v _q 
  have p16117 := n16117 _v _q h5108
  exact FloorCertificate.node_16743 (e49 _v) (e61 _v) p8139 p16117
theorem n16744 (_v : Vars) (_q : Query _v) (h5108 : (e5108 _v)) : (e214 _v) := by
  have p8663 := n8663 _v _q 
  have p11366 := n11366 _v _q h5108
  have p5257 := n5257 _v _q 
  exact FloorCertificate.node_16744 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8663 p11366 p5257
theorem n16745 (_v : Vars) (_q : Query _v) (h5108 : (e5108 _v)) : (e5232 _v) := by
  have p14731 := n14731 _v _q 
  have p16744 := n16744 _v _q h5108
  simp only [e214, e225, e227, e230, e231, e5223, e5231, e5232, e5235] at *
  tauto
theorem n16746 (_v : Vars) (_q : Query _v) (h6676 : (e6676 _v)) : (e196 _v) := by
  have p12900 := n12900 _v _q 
  have p10943 := n10943 _v _q h6676
  simp only [e196, e2585, e6676, e12899] at *
  tauto
theorem n16747 (_v : Vars) (_q : Query _v) (h6676 : (e6676 _v)) : (e5203 _v) := by
  have p14730 := n14730 _v _q 
  have p16746 := n16746 _v _q h6676
  simp only [e191, e192, e193, e194, e196, e5193, e5195, e5203, e5206] at *
  tauto
theorem n16748 (_v : Vars) (_q : Query _v) (h5108 : (e5108 _v)) : (e4096 _v) := by
  have p15703 := n15703 _v _q 
  have p16140 := n16140 _v _q h5108
  simp only [e4096, e4097, e4098, e4099, e7589, e7590, e7597] at *
  tauto
theorem n16749 (_v : Vars) (_q : Query _v) (h6583 : (e6583 _v)) : (e4675 _v) := by
  have p15965 := n15965 _v _q 
  have p16142 := n16142 _v _q h6583
  simp only [e4673, e4674, e4675, e4676, e8166, e8167, e8174] at *
  tauto
theorem n16750 (_v : Vars) (_q : Query _v) (h2132 : (e2132 _v)) : (e2529 _v) := by
  have p11387 := n11387 _v _q 
  have p12942 := n12942 _v _q h2132
  simp only [e2303, e2529, e7807, e11386] at *
  tauto
theorem n16751 (_v : Vars) (_q : Query _v) (h2132 : (e2132 _v)) : (e8307 _v) := by
  have p14906 := n14906 _v _q 
  have p16750 := n16750 _v _q h2132
  simp only [e2529, e4836, e4837, e4838, e4839, e8301, e8307, e8310, e8312] at *
  tauto
theorem n16752 (_v : Vars) (_q : Query _v) (h6772 : (e6772 _v)) : (e7517 _v) := by
  have p15196 := n15196 _v _q 
  have p16143 := n16143 _v _q h6772
  simp only [e2691, e6724, e7493, e7494, e7495, e7496, e7497, e7517, e10904] at *
  tauto
theorem n16753 (_v : Vars) (_q : Query _v) (h6772 : (e6772 _v)) : (e7493 _v) := by
  have p15195 := n15195 _v _q 
  have p16752 := n16752 _v _q h6772
  simp only [e7493, e7494, e7495, e7496, e7497, e7498, e7517] at *
  tauto
theorem n16754 (_v : Vars) (_q : Query _v) (h5247 : (e5247 _v)) : (e225 _v) := by
  have p16653 := n16653 _v _q 
  have p16145 := n16145 _v _q h5247
  simp only [e225, e227, e230, e231, e5231, e5232, e5253] at *
  tauto
theorem n16755 (_v : Vars) (_q : Query _v) (h5218 : (e5218 _v)) : (e5193 _v) := by
  have p16442 := n16442 _v _q 
  have p16148 := n16148 _v _q h5218
  simp only [e191, e192, e193, e194, e5193, e5194] at *
  tauto
theorem n16756 (_v : Vars) (_q : Query _v) (h5218 : (e5218 _v)) : (e7489 _v) := by
  have p14730 := n14730 _v _q 
  have p16755 := n16755 _v _q h5218
  have p14733 := n14733 _v _q h5218
  simp only [e191, e192, e193, e194, e196, e5193, e5195, e5203, e5206] at *
  tauto
theorem n16758 (_v : Vars) (_q : Query _v)  : (e16757 _v) := by
  simp only [e5, e9159, e16171, e16757] at *
  omega
theorem n16760 (_v : Vars) (_q : Query _v)  : (e16759 _v) := by
  have p16173 := n16173 _v _q 
  have p16758 := n16758 _v _q 
  exact (Eq.trans p16173 p16758)
theorem n16761 (_v : Vars) (_q : Query _v) (h4031 : (e4031 _v)) : (e7517 _v) := by
  have p15196 := n15196 _v _q 
  have p16197 := n16197 _v _q h4031
  simp only [e2691, e6724, e7493, e7494, e7495, e7496, e7497, e7517, e10904] at *
  tauto
theorem n16762 (_v : Vars) (_q : Query _v) (h4031 : (e4031 _v)) : (e7493 _v) := by
  have p15195 := n15195 _v _q 
  have p16761 := n16761 _v _q h4031
  simp only [e7493, e7494, e7495, e7496, e7497, e7498, e7517] at *
  tauto
theorem n16763 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e30 _v) := by
  have p16290 := n16290 _v _q 
  have p16200 := n16200 _v _q h6792
  simp only [e28, e30, e34, e35, e5089, e5090, e5107] at *
  tauto
theorem n16764 (_v : Vars) (_q : Query _v) (h4133 : (e4133 _v)) : (e7630 _v) := by
  have p15152 := n15152 _v _q 
  have p16205 := n16205 _v _q h4133
  simp only [e2740, e6746, e7606, e7607, e7608, e7609, e7610, e7630, e10951] at *
  tauto
theorem n16765 (_v : Vars) (_q : Query _v) (h4133 : (e4133 _v)) : (e7606 _v) := by
  have p11418 := n11418 _v _q 
  have p16764 := n16764 _v _q h4133
  simp only [e7606, e7607, e7608, e7609, e7610, e7611, e7630] at *
  tauto
theorem n16766 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e4139 _v) := by
  have p16281 := n16281 _v _q 
  have p16208 := n16208 _v _q h6792
  simp only [e4139, e4140, e4141, e4142, e7634, e7635, e7640] at *
  tauto
theorem n16767 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e4181 _v) := by
  have p16453 := n16453 _v _q 
  have p16211 := n16211 _v _q h6792
  simp only [e4181, e4182, e4183, e4184, e7677, e7678, e7683] at *
  tauto
theorem n16768 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e4220 _v) := by
  have p16334 := n16334 _v _q 
  have p16217 := n16217 _v _q h6792
  simp only [e4218, e4219, e4220, e4221, e7733, e7734, e7739] at *
  tauto
theorem n16769 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e4285 _v) := by
  have p16274 := n16274 _v _q 
  have p16220 := n16220 _v _q h6792
  simp only [e4283, e4284, e4285, e4286, e7798, e7799, e7804] at *
  tauto
theorem n16770 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e4419 _v) := by
  have p16347 := n16347 _v _q 
  have p16225 := n16225 _v _q h6792
  simp only [e4417, e4418, e4419, e4420, e7921, e7922, e7927] at *
  tauto
theorem n16771 (_v : Vars) (_q : Query _v)  : (e7981 _v) := by
  simp only [e7747, e7749, e7751, e7752, e7753, e7981] at *
  tauto
theorem n16772 (_v : Vars) (_q : Query _v) (h4481 : (e4481 _v)) : (e7751 _v) := by
  have p16234 := n16234 _v _q 
  have p14859 := n14859 _v _q h4481
  simp only [e4477, e4481, e7747, e7751, e7982] at *
  tauto
theorem n16773 (_v : Vars) (_q : Query _v) (h4481 : (e4481 _v)) : (e7753 _v) := by
  have p16771 := n16771 _v _q 
  have p16772 := n16772 _v _q h4481
  simp only [e7747, e7749, e7751, e7752, e7753, e7981] at *
  tauto
theorem n16774 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e225 _v) := by
  have p16653 := n16653 _v _q 
  have p16239 := n16239 _v _q h6792
  simp only [e225, e227, e230, e231, e5231, e5232, e5253] at *
  tauto
theorem n16775 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e191 _v) := by
  have p16442 := n16442 _v _q 
  have p16240 := n16240 _v _q h6792
  simp only [e191, e192, e193, e194, e5193, e5194, e5203] at *
  tauto
theorem n16776 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e4546 _v) := by
  have p16307 := n16307 _v _q 
  have p16243 := n16243 _v _q h6792
  simp only [e4544, e4545, e4546, e4547, e8029, e8030, e8035] at *
  tauto
theorem n16777 (_v : Vars) (_q : Query _v)  : (e4585 _v) := by
  by_contra hc
  change ¬ ((e3851 _v) ∨ (¬ (e3855 _v))) at hc
  have h3852 : (e3852 _v) := by
    change (¬ (e3851 _v))
    tauto
  have h3855 : (e3855 _v) := by
    tauto
  have p16251 := n16251 _v _q h3852 h3855
  exact p16251
theorem n16778 (_v : Vars) (_q : Query _v)  : (e3855 _v) := by
  by_contra hc
  change ¬ (e3855 _v) at hc
  have h3860 : (e3860 _v) := by
    change (¬ (e3855 _v))
    tauto
  have p16185 := n16185 _v _q h3860
  exact p16185
theorem n16779 (_v : Vars) (_q : Query _v)  : (e3851 _v) := by
  have p16777 := n16777 _v _q 
  have p16778 := n16778 _v _q 
  simp only [e3851, e3855, e3860, e4585] at *
  tauto
theorem n16780 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e4838 _v) := by
  have p16285 := n16285 _v _q 
  have p16262 := n16262 _v _q h6792
  simp only [e4836, e4837, e4838, e4839, e8301, e8302, e8307] at *
  tauto
theorem n16781 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e4855 _v) := by
  have p16317 := n16317 _v _q 
  have p16264 := n16264 _v _q h6792
  simp only [e4855, e4856, e4857, e4858, e8324, e8325, e8330] at *
  tauto
theorem n16782 (_v : Vars) (_q : Query _v) (h6792 : (e6792 _v)) : (e4924 _v) := by
  have p16462 := n16462 _v _q 
  have p16268 := n16268 _v _q h6792
  simp only [e4922, e4923, e4924, e4925, e8384, e8385, e8390] at *
  tauto
theorem n16784 (_v : Vars) (_q : Query _v)  : (e16783 _v) := by
  by_contra hc
  change ¬ ((e4459 _v) ∨ (¬ (e7749 _v))) at hc
  have h4464 : (e4464 _v) := by
    change (¬ (e4459 _v))
    tauto
  have h7749 : (e7749 _v) := by
    tauto
  have p16270 := n16270 _v _q h4464 h7749
  exact p16270
theorem n16785 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e225 _v) := by
  have p16653 := n16653 _v _q 
  have p16272 := n16272 _v _q h6591
  simp only [e225, e227, e230, e231, e5231, e5232, e5253] at *
  tauto
theorem n16786 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e4181 _v) := by
  have p16453 := n16453 _v _q 
  have p16289 := n16289 _v _q h6591
  simp only [e4181, e4182, e4183, e4184, e7677, e7678, e7683] at *
  tauto
theorem n16787 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e4419 _v) := by
  have p16347 := n16347 _v _q 
  have p16306 := n16306 _v _q h6591
  simp only [e4417, e4418, e4419, e4420, e7921, e7922, e7927] at *
  tauto
theorem n16788 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e191 _v) := by
  have p16442 := n16442 _v _q 
  have p16315 := n16315 _v _q h6591
  simp only [e191, e192, e193, e194, e5193, e5194, e5203] at *
  tauto
theorem n16789 (_v : Vars) (_q : Query _v) (h6591 : (e6591 _v)) : (e4220 _v) := by
  have p16334 := n16334 _v _q 
  have p16321 := n16321 _v _q h6591
  simp only [e4218, e4219, e4220, e4221, e7733, e7734, e7739] at *
  tauto
theorem n16790 (_v : Vars) (_q : Query _v) (h7655 : (e7655 _v)) : (e4139 _v) := by
  have p16281 := n16281 _v _q 
  have p16328 := n16328 _v _q h7655
  simp only [e4139, e4140, e4141, e4142, e7634, e7635, e7640] at *
  tauto
end
end Assembly
