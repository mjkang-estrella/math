import Dag138
import generated.th_lemma_11
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n15913 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) : (e4314 _v) := by
  have p14704 := n14704 _v _q 
  have p15912 := n15912 _v _q h2351
  simp only [e2585, e4306, e4307, e4311, e4312, e4313, e4314, e6676, e7836] at *
  tauto
theorem n15914 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) : (e4306 _v) := by
  have p14984 := n14984 _v _q 
  have p15913 := n15913 _v _q h2351
  simp only [e4306, e4307, e4311, e4312, e4313, e4314, e4964] at *
  tauto
theorem n15915 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) : (e48 _v) := by
  have p11369 := n11369 _v _q 
  have p11533 := n11533 _v _q h2351
  simp only [e48, e2733, e6750, e11368] at *
  tauto
theorem n15916 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) : (e60 _v) := by
  have p14152 := n14152 _v _q 
  have p15915 := n15915 _v _q h2351
  simp only [e48, e51, e52, e57, e58, e59, e60, e5108, e5125] at *
  tauto
theorem n15917 (_v : Vars) (_q : Query _v) (h2351 : (e2351 _v)) : (e51 _v) := by
  have p14962 := n14962 _v _q 
  have p15916 := n15916 _v _q h2351
  simp only [e51, e52, e57, e58, e59, e60, e77] at *
  tauto
theorem n15918 (_v : Vars) (_q : Query _v) (h6600 : (e6600 _v)) : (e6630 _v) := by
  have p8442 := n8442 _v _q 
  have p8439 := n8439 _v _q h6600
  simp only [e2402, e2468, e6600, e6630, e8441] at *
  tauto
theorem n15919 (_v : Vars) (_q : Query _v) (h6600 : (e6600 _v)) : (e8275 _v) := by
  have p14655 := n14655 _v _q 
  have p15918 := n15918 _v _q h6600
  simp only [e2468, e4785, e4786, e4787, e4788, e6630, e8267, e8275, e8278] at *
  tauto
theorem n15920 (_v : Vars) (_q : Query _v) (h5223 : (e5223 _v)) : (e8322 _v) := by
  have p15218 := n15218 _v _q 
  have p12924 := n12924 _v _q h5223
  simp only [e2529, e8310, e8315, e8317, e8319, e8320, e8321, e8322, e11298] at *
  tauto
theorem n15921 (_v : Vars) (_q : Query _v) (h5223 : (e5223 _v)) : (e8317 _v) := by
  have p11541 := n11541 _v _q 
  have p15920 := n15920 _v _q h5223
  simp only [e8315, e8317, e8319, e8320, e8321, e8322, e8491] at *
  tauto
theorem n15922 (_v : Vars) (_q : Query _v) (h5223 : (e5223 _v)) : (e8038 _v) := by
  have p11493 := n11493 _v _q 
  have p12924 := n12924 _v _q h5223
  simp only [e2475, e2529, e8038, e8310, e11492] at *
  tauto
theorem n15923 (_v : Vars) (_q : Query _v) (h5223 : (e5223 _v)) : (e8050 _v) := by
  have p15207 := n15207 _v _q 
  have p15922 := n15922 _v _q h5223
  simp only [e2475, e8038, e8043, e8045, e8047, e8048, e8049, e8050, e11165] at *
  tauto
theorem n15924 (_v : Vars) (_q : Query _v) (h5223 : (e5223 _v)) : (e8045 _v) := by
  have p15206 := n15206 _v _q 
  have p15923 := n15923 _v _q h5223
  simp only [e8043, e8045, e8047, e8048, e8049, e8050, e8490] at *
  tauto
theorem n15925 (_v : Vars) (_q : Query _v)  : (e5152 _v) := by
  simp only [e5143, e5145, e5147, e5148, e5149, e5152] at *
  tauto
theorem n15926 (_v : Vars) (_q : Query _v) (h5138 : (e5138 _v)) : (e5150 _v) := by
  have p15115 := n15115 _v _q 
  have p11487 := n11487 _v _q h5138
  simp only [e79, e5138, e5143, e5145, e5147, e5148, e5149, e5150, e8647] at *
  tauto
theorem n15927 (_v : Vars) (_q : Query _v) (h5138 : (e5138 _v)) : (e5145 _v) := by
  have p15925 := n15925 _v _q 
  have p15926 := n15926 _v _q h5138
  simp only [e5143, e5145, e5147, e5148, e5149, e5150, e5152] at *
  tauto
theorem n15928 (_v : Vars) (_q : Query _v) (h5138 : (e5138 _v)) : (e8310 _v) := by
  have p5255 := n5255 _v _q 
  have p11487 := n11487 _v _q h5138
  exact FloorCertificate.node_15928 (e2 _v) (e9 _v) (e45 _v) (e110 _v) p5255 p11487
theorem n15929 (_v : Vars) (_q : Query _v) (h5138 : (e5138 _v)) : (e8322 _v) := by
  have p15218 := n15218 _v _q 
  have p15928 := n15928 _v _q h5138
  simp only [e2529, e8310, e8315, e8317, e8319, e8320, e8321, e8322, e11298] at *
  tauto
theorem n15930 (_v : Vars) (_q : Query _v) (h2522 : (e2522 _v)) : (e2468 _v) := by
  have p12831 := n12831 _v _q h2522
  have p5257 := n5257 _v _q 
  exact FloorCertificate.node_15930 (e2 _v) (e7 _v) (e17 _v) (e45 _v) (e110 _v) p12831 p5257
theorem n15931 (_v : Vars) (_q : Query _v) (h2522 : (e2522 _v)) : (e4798 _v) := by
  have p14690 := n14690 _v _q 
  have p15930 := n15930 _v _q h2522
  simp only [e2468, e4790, e4791, e4795, e4796, e4797, e4798, e6630, e8281] at *
  tauto
theorem n15932 (_v : Vars) (_q : Query _v) (h2522 : (e2522 _v)) : (e4791 _v) := by
  have p14932 := n14932 _v _q 
  have p15931 := n15931 _v _q h2522
  simp only [e4790, e4791, e4795, e4796, e4797, e4798, e4953] at *
  tauto
theorem n15933 (_v : Vars) (_q : Query _v) (h6630 : (e6630 _v)) : (e8275 _v) := by
  have p14655 := n14655 _v _q 
  have p8434 := n8434 _v _q h6630
  simp only [e2468, e4785, e4786, e4787, e4788, e6630, e8267, e8275, e8278] at *
  tauto
theorem n15934 (_v : Vars) (_q : Query _v) (h6630 : (e6630 _v)) : (e4787 _v) := by
  have p15670 := n15670 _v _q 
  have p15933 := n15933 _v _q h6630
  simp only [e4785, e4786, e4787, e4788, e8267, e8268, e8275] at *
  tauto
theorem n15935 (_v : Vars) (_q : Query _v) (h5195 : (e5195 _v)) : (e8322 _v) := by
  have p15218 := n15218 _v _q 
  have p12925 := n12925 _v _q h5195
  simp only [e2529, e8310, e8315, e8317, e8319, e8320, e8321, e8322, e11298] at *
  tauto
theorem n15936 (_v : Vars) (_q : Query _v) (h5138 : (e5138 _v)) : (e8050 _v) := by
  have p15207 := n15207 _v _q 
  have p12954 := n12954 _v _q h5138
  simp only [e2475, e8038, e8043, e8045, e8047, e8048, e8049, e8050, e11165] at *
  tauto
theorem n15937 (_v : Vars) (_q : Query _v) (h5195 : (e5195 _v)) : (e8050 _v) := by
  have p15207 := n15207 _v _q 
  have p12926 := n12926 _v _q h5195
  simp only [e2475, e8038, e8043, e8045, e8047, e8048, e8049, e8050, e11165] at *
  tauto
theorem n15938 (_v : Vars) (_q : Query _v) (h5195 : (e5195 _v)) : (e8045 _v) := by
  have p15206 := n15206 _v _q 
  have p15937 := n15937 _v _q h5195
  simp only [e8043, e8045, e8047, e8048, e8049, e8050, e8490] at *
  tauto
theorem n15939 (_v : Vars) (_q : Query _v) (h6750 : (e6750 _v)) : (e7597 _v) := by
  have p14525 := n14525 _v _q 
  have p8420 := n8420 _v _q h6750
  simp only [e2733, e4096, e4097, e4098, e4099, e6750, e7589, e7597, e7600] at *
  tauto
theorem n15940 (_v : Vars) (_q : Query _v) (h6750 : (e6750 _v)) : (e4096 _v) := by
  have p15703 := n15703 _v _q 
  have p15939 := n15939 _v _q h6750
  simp only [e4096, e4097, e4098, e4099, e7589, e7590, e7597] at *
  tauto
theorem n15941 (_v : Vars) (_q : Query _v) (h2402 : (e2402 _v)) (h6750 : (e6750 _v)) (h6772 : (e6772 _v)) : (e8050 _v) := by
  have p15207 := n15207 _v _q 
  have p11535 := n11535 _v _q h2402 h6750 h6772
  simp only [e2475, e8038, e8043, e8045, e8047, e8048, e8049, e8050, e11165] at *
  tauto
theorem n15942 (_v : Vars) (_q : Query _v) (h2402 : (e2402 _v)) (h6750 : (e6750 _v)) (h6772 : (e6772 _v)) : (e8045 _v) := by
  have p15206 := n15206 _v _q 
  have p15941 := n15941 _v _q h2402 h6750 h6772
  simp only [e8043, e8045, e8047, e8048, e8049, e8050, e8490] at *
  tauto
theorem n15943 (_v : Vars) (_q : Query _v) (h6772 : (e6772 _v)) : (e7945 _v) := by
  have p15228 := n15228 _v _q 
  have p8458 := n8458 _v _q h6772
  simp only [e2787, e6772, e7932, e7935, e7942, e7943, e7944, e7945, e11111] at *
  tauto
theorem n15944 (_v : Vars) (_q : Query _v) (h6772 : (e6772 _v)) : (e7935 _v) := by
  have p15266 := n15266 _v _q 
  have p15943 := n15943 _v _q h6772
  simp only [e7932, e7935, e7942, e7943, e7944, e7945, e8489] at *
  tauto
theorem n15945 (_v : Vars) (_q : Query _v) (h2242 : (e2242 _v)) : (e4575 _v) := by
  have p14696 := n14696 _v _q 
  have p12929 := n12929 _v _q h2242
  simp only [e1995, e4567, e4568, e4572, e4573, e4574, e4575, e6423, e8066] at *
  tauto
theorem n15946 (_v : Vars) (_q : Query _v) (h2242 : (e2242 _v)) : (e4567 _v) := by
  have p8485 := n8485 _v _q 
  have p15945 := n15945 _v _q h2242
  simp only [e4567, e4568, e4572, e4573, e4574, e4575, e4956] at *
  tauto
theorem n15947 (_v : Vars) (_q : Query _v) (h2242 : (e2242 _v)) : (e2179 _v) := by
  have p8557 := n8557 _v _q 
  have p8553 := n8553 _v _q h2242
  simp only [e2179, e2242, e6525, e8556] at *
  tauto
theorem n15948 (_v : Vars) (_q : Query _v) (h2242 : (e2242 _v)) : (e4616 _v) := by
  have p14684 := n14684 _v _q 
  have p15947 := n15947 _v _q h2242
  simp only [e2179, e3158, e3159, e3160, e3161, e3162, e4616, e6501, e8109] at *
  tauto
theorem n15949 (_v : Vars) (_q : Query _v) (h2242 : (e2242 _v)) : (e3158 _v) := by
  have p15126 := n15126 _v _q 
  have p15948 := n15948 _v _q h2242
  simp only [e3158, e3159, e3160, e3161, e3162, e3163, e4616] at *
  tauto
theorem n15950 (_v : Vars) (_q : Query _v) (h2242 : (e2242 _v)) : (e4447 _v) := by
  have p14688 := n14688 _v _q 
  have p12928 := n12928 _v _q h2242
  simp only [e2061, e4439, e4440, e4444, e4445, e4446, e4447, e6454, e7961] at *
  tauto
theorem n15951 (_v : Vars) (_q : Query _v) (h2242 : (e2242 _v)) : (e4466 _v) := by
  have p14604 := n14604 _v _q 
  have p12927 := n12927 _v _q h2242
  simp only [e2125, e4458, e4459, e4463, e4464, e4465, e4466, e6480, e7977] at *
  tauto
theorem n15952 (_v : Vars) (_q : Query _v) (h2242 : (e2242 _v)) : (e4459 _v) := by
  have p8443 := n8443 _v _q 
  have p15951 := n15951 _v _q h2242
  simp only [e4458, e4459, e4463, e4464, e4465, e4466, e4482] at *
  tauto
theorem n15953 (_v : Vars) (_q : Query _v) (h2475 : (e2475 _v)) (h6772 : (e6772 _v)) : (e7807 _v) := by
  have p8461 := n8461 _v _q 
  have p8458 := n8458 _v _q h6772
  have p8457 := n8457 _v _q h2475
  simp only [e2303, e2475, e2787, e6772, e7807, e8038, e8460] at *
  tauto
theorem n15954 (_v : Vars) (_q : Query _v) (h2475 : (e2475 _v)) (h6772 : (e6772 _v)) : (e7819 _v) := by
  have p14994 := n14994 _v _q 
  have p15953 := n15953 _v _q h2475 h6772
  simp only [e2303, e7807, e7812, e7814, e7816, e7817, e7818, e7819, e11046] at *
  tauto
theorem n15955 (_v : Vars) (_q : Query _v) (h6776 : (e6776 _v)) : (e7789 _v) := by
  have p14570 := n14570 _v _q 
  have p8601 := n8601 _v _q h6776
  simp only [e2781, e4258, e4259, e4260, e4261, e6776, e7781, e7789, e7792] at *
  tauto
theorem n15956 (_v : Vars) (_q : Query _v) (h6776 : (e6776 _v)) : (e4260 _v) := by
  have p15824 := n15824 _v _q 
  have p15955 := n15955 _v _q h6776
  simp only [e4258, e4259, e4260, e4261, e7781, e7782, e7789] at *
  tauto
theorem n15957 (_v : Vars) (_q : Query _v) (h2179 : (e2179 _v)) : (e2179 _v) := by
  exact h2179
end
end Assembly
