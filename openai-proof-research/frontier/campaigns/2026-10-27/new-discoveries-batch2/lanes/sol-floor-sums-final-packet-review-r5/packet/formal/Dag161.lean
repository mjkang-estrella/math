import Dag160
import generated.th_lemma_14
import generated.th_lemma_15
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n16938 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) : (e4439 _v) := by
  have p14925 := n14925 _v _q 
  have p16937 := n16937 _v _q h2468
  simp only [e4439, e4440, e4444, e4445, e4446, e4447, e4941] at *
  tauto
theorem n16939 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) : (e1995 _v) := by
  have p11412 := n11412 _v _q 
  have p16860 := n16860 _v _q h2468
  simp only [e1995, e2061, e6454, e11411] at *
  tauto
theorem n16940 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) : (e4575 _v) := by
  have p14696 := n14696 _v _q 
  have p16939 := n16939 _v _q h2468
  simp only [e1995, e4567, e4568, e4572, e4573, e4574, e4575, e6423, e8066] at *
  tauto
theorem n16941 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) : (e4567 _v) := by
  have p8485 := n8485 _v _q 
  have p16940 := n16940 _v _q h2468
  simp only [e4567, e4568, e4572, e4573, e4574, e4575, e4956] at *
  tauto
theorem n16942 (_v : Vars) (_q : Query _v) (h4200 : (e4200 _v)) : (e7489 _v) := by
  have p16642 := n16642 _v _q h4200
  have p16863 := n16863 _v _q h4200
  have p16640 := n16640 _v _q h4200
  exact FloorCertificate.node_16942 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e2902 _v) p16642 p16863 p16640
theorem n16943 (_v : Vars) (_q : Query _v)  : (e4199 _v) := by
  by_contra hc
  change ¬ (e4199 _v) at hc
  have h4200 : (e4200 _v) := by
    change (¬ (e4199 _v))
    tauto
  have p16942 := n16942 _v _q h4200
  exact p16942
theorem n16944 (_v : Vars) (_q : Query _v) (h2787 : (e2787 _v)) (h8038 : (e8038 _v)) : (e4285 _v) := by
  have p16274 := n16274 _v _q 
  have p16866 := n16866 _v _q h2787 h8038
  simp only [e4283, e4284, e4285, e4286, e7798, e7799, e7804] at *
  tauto
theorem n16945 (_v : Vars) (_q : Query _v) (h5138 : (e5138 _v)) (h8320 : (e8320 _v)) : (e7489 _v) := by
  have p5255 := n5255 _v _q 
  have p11487 := n11487 _v _q h5138
  have p16868 := n16868 _v _q h8320
  have p11542 := n11542 _v _q h8320
  exact FloorCertificate.node_16945 (e2 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) (e4808 _v) p5255 p11487 p16868 p11542
theorem n16946 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h6454 : (e6454 _v)) : (e7597 _v) := by
  have p14525 := n14525 _v _q 
  have p16872 := n16872 _v _q h91 h6454
  simp only [e2733, e4096, e4097, e4098, e4099, e6750, e7589, e7597, e7600] at *
  tauto
theorem n16947 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h6454 : (e6454 _v)) : (e4096 _v) := by
  have p15703 := n15703 _v _q 
  have p16946 := n16946 _v _q h91 h6454
  simp only [e4096, e4097, e4098, e4099, e7589, e7590, e7597] at *
  tauto
theorem n16948 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h6454 : (e6454 _v)) : (e6776 _v) := by
  have p8424 := n8424 _v _q 
  have p16872 := n16872 _v _q h91 h6454
  simp only [e2733, e2781, e6750, e6776, e8423] at *
  tauto
theorem n16949 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h6454 : (e6454 _v)) : (e7789 _v) := by
  have p14570 := n14570 _v _q 
  have p16948 := n16948 _v _q h91 h6454
  simp only [e2781, e4258, e4259, e4260, e4261, e6776, e7781, e7789, e7792] at *
  tauto
theorem n16950 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h6454 : (e6454 _v)) : (e4260 _v) := by
  have p15824 := n15824 _v _q 
  have p16949 := n16949 _v _q h91 h6454
  simp only [e4258, e4259, e4260, e4261, e7781, e7782, e7789] at *
  tauto
theorem n16951 (_v : Vars) (_q : Query _v) (h7807 : (e7807 _v)) (h8038 : (e8038 _v)) : (e6772 _v) := by
  have p14855 := n14855 _v _q 
  have p16881 := n16881 _v _q h7807 h8038
  simp only [e2787, e4417, e4418, e4419, e4420, e6772, e7921, e7927, e7930] at *
  tauto
theorem n16952 (_v : Vars) (_q : Query _v) (h7807 : (e7807 _v)) (h8038 : (e8038 _v)) : (e7945 _v) := by
  have p15228 := n15228 _v _q 
  have p16951 := n16951 _v _q h7807 h8038
  simp only [e2787, e6772, e7932, e7935, e7942, e7943, e7944, e7945, e11111] at *
  tauto
theorem n16953 (_v : Vars) (_q : Query _v) (h7807 : (e7807 _v)) (h8038 : (e8038 _v)) : (e7935 _v) := by
  have p15266 := n15266 _v _q 
  have p16952 := n16952 _v _q h7807 h8038
  simp only [e7932, e7935, e7942, e7943, e7944, e7945, e8489] at *
  tauto
theorem n16954 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) (h5195 : (e5195 _v)) : (e2733 _v) := by
  have p8424 := n8424 _v _q 
  have p16884 := n16884 _v _q h2468 h5195
  simp only [e2733, e2781, e6776, e8423] at *
  tauto
theorem n16955 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) (h5195 : (e5195 _v)) : (e4109 _v) := by
  have p14689 := n14689 _v _q 
  have p16954 := n16954 _v _q h2468 h5195
  simp only [e2733, e4101, e4102, e4106, e4107, e4108, e4109, e6750, e7603] at *
  tauto
theorem n16956 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) (h5195 : (e5195 _v)) : (e4101 _v) := by
  have p14929 := n14929 _v _q 
  have p16955 := n16955 _v _q h2468 h5195
  simp only [e4101, e4102, e4106, e4107, e4108, e4109, e4952] at *
  tauto
theorem n16957 (_v : Vars) (_q : Query _v) (h3158 : (e3158 _v)) (h5195 : (e5195 _v)) : (e2733 _v) := by
  have p8424 := n8424 _v _q 
  have p16886 := n16886 _v _q h3158 h5195
  simp only [e2733, e2781, e6776, e8423] at *
  tauto
theorem n16958 (_v : Vars) (_q : Query _v) (h3158 : (e3158 _v)) (h5195 : (e5195 _v)) : (e4109 _v) := by
  have p14689 := n14689 _v _q 
  have p16957 := n16957 _v _q h3158 h5195
  simp only [e2733, e4101, e4102, e4106, e4107, e4108, e4109, e6750, e7603] at *
  tauto
theorem n16959 (_v : Vars) (_q : Query _v) (h3158 : (e3158 _v)) (h5195 : (e5195 _v)) : (e4101 _v) := by
  have p14929 := n14929 _v _q 
  have p16958 := n16958 _v _q h3158 h5195
  simp only [e4101, e4102, e4106, e4107, e4108, e4109, e4952] at *
  tauto
theorem n16960 (_v : Vars) (_q : Query _v) (h3158 : (e3158 _v)) (h5195 : (e5195 _v)) : (e4271 _v) := by
  have p14699 := n14699 _v _q 
  have p16886 := n16886 _v _q h3158 h5195
  simp only [e2781, e4263, e4264, e4268, e4269, e4270, e4271, e6776, e7795] at *
  tauto
theorem n16961 (_v : Vars) (_q : Query _v) (h3158 : (e3158 _v)) (h5195 : (e5195 _v)) : (e4264 _v) := by
  have p14966 := n14966 _v _q 
  have p16960 := n16960 _v _q h3158 h5195
  simp only [e4263, e4264, e4268, e4269, e4270, e4271, e4959] at *
  tauto
theorem n16962 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) (h5195 : (e5195 _v)) : (e4271 _v) := by
  have p14699 := n14699 _v _q 
  have p16884 := n16884 _v _q h2468 h5195
  simp only [e2781, e4263, e4264, e4268, e4269, e4270, e4271, e6776, e7795] at *
  tauto
theorem n16963 (_v : Vars) (_q : Query _v) (h2468 : (e2468 _v)) (h5195 : (e5195 _v)) : (e4264 _v) := by
  have p14966 := n14966 _v _q 
  have p16962 := n16962 _v _q h2468 h5195
  simp only [e4263, e4264, e4268, e4269, e4270, e4271, e4959] at *
  tauto
theorem n16964 (_v : Vars) (_q : Query _v) (h7807 : (e7807 _v)) (h8038 : (e8038 _v)) : (e6772 _v) := by
  have p14855 := n14855 _v _q 
  have p16888 := n16888 _v _q h7807 h8038
  simp only [e2787, e4417, e4418, e4419, e4420, e6772, e7921, e7927, e7930] at *
  tauto
theorem n16965 (_v : Vars) (_q : Query _v) (h7807 : (e7807 _v)) (h8038 : (e8038 _v)) : (e7945 _v) := by
  have p15228 := n15228 _v _q 
  have p16964 := n16964 _v _q h7807 h8038
  simp only [e2787, e6772, e7932, e7935, e7942, e7943, e7944, e7945, e11111] at *
  tauto
theorem n16966 (_v : Vars) (_q : Query _v) (h7807 : (e7807 _v)) (h8038 : (e8038 _v)) : (e7935 _v) := by
  have p15266 := n15266 _v _q 
  have p16965 := n16965 _v _q h7807 h8038
  simp only [e7932, e7935, e7942, e7943, e7944, e7945, e8489] at *
  tauto
theorem n16967 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h5108 : (e5108 _v)) : (e2691 _v) := by
  have p15196 := n15196 _v _q 
  have p16891 := n16891 _v _q h51 h5108
  simp only [e2691, e7493, e7494, e7495, e7496, e7497, e7517, e10904] at *
  tauto
theorem n16968 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h5108 : (e5108 _v)) : (e7504 _v) := by
  have p14811 := n14811 _v _q 
  have p16967 := n16967 _v _q h51 h5108
  simp only [e2691, e4026, e4028, e4031, e4032, e6724, e7503, e7504, e7507] at *
  tauto
theorem n16970 (_v : Vars) (_q : Query _v)  : (e16969 _v) := by
  simp only [e5, e6, e5770, e5771, e5772, e5773, e5774, e5915, e5916, e5917, e5918, e5919, e5989, e5990, e5991, e5992, e5993, e6027, e6028, e6029, e6030, e6031, e8865, e8898, e8899, e8900, e8901, e8902, e8932, e8933, e8934, e8935, e8936, e8948, e8981, e8982, e8983, e8984, e8985, e8997, e9012, e9056, e9057, e9058, e9059, e9060, e9072, e9087, e9113, e9159, e9160, e11808, e16969] at *
  omega
theorem n16972 (_v : Vars) (_q : Query _v)  : (e16971 _v) := by
  have p16909 := n16909 _v _q 
  have p16970 := n16970 _v _q 
  exact (Eq.trans p16909 p16970)
theorem n16973 (_v : Vars) (_q : Query _v)  : (e13391 _v) := by
  have p16972 := n16972 _v _q 
  have p1573 := n1573 _v _q 
  change ((e11660 _v) = (e9160 _v)) at p16972
  change ((e1571 _v) = (e1571 _v)) at p1573
  simp only [e13391, e13061, e11809, p16972]
theorem n16974 (_v : Vars) (_q : Query _v) (h4481 : (e4481 _v)) : (e7489 _v) := by
  have p8139 := n8139 _v _q 
  have p11482 := n11482 _v _q 
  have p16229 := n16229 _v _q h4481
  have p16915 := n16915 _v _q h4481
  exact FloorCertificate.node_16974 (e2 _v) (e7 _v) (e17 _v) (e110 _v) p8139 p11482 p16229 p16915
theorem n16976 (_v : Vars) (_q : Query _v)  : (e16975 _v) := by
  by_contra hc
  change ¬ ((e7606 _v) ∨ (¬ (e4128 _v))) at hc
  have h4128 : (e4128 _v) := by
    tauto
  have h7607 : (e7607 _v) := by
    change (¬ (e7606 _v))
    tauto
  have p15154 := n15154 _v _q h4128 h7607
  exact p15154
theorem n16977 (_v : Vars) (_q : Query _v)  : (e7606 _v) := by
  have p16976 := n16976 _v _q 
  have p16913 := n16913 _v _q 
  simp only [e4128, e4133, e7606, e16975] at *
  tauto
theorem n16978 (_v : Vars) (_q : Query _v) (h7608 : (e7608 _v)) : (e7608 _v) := by
  exact h7608
theorem n16979 (_v : Vars) (_q : Query _v) (h2799 : (e2799 _v)) (h7608 : (e7608 _v)) : (e7489 _v) := by
  have p16913 := n16913 _v _q 
  have p11376 := n11376 _v _q 
  have p8511 := n8511 _v _q h2799
  have p16978 := n16978 _v _q h7608
  exact FloorCertificate.node_16979 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) (e2907 _v) p16913 p11376 p8511 p16978
theorem n16981 (_v : Vars) (_q : Query _v)  : (e16980 _v) := by
  by_contra hc
  change ¬ ((¬ (e2799 _v)) ∨ (¬ (e7608 _v))) at hc
  have h2799 : (e2799 _v) := by
    tauto
  have h7608 : (e7608 _v) := by
    tauto
  have p16979 := n16979 _v _q h2799 h7608
  exact p16979
theorem n16982 (_v : Vars) (_q : Query _v) (h4419 : (e4419 _v)) (h4649 : (e4649 _v)) (h8038 : (e8038 _v)) : (e1995 _v) := by
  have p15526 := n15526 _v _q h8038
  have p16921 := n16921 _v _q h4649
  have p15374 := n15374 _v _q h4649
  have p16833 := n16833 _v _q h4419 h8038
  exact FloorCertificate.node_16982 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e110 _v) (e2879 _v) (e2951 _v) p15526 p16921 p15374 p16833
theorem n16983 (_v : Vars) (_q : Query _v) (h4419 : (e4419 _v)) (h4562 : (e4562 _v)) (h4649 : (e4649 _v)) (h8038 : (e8038 _v)) : (e7489 _v) := by
  have p14696 := n14696 _v _q 
  have p16923 := n16923 _v _q h4419 h4562 h4649 h8038
  have p16982 := n16982 _v _q h4419 h4649 h8038
  simp only [e1995, e4567, e4568, e4572, e4573, e4574, e4575, e6423, e8066] at *
  tauto
theorem n16984 (_v : Vars) (_q : Query _v) (h4302 : (e4302 _v)) (h4419 : (e4419 _v)) (h7807 : (e7807 _v)) : (e2061 _v) := by
  have p16834 := n16834 _v _q h4419 h7807
  have p15582 := n15582 _v _q h7807
  have p16517 := n16517 _v _q h4302
  have p15577 := n15577 _v _q h4302
  exact FloorCertificate.node_16984 (e2 _v) (e7 _v) (e17 _v) (e45 _v) (e110 _v) (e2898 _v) (e2970 _v) p16834 p15582 p16517 p15577
theorem n16985 (_v : Vars) (_q : Query _v) (h4302 : (e4302 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h7807 : (e7807 _v)) : (e7489 _v) := by
  have p14688 := n14688 _v _q 
  have p16933 := n16933 _v _q h4302 h4419 h4434 h7807
  have p16984 := n16984 _v _q h4302 h4419 h7807
  simp only [e2061, e4439, e4440, e4444, e4445, e4446, e4447, e6454, e7961] at *
  tauto
theorem n16986 (_v : Vars) (_q : Query _v)  : (e8519 _v) := by
  by_contra hc
  change ¬ ((e2303 _v) ∨ (e4301 _v) ∨ (¬ (e4434 _v)) ∨ (¬ (e4419 _v))) at hc
  have h4302 : (e4302 _v) := by
    change (¬ (e4301 _v))
    tauto
  have h4419 : (e4419 _v) := by
    tauto
  have h4434 : (e4434 _v) := by
    tauto
  have h7807 : (e7807 _v) := by
    change (¬ (e2303 _v))
    tauto
  have p16985 := n16985 _v _q h4302 h4419 h4434 h7807
  exact p16985
end
end Assembly
