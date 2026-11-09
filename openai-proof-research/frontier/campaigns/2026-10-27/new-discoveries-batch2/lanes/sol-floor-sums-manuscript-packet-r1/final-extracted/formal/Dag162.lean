import Dag161
import generated.th_lemma_15
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n16987 (_v : Vars) (_q : Query _v)  : (e8518 _v) := by
  by_contra hc
  change ¬ ((¬ (e8338 _v)) ∨ (¬ (e2475 _v)) ∨ (¬ (e4434 _v)) ∨ (e4301 _v)) at hc
  have h2475 : (e2475 _v) := by
    tauto
  have h4302 : (e4302 _v) := by
    change (¬ (e4301 _v))
    tauto
  have h4434 : (e4434 _v) := by
    tauto
  have h8338 : (e8338 _v) := by
    tauto
  have p16931 := n16931 _v _q h2475 h4302 h4434 h8338
  exact p16931
theorem n16988 (_v : Vars) (_q : Query _v) (h4302 : (e4302 _v)) (h4434 : (e4434 _v)) : (e8038 _v) := by
  have p16987 := n16987 _v _q 
  have p16840 := n16840 _v _q h4302
  have p4987 := n4987 _v _q h4434
  have p15577 := n15577 _v _q h4302
  simp only [e2475, e4301, e4302, e4434, e4435, e8038, e8338, e8346, e8518] at *
  tauto
theorem n16989 (_v : Vars) (_q : Query _v) (h230 : (e230 _v)) : (e230 _v) := by
  exact h230
theorem n16990 (_v : Vars) (_q : Query _v) (h230 : (e230 _v)) : (e5231 _v) := by
  have p16653 := n16653 _v _q 
  have p16989 := n16989 _v _q h230
  simp only [e225, e227, e230, e231, e5231, e5253] at *
  tauto
theorem n16991 (_v : Vars) (_q : Query _v) (h230 : (e230 _v)) : (e5223 _v) := by
  have p14731 := n14731 _v _q 
  have p16990 := n16990 _v _q h230
  simp only [e214, e225, e227, e230, e231, e5223, e5231, e5232, e5235] at *
  tauto
theorem n16992 (_v : Vars) (_q : Query _v)  : (e5237 _v) := by
  by_contra hc
  change ¬ (e5237 _v) at hc
  have h5247 : (e5247 _v) := by
    change (¬ (e5237 _v))
    tauto
  have p16895 := n16895 _v _q h5247
  exact p16895
theorem n16993 (_v : Vars) (_q : Query _v) (h230 : (e230 _v)) : (e7489 _v) := by
  have p16991 := n16991 _v _q h230
  have p16989 := n16989 _v _q h230
  have p16992 := n16992 _v _q 
  exact FloorCertificate.node_16993 (e2 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) (e211 _v) p16991 p16989 p16992
theorem n16994 (_v : Vars) (_q : Query _v)  : (e8335 _v) := by
  by_contra hc
  change ¬ (e8335 _v) at hc
  have h8345 : (e8345 _v) := by
    change (¬ (e8335 _v))
    tauto
  have p16917 := n16917 _v _q h8345
  exact p16917
theorem n16995 (_v : Vars) (_q : Query _v)  : (e5041 _v) := by
  simp only [e4306, e4307, e4311, e4312, e4313, e5041] at *
  tauto
theorem n16996 (_v : Vars) (_q : Query _v) (h5195 : (e5195 _v)) : (e4307 _v) := by
  have p16995 := n16995 _v _q 
  have p15991 := n15991 _v _q h5195
  simp only [e4306, e4307, e4311, e4312, e4313, e4314, e5041] at *
  tauto
theorem n16997 (_v : Vars) (_q : Query _v) (h5195 : (e5195 _v)) : (e4302 _v) := by
  have p8663 := n8663 _v _q 
  have p16994 := n16994 _v _q 
  have p8549 := n8549 _v _q h5195
  have p16996 := n16996 _v _q h5195
  exact FloorCertificate.node_16997 (e2 _v) (e7 _v) (e17 _v) (e45 _v) (e110 _v) (e2898 _v) (e2970 _v) p8663 p16994 p8549 p16996
theorem n16998 (_v : Vars) (_q : Query _v) (h5195 : (e5195 _v)) : (e8338 _v) := by
  have p15580 := n15580 _v _q 
  have p15993 := n15993 _v _q h5195
  simp only [e8335, e8338, e8345, e8346, e8347, e8348, e8517] at *
  tauto
theorem n16999 (_v : Vars) (_q : Query _v) (h4434 : (e4434 _v)) (h5195 : (e5195 _v)) : (e8038 _v) := by
  have p16987 := n16987 _v _q 
  have p16997 := n16997 _v _q h5195
  have p4987 := n4987 _v _q h4434
  have p16998 := n16998 _v _q h5195
  simp only [e2475, e4301, e4302, e4434, e4435, e8038, e8338, e8346, e8518] at *
  tauto
theorem n17001 (_v : Vars) (_q : Query _v)  : (e17000 _v) := by
  by_contra hc
  change ¬ ((e8317 _v) ∨ (e79 _v)) at hc
  have h5138 : (e5138 _v) := by
    change (¬ (e79 _v))
    tauto
  have h8320 : (e8320 _v) := by
    change (¬ (e8317 _v))
    tauto
  have p16945 := n16945 _v _q h5138 h8320
  exact p16945
theorem n17002 (_v : Vars) (_q : Query _v) (h8320 : (e8320 _v)) : (e79 _v) := by
  have p17001 := n17001 _v _q 
  have p11542 := n11542 _v _q h8320
  simp only [e79, e8317, e8320, e17000] at *
  tauto
theorem n17003 (_v : Vars) (_q : Query _v)  : (e8609 _v) := by
  simp only [e4026, e4028, e4031, e4032, e7503, e8609] at *
  tauto
theorem n17004 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h5108 : (e5108 _v)) : (e4028 _v) := by
  have p17003 := n17003 _v _q 
  have p16968 := n16968 _v _q h51 h5108
  simp only [e4026, e4028, e4031, e4032, e7503, e7504, e8609] at *
  tauto
theorem n17005 (_v : Vars) (_q : Query _v) (h5138 : (e5138 _v)) : (e8317 _v) := by
  have p17001 := n17001 _v _q 
  have p11487 := n11487 _v _q h5138
  simp only [e79, e5138, e8317, e17000] at *
  tauto
theorem n17006 (_v : Vars) (_q : Query _v)  : (e11812 _v) := by
  simp only [e5, e6, e266, e781, e1571, e5770, e5771, e5772, e5773, e5915, e5916, e5917, e5918, e5989, e5990, e5991, e5992, e6027, e6028, e6029, e6030, e8898, e8899, e8900, e8901, e8932, e8933, e8934, e8935, e8981, e8982, e8983, e8984, e9056, e9057, e9058, e9059, e9160, e11809, e11810, e11811, e11812] at *
  omega
theorem n17007 (_v : Vars) (_q : Query _v)  : (e13392 _v) := by
  have p16973 := n16973 _v _q 
  have p17006 := n17006 _v _q 
  exact (Iff.trans p16973 p17006)
theorem n17008 (_v : Vars) (_q : Query _v)  : (e11811 _v) := by
  have p13062 := n13062 _v _q 
  have p17007 := n17007 _v _q 
  simp only [e11810, e11811, e13061, e13392] at *
  tauto
theorem n17009 (_v : Vars) (_q : Query _v)  : (e4477 _v) := by
  by_contra hc
  change ¬ (e4477 _v) at hc
  have h4481 : (e4481 _v) := by
    change (¬ (e4477 _v))
    tauto
  have p16974 := n16974 _v _q h4481
  exact p16974
theorem n17010 (_v : Vars) (_q : Query _v) (h4302 : (e4302 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) : (e2303 _v) := by
  have p16986 := n16986 _v _q 
  have p4971 := n4971 _v _q h4419
  have p4987 := n4987 _v _q h4434
  have p15577 := n15577 _v _q h4302
  simp only [e2303, e4301, e4302, e4419, e4420, e4434, e4435, e8519] at *
  tauto
theorem n17011 (_v : Vars) (_q : Query _v) (h4302 : (e4302 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) : (e2358 _v) := by
  have p8451 := n8451 _v _q 
  have p17010 := n17010 _v _q h4302 h4419 h4434
  simp only [e2303, e2358, e7807, e8450] at *
  tauto
theorem n17012 (_v : Vars) (_q : Query _v) (h4302 : (e4302 _v)) (h4434 : (e4434 _v)) : (e8050 _v) := by
  have p15207 := n15207 _v _q 
  have p16988 := n16988 _v _q h4302 h4434
  simp only [e2475, e8038, e8043, e8045, e8047, e8048, e8049, e8050, e11165] at *
  tauto
theorem n17013 (_v : Vars) (_q : Query _v) (h4302 : (e4302 _v)) (h4434 : (e4434 _v)) : (e8045 _v) := by
  have p15206 := n15206 _v _q 
  have p17012 := n17012 _v _q h4302 h4434
  simp only [e8043, e8045, e8047, e8048, e8049, e8050, e8490] at *
  tauto
theorem n17014 (_v : Vars) (_q : Query _v) (h4302 : (e4302 _v)) (h4434 : (e4434 _v)) : (e6724 _v) := by
  have p14112 := n14112 _v _q 
  have p16988 := n16988 _v _q h4302 h4434
  simp only [e2475, e2691, e6724, e8038, e14111] at *
  tauto
theorem n17015 (_v : Vars) (_q : Query _v) (h4302 : (e4302 _v)) (h4434 : (e4434 _v)) : (e5093 _v) := by
  have p11399 := n11399 _v _q 
  have p16988 := n16988 _v _q h4302 h4434
  simp only [e13, e2475, e5093, e8038, e11398] at *
  tauto
theorem n17016 (_v : Vars) (_q : Query _v) (h4302 : (e4302 _v)) (h4434 : (e4434 _v)) : (e5105 _v) := by
  have p15204 := n15204 _v _q 
  have p17015 := n17015 _v _q h4302 h4434
  simp only [e13, e5093, e5098, e5100, e5102, e5103, e5104, e5105, e8622] at *
  tauto
theorem n17017 (_v : Vars) (_q : Query _v) (h4302 : (e4302 _v)) (h4434 : (e4434 _v)) : (e5100 _v) := by
  have p15319 := n15319 _v _q 
  have p17016 := n17016 _v _q h4302 h4434
  simp only [e5098, e5100, e5102, e5103, e5104, e5105, e8479] at *
  tauto
theorem n17018 (_v : Vars) (_q : Query _v) (h4302 : (e4302 _v)) (h4434 : (e4434 _v)) : (e7742 _v) := by
  have p11479 := n11479 _v _q 
  have p17015 := n17015 _v _q h4302 h4434
  simp only [e13, e2132, e5093, e7742, e11478] at *
  tauto
theorem n17019 (_v : Vars) (_q : Query _v) (h4302 : (e4302 _v)) (h4434 : (e4434 _v)) : (e7754 _v) := by
  have p14942 := n14942 _v _q 
  have p17018 := n17018 _v _q h4302 h4434
  simp only [e2132, e7742, e7747, e7749, e7751, e7752, e7753, e7754, e11001] at *
  tauto
theorem n17020 (_v : Vars) (_q : Query _v)  : (e225 _v) := by
  by_contra hc
  change ¬ (e225 _v) at hc
  have h230 : (e230 _v) := by
    change (¬ (e225 _v))
    tauto
  have p16993 := n16993 _v _q h230
  exact p16993
theorem n17021 (_v : Vars) (_q : Query _v) (h4434 : (e4434 _v)) (h5195 : (e5195 _v)) : (e8050 _v) := by
  have p15207 := n15207 _v _q 
  have p16999 := n16999 _v _q h4434 h5195
  simp only [e2475, e8038, e8043, e8045, e8047, e8048, e8049, e8050, e11165] at *
  tauto
theorem n17022 (_v : Vars) (_q : Query _v) (h4434 : (e4434 _v)) (h5195 : (e5195 _v)) : (e8045 _v) := by
  have p15206 := n15206 _v _q 
  have p17021 := n17021 _v _q h4434 h5195
  simp only [e8043, e8045, e8047, e8048, e8049, e8050, e8490] at *
  tauto
theorem n17023 (_v : Vars) (_q : Query _v) (h8320 : (e8320 _v)) : (e5135 _v) := by
  have p14729 := n14729 _v _q 
  have p17002 := n17002 _v _q h8320
  simp only [e79, e89, e91, e94, e95, e5134, e5135, e5138, e5140] at *
  tauto
theorem n17024 (_v : Vars) (_q : Query _v) (h8320 : (e8320 _v)) : (e91 _v) := by
  have p16235 := n16235 _v _q 
  have p17023 := n17023 _v _q h8320
  simp only [e89, e91, e94, e95, e5134, e5135, e7983] at *
  tauto
theorem n17027 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h5108 : (e5108 _v)) : (e17026 _v) := by
  have p8139 := n8139 _v _q 
  have p17004 := n17004 _v _q h51 h5108
  exact FloorCertificate.node_17027 (e17 _v) (e61 _v) p8139 p17004
theorem n17028 (_v : Vars) (_q : Query _v)  : (e11813 _v) := by
  simp only [e5, e6, e266, e781, e1571, e5770, e5771, e5772, e5773, e5915, e5916, e5917, e5918, e5989, e5990, e5991, e5992, e6027, e6028, e6029, e6030, e8898, e8899, e8900, e8901, e8932, e8933, e8934, e8935, e8981, e8982, e8983, e8984, e9056, e9057, e9058, e9059, e9160, e11810, e11811, e11813] at *
theorem n17029 (_v : Vars) (_q : Query _v)  : (e11811 _v) := by
  have p17008 := n17008 _v _q 
  have p17028 := n17028 _v _q 
  simp only [e11810, e11811, e11813] at *
  tauto
theorem n17030 (_v : Vars) (_q : Query _v) (h4302 : (e4302 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) : (e196 _v) := by
  have p11357 := n11357 _v _q 
  have p17011 := n17011 _v _q h4302 h4419 h4434
  simp only [e196, e2358, e6571, e11356] at *
  tauto
theorem n17031 (_v : Vars) (_q : Query _v) (h4302 : (e4302 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) : (e5203 _v) := by
  have p14730 := n14730 _v _q 
  have p17030 := n17030 _v _q h4302 h4419 h4434
  simp only [e191, e192, e193, e194, e196, e5193, e5195, e5203, e5206] at *
  tauto
theorem n17032 (_v : Vars) (_q : Query _v) (h4302 : (e4302 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) : (e191 _v) := by
  have p16442 := n16442 _v _q 
  have p17031 := n17031 _v _q h4302 h4419 h4434
  simp only [e191, e192, e193, e194, e5193, e5194, e5203] at *
  tauto
theorem n17033 (_v : Vars) (_q : Query _v) (h4302 : (e4302 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) : (e7640 _v) := by
  have p14828 := n14828 _v _q 
  have p17011 := n17011 _v _q h4302 h4419 h4434
  simp only [e2358, e4139, e4140, e4141, e4142, e6571, e7634, e7640, e7643] at *
  tauto
theorem n17034 (_v : Vars) (_q : Query _v) (h4302 : (e4302 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) : (e4139 _v) := by
  have p16281 := n16281 _v _q 
  have p17033 := n17033 _v _q h4302 h4419 h4434
  simp only [e4139, e4140, e4141, e4142, e7634, e7635, e7640] at *
  tauto
end
end Assembly
