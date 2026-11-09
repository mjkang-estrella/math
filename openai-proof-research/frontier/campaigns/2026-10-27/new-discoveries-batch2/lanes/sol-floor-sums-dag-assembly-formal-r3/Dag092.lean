import Dag091
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n13380 (_v : Vars) (_q : Query _v)  : (e13379 _v) := by
  have p11800 := n11800 _v _q 
  change ((e733 _v) = (e1557 _v)) at p11800
  simp only [e13379, e5495, e1559, p11800]
theorem n13382 (_v : Vars) (_q : Query _v)  : (e13381 _v) := by
  simp only [e12, e266, e781, e782, e1557, e1559, e1560, e1561, e13381] at *
  omega
theorem n13384 (_v : Vars) (_q : Query _v)  : (e13383 _v) := by
  have p13380 := n13380 _v _q 
  have p13382 := n13382 _v _q 
  exact (Iff.trans p13380 p13382)
theorem n13386 (_v : Vars) (_q : Query _v)  : (e13385 _v) := by
  have p11807 := n11807 _v _q 
  change ((e734 _v) = (e1564 _v)) at p11807
  simp only [e13385, e5499, e1566, p11807]
theorem n13388 (_v : Vars) (_q : Query _v)  : (e13387 _v) := by
  simp only [e12, e108, e802, e803, e1564, e1566, e1567, e1568, e13387] at *
  omega
theorem n13390 (_v : Vars) (_q : Query _v)  : (e13389 _v) := by
  have p13386 := n13386 _v _q 
  have p13388 := n13388 _v _q 
  exact (Iff.trans p13386 p13388)
theorem n13393 (_v : Vars) (_q : Query _v)  : (e11978 _v) := by
  simp only [e5, e6, e5770, e5771, e5772, e5773, e5915, e5916, e5917, e5918, e5989, e5990, e5991, e5992, e6027, e6028, e6029, e6030, e8898, e8899, e8900, e8901, e8932, e8933, e8934, e8935, e8981, e8982, e8983, e8984, e9056, e9057, e9058, e9059, e9160, e11978] at *
theorem n13394 (_v : Vars) (_q : Query _v)  : (e11978 _v) := by
  have p11979 := n11979 _v _q 
  have p13393 := n13393 _v _q 
  exact (Eq.trans p11979 p13393)
theorem n13396 (_v : Vars) (_q : Query _v)  : (e13395 _v) := by
  have p13394 := n13394 _v _q 
  change ((e9160 _v) = (e9160 _v)) at p13394
  simp only [e13395, e11810]
theorem n13398 (_v : Vars) (_q : Query _v)  : (e13397 _v) := by
  have p147 := n147 _v _q 
  change ((e142 _v) = (e145 _v)) at p147
  simp only [e13397, e752, e1962, p147]
theorem n13400 (_v : Vars) (_q : Query _v)  : (e13399 _v) := by
  have p8662 := n8662 _v _q 
  have p13398 := n13398 _v _q 
  change ((e143 _v) ↔ (e151 _v)) at p8662
  change ((e752 _v) = (e1962 _v)) at p13398
  simp only [e13399, e5505, e6193, p8662, p13398]
theorem n13401 (_v : Vars) (_q : Query _v)  : (e1967 _v) := by
  have p1965 := n1965 _v _q 
  change ((e764 _v) = (e1963 _v)) at p1965
  simp only [e1967, e767, e1966, p1965]
theorem n13402 (_v : Vars) (_q : Query _v)  : (e1968 _v) := by
  simp only [e5, e6, e12, e41, e43, e44, e504, e505, e760, e761, e1963, e1966, e1968] at *
  omega
theorem n13403 (_v : Vars) (_q : Query _v)  : (e1969 _v) := by
  have p13401 := n13401 _v _q 
  have p13402 := n13402 _v _q 
  exact (Iff.trans p13401 p13402)
theorem n13405 (_v : Vars) (_q : Query _v)  : (e13404 _v) := by
  have p1965 := n1965 _v _q 
  change ((e764 _v) = (e1963 _v)) at p1965
  simp only [e13404, e773, e1970, p1965]
theorem n13407 (_v : Vars) (_q : Query _v)  : (e13406 _v) := by
  have p13403 := n13403 _v _q 
  have p13405 := n13405 _v _q 
  change ((e767 _v) ↔ (e505 _v)) at p13403
  change ((e773 _v) = (e1970 _v)) at p13405
  simp only [e13406, e5511, e6194, p13403, p13405]
theorem n13408 (_v : Vars) (_q : Query _v)  : (e1975 _v) := by
  have p1973 := n1973 _v _q 
  change ((e785 _v) = (e1971 _v)) at p1973
  simp only [e1975, e788, e1974, p1973]
theorem n13409 (_v : Vars) (_q : Query _v)  : (e1976 _v) := by
  simp only [e5, e6, e12, e41, e266, e267, e410, e411, e781, e782, e1971, e1974, e1976] at *
  omega
theorem n13410 (_v : Vars) (_q : Query _v)  : (e1977 _v) := by
  have p13408 := n13408 _v _q 
  have p13409 := n13409 _v _q 
  exact (Iff.trans p13408 p13409)
theorem n13412 (_v : Vars) (_q : Query _v)  : (e13411 _v) := by
  have p1973 := n1973 _v _q 
  change ((e785 _v) = (e1971 _v)) at p1973
  simp only [e13411, e794, e1978, p1973]
theorem n13414 (_v : Vars) (_q : Query _v)  : (e13413 _v) := by
  have p13410 := n13410 _v _q 
  have p13412 := n13412 _v _q 
  change ((e788 _v) ↔ (e411 _v)) at p13410
  change ((e794 _v) = (e1978 _v)) at p13412
  simp only [e13413, e5517, e6195, p13410, p13412]
theorem n13415 (_v : Vars) (_q : Query _v)  : (e1983 _v) := by
  have p1981 := n1981 _v _q 
  change ((e806 _v) = (e1979 _v)) at p1981
  simp only [e1983, e809, e1982, p1981]
theorem n13416 (_v : Vars) (_q : Query _v)  : (e1986 _v) := by
  simp only [e5, e6, e12, e41, e108, e109, e802, e803, e1979, e1982, e1984, e1985, e1986] at *
  omega
theorem n13417 (_v : Vars) (_q : Query _v)  : (e1987 _v) := by
  have p13415 := n13415 _v _q 
  have p13416 := n13416 _v _q 
  exact (Iff.trans p13415 p13416)
theorem n13419 (_v : Vars) (_q : Query _v)  : (e13418 _v) := by
  have p1981 := n1981 _v _q 
  change ((e806 _v) = (e1979 _v)) at p1981
  simp only [e13418, e815, e1988, p1981]
theorem n13421 (_v : Vars) (_q : Query _v)  : (e13420 _v) := by
  have p13417 := n13417 _v _q 
  have p13419 := n13419 _v _q 
  change ((e809 _v) ↔ (e1985 _v)) at p13417
  change ((e815 _v) = (e1988 _v)) at p13419
  simp only [e13420, e5523, e6196, p13417, p13419]
theorem n13423 (_v : Vars) (_q : Query _v)  : (e13422 _v) := by
  have p13400 := n13400 _v _q 
  have p13407 := n13407 _v _q 
  have p13414 := n13414 _v _q 
  have p13421 := n13421 _v _q 
  have p11986 := n11986 _v _q 
  have p11988 := n11988 _v _q 
  have p11990 := n11990 _v _q 
  have p11992 := n11992 _v _q 
  have p11994 := n11994 _v _q 
  have p11996 := n11996 _v _q 
  have p11998 := n11998 _v _q 
  have p12000 := n12000 _v _q 
  have p9420 := n9420 _v _q 
  have p9431 := n9431 _v _q 
  have p9442 := n9442 _v _q 
  have p9453 := n9453 _v _q 
  have p12002 := n12002 _v _q 
  have p12004 := n12004 _v _q 
  have p12006 := n12006 _v _q 
  have p12008 := n12008 _v _q 
  have p9508 := n9508 _v _q 
  have p9519 := n9519 _v _q 
  have p9530 := n9530 _v _q 
  have p9541 := n9541 _v _q 
  have p9552 := n9552 _v _q 
  have p9563 := n9563 _v _q 
  have p9574 := n9574 _v _q 
  have p9585 := n9585 _v _q 
  have p12010 := n12010 _v _q 
  have p12012 := n12012 _v _q 
  have p12014 := n12014 _v _q 
  have p12016 := n12016 _v _q 
  have p12018 := n12018 _v _q 
  have p12020 := n12020 _v _q 
  have p12022 := n12022 _v _q 
  have p12024 := n12024 _v _q 
  have p9696 := n9696 _v _q 
  have p9707 := n9707 _v _q 
  have p9718 := n9718 _v _q 
  have p9729 := n9729 _v _q 
  have p9740 := n9740 _v _q 
  have p9751 := n9751 _v _q 
  have p9762 := n9762 _v _q 
  have p9773 := n9773 _v _q 
  have p12026 := n12026 _v _q 
  have p12028 := n12028 _v _q 
  have p12030 := n12030 _v _q 
  have p12032 := n12032 _v _q 
  have p9840 := n9840 _v _q 
  have p9851 := n9851 _v _q 
  have p9862 := n9862 _v _q 
  have p9873 := n9873 _v _q 
  have p12034 := n12034 _v _q 
  have p12036 := n12036 _v _q 
  have p12038 := n12038 _v _q 
  have p12040 := n12040 _v _q 
  have p12042 := n12042 _v _q 
  have p12044 := n12044 _v _q 
  have p12046 := n12046 _v _q 
  have p12048 := n12048 _v _q 
  have p12056 := n12056 _v _q 
  have p12064 := n12064 _v _q 
  have p12072 := n12072 _v _q 
  have p12080 := n12080 _v _q 
  change ((e5505 _v) = (e6193 _v)) at p13400
  change ((e5511 _v) = (e6194 _v)) at p13407
  change ((e5517 _v) = (e6195 _v)) at p13414
  change ((e5523 _v) = (e6196 _v)) at p13421
  change ((e8898 _v) = (e10018 _v)) at p11986
  change ((e8899 _v) = (e10019 _v)) at p11988
  change ((e8900 _v) = (e10020 _v)) at p11990
  change ((e8901 _v) = (e10021 _v)) at p11992
  change ((e8932 _v) = (e10022 _v)) at p11994
  change ((e8933 _v) = (e10023 _v)) at p11996
  change ((e8934 _v) = (e10024 _v)) at p11998
  change ((e8935 _v) = (e10025 _v)) at p12000
  change ((e5599 _v) = (e9418 _v)) at p9420
  change ((e5609 _v) = (e9429 _v)) at p9431
  change ((e5619 _v) = (e9440 _v)) at p9442
  change ((e5629 _v) = (e9451 _v)) at p9453
  change ((e8981 _v) = (e10026 _v)) at p12002
  change ((e8982 _v) = (e10027 _v)) at p12004
  change ((e8983 _v) = (e10028 _v)) at p12006
  change ((e8984 _v) = (e10029 _v)) at p12008
  change ((e5670 _v) = (e9506 _v)) at p9508
  change ((e5680 _v) = (e9517 _v)) at p9519
  change ((e5690 _v) = (e9528 _v)) at p9530
  change ((e5700 _v) = (e9539 _v)) at p9541
  change ((e5706 _v) = (e9550 _v)) at p9552
  change ((e5716 _v) = (e9561 _v)) at p9563
  change ((e5726 _v) = (e9572 _v)) at p9574
  change ((e5736 _v) = (e9583 _v)) at p9585
  change ((e5770 _v) = (e10030 _v)) at p12010
  change ((e5771 _v) = (e10031 _v)) at p12012
  change ((e5772 _v) = (e10032 _v)) at p12014
  change ((e5773 _v) = (e10033 _v)) at p12016
  change ((e9056 _v) = (e10034 _v)) at p12018
  change ((e9057 _v) = (e10035 _v)) at p12020
  change ((e9058 _v) = (e10036 _v)) at p12022
  change ((e9059 _v) = (e10037 _v)) at p12024
  change ((e5815 _v) = (e9694 _v)) at p9696
  change ((e5825 _v) = (e9705 _v)) at p9707
  change ((e5835 _v) = (e9716 _v)) at p9718
  change ((e5845 _v) = (e9727 _v)) at p9729
  change ((e5851 _v) = (e9738 _v)) at p9740
  change ((e5861 _v) = (e9749 _v)) at p9751
  change ((e5871 _v) = (e9760 _v)) at p9762
  change ((e5881 _v) = (e9771 _v)) at p9773
  change ((e5915 _v) = (e10038 _v)) at p12026
  change ((e5916 _v) = (e10039 _v)) at p12028
  change ((e5917 _v) = (e10040 _v)) at p12030
  change ((e5918 _v) = (e10041 _v)) at p12032
  change ((e5925 _v) = (e9838 _v)) at p9840
  change ((e5935 _v) = (e9849 _v)) at p9851
  change ((e5945 _v) = (e9860 _v)) at p9862
  change ((e5955 _v) = (e9871 _v)) at p9873
  change ((e5989 _v) = (e10042 _v)) at p12034
  change ((e5990 _v) = (e10043 _v)) at p12036
  change ((e5991 _v) = (e10044 _v)) at p12038
  change ((e5992 _v) = (e10045 _v)) at p12040
  change ((e6027 _v) = (e10046 _v)) at p12042
  change ((e6028 _v) = (e10047 _v)) at p12044
  change ((e6029 _v) = (e10048 _v)) at p12046
  change ((e6030 _v) = (e10049 _v)) at p12048
  change ((e9155 _v) = (e10050 _v)) at p12056
  change ((e9156 _v) = (e10051 _v)) at p12064
  change ((e9157 _v) = (e10052 _v)) at p12072
  change ((e9158 _v) = (e10053 _v)) at p12080
  simp only [e13422, e9321, e10054, p13400, p13407, p13414, p13421, p11986, p11988, p11990, p11992, p11994, p11996, p11998, p12000, p9420, p9431, p9442, p9453, p12002, p12004, p12006, p12008, p9508, p9519, p9530, p9541, p9552, p9563, p9574, p9585, p12010, p12012, p12014, p12016, p12018, p12020, p12022, p12024, p9696, p9707, p9718, p9729, p9740, p9751, p9762, p9773, p12026, p12028, p12030, p12032, p9840, p9851, p9862, p9873, p12034, p12036, p12038, p12040, p12042, p12044, p12046, p12048, p12056, p12064, p12072, p12080]
theorem n13425 (_v : Vars) (_q : Query _v)  : (e13424 _v) := by
  have p12240 := n12240 _v _q 
  change ((e9639 _v) = (e101 _v)) at p12240
  simp only [e13424, e10033, e126, p12240]
theorem n13427 (_v : Vars) (_q : Query _v)  : (e13426 _v) := by
  have p12344 := n12344 _v _q 
  change ((e9827 _v) = (e2974 _v)) at p12344
  simp only [e13426, e10041, e2975, p12344]
theorem n13429 (_v : Vars) (_q : Query _v)  : (e13428 _v) := by
  have p12400 := n12400 _v _q 
  change ((e9927 _v) = (e2984 _v)) at p12400
  simp only [e13428, e10045, e2985, p12400]
theorem n13431 (_v : Vars) (_q : Query _v)  : (e13430 _v) := by
  have p12416 := n12416 _v _q 
  change ((e9983 _v) = (e2992 _v)) at p12416
  simp only [e13430, e10049, e2993, p12416]
theorem n13432 (_v : Vars) (_q : Query _v)  : (e6807 _v) := by
  have p12418 := n12418 _v _q 
  change ((e3011 _v) ↔ (e6803 _v)) at p12418
  simp only [e6807, e6496, e6806, p12418]
theorem n13433 (_v : Vars) (_q : Query _v)  : (e6808 _v) := by
  simp only [e5, e6, e8, e12, e41, e108, e109, e111, e2164, e2165, e3017, e3018, e3019, e3021, e3024, e3025, e6802, e6803, e6806, e6808] at *
theorem n13434 (_v : Vars) (_q : Query _v)  : (e6807 _v) := by
  have p13432 := n13432 _v _q 
  have p13433 := n13433 _v _q 
  exact (Iff.trans p13432 p13433)
theorem n13436 (_v : Vars) (_q : Query _v)  : (e13435 _v) := by
  have p10532 := n10532 _v _q 
  have p13434 := n13434 _v _q 
  change ((e6495 _v) ↔ (e6809 _v)) at p10532
  change ((e6496 _v) ↔ (e6806 _v)) at p13434
  simp only [e13435, e6497, e6810, p10532, p13434]
theorem n13439 (_v : Vars) (_q : Query _v)  : (e13438 _v) := by
  simp only [e5, e6, e8, e12, e41, e108, e109, e111, e2164, e2165, e2999, e3000, e3001, e3002, e3003, e3009, e3017, e3018, e3019, e3021, e3024, e3025, e6494, e6802, e6803, e6806, e6809, e6810, e6811, e10535, e10536, e13437, e13438] at *
  omega
theorem n13441 (_v : Vars) (_q : Query _v)  : (e13440 _v) := by
  have p13436 := n13436 _v _q 
  have p13439 := n13439 _v _q 
  exact (Iff.trans p13436 p13439)
theorem n13443 (_v : Vars) (_q : Query _v)  : (e13442 _v) := by
  have p12420 := n12420 _v _q 
  change ((e2818 _v) ↔ (e6819 _v)) at p12420
  simp only [e13442, e2819, e6822, p12420]
theorem n13445 (_v : Vars) (_q : Query _v)  : (e13444 _v) := by
  simp only [e5, e6, e12, e41, e150, e151, e3042, e3043, e3044, e3046, e3049, e3050, e6818, e6819, e6822, e13444] at *
theorem n13446 (_v : Vars) (_q : Query _v)  : (e13442 _v) := by
  have p13443 := n13443 _v _q 
  have p13445 := n13445 _v _q 
  exact (Iff.trans p13443 p13445)
theorem n13447 (_v : Vars) (_q : Query _v)  : (e10545 _v) := by
  have p10541 := n10541 _v _q 
  have p13446 := n13446 _v _q 
  change ((e6405 _v) ↔ (e10539 _v)) at p10541
  change ((e2819 _v) ↔ (e6822 _v)) at p13446
  simp only [e10545, e6406, e10544, p10541, p13446]
theorem n13448 (_v : Vars) (_q : Query _v)  : (e6834 _v) := by
  have p12425 := n12425 _v _q 
  change ((e3062 _v) ↔ (e6830 _v)) at p12425
  simp only [e6834, e6722, e6833, p12425]
theorem n13449 (_v : Vars) (_q : Query _v)  : (e6835 _v) := by
  simp only [e5, e6, e8, e10, e12, e41, e46, e495, e496, e2981, e3068, e3069, e3071, e3074, e3075, e6829, e6830, e6833, e6835] at *
theorem n13450 (_v : Vars) (_q : Query _v)  : (e6834 _v) := by
  have p13448 := n13448 _v _q 
  have p13449 := n13449 _v _q 
  exact (Iff.trans p13448 p13449)
theorem n13452 (_v : Vars) (_q : Query _v)  : (e13451 _v) := by
  have p10553 := n10553 _v _q 
  have p13450 := n13450 _v _q 
  change ((e6721 _v) ↔ (e6836 _v)) at p10553
  change ((e6722 _v) ↔ (e6833 _v)) at p13450
  simp only [e13451, e6723, e6837, p10553, p13450]
end
end Assembly
