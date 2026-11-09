import Dag193
import generated.th_lemma_22
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n18611 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4491 : (e4491 _v)) (h4546 : (e4546 _v)) (h4562 : (e4562 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) (h5093 : (e5093 _v)) : (e2475 _v) := by
  have p18603 := n18603 _v _q 
  have p17225 := n17225 _v _q h5093
  have p4986 := n4986 _v _q h3105
  have p4983 := n4983 _v _q h4813
  have p4994 := n4994 _v _q h3069
  have p4984 := n4984 _v _q h4872
  have p4991 := n4991 _v _q h4608
  have p4972 := n4972 _v _q h4899
  have p4998 := n4998 _v _q h3152
  have p4995 := n4995 _v _q h4369
  have p4988 := n4988 _v _q h488
  have p4999 := n4999 _v _q h91
  have p5001 := n5001 _v _q h4096
  have p4989 := n4989 _v _q h4838
  have p4996 := n4996 _v _q h3937
  have p5007 := n5007 _v _q h225
  have p4987 := n4987 _v _q h4434
  have p5008 := n5008 _v _q h4787
  have p4985 := n4985 _v _q h4156
  have p17076 := n17076 _v _q h3976
  have p5003 := n5003 _v _q h4199
  have p5005 := n5005 _v _q h3169
  have p5006 := n5006 _v _q h4675
  have p18610 := n18610 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h3976 h4059 h4096 h4139 h4156 h4199 h4260 h4285 h4301 h4369 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h5093
  have p5010 := n5010 _v _q h70
  have p4981 := n4981 _v _q h4260
  have p4992 := n4992 _v _q h442
  simp only [e70, e75, e91, e95, e225, e230, e442, e443, e488, e493, e2475, e2634, e3069, e3074, e3105, e3106, e3152, e3156, e3169, e3170, e3937, e3942, e3976, e3981, e4096, e4097, e4156, e4157, e4199, e4200, e4260, e4261, e4369, e4370, e4434, e4435, e4608, e4609, e4675, e4676, e4787, e4788, e4813, e4814, e4838, e4839, e4872, e4873, e4899, e4900, e6700, e8398, e8406, e18602] at *
  tauto
theorem n18612 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4491 : (e4491 _v)) (h4546 : (e4546 _v)) (h4562 : (e4562 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) (h5093 : (e5093 _v)) : (e4398 _v) := by
  have p14976 := n14976 _v _q 
  have p18026 := n18026 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h3976 h4059 h4096 h4139 h4156 h4199 h4260 h4285 h4301 h4369 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h4899 h5093
  simp only [e4397, e4398, e4402, e4403, e4404, e4405, e4962] at *
  tauto
theorem n18613 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4491 : (e4491 _v)) (h4546 : (e4546 _v)) (h4562 : (e4562 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) (h5093 : (e5093 _v)) : (e2310 _v) := by
  have p17709 := n17709 _v _q 
  have p18611 := n18611 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h3976 h4059 h4096 h4139 h4156 h4199 h4260 h4285 h4301 h4369 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h4899 h5093
  have p4980 := n4980 _v _q h4301
  have p16994 := n16994 _v _q 
  have p17076 := n17076 _v _q h3976
  have p4978 := n4978 _v _q h4477
  have p4973 := n4973 _v _q h4562
  have p4981 := n4981 _v _q h4260
  have p17061 := n17061 _v _q h4747
  have p4983 := n4983 _v _q h4813
  have p4984 := n4984 _v _q h4872
  have p4985 := n4985 _v _q h4156
  have p4986 := n4986 _v _q h3105
  have p4987 := n4987 _v _q h4434
  have p4988 := n4988 _v _q h488
  have p15321 := n15321 _v _q h5093
  have p17222 := n17222 _v _q h5093
  have p4990 := n4990 _v _q h4648
  have p4991 := n4991 _v _q h4608
  have p4992 := n4992 _v _q h442
  have p16778 := n16778 _v _q 
  have p4994 := n4994 _v _q h3069
  have p4995 := n4995 _v _q h4369
  have p4996 := n4996 _v _q h3937
  have p17772 := n17772 _v _q h5093
  have p4998 := n4998 _v _q h3152
  have p17137 := n17137 _v _q h4059
  have p4999 := n4999 _v _q h91
  have p17223 := n17223 _v _q h5093
  have p5001 := n5001 _v _q h4096
  have p17128 := n17128 _v _q h4491
  have p17056 := n17056 _v _q h3946
  have p5003 := n5003 _v _q h4199
  have p5006 := n5006 _v _q h4675
  have p5007 := n5007 _v _q h225
  have p5008 := n5008 _v _q h4787
  have p5010 := n5010 _v _q h70
  have p18612 := n18612 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h3976 h4059 h4096 h4139 h4156 h4199 h4260 h4285 h4301 h4369 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h4899 h5093
  simp only [e70, e75, e91, e95, e225, e230, e442, e443, e488, e493, e2310, e2475, e3069, e3074, e3105, e3106, e3152, e3156, e3855, e3860, e3937, e3942, e3946, e3947, e3976, e3981, e4059, e4064, e4096, e4097, e4156, e4157, e4199, e4200, e4260, e4261, e4301, e4302, e4369, e4370, e4398, e4403, e4434, e4435, e4477, e4481, e4491, e4496, e4562, e4563, e4608, e4609, e4648, e4649, e4675, e4676, e4724, e4729, e4747, e4752, e4787, e4788, e4813, e4814, e4872, e4873, e5100, e5103, e7493, e7494, e7749, e7752, e8038, e8335, e8345, e17708] at *
  tauto
theorem n18614 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2364 : (e2364 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h7935 : (e7935 _v)) (h8310 : (e8310 _v)) : (e196 _v) := by
  have p17611 := n17611 _v _q 
  have p15606 := n15606 _v _q h8310
  have p17163 := n17163 _v _q h7935
  have p4981 := n4981 _v _q h4260
  have p5001 := n5001 _v _q h4096
  have p4999 := n4999 _v _q h91
  have p4994 := n4994 _v _q h3069
  have p5010 := n5010 _v _q h70
  have p5003 := n5003 _v _q h4199
  have p5007 := n5007 _v _q h225
  have p4992 := n4992 _v _q h442
  have p15608 := n15608 _v _q h8310
  have p4996 := n4996 _v _q h3937
  have p15599 := n15599 _v _q h2364
  have p17134 := n17134 _v _q h4398
  have p4987 := n4987 _v _q h4434
  have p17453 := n17453 _v _q h8310
  have p17137 := n17137 _v _q h4059
  have p17138 := n17138 _v _q h4306
  have p17440 := n17440 _v _q h2364
  have p15604 := n15604 _v _q h2364
  have p15248 := n15248 _v _q h8310
  have p4983 := n4983 _v _q h4813
  have p4995 := n4995 _v _q h4369
  have p4998 := n4998 _v _q h3152
  have p15612 := n15612 _v _q h8310
  have p5008 := n5008 _v _q h4787
  have p15170 := n15170 _v _q h2364
  have p5006 := n5006 _v _q h4675
  have p17056 := n17056 _v _q h3946
  have p17061 := n17061 _v _q h4747
  have p4985 := n4985 _v _q h4156
  have p15567 := n15567 _v _q h2364
  have p4988 := n4988 _v _q h488
  have p4986 := n4986 _v _q h3105
  have p4984 := n4984 _v _q h4872
  have p4991 := n4991 _v _q h4608
  have p18606 := n18606 _v _q h70 h91 h225 h442 h488 h2364 h3069 h3105 h3152 h3937 h4096 h4156 h4199 h4260 h4369 h4608 h4675 h4787 h4813 h4872 h8310
  simp only [e70, e75, e91, e95, e196, e225, e230, e442, e443, e488, e493, e2634, e3069, e3074, e3105, e3106, e3152, e3156, e3937, e3942, e3946, e3947, e3976, e3981, e4059, e4064, e4096, e4097, e4156, e4157, e4199, e4200, e4260, e4261, e4306, e4311, e4369, e4370, e4398, e4403, e4434, e4435, e4491, e4496, e4608, e4609, e4653, e4658, e4675, e4676, e4724, e4729, e4747, e4752, e4787, e4788, e4813, e4814, e4872, e4873, e4903, e4908, e5100, e5103, e6700, e7493, e7494, e7749, e7752, e7935, e7943, e8045, e8048, e8317, e8320, e17610] at *
  tauto
theorem n18615 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2364 : (e2364 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h8310 : (e8310 _v)) : (e3180 _v) := by
  have p14361 := n14361 _v _q 
  have p18606 := n18606 _v _q h70 h91 h225 h442 h488 h2364 h3069 h3105 h3152 h3937 h4096 h4156 h4199 h4260 h4369 h4608 h4675 h4787 h4813 h4872 h8310
  simp only [e2634, e3172, e3173, e3177, e3178, e3179, e3180, e6700, e6902] at *
  tauto
theorem n18616 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2364 : (e2364 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h8310 : (e8310 _v)) : (e3173 _v) := by
  have p6907 := n6907 _v _q 
  have p18615 := n18615 _v _q h70 h91 h225 h442 h488 h2364 h3069 h3105 h3152 h3937 h4096 h4156 h4199 h4260 h4369 h4608 h4675 h4787 h4813 h4872 h8310
  simp only [e3172, e3173, e3177, e3178, e3179, e3180, e3190] at *
  tauto
theorem n18617 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4491 : (e4491 _v)) (h4546 : (e4546 _v)) (h4562 : (e4562 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) (h5093 : (e5093 _v)) : (e3278 _v) := by
  have p14378 := n14378 _v _q 
  have p18613 := n18613 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h3976 h4059 h4096 h4139 h4156 h4199 h4260 h4285 h4301 h4369 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h4899 h5093
  simp only [e2310, e3270, e3271, e3275, e3276, e3277, e3278, e6555, e6979] at *
  tauto
theorem n18618 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4491 : (e4491 _v)) (h4546 : (e4546 _v)) (h4562 : (e4562 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) (h5093 : (e5093 _v)) : (e3271 _v) := by
  have p6982 := n6982 _v _q 
  have p18617 := n18617 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h3976 h4059 h4096 h4139 h4156 h4199 h4260 h4285 h4301 h4369 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h4899 h5093
  simp only [e3270, e3271, e3275, e3276, e3277, e3278, e3288] at *
  tauto
theorem n18619 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4491 : (e4491 _v)) (h4546 : (e4546 _v)) (h4562 : (e4562 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) (h5093 : (e5093 _v)) : (e7489 _v) := by
  have p17133 := n17133 _v _q 
  have p17093 := n17093 _v _q 
  have p8663 := n8663 _v _q 
  have p296 := n296 _v _q 
  have p17141 := n17141 _v _q 
  have p17069 := n17069 _v _q 
  have p17131 := n17131 _v _q 
  have p18612 := n18612 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h3976 h4059 h4096 h4139 h4156 h4199 h4260 h4285 h4301 h4369 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h4899 h5093
  have p17225 := n17225 _v _q h5093
  have p4972 := n4972 _v _q h4899
  have p4999 := n4999 _v _q h91
  have p5001 := n5001 _v _q h4096
  have p4996 := n4996 _v _q h3937
  have p4998 := n4998 _v _q h3152
  have p16181 := n16181 _v _q 
  have p4977 := n4977 _v _q h4285
  have p16913 := n16913 _v _q 
  have p17128 := n17128 _v _q h4491
  have p17136 := n17136 _v _q 
  have p5003 := n5003 _v _q h4199
  have p17053 := n17053 _v _q 
  have p17772 := n17772 _v _q h5093
  have p17497 := n17497 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h3976 h4059 h4096 h4139 h4156 h4199 h4260 h4285 h4301 h4369 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h5093
  have p17076 := n17076 _v _q h3976
  have p17056 := n17056 _v _q h3946
  have p18618 := n18618 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h3976 h4059 h4096 h4139 h4156 h4199 h4260 h4285 h4301 h4369 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h4899 h5093
  have p17127 := n17127 _v _q 
  have p5008 := n5008 _v _q h4787
  have p5007 := n5007 _v _q h225
  have p17055 := n17055 _v _q 
  have p16778 := n16778 _v _q 
  have p17061 := n17061 _v _q h4747
  have p17147 := n17147 _v _q 
  have p17221 := n17221 _v _q 
  have p16994 := n16994 _v _q 
  have p17222 := n17222 _v _q h5093
  have p17223 := n17223 _v _q h5093
  have p15321 := n15321 _v _q h5093
  have p17137 := n17137 _v _q h4059
  have p5006 := n5006 _v _q h4675
  have p5010 := n5010 _v _q h70
  have p17064 := n17064 _v _q 
  have p4971 := n4971 _v _q h4419
  have p4976 := n4976 _v _q h4546
  have p16929 := n16929 _v _q 
  have p4978 := n4978 _v _q h4477
  have p4979 := n4979 _v _q h4139
  have p4980 := n4980 _v _q h4301
  have p5005 := n5005 _v _q h3169
  have p16394 := n16394 _v _q 
  have p4973 := n4973 _v _q h4562
  have p4985 := n4985 _v _q h4156
  have p4987 := n4987 _v _q h4434
  have p4983 := n4983 _v _q h4813
  have p16175 := n16175 _v _q 
  have p17074 := n17074 _v _q 
  have p4988 := n4988 _v _q h488
  have p4981 := n4981 _v _q h4260
  have p4989 := n4989 _v _q h4838
  have p17072 := n17072 _v _q 
  have p4986 := n4986 _v _q h3105
  have p17080 := n17080 _v _q 
  have p17078 := n17078 _v _q 
  have p17091 := n17091 _v _q 
  have p253 := n253 _v _q h191
  have p17098 := n17098 _v _q 
  have p4990 := n4990 _v _q h4648
  have p17100 := n17100 _v _q 
  have p4984 := n4984 _v _q h4872
  have p17067 := n17067 _v _q 
  have p17087 := n17087 _v _q 
  have p4991 := n4991 _v _q h4608
  have p4992 := n4992 _v _q h442
  have p17115 := n17115 _v _q 
  have p17083 := n17083 _v _q 
  have p17110 := n17110 _v _q 
  have p16576 := n16576 _v _q 
  have p17058 := n17058 _v _q 
  have p17113 := n17113 _v _q 
  have p17102 := n17102 _v _q 
  have p17096 := n17096 _v _q 
  have p17106 := n17106 _v _q 
  have p17122 := n17122 _v _q 
  have p17104 := n17104 _v _q 
  have p4995 := n4995 _v _q h4369
  have p17124 := n17124 _v _q 
  have p17108 := n17108 _v _q 
  have p4994 := n4994 _v _q h3069
  have p17117 := n17117 _v _q 
  have p17120 := n17120 _v _q 
  have p5257 := n5257 _v _q 
  have p11440 := n11440 _v _q h5093
  have p5255 := n5255 _v _q 
  have p13951 := n13951 _v _q 
  exact FloorCertificate.node_18619 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e61 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2834 _v) (e2849 _v) (e2863 _v) (e2877 _v) (e2879 _v) (e2883 _v) (e2898 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2913 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e3164 _v) (e3574 _v) (e4215 _v) (e4541 _v) (e4808 _v) p17133 p17093 p8663 p296 p17141 p17069 p17131 p18612 p17225 p4972 p4999 p5001 p4996 p4998 p16181 p4977 p16913 p17128 p17136 p5003 p17053 p17772 p17497 p17076 p17056 p18618 p17127 p5008 p5007 p17055 p16778 p17061 p17147 p17221 p16994 p17222 p17223 p15321 p17137 p5006 p5010 p17064 p4971 p4976 p16929 p4978 p4979 p4980 p5005 p16394 p4973 p4985 p4987 p4983 p16175 p17074 p4988 p4981 p4989 p17072 p4986 p17080 p17078 p17091 p253 p17098 p4990 p17100 p4984 p17067 p17087 p4991 p4992 p17115 p17083 p17110 p16576 p17058 p17113 p17102 p17096 p17106 p17122 p17104 p4995 p17124 p17108 p4994 p17117 p17120 p5257 p11440 p5255 p13951
theorem n18620 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2364 : (e2364 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h7935 : (e7935 _v)) (h8310 : (e8310 _v)) : (e5203 _v) := by
  have p14730 := n14730 _v _q 
  have p18614 := n18614 _v _q h70 h91 h225 h442 h488 h2364 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4156 h4199 h4260 h4306 h4369 h4398 h4434 h4608 h4675 h4747 h4787 h4813 h4872 h7935 h8310
  simp only [e191, e192, e193, e194, e196, e5193, e5195, e5203, e5206] at *
  tauto
theorem n18621 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2364 : (e2364 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h7935 : (e7935 _v)) (h8310 : (e8310 _v)) : (e191 _v) := by
  have p16442 := n16442 _v _q 
  have p18620 := n18620 _v _q h70 h91 h225 h442 h488 h2364 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4156 h4199 h4260 h4306 h4369 h4398 h4434 h4608 h4675 h4747 h4787 h4813 h4872 h7935 h8310
  simp only [e191, e192, e193, e194, e5193, e5194, e5203] at *
  tauto
theorem n18623 (_v : Vars) (_q : Query _v)  : (e18622 _v) := by
  by_contra hc
  change ¬ ((e13 _v) ∨ (¬ (e4899 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4285 _v)) ∨ (¬ (e4491 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e3976 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4419 _v)) ∨ (¬ (e4546 _v)) ∨ (¬ (e4477 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e4301 _v)) ∨ (¬ (e3169 _v)) ∨ (¬ (e4562 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e4648 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e3069 _v))) at hc
  have h70 : (e70 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h191 : (e191 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))))
  have h225 : (e225 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h442 : (e442 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))))))))
  have h488 : (e488 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))
  have h3069 : (e3069 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))))))))))))))))))))))))))))))))))
  have h3105 : (e3105 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h3169 : (e3169 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h3946 : (e3946 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h3976 : (e3976 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h4059 : (e4059 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h4096 : (e4096 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4139 : (e4139 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))
  have h4156 : (e4156 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))
  have h4199 : (e4199 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h4260 : (e4260 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))
  have h4285 : (e4285 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h4301 : (e4301 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))
  have h4369 : (e4369 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))))))))
  have h4419 : (e4419 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))
  have h4434 : (e4434 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))
  have h4477 : (e4477 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))
  have h4491 : (e4491 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h4546 : (e4546 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))
  have h4562 : (e4562 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))
  have h4608 : (e4608 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))))))
  have h4648 : (e4648 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))))
  have h4675 : (e4675 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))
  have h4747 : (e4747 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))
  have h4838 : (e4838 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))
  have h4872 : (e4872 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))))))
  have h4899 : (e4899 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h5093 : (e5093 _v) := (fun hn => hc (Or.inl hn))
  have p18619 := n18619 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h3976 h4059 h4096 h4139 h4156 h4199 h4260 h4285 h4301 h4369 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h4899 h5093
  exact p18619
theorem n18624 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2364 : (e2364 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h7935 : (e7935 _v)) (h8310 : (e8310 _v)) : (e1995 _v) := by
  have p17609 := n17609 _v _q 
  have p18621 := n18621 _v _q h70 h91 h225 h442 h488 h2364 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4156 h4199 h4260 h4306 h4369 h4398 h4434 h4608 h4675 h4747 h4787 h4813 h4872 h7935 h8310
  have p4994 := n4994 _v _q h3069
  have p17163 := n17163 _v _q h7935
  have p4981 := n4981 _v _q h4260
  have p5001 := n5001 _v _q h4096
  have p4999 := n4999 _v _q h91
  have p15606 := n15606 _v _q h8310
  have p5010 := n5010 _v _q h70
  have p5003 := n5003 _v _q h4199
  have p5007 := n5007 _v _q h225
  have p4992 := n4992 _v _q h442
  have p15608 := n15608 _v _q h8310
  have p4996 := n4996 _v _q h3937
  have p18616 := n18616 _v _q h70 h91 h225 h442 h488 h2364 h3069 h3105 h3152 h3937 h4096 h4156 h4199 h4260 h4369 h4608 h4675 h4787 h4813 h4872 h8310
  have p17134 := n17134 _v _q h4398
  have p4987 := n4987 _v _q h4434
  have p17453 := n17453 _v _q h8310
  have p17137 := n17137 _v _q h4059
  have p17138 := n17138 _v _q h4306
  have p15248 := n15248 _v _q h8310
  have p4983 := n4983 _v _q h4813
  have p4995 := n4995 _v _q h4369
  have p4998 := n4998 _v _q h3152
  have p15612 := n15612 _v _q h8310
  have p5008 := n5008 _v _q h4787
  have p5006 := n5006 _v _q h4675
  have p17056 := n17056 _v _q h3946
  have p17061 := n17061 _v _q h4747
  have p4985 := n4985 _v _q h4156
  have p4988 := n4988 _v _q h488
  have p4986 := n4986 _v _q h3105
  have p4984 := n4984 _v _q h4872
  have p4991 := n4991 _v _q h4608
  have p8527 := n8527 _v _q h2364
  simp only [e70, e75, e91, e95, e191, e192, e225, e230, e442, e443, e488, e493, e1995, e2364, e3069, e3074, e3105, e3106, e3152, e3156, e3173, e3178, e3937, e3942, e3946, e3947, e4059, e4064, e4096, e4097, e4156, e4157, e4199, e4200, e4260, e4261, e4306, e4311, e4369, e4370, e4398, e4403, e4434, e4435, e4608, e4609, e4675, e4676, e4747, e4752, e4787, e4788, e4813, e4814, e4872, e4873, e5100, e5103, e6583, e7493, e7494, e7749, e7752, e7935, e7943, e8045, e8048, e8317, e8320, e17608] at *
  tauto
theorem n18625 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4491 : (e4491 _v)) (h4546 : (e4546 _v)) (h4562 : (e4562 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) : (e13 _v) := by
  have p18623 := n18623 _v _q 
  have p17076 := n17076 _v _q h3976
  have p4999 := n4999 _v _q h91
  have p5001 := n5001 _v _q h4096
  have p4996 := n4996 _v _q h3937
  have p4998 := n4998 _v _q h3152
  have p4977 := n4977 _v _q h4285
  have p17128 := n17128 _v _q h4491
  have p5003 := n5003 _v _q h4199
  have p4972 := n4972 _v _q h4899
  have p17056 := n17056 _v _q h3946
  have p5008 := n5008 _v _q h4787
  have p5007 := n5007 _v _q h225
  have p17061 := n17061 _v _q h4747
  have p17137 := n17137 _v _q h4059
  have p5006 := n5006 _v _q h4675
  have p5010 := n5010 _v _q h70
  have p4971 := n4971 _v _q h4419
  have p4976 := n4976 _v _q h4546
  have p4978 := n4978 _v _q h4477
  have p4979 := n4979 _v _q h4139
  have p4980 := n4980 _v _q h4301
  have p5005 := n5005 _v _q h3169
  have p4973 := n4973 _v _q h4562
  have p4985 := n4985 _v _q h4156
  have p4987 := n4987 _v _q h4434
  have p4983 := n4983 _v _q h4813
  have p4988 := n4988 _v _q h488
  have p4981 := n4981 _v _q h4260
  have p4989 := n4989 _v _q h4838
  have p4986 := n4986 _v _q h3105
  have p253 := n253 _v _q h191
  have p4990 := n4990 _v _q h4648
  have p4984 := n4984 _v _q h4872
  have p4991 := n4991 _v _q h4608
  have p4992 := n4992 _v _q h442
  have p4995 := n4995 _v _q h4369
  have p4994 := n4994 _v _q h3069
  simp only [e13, e70, e75, e91, e95, e191, e192, e225, e230, e442, e443, e488, e493, e3069, e3074, e3105, e3106, e3152, e3156, e3169, e3170, e3937, e3942, e3946, e3947, e3976, e3981, e4059, e4064, e4096, e4097, e4139, e4140, e4156, e4157, e4199, e4200, e4260, e4261, e4285, e4286, e4301, e4302, e4369, e4370, e4419, e4420, e4434, e4435, e4477, e4481, e4491, e4496, e4546, e4547, e4562, e4563, e4608, e4609, e4648, e4649, e4675, e4676, e4747, e4752, e4787, e4788, e4813, e4814, e4838, e4839, e4872, e4873, e4899, e4900, e18622] at *
  tauto
theorem n18626 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2364 : (e2364 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h7935 : (e7935 _v)) (h8310 : (e8310 _v)) : (e4575 _v) := by
  have p14696 := n14696 _v _q 
  have p18624 := n18624 _v _q h70 h91 h225 h442 h488 h2364 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4156 h4199 h4260 h4306 h4369 h4398 h4434 h4608 h4675 h4747 h4787 h4813 h4872 h7935 h8310
  simp only [e1995, e4567, e4568, e4572, e4573, e4574, e4575, e6423, e8066] at *
  tauto
theorem n18627 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2364 : (e2364 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h7935 : (e7935 _v)) (h8310 : (e8310 _v)) : (e4567 _v) := by
  have p8485 := n8485 _v _q 
  have p18626 := n18626 _v _q h70 h91 h225 h442 h488 h2364 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4156 h4199 h4260 h4306 h4369 h4398 h4434 h4608 h4675 h4747 h4787 h4813 h4872 h7935 h8310
  simp only [e4567, e4568, e4572, e4573, e4574, e4575, e4956] at *
  tauto
theorem n18628 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4491 : (e4491 _v)) (h4546 : (e4546 _v)) (h4562 : (e4562 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) : (e5090 _v) := by
  have p14728 := n14728 _v _q 
  have p18625 := n18625 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h3976 h4059 h4096 h4139 h4156 h4199 h4260 h4285 h4301 h4369 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h4899
  simp only [e13, e28, e30, e34, e35, e5089, e5090, e5093, e5095] at *
  tauto
theorem n18629 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4491 : (e4491 _v)) (h4546 : (e4546 _v)) (h4562 : (e4562 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) : (e30 _v) := by
  have p16290 := n16290 _v _q 
  have p18628 := n18628 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h3976 h4059 h4096 h4139 h4156 h4199 h4260 h4285 h4301 h4369 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h4899
  simp only [e28, e30, e34, e35, e5089, e5090, e5107] at *
  tauto
theorem n18630 (_v : Vars) (_q : Query _v) (h8310 : (e8310 _v)) : (e7814 _v) := by
  have p15221 := n15221 _v _q 
  have p15613 := n15613 _v _q h8310
  simp only [e7812, e7814, e7816, e7817, e7818, e7819, e8456] at *
  tauto
theorem n18631 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2364 : (e2364 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h7935 : (e7935 _v)) (h8310 : (e8310 _v)) : (e5208 _v) := by
  have p18614 := n18614 _v _q h70 h91 h225 h442 h488 h2364 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4156 h4199 h4260 h4306 h4369 h4398 h4434 h4608 h4675 h4747 h4787 h4813 h4872 h7935 h8310
  have p18621 := n18621 _v _q h70 h91 h225 h442 h488 h2364 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4156 h4199 h4260 h4306 h4369 h4398 h4434 h4608 h4675 h4747 h4787 h4813 h4872 h7935 h8310
  exact FloorCertificate.node_18631 (e2 _v) (e7 _v) (e17 _v) (e45 _v) (e110 _v) (e188 _v) p18614 p18621
theorem n18632 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2364 : (e2364 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h7935 : (e7935 _v)) (h8310 : (e8310 _v)) : (e7655 _v) := by
  have p17360 := n17360 _v _q 
  have p18630 := n18630 _v _q h8310
  have p17163 := n17163 _v _q h7935
  have p4981 := n4981 _v _q h4260
  have p5001 := n5001 _v _q h4096
  have p4999 := n4999 _v _q h91
  have p15606 := n15606 _v _q h8310
  have p5010 := n5010 _v _q h70
  have p5003 := n5003 _v _q h4199
  have p5007 := n5007 _v _q h225
  have p4992 := n4992 _v _q h442
  have p15608 := n15608 _v _q h8310
  have p4996 := n4996 _v _q h3937
  have p15599 := n15599 _v _q h2364
  have p17134 := n17134 _v _q h4398
  have p4987 := n4987 _v _q h4434
  have p17453 := n17453 _v _q h8310
  have p17137 := n17137 _v _q h4059
  have p17138 := n17138 _v _q h4306
  have p17440 := n17440 _v _q h2364
  have p15604 := n15604 _v _q h2364
  have p15248 := n15248 _v _q h8310
  have p4983 := n4983 _v _q h4813
  have p4995 := n4995 _v _q h4369
  have p4998 := n4998 _v _q h3152
  have p18606 := n18606 _v _q h70 h91 h225 h442 h488 h2364 h3069 h3105 h3152 h3937 h4096 h4156 h4199 h4260 h4369 h4608 h4675 h4787 h4813 h4872 h8310
  have p15612 := n15612 _v _q h8310
  have p5008 := n5008 _v _q h4787
  have p15170 := n15170 _v _q h2364
  have p5006 := n5006 _v _q h4675
  have p17056 := n17056 _v _q h3946
  have p17061 := n17061 _v _q h4747
  have p4985 := n4985 _v _q h4156
  have p15567 := n15567 _v _q h2364
  have p4988 := n4988 _v _q h488
  have p18631 := n18631 _v _q h70 h91 h225 h442 h488 h2364 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4156 h4199 h4260 h4306 h4369 h4398 h4434 h4608 h4675 h4747 h4787 h4813 h4872 h7935 h8310
  have p4986 := n4986 _v _q h3105
  have p4984 := n4984 _v _q h4872
  have p4991 := n4991 _v _q h4608
  have p18627 := n18627 _v _q h70 h91 h225 h442 h488 h2364 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4156 h4199 h4260 h4306 h4369 h4398 h4434 h4608 h4675 h4747 h4787 h4813 h4872 h7935 h8310
  have p4994 := n4994 _v _q h3069
  simp only [e70, e75, e91, e95, e225, e230, e442, e443, e488, e493, e2634, e3069, e3074, e3105, e3106, e3152, e3156, e3937, e3942, e3946, e3947, e3976, e3981, e4059, e4064, e4096, e4097, e4156, e4157, e4199, e4200, e4260, e4261, e4306, e4311, e4369, e4370, e4398, e4403, e4434, e4435, e4491, e4496, e4567, e4572, e4608, e4609, e4653, e4658, e4675, e4676, e4724, e4729, e4747, e4752, e4787, e4788, e4813, e4814, e4872, e4873, e4903, e4908, e5100, e5103, e5208, e5218, e6700, e7493, e7494, e7645, e7655, e7749, e7752, e7814, e7817, e7935, e7943, e8045, e8048, e8317, e8320, e17359] at *
  tauto
theorem n18633 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2364 : (e2364 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h7935 : (e7935 _v)) (h8310 : (e8310 _v)) : (e7657 _v) := by
  have p11406 := n11406 _v _q 
  have p18632 := n18632 _v _q h70 h91 h225 h442 h488 h2364 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4156 h4199 h4260 h4306 h4369 h4398 h4434 h4608 h4675 h4747 h4787 h4813 h4872 h7935 h8310
  simp only [e7645, e7648, e7655, e7656, e7657, e8474] at *
  tauto
theorem n18634 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4491 : (e4491 _v)) (h4546 : (e4546 _v)) (h4562 : (e4562 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) : (e4221 _v) := by
  have p18342 := n18342 _v _q 
  have p18629 := n18629 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h3976 h4059 h4096 h4139 h4156 h4199 h4260 h4285 h4301 h4369 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h4899
  have p16911 := n16911 _v _q 
  have p5008 := n5008 _v _q h4787
  have p5007 := n5007 _v _q h225
  have p17061 := n17061 _v _q h4747
  have p5006 := n5006 _v _q h4675
  have p5010 := n5010 _v _q h70
  have p4971 := n4971 _v _q h4419
  have p17137 := n17137 _v _q h4059
  have p4972 := n4972 _v _q h4899
  have p4978 := n4978 _v _q h4477
  have p4979 := n4979 _v _q h4139
  have p4980 := n4980 _v _q h4301
  have p5005 := n5005 _v _q h3169
  have p4973 := n4973 _v _q h4562
  have p4985 := n4985 _v _q h4156
  have p4987 := n4987 _v _q h4434
  have p4983 := n4983 _v _q h4813
  have p4988 := n4988 _v _q h488
  have p4981 := n4981 _v _q h4260
  have p4989 := n4989 _v _q h4838
  have p4986 := n4986 _v _q h3105
  have p253 := n253 _v _q h191
  have p4990 := n4990 _v _q h4648
  have p4984 := n4984 _v _q h4872
  have p4991 := n4991 _v _q h4608
  have p4992 := n4992 _v _q h442
  have p4977 := n4977 _v _q h4285
  have p4995 := n4995 _v _q h4369
  have p4994 := n4994 _v _q h3069
  have p4996 := n4996 _v _q h3937
  have p4999 := n4999 _v _q h91
  have p4998 := n4998 _v _q h3152
  have p5001 := n5001 _v _q h4096
  have p17056 := n17056 _v _q h3946
  have p17128 := n17128 _v _q h4491
  have p5003 := n5003 _v _q h4199
  have p4976 := n4976 _v _q h4546
  have p17076 := n17076 _v _q h3976
  simp only [e30, e35, e70, e75, e91, e95, e191, e192, e225, e230, e442, e443, e488, e493, e3069, e3074, e3105, e3106, e3152, e3156, e3169, e3170, e3937, e3942, e3946, e3947, e3976, e3981, e4026, e4031, e4059, e4064, e4096, e4097, e4139, e4140, e4156, e4157, e4199, e4200, e4220, e4221, e4260, e4261, e4285, e4286, e4301, e4302, e4369, e4370, e4419, e4420, e4434, e4435, e4477, e4481, e4491, e4496, e4546, e4547, e4562, e4563, e4608, e4609, e4648, e4649, e4675, e4676, e4747, e4752, e4787, e4788, e4813, e4814, e4838, e4839, e4872, e4873, e4899, e4900, e18341] at *
  tauto
theorem n18635 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4491 : (e4491 _v)) (h4546 : (e4546 _v)) (h4562 : (e4562 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) : (e7733 _v) := by
  have p16334 := n16334 _v _q 
  have p18634 := n18634 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h3976 h4059 h4096 h4139 h4156 h4199 h4260 h4285 h4301 h4369 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h4899
  simp only [e4218, e4219, e4220, e4221, e7733, e7734] at *
  tauto
theorem n18636 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2364 : (e2364 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h7935 : (e7935 _v)) (h8310 : (e8310 _v)) : (e2358 _v) := by
  have p15249 := n15249 _v _q 
  have p18633 := n18633 _v _q h70 h91 h225 h442 h488 h2364 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4156 h4199 h4260 h4306 h4369 h4398 h4434 h4608 h4675 h4747 h4787 h4813 h4872 h7935 h8310
  simp only [e2358, e7645, e7648, e7655, e7656, e7657, e7658, e10960] at *
  tauto
theorem n18637 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2364 : (e2364 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h7935 : (e7935 _v)) (h8310 : (e8310 _v)) : (e7640 _v) := by
  have p14828 := n14828 _v _q 
  have p18636 := n18636 _v _q h70 h91 h225 h442 h488 h2364 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4156 h4199 h4260 h4306 h4369 h4398 h4434 h4608 h4675 h4747 h4787 h4813 h4872 h7935 h8310
  simp only [e2358, e4139, e4140, e4141, e4142, e6571, e7634, e7640, e7643] at *
  tauto
theorem n18638 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4491 : (e4491 _v)) (h4546 : (e4546 _v)) (h4562 : (e4562 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) : (e7742 _v) := by
  have p14833 := n14833 _v _q 
  have p18635 := n18635 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h3976 h4059 h4096 h4139 h4156 h4199 h4260 h4285 h4301 h4369 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h4899
  simp only [e2132, e4218, e4219, e4220, e4221, e7733, e7739, e7742, e7744] at *
  tauto
theorem n18639 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4491 : (e4491 _v)) (h4546 : (e4546 _v)) (h4562 : (e4562 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) : (e6780 _v) := by
  have p10893 := n10893 _v _q 
  have p18638 := n18638 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h3976 h4059 h4096 h4139 h4156 h4199 h4260 h4285 h4301 h4369 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h4899
  have p10896 := n10896 _v _q 
  exact FloorCertificate.node_18639 (e2 _v) (e7 _v) (e9 _v) (e45 _v) (e110 _v) p10893 p18638 p10896
theorem n18640 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4491 : (e4491 _v)) (h4546 : (e4546 _v)) (h4562 : (e4562 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) : (e8408 _v) := by
  have p15435 := n15435 _v _q 
  have p18639 := n18639 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h3976 h4059 h4096 h4139 h4156 h4199 h4260 h4285 h4301 h4369 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h4899
  simp only [e2799, e6780, e8395, e8398, e8405, e8406, e8407, e8408, e11332] at *
  tauto
theorem n18641 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4491 : (e4491 _v)) (h4546 : (e4546 _v)) (h4562 : (e4562 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) : (e7754 _v) := by
  have p14942 := n14942 _v _q 
  have p18638 := n18638 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h3976 h4059 h4096 h4139 h4156 h4199 h4260 h4285 h4301 h4369 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h4899
  simp only [e2132, e7742, e7747, e7749, e7751, e7752, e7753, e7754, e11001] at *
  tauto
theorem n18642 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4491 : (e4491 _v)) (h4546 : (e4546 _v)) (h4562 : (e4562 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) : (e7749 _v) := by
  have p14941 := n14941 _v _q 
  have p18641 := n18641 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h3976 h4059 h4096 h4139 h4156 h4199 h4260 h4285 h4301 h4369 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h4899
  simp only [e7747, e7749, e7751, e7752, e7753, e7754, e8446] at *
  tauto
theorem n18643 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2364 : (e2364 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h7935 : (e7935 _v)) (h8310 : (e8310 _v)) : (e4139 _v) := by
  have p16281 := n16281 _v _q 
  have p18637 := n18637 _v _q h70 h91 h225 h442 h488 h2364 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4156 h4199 h4260 h4306 h4369 h4398 h4434 h4608 h4675 h4747 h4787 h4813 h4872 h7935 h8310
  simp only [e4139, e4140, e4141, e4142, e7634, e7635, e7640] at *
  tauto
theorem n18644 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4491 : (e4491 _v)) (h4546 : (e4546 _v)) (h4562 : (e4562 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) : (e8398 _v) := by
  have p11470 := n11470 _v _q 
  have p18640 := n18640 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h3976 h4059 h4096 h4139 h4156 h4199 h4260 h4285 h4301 h4369 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h4899
  simp only [e8395, e8398, e8405, e8406, e8407, e8408, e8462] at *
  tauto
theorem n18645 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4491 : (e4491 _v)) (h4546 : (e4546 _v)) (h4562 : (e4562 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) (h6531 : (e6531 _v)) : (e7489 _v) := by
  have p15463 := n15463 _v _q h6531
  have p5391 := n5391 _v _q 
  have p16911 := n16911 _v _q 
  have p11358 := n11358 _v _q h6531
  have p8663 := n8663 _v _q 
  have p16178 := n16178 _v _q 
  have p5257 := n5257 _v _q 
  have p16451 := n16451 _v _q h6531
  have p14849 := n14849 _v _q 
  have p16452 := n16452 _v _q h6531
  have p18638 := n18638 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h3976 h4059 h4096 h4139 h4156 h4199 h4260 h4285 h4301 h4369 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h4899
  have p17133 := n17133 _v _q 
  have p17093 := n17093 _v _q 
  have p13951 := n13951 _v _q 
  have p17141 := n17141 _v _q 
  have p17069 := n17069 _v _q 
  have p17131 := n17131 _v _q 
  have p18644 := n18644 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h3976 h4059 h4096 h4139 h4156 h4199 h4260 h4285 h4301 h4369 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h4899
  have p4972 := n4972 _v _q h4899
  have p4999 := n4999 _v _q h91
  have p5001 := n5001 _v _q h4096
  have p4996 := n4996 _v _q h3937
  have p4998 := n4998 _v _q h3152
  have p16181 := n16181 _v _q 
  have p4977 := n4977 _v _q h4285
  have p16913 := n16913 _v _q 
  have p17128 := n17128 _v _q h4491
  have p17136 := n17136 _v _q 
  have p5003 := n5003 _v _q h4199
  have p17053 := n17053 _v _q 
  have p18642 := n18642 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h3976 h4059 h4096 h4139 h4156 h4199 h4260 h4285 h4301 h4369 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h4899
  have p15480 := n15480 _v _q h6531
  have p17076 := n17076 _v _q h3976
  have p17056 := n17056 _v _q h3946
  have p17127 := n17127 _v _q 
  have p5008 := n5008 _v _q h4787
  have p5007 := n5007 _v _q h225
  have p17055 := n17055 _v _q 
  have p16778 := n16778 _v _q 
  have p17061 := n17061 _v _q h4747
  have p17147 := n17147 _v _q 
  have p17221 := n17221 _v _q 
  have p16994 := n16994 _v _q 
  have p18629 := n18629 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h3976 h4059 h4096 h4139 h4156 h4199 h4260 h4285 h4301 h4369 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h4899
  have p17137 := n17137 _v _q h4059
  have p5006 := n5006 _v _q h4675
  have p5010 := n5010 _v _q h70
  have p17064 := n17064 _v _q 
  have p4971 := n4971 _v _q h4419
  have p4976 := n4976 _v _q h4546
  have p16929 := n16929 _v _q 
  have p4978 := n4978 _v _q h4477
  have p4979 := n4979 _v _q h4139
  have p4980 := n4980 _v _q h4301
  have p5005 := n5005 _v _q h3169
  have p16394 := n16394 _v _q 
  have p4973 := n4973 _v _q h4562
  have p4985 := n4985 _v _q h4156
  have p4987 := n4987 _v _q h4434
  have p4983 := n4983 _v _q h4813
  have p16175 := n16175 _v _q 
  have p17074 := n17074 _v _q 
  have p4988 := n4988 _v _q h488
  have p4981 := n4981 _v _q h4260
  have p4989 := n4989 _v _q h4838
  have p17072 := n17072 _v _q 
  have p4986 := n4986 _v _q h3105
  have p17080 := n17080 _v _q 
  have p17078 := n17078 _v _q 
  have p17091 := n17091 _v _q 
  have p253 := n253 _v _q h191
  have p17098 := n17098 _v _q 
  have p4990 := n4990 _v _q h4648
  have p17100 := n17100 _v _q 
  have p4984 := n4984 _v _q h4872
  have p17067 := n17067 _v _q 
  have p17087 := n17087 _v _q 
  have p4991 := n4991 _v _q h4608
  have p4992 := n4992 _v _q h442
  have p17115 := n17115 _v _q 
  have p17083 := n17083 _v _q 
  have p17110 := n17110 _v _q 
  have p16576 := n16576 _v _q 
  have p17058 := n17058 _v _q 
  have p17113 := n17113 _v _q 
  have p17102 := n17102 _v _q 
  have p17096 := n17096 _v _q 
  have p17106 := n17106 _v _q 
  have p17122 := n17122 _v _q 
  have p17104 := n17104 _v _q 
  have p4995 := n4995 _v _q h4369
  have p17124 := n17124 _v _q 
  have p17108 := n17108 _v _q 
  have p4994 := n4994 _v _q h3069
  have p17117 := n17117 _v _q 
  have p17120 := n17120 _v _q 
  have p17151 := n17151 _v _q 
  exact FloorCertificate.node_18645 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e61 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2834 _v) (e2849 _v) (e2863 _v) (e2877 _v) (e2879 _v) (e2883 _v) (e2898 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2913 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e3164 _v) (e3262 _v) (e3574 _v) (e4215 _v) (e4324 _v) (e4541 _v) (e4696 _v) (e4808 _v) p15463 p5391 p16911 p11358 p8663 p16178 p5257 p16451 p14849 p16452 p18638 p17133 p17093 p13951 p17141 p17069 p17131 p18644 p4972 p4999 p5001 p4996 p4998 p16181 p4977 p16913 p17128 p17136 p5003 p17053 p18642 p15480 p17076 p17056 p17127 p5008 p5007 p17055 p16778 p17061 p17147 p17221 p16994 p18629 p17137 p5006 p5010 p17064 p4971 p4976 p16929 p4978 p4979 p4980 p5005 p16394 p4973 p4985 p4987 p4983 p16175 p17074 p4988 p4981 p4989 p17072 p4986 p17080 p17078 p17091 p253 p17098 p4990 p17100 p4984 p17067 p17087 p4991 p4992 p17115 p17083 p17110 p16576 p17058 p17113 p17102 p17096 p17106 p17122 p17104 p4995 p17124 p17108 p4994 p17117 p17120 p17151
theorem n18646 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2364 : (e2364 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4306 : (e4306 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h7935 : (e7935 _v)) (h8310 : (e8310 _v)) : (e7489 _v) := by
  have p18627 := n18627 _v _q h70 h91 h225 h442 h488 h2364 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4156 h4199 h4260 h4306 h4369 h4398 h4434 h4608 h4675 h4747 h4787 h4813 h4872 h7935 h8310
  have p18624 := n18624 _v _q h70 h91 h225 h442 h488 h2364 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4156 h4199 h4260 h4306 h4369 h4398 h4434 h4608 h4675 h4747 h4787 h4813 h4872 h7935 h8310
  have p5257 := n5257 _v _q 
  have p18630 := n18630 _v _q h8310
  have p13951 := n13951 _v _q 
  have p11384 := n11384 _v _q h8310
  have p18621 := n18621 _v _q h70 h91 h225 h442 h488 h2364 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4156 h4199 h4260 h4306 h4369 h4398 h4434 h4608 h4675 h4747 h4787 h4813 h4872 h7935 h8310
  have p17108 := n17108 _v _q 
  have p18614 := n18614 _v _q h70 h91 h225 h442 h488 h2364 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4156 h4199 h4260 h4306 h4369 h4398 h4434 h4608 h4675 h4747 h4787 h4813 h4872 h7935 h8310
  have p18643 := n18643 _v _q h70 h91 h225 h442 h488 h2364 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4156 h4199 h4260 h4306 h4369 h4398 h4434 h4608 h4675 h4747 h4787 h4813 h4872 h7935 h8310
  have p4994 := n4994 _v _q h3069
  have p17120 := n17120 _v _q 
  have p17113 := n17113 _v _q 
  have p17117 := n17117 _v _q 
  have p17124 := n17124 _v _q 
  have p17122 := n17122 _v _q 
  have p17163 := n17163 _v _q h7935
  have p4981 := n4981 _v _q h4260
  have p16977 := n16977 _v _q 
  have p5001 := n5001 _v _q h4096
  have p4999 := n4999 _v _q h91
  have p15606 := n15606 _v _q h8310
  have p5010 := n5010 _v _q h70
  have p5003 := n5003 _v _q h4199
  have p5007 := n5007 _v _q h225
  have p4992 := n4992 _v _q h442
  have p15608 := n15608 _v _q h8310
  have p17131 := n17131 _v _q 
  have p4996 := n4996 _v _q h3937
  have p15599 := n15599 _v _q h2364
  have p18616 := n18616 _v _q h70 h91 h225 h442 h488 h2364 h3069 h3105 h3152 h3937 h4096 h4156 h4199 h4260 h4369 h4608 h4675 h4787 h4813 h4872 h8310
  have p17133 := n17133 _v _q 
  have p17134 := n17134 _v _q h4398
  have p4987 := n4987 _v _q h4434
  have p17136 := n17136 _v _q 
  have p17453 := n17453 _v _q h8310
  have p17137 := n17137 _v _q h4059
  have p16778 := n16778 _v _q 
  have p17138 := n17138 _v _q h4306
  have p17440 := n17440 _v _q h2364
  have p15604 := n15604 _v _q h2364
  have p15248 := n15248 _v _q h8310
  have p4983 := n4983 _v _q h4813
  have p17053 := n17053 _v _q 
  have p17127 := n17127 _v _q 
  have p4995 := n4995 _v _q h4369
  have p4998 := n4998 _v _q h3152
  have p16576 := n16576 _v _q 
  have p15612 := n15612 _v _q h8310
  have p5008 := n5008 _v _q h4787
  have p17009 := n17009 _v _q 
  have p17055 := n17055 _v _q 
  have p15170 := n15170 _v _q h2364
  have p17058 := n17058 _v _q 
  have p5006 := n5006 _v _q h4675
  have p17056 := n17056 _v _q h3946
  have p17061 := n17061 _v _q h4747
  have p17147 := n17147 _v _q 
  have p17064 := n17064 _v _q 
  have p17089 := n17089 _v _q 
  have p17067 := n17067 _v _q 
  have p17072 := n17072 _v _q 
  have p17069 := n17069 _v _q 
  have p17074 := n17074 _v _q 
  have p4985 := n4985 _v _q h4156
  have p15567 := n15567 _v _q h2364
  have p16929 := n16929 _v _q 
  have p4988 := n4988 _v _q h488
  have p17080 := n17080 _v _q 
  have p17078 := n17078 _v _q 
  have p17141 := n17141 _v _q 
  have p17091 := n17091 _v _q 
  have p17093 := n17093 _v _q 
  have p4986 := n4986 _v _q h3105
  have p17111 := n17111 _v _q 
  have p4984 := n4984 _v _q h4872
  have p17083 := n17083 _v _q 
  have p4991 := n4991 _v _q h4608
  have p17087 := n17087 _v _q 
  have p17115 := n17115 _v _q 
  have p17100 := n17100 _v _q 
  have p17102 := n17102 _v _q 
  have p17098 := n17098 _v _q 
  have p17104 := n17104 _v _q 
  have p17110 := n17110 _v _q 
  have p17096 := n17096 _v _q 
  have p17106 := n17106 _v _q 
  exact FloorCertificate.node_18646 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e61 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2849 _v) (e2863 _v) (e2877 _v) (e2883 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p18627 p18624 p5257 p18630 p13951 p11384 p18621 p17108 p18614 p18643 p4994 p17120 p17113 p17117 p17124 p17122 p17163 p4981 p16977 p5001 p4999 p15606 p5010 p5003 p5007 p4992 p15608 p17131 p4996 p15599 p18616 p17133 p17134 p4987 p17136 p17453 p17137 p16778 p17138 p17440 p15604 p15248 p4983 p17053 p17127 p4995 p4998 p16576 p15612 p5008 p17009 p17055 p15170 p17058 p5006 p17056 p17061 p17147 p17064 p17089 p17067 p17072 p17069 p17074 p4985 p15567 p16929 p4988 p17080 p17078 p17141 p17091 p17093 p4986 p17111 p4984 p17083 p4991 p17087 p17115 p17100 p17102 p17098 p17104 p17110 p17096 p17106
theorem n18648 (_v : Vars) (_q : Query _v)  : (e18647 _v) := by
  by_contra hc
  change ¬ ((e2254 _v) ∨ (¬ (e4899 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4285 _v)) ∨ (¬ (e4491 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e3976 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4419 _v)) ∨ (¬ (e4546 _v)) ∨ (¬ (e4477 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e4301 _v)) ∨ (¬ (e3169 _v)) ∨ (¬ (e4562 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e4648 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e3069 _v))) at hc
  have h70 : (e70 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h191 : (e191 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))))
  have h225 : (e225 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h442 : (e442 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))))))))
  have h488 : (e488 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))
  have h3069 : (e3069 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))))))))))))))))))))))))))))))))))
  have h3105 : (e3105 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h3169 : (e3169 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h3946 : (e3946 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h3976 : (e3976 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h4059 : (e4059 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h4096 : (e4096 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4139 : (e4139 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))
  have h4156 : (e4156 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))
  have h4199 : (e4199 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h4260 : (e4260 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))
  have h4285 : (e4285 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h4301 : (e4301 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))
  have h4369 : (e4369 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))))))))
  have h4419 : (e4419 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))
  have h4434 : (e4434 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))
  have h4477 : (e4477 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))
  have h4491 : (e4491 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h4546 : (e4546 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))
  have h4562 : (e4562 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))
  have h4608 : (e4608 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))))))
  have h4648 : (e4648 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))))
  have h4675 : (e4675 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))
  have h4747 : (e4747 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))
  have h4838 : (e4838 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))
  have h4872 : (e4872 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))))))
  have h4899 : (e4899 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h6531 : (e6531 _v) := (fun hn => hc (Or.inl hn))
  have p18645 := n18645 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h3976 h4059 h4096 h4139 h4156 h4199 h4260 h4285 h4301 h4369 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h4899 h6531
  exact p18645
theorem n18650 (_v : Vars) (_q : Query _v)  : (e18649 _v) := by
  by_contra hc
  change ¬ ((e2529 _v) ∨ (¬ (e3069 _v)) ∨ (¬ (e7935 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e4398 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e2364 _v))) at hc
  have h70 : (e70 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h225 : (e225 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h442 : (e442 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h488 : (e488 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))
  have h2364 : (e2364 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))))))))))))))))))))))))
  have h3069 : (e3069 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h3105 : (e3105 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h3946 : (e3946 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))
  have h4059 : (e4059 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h4096 : (e4096 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4156 : (e4156 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))
  have h4199 : (e4199 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h4260 : (e4260 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h4369 : (e4369 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))
  have h4398 : (e4398 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h4434 : (e4434 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h4608 : (e4608 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))
  have h4675 : (e4675 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))
  have h4747 : (e4747 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))
  have h4872 : (e4872 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))
  have h7935 : (e7935 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h8310 : (e8310 _v) := (fun hn => hc (Or.inl hn))
  have p18646 := n18646 _v _q h70 h91 h225 h442 h488 h2364 h3069 h3105 h3152 h3937 h3946 h4059 h4096 h4156 h4199 h4260 h4306 h4369 h4398 h4434 h4608 h4675 h4747 h4787 h4813 h4872 h7935 h8310
  exact p18646
theorem n18651 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4491 : (e4491 _v)) (h4546 : (e4546 _v)) (h4562 : (e4562 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) : (e2254 _v) := by
  have p18648 := n18648 _v _q 
  have p17076 := n17076 _v _q h3976
  have p4999 := n4999 _v _q h91
  have p5001 := n5001 _v _q h4096
  have p4996 := n4996 _v _q h3937
  have p4998 := n4998 _v _q h3152
  have p4977 := n4977 _v _q h4285
  have p17128 := n17128 _v _q h4491
  have p5003 := n5003 _v _q h4199
  have p4972 := n4972 _v _q h4899
  have p17056 := n17056 _v _q h3946
  have p5008 := n5008 _v _q h4787
  have p5007 := n5007 _v _q h225
  have p17061 := n17061 _v _q h4747
  have p17137 := n17137 _v _q h4059
  have p5006 := n5006 _v _q h4675
  have p5010 := n5010 _v _q h70
  have p4971 := n4971 _v _q h4419
  have p4976 := n4976 _v _q h4546
  have p4978 := n4978 _v _q h4477
  have p4979 := n4979 _v _q h4139
  have p4980 := n4980 _v _q h4301
  have p5005 := n5005 _v _q h3169
  have p4973 := n4973 _v _q h4562
  have p4985 := n4985 _v _q h4156
  have p4987 := n4987 _v _q h4434
  have p4983 := n4983 _v _q h4813
  have p4988 := n4988 _v _q h488
  have p4981 := n4981 _v _q h4260
  have p4989 := n4989 _v _q h4838
  have p4986 := n4986 _v _q h3105
  have p253 := n253 _v _q h191
  have p4990 := n4990 _v _q h4648
  have p4984 := n4984 _v _q h4872
  have p4991 := n4991 _v _q h4608
  have p4992 := n4992 _v _q h442
  have p4995 := n4995 _v _q h4369
  have p4994 := n4994 _v _q h3069
  simp only [e70, e75, e91, e95, e191, e192, e225, e230, e442, e443, e488, e493, e2254, e3069, e3074, e3105, e3106, e3152, e3156, e3169, e3170, e3937, e3942, e3946, e3947, e3976, e3981, e4059, e4064, e4096, e4097, e4139, e4140, e4156, e4157, e4199, e4200, e4260, e4261, e4285, e4286, e4301, e4302, e4369, e4370, e4419, e4420, e4434, e4435, e4477, e4481, e4491, e4496, e4546, e4547, e4562, e4563, e4608, e4609, e4648, e4649, e4675, e4676, e4747, e4752, e4787, e4788, e4813, e4814, e4838, e4839, e4872, e4873, e4899, e4900, e18647] at *
  tauto
theorem n18652 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4491 : (e4491 _v)) (h4546 : (e4546 _v)) (h4562 : (e4562 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) : (e4731 _v) := by
  have p14698 := n14698 _v _q 
  have p18651 := n18651 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h3976 h4059 h4096 h4139 h4156 h4199 h4260 h4285 h4301 h4369 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h4899
  simp only [e2254, e4723, e4724, e4728, e4729, e4730, e4731, e6531, e8220] at *
  tauto
theorem n18653 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4491 : (e4491 _v)) (h4546 : (e4546 _v)) (h4562 : (e4562 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) : (e4724 _v) := by
  have p15518 := n15518 _v _q 
  have p18652 := n18652 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h3976 h4059 h4096 h4139 h4156 h4199 h4260 h4285 h4301 h4369 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h4899
  simp only [e4723, e4724, e4728, e4729, e4730, e4731, e4958] at *
  tauto
theorem n18654 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4491 : (e4491 _v)) (h4546 : (e4546 _v)) (h4562 : (e4562 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) (h6555 : (e6555 _v)) (h6636 : (e6636 _v)) : (e7489 _v) := by
  have p17120 := n17120 _v _q 
  have p18651 := n18651 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h3976 h4059 h4096 h4139 h4156 h4199 h4260 h4285 h4301 h4369 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h4899
  have p18653 := n18653 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h3976 h4059 h4096 h4139 h4156 h4199 h4260 h4285 h4301 h4369 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h4899
  have p11362 := n11362 _v _q h6555
  have p11031 := n11031 _v _q h6636
  have p16911 := n16911 _v _q 
  have p8663 := n8663 _v _q 
  have p16178 := n16178 _v _q 
  have p15329 := n15329 _v _q h6555
  have p14849 := n14849 _v _q 
  have p15443 := n15443 _v _q h6636
  have p18638 := n18638 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h3976 h4059 h4096 h4139 h4156 h4199 h4260 h4285 h4301 h4369 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h4899
  have p17133 := n17133 _v _q 
  have p17093 := n17093 _v _q 
  have p13951 := n13951 _v _q 
  have p17141 := n17141 _v _q 
  have p17069 := n17069 _v _q 
  have p17131 := n17131 _v _q 
  have p18644 := n18644 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h3976 h4059 h4096 h4139 h4156 h4199 h4260 h4285 h4301 h4369 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h4899
  have p4972 := n4972 _v _q h4899
  have p4999 := n4999 _v _q h91
  have p5001 := n5001 _v _q h4096
  have p4996 := n4996 _v _q h3937
  have p4998 := n4998 _v _q h3152
  have p16181 := n16181 _v _q 
  have p4977 := n4977 _v _q h4285
  have p16913 := n16913 _v _q 
  have p17128 := n17128 _v _q h4491
  have p17136 := n17136 _v _q 
  have p5003 := n5003 _v _q h4199
  have p17053 := n17053 _v _q 
  have p18642 := n18642 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h3976 h4059 h4096 h4139 h4156 h4199 h4260 h4285 h4301 h4369 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h4899
  have p16488 := n16488 _v _q h6636
  have p17076 := n17076 _v _q h3976
  have p17056 := n17056 _v _q h3946
  have p17127 := n17127 _v _q 
  have p5008 := n5008 _v _q h4787
  have p5007 := n5007 _v _q h225
  have p17055 := n17055 _v _q 
  have p16778 := n16778 _v _q 
  have p17061 := n17061 _v _q h4747
  have p17147 := n17147 _v _q 
  have p17221 := n17221 _v _q 
  have p16994 := n16994 _v _q 
  have p18629 := n18629 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h3976 h4059 h4096 h4139 h4156 h4199 h4260 h4285 h4301 h4369 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h4899
  have p17137 := n17137 _v _q h4059
  have p5006 := n5006 _v _q h4675
  have p5010 := n5010 _v _q h70
  have p17064 := n17064 _v _q 
  have p4971 := n4971 _v _q h4419
  have p4976 := n4976 _v _q h4546
  have p16929 := n16929 _v _q 
  have p4978 := n4978 _v _q h4477
  have p4979 := n4979 _v _q h4139
  have p4980 := n4980 _v _q h4301
  have p5005 := n5005 _v _q h3169
  have p16394 := n16394 _v _q 
  have p4973 := n4973 _v _q h4562
  have p4985 := n4985 _v _q h4156
  have p4987 := n4987 _v _q h4434
  have p4983 := n4983 _v _q h4813
  have p16175 := n16175 _v _q 
  have p17074 := n17074 _v _q 
  have p4988 := n4988 _v _q h488
  have p4981 := n4981 _v _q h4260
  have p4989 := n4989 _v _q h4838
  have p17072 := n17072 _v _q 
  have p4986 := n4986 _v _q h3105
  have p17080 := n17080 _v _q 
  have p17078 := n17078 _v _q 
  have p17091 := n17091 _v _q 
  have p253 := n253 _v _q h191
  have p17098 := n17098 _v _q 
  have p4990 := n4990 _v _q h4648
  have p17100 := n17100 _v _q 
  have p4984 := n4984 _v _q h4872
  have p17067 := n17067 _v _q 
  have p17087 := n17087 _v _q 
  have p4991 := n4991 _v _q h4608
  have p4992 := n4992 _v _q h442
  have p17115 := n17115 _v _q 
  have p17083 := n17083 _v _q 
  have p17110 := n17110 _v _q 
  have p16576 := n16576 _v _q 
  have p17058 := n17058 _v _q 
  have p17113 := n17113 _v _q 
  have p17102 := n17102 _v _q 
  have p17096 := n17096 _v _q 
  have p17106 := n17106 _v _q 
  have p17122 := n17122 _v _q 
  have p17104 := n17104 _v _q 
  have p4995 := n4995 _v _q h4369
  have p17124 := n17124 _v _q 
  have p17108 := n17108 _v _q 
  have p4994 := n4994 _v _q h3069
  have p17117 := n17117 _v _q 
  exact FloorCertificate.node_18654 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e61 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2834 _v) (e2849 _v) (e2863 _v) (e2877 _v) (e2879 _v) (e2883 _v) (e2898 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2913 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e3164 _v) (e3262 _v) (e3574 _v) (e4215 _v) (e4324 _v) (e4541 _v) (e4808 _v) p17120 p18651 p18653 p11362 p11031 p16911 p8663 p16178 p15329 p14849 p15443 p18638 p17133 p17093 p13951 p17141 p17069 p17131 p18644 p4972 p4999 p5001 p4996 p4998 p16181 p4977 p16913 p17128 p17136 p5003 p17053 p18642 p16488 p17076 p17056 p17127 p5008 p5007 p17055 p16778 p17061 p17147 p17221 p16994 p18629 p17137 p5006 p5010 p17064 p4971 p4976 p16929 p4978 p4979 p4980 p5005 p16394 p4973 p4985 p4987 p4983 p16175 p17074 p4988 p4981 p4989 p17072 p4986 p17080 p17078 p17091 p253 p17098 p4990 p17100 p4984 p17067 p17087 p4991 p4992 p17115 p17083 p17110 p16576 p17058 p17113 p17102 p17096 p17106 p17122 p17104 p4995 p17124 p17108 p4994 p17117
theorem n18656 (_v : Vars) (_q : Query _v)  : (e18655 _v) := by
  by_contra hc
  change ¬ ((e2310 _v) ∨ (e2482 _v) ∨ (¬ (e4899 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4285 _v)) ∨ (¬ (e4491 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e3976 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4419 _v)) ∨ (¬ (e4546 _v)) ∨ (¬ (e4477 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e4301 _v)) ∨ (¬ (e3169 _v)) ∨ (¬ (e4562 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e4648 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e3069 _v))) at hc
  have h70 : (e70 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h191 : (e191 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))))
  have h225 : (e225 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h442 : (e442 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))))))))
  have h488 : (e488 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))
  have h3069 : (e3069 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn)))))))))))))))))))))))))))))))))))))))
  have h3105 : (e3105 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h3169 : (e3169 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h3946 : (e3946 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h3976 : (e3976 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h4059 : (e4059 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))
  have h4096 : (e4096 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4139 : (e4139 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))
  have h4156 : (e4156 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))
  have h4199 : (e4199 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h4260 : (e4260 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))
  have h4285 : (e4285 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h4301 : (e4301 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))
  have h4369 : (e4369 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))))))))))
  have h4419 : (e4419 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))
  have h4434 : (e4434 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))
  have h4477 : (e4477 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))
  have h4491 : (e4491 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h4546 : (e4546 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))
  have h4562 : (e4562 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))
  have h4608 : (e4608 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))))))))
  have h4648 : (e4648 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))))))
  have h4675 : (e4675 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))
  have h4747 : (e4747 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))
  have h4838 : (e4838 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))
  have h4872 : (e4872 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))))))
  have h4899 : (e4899 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h6555 : (e6555 _v) := (fun hn => hc (Or.inl hn))
  have h6636 : (e6636 _v) := (fun hn => hc (Or.inr (Or.inl hn)))
  have p18654 := n18654 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h3976 h4059 h4096 h4139 h4156 h4199 h4260 h4285 h4301 h4369 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h4899 h6555 h6636
  exact p18654
theorem n18657 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4491 : (e4491 _v)) (h4546 : (e4546 _v)) (h4562 : (e4562 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) (h6636 : (e6636 _v)) : (e2310 _v) := by
  have p18656 := n18656 _v _q 
  have p11031 := n11031 _v _q h6636
  have p4972 := n4972 _v _q h4899
  have p4999 := n4999 _v _q h91
  have p5001 := n5001 _v _q h4096
  have p4996 := n4996 _v _q h3937
  have p4998 := n4998 _v _q h3152
  have p4977 := n4977 _v _q h4285
  have p17128 := n17128 _v _q h4491
  have p5003 := n5003 _v _q h4199
  have p17076 := n17076 _v _q h3976
  have p17056 := n17056 _v _q h3946
  have p5008 := n5008 _v _q h4787
  have p5007 := n5007 _v _q h225
  have p17061 := n17061 _v _q h4747
  have p17137 := n17137 _v _q h4059
  have p5006 := n5006 _v _q h4675
  have p5010 := n5010 _v _q h70
  have p4971 := n4971 _v _q h4419
  have p4976 := n4976 _v _q h4546
  have p4978 := n4978 _v _q h4477
  have p4979 := n4979 _v _q h4139
  have p4980 := n4980 _v _q h4301
  have p5005 := n5005 _v _q h3169
  have p4973 := n4973 _v _q h4562
  have p4985 := n4985 _v _q h4156
  have p4987 := n4987 _v _q h4434
  have p4983 := n4983 _v _q h4813
  have p4988 := n4988 _v _q h488
  have p4981 := n4981 _v _q h4260
  have p4989 := n4989 _v _q h4838
  have p4986 := n4986 _v _q h3105
  have p253 := n253 _v _q h191
  have p4990 := n4990 _v _q h4648
  have p4984 := n4984 _v _q h4872
  have p4991 := n4991 _v _q h4608
  have p4992 := n4992 _v _q h442
  have p4995 := n4995 _v _q h4369
  have p4994 := n4994 _v _q h3069
  simp only [e70, e75, e91, e95, e191, e192, e225, e230, e442, e443, e488, e493, e2310, e2482, e3069, e3074, e3105, e3106, e3152, e3156, e3169, e3170, e3937, e3942, e3946, e3947, e3976, e3981, e4059, e4064, e4096, e4097, e4139, e4140, e4156, e4157, e4199, e4200, e4260, e4261, e4285, e4286, e4301, e4302, e4369, e4370, e4419, e4420, e4434, e4435, e4477, e4481, e4491, e4496, e4546, e4547, e4562, e4563, e4608, e4609, e4648, e4649, e4675, e4676, e4747, e4752, e4787, e4788, e4813, e4814, e4838, e4839, e4872, e4873, e4899, e4900, e6636, e18655] at *
  tauto
theorem n18658 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4491 : (e4491 _v)) (h4546 : (e4546 _v)) (h4562 : (e4562 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) (h6636 : (e6636 _v)) : (e3278 _v) := by
  have p14378 := n14378 _v _q 
  have p18657 := n18657 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h3976 h4059 h4096 h4139 h4156 h4199 h4260 h4285 h4301 h4369 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h4899 h6636
  simp only [e2310, e3270, e3271, e3275, e3276, e3277, e3278, e6555, e6979] at *
  tauto
theorem n18659 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4491 : (e4491 _v)) (h4546 : (e4546 _v)) (h4562 : (e4562 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) (h6636 : (e6636 _v)) : (e3271 _v) := by
  have p6982 := n6982 _v _q 
  have p18658 := n18658 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h3976 h4059 h4096 h4139 h4156 h4199 h4260 h4285 h4301 h4369 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h4899 h6636
  simp only [e3270, e3271, e3275, e3276, e3277, e3278, e3288] at *
  tauto
end
end Assembly
