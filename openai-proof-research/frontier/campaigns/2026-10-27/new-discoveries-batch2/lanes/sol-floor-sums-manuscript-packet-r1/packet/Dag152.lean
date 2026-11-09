import Dag151
import generated.th_lemma_14
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n16513 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e4648 _v) := by
  have p15027 := n15027 _v _q 
  have p15575 := n15575 _v _q h6784
  simp only [e4648, e4649, e4650, e4651, e8149, e8150, e8157] at *
  tauto
theorem n16514 (_v : Vars) (_q : Query _v) (h2132 : (e2132 _v)) : (e5090 _v) := by
  have p14728 := n14728 _v _q 
  have p12940 := n12940 _v _q h2132
  simp only [e13, e28, e30, e34, e35, e5089, e5090, e5093, e5095] at *
  tauto
theorem n16515 (_v : Vars) (_q : Query _v) (h2132 : (e2132 _v)) : (e30 _v) := by
  have p16290 := n16290 _v _q 
  have p16514 := n16514 _v _q h2132
  simp only [e28, e30, e34, e35, e5089, e5090, e5107] at *
  tauto
theorem n16516 (_v : Vars) (_q : Query _v) (h4302 : (e4302 _v)) : (e4314 _v) := by
  have p14704 := n14704 _v _q 
  have p15579 := n15579 _v _q h4302
  simp only [e2585, e4306, e4307, e4311, e4312, e4313, e4314, e6676, e7836] at *
  tauto
theorem n16517 (_v : Vars) (_q : Query _v) (h4302 : (e4302 _v)) : (e4306 _v) := by
  have p14984 := n14984 _v _q 
  have p16516 := n16516 _v _q h4302
  simp only [e4306, e4307, e4311, e4312, e4313, e4314, e4964] at *
  tauto
theorem n16518 (_v : Vars) (_q : Query _v) (h6684 : (e6684 _v)) : (e5203 _v) := by
  have p14730 := n14730 _v _q 
  have p14114 := n14114 _v _q h6684
  simp only [e191, e192, e193, e194, e196, e5193, e5195, e5203, e5206] at *
  tauto
theorem n16519 (_v : Vars) (_q : Query _v) (h6758 : (e6758 _v)) : (e8307 _v) := by
  have p14906 := n14906 _v _q 
  have p14119 := n14119 _v _q h6758
  simp only [e2529, e4836, e4837, e4838, e4839, e8301, e8307, e8310, e8312] at *
  tauto
theorem n16520 (_v : Vars) (_q : Query _v) (h6758 : (e6758 _v)) : (e4838 _v) := by
  have p16285 := n16285 _v _q 
  have p16519 := n16519 _v _q h6758
  simp only [e4836, e4837, e4838, e4839, e8301, e8302, e8307] at *
  tauto
theorem n16521 (_v : Vars) (_q : Query _v) (h4302 : (e4302 _v)) : (e2482 _v) := by
  have p12579 := n12579 _v _q 
  have p15579 := n15579 _v _q h4302
  simp only [e2482, e2585, e6676, e12578] at *
  tauto
theorem n16522 (_v : Vars) (_q : Query _v) (h4302 : (e4302 _v)) : (e2139 _v) := by
  have p10892 := n10892 _v _q 
  have p16521 := n16521 _v _q h4302
  simp only [e2139, e2482, e6636, e10891] at *
  tauto
theorem n16523 (_v : Vars) (_q : Query _v) (h4302 : (e4302 _v)) : (e2377 _v) := by
  have p11382 := n11382 _v _q 
  have p16522 := n16522 _v _q h4302
  simp only [e2139, e2377, e6486, e11381] at *
  tauto
theorem n16524 (_v : Vars) (_q : Query _v) (h4302 : (e4302 _v)) : (e4755 _v) := by
  have p14687 := n14687 _v _q 
  have p16523 := n16523 _v _q h4302
  simp only [e2377, e4747, e4748, e4752, e4753, e4754, e4755, e6591, e8238] at *
  tauto
theorem n16525 (_v : Vars) (_q : Query _v) (h4302 : (e4302 _v)) : (e2805 _v) := by
  have p10899 := n10899 _v _q 
  have p16522 := n16522 _v _q h4302
  simp only [e2139, e2805, e6486, e10898] at *
  tauto
theorem n16526 (_v : Vars) (_q : Query _v) (h4302 : (e4302 _v)) : (e3954 _v) := by
  have p14486 := n14486 _v _q 
  have p16525 := n16525 _v _q h4302
  simp only [e2805, e3944, e3945, e3946, e3947, e3948, e3954, e6792, e7438] at *
  tauto
theorem n16527 (_v : Vars) (_q : Query _v) (h4302 : (e4302 _v)) : (e4405 _v) := by
  have p14702 := n14702 _v _q 
  have p16521 := n16521 _v _q h4302
  simp only [e2482, e4397, e4398, e4402, e4403, e4404, e4405, e6636, e7918] at *
  tauto
theorem n16528 (_v : Vars) (_q : Query _v) (h4302 : (e4302 _v)) : (e4398 _v) := by
  have p14976 := n14976 _v _q 
  have p16527 := n16527 _v _q h4302
  simp only [e4397, e4398, e4402, e4403, e4404, e4405, e4962] at *
  tauto
theorem n16530 (_v : Vars) (_q : Query _v)  : (e16529 _v) := by
  by_contra hc
  change ¬ ((¬ (e2592 _v)) ∨ (¬ (e2585 _v))) at hc
  have h2585 : (e2585 _v) := by
    tauto
  have h2592 : (e2592 _v) := by
    tauto
  have p11494 := n11494 _v _q h2585 h2592
  exact p11494
theorem n16531 (_v : Vars) (_q : Query _v) (h4302 : (e4302 _v)) : (e6672 _v) := by
  have p16530 := n16530 _v _q 
  have p15579 := n15579 _v _q h4302
  simp only [e2585, e2592, e6672, e6676, e16529] at *
  tauto
theorem n16532 (_v : Vars) (_q : Query _v) (h4302 : (e4302 _v)) : (e2364 _v) := by
  have p11343 := n11343 _v _q 
  have p15579 := n15579 _v _q h4302
  simp only [e2364, e2585, e6676, e11342] at *
  tauto
theorem n16533 (_v : Vars) (_q : Query _v) (h4302 : (e4302 _v)) : (e2254 _v) := by
  have p14710 := n14710 _v _q 
  have p16532 := n16532 _v _q h4302
  simp only [e2254, e2364, e6583, e14709] at *
  tauto
theorem n16534 (_v : Vars) (_q : Query _v) (h4302 : (e4302 _v)) : (e2793 _v) := by
  have p11476 := n11476 _v _q 
  have p16532 := n16532 _v _q h4302
  simp only [e2364, e2793, e6583, e11475] at *
  tauto
theorem n16535 (_v : Vars) (_q : Query _v) (h4302 : (e4302 _v)) : (e2746 _v) := by
  have p8429 := n8429 _v _q 
  have p16534 := n16534 _v _q h4302
  simp only [e2746, e2793, e6784, e8428] at *
  tauto
theorem n16536 (_v : Vars) (_q : Query _v) (h4302 : (e4302 _v)) : (e3984 _v) := by
  have p14691 := n14691 _v _q 
  have p16535 := n16535 _v _q h4302
  simp only [e2746, e3976, e3977, e3981, e3982, e3983, e3984, e6758, e7456] at *
  tauto
theorem n16537 (_v : Vars) (_q : Query _v) (h4302 : (e4302 _v)) : (e4910 _v) := by
  have p14701 := n14701 _v _q 
  have p16534 := n16534 _v _q h4302
  simp only [e2793, e4902, e4903, e4907, e4908, e4909, e4910, e6784, e8381] at *
  tauto
theorem n16538 (_v : Vars) (_q : Query _v) (h4302 : (e4302 _v)) : (e4903 _v) := by
  have p14973 := n14973 _v _q 
  have p16537 := n16537 _v _q h4302
  simp only [e4902, e4903, e4907, e4908, e4909, e4910, e4961] at *
  tauto
theorem n16539 (_v : Vars) (_q : Query _v) (h4302 : (e4302 _v)) : (e4661 _v) := by
  have p14686 := n14686 _v _q 
  have p16532 := n16532 _v _q h4302
  simp only [e2364, e4653, e4654, e4658, e4659, e4660, e4661, e6583, e8163] at *
  tauto
theorem n16540 (_v : Vars) (_q : Query _v) (h4302 : (e4302 _v)) : (e4653 _v) := by
  have p15168 := n15168 _v _q 
  have p16539 := n16539 _v _q h4302
  simp only [e4653, e4654, e4658, e4659, e4660, e4661, e4939] at *
  tauto
theorem n16541 (_v : Vars) (_q : Query _v) (h6758 : (e6758 _v)) : (e7640 _v) := by
  have p14828 := n14828 _v _q 
  have p14121 := n14121 _v _q h6758
  simp only [e2358, e4139, e4140, e4141, e4142, e6571, e7634, e7640, e7643] at *
  tauto
theorem n16542 (_v : Vars) (_q : Query _v) (h6758 : (e6758 _v)) : (e4139 _v) := by
  have p16281 := n16281 _v _q 
  have p16541 := n16541 _v _q h6758
  simp only [e4139, e4140, e4141, e4142, e7634, e7635, e7640] at *
  tauto
theorem n16543 (_v : Vars) (_q : Query _v) (h6758 : (e6758 _v)) : (e5203 _v) := by
  have p14730 := n14730 _v _q 
  have p14720 := n14720 _v _q h6758
  simp only [e191, e192, e193, e194, e196, e5193, e5195, e5203, e5206] at *
  tauto
theorem n16544 (_v : Vars) (_q : Query _v) (h6758 : (e6758 _v)) : (e191 _v) := by
  have p16442 := n16442 _v _q 
  have p16543 := n16543 _v _q h6758
  simp only [e191, e192, e193, e194, e5193, e5194, e5203] at *
  tauto
theorem n16545 (_v : Vars) (_q : Query _v) (h8395 : (e8395 _v)) : (e8395 _v) := by
  exact h8395
theorem n16546 (_v : Vars) (_q : Query _v) (h4897 : (e4897 _v)) (h8038 : (e8038 _v)) (h8310 : (e8310 _v)) (h8395 : (e8395 _v)) : (e4908 _v) := by
  have p5024 := n5024 _v _q h4897
  have p8602 := n8602 _v _q h8038
  have p8663 := n8663 _v _q 
  have p16545 := n16545 _v _q h8395
  have p5391 := n5391 _v _q 
  have p11384 := n11384 _v _q h8310
  exact FloorCertificate.node_16546 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) (e2913 _v) (e2996 _v) p5024 p8602 p8663 p16545 p5391 p11384
theorem n16547 (_v : Vars) (_q : Query _v) (h4897 : (e4897 _v)) (h8038 : (e8038 _v)) (h8310 : (e8310 _v)) (h8395 : (e8395 _v)) : (e7489 _v) := by
  have p14973 := n14973 _v _q 
  have p15615 := n15615 _v _q h8038 h8310
  have p16546 := n16546 _v _q h4897 h8038 h8310 h8395
  simp only [e4902, e4903, e4907, e4908, e4909, e4910, e4961] at *
  tauto
theorem n16548 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e7640 _v) := by
  have p14828 := n14828 _v _q 
  have p14122 := n14122 _v _q h6784
  simp only [e2358, e4139, e4140, e4141, e4142, e6571, e7634, e7640, e7643] at *
  tauto
theorem n16549 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e4139 _v) := by
  have p16281 := n16281 _v _q 
  have p16548 := n16548 _v _q h6784
  simp only [e4139, e4140, e4141, e4142, e7634, e7635, e7640] at *
  tauto
theorem n16550 (_v : Vars) (_q : Query _v) (h6636 : (e6636 _v)) : (e3169 _v) := by
  have p14769 := n14769 _v _q 
  have p15624 := n15624 _v _q h6636
  simp only [e3167, e3168, e3169, e3170, e6888, e6889, e6896] at *
  tauto
theorem n16551 (_v : Vars) (_q : Query _v) (h6636 : (e6636 _v)) : (e5203 _v) := by
  have p14730 := n14730 _v _q 
  have p14124 := n14124 _v _q h6636
  simp only [e191, e192, e193, e194, e196, e5193, e5195, e5203, e5206] at *
  tauto
theorem n16552 (_v : Vars) (_q : Query _v) (h6636 : (e6636 _v)) : (e191 _v) := by
  have p16442 := n16442 _v _q 
  have p16551 := n16551 _v _q h6636
  simp only [e191, e192, e193, e194, e5193, e5194, e5203] at *
  tauto
theorem n16553 (_v : Vars) (_q : Query _v) (h6636 : (e6636 _v)) : (e8307 _v) := by
  have p14906 := n14906 _v _q 
  have p14125 := n14125 _v _q h6636
  simp only [e2529, e4836, e4837, e4838, e4839, e8301, e8307, e8310, e8312] at *
  tauto
theorem n16554 (_v : Vars) (_q : Query _v) (h6636 : (e6636 _v)) : (e4838 _v) := by
  have p16285 := n16285 _v _q 
  have p16553 := n16553 _v _q h6636
  simp only [e4836, e4837, e4838, e4839, e8301, e8302, e8307] at *
  tauto
theorem n16555 (_v : Vars) (_q : Query _v) (h6531 : (e6531 _v)) : (e196 _v) := by
  have p12689 := n12689 _v _q 
  have p12865 := n12865 _v _q h6531
  simp only [e196, e2536, e6656, e12688] at *
  tauto
theorem n16556 (_v : Vars) (_q : Query _v) (h6531 : (e6531 _v)) : (e5203 _v) := by
  have p14730 := n14730 _v _q 
  have p16555 := n16555 _v _q h6531
  simp only [e191, e192, e193, e194, e196, e5193, e5195, e5203, e5206] at *
  tauto
theorem n16557 (_v : Vars) (_q : Query _v) (h6531 : (e6531 _v)) : (e191 _v) := by
  have p16442 := n16442 _v _q 
  have p16556 := n16556 _v _q h6531
  simp only [e191, e192, e193, e194, e5193, e5194, e5203] at *
  tauto
theorem n16558 (_v : Vars) (_q : Query _v) (h6531 : (e6531 _v)) : (e2529 _v) := by
  have p12781 := n12781 _v _q 
  have p12865 := n12865 _v _q h6531
  simp only [e2529, e2536, e6656, e12780] at *
  tauto
end
end Assembly
