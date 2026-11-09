import Dag178
import generated.th_lemma_18
import generated.th_lemma_19
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n17868 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h196 : (e196 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2781 : (e2781 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5100 : (e5100 _v)) (h7749 : (e7749 _v)) (h8038 : (e8038 _v)) (h8045 : (e8045 _v)) : (e4686 _v) := by
  have p14708 := n14708 _v _q 
  have p17841 := n17841 _v _q h91 h196 h225 h442 h488 h2781 h3069 h3105 h3152 h3937 h3946 h3976 h4156 h4199 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4838 h4872 h4903 h5100 h7749 h8038 h8045
  simp only [e2242, e4678, e4679, e4683, e4684, e4685, e4686, e6525, e8180] at *
  tauto
theorem n17869 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h196 : (e196 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2781 : (e2781 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5100 : (e5100 _v)) (h7749 : (e7749 _v)) (h8038 : (e8038 _v)) (h8045 : (e8045 _v)) : (e7489 _v) := by
  have p14989 := n14989 _v _q 
  have p17868 := n17868 _v _q h91 h196 h225 h442 h488 h2781 h3069 h3105 h3152 h3937 h3946 h3976 h4156 h4199 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4838 h4872 h4903 h5100 h7749 h8038 h8045
  have p17842 := n17842 _v _q h91 h196 h225 h442 h488 h2781 h3069 h3105 h3152 h3937 h3946 h3976 h4156 h4199 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4838 h4872 h4903 h5100 h7749 h8038 h8045
  simp only [e4678, e4679, e4683, e4684, e4685, e4686, e4967] at *
  tauto
theorem n17871 (_v : Vars) (_q : Query _v)  : (e17870 _v) := by
  by_contra hc
  change ¬ ((¬ (e4838 _v)) ∨ (e2475 _v) ∨ (¬ (e4813 _v)) ∨ (¬ (e196 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e4903 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e7749 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e8045 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e3976 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e5100 _v)) ∨ (¬ (e2781 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e4608 _v))) at hc
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h196 : (e196 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h225 : (e225 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h442 : (e442 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h488 : (e488 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))
  have h2781 : (e2781 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))
  have h3069 : (e3069 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))
  have h3105 : (e3105 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h3946 : (e3946 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h3976 : (e3976 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))
  have h4156 : (e4156 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))
  have h4199 : (e4199 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4369 : (e4369 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))
  have h4434 : (e4434 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))
  have h4608 : (e4608 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))))))))))))))))))))))))
  have h4675 : (e4675 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))
  have h4747 : (e4747 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4838 : (e4838 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h4872 : (e4872 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))
  have h4903 : (e4903 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h5100 : (e5100 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))
  have h7749 : (e7749 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h8038 : (e8038 _v) := (fun hn => hc (Or.inr (Or.inl hn)))
  have h8045 : (e8045 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have p17869 := n17869 _v _q h91 h196 h225 h442 h488 h2781 h3069 h3105 h3152 h3937 h3946 h3976 h4156 h4199 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4838 h4872 h4903 h5100 h7749 h8038 h8045
  exact p17869
theorem n17872 (_v : Vars) (_q : Query _v)  : (e2377 _v) := by
  by_contra hc
  change ¬ (e2377 _v) at hc
  have h6591 : (e6591 _v) := (fun hn => hc hn)
  have p17844 := n17844 _v _q h6591
  exact p17844
theorem n17873 (_v : Vars) (_q : Query _v)  : (e4755 _v) := by
  have p14687 := n14687 _v _q 
  have p17872 := n17872 _v _q 
  simp only [e2377, e4747, e4748, e4752, e4753, e4754, e4755, e6591, e8238] at *
  tauto
theorem n17874 (_v : Vars) (_q : Query _v)  : (e4747 _v) := by
  have p14920 := n14920 _v _q 
  have p17873 := n17873 _v _q 
  simp only [e4747, e4748, e4752, e4753, e4754, e4755, e4940] at *
  tauto
theorem n17875 (_v : Vars) (_q : Query _v) (h225 : (e225 _v)) (h488 : (e488 _v)) (h2061 : (e2061 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3271 : (e3271 _v)) (h3855 : (e3855 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4491 : (e4491 _v)) (h4653 : (e4653 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5100 : (e5100 _v)) (h6571 : (e6571 _v)) (h6700 : (e6700 _v)) (h7493 : (e7493 _v)) (h7749 : (e7749 _v)) (h8045 : (e8045 _v)) (h8310 : (e8310 _v)) : (e7489 _v) := by
  have p17845 := n17845 _v _q h225 h488 h2061 h3069 h3105 h3152 h3271 h3855 h3937 h3946 h3976 h4059 h4096 h4156 h4260 h4369 h4398 h4491 h4653 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h6571 h6700 h7493 h7749 h8045 h8310
  have p17155 := n17155 _v _q h7493
  have p17659 := n17659 _v _q h225 h488 h2061 h3069 h3105 h3152 h3271 h3855 h3937 h3946 h3976 h4059 h4096 h4156 h4260 h4369 h4398 h4491 h4653 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h6571 h6700 h7493 h8045 h8310
  have p5001 := n5001 _v _q h4096
  have p11409 := n11409 _v _q h2061
  have p11027 := n11027 _v _q h6700
  have p17658 := n17658 _v _q h6571 h8310
  have p15217 := n15217 _v _q h2061
  have p17056 := n17056 _v _q h3946
  have p17165 := n17165 _v _q h3271
  have p16803 := n16803 _v _q h6700
  have p17159 := n17159 _v _q h5100
  have p17129 := n17129 _v _q h4903
  have p16352 := n16352 _v _q h6700
  have p17076 := n17076 _v _q h3976
  have p17147 := n17147 _v _q 
  have p5007 := n5007 _v _q h225
  have p5008 := n5008 _v _q h4787
  have p17133 := n17133 _v _q 
  have p15234 := n15234 _v _q h6700
  have p15237 := n15237 _v _q h2061
  have p16353 := n16353 _v _q h6700
  have p4981 := n4981 _v _q h4260
  have p17759 := n17759 _v _q h2061 h8310
  have p17157 := n17157 _v _q h8045
  have p17061 := n17061 _v _q h4747
  have p4988 := n4988 _v _q h488
  have p4986 := n4986 _v _q h3105
  have p16175 := n16175 _v _q 
  have p4983 := n4983 _v _q h4813
  have p17094 := n17094 _v _q h4724
  have p4994 := n4994 _v _q h3069
  have p16804 := n16804 _v _q h6700
  have p4984 := n4984 _v _q h4872
  have p4985 := n4985 _v _q h4156
  have p17080 := n17080 _v _q 
  have p17134 := n17134 _v _q h4398
  have p17074 := n17074 _v _q 
  have p17078 := n17078 _v _q 
  have p17072 := n17072 _v _q 
  have p17098 := n17098 _v _q 
  have p17091 := n17091 _v _q 
  have p17087 := n17087 _v _q 
  have p17115 := n17115 _v _q 
  have p17110 := n17110 _v _q 
  have p17067 := n17067 _v _q 
  have p17100 := n17100 _v _q 
  have p16358 := n16358 _v _q h6700
  have p17058 := n17058 _v _q 
  have p17083 := n17083 _v _q 
  have p16576 := n16576 _v _q 
  have p17113 := n17113 _v _q 
  have p17064 := n17064 _v _q 
  have p17102 := n17102 _v _q 
  have p16250 := n16250 _v _q h3855
  have p17656 := n17656 _v _q h6571
  have p17096 := n17096 _v _q 
  have p17122 := n17122 _v _q 
  have p17060 := n17060 _v _q h4653
  have p17657 := n17657 _v _q h6571 h8310
  have p17108 := n17108 _v _q 
  have p17124 := n17124 _v _q 
  have p15258 := n15258 _v _q h2061
  have p17117 := n17117 _v _q 
  have p17104 := n17104 _v _q 
  have p17131 := n17131 _v _q 
  have p17106 := n17106 _v _q 
  have p4998 := n4998 _v _q h3152
  have p4995 := n4995 _v _q h4369
  have p17120 := n17120 _v _q 
  have p17069 := n17069 _v _q 
  have p17128 := n17128 _v _q h4491
  have p4996 := n4996 _v _q h3937
  have p17141 := n17141 _v _q 
  have p17093 := n17093 _v _q 
  have p15248 := n15248 _v _q h8310
  have p17053 := n17053 _v _q 
  have p17137 := n17137 _v _q h4059
  have p16805 := n16805 _v _q h6700
  have p17136 := n17136 _v _q 
  have p17127 := n17127 _v _q 
  have p15251 := n15251 _v _q h6571
  have p17055 := n17055 _v _q 
  have p13951 := n13951 _v _q 
  have p8447 := n8447 _v _q h6571
  have p5257 := n5257 _v _q 
  have p17697 := n17697 _v _q h225 h488 h2061 h3069 h3105 h3152 h3271 h3855 h3937 h3946 h3976 h4059 h4096 h4156 h4260 h4369 h4398 h4491 h4653 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h6571 h6700 h7493 h8045 h8310
  have p16269 := n16269 _v _q h7749
  exact FloorCertificate.node_17875 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e61 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2863 _v) (e2877 _v) (e2883 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e3164 _v) (e4215 _v) (e4541 _v) (e4808 _v) p17845 p17155 p17659 p5001 p11409 p11027 p17658 p15217 p17056 p17165 p16803 p17159 p17129 p16352 p17076 p17147 p5007 p5008 p17133 p15234 p15237 p16353 p4981 p17759 p17157 p17061 p4988 p4986 p16175 p4983 p17094 p4994 p16804 p4984 p4985 p17080 p17134 p17074 p17078 p17072 p17098 p17091 p17087 p17115 p17110 p17067 p17100 p16358 p17058 p17083 p16576 p17113 p17064 p17102 p16250 p17656 p17096 p17122 p17060 p17657 p17108 p17124 p15258 p17117 p17104 p17131 p17106 p4998 p4995 p17120 p17069 p17128 p4996 p17141 p17093 p15248 p17053 p17137 p16805 p17136 p17127 p15251 p17055 p13951 p8447 p5257 p17697 p16269
theorem n17877 (_v : Vars) (_q : Query _v)  : (e17876 _v) := by
  by_contra hc
  change ¬ ((¬ (e2358 _v)) ∨ (e2475 _v) ∨ (¬ (e2125 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e4903 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e3976 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e3169 _v)) ∨ (¬ (e4567 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e91 _v)) ∨ (e2634 _v)) at hc
  have h70 : (e70 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))
  have h191 : (e191 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h225 : (e225 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h442 : (e442 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))
  have h488 : (e488 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))
  have h2125 : (e2125 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h2358 : (e2358 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h3069 : (e3069 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))
  have h3105 : (e3105 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))
  have h3169 : (e3169 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))
  have h3976 : (e3976 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h4096 : (e4096 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4156 : (e4156 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))
  have h4199 : (e4199 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h4260 : (e4260 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h4369 : (e4369 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))
  have h4567 : (e4567 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h4608 : (e4608 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))
  have h4675 : (e4675 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))
  have h4872 : (e4872 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))
  have h4903 : (e4903 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h6700 : (e6700 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))))))))))))))))))))))))
  have h8038 : (e8038 _v) := (fun hn => hc (Or.inr (Or.inl hn)))
  have p17848 := n17848 _v _q h70 h91 h191 h225 h442 h488 h2125 h2358 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4567 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  exact p17848
theorem n17878 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3976 : (e3976 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4572 : (e4572 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h6656 : (e6656 _v)) (h7935 : (e7935 _v)) (h8038 : (e8038 _v)) : (e7807 _v) := by
  have p14837 := n14837 _v _q 
  have p17850 := n17850 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4572 h4608 h4648 h4675 h4787 h4813 h4838 h4872 h4903 h6656 h7935 h8038
  simp only [e2303, e4283, e4284, e4285, e4286, e7798, e7804, e7807, e7809] at *
  tauto
theorem n17879 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3976 : (e3976 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4572 : (e4572 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h6656 : (e6656 _v)) (h7935 : (e7935 _v)) (h8038 : (e8038 _v)) : (e7819 _v) := by
  have p14994 := n14994 _v _q 
  have p17878 := n17878 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4572 h4608 h4648 h4675 h4787 h4813 h4838 h4872 h4903 h6656 h7935 h8038
  simp only [e2303, e7807, e7812, e7814, e7816, e7817, e7818, e7819, e11046] at *
  tauto
theorem n17880 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3976 : (e3976 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4572 : (e4572 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h6656 : (e6656 _v)) (h7935 : (e7935 _v)) (h8038 : (e8038 _v)) : (e7814 _v) := by
  have p15221 := n15221 _v _q 
  have p17879 := n17879 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4139 h4156 h4199 h4260 h4301 h4369 h4572 h4608 h4648 h4675 h4787 h4813 h4838 h4872 h4903 h6656 h7935 h8038
  simp only [e7812, e7814, e7816, e7817, e7818, e7819, e8456] at *
  tauto
theorem n17881 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h225 : (e225 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h4096 : (e4096 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h8038 : (e8038 _v)) : (e2793 _v) := by
  have p17852 := n17852 _v _q 
  have p8602 := n8602 _v _q h8038
  have p4986 := n4986 _v _q h3105
  have p4983 := n4983 _v _q h4813
  have p4994 := n4994 _v _q h3069
  have p4984 := n4984 _v _q h4872
  have p4991 := n4991 _v _q h4608
  have p4988 := n4988 _v _q h488
  have p4998 := n4998 _v _q h3152
  have p4995 := n4995 _v _q h4369
  have p4999 := n4999 _v _q h91
  have p5001 := n5001 _v _q h4096
  have p4989 := n4989 _v _q h4838
  have p4996 := n4996 _v _q h3937
  have p5007 := n5007 _v _q h225
  have p4987 := n4987 _v _q h4434
  have p5008 := n5008 _v _q h4787
  simp only [e91, e95, e225, e230, e488, e493, e2475, e2793, e3069, e3074, e3105, e3106, e3152, e3156, e3937, e3942, e4096, e4097, e4369, e4370, e4434, e4435, e4608, e4609, e4787, e4788, e4813, e4814, e4838, e4839, e4872, e4873, e8038, e17851] at *
  tauto
theorem n17882 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4491 : (e4491 _v)) (h4546 : (e4546 _v)) (h4562 : (e4562 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h5093 : (e5093 _v)) (h6636 : (e6636 _v)) : (e6784 _v) := by
  have p14701 := n14701 _v _q 
  have p17853 := n17853 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h3976 h4059 h4096 h4139 h4156 h4199 h4260 h4285 h4301 h4369 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h5093 h6636
  simp only [e2793, e4902, e4903, e4907, e4908, e4909, e4910, e6784, e8381] at *
  tauto
theorem n17883 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4491 : (e4491 _v)) (h4546 : (e4546 _v)) (h4562 : (e4562 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) (h5093 : (e5093 _v)) (h6636 : (e6636 _v)) : (e7489 _v) := by
  have p17225 := n17225 _v _q h5093
  have p5255 := n5255 _v _q 
  have p11440 := n11440 _v _q h5093
  have p4972 := n4972 _v _q h4899
  have p4999 := n4999 _v _q h91
  have p14849 := n14849 _v _q 
  have p15443 := n15443 _v _q h6636
  have p5001 := n5001 _v _q h4096
  have p4996 := n4996 _v _q h3937
  have p13951 := n13951 _v _q 
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
  have p17802 := n17802 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h3976 h4059 h4096 h4156 h4199 h4260 h4301 h4369 h4434 h4477 h4491 h4562 h4608 h4648 h4675 h4747 h4787 h4813 h4872 h5093 h6636
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
  have p17069 := n17069 _v _q 
  have p17133 := n17133 _v _q 
  have p17093 := n17093 _v _q 
  have p17141 := n17141 _v _q 
  have p17131 := n17131 _v _q 
  have p8663 := n8663 _v _q 
  have p11031 := n11031 _v _q h6636
  have p10893 := n10893 _v _q 
  have p17882 := n17882 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h3976 h4059 h4096 h4139 h4156 h4199 h4260 h4285 h4301 h4369 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h5093 h6636
  exact FloorCertificate.node_17883 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e61 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2834 _v) (e2849 _v) (e2863 _v) (e2877 _v) (e2879 _v) (e2883 _v) (e2898 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2913 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e3164 _v) (e3574 _v) (e4215 _v) (e4324 _v) (e4541 _v) (e4808 _v) p17225 p5255 p11440 p4972 p4999 p14849 p15443 p5001 p4996 p13951 p4998 p16181 p4977 p16913 p17128 p17136 p5003 p17053 p17772 p17497 p17076 p17056 p17802 p17127 p5008 p5007 p17055 p16778 p17061 p17147 p17221 p16994 p17222 p17223 p15321 p17137 p5006 p5010 p17064 p4971 p4976 p16929 p4978 p4979 p4980 p5005 p16394 p4973 p4985 p4987 p4983 p16175 p17074 p4988 p4981 p4989 p17072 p4986 p17080 p17078 p17091 p253 p17098 p4990 p17100 p4984 p17067 p17087 p4991 p4992 p17115 p17083 p17110 p16576 p17058 p17113 p17102 p17096 p17106 p17122 p17104 p4995 p17124 p17108 p4994 p17117 p17120 p17069 p17133 p17093 p17141 p17131 p8663 p11031 p10893 p17882
theorem n17884 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2592 : (e2592 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3585 : (e3585 _v)) (h3855 : (e3855 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4026 : (e4026 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4128 : (e4128 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4220 : (e4220 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4491 : (e4491 _v)) (h4546 : (e4546 _v)) (h4562 : (e4562 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4855 : (e4855 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) (h6579 : (e6579 _v)) (h8398 : (e8398 _v)) : (e4394 _v) := by
  have p14852 := n14852 _v _q 
  have p17855 := n17855 _v _q h30 h70 h91 h191 h225 h442 h488 h2592 h3069 h3105 h3152 h3169 h3585 h3855 h3937 h3946 h3976 h4026 h4059 h4096 h4128 h4139 h4156 h4199 h4220 h4260 h4285 h4301 h4369 h4398 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4724 h4747 h4787 h4813 h4838 h4855 h4872 h4899 h6579 h8398
  simp only [e4392, e4393, e4394, e4395, e7904, e7905, e7912] at *
  tauto
theorem n17885 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2536 : (e2536 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3855 : (e3855 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4026 : (e4026 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4220 : (e4220 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4491 : (e4491 _v)) (h4546 : (e4546 _v)) (h4562 : (e4562 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) (h6672 : (e6672 _v)) : (e6724 _v) := by
  have p17857 := n17857 _v _q 
  have p11401 := n11401 _v _q h6672
  have p11132 := n11132 _v _q h2536
  have p17134 := n17134 _v _q h4398
  have p4978 := n4978 _v _q h4477
  have p4979 := n4979 _v _q h4139
  have p4980 := n4980 _v _q h4301
  have p5005 := n5005 _v _q h3169
  have p4973 := n4973 _v _q h4562
  have p4985 := n4985 _v _q h4156
  have p4987 := n4987 _v _q h4434
  have p4983 := n4983 _v _q h4813
  have p4975 := n4975 _v _q h4026
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
  have p16250 := n16250 _v _q h3855
  have p5001 := n5001 _v _q h4096
  have p5000 := n5000 _v _q h30
  have p17128 := n17128 _v _q h4491
  have p5003 := n5003 _v _q h4199
  have p5004 := n5004 _v _q h4220
  have p17076 := n17076 _v _q h3976
  have p17056 := n17056 _v _q h3946
  have p5007 := n5007 _v _q h225
  have p5008 := n5008 _v _q h4787
  have p17061 := n17061 _v _q h4747
  have p5010 := n5010 _v _q h70
  have p17137 := n17137 _v _q h4059
  have p5006 := n5006 _v _q h4675
  have p17094 := n17094 _v _q h4724
  have p4971 := n4971 _v _q h4419
  have p4972 := n4972 _v _q h4899
  have p4976 := n4976 _v _q h4546
  simp only [e30, e35, e70, e75, e91, e95, e191, e192, e225, e230, e442, e443, e488, e493, e2536, e2592, e2691, e3069, e3074, e3105, e3106, e3152, e3156, e3169, e3170, e3855, e3860, e3937, e3942, e3946, e3947, e3976, e3981, e4026, e4031, e4059, e4064, e4096, e4097, e4139, e4140, e4156, e4157, e4199, e4200, e4220, e4221, e4260, e4261, e4285, e4286, e4301, e4302, e4369, e4370, e4398, e4403, e4419, e4420, e4434, e4435, e4477, e4481, e4491, e4496, e4546, e4547, e4562, e4563, e4608, e4609, e4648, e4649, e4675, e4676, e4724, e4729, e4747, e4752, e4787, e4788, e4813, e4814, e4838, e4839, e4872, e4873, e4899, e4900, e6656, e6672, e6724, e17856] at *
  tauto
theorem n17886 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2536 : (e2536 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3855 : (e3855 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4026 : (e4026 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4220 : (e4220 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4491 : (e4491 _v)) (h4546 : (e4546 _v)) (h4562 : (e4562 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) (h6672 : (e6672 _v)) : (e7517 _v) := by
  have p15196 := n15196 _v _q 
  have p17885 := n17885 _v _q h30 h70 h91 h191 h225 h442 h488 h2536 h3069 h3105 h3152 h3169 h3855 h3937 h3946 h3976 h4026 h4059 h4096 h4139 h4156 h4199 h4220 h4260 h4285 h4301 h4369 h4398 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4724 h4747 h4787 h4813 h4838 h4872 h4899 h6672
  simp only [e2691, e6724, e7493, e7494, e7495, e7496, e7497, e7517, e10904] at *
  tauto
theorem n17888 (_v : Vars) (_q : Query _v)  : (e17887 _v) := by
  have p17859 := n17859 _v _q 
  have p16913 := n16913 _v _q 
  simp only [e30, e35, e70, e75, e91, e95, e191, e192, e225, e230, e442, e443, e488, e493, e2254, e3069, e3074, e3105, e3106, e3152, e3156, e3169, e3170, e3267, e3268, e3585, e3589, e3855, e3860, e3937, e3942, e3946, e3947, e3976, e3981, e4026, e4031, e4059, e4064, e4096, e4097, e4128, e4133, e4139, e4140, e4156, e4157, e4199, e4200, e4220, e4221, e4260, e4261, e4285, e4286, e4301, e4302, e4369, e4370, e4398, e4403, e4419, e4420, e4434, e4435, e4477, e4481, e4491, e4496, e4546, e4547, e4562, e4563, e4608, e4609, e4648, e4649, e4675, e4676, e4724, e4729, e4747, e4752, e4787, e4788, e4813, e4814, e4838, e4839, e4855, e4856, e4872, e4873, e4899, e4900, e17858, e17887] at *
  tauto
theorem n17889 (_v : Vars) (_q : Query _v)  : (e8502 _v) := by
  simp only [e3849, e3850, e3851, e3852, e7350, e8502] at *
  tauto
theorem n17890 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4026 : (e4026 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4220 : (e4220 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4491 : (e4491 _v)) (h4546 : (e4546 _v)) (h4562 : (e4562 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) (h6531 : (e6531 _v)) : (e7350 _v) := by
  have p17889 := n17889 _v _q 
  have p17861 := n17861 _v _q h30 h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h3976 h4026 h4059 h4096 h4139 h4156 h4199 h4220 h4260 h4285 h4301 h4369 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h4899 h6531
  simp only [e3849, e3850, e3851, e3852, e7350, e8502] at *
  tauto
theorem n17891 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4026 : (e4026 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4220 : (e4220 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4491 : (e4491 _v)) (h4546 : (e4546 _v)) (h4562 : (e4562 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) (h6531 : (e6531 _v)) : (e2139 _v) := by
  have p14471 := n14471 _v _q 
  have p17890 := n17890 _v _q h30 h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h3976 h4026 h4059 h4096 h4139 h4156 h4199 h4220 h4260 h4285 h4301 h4369 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h4899 h6531
  simp only [e2139, e3849, e3850, e3851, e3852, e7350, e7358, e7361] at *
  tauto
theorem n17892 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4026 : (e4026 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4220 : (e4220 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4491 : (e4491 _v)) (h4546 : (e4546 _v)) (h4562 : (e4562 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) (h6531 : (e6531 _v)) : (e3862 _v) := by
  have p14472 := n14472 _v _q 
  have p17891 := n17891 _v _q h30 h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h3976 h4026 h4059 h4096 h4139 h4156 h4199 h4220 h4260 h4285 h4301 h4369 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h4899 h6531
  simp only [e2139, e3854, e3855, e3859, e3860, e3861, e3862, e6486, e7364] at *
  tauto
theorem n17893 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4026 : (e4026 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4220 : (e4220 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4491 : (e4491 _v)) (h4546 : (e4546 _v)) (h4562 : (e4562 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) (h6531 : (e6531 _v)) : (e4924 _v) := by
  have p16462 := n16462 _v _q 
  have p17862 := n17862 _v _q h30 h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h3976 h4026 h4059 h4096 h4139 h4156 h4199 h4220 h4260 h4285 h4301 h4369 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h4899 h6531
  simp only [e4922, e4923, e4924, e4925, e8384, e8385, e8390] at *
  tauto
theorem n17894 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4026 : (e4026 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4220 : (e4220 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4491 : (e4491 _v)) (h4546 : (e4546 _v)) (h4562 : (e4562 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) (h6531 : (e6531 _v)) : (e2592 _v) := by
  have p11404 := n11404 _v _q 
  have p17863 := n17863 _v _q h30 h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h3976 h4026 h4059 h4096 h4139 h4156 h4199 h4220 h4260 h4285 h4301 h4369 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h4899 h6531
  simp only [e2371, e2592, e6579, e11403] at *
  tauto
theorem n17895 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4026 : (e4026 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4220 : (e4220 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4491 : (e4491 _v)) (h4546 : (e4546 _v)) (h4562 : (e4562 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) (h6531 : (e6531 _v)) : (e8330 _v) := by
  have p14907 := n14907 _v _q 
  have p17894 := n17894 _v _q h30 h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h3976 h4026 h4059 h4096 h4139 h4156 h4199 h4220 h4260 h4285 h4301 h4369 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h4899 h6531
  simp only [e2592, e4855, e4856, e4857, e4858, e6672, e8324, e8330, e8333] at *
  tauto
theorem n17896 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4026 : (e4026 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4220 : (e4220 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4491 : (e4491 _v)) (h4546 : (e4546 _v)) (h4562 : (e4562 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) (h6531 : (e6531 _v)) : (e4855 _v) := by
  have p16317 := n16317 _v _q 
  have p17895 := n17895 _v _q h30 h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h3976 h4026 h4059 h4096 h4139 h4156 h4199 h4220 h4260 h4285 h4301 h4369 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h4899 h6531
  simp only [e4855, e4856, e4857, e4858, e8324, e8325, e8330] at *
  tauto
theorem n17897 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4026 : (e4026 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4220 : (e4220 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4491 : (e4491 _v)) (h4546 : (e4546 _v)) (h4562 : (e4562 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) (h6531 : (e6531 _v)) : (e7683 _v) := by
  have p14831 := n14831 _v _q 
  have p17863 := n17863 _v _q h30 h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h3976 h4026 h4059 h4096 h4139 h4156 h4199 h4220 h4260 h4285 h4301 h4369 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h4899 h6531
  simp only [e2371, e4181, e4182, e4183, e4184, e6579, e7677, e7683, e7686] at *
  tauto
theorem n17898 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4026 : (e4026 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4220 : (e4220 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4491 : (e4491 _v)) (h4546 : (e4546 _v)) (h4562 : (e4562 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) (h6531 : (e6531 _v)) : (e4181 _v) := by
  have p16453 := n16453 _v _q 
  have p17897 := n17897 _v _q h30 h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h3976 h4026 h4059 h4096 h4139 h4156 h4199 h4220 h4260 h4285 h4301 h4369 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h4899 h6531
  simp only [e4181, e4182, e4183, e4184, e7677, e7678, e7683] at *
  tauto
theorem n17899 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2799 : (e2799 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3267 : (e3267 _v)) (h3585 : (e3585 _v)) (h3855 : (e3855 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3971 : (e3971 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4128 : (e4128 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4546 : (e4546 _v)) (h4562 : (e4562 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4855 : (e4855 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) (h6732 : (e6732 _v)) : (e7489 _v) := by
  have p16506 := n16506 _v _q h6732
  have p17151 := n17151 _v _q 
  have p16250 := n16250 _v _q h3855
  have p10893 := n10893 _v _q 
  have p11370 := n11370 _v _q h6732
  have p17137 := n17137 _v _q h4059
  have p16464 := n16464 _v _q h2799
  have p4969 := n4969 _v _q h3267
  have p4970 := n4970 _v _q h3585
  have p4971 := n4971 _v _q h4419
  have p17865 := n17865 _v _q h30 h70 h91 h191 h225 h442 h488 h2799 h3069 h3105 h3152 h3169 h3267 h3585 h3937 h3946 h3971 h4096 h4128 h4139 h4156 h4199 h4260 h4285 h4301 h4369 h4419 h4434 h4477 h4546 h4562 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4855 h4872 h4899 h6732
  have p5257 := n5257 _v _q 
  have p16929 := n16929 _v _q 
  have p4972 := n4972 _v _q h4899
  have p4973 := n4973 _v _q h4562
  have p4974 := n4974 _v _q h4128
  have p16467 := n16467 _v _q h2799
  have p4976 := n4976 _v _q h4546
  have p4977 := n4977 _v _q h4285
  have p4978 := n4978 _v _q h4477
  have p16181 := n16181 _v _q 
  have p4979 := n4979 _v _q h4139
  have p4980 := n4980 _v _q h4301
  have p4981 := n4981 _v _q h4260
  have p16175 := n16175 _v _q 
  have p17134 := n17134 _v _q h4398
  have p4983 := n4983 _v _q h4813
  have p4984 := n4984 _v _q h4872
  have p4985 := n4985 _v _q h4156
  have p16178 := n16178 _v _q 
  have p4986 := n4986 _v _q h3105
  have p4987 := n4987 _v _q h4434
  have p4988 := n4988 _v _q h488
  have p17074 := n17074 _v _q 
  have p4989 := n4989 _v _q h4838
  have p8511 := n8511 _v _q h2799
  have p17072 := n17072 _v _q 
  have p17091 := n17091 _v _q 
  have p17080 := n17080 _v _q 
  have p17098 := n17098 _v _q 
  have p17078 := n17078 _v _q 
  have p253 := n253 _v _q h191
  have p4990 := n4990 _v _q h4648
  have p17087 := n17087 _v _q 
  have p17067 := n17067 _v _q 
  have p17100 := n17100 _v _q 
  have p4991 := n4991 _v _q h4608
  have p4992 := n4992 _v _q h442
  have p17110 := n17110 _v _q 
  have p17115 := n17115 _v _q 
  have p17083 := n17083 _v _q 
  have p16576 := n16576 _v _q 
  have p17058 := n17058 _v _q 
  have p17113 := n17113 _v _q 
  have p17064 := n17064 _v _q 
  have p17102 := n17102 _v _q 
  have p17061 := n17061 _v _q h4747
  have p17096 := n17096 _v _q 
  have p4994 := n4994 _v _q h3069
  have p17122 := n17122 _v _q 
  have p17124 := n17124 _v _q 
  have p17106 := n17106 _v _q 
  have p17108 := n17108 _v _q 
  have p17104 := n17104 _v _q 
  have p4995 := n4995 _v _q h4369
  have p17117 := n17117 _v _q 
  have p17120 := n17120 _v _q 
  have p17069 := n17069 _v _q 
  have p17141 := n17141 _v _q 
  have p17093 := n17093 _v _q 
  have p17131 := n17131 _v _q 
  have p17053 := n17053 _v _q 
  have p4996 := n4996 _v _q h3937
  have p4997 := n4997 _v _q h4855
  have p4998 := n4998 _v _q h3152
  have p16394 := n16394 _v _q 
  have p4999 := n4999 _v _q h91
  have p17055 := n17055 _v _q 
  have p5000 := n5000 _v _q h30
  have p5001 := n5001 _v _q h4096
  have p17136 := n17136 _v _q 
  have p17127 := n17127 _v _q 
  have p5002 := n5002 _v _q h3971
  have p17056 := n17056 _v _q h3946
  have p5003 := n5003 _v _q h4199
  have p16470 := n16470 _v _q h2799
  have p5005 := n5005 _v _q h3169
  have p5006 := n5006 _v _q h4675
  have p17147 := n17147 _v _q 
  have p5007 := n5007 _v _q h225
  have p5008 := n5008 _v _q h4787
  have p17133 := n17133 _v _q 
  have p16461 := n16461 _v _q h2799
  have p5010 := n5010 _v _q h70
  have p17146 := n17146 _v _q 
  have p15504 := n15504 _v _q h6732
  have p13951 := n13951 _v _q 
  have p14810 := n14810 _v _q 
  exact FloorCertificate.node_17899 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e61 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2834 _v) (e2849 _v) (e2863 _v) (e2877 _v) (e2879 _v) (e2883 _v) (e2898 _v) (e2902 _v) (e2905 _v) (e2907 _v) (e2909 _v) (e2911 _v) (e2913 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e3164 _v) (e3262 _v) (e3574 _v) (e4215 _v) (e4541 _v) (e4696 _v) (e4808 _v) p16506 p17151 p16250 p10893 p11370 p17137 p16464 p4969 p4970 p4971 p17865 p5257 p16929 p4972 p4973 p4974 p16467 p4976 p4977 p4978 p16181 p4979 p4980 p4981 p16175 p17134 p4983 p4984 p4985 p16178 p4986 p4987 p4988 p17074 p4989 p8511 p17072 p17091 p17080 p17098 p17078 p253 p4990 p17087 p17067 p17100 p4991 p4992 p17110 p17115 p17083 p16576 p17058 p17113 p17064 p17102 p17061 p17096 p4994 p17122 p17124 p17106 p17108 p17104 p4995 p17117 p17120 p17069 p17141 p17093 p17131 p17053 p4996 p4997 p4998 p16394 p4999 p17055 p5000 p5001 p17136 p17127 p5002 p17056 p5003 p16470 p5005 p5006 p17147 p5007 p5008 p17133 p16461 p5010 p17146 p15504 p13951 p14810
theorem n17900 (_v : Vars) (_q : Query _v) (h6684 : (e6684 _v)) : (e6575 _v) := by
  have p12804 := n12804 _v _q h6684
  have p5255 := n5255 _v _q 
  have p17872 := n17872 _v _q 
  have p8663 := n8663 _v _q 
  have p10893 := n10893 _v _q 
  have p5257 := n5257 _v _q 
  exact FloorCertificate.node_17900 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p12804 p5255 p17872 p8663 p10893 p5257
theorem n17901 (_v : Vars) (_q : Query _v) (h6684 : (e6684 _v)) : (e7668 _v) := by
  have p14544 := n14544 _v _q 
  have p17900 := n17900 _v _q h6684
  simp only [e2351, e4156, e4157, e4158, e4159, e6575, e7660, e7668, e7671] at *
  tauto
theorem n17902 (_v : Vars) (_q : Query _v) (h6684 : (e6684 _v)) : (e6694 _v) := by
  have p17872 := n17872 _v _q 
  have p12804 := n12804 _v _q h6684
  have p8663 := n8663 _v _q 
  have p5255 := n5255 _v _q 
  have p10893 := n10893 _v _q 
  have p5257 := n5257 _v _q 
  exact FloorCertificate.node_17902 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p17872 p12804 p8663 p5255 p10893 p5257
theorem n17903 (_v : Vars) (_q : Query _v) (h6684 : (e6684 _v)) : (e7895 _v) := by
  have p14589 := n14589 _v _q 
  have p17902 := n17902 _v _q h6684
  simp only [e251, e4367, e4368, e4369, e4370, e6694, e7887, e7895, e7898] at *
  tauto
theorem n17904 (_v : Vars) (_q : Query _v) (h6684 : (e6684 _v)) : (e6776 _v) := by
  have p12804 := n12804 _v _q h6684
  have p17872 := n17872 _v _q 
  have p10893 := n10893 _v _q 
  have p8663 := n8663 _v _q 
  have p5255 := n5255 _v _q 
  have p5257 := n5257 _v _q 
  exact FloorCertificate.node_17904 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p12804 p17872 p10893 p8663 p5255 p5257
theorem n17905 (_v : Vars) (_q : Query _v) (h6684 : (e6684 _v)) : (e7789 _v) := by
  have p14570 := n14570 _v _q 
  have p17904 := n17904 _v _q h6684
  simp only [e2781, e4258, e4259, e4260, e4261, e6776, e7781, e7789, e7792] at *
  tauto
theorem n17906 (_v : Vars) (_q : Query _v) (h6684 : (e6684 _v)) : (e6525 _v) := by
  have p8663 := n8663 _v _q 
  have p12804 := n12804 _v _q h6684
  have p10893 := n10893 _v _q 
  have p17872 := n17872 _v _q 
  have p5255 := n5255 _v _q 
  have p5257 := n5257 _v _q 
  exact FloorCertificate.node_17906 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8663 p12804 p10893 p17872 p5255 p5257
theorem n17907 (_v : Vars) (_q : Query _v) (h6684 : (e6684 _v)) : (e8174 _v) := by
  have p14634 := n14634 _v _q 
  have p17906 := n17906 _v _q h6684
  simp only [e2242, e4673, e4674, e4675, e4676, e6525, e8166, e8174, e8177] at *
  tauto
theorem n17908 (_v : Vars) (_q : Query _v) (h6684 : (e6684 _v)) : (e6630 _v) := by
  have p12804 := n12804 _v _q h6684
  have p5255 := n5255 _v _q 
  have p10893 := n10893 _v _q 
  have p8663 := n8663 _v _q 
  have p17872 := n17872 _v _q 
  have p5257 := n5257 _v _q 
  exact FloorCertificate.node_17908 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p12804 p5255 p10893 p8663 p17872 p5257
theorem n17909 (_v : Vars) (_q : Query _v) (h6684 : (e6684 _v)) : (e8275 _v) := by
  have p14655 := n14655 _v _q 
  have p17908 := n17908 _v _q h6684
  simp only [e2468, e4785, e4786, e4787, e4788, e6630, e8267, e8275, e8278] at *
  tauto
theorem n17910 (_v : Vars) (_q : Query _v) (h6684 : (e6684 _v)) : (e2680 _v) := by
  have p10893 := n10893 _v _q 
  have p12804 := n12804 _v _q h6684
  have p8663 := n8663 _v _q 
  have p17872 := n17872 _v _q 
  have p5255 := n5255 _v _q 
  have p5257 := n5257 _v _q 
  exact FloorCertificate.node_17910 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p10893 p12804 p8663 p17872 p5255 p5257
theorem n17911 (_v : Vars) (_q : Query _v) (h6684 : (e6684 _v)) : (e7709 _v) := by
  have p14832 := n14832 _v _q 
  have p17910 := n17910 _v _q h6684
  simp only [e2680, e4199, e4200, e4201, e4202, e6716, e7703, e7709, e7712] at *
  tauto
theorem n17912 (_v : Vars) (_q : Query _v) (h6684 : (e6684 _v)) : (e214 _v) := by
  have p8663 := n8663 _v _q 
  have p10893 := n10893 _v _q 
  have p12804 := n12804 _v _q h6684
  have p5255 := n5255 _v _q 
  have p5257 := n5257 _v _q 
  have p17872 := n17872 _v _q 
  exact FloorCertificate.node_17912 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8663 p10893 p12804 p5255 p5257 p17872
theorem n17913 (_v : Vars) (_q : Query _v) (h6684 : (e6684 _v)) : (e5232 _v) := by
  have p14731 := n14731 _v _q 
  have p17912 := n17912 _v _q h6684
  simp only [e214, e225, e227, e230, e231, e5223, e5231, e5232, e5235] at *
  tauto
theorem n17914 (_v : Vars) (_q : Query _v) (h6684 : (e6684 _v)) : (e6454 _v) := by
  have p12804 := n12804 _v _q h6684
  have p10893 := n10893 _v _q 
  have p5257 := n5257 _v _q 
  have p17872 := n17872 _v _q 
  have p5255 := n5255 _v _q 
  exact FloorCertificate.node_17914 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p12804 p10893 p5257 p17872 p5255
theorem n17915 (_v : Vars) (_q : Query _v) (h6684 : (e6684 _v)) : (e7955 _v) := by
  have p14601 := n14601 _v _q 
  have p17914 := n17914 _v _q h6684
  simp only [e2061, e4434, e4435, e4436, e4437, e6454, e7947, e7955, e7958] at *
  tauto
end
end Assembly
