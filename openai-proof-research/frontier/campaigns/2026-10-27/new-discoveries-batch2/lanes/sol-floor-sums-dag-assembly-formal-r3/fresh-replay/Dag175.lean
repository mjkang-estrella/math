import Dag174
import generated.th_lemma_17
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n17672 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4026 : (e4026 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4220 : (e4220 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4491 : (e4491 _v)) (h4546 : (e4546 _v)) (h4562 : (e4562 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) (h6531 : (e6531 _v)) (h8398 : (e8398 _v)) : (e2371 _v) := by
  have p17642 := n17642 _v _q 
  have p17208 := n17208 _v _q h8398
  have p16994 := n16994 _v _q 
  have p5010 := n5010 _v _q h70
  have p5006 := n5006 _v _q h4675
  have p4971 := n4971 _v _q h4419
  have p4972 := n4972 _v _q h4899
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
  have p4977 := n4977 _v _q h4285
  have p4995 := n4995 _v _q h4369
  have p4994 := n4994 _v _q h3069
  have p4996 := n4996 _v _q h3937
  have p4999 := n4999 _v _q h91
  have p4998 := n4998 _v _q h3152
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
  have p11358 := n11358 _v _q h6531
  have p17137 := n17137 _v _q h4059
  have p4975 := n4975 _v _q h4026
  change (¬ (e8335 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4419 _v)) ∨ (¬ (e4546 _v)) ∨ (¬ (e4899 _v)) ∨ (¬ (e8398 _v)) ∨ (¬ (e4477 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e4301 _v)) ∨ (¬ (e3169 _v)) ∨ (¬ (e4562 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e4648 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e4285 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e30 _v)) ∨ (¬ (e4491 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e4220 _v)) ∨ (¬ (e3976 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4747 _v)) ∨ (e2254 _v) ∨ (e2371 _v) ∨ (¬ (e4026 _v)) at p17642
  change (¬ (e2254 _v)) at p11358
  rcases p17642 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact (False.elim (hlit p16994))
  · exact (False.elim (hlit p17137))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p5010))
  · exact (False.elim (hlit p4971))
  · exact (False.elim (hlit p4976))
  · exact (False.elim (hlit p4972))
  · exact (False.elim (hlit p17208))
  · exact (False.elim (hlit p4978))
  · exact (False.elim (hlit p4979))
  · exact (False.elim (hlit p4980))
  · exact (False.elim (hlit p5005))
  · exact (False.elim (hlit p4973))
  · exact (False.elim (hlit p4985))
  · exact (False.elim (hlit p4987))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p4988))
  · exact (False.elim (hlit p4981))
  · exact (False.elim (hlit p4989))
  · exact (False.elim (hlit p4986))
  · exact (False.elim (hlit p253))
  · exact (False.elim (hlit p4990))
  · exact (False.elim (hlit p4984))
  · exact (False.elim (hlit p4991))
  · exact (False.elim (hlit p4992))
  · exact (False.elim (hlit p4977))
  · exact (False.elim (hlit p4995))
  · exact (False.elim (hlit p4994))
  · exact (False.elim (hlit p4996))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p5001))
  · exact (False.elim (hlit p5000))
  · exact (False.elim (hlit p17128))
  · exact (False.elim (hlit p5003))
  · exact (False.elim (hlit p5004))
  · exact (False.elim (hlit p17076))
  · exact (False.elim (hlit p17056))
  · exact (False.elim (hlit p5007))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p17061))
  · exact (False.elim (p11358 hlit))
  · exact hlit
  · exact (False.elim (hlit p4975))
theorem n17673 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2799 : (e2799 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3267 : (e3267 _v)) (h3585 : (e3585 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3971 : (e3971 _v)) (h4096 : (e4096 _v)) (h4128 : (e4128 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4486 : (e4486 _v)) (h4546 : (e4546 _v)) (h4562 : (e4562 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4855 : (e4855 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) (h6684 : (e6684 _v)) : (e2377 _v) := by
  have p17644 := n17644 _v _q 
  have p15497 := n15497 _v _q h6684
  have p4971 := n4971 _v _q h4419
  have p4972 := n4972 _v _q h4899
  have p4973 := n4973 _v _q h4562
  have p4974 := n4974 _v _q h4128
  have p16467 := n16467 _v _q h2799
  have p4976 := n4976 _v _q h4546
  have p4977 := n4977 _v _q h4285
  have p4978 := n4978 _v _q h4477
  have p4979 := n4979 _v _q h4139
  have p4980 := n4980 _v _q h4301
  have p4981 := n4981 _v _q h4260
  have p4969 := n4969 _v _q h3267
  have p4983 := n4983 _v _q h4813
  have p4984 := n4984 _v _q h4872
  have p4985 := n4985 _v _q h4156
  have p4986 := n4986 _v _q h3105
  have p4987 := n4987 _v _q h4434
  have p4988 := n4988 _v _q h488
  have p4989 := n4989 _v _q h4838
  have p253 := n253 _v _q h191
  have p4990 := n4990 _v _q h4648
  have p4991 := n4991 _v _q h4608
  have p4992 := n4992 _v _q h442
  have p4994 := n4994 _v _q h3069
  have p4995 := n4995 _v _q h4369
  have p4996 := n4996 _v _q h3937
  have p4997 := n4997 _v _q h4855
  have p4998 := n4998 _v _q h3152
  have p4999 := n4999 _v _q h91
  have p5000 := n5000 _v _q h30
  have p5001 := n5001 _v _q h4096
  have p5002 := n5002 _v _q h3971
  have p17056 := n17056 _v _q h3946
  have p5003 := n5003 _v _q h4199
  have p16470 := n16470 _v _q h2799
  have p5005 := n5005 _v _q h3169
  have p5006 := n5006 _v _q h4675
  have p5007 := n5007 _v _q h225
  have p5008 := n5008 _v _q h4787
  have p16461 := n16461 _v _q h2799
  have p5010 := n5010 _v _q h70
  have p5011 := n5011 _v _q h4486
  have p4970 := n4970 _v _q h3585
  have p16464 := n16464 _v _q h2799
  change (e2377 _v) ∨ (¬ (e3585 _v)) ∨ (¬ (e4419 _v)) ∨ (¬ (e4899 _v)) ∨ (¬ (e4562 _v)) ∨ (¬ (e4128 _v)) ∨ (¬ (e4026 _v)) ∨ (¬ (e4546 _v)) ∨ (¬ (e4285 _v)) ∨ (¬ (e4477 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e4301 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e3267 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e4648 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e4855 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e30 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e3971 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e4220 _v)) ∨ (¬ (e3169 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4181 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4486 _v)) ∨ (¬ (e4054 _v)) ∨ (¬ (e4924 _v)) at p17644
  rcases p17644 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p4970))
  · exact (False.elim (hlit p4971))
  · exact (False.elim (hlit p4972))
  · exact (False.elim (hlit p4973))
  · exact (False.elim (hlit p4974))
  · exact (False.elim (hlit p16467))
  · exact (False.elim (hlit p4976))
  · exact (False.elim (hlit p4977))
  · exact (False.elim (hlit p4978))
  · exact (False.elim (hlit p4979))
  · exact (False.elim (hlit p4980))
  · exact (False.elim (hlit p4981))
  · exact (False.elim (hlit p4969))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p4984))
  · exact (False.elim (hlit p4985))
  · exact (False.elim (hlit p4986))
  · exact (False.elim (hlit p4987))
  · exact (False.elim (hlit p4988))
  · exact (False.elim (hlit p4989))
  · exact (False.elim (hlit p253))
  · exact (False.elim (hlit p4990))
  · exact (False.elim (hlit p4991))
  · exact (False.elim (hlit p4992))
  · exact (False.elim (hlit p4994))
  · exact (False.elim (hlit p4995))
  · exact (False.elim (hlit p4996))
  · exact (False.elim (hlit p4997))
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p5000))
  · exact (False.elim (hlit p5001))
  · exact (False.elim (hlit p5002))
  · exact (False.elim (hlit p17056))
  · exact (False.elim (hlit p5003))
  · exact (False.elim (hlit p16470))
  · exact (False.elim (hlit p5005))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p5007))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p16461))
  · exact (False.elim (hlit p5010))
  · exact (False.elim (hlit p5011))
  · exact (False.elim (hlit p15497))
  · exact (False.elim (hlit p16464))
theorem n17675 (_v : Vars) (_q : Query _v)  : (e17674 _v) := by
  have p17648 := n17648 _v _q 
  have p17256 := n17256 _v _q 
  change (¬ (e51 _v)) ∨ (e2303 _v) ∨ (¬ (e91 _v)) ∨ (e2061 _v) ∨ (¬ (e4199 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e2634 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e4724 _v)) ∨ (¬ (e4398 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e3976 _v)) ∨ (¬ (e4491 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e4264 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4101 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e4903 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e5208 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e7645 _v)) ∨ (¬ (e3069 _v)) ∨ (e2529 _v) ∨ (¬ (e1995 _v)) at p17648
  rcases p17648 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact (Or.inl hlit)
  · exact (Or.inr (Or.inl hlit))
  · exact (Or.inr (Or.inr (Or.inl hlit)))
  · exact (Or.inr (Or.inr (Or.inr (Or.inl hlit))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hlit)))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hlit))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hlit)))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hlit))))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hlit)))))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hlit))))))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hlit)))))))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hlit))))))))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hlit)))))))))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hlit))))))))))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hlit)))))))))))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hlit))))))))))))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hlit)))))))))))))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hlit))))))))))))))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hlit)))))))))))))))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hlit))))))))))))))))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hlit)))))))))))))))))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hlit))))))))))))))))))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hlit)))))))))))))))))))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hlit))))))))))))))))))))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hlit)))))))))))))))))))))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hlit))))))))))))))))))))))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hlit)))))))))))))))))))))))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hlit))))))))))))))))))))))))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hlit)))))))))))))))))))))))))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hlit))))))))))))))))))))))))))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hlit)))))))))))))))))))))))))))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hlit))))))))))))))))))))))))))))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hlit)))))))))))))))))))))))))))))))))
  · exact (False.elim (hlit p17256))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hlit))))))))))))))))))))))))))))))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hlit)))))))))))))))))))))))))))))))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hlit)))))))))))))))))))))))))))))))))))
theorem n17676 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2358 : (e2358 _v)) (h2781 : (e2781 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3158 : (e3158 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4306 : (e4306 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4439 : (e4439 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5100 : (e5100 _v)) (h5208 : (e5208 _v)) (h7714 : (e7714 _v)) (h7749 : (e7749 _v)) (h7807 : (e7807 _v)) (h8038 : (e8038 _v)) (h8045 : (e8045 _v)) : (e79 _v) := by
  have p15115 := n15115 _v _q 
  have p17650 := n17650 _v _q h91 h191 h225 h442 h488 h2358 h2781 h3069 h3105 h3152 h3158 h3937 h3946 h3976 h4156 h4199 h4306 h4369 h4434 h4439 h4567 h4608 h4653 h4675 h4747 h4787 h4813 h4838 h4872 h4903 h5100 h5208 h7714 h7749 h7807 h8038 h8045
  change (e79 _v) ∨ (¬ (e5149 _v)) at p15115
  rcases p15115 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p17650))
theorem n17677 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2358 : (e2358 _v)) (h2781 : (e2781 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3158 : (e3158 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4306 : (e4306 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4439 : (e4439 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5100 : (e5100 _v)) (h5208 : (e5208 _v)) (h7714 : (e7714 _v)) (h7749 : (e7749 _v)) (h7807 : (e7807 _v)) (h8038 : (e8038 _v)) (h8045 : (e8045 _v)) : (e2125 _v) := by
  have p8578 := n8578 _v _q 
  have p17676 := n17676 _v _q h91 h191 h225 h442 h488 h2358 h2781 h3069 h3105 h3152 h3158 h3937 h3946 h3976 h4156 h4199 h4306 h4369 h4434 h4439 h4567 h4608 h4653 h4675 h4747 h4787 h4813 h4838 h4872 h4903 h5100 h5208 h7714 h7749 h7807 h8038 h8045
  have p8421 := n8421 _v _q h2781
  change (e2125 _v) ∨ (¬ (e79 _v)) ∨ (¬ (e2781 _v)) at p8578
  rcases p8578 with hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p17676))
  · exact (False.elim (hlit p8421))
theorem n17678 (_v : Vars) (_q : Query _v)  : (e6768 _v) := by
  by_contra hc
  change ¬ (¬ (e2771 _v)) at hc
  have h2771 : (e2771 _v) := Classical.byContradiction (fun hn => hc hn)
  have p17655 := n17655 _v _q h2771
  exact p17655
theorem n17679 (_v : Vars) (_q : Query _v)  : (e6863 _v) := by
  have p14356 := n14356 _v _q 
  have p17678 := n17678 _v _q 
  change (e2771 _v) ∨ (¬ (e6855 _v)) at p14356
  change (¬ (e2771 _v)) at p17678
  rcases p14356 with hlit | hlit
  · exact (False.elim (p17678 hlit))
  · exact hlit
theorem n17680 (_v : Vars) (_q : Query _v) (h2296 : (e2296 _v)) : (e2364 _v) := by
  have p8583 := n8583 _v _q h2296
  have p258 := n258 _v _q 
  have p17678 := n17678 _v _q 
  have p5255 := n5255 _v _q 
  have p10893 := n10893 _v _q 
  have p5257 := n5257 _v _q 
  exact FloorCertificate.node_17680 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8583 p258 p17678 p5255 p10893 p5257
theorem n17681 (_v : Vars) (_q : Query _v) (h2296 : (e2296 _v)) : (e4661 _v) := by
  have p14686 := n14686 _v _q 
  have p17680 := n17680 _v _q h2296
  change (¬ (e2364 _v)) ∨ (¬ (e4660 _v)) at p14686
  rcases p14686 with hlit | hlit
  · exact (False.elim (hlit p17680))
  · exact hlit
theorem n17682 (_v : Vars) (_q : Query _v) (h2296 : (e2296 _v)) : (e2598 _v) := by
  have p10893 := n10893 _v _q 
  have p17678 := n17678 _v _q 
  have p8583 := n8583 _v _q h2296
  have p5257 := n5257 _v _q 
  have p5255 := n5255 _v _q 
  have p258 := n258 _v _q 
  exact FloorCertificate.node_17682 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p10893 p17678 p8583 p5257 p5255 p258
theorem n17683 (_v : Vars) (_q : Query _v) (h2296 : (e2296 _v)) : (e4067 _v) := by
  have p14703 := n14703 _v _q 
  have p17682 := n17682 _v _q h2296
  change (¬ (e2598 _v)) ∨ (¬ (e4066 _v)) at p14703
  rcases p14703 with hlit | hlit
  · exact (False.elim (hlit p17682))
  · exact hlit
theorem n17684 (_v : Vars) (_q : Query _v) (h2296 : (e2296 _v)) : (e2697 _v) := by
  have p17678 := n17678 _v _q 
  have p10893 := n10893 _v _q 
  have p5257 := n5257 _v _q 
  have p8583 := n8583 _v _q h2296
  have p258 := n258 _v _q 
  have p5255 := n5255 _v _q 
  exact FloorCertificate.node_17684 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p17678 p10893 p5257 p8583 p258 p5255
theorem n17685 (_v : Vars) (_q : Query _v) (h2296 : (e2296 _v)) : (e4499 _v) := by
  have p14700 := n14700 _v _q 
  have p17684 := n17684 _v _q h2296
  change (¬ (e2697 _v)) ∨ (¬ (e4498 _v)) at p14700
  rcases p14700 with hlit | hlit
  · exact (False.elim (hlit p17684))
  · exact hlit
theorem n17686 (_v : Vars) (_q : Query _v) (h2296 : (e2296 _v)) : (e2254 _v) := by
  have p17678 := n17678 _v _q 
  have p8583 := n8583 _v _q h2296
  have p10893 := n10893 _v _q 
  have p5257 := n5257 _v _q 
  have p258 := n258 _v _q 
  have p5255 := n5255 _v _q 
  exact FloorCertificate.node_17686 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p17678 p8583 p10893 p5257 p258 p5255
theorem n17687 (_v : Vars) (_q : Query _v) (h2296 : (e2296 _v)) : (e4731 _v) := by
  have p14698 := n14698 _v _q 
  have p17686 := n17686 _v _q h2296
  change (¬ (e2254 _v)) ∨ (¬ (e4730 _v)) at p14698
  rcases p14698 with hlit | hlit
  · exact (False.elim (hlit p17686))
  · exact hlit
theorem n17688 (_v : Vars) (_q : Query _v) (h2296 : (e2296 _v)) : (e2793 _v) := by
  have p8583 := n8583 _v _q h2296
  have p10893 := n10893 _v _q 
  have p258 := n258 _v _q 
  have p17678 := n17678 _v _q 
  have p5255 := n5255 _v _q 
  have p5257 := n5257 _v _q 
  exact FloorCertificate.node_17688 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p8583 p10893 p258 p17678 p5255 p5257
theorem n17689 (_v : Vars) (_q : Query _v) (h2296 : (e2296 _v)) : (e4910 _v) := by
  have p14701 := n14701 _v _q 
  have p17688 := n17688 _v _q h2296
  change (¬ (e2793 _v)) ∨ (¬ (e4909 _v)) at p14701
  rcases p14701 with hlit | hlit
  · exact (False.elim (hlit p17688))
  · exact hlit
theorem n17690 (_v : Vars) (_q : Query _v) (h2296 : (e2296 _v)) : (e2746 _v) := by
  have p17678 := n17678 _v _q 
  have p8583 := n8583 _v _q h2296
  have p10893 := n10893 _v _q 
  have p258 := n258 _v _q 
  have p5255 := n5255 _v _q 
  have p5257 := n5257 _v _q 
  exact FloorCertificate.node_17690 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p17678 p8583 p10893 p258 p5255 p5257
theorem n17691 (_v : Vars) (_q : Query _v) (h2296 : (e2296 _v)) : (e3984 _v) := by
  have p14691 := n14691 _v _q 
  have p17690 := n17690 _v _q h2296
  change (¬ (e2746 _v)) ∨ (¬ (e3983 _v)) at p14691
  rcases p14691 with hlit | hlit
  · exact (False.elim (hlit p17690))
  · exact hlit
theorem n17692 (_v : Vars) (_q : Query _v) (h2722 : (e2722 _v)) : (e2125 _v) := by
  have p5257 := n5257 _v _q 
  have p5391 := n5391 _v _q 
  have p5255 := n5255 _v _q 
  have p8410 := n8410 _v _q h2722
  have p17678 := n17678 _v _q 
  exact FloorCertificate.node_17692 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p5257 p5391 p5255 p8410 p17678
theorem n17693 (_v : Vars) (_q : Query _v) (h2722 : (e2722 _v)) : (e4466 _v) := by
  have p14604 := n14604 _v _q 
  have p17692 := n17692 _v _q h2722
  change (¬ (e2125 _v)) ∨ (¬ (e4465 _v)) at p14604
  rcases p14604 with hlit | hlit
  · exact (False.elim (hlit p17692))
  · exact hlit
theorem n17694 (_v : Vars) (_q : Query _v) (h2722 : (e2722 _v)) : (e2364 _v) := by
  have p17678 := n17678 _v _q 
  have p258 := n258 _v _q 
  have p5255 := n5255 _v _q 
  have p5391 := n5391 _v _q 
  have p5257 := n5257 _v _q 
  have p8410 := n8410 _v _q h2722
  exact FloorCertificate.node_17694 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p17678 p258 p5255 p5391 p5257 p8410
theorem n17695 (_v : Vars) (_q : Query _v) (h2722 : (e2722 _v)) : (e4661 _v) := by
  have p14686 := n14686 _v _q 
  have p17694 := n17694 _v _q h2722
  change (¬ (e2364 _v)) ∨ (¬ (e4660 _v)) at p14686
  rcases p14686 with hlit | hlit
  · exact (False.elim (hlit p17694))
  · exact hlit
theorem n17696 (_v : Vars) (_q : Query _v) (h225 : (e225 _v)) (h488 : (e488 _v)) (h2061 : (e2061 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3271 : (e3271 _v)) (h3855 : (e3855 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4491 : (e4491 _v)) (h4653 : (e4653 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5100 : (e5100 _v)) (h6571 : (e6571 _v)) (h6700 : (e6700 _v)) (h7493 : (e7493 _v)) (h8045 : (e8045 _v)) (h8310 : (e8310 _v)) : (e7971 _v) := by
  have p14603 := n14603 _v _q 
  have p17659 := n17659 _v _q h225 h488 h2061 h3069 h3105 h3152 h3271 h3855 h3937 h3946 h3976 h4059 h4096 h4156 h4260 h4369 h4398 h4491 h4653 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h6571 h6700 h7493 h8045 h8310
  change (e2125 _v) ∨ (¬ (e7970 _v)) at p14603
  change (¬ (e2125 _v)) at p17659
  rcases p14603 with hlit | hlit
  · exact (False.elim (p17659 hlit))
  · exact hlit
theorem n17697 (_v : Vars) (_q : Query _v) (h225 : (e225 _v)) (h488 : (e488 _v)) (h2061 : (e2061 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3271 : (e3271 _v)) (h3855 : (e3855 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4491 : (e4491 _v)) (h4653 : (e4653 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5100 : (e5100 _v)) (h6571 : (e6571 _v)) (h6700 : (e6700 _v)) (h7493 : (e7493 _v)) (h8045 : (e8045 _v)) (h8310 : (e8310 _v)) : (e4477 _v) := by
  have p14858 := n14858 _v _q 
  have p17696 := n17696 _v _q h225 h488 h2061 h3069 h3105 h3152 h3271 h3855 h3937 h3946 h3976 h4059 h4096 h4156 h4260 h4369 h4398 h4491 h4653 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h6571 h6700 h7493 h8045 h8310
  change (e7970 _v) ∨ (e4477 _v) at p14858
  change (¬ (e7970 _v)) at p17696
  rcases p14858 with hlit | hlit
  · exact (False.elim (p17696 hlit))
  · exact hlit
theorem n17698 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2125 : (e2125 _v)) (h2358 : (e2358 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3976 : (e3976 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h6700 : (e6700 _v)) (h8038 : (e8038 _v)) : (e7944 _v) := by
  have p15266 := n15266 _v _q 
  have p17660 := n17660 _v _q h70 h91 h191 h225 h442 h488 h2125 h2358 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4567 h4608 h4675 h4787 h4813 h4872 h4903 h6700 h8038
  change (e7944 _v) ∨ (e7935 _v) at p15266
  change (¬ (e7935 _v)) at p17660
  rcases p15266 with hlit | hlit
  · exact hlit
  · exact (False.elim (p17660 hlit))
theorem n17699 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2358 : (e2358 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3271 : (e3271 _v)) (h3855 : (e3855 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4477 : (e4477 _v)) (h4491 : (e4491 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5100 : (e5100 _v)) (h5208 : (e5208 _v)) (h6700 : (e6700 _v)) (h7493 : (e7493 _v)) (h7606 : (e7606 _v)) (h7688 : (e7688 _v)) (h7749 : (e7749 _v)) (h8045 : (e8045 _v)) (h8310 : (e8310 _v)) (h8335 : (e8335 _v)) : (e4306 _v) := by
  have p14984 := n14984 _v _q 
  have p17663 := n17663 _v _q h70 h91 h191 h225 h442 h488 h2358 h3069 h3105 h3152 h3169 h3271 h3855 h3937 h3946 h3976 h4059 h4096 h4156 h4199 h4260 h4369 h4398 h4477 h4491 h4567 h4608 h4675 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h5208 h6700 h7493 h7606 h7688 h7749 h8045 h8310 h8335
  change (e4313 _v) ∨ (e4306 _v) at p14984
  change (¬ (e4313 _v)) at p17663
  rcases p14984 with hlit | hlit
  · exact (False.elim (p17663 hlit))
  · exact hlit
theorem n17700 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2358 : (e2358 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3271 : (e3271 _v)) (h3855 : (e3855 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4477 : (e4477 _v)) (h4491 : (e4491 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5100 : (e5100 _v)) (h5208 : (e5208 _v)) (h6700 : (e6700 _v)) (h7493 : (e7493 _v)) (h7606 : (e7606 _v)) (h7688 : (e7688 _v)) (h7749 : (e7749 _v)) (h8045 : (e8045 _v)) (h8310 : (e8310 _v)) (h8335 : (e8335 _v)) : (e7489 _v) := by
  have p4016 := n4016 _v _q 
  have p17096 := n17096 _v _q 
  have p8663 := n8663 _v _q 
  have p17588 := n17588 _v _q h70 h91 h225 h442 h488 h2358 h3069 h3105 h3152 h3169 h3271 h3855 h3937 h3946 h3976 h4059 h4096 h4156 h4199 h4260 h4369 h4398 h4491 h4567 h4608 h4675 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h5208 h7493 h7606 h7749 h8045 h8310
  have p17699 := n17699 _v _q h70 h91 h191 h225 h442 h488 h2358 h3069 h3105 h3152 h3169 h3271 h3855 h3937 h3946 h3976 h4059 h4096 h4156 h4199 h4260 h4369 h4398 h4477 h4491 h4567 h4608 h4675 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h5208 h6700 h7493 h7606 h7688 h7749 h8045 h8310 h8335
  have p16929 := n16929 _v _q 
  have p17182 := n17182 _v _q h8310
  have p17122 := n17122 _v _q 
  have p16250 := n16250 _v _q h3855
  have p11027 := n11027 _v _q h6700
  have p17165 := n17165 _v _q h3271
  have p16370 := n16370 _v _q h2358
  have p17661 := n17661 _v _q h70 h91 h191 h225 h442 h488 h2358 h3069 h3105 h3152 h3169 h3271 h3855 h3937 h3946 h3976 h4059 h4096 h4156 h4199 h4260 h4369 h4398 h4477 h4491 h4567 h4608 h4675 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h5208 h6700 h7493 h7606 h7688 h7749 h8045 h8310 h8335
  have p17124 := n17124 _v _q 
  have p17106 := n17106 _v _q 
  have p17108 := n17108 _v _q 
  have p17104 := n17104 _v _q 
  have p17191 := n17191 _v _q h8310
  have p4995 := n4995 _v _q h4369
  have p17117 := n17117 _v _q 
  have p17120 := n17120 _v _q 
  have p17069 := n17069 _v _q 
  have p17164 := n17164 _v _q h7606
  have p17141 := n17141 _v _q 
  have p17093 := n17093 _v _q 
  have p17131 := n17131 _v _q 
  have p17053 := n17053 _v _q 
  have p4996 := n4996 _v _q h3937
  have p16269 := n16269 _v _q h7749
  have p4998 := n4998 _v _q h3152
  have p4978 := n4978 _v _q h4477
  have p13951 := n13951 _v _q 
  have p253 := n253 _v _q h191
  have p17137 := n17137 _v _q h4059
  have p17192 := n17192 _v _q h8310
  have p4999 := n4999 _v _q h91
  have p17055 := n17055 _v _q 
  have p17155 := n17155 _v _q h7493
  have p5001 := n5001 _v _q h4096
  have p17136 := n17136 _v _q 
  have p17127 := n17127 _v _q 
  have p17128 := n17128 _v _q h4491
  have p17056 := n17056 _v _q h3946
  have p15248 := n15248 _v _q h8310
  have p5003 := n5003 _v _q h4199
  have p17159 := n17159 _v _q h5100
  have p17129 := n17129 _v _q h4903
  have p5006 := n5006 _v _q h4675
  have p17076 := n17076 _v _q h3976
  have p17147 := n17147 _v _q 
  have p5007 := n5007 _v _q h225
  have p5008 := n5008 _v _q h4787
  have p17133 := n17133 _v _q 
  have p5005 := n5005 _v _q h3169
  have p17143 := n17143 _v _q h4567
  have p5010 := n5010 _v _q h70
  have p4981 := n4981 _v _q h4260
  have p17157 := n17157 _v _q h8045
  have p17061 := n17061 _v _q h4747
  have p4988 := n4988 _v _q h488
  have p4986 := n4986 _v _q h3105
  have p16175 := n16175 _v _q 
  have p4983 := n4983 _v _q h4813
  have p17094 := n17094 _v _q h4724
  have p4994 := n4994 _v _q h3069
  have p4992 := n4992 _v _q h442
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
  have p4991 := n4991 _v _q h4608
  have p17058 := n17058 _v _q 
  have p17083 := n17083 _v _q 
  have p16576 := n16576 _v _q 
  have p17113 := n17113 _v _q 
  have p17064 := n17064 _v _q 
  have p17102 := n17102 _v _q 
  have p17549 := n17549 _v _q h70 h91 h225 h442 h488 h2358 h3069 h3105 h3152 h3169 h3271 h3855 h3937 h3946 h3976 h4059 h4096 h4156 h4199 h4260 h4369 h4398 h4491 h4567 h4608 h4675 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h5208 h7493 h7606 h7749 h8045 h8310
  exact FloorCertificate.node_17700 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e61 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2849 _v) (e2863 _v) (e2877 _v) (e2883 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e3164 _v) (e4215 _v) (e4541 _v) (e4808 _v) p4016 p17096 p8663 p17588 p17699 p16929 p17182 p17122 p16250 p11027 p17165 p16370 p17661 p17124 p17106 p17108 p17104 p17191 p4995 p17117 p17120 p17069 p17164 p17141 p17093 p17131 p17053 p4996 p16269 p4998 p4978 p13951 p253 p17137 p17192 p4999 p17055 p17155 p5001 p17136 p17127 p17128 p17056 p15248 p5003 p17159 p17129 p5006 p17076 p17147 p5007 p5008 p17133 p5005 p17143 p5010 p4981 p17157 p17061 p4988 p4986 p16175 p4983 p17094 p4994 p4992 p4984 p4985 p17080 p17134 p17074 p17078 p17072 p17098 p17091 p17087 p17115 p17110 p17067 p17100 p4991 p17058 p17083 p16576 p17113 p17064 p17102 p17549
theorem n17702 (_v : Vars) (_q : Query _v)  : (e17701 _v) := by
  by_contra hc
  change ¬ ((e2310 _v) ∨ (e1995 _v) ∨ (¬ (e4608 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e4903 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e3976 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e3169 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e191 _v)) ∨ (e2475 _v)) at hc
  have h70 : (e70 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h191 : (e191 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))
  have h225 : (e225 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h442 : (e442 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))
  have h488 : (e488 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))
  have h3069 : (e3069 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))
  have h3105 : (e3105 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h3169 : (e3169 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h3976 : (e3976 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h4096 : (e4096 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h4156 : (e4156 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))
  have h4199 : (e4199 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h4260 : (e4260 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))
  have h4369 : (e4369 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4608 : (e4608 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4675 : (e4675 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))
  have h4872 : (e4872 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))
  have h4903 : (e4903 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h6423 : (e6423 _v) := (fun hn => hc (Or.inr (Or.inl hn)))
  have h6555 : (e6555 _v) := (fun hn => hc (Or.inl hn))
  have h8038 : (e8038 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))))))))))))))))))))))
  have p17664 := n17664 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3976 h4096 h4156 h4199 h4260 h4369 h4608 h4675 h4787 h4813 h4872 h4903 h6423 h6555 h8038
  exact p17664
theorem n17703 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h225 : (e225 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h4096 : (e4096 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) (h6784 : (e6784 _v)) (h8038 : (e8038 _v)) (h8398 : (e8398 _v)) : (e6423 _v) := by
  have p14696 := n14696 _v _q 
  have p17666 := n17666 _v _q h91 h225 h488 h3069 h3105 h3152 h3937 h4096 h4369 h4434 h4608 h4787 h4813 h4838 h4872 h4899 h6784 h8038 h8398
  change (¬ (e1995 _v)) ∨ (¬ (e4574 _v)) at p14696
  rcases p14696 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p17666))
theorem n17704 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h225 : (e225 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h4096 : (e4096 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) (h6784 : (e6784 _v)) (h8038 : (e8038 _v)) (h8398 : (e8398 _v)) : (e8060 _v) := by
  have p14622 := n14622 _v _q 
  have p17703 := n17703 _v _q h91 h225 h488 h3069 h3105 h3152 h3937 h4096 h4369 h4434 h4608 h4787 h4813 h4838 h4872 h4899 h6784 h8038 h8398
  change (e1995 _v) ∨ (¬ (e8052 _v)) at p14622
  change (¬ (e1995 _v)) at p17703
  rcases p14622 with hlit | hlit
  · exact (False.elim (p17703 hlit))
  · exact hlit
theorem n17705 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h225 : (e225 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h4096 : (e4096 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) (h6784 : (e6784 _v)) (h8038 : (e8038 _v)) (h8398 : (e8398 _v)) : (e4562 _v) := by
  have p15155 := n15155 _v _q 
  have p17704 := n17704 _v _q h91 h225 h488 h3069 h3105 h3152 h3937 h4096 h4369 h4434 h4608 h4787 h4813 h4838 h4872 h4899 h6784 h8038 h8398
  change (e8052 _v) ∨ (e4562 _v) at p15155
  change (¬ (e8052 _v)) at p17704
  rcases p15155 with hlit | hlit
  · exact (False.elim (p17704 hlit))
  · exact hlit
theorem n17706 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h225 : (e225 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h4096 : (e4096 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) (h6784 : (e6784 _v)) (h8038 : (e8038 _v)) (h8398 : (e8398 _v)) : (e3972 _v) := by
  have p17495 := n17495 _v _q 
  have p17703 := n17703 _v _q h91 h225 h488 h3069 h3105 h3152 h3937 h4096 h4369 h4434 h4608 h4787 h4813 h4838 h4872 h4899 h6784 h8038 h8398
  have p4986 := n4986 _v _q h3105
  have p4983 := n4983 _v _q h4813
  have p4994 := n4994 _v _q h3069
  have p4984 := n4984 _v _q h4872
  have p4991 := n4991 _v _q h4608
  have p4989 := n4989 _v _q h4838
  have p4998 := n4998 _v _q h3152
  have p4995 := n4995 _v _q h4369
  have p17208 := n17208 _v _q h8398
  have p4999 := n4999 _v _q h91
  have p5001 := n5001 _v _q h4096
  have p4987 := n4987 _v _q h4434
  have p4988 := n4988 _v _q h488
  have p4996 := n4996 _v _q h3937
  have p5007 := n5007 _v _q h225
  have p4972 := n4972 _v _q h4899
  have p5008 := n5008 _v _q h4787
  have p8602 := n8602 _v _q h8038
  have p11473 := n11473 _v _q h6784
  change (e1995 _v) ∨ (¬ (e488 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e8398 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e3971 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4899 _v)) ∨ (¬ (e4787 _v)) ∨ (e2475 _v) ∨ (e2793 _v) at p17495
  change (¬ (e1995 _v)) at p17703
  change (¬ (e2475 _v)) at p8602
  change (¬ (e2793 _v)) at p11473
  rcases p17495 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact (False.elim (p17703 hlit))
  · exact (False.elim (hlit p4988))
  · exact (False.elim (hlit p4986))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p4994))
  · exact (False.elim (hlit p4984))
  · exact (False.elim (hlit p4991))
  · exact (False.elim (hlit p4989))
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p4995))
  · exact (False.elim (hlit p17208))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p5001))
  · exact (False.elim (hlit p4987))
  · exact hlit
  · exact (False.elim (hlit p4996))
  · exact (False.elim (hlit p5007))
  · exact (False.elim (hlit p4972))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (p8602 hlit))
  · exact (False.elim (p11473 hlit))
theorem n17707 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h225 : (e225 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h4096 : (e4096 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) (h6784 : (e6784 _v)) (h8038 : (e8038 _v)) (h8398 : (e8398 _v)) : (e7442 _v) := by
  have p15486 := n15486 _v _q 
  have p17706 := n17706 _v _q h91 h225 h488 h3069 h3105 h3152 h3937 h4096 h4369 h4434 h4608 h4787 h4813 h4838 h4872 h4899 h6784 h8038 h8398
  change (e7442 _v) ∨ (e3971 _v) at p15486
  change (¬ (e3971 _v)) at p17706
  rcases p15486 with hlit | hlit
  · exact hlit
  · exact (False.elim (p17706 hlit))
theorem n17709 (_v : Vars) (_q : Query _v)  : (e17708 _v) := by
  have p17668 := n17668 _v _q 
  have p17221 := n17221 _v _q 
  have p16913 := n16913 _v _q 
  change (¬ (e7688 _v)) ∨ (¬ (e5100 _v)) ∨ (¬ (e8335 _v)) ∨ (¬ (e4562 _v)) ∨ (e2310 _v) ∨ (¬ (e4128 _v)) ∨ (¬ (e3976 _v)) ∨ (¬ (e4477 _v)) ∨ (¬ (e4301 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e4724 _v)) ∨ (¬ (e4398 _v)) ∨ (¬ (e4648 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e3855 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e7749 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e7493 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e4491 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e2475 _v)) at p17668
  rcases p17668 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact (False.elim (hlit p17221))
  · exact (Or.inl hlit)
  · exact (Or.inr (Or.inl hlit))
  · exact (Or.inr (Or.inr (Or.inl hlit)))
  · exact (Or.inr (Or.inr (Or.inr (Or.inl hlit))))
  · exact (False.elim (hlit p16913))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hlit)))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hlit))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hlit)))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hlit))))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hlit)))))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hlit))))))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hlit)))))))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hlit))))))))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hlit)))))))))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hlit))))))))))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hlit)))))))))))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hlit))))))))))))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hlit)))))))))))))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hlit))))))))))))))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hlit)))))))))))))))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hlit))))))))))))))))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hlit)))))))))))))))))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hlit))))))))))))))))))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hlit)))))))))))))))))))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hlit))))))))))))))))))))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hlit)))))))))))))))))))))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hlit))))))))))))))))))))))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hlit)))))))))))))))))))))))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hlit))))))))))))))))))))))))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hlit)))))))))))))))))))))))))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hlit))))))))))))))))))))))))))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hlit)))))))))))))))))))))))))))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hlit))))))))))))))))))))))))))))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hlit)))))))))))))))))))))))))))))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hlit))))))))))))))))))))))))))))))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hlit)))))))))))))))))))))))))))))))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hlit))))))))))))))))))))))))))))))))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hlit)))))))))))))))))))))))))))))))))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hlit)))))))))))))))))))))))))))))))))))))
theorem n17711 (_v : Vars) (_q : Query _v)  : (e17710 _v) := by
  by_contra hc
  change ¬ ((e2371 _v) ∨ (e2310 _v) ∨ (¬ (e225 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e2592 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e3976 _v)) ∨ (¬ (e4491 _v)) ∨ (¬ (e3855 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4419 _v)) ∨ (¬ (e4899 _v)) ∨ (¬ (e4562 _v)) ∨ (¬ (e4128 _v)) ∨ (¬ (e4546 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e4301 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4398 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e4648 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e3169 _v)) ∨ (¬ (e4724 _v))) at hc
  have h70 : (e70 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))))))))
  have h191 : (e191 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))
  have h225 : (e225 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h442 : (e442 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))
  have h488 : (e488 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))
  have h2592 : (e2592 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h3069 : (e3069 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))))
  have h3105 : (e3105 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))))))
  have h3169 : (e3169 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))))))))))))
  have h3855 : (e3855 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))))))
  have h3946 : (e3946 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))))))))))
  have h3976 : (e3976 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h4059 : (e4059 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h4096 : (e4096 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))))))))
  have h4128 : (e4128 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h4139 : (e4139 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))
  have h4156 : (e4156 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))
  have h4199 : (e4199 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))))))))))
  have h4260 : (e4260 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))
  have h4301 : (e4301 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))
  have h4369 : (e4369 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))))
  have h4398 : (e4398 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))
  have h4419 : (e4419 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h4491 : (e4491 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h4546 : (e4546 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))
  have h4562 : (e4562 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h4608 : (e4608 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))
  have h4648 : (e4648 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))
  have h4675 : (e4675 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h4724 : (e4724 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn)))))))))))))))))))))))))))))))))))))))))
  have h4747 : (e4747 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))
  have h4838 : (e4838 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))
  have h4872 : (e4872 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))
  have h4899 : (e4899 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h6555 : (e6555 _v) := (fun hn => hc (Or.inr (Or.inl hn)))
  have h6579 : (e6579 _v) := (fun hn => hc (Or.inl hn))
  have p17669 := n17669 _v _q h70 h91 h191 h225 h442 h488 h2592 h3069 h3105 h3152 h3169 h3855 h3937 h3946 h3976 h4059 h4096 h4128 h4139 h4156 h4199 h4260 h4301 h4369 h4398 h4419 h4491 h4546 h4562 h4608 h4648 h4675 h4724 h4747 h4787 h4813 h4838 h4872 h4899 h6555 h6579
  exact p17669
theorem n17712 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2799 : (e2799 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3855 : (e3855 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4026 : (e4026 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4220 : (e4220 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4491 : (e4491 _v)) (h4546 : (e4546 _v)) (h4562 : (e4562 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) : (e3573 _v) := by
  have p14426 := n14426 _v _q 
  have p17671 := n17671 _v _q h30 h70 h91 h191 h225 h442 h488 h2799 h3069 h3105 h3152 h3169 h3855 h3937 h3946 h3976 h4026 h4059 h4096 h4139 h4156 h4199 h4220 h4260 h4285 h4301 h4369 h4398 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4724 h4747 h4787 h4813 h4838 h4872 h4899
  change (¬ (e2536 _v)) ∨ (¬ (e3572 _v)) at p14426
  rcases p14426 with hlit | hlit
  · exact (False.elim (hlit p17671))
  · exact hlit
theorem n17713 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2799 : (e2799 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3855 : (e3855 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4026 : (e4026 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4220 : (e4220 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4491 : (e4491 _v)) (h4546 : (e4546 _v)) (h4562 : (e4562 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) : (e3566 _v) := by
  have p7179 := n7179 _v _q 
  have p17712 := n17712 _v _q h30 h70 h91 h191 h225 h442 h488 h2799 h3069 h3105 h3152 h3169 h3855 h3937 h3946 h3976 h4026 h4059 h4096 h4139 h4156 h4199 h4220 h4260 h4285 h4301 h4369 h4398 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4724 h4747 h4787 h4813 h4838 h4872 h4899
  change (e3572 _v) ∨ (e3566 _v) at p7179
  change (¬ (e3572 _v)) at p17712
  rcases p7179 with hlit | hlit
  · exact (False.elim (p17712 hlit))
  · exact hlit
theorem n17714 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2799 : (e2799 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3855 : (e3855 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4026 : (e4026 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4220 : (e4220 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4491 : (e4491 _v)) (h4546 : (e4546 _v)) (h4562 : (e4562 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) : (e2310 _v) := by
  have p11439 := n11439 _v _q 
  have p17671 := n17671 _v _q h30 h70 h91 h191 h225 h442 h488 h2799 h3069 h3105 h3152 h3169 h3855 h3937 h3946 h3976 h4026 h4059 h4096 h4139 h4156 h4199 h4220 h4260 h4285 h4301 h4369 h4398 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4724 h4747 h4787 h4813 h4838 h4872 h4899
  change (¬ (e2536 _v)) ∨ (e2310 _v) at p11439
  rcases p11439 with hlit | hlit
  · exact (False.elim (hlit p17671))
  · exact hlit
theorem n17715 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2799 : (e2799 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3855 : (e3855 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4026 : (e4026 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4220 : (e4220 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4491 : (e4491 _v)) (h4546 : (e4546 _v)) (h4562 : (e4562 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) : (e3278 _v) := by
  have p14378 := n14378 _v _q 
  have p17714 := n17714 _v _q h30 h70 h91 h191 h225 h442 h488 h2799 h3069 h3105 h3152 h3169 h3855 h3937 h3946 h3976 h4026 h4059 h4096 h4139 h4156 h4199 h4220 h4260 h4285 h4301 h4369 h4398 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4724 h4747 h4787 h4813 h4838 h4872 h4899
  change (¬ (e2310 _v)) ∨ (¬ (e3277 _v)) at p14378
  rcases p14378 with hlit | hlit
  · exact (False.elim (hlit p17714))
  · exact hlit
theorem n17716 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2799 : (e2799 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3855 : (e3855 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4026 : (e4026 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4220 : (e4220 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4491 : (e4491 _v)) (h4546 : (e4546 _v)) (h4562 : (e4562 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) : (e3271 _v) := by
  have p6982 := n6982 _v _q 
  have p17715 := n17715 _v _q h30 h70 h91 h191 h225 h442 h488 h2799 h3069 h3105 h3152 h3169 h3855 h3937 h3946 h3976 h4026 h4059 h4096 h4139 h4156 h4199 h4220 h4260 h4285 h4301 h4369 h4398 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4724 h4747 h4787 h4813 h4838 h4872 h4899
  change (e3277 _v) ∨ (e3271 _v) at p6982
  change (¬ (e3277 _v)) at p17715
  rcases p6982 with hlit | hlit
  · exact (False.elim (p17715 hlit))
  · exact hlit
theorem n17717 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2799 : (e2799 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3855 : (e3855 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4026 : (e4026 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4220 : (e4220 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4491 : (e4491 _v)) (h4546 : (e4546 _v)) (h4562 : (e4562 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) : (e7489 _v) := by
  have p17640 := n17640 _v _q h30 h70 h91 h191 h225 h442 h488 h2799 h3069 h3105 h3152 h3169 h3855 h3937 h3946 h3976 h4026 h4059 h4096 h4139 h4156 h4199 h4220 h4260 h4285 h4301 h4369 h4398 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4724 h4747 h4787 h4813 h4838 h4872 h4899
  have p16342 := n16342 _v _q 
  have p17713 := n17713 _v _q h30 h70 h91 h191 h225 h442 h488 h2799 h3069 h3105 h3152 h3169 h3855 h3937 h3946 h3976 h4026 h4059 h4096 h4139 h4156 h4199 h4220 h4260 h4285 h4301 h4369 h4398 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4724 h4747 h4787 h4813 h4838 h4872 h4899
  have p5257 := n5257 _v _q 
  have p17134 := n17134 _v _q h4398
  have p10893 := n10893 _v _q 
  have p16464 := n16464 _v _q h2799
  have p8511 := n8511 _v _q h2799
  have p4978 := n4978 _v _q h4477
  have p4979 := n4979 _v _q h4139
  have p4980 := n4980 _v _q h4301
  have p5005 := n5005 _v _q h3169
  have p16394 := n16394 _v _q 
  have p4973 := n4973 _v _q h4562
  have p4985 := n4985 _v _q h4156
  have p4987 := n4987 _v _q h4434
  have p16461 := n16461 _v _q h2799
  have p4983 := n4983 _v _q h4813
  have p16175 := n16175 _v _q 
  have p17074 := n17074 _v _q 
  have p4975 := n4975 _v _q h4026
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
  have p16913 := n16913 _v _q 
  have p17102 := n17102 _v _q 
  have p17096 := n17096 _v _q 
  have p17106 := n17106 _v _q 
  have p4977 := n4977 _v _q h4285
  have p17122 := n17122 _v _q 
  have p17104 := n17104 _v _q 
  have p4995 := n4995 _v _q h4369
  have p17124 := n17124 _v _q 
  have p17108 := n17108 _v _q 
  have p4994 := n4994 _v _q h3069
  have p17117 := n17117 _v _q 
  have p17120 := n17120 _v _q 
  have p17069 := n17069 _v _q 
  have p17093 := n17093 _v _q 
  have p17141 := n17141 _v _q 
  have p17131 := n17131 _v _q 
  have p4996 := n4996 _v _q h3937
  have p4999 := n4999 _v _q h91
  have p4998 := n4998 _v _q h3152
  have p16250 := n16250 _v _q h3855
  have p5001 := n5001 _v _q h4096
  have p5000 := n5000 _v _q h30
  have p17136 := n17136 _v _q 
  have p17128 := n17128 _v _q h4491
  have p17127 := n17127 _v _q 
  have p5003 := n5003 _v _q h4199
  have p5004 := n5004 _v _q h4220
  have p17053 := n17053 _v _q 
  have p17076 := n17076 _v _q h3976
  have p17056 := n17056 _v _q h3946
  have p5007 := n5007 _v _q h225
  have p5008 := n5008 _v _q h4787
  have p17055 := n17055 _v _q 
  have p17061 := n17061 _v _q h4747
  have p17147 := n17147 _v _q 
  have p17133 := n17133 _v _q 
  have p5010 := n5010 _v _q h70
  have p17137 := n17137 _v _q h4059
  have p5006 := n5006 _v _q h4675
  have p17094 := n17094 _v _q h4724
  have p17064 := n17064 _v _q 
  have p4971 := n4971 _v _q h4419
  have p16929 := n16929 _v _q 
  have p4972 := n4972 _v _q h4899
  have p13951 := n13951 _v _q 
  have p17716 := n17716 _v _q h30 h70 h91 h191 h225 h442 h488 h2799 h3069 h3105 h3152 h3169 h3855 h3937 h3946 h3976 h4026 h4059 h4096 h4139 h4156 h4199 h4220 h4260 h4285 h4301 h4369 h4398 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4724 h4747 h4787 h4813 h4838 h4872 h4899
  have p4976 := n4976 _v _q h4546
  have p17714 := n17714 _v _q h30 h70 h91 h191 h225 h442 h488 h2799 h3069 h3105 h3152 h3169 h3855 h3937 h3946 h3976 h4026 h4059 h4096 h4139 h4156 h4199 h4220 h4260 h4285 h4301 h4369 h4398 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4724 h4747 h4787 h4813 h4838 h4872 h4899
  have p16484 := n16484 _v _q h2799
  have p5255 := n5255 _v _q 
  exact FloorCertificate.node_17717 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e61 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2834 _v) (e2849 _v) (e2863 _v) (e2877 _v) (e2879 _v) (e2883 _v) (e2898 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2913 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e3164 _v) (e3574 _v) (e4215 _v) (e4541 _v) (e4808 _v) p17640 p16342 p17713 p5257 p17134 p10893 p16464 p8511 p4978 p4979 p4980 p5005 p16394 p4973 p4985 p4987 p16461 p4983 p16175 p17074 p4975 p4988 p4981 p4989 p17072 p4986 p17080 p17078 p17091 p253 p17098 p4990 p17100 p4984 p17067 p17087 p4991 p4992 p17115 p17083 p17110 p16576 p17058 p17113 p16913 p17102 p17096 p17106 p4977 p17122 p17104 p4995 p17124 p17108 p4994 p17117 p17120 p17069 p17093 p17141 p17131 p4996 p4999 p4998 p16250 p5001 p5000 p17136 p17128 p17127 p5003 p5004 p17053 p17076 p17056 p5007 p5008 p17055 p17061 p17147 p17133 p5010 p17137 p5006 p17094 p17064 p4971 p16929 p4972 p13951 p17716 p4976 p17714 p16484 p5255
theorem n17718 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4026 : (e4026 _v)) (h4059 : (e4059 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4220 : (e4220 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4491 : (e4491 _v)) (h4546 : (e4546 _v)) (h4562 : (e4562 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) (h6531 : (e6531 _v)) (h8398 : (e8398 _v)) : (e4856 _v) := by
  have p17422 := n17422 _v _q 
  have p17672 := n17672 _v _q h30 h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3169 h3937 h3946 h3976 h4026 h4059 h4096 h4139 h4156 h4199 h4220 h4260 h4285 h4301 h4369 h4419 h4434 h4477 h4491 h4546 h4562 h4608 h4648 h4675 h4747 h4787 h4813 h4838 h4872 h4899 h6531 h8398
  have p5001 := n5001 _v _q h4096
  have p17128 := n17128 _v _q h4491
  have p5003 := n5003 _v _q h4199
  have p17208 := n17208 _v _q h8398
  have p5004 := n5004 _v _q h4220
  have p17076 := n17076 _v _q h3976
  have p5005 := n5005 _v _q h3169
  have p17056 := n17056 _v _q h3946
  have p5007 := n5007 _v _q h225
  have p5008 := n5008 _v _q h4787
  have p16779 := n16779 _v _q 
  have p15463 := n15463 _v _q h6531
  have p17061 := n17061 _v _q h4747
  have p5010 := n5010 _v _q h70
  have p17137 := n17137 _v _q h4059
  have p5006 := n5006 _v _q h4675
  have p12864 := n12864 _v _q h6531
  have p16487 := n16487 _v _q h6531
  have p4971 := n4971 _v _q h4419
  have p4972 := n4972 _v _q h4899
  have p4973 := n4973 _v _q h4562
  have p4975 := n4975 _v _q h4026
  have p4976 := n4976 _v _q h4546
  have p4977 := n4977 _v _q h4285
  have p4978 := n4978 _v _q h4477
  have p4979 := n4979 _v _q h4139
  have p4980 := n4980 _v _q h4301
  have p4981 := n4981 _v _q h4260
  have p4983 := n4983 _v _q h4813
  have p4984 := n4984 _v _q h4872
  have p4985 := n4985 _v _q h4156
  have p4986 := n4986 _v _q h3105
  have p4987 := n4987 _v _q h4434
  have p4988 := n4988 _v _q h488
  have p4989 := n4989 _v _q h4838
  have p253 := n253 _v _q h191
  have p4990 := n4990 _v _q h4648
  have p4991 := n4991 _v _q h4608
  have p4992 := n4992 _v _q h442
  have p4994 := n4994 _v _q h3069
  have p4995 := n4995 _v _q h4369
  have p4996 := n4996 _v _q h3937
  have p15477 := n15477 _v _q h6531
  have p4998 := n4998 _v _q h3152
  have p4999 := n4999 _v _q h91
  have p5000 := n5000 _v _q h30
  change (e2482 _v) ∨ (¬ (e2371 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e4491 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e4220 _v)) ∨ (¬ (e4720 _v)) ∨ (¬ (e3976 _v)) ∨ (¬ (e3169 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e3851 _v)) ∨ (¬ (e8398 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e3267 _v)) ∨ (¬ (e3585 _v)) ∨ (¬ (e4419 _v)) ∨ (¬ (e4899 _v)) ∨ (¬ (e4562 _v)) ∨ (¬ (e4026 _v)) ∨ (¬ (e4546 _v)) ∨ (¬ (e4285 _v)) ∨ (¬ (e4477 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e4301 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e4648 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e4855 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e30 _v)) at p17422
  change (¬ (e2482 _v)) at p12864
  rcases p17422 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact (False.elim (p12864 hlit))
  · exact (False.elim (hlit p17672))
  · exact (False.elim (hlit p5001))
  · exact (False.elim (hlit p17128))
  · exact (False.elim (hlit p5003))
  · exact (False.elim (hlit p5004))
  · exact (False.elim (hlit p15463))
  · exact (False.elim (hlit p17076))
  · exact (False.elim (hlit p5005))
  · exact (False.elim (hlit p17056))
  · exact (False.elim (hlit p5007))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p16779))
  · exact (False.elim (hlit p17208))
  · exact (False.elim (hlit p17061))
  · exact (False.elim (hlit p5010))
  · exact (False.elim (hlit p17137))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p16487))
  · exact (False.elim (hlit p15477))
  · exact (False.elim (hlit p4971))
  · exact (False.elim (hlit p4972))
  · exact (False.elim (hlit p4973))
  · exact (False.elim (hlit p4975))
  · exact (False.elim (hlit p4976))
  · exact (False.elim (hlit p4977))
  · exact (False.elim (hlit p4978))
  · exact (False.elim (hlit p4979))
  · exact (False.elim (hlit p4980))
  · exact (False.elim (hlit p4981))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p4984))
  · exact (False.elim (hlit p4985))
  · exact (False.elim (hlit p4986))
  · exact (False.elim (hlit p4987))
  · exact (False.elim (hlit p4988))
  · exact (False.elim (hlit p4989))
  · exact (False.elim (hlit p253))
  · exact (False.elim (hlit p4990))
  · exact (False.elim (hlit p4991))
  · exact (False.elim (hlit p4992))
  · exact (False.elim (hlit p4994))
  · exact (False.elim (hlit p4995))
  · exact (False.elim (hlit p4996))
  · exact hlit
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p5000))
theorem n17719 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2799 : (e2799 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3267 : (e3267 _v)) (h3585 : (e3585 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3971 : (e3971 _v)) (h4096 : (e4096 _v)) (h4128 : (e4128 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4486 : (e4486 _v)) (h4546 : (e4546 _v)) (h4562 : (e4562 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4855 : (e4855 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) (h6684 : (e6684 _v)) : (e6636 _v) := by
  have p12804 := n12804 _v _q h6684
  have p5255 := n5255 _v _q 
  have p10893 := n10893 _v _q 
  have p17673 := n17673 _v _q h30 h70 h91 h191 h225 h442 h488 h2799 h3069 h3105 h3152 h3169 h3267 h3585 h3937 h3946 h3971 h4096 h4128 h4139 h4156 h4199 h4260 h4285 h4301 h4369 h4419 h4434 h4477 h4486 h4546 h4562 h4608 h4648 h4675 h4787 h4813 h4838 h4855 h4872 h4899 h6684
  exact FloorCertificate.node_17719 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p12804 p5255 p10893 p17673
theorem n17720 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2799 : (e2799 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3169 : (e3169 _v)) (h3267 : (e3267 _v)) (h3585 : (e3585 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3971 : (e3971 _v)) (h4096 : (e4096 _v)) (h4128 : (e4128 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4486 : (e4486 _v)) (h4546 : (e4546 _v)) (h4562 : (e4562 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4855 : (e4855 _v)) (h4872 : (e4872 _v)) (h4899 : (e4899 _v)) (h6684 : (e6684 _v)) : (e7912 _v) := by
  have p14591 := n14591 _v _q 
  have p17719 := n17719 _v _q h30 h70 h91 h191 h225 h442 h488 h2799 h3069 h3105 h3152 h3169 h3267 h3585 h3937 h3946 h3971 h4096 h4128 h4139 h4156 h4199 h4260 h4285 h4301 h4369 h4419 h4434 h4477 h4486 h4546 h4562 h4608 h4648 h4675 h4787 h4813 h4838 h4855 h4872 h4899 h6684
  change (e2482 _v) ∨ (¬ (e7904 _v)) at p14591
  change (¬ (e2482 _v)) at p17719
  rcases p14591 with hlit | hlit
  · exact (False.elim (p17719 hlit))
  · exact hlit
end
end Assembly
