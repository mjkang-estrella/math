import Dag223
import generated.th_lemma_28
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n20080 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e4059 _v) := by
  have p14980 := n14980 _v _q 
  have p20079 := n20079 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  change (e4066 _v) ∨ (e4059 _v) at p14980
  change (¬ (e4066 _v)) at p20079
  rcases p14980 with hlit | hlit
  · exact (False.elim (p20079 hlit))
  · exact hlit
theorem n20081 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e2634 _v) := by
  have p11030 := n11030 _v _q 
  have p20077 := n20077 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  change (e2634 _v) ∨ (¬ (e2781 _v)) at p11030
  rcases p11030 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p20077))
theorem n20082 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e48 _v) := by
  have p20081 := n20081 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  have p5257 := n5257 _v _q 
  have p20077 := n20077 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  exact FloorCertificate.node_20082 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p20081 p5257 p20077
theorem n20083 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e60 _v) := by
  have p14152 := n14152 _v _q 
  have p20082 := n20082 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  change (¬ (e48 _v)) ∨ (¬ (e59 _v)) at p14152
  rcases p14152 with hlit | hlit
  · exact (False.elim (hlit p20082))
  · exact hlit
theorem n20084 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e2310 _v) := by
  have p11365 := n11365 _v _q 
  have p20081 := n20081 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  change (e2310 _v) ∨ (¬ (e2634 _v)) at p11365
  rcases p11365 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p20081))
theorem n20085 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e2254 _v) := by
  have p11361 := n11361 _v _q 
  have p20084 := n20084 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  change (e2254 _v) ∨ (¬ (e2310 _v)) at p11361
  rcases p11361 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p20084))
theorem n20086 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e4271 _v) := by
  have p14699 := n14699 _v _q 
  have p20077 := n20077 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  change (¬ (e2781 _v)) ∨ (¬ (e4270 _v)) at p14699
  rcases p14699 with hlit | hlit
  · exact (False.elim (hlit p20077))
  · exact hlit
theorem n20087 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e4264 _v) := by
  have p14966 := n14966 _v _q 
  have p20086 := n20086 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  change (e4270 _v) ∨ (e4264 _v) at p14966
  change (¬ (e4270 _v)) at p20086
  rcases p14966 with hlit | hlit
  · exact (False.elim (p20086 hlit))
  · exact hlit
theorem n20088 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e2482 _v) := by
  have p11035 := n11035 _v _q 
  have p20081 := n20081 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  change (¬ (e2634 _v)) ∨ (e2482 _v) at p11035
  rcases p11035 with hlit | hlit
  · exact (False.elim (hlit p20081))
  · exact hlit
theorem n20089 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e4405 _v) := by
  have p14702 := n14702 _v _q 
  have p20088 := n20088 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  change (¬ (e2482 _v)) ∨ (¬ (e4404 _v)) at p14702
  rcases p14702 with hlit | hlit
  · exact (False.elim (hlit p20088))
  · exact hlit
theorem n20090 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e2733 _v) := by
  have p8424 := n8424 _v _q 
  have p20077 := n20077 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  change (e2733 _v) ∨ (¬ (e2781 _v)) at p8424
  rcases p8424 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p20077))
theorem n20091 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e4109 _v) := by
  have p14689 := n14689 _v _q 
  have p20090 := n20090 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  change (¬ (e2733 _v)) ∨ (¬ (e4108 _v)) at p14689
  rcases p14689 with hlit | hlit
  · exact (False.elim (hlit p20090))
  · exact hlit
theorem n20092 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e4101 _v) := by
  have p14929 := n14929 _v _q 
  have p20091 := n20091 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  change (e4108 _v) ∨ (e4101 _v) at p14929
  change (¬ (e4108 _v)) at p20091
  rcases p14929 with hlit | hlit
  · exact (False.elim (p20091 hlit))
  · exact hlit
theorem n20094 (_v : Vars) (_q : Query _v)  : (e20093 _v) := by
  by_contra hc
  change ¬ ((e1995 _v) ∨ (¬ (e70 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e3152 _v))) at hc
  have h70 : (e70 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h225 : (e225 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h442 : (e442 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h488 : (e488 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h3069 : (e3069 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))))))))))))
  have h4096 : (e4096 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h4156 : (e4156 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4199 : (e4199 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h4260 : (e4260 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h4369 : (e4369 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h4675 : (e4675 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h6423 : (e6423 _v) := (fun hn => hc (Or.inl hn))
  have p20067 := n20067 _v _q h70 h91 h225 h442 h488 h3069 h3152 h4096 h4156 h4199 h4260 h4369 h4675 h4787 h4813 h6423
  exact p20067
theorem n20095 (_v : Vars) (_q : Query _v)  : (e4499 _v) := by
  have p14700 := n14700 _v _q 
  have p20071 := n20071 _v _q 
  change (¬ (e2697 _v)) ∨ (¬ (e4498 _v)) at p14700
  rcases p14700 with hlit | hlit
  · exact (False.elim (hlit p20071))
  · exact hlit
theorem n20096 (_v : Vars) (_q : Query _v)  : (e4491 _v) := by
  have p14969 := n14969 _v _q 
  have p20095 := n20095 _v _q 
  change (e4498 _v) ∨ (e4491 _v) at p14969
  change (¬ (e4498 _v)) at p20095
  rcases p14969 with hlit | hlit
  · exact (False.elim (p20095 hlit))
  · exact hlit
theorem n20097 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h6423 : (e6423 _v)) : (e5138 _v) := by
  have p20059 := n20059 _v _q h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4156 h4199 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872 h6423
  have p8452 := n8452 _v _q h6423
  exact FloorCertificate.node_20097 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) p20059 p8452
theorem n20098 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4059 : (e4059 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h6423 : (e6423 _v)) : (e7489 _v) := by
  have p15115 := n15115 _v _q 
  have p20073 := n20073 _v _q h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4156 h4199 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872 h6423
  have p20097 := n20097 _v _q h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4156 h4199 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872 h6423
  change (e79 _v) ∨ (¬ (e5149 _v)) at p15115
  change (¬ (e79 _v)) at p20097
  rcases p15115 with hlit | hlit
  · exact (False.elim (p20097 hlit))
  · exact (False.elim (hlit p20073))
theorem n20099 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4306 : (e4306 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4434 : (e4434 _v)) (h4491 : (e4491 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5100 : (e5100 _v)) (h5208 : (e5208 _v)) (h6454 : (e6454 _v)) (h6571 : (e6571 _v)) (h7749 : (e7749 _v)) (h7814 : (e7814 _v)) (h8045 : (e8045 _v)) : (e8310 _v) := by
  have p14906 := n14906 _v _q 
  have p20076 := n20076 _v _q h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h3976 h4059 h4156 h4199 h4306 h4369 h4398 h4434 h4491 h4567 h4608 h4653 h4675 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h5208 h6454 h6571 h7749 h7814 h8045
  change (¬ (e2529 _v)) ∨ (¬ (e8301 _v)) at p14906
  rcases p14906 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p20076))
theorem n20100 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4306 : (e4306 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4434 : (e4434 _v)) (h4491 : (e4491 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5100 : (e5100 _v)) (h5208 : (e5208 _v)) (h6454 : (e6454 _v)) (h6571 : (e6571 _v)) (h7749 : (e7749 _v)) (h7814 : (e7814 _v)) (h8045 : (e8045 _v)) : (e8322 _v) := by
  have p15218 := n15218 _v _q 
  have p20099 := n20099 _v _q h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h3976 h4059 h4156 h4199 h4306 h4369 h4398 h4434 h4491 h4567 h4608 h4653 h4675 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h5208 h6454 h6571 h7749 h7814 h8045
  change (e2529 _v) ∨ (¬ (e8321 _v)) at p15218
  change (¬ (e2529 _v)) at p20099
  rcases p15218 with hlit | hlit
  · exact (False.elim (p20099 hlit))
  · exact hlit
theorem n20101 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4306 : (e4306 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4434 : (e4434 _v)) (h4491 : (e4491 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5100 : (e5100 _v)) (h5208 : (e5208 _v)) (h6454 : (e6454 _v)) (h6571 : (e6571 _v)) (h7749 : (e7749 _v)) (h7814 : (e7814 _v)) (h8045 : (e8045 _v)) : (e8317 _v) := by
  have p11541 := n11541 _v _q 
  have p20100 := n20100 _v _q h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h3976 h4059 h4156 h4199 h4306 h4369 h4398 h4434 h4491 h4567 h4608 h4653 h4675 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h5208 h6454 h6571 h7749 h7814 h8045
  change (e8321 _v) ∨ (e8317 _v) at p11541
  change (¬ (e8321 _v)) at p20100
  rcases p11541 with hlit | hlit
  · exact (False.elim (p20100 hlit))
  · exact hlit
theorem n20102 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e4731 _v) := by
  have p14698 := n14698 _v _q 
  have p20085 := n20085 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  change (¬ (e2254 _v)) ∨ (¬ (e4730 _v)) at p14698
  rcases p14698 with hlit | hlit
  · exact (False.elim (hlit p20085))
  · exact hlit
theorem n20103 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e4724 _v) := by
  have p15518 := n15518 _v _q 
  have p20102 := n20102 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  change (e4730 _v) ∨ (e4724 _v) at p15518
  change (¬ (e4730 _v)) at p20102
  rcases p15518 with hlit | hlit
  · exact (False.elim (p20102 hlit))
  · exact hlit
theorem n20104 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e2697 _v) := by
  have p11391 := n11391 _v _q 
  have p20085 := n20085 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  change (e2697 _v) ∨ (¬ (e2254 _v)) at p11391
  rcases p11391 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p20085))
theorem n20105 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e4499 _v) := by
  have p14700 := n14700 _v _q 
  have p20104 := n20104 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  change (¬ (e2697 _v)) ∨ (¬ (e4498 _v)) at p14700
  rcases p14700 with hlit | hlit
  · exact (False.elim (hlit p20104))
  · exact hlit
theorem n20106 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e4491 _v) := by
  have p14969 := n14969 _v _q 
  have p20105 := n20105 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  change (e4498 _v) ∨ (e4491 _v) at p14969
  change (¬ (e4498 _v)) at p20105
  rcases p14969 with hlit | hlit
  · exact (False.elim (p20105 hlit))
  · exact hlit
theorem n20107 (_v : Vars) (_q : Query _v) (h5195 : (e5195 _v)) : (e4306 _v) := by
  have p14984 := n14984 _v _q 
  have p15991 := n15991 _v _q h5195
  change (e4313 _v) ∨ (e4306 _v) at p14984
  change (¬ (e4313 _v)) at p15991
  rcases p14984 with hlit | hlit
  · exact (False.elim (p15991 hlit))
  · exact hlit
theorem n20108 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e4398 _v) := by
  have p14976 := n14976 _v _q 
  have p20089 := n20089 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  change (e4404 _v) ∨ (e4398 _v) at p14976
  change (¬ (e4404 _v)) at p20089
  rcases p14976 with hlit | hlit
  · exact (False.elim (p20089 hlit))
  · exact hlit
theorem n20109 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h5195 : (e5195 _v)) : (e1995 _v) := by
  have p17376 := n17376 _v _q 
  have p17276 := n17276 _v _q h5195
  have p12839 := n12839 _v _q h5195
  have p4992 := n4992 _v _q h442
  have p15274 := n15274 _v _q h5195
  have p5008 := n5008 _v _q h4787
  have p5006 := n5006 _v _q h4675
  have p17056 := n17056 _v _q h3946
  have p17061 := n17061 _v _q h4747
  have p4995 := n4995 _v _q h4369
  have p4983 := n4983 _v _q h4813
  have p20107 := n20107 _v _q h5195
  have p17022 := n17022 _v _q h4434 h5195
  have p4985 := n4985 _v _q h4156
  have p4988 := n4988 _v _q h488
  have p4986 := n4986 _v _q h3105
  have p4984 := n4984 _v _q h4872
  have p4991 := n4991 _v _q h4608
  have p4994 := n4994 _v _q h3069
  have p4998 := n4998 _v _q h3152
  have p4996 := n4996 _v _q h3937
  have p20108 := n20108 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  have p4987 := n4987 _v _q h4434
  have p20077 := n20077 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  change (e1995 _v) ∨ (¬ (e4813 _v)) ∨ (e2358 _v) ∨ (¬ (e442 _v)) ∨ (¬ (e5208 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e8317 _v)) ∨ (¬ (e8045 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e4398 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e2781 _v)) at p17376
  change (¬ (e2358 _v)) at p12839
  rcases p17376 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p4983))
  · exact (False.elim (p12839 hlit))
  · exact (False.elim (hlit p4992))
  · exact (False.elim (hlit p15274))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p17056))
  · exact (False.elim (hlit p17061))
  · exact (False.elim (hlit p4995))
  · exact (False.elim (hlit p20107))
  · exact (False.elim (hlit p17276))
  · exact (False.elim (hlit p17022))
  · exact (False.elim (hlit p4985))
  · exact (False.elim (hlit p4988))
  · exact (False.elim (hlit p4986))
  · exact (False.elim (hlit p4984))
  · exact (False.elim (hlit p4991))
  · exact (False.elim (hlit p4994))
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p4996))
  · exact (False.elim (hlit p20108))
  · exact (False.elim (hlit p4987))
  · exact (False.elim (hlit p20077))
theorem n20110 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3152 : (e3152 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) : (e1995 _v) := by
  have p20094 := n20094 _v _q 
  have p5010 := n5010 _v _q h70
  have p5008 := n5008 _v _q h4787
  have p4994 := n4994 _v _q h3069
  have p4985 := n4985 _v _q h4156
  have p4988 := n4988 _v _q h488
  have p5006 := n5006 _v _q h4675
  have p5001 := n5001 _v _q h4096
  have p5003 := n5003 _v _q h4199
  have p4999 := n4999 _v _q h91
  have p4992 := n4992 _v _q h442
  have p5007 := n5007 _v _q h225
  have p4981 := n4981 _v _q h4260
  have p4983 := n4983 _v _q h4813
  have p4995 := n4995 _v _q h4369
  have p4998 := n4998 _v _q h3152
  change (e1995 _v) ∨ (¬ (e70 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e3152 _v)) at p20094
  rcases p20094 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p5010))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p4994))
  · exact (False.elim (hlit p4985))
  · exact (False.elim (hlit p4988))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p5001))
  · exact (False.elim (hlit p5003))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p4992))
  · exact (False.elim (hlit p5007))
  · exact (False.elim (hlit p4981))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p4995))
  · exact (False.elim (hlit p4998))
theorem n20111 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e1995 _v) := by
  have p20094 := n20094 _v _q 
  have p16619 := n16619 _v _q h6784
  have p16626 := n16626 _v _q h6784
  have p15702 := n15702 _v _q h6784
  have p19760 := n19760 _v _q h6784
  have p19762 := n19762 _v _q h6784
  have p16598 := n16598 _v _q h6784
  have p15705 := n15705 _v _q h6784
  have p16856 := n16856 _v _q h6784
  have p19747 := n19747 _v _q h6784
  have p16854 := n16854 _v _q h6784
  have p19772 := n19772 _v _q h6784
  have p16603 := n16603 _v _q h6784
  have p16625 := n16625 _v _q h6784
  have p16620 := n16620 _v _q h6784
  have p19771 := n19771 _v _q h6784
  change (e1995 _v) ∨ (¬ (e70 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e3152 _v)) at p20094
  rcases p20094 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p16619))
  · exact (False.elim (hlit p16626))
  · exact (False.elim (hlit p15702))
  · exact (False.elim (hlit p19760))
  · exact (False.elim (hlit p19762))
  · exact (False.elim (hlit p16598))
  · exact (False.elim (hlit p15705))
  · exact (False.elim (hlit p16856))
  · exact (False.elim (hlit p19747))
  · exact (False.elim (hlit p16854))
  · exact (False.elim (hlit p19772))
  · exact (False.elim (hlit p16603))
  · exact (False.elim (hlit p16625))
  · exact (False.elim (hlit p16620))
  · exact (False.elim (hlit p19771))
theorem n20113 (_v : Vars) (_q : Query _v)  : (e20112 _v) := by
  by_contra hc
  change ¬ ((e1995 _v) ∨ (¬ (e91 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e3946 _v))) at hc
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h225 : (e225 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h442 : (e442 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h488 : (e488 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h3069 : (e3069 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h3105 : (e3105 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))
  have h3946 : (e3946 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn)))))))))))))))))))))
  have h4059 : (e4059 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h4156 : (e4156 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4199 : (e4199 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h4369 : (e4369 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))
  have h4434 : (e4434 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))
  have h4608 : (e4608 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h4675 : (e4675 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h4747 : (e4747 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))
  have h4872 : (e4872 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h6423 : (e6423 _v) := (fun hn => hc (Or.inl hn))
  have p20098 := n20098 _v _q h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4156 h4199 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872 h6423
  exact p20098
theorem n20114 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4306 : (e4306 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4434 : (e4434 _v)) (h4491 : (e4491 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5100 : (e5100 _v)) (h5208 : (e5208 _v)) (h6454 : (e6454 _v)) (h6571 : (e6571 _v)) (h7749 : (e7749 _v)) (h7814 : (e7814 _v)) (h8045 : (e8045 _v)) : (e7489 _v) := by
  have p20101 := n20101 _v _q h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h3976 h4059 h4156 h4199 h4306 h4369 h4398 h4434 h4491 h4567 h4608 h4653 h4675 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h5208 h6454 h6571 h7749 h7814 h8045
  have p17102 := n17102 _v _q 
  have p17104 := n17104 _v _q 
  have p17106 := n17106 _v _q 
  have p17108 := n17108 _v _q 
  have p17110 := n17110 _v _q 
  have p4016 := n4016 _v _q 
  have p16977 := n16977 _v _q 
  have p16947 := n16947 _v _q h91 h6454
  have p20074 := n20074 _v _q h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4059 h4156 h4199 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872 h6454
  have p17113 := n17113 _v _q 
  have p4994 := n4994 _v _q h3069
  have p17117 := n17117 _v _q 
  have p17255 := n17255 _v _q h6571
  have p17120 := n17120 _v _q 
  have p4987 := n4987 _v _q h4434
  have p16929 := n16929 _v _q 
  have p16269 := n16269 _v _q h7749
  have p17009 := n17009 _v _q 
  have p17122 := n17122 _v _q 
  have p4991 := n4991 _v _q h4608
  have p16576 := n16576 _v _q 
  have p17124 := n17124 _v _q 
  have p4999 := n4999 _v _q h91
  have p4996 := n4996 _v _q h3937
  have p16950 := n16950 _v _q h91 h6454
  have p17147 := n17147 _v _q 
  have p5003 := n5003 _v _q h4199
  have p4998 := n4998 _v _q h3152
  have p17127 := n17127 _v _q 
  have p17128 := n17128 _v _q h4491
  have p4983 := n4983 _v _q h4813
  have p5008 := n5008 _v _q h4787
  have p17256 := n17256 _v _q 
  have p17129 := n17129 _v _q h4903
  have p17175 := n17175 _v _q h5208
  have p5006 := n5006 _v _q h4675
  have p17159 := n17159 _v _q h5100
  have p17131 := n17131 _v _q 
  have p17172 := n17172 _v _q h7814
  have p17133 := n17133 _v _q 
  have p17134 := n17134 _v _q h4398
  have p17136 := n17136 _v _q 
  have p17157 := n17157 _v _q h8045
  have p17137 := n17137 _v _q h4059
  have p17138 := n17138 _v _q h4306
  have p5007 := n5007 _v _q h225
  have p16778 := n16778 _v _q 
  have p17141 := n17141 _v _q 
  have p4992 := n4992 _v _q h442
  have p17143 := n17143 _v _q h4567
  have p17050 := n17050 _v _q 
  have p17053 := n17053 _v _q 
  have p17055 := n17055 _v _q 
  have p17056 := n17056 _v _q h3946
  have p17058 := n17058 _v _q 
  have p17060 := n17060 _v _q h4653
  have p17061 := n17061 _v _q h4747
  have p17064 := n17064 _v _q 
  have p4995 := n4995 _v _q h4369
  have p17067 := n17067 _v _q 
  have p17069 := n17069 _v _q 
  have p17072 := n17072 _v _q 
  have p17074 := n17074 _v _q 
  have p17076 := n17076 _v _q h3976
  have p4985 := n4985 _v _q h4156
  have p4988 := n4988 _v _q h488
  have p17078 := n17078 _v _q 
  have p4986 := n4986 _v _q h3105
  have p17080 := n17080 _v _q 
  have p17083 := n17083 _v _q 
  have p4984 := n4984 _v _q h4872
  have p17087 := n17087 _v _q 
  have p17091 := n17091 _v _q 
  have p17094 := n17094 _v _q h4724
  have p17093 := n17093 _v _q 
  have p17111 := n17111 _v _q 
  have p17115 := n17115 _v _q 
  have p17089 := n17089 _v _q 
  have p17100 := n17100 _v _q 
  have p17098 := n17098 _v _q 
  have p17096 := n17096 _v _q 
  have p5255 := n5255 _v _q 
  have p8663 := n8663 _v _q 
  have p13951 := n13951 _v _q 
  have p8430 := n8430 _v _q h6454
  have p8447 := n8447 _v _q h6571
  exact FloorCertificate.node_20114 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2849 _v) (e2863 _v) (e2877 _v) (e2883 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p20101 p17102 p17104 p17106 p17108 p17110 p4016 p16977 p16947 p20074 p17113 p4994 p17117 p17255 p17120 p4987 p16929 p16269 p17009 p17122 p4991 p16576 p17124 p4999 p4996 p16950 p17147 p5003 p4998 p17127 p17128 p4983 p5008 p17256 p17129 p17175 p5006 p17159 p17131 p17172 p17133 p17134 p17136 p17157 p17137 p17138 p5007 p16778 p17141 p4992 p17143 p17050 p17053 p17055 p17056 p17058 p17060 p17061 p17064 p4995 p17067 p17069 p17072 p17074 p17076 p4985 p4988 p17078 p4986 p17080 p17083 p4984 p17087 p17091 p17094 p17093 p17111 p17115 p17089 p17100 p17098 p17096 p5255 p8663 p13951 p8430 p8447
theorem n20115 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4306 : (e4306 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5100 : (e5100 _v)) (h5195 : (e5195 _v)) (h7749 : (e7749 _v)) (h8045 : (e8045 _v)) (h8317 : (e8317 _v)) : (e2061 _v) := by
  have p17374 := n17374 _v _q 
  have p17138 := n17138 _v _q h4306
  have p20087 := n20087 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  have p5001 := n5001 _v _q h4096
  have p20081 := n20081 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  have p4999 := n4999 _v _q h91
  have p8549 := n8549 _v _q h5195
  have p5010 := n5010 _v _q h70
  have p5003 := n5003 _v _q h4199
  have p5007 := n5007 _v _q h225
  have p4992 := n4992 _v _q h442
  have p17159 := n17159 _v _q h5100
  have p4996 := n4996 _v _q h3937
  have p20103 := n20103 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  have p20108 := n20108 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  have p4987 := n4987 _v _q h4434
  have p16674 := n16674 _v _q h5195
  have p20080 := n20080 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  have p17157 := n17157 _v _q h8045
  have p17076 := n17076 _v _q h3976
  have p20106 := n20106 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  have p17174 := n17174 _v _q h8317
  have p17143 := n17143 _v _q h4567
  have p4983 := n4983 _v _q h4813
  have p4995 := n4995 _v _q h4369
  have p4998 := n4998 _v _q h3152
  have p16269 := n16269 _v _q h7749
  have p5008 := n5008 _v _q h4787
  have p15392 := n15392 _v _q h5195
  have p5006 := n5006 _v _q h4675
  have p17056 := n17056 _v _q h3946
  have p17061 := n17061 _v _q h4747
  have p4985 := n4985 _v _q h4156
  have p17129 := n17129 _v _q h4903
  have p4988 := n4988 _v _q h488
  have p4986 := n4986 _v _q h3105
  have p4984 := n4984 _v _q h4872
  have p4991 := n4991 _v _q h4608
  have p4994 := n4994 _v _q h3069
  change (¬ (e4264 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e2634 _v)) ∨ (e2061 _v) ∨ (e196 _v) ∨ (¬ (e91 _v)) ∨ (¬ (e7493 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e5100 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e4724 _v)) ∨ (¬ (e4398 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e8045 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e3976 _v)) ∨ (¬ (e4491 _v)) ∨ (¬ (e8317 _v)) ∨ (¬ (e4567 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e7749 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e4903 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e3069 _v)) at p17374
  change (¬ (e196 _v)) at p8549
  rcases p17374 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact (False.elim (hlit p20087))
  · exact (False.elim (hlit p5001))
  · exact (False.elim (hlit p20081))
  · exact hlit
  · exact (False.elim (p8549 hlit))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p16674))
  · exact (False.elim (hlit p5010))
  · exact (False.elim (hlit p5003))
  · exact (False.elim (hlit p5007))
  · exact (False.elim (hlit p4992))
  · exact (False.elim (hlit p17159))
  · exact (False.elim (hlit p4996))
  · exact (False.elim (hlit p20103))
  · exact (False.elim (hlit p20108))
  · exact (False.elim (hlit p4987))
  · exact (False.elim (hlit p17157))
  · exact (False.elim (hlit p20080))
  · exact (False.elim (hlit p17138))
  · exact (False.elim (hlit p17076))
  · exact (False.elim (hlit p20106))
  · exact (False.elim (hlit p17174))
  · exact (False.elim (hlit p17143))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p4995))
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p16269))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p15392))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p17056))
  · exact (False.elim (hlit p17061))
  · exact (False.elim (hlit p4985))
  · exact (False.elim (hlit p17129))
  · exact (False.elim (hlit p4988))
  · exact (False.elim (hlit p4986))
  · exact (False.elim (hlit p4984))
  · exact (False.elim (hlit p4991))
  · exact (False.elim (hlit p4994))
theorem n20116 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4306 : (e4306 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5100 : (e5100 _v)) (h5195 : (e5195 _v)) (h7749 : (e7749 _v)) (h8045 : (e8045 _v)) (h8317 : (e8317 _v)) : (e4447 _v) := by
  have p14688 := n14688 _v _q 
  have p20115 := n20115 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h3976 h4096 h4156 h4199 h4306 h4369 h4434 h4567 h4608 h4675 h4747 h4787 h4813 h4872 h4903 h5100 h5195 h7749 h8045 h8317
  change (¬ (e2061 _v)) ∨ (¬ (e4446 _v)) at p14688
  rcases p14688 with hlit | hlit
  · exact (False.elim (hlit p20115))
  · exact hlit
theorem n20117 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3152 : (e3152 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) : (e4575 _v) := by
  have p14696 := n14696 _v _q 
  have p20110 := n20110 _v _q h70 h91 h225 h442 h488 h3069 h3152 h4096 h4156 h4199 h4260 h4369 h4675 h4787 h4813
  change (¬ (e1995 _v)) ∨ (¬ (e4574 _v)) at p14696
  rcases p14696 with hlit | hlit
  · exact (False.elim (hlit p20110))
  · exact hlit
theorem n20118 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3152 : (e3152 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) : (e4567 _v) := by
  have p8485 := n8485 _v _q 
  have p20117 := n20117 _v _q h70 h91 h225 h442 h488 h3069 h3152 h4096 h4156 h4199 h4260 h4369 h4675 h4787 h4813
  change (e4574 _v) ∨ (e4567 _v) at p8485
  change (¬ (e4574 _v)) at p20117
  rcases p8485 with hlit | hlit
  · exact (False.elim (p20117 hlit))
  · exact hlit
theorem n20119 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e4575 _v) := by
  have p14696 := n14696 _v _q 
  have p20111 := n20111 _v _q h6784
  change (¬ (e1995 _v)) ∨ (¬ (e4574 _v)) at p14696
  rcases p14696 with hlit | hlit
  · exact (False.elim (hlit p20111))
  · exact hlit
theorem n20120 (_v : Vars) (_q : Query _v) (h6784 : (e6784 _v)) : (e4567 _v) := by
  have p8485 := n8485 _v _q 
  have p20119 := n20119 _v _q h6784
  change (e4574 _v) ∨ (e4567 _v) at p8485
  change (¬ (e4574 _v)) at p20119
  rcases p8485 with hlit | hlit
  · exact (False.elim (p20119 hlit))
  · exact hlit
theorem n20122 (_v : Vars) (_q : Query _v)  : (e20121 _v) := by
  by_contra hc
  change ¬ ((e2061 _v) ∨ (¬ (e3069 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e7749 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4491 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4903 _v)) ∨ (¬ (e5208 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e5100 _v)) ∨ (¬ (e7814 _v)) ∨ (¬ (e4398 _v)) ∨ (¬ (e8045 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e4567 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e3976 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4724 _v)) ∨ (e2358 _v)) at hc
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h225 : (e225 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))
  have h442 : (e442 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))
  have h488 : (e488 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))
  have h3069 : (e3069 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h3105 : (e3105 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h3946 : (e3946 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))
  have h3976 : (e3976 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))
  have h4059 : (e4059 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))
  have h4156 : (e4156 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))
  have h4199 : (e4199 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))
  have h4369 : (e4369 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))
  have h4398 : (e4398 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))
  have h4434 : (e4434 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4491 : (e4491 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h4567 : (e4567 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))
  have h4608 : (e4608 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))
  have h4675 : (e4675 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h4724 : (e4724 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))))))
  have h4747 : (e4747 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h4872 : (e4872 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))))
  have h4903 : (e4903 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h5100 : (e5100 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))
  have h5208 : (e5208 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h6454 : (e6454 _v) := (fun hn => hc (Or.inl hn))
  have h6571 : (e6571 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn)))))))))))))))))))))))))))))))))))
  have h7749 : (e7749 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h7814 : (e7814 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))
  have h8045 : (e8045 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))
  have p20114 := n20114 _v _q h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h3976 h4059 h4156 h4199 h4306 h4369 h4398 h4434 h4491 h4567 h4608 h4653 h4675 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h5208 h6454 h6571 h7749 h7814 h8045
  exact p20114
theorem n20123 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e51 _v) := by
  have p14962 := n14962 _v _q 
  have p20083 := n20083 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  change (e59 _v) ∨ (e51 _v) at p14962
  change (¬ (e59 _v)) at p20083
  rcases p14962 with hlit | hlit
  · exact (False.elim (p20083 hlit))
  · exact hlit
theorem n20124 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4306 : (e4306 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5100 : (e5100 _v)) (h5195 : (e5195 _v)) (h7749 : (e7749 _v)) (h8045 : (e8045 _v)) (h8317 : (e8317 _v)) : (e4439 _v) := by
  have p14925 := n14925 _v _q 
  have p20116 := n20116 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h3976 h4096 h4156 h4199 h4306 h4369 h4434 h4567 h4608 h4675 h4747 h4787 h4813 h4872 h4903 h5100 h5195 h7749 h8045 h8317
  change (e4446 _v) ∨ (e4439 _v) at p14925
  change (¬ (e4446 _v)) at p20116
  rcases p14925 with hlit | hlit
  · exact (False.elim (p20116 hlit))
  · exact hlit
theorem n20125 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4306 : (e4306 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5100 : (e5100 _v)) (h5195 : (e5195 _v)) (h7749 : (e7749 _v)) (h8045 : (e8045 _v)) (h8317 : (e8317 _v)) : (e7489 _v) := by
  have p296 := n296 _v _q 
  have p17136 := n17136 _v _q 
  have p17547 := n17547 _v _q h7749
  have p20080 := n20080 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  have p4999 := n4999 _v _q h91
  have p5007 := n5007 _v _q h225
  have p16778 := n16778 _v _q 
  have p17141 := n17141 _v _q 
  have p4992 := n4992 _v _q h442
  have p17143 := n17143 _v _q h4567
  have p17050 := n17050 _v _q 
  have p17053 := n17053 _v _q 
  have p15223 := n15223 _v _q h5195
  have p15274 := n15274 _v _q h5195
  have p5008 := n5008 _v _q h4787
  have p17055 := n17055 _v _q 
  have p5006 := n5006 _v _q h4675
  have p17056 := n17056 _v _q h3946
  have p17147 := n17147 _v _q 
  have p17058 := n17058 _v _q 
  have p15392 := n15392 _v _q h5195
  have p17061 := n17061 _v _q h4747
  have p17064 := n17064 _v _q 
  have p4995 := n4995 _v _q h4369
  have p17067 := n17067 _v _q 
  have p17069 := n17069 _v _q 
  have p17138 := n17138 _v _q h4306
  have p17174 := n17174 _v _q h8317
  have p17072 := n17072 _v _q 
  have p17157 := n17157 _v _q h8045
  have p17074 := n17074 _v _q 
  have p17076 := n17076 _v _q h3976
  have p4985 := n4985 _v _q h4156
  have p20123 := n20123 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  have p4988 := n4988 _v _q h488
  have p17078 := n17078 _v _q 
  have p4986 := n4986 _v _q h3105
  have p17080 := n17080 _v _q 
  have p17204 := n17204 _v _q h5195
  have p17083 := n17083 _v _q 
  have p4984 := n4984 _v _q h4872
  have p4991 := n4991 _v _q h4608
  have p17087 := n17087 _v _q 
  have p17091 := n17091 _v _q 
  have p17159 := n17159 _v _q h5100
  have p20103 := n20103 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  have p17093 := n17093 _v _q 
  have p17111 := n17111 _v _q 
  have p20124 := n20124 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h3976 h4096 h4156 h4199 h4306 h4369 h4434 h4567 h4608 h4675 h4747 h4787 h4813 h4872 h4903 h5100 h5195 h7749 h8045 h8317
  have p17115 := n17115 _v _q 
  have p17089 := n17089 _v _q 
  have p17100 := n17100 _v _q 
  have p17098 := n17098 _v _q 
  have p17096 := n17096 _v _q 
  have p17110 := n17110 _v _q 
  have p17102 := n17102 _v _q 
  have p17104 := n17104 _v _q 
  have p17106 := n17106 _v _q 
  have p17108 := n17108 _v _q 
  have p4994 := n4994 _v _q h3069
  have p17120 := n17120 _v _q 
  have p17113 := n17113 _v _q 
  have p17117 := n17117 _v _q 
  have p17124 := n17124 _v _q 
  have p17122 := n17122 _v _q 
  have p20087 := n20087 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  have p16576 := n16576 _v _q 
  have p4998 := n4998 _v _q h3152
  have p20092 := n20092 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  have p5003 := n5003 _v _q h4199
  have p17127 := n17127 _v _q 
  have p4983 := n4983 _v _q h4813
  have p20106 := n20106 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  have p17129 := n17129 _v _q h4903
  have p17131 := n17131 _v _q 
  have p4996 := n4996 _v _q h3937
  have p17133 := n17133 _v _q 
  have p20108 := n20108 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  exact FloorCertificate.node_20125 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2863 _v) (e2877 _v) (e2883 _v) (e2902 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4541 _v) (e4808 _v) p296 p17136 p17547 p20080 p4999 p5007 p16778 p17141 p4992 p17143 p17050 p17053 p15223 p15274 p5008 p17055 p5006 p17056 p17147 p17058 p15392 p17061 p17064 p4995 p17067 p17069 p17138 p17174 p17072 p17157 p17074 p17076 p4985 p20123 p4988 p17078 p4986 p17080 p17204 p17083 p4984 p4991 p17087 p17091 p17159 p20103 p17093 p17111 p20124 p17115 p17089 p17100 p17098 p17096 p17110 p17102 p17104 p17106 p17108 p4994 p17120 p17113 p17117 p17124 p17122 p20087 p16576 p4998 p20092 p5003 p17127 p4983 p20106 p17129 p17131 p4996 p17133 p20108
theorem n20126 (_v : Vars) (_q : Query _v)  : (e3976 _v) := by
  have p14935 := n14935 _v _q 
  have p20070 := n20070 _v _q 
  change (e3983 _v) ∨ (e3976 _v) at p14935
  change (¬ (e3983 _v)) at p20070
  rcases p14935 with hlit | hlit
  · exact (False.elim (p20070 hlit))
  · exact hlit
theorem n20127 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2061 : (e2061 _v)) (h3069 : (e3069 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4220 : (e4220 _v)) (h4260 : (e4260 _v)) (h4285 : (e4285 _v)) (h4301 : (e4301 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4419 : (e4419 _v)) (h4546 : (e4546 _v)) (h4608 : (e4608 _v)) (h4648 : (e4648 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4899 : (e4899 _v)) (h4924 : (e4924 _v)) (h6579 : (e6579 _v)) : (e7489 _v) := by
  have p10896 := n10896 _v _q 
  have p10893 := n10893 _v _q 
  have p17230 := n17230 _v _q h6579
  have p331 := n331 _v _q 
  have p20110 := n20110 _v _q h70 h91 h225 h442 h488 h3069 h3152 h4096 h4156 h4199 h4260 h4369 h4675 h4787 h4813
  have p11409 := n11409 _v _q h2061
  have p17050 := n17050 _v _q 
  have p4968 := n4968 _v _q h4924
  have p4990 := n4990 _v _q h4648
  have p20118 := n20118 _v _q h70 h91 h225 h442 h488 h3069 h3152 h4096 h4156 h4199 h4260 h4369 h4675 h4787 h4813
  have p16994 := n16994 _v _q 
  have p4972 := n4972 _v _q h4899
  have p5006 := n5006 _v _q h4675
  have p4979 := n4979 _v _q h4139
  have p4976 := n4976 _v _q h4546
  have p20126 := n20126 _v _q 
  have p13951 := n13951 _v _q 
  have p17009 := n17009 _v _q 
  have p4998 := n4998 _v _q h3152
  have p253 := n253 _v _q h191
  have p5010 := n5010 _v _q h70
  have p16911 := n16911 _v _q 
  have p4996 := n4996 _v _q h3937
  have p4991 := n4991 _v _q h4608
  have p4995 := n4995 _v _q h4369
  have p5003 := n5003 _v _q h4199
  have p5001 := n5001 _v _q h4096
  have p16576 := n16576 _v _q 
  have p4999 := n4999 _v _q h91
  have p4989 := n4989 _v _q h4838
  have p4994 := n4994 _v _q h3069
  have p5000 := n5000 _v _q h30
  have p4977 := n4977 _v _q h4285
  have p17134 := n17134 _v _q h4398
  have p17058 := n17058 _v _q 
  have p17064 := n17064 _v _q 
  have p17067 := n17067 _v _q 
  have p17069 := n17069 _v _q 
  have p17072 := n17072 _v _q 
  have p4992 := n4992 _v _q h442
  have p5007 := n5007 _v _q h225
  have p17078 := n17078 _v _q 
  have p17080 := n17080 _v _q 
  have p17083 := n17083 _v _q 
  have p17074 := n17074 _v _q 
  have p17087 := n17087 _v _q 
  have p17758 := n17758 _v _q 
  have p17091 := n17091 _v _q 
  have p17093 := n17093 _v _q 
  have p4980 := n4980 _v _q h4301
  have p17221 := n17221 _v _q 
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p17100 := n17100 _v _q 
  have p17102 := n17102 _v _q 
  have p19610 := n19610 _v _q 
  have p17104 := n17104 _v _q 
  have p17096 := n17096 _v _q 
  have p4983 := n4983 _v _q h4813
  have p5008 := n5008 _v _q h4787
  have p17113 := n17113 _v _q 
  have p17094 := n17094 _v _q h4724
  have p17122 := n17122 _v _q 
  have p17117 := n17117 _v _q 
  have p17124 := n17124 _v _q 
  have p17115 := n17115 _v _q 
  have p17120 := n17120 _v _q 
  have p4985 := n4985 _v _q h4156
  have p17127 := n17127 _v _q 
  have p16778 := n16778 _v _q 
  have p17874 := n17874 _v _q 
  have p17131 := n17131 _v _q 
  have p17110 := n17110 _v _q 
  have p17133 := n17133 _v _q 
  have p4981 := n4981 _v _q h4260
  have p4971 := n4971 _v _q h4419
  have p17111 := n17111 _v _q 
  have p17294 := n17294 _v _q 
  have p17136 := n17136 _v _q 
  have p17141 := n17141 _v _q 
  have p16913 := n16913 _v _q 
  have p5004 := n5004 _v _q h4220
  have p17147 := n17147 _v _q 
  have p20096 := n20096 _v _q 
  have p17053 := n17053 _v _q 
  have p15217 := n15217 _v _q h2061
  have p17055 := n17055 _v _q 
  have p17108 := n17108 _v _q 
  have p4988 := n4988 _v _q h488
  have p17089 := n17089 _v _q 
  have p19665 := n19665 _v _q 
  exact FloorCertificate.node_20127 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e61 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2863 _v) (e2877 _v) (e2879 _v) (e2883 _v) (e2898 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2913 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p10896 p10893 p17230 p331 p20110 p11409 p17050 p4968 p4990 p20118 p16994 p4972 p5006 p4979 p4976 p20126 p13951 p17009 p4998 p253 p5010 p16911 p4996 p4991 p4995 p5003 p5001 p16576 p4999 p4989 p4994 p5000 p4977 p17134 p17058 p17064 p17067 p17069 p17072 p4992 p5007 p17078 p17080 p17083 p17074 p17087 p17758 p17091 p17093 p4980 p17221 p17098 p17106 p17100 p17102 p19610 p17104 p17096 p4983 p5008 p17113 p17094 p17122 p17117 p17124 p17115 p17120 p4985 p17127 p16778 p17874 p17131 p17110 p17133 p4981 p4971 p17111 p17294 p17136 p17141 p16913 p5004 p17147 p20096 p17053 p15217 p17055 p17108 p4988 p17089 p19665
end
end Assembly
