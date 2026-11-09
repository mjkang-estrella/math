import Dag225
import generated.th_lemma_29
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n20179 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4306 : (e4306 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4434 : (e4434 _v)) (h4491 : (e4491 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5100 : (e5100 _v)) (h5195 : (e5195 _v)) (h5208 : (e5208 _v)) (h6571 : (e6571 _v)) (h7807 : (e7807 _v)) (h8045 : (e8045 _v)) : (e2733 _v) := by
  have p14525 := n14525 _v _q 
  have p20178 := n20178 _v _q h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h3976 h4059 h4156 h4199 h4306 h4369 h4398 h4434 h4491 h4567 h4608 h4653 h4675 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h5195 h5208 h6571 h7807 h8045
  simp only [e2733, e4096, e4097, e4098, e4099, e7589, e7597, e7600] at *
  tauto
theorem n20180 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4306 : (e4306 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4434 : (e4434 _v)) (h4491 : (e4491 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5100 : (e5100 _v)) (h5195 : (e5195 _v)) (h5208 : (e5208 _v)) (h6571 : (e6571 _v)) (h7807 : (e7807 _v)) (h8045 : (e8045 _v)) : (e7489 _v) := by
  have p14689 := n14689 _v _q 
  have p20179 := n20179 _v _q h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h3976 h4059 h4156 h4199 h4306 h4369 h4398 h4434 h4491 h4567 h4608 h4653 h4675 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h5195 h5208 h6571 h7807 h8045
  have p20172 := n20172 _v _q h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h3976 h4059 h4156 h4199 h4306 h4369 h4398 h4434 h4491 h4567 h4608 h4653 h4675 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h5195 h5208 h6571 h7807 h8045
  simp only [e2733, e4101, e4102, e4106, e4107, e4108, e4109, e6750, e7603] at *
  tauto
theorem n20181 (_v : Vars) (_q : Query _v) (h2061 : (e2061 _v)) (h6501 : (e6501 _v)) (h6784 : (e6784 _v)) : (e3169 _v) := by
  have p14769 := n14769 _v _q 
  have p20177 := n20177 _v _q h2061 h6501 h6784
  simp only [e3167, e3168, e3169, e3170, e6888, e6889, e6896] at *
  tauto
theorem n20183 (_v : Vars) (_q : Query _v)  : (e20182 _v) := by
  by_contra hc
  change ¬ ((e196 _v) ∨ (¬ (e3069 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4491 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4903 _v)) ∨ (¬ (e5208 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e5100 _v)) ∨ (¬ (e4398 _v)) ∨ (¬ (e8045 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e4567 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e3976 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4724 _v)) ∨ (e2303 _v) ∨ (e2358 _v)) at hc
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h225 : (e225 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))
  have h442 : (e442 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))
  have h488 : (e488 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))
  have h3069 : (e3069 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h3105 : (e3105 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h3946 : (e3946 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))
  have h3976 : (e3976 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))
  have h4059 : (e4059 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))
  have h4156 : (e4156 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))
  have h4199 : (e4199 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))
  have h4369 : (e4369 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))
  have h4398 : (e4398 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))
  have h4434 : (e4434 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4491 : (e4491 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h4567 : (e4567 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))
  have h4608 : (e4608 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))
  have h4675 : (e4675 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h4724 : (e4724 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))))
  have h4747 : (e4747 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h4872 : (e4872 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))
  have h4903 : (e4903 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h5100 : (e5100 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h5195 : (e5195 _v) := (fun hn => hc (Or.inl hn))
  have h5208 : (e5208 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h6571 : (e6571 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))))))))))))))))))))))))))))))
  have h7807 : (e7807 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))))
  have h8045 : (e8045 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))
  have p20180 := n20180 _v _q h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h3976 h4059 h4156 h4199 h4306 h4369 h4398 h4434 h4491 h4567 h4608 h4653 h4675 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h5195 h5208 h6571 h7807 h8045
  exact p20180
theorem n20184 (_v : Vars) (_q : Query _v) (h2061 : (e2061 _v)) (h6501 : (e6501 _v)) (h6784 : (e6784 _v)) : (e8398 _v) := by
  have p15563 := n15563 _v _q 
  have p20173 := n20173 _v _q h2061 h6501 h6784
  simp only [e2132, e7742, e8398, e15562] at *
  tauto
theorem n20185 (_v : Vars) (_q : Query _v) (h2061 : (e2061 _v)) (h6501 : (e6501 _v)) (h6784 : (e6784 _v)) : (e7489 _v) := by
  have p20173 := n20173 _v _q h2061 h6501 h6784
  have p20175 := n20175 _v _q h2061 h6501 h6784
  have p20184 := n20184 _v _q h2061 h6501 h6784
  have p17089 := n17089 _v _q 
  have p10893 := n10893 _v _q 
  have p10896 := n10896 _v _q 
  have p19665 := n19665 _v _q 
  have p20111 := n20111 _v _q h6784
  have p11409 := n11409 _v _q h2061
  have p11473 := n11473 _v _q h6784
  have p16513 := n16513 _v _q h6784
  have p20120 := n20120 _v _q h6784
  have p16994 := n16994 _v _q 
  have p15560 := n15560 _v _q h6784
  have p16598 := n16598 _v _q h6784
  have p16549 := n16549 _v _q h6784
  have p16852 := n16852 _v _q h2061 h6784
  have p20126 := n20126 _v _q 
  have p13951 := n13951 _v _q 
  have p17009 := n17009 _v _q 
  have p19771 := n19771 _v _q h6784
  have p16607 := n16607 _v _q h6784
  have p16619 := n16619 _v _q h6784
  have p16911 := n16911 _v _q 
  have p16325 := n16325 _v _q h6501
  have p15641 := n15641 _v _q h6501
  have p16620 := n16620 _v _q h6784
  have p16856 := n16856 _v _q h6784
  have p15705 := n15705 _v _q h6784
  have p16576 := n16576 _v _q 
  have p19747 := n19747 _v _q h6784
  have p19750 := n19750 _v _q h6784
  have p15702 := n15702 _v _q h6784
  have p16857 := n16857 _v _q h2061 h6784
  have p19752 := n19752 _v _q h6784
  have p20169 := n20169 _v _q h6784
  have p17058 := n17058 _v _q 
  have p17064 := n17064 _v _q 
  have p17067 := n17067 _v _q 
  have p17069 := n17069 _v _q 
  have p17072 := n17072 _v _q 
  have p16854 := n16854 _v _q h6784
  have p19772 := n19772 _v _q h6784
  have p17078 := n17078 _v _q 
  have p17080 := n17080 _v _q 
  have p17083 := n17083 _v _q 
  have p17074 := n17074 _v _q 
  have p17087 := n17087 _v _q 
  have p17758 := n17758 _v _q 
  have p17091 := n17091 _v _q 
  have p17093 := n17093 _v _q 
  have p15713 := n15713 _v _q h6784
  have p17221 := n17221 _v _q 
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p17100 := n17100 _v _q 
  have p17102 := n17102 _v _q 
  have p19610 := n19610 _v _q 
  have p17104 := n17104 _v _q 
  have p17096 := n17096 _v _q 
  have p16625 := n16625 _v _q h6784
  have p16626 := n16626 _v _q h6784
  have p17113 := n17113 _v _q 
  have p19758 := n19758 _v _q h6784
  have p17122 := n17122 _v _q 
  have p17117 := n17117 _v _q 
  have p17124 := n17124 _v _q 
  have p17115 := n17115 _v _q 
  have p17120 := n17120 _v _q 
  have p19760 := n19760 _v _q h6784
  have p17127 := n17127 _v _q 
  have p16778 := n16778 _v _q 
  have p17874 := n17874 _v _q 
  have p17131 := n17131 _v _q 
  have p17110 := n17110 _v _q 
  have p17133 := n17133 _v _q 
  have p16603 := n16603 _v _q h6784
  have p16816 := n16816 _v _q h6784
  have p17111 := n17111 _v _q 
  have p17294 := n17294 _v _q 
  have p17136 := n17136 _v _q 
  have p17141 := n17141 _v _q 
  have p16913 := n16913 _v _q 
  have p17147 := n17147 _v _q 
  have p20096 := n20096 _v _q 
  have p17053 := n17053 _v _q 
  have p15217 := n15217 _v _q h2061
  have p17055 := n17055 _v _q 
  have p17108 := n17108 _v _q 
  have p19762 := n19762 _v _q h6784
  have p16175 := n16175 _v _q 
  have p20181 := n20181 _v _q h2061 h6501 h6784
  exact FloorCertificate.node_20185 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e61 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2863 _v) (e2877 _v) (e2879 _v) (e2883 _v) (e2898 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2913 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e3164 _v) (e4215 _v) (e4541 _v) (e4808 _v) p20173 p20175 p20184 p17089 p10893 p10896 p19665 p20111 p11409 p11473 p16513 p20120 p16994 p15560 p16598 p16549 p16852 p20126 p13951 p17009 p19771 p16607 p16619 p16911 p16325 p15641 p16620 p16856 p15705 p16576 p19747 p19750 p15702 p16857 p19752 p20169 p17058 p17064 p17067 p17069 p17072 p16854 p19772 p17078 p17080 p17083 p17074 p17087 p17758 p17091 p17093 p15713 p17221 p17098 p17106 p17100 p17102 p19610 p17104 p17096 p16625 p16626 p17113 p19758 p17122 p17117 p17124 p17115 p17120 p19760 p17127 p16778 p17874 p17131 p17110 p17133 p16603 p16816 p17111 p17294 p17136 p17141 p16913 p17147 p20096 p17053 p15217 p17055 p17108 p19762 p16175 p20181
theorem n20186 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4306 : (e4306 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4434 : (e4434 _v)) (h4491 : (e4491 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5100 : (e5100 _v)) (h5208 : (e5208 _v)) (h6571 : (e6571 _v)) (h7807 : (e7807 _v)) (h8045 : (e8045 _v)) : (e196 _v) := by
  have p20183 := n20183 _v _q 
  have p17143 := n17143 _v _q h4567
  have p4987 := n4987 _v _q h4434
  have p4991 := n4991 _v _q h4608
  have p4999 := n4999 _v _q h91
  have p4996 := n4996 _v _q h3937
  have p5003 := n5003 _v _q h4199
  have p4998 := n4998 _v _q h3152
  have p17128 := n17128 _v _q h4491
  have p4983 := n4983 _v _q h4813
  have p5008 := n5008 _v _q h4787
  have p17129 := n17129 _v _q h4903
  have p17175 := n17175 _v _q h5208
  have p5006 := n5006 _v _q h4675
  have p17159 := n17159 _v _q h5100
  have p17134 := n17134 _v _q h4398
  have p17157 := n17157 _v _q h8045
  have p17137 := n17137 _v _q h4059
  have p17138 := n17138 _v _q h4306
  have p5007 := n5007 _v _q h225
  have p4992 := n4992 _v _q h442
  have p4994 := n4994 _v _q h3069
  have p17056 := n17056 _v _q h3946
  have p17060 := n17060 _v _q h4653
  have p17061 := n17061 _v _q h4747
  have p4995 := n4995 _v _q h4369
  have p17076 := n17076 _v _q h3976
  have p4985 := n4985 _v _q h4156
  have p4988 := n4988 _v _q h488
  have p4986 := n4986 _v _q h3105
  have p4984 := n4984 _v _q h4872
  have p17094 := n17094 _v _q h4724
  have p11350 := n11350 _v _q h7807
  have p8447 := n8447 _v _q h6571
  simp only [e91, e95, e196, e225, e230, e442, e443, e488, e493, e2303, e2358, e3069, e3074, e3105, e3106, e3152, e3156, e3937, e3942, e3946, e3947, e3976, e3981, e4059, e4064, e4156, e4157, e4199, e4200, e4306, e4311, e4369, e4370, e4398, e4403, e4434, e4435, e4491, e4496, e4567, e4572, e4608, e4609, e4653, e4658, e4675, e4676, e4724, e4729, e4747, e4752, e4787, e4788, e4813, e4814, e4872, e4873, e4903, e4908, e5100, e5103, e5208, e5218, e6571, e7807, e8045, e8048, e20182] at *
  tauto
theorem n20188 (_v : Vars) (_q : Query _v)  : (e20187 _v) := by
  by_contra hc
  change ¬ ((e2179 _v) ∨ (¬ (e2061 _v)) ∨ (e2793 _v)) at hc
  have h2061 : (e2061 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h6501 : (e6501 _v) := (fun hn => hc (Or.inl hn))
  have h6784 : (e6784 _v) := (fun hn => hc (Or.inr (Or.inr hn)))
  have p20185 := n20185 _v _q h2061 h6501 h6784
  exact p20185
theorem n20189 (_v : Vars) (_q : Query _v) (h2061 : (e2061 _v)) (h6784 : (e6784 _v)) : (e2179 _v) := by
  have p20188 := n20188 _v _q 
  have p11409 := n11409 _v _q h2061
  have p11473 := n11473 _v _q h6784
  simp only [e2061, e2179, e2793, e6454, e6784, e20187] at *
  tauto
theorem n20190 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2781 : (e2781 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4306 : (e4306 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4434 : (e4434 _v)) (h4491 : (e4491 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5100 : (e5100 _v)) (h5208 : (e5208 _v)) (h6571 : (e6571 _v)) (h7807 : (e7807 _v)) (h8038 : (e8038 _v)) (h8045 : (e8045 _v)) : (e4839 _v) := by
  have p17871 := n17871 _v _q 
  have p8421 := n8421 _v _q h2781
  have p4983 := n4983 _v _q h4813
  have p8602 := n8602 _v _q h8038
  have p5003 := n5003 _v _q h4199
  have p17129 := n17129 _v _q h4903
  have p5008 := n5008 _v _q h4787
  have p17786 := n17786 _v _q h7807
  have p4996 := n4996 _v _q h3937
  have p17157 := n17157 _v _q h8045
  have p4999 := n4999 _v _q h91
  have p5007 := n5007 _v _q h225
  have p4992 := n4992 _v _q h442
  have p17056 := n17056 _v _q h3946
  have p17061 := n17061 _v _q h4747
  have p4995 := n4995 _v _q h4369
  have p17076 := n17076 _v _q h3976
  have p4985 := n4985 _v _q h4156
  have p4988 := n4988 _v _q h488
  have p4986 := n4986 _v _q h3105
  have p4984 := n4984 _v _q h4872
  have p4994 := n4994 _v _q h3069
  have p4998 := n4998 _v _q h3152
  have p5006 := n5006 _v _q h4675
  have p17159 := n17159 _v _q h5100
  have p20186 := n20186 _v _q h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h3976 h4059 h4156 h4199 h4306 h4369 h4398 h4434 h4491 h4567 h4608 h4653 h4675 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h5208 h6571 h7807 h8045
  have p4987 := n4987 _v _q h4434
  have p4991 := n4991 _v _q h4608
  simp only [e91, e95, e196, e225, e230, e442, e443, e488, e493, e2475, e2781, e3069, e3074, e3105, e3106, e3152, e3156, e3937, e3942, e3946, e3947, e3976, e3981, e4156, e4157, e4199, e4200, e4369, e4370, e4434, e4435, e4608, e4609, e4675, e4676, e4747, e4752, e4787, e4788, e4813, e4814, e4838, e4839, e4872, e4873, e4903, e4908, e5100, e5103, e5195, e6776, e7749, e7752, e8038, e8045, e8048, e17870] at *
  tauto
theorem n20191 (_v : Vars) (_q : Query _v) (h51 : (e51 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2781 : (e2781 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4306 : (e4306 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4434 : (e4434 _v)) (h4491 : (e4491 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5100 : (e5100 _v)) (h5208 : (e5208 _v)) (h6571 : (e6571 _v)) (h7807 : (e7807 _v)) (h8038 : (e8038 _v)) (h8045 : (e8045 _v)) : (e7489 _v) := by
  have p16285 := n16285 _v _q 
  have p17839 := n17839 _v _q h51 h91 h225 h442 h488 h2781 h3069 h3105 h3152 h3937 h3946 h3976 h4059 h4156 h4199 h4306 h4369 h4398 h4434 h4491 h4567 h4608 h4653 h4675 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h5208 h6571 h7807 h8045
  have p20190 := n20190 _v _q h91 h225 h442 h488 h2781 h3069 h3105 h3152 h3937 h3946 h3976 h4059 h4156 h4199 h4306 h4369 h4398 h4434 h4491 h4567 h4608 h4653 h4675 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h5208 h6571 h7807 h8038 h8045
  simp only [e4836, e4837, e4838, e4839, e8301, e8302, e8307] at *
  tauto
theorem n20192 (_v : Vars) (_q : Query _v) (h2061 : (e2061 _v)) (h6784 : (e6784 _v)) : (e4616 _v) := by
  have p14684 := n14684 _v _q 
  have p20189 := n20189 _v _q h2061 h6784
  simp only [e2179, e3158, e3159, e3160, e3161, e3162, e4616, e6501, e8109] at *
  tauto
theorem n20193 (_v : Vars) (_q : Query _v) (h2061 : (e2061 _v)) (h6784 : (e6784 _v)) : (e3158 _v) := by
  have p15126 := n15126 _v _q 
  have p20192 := n20192 _v _q h2061 h6784
  simp only [e3158, e3159, e3160, e3161, e3162, e3163, e4616] at *
  tauto
theorem n20195 (_v : Vars) (_q : Query _v)  : (e20194 _v) := by
  by_contra hc
  change ¬ ((¬ (e2781 _v)) ∨ (¬ (e4813 _v)) ∨ (e2475 _v) ∨ (¬ (e4199 _v)) ∨ (¬ (e4903 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e8045 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e3976 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e5100 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e4491 _v)) ∨ (¬ (e4398 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e5208 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4724 _v)) ∨ (e2303 _v) ∨ (¬ (e4567 _v)) ∨ (e2358 _v) ∨ (¬ (e51 _v))) at hc
  have h51 : (e51 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))))))))))))))))))))))))))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h225 : (e225 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h442 : (e442 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h488 : (e488 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))
  have h2781 : (e2781 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h3069 : (e3069 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))
  have h3105 : (e3105 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h3946 : (e3946 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h3976 : (e3976 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h4059 : (e4059 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))
  have h4156 : (e4156 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))
  have h4199 : (e4199 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))
  have h4369 : (e4369 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h4398 : (e4398 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))
  have h4434 : (e4434 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))
  have h4491 : (e4491 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))
  have h4567 : (e4567 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))))))
  have h4608 : (e4608 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))
  have h4675 : (e4675 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))
  have h4724 : (e4724 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))))
  have h4747 : (e4747 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h4872 : (e4872 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))
  have h4903 : (e4903 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h5100 : (e5100 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))
  have h5208 : (e5208 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))
  have h6571 : (e6571 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))))))
  have h7807 : (e7807 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))))
  have h8038 : (e8038 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h8045 : (e8045 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have p20191 := n20191 _v _q h51 h91 h225 h442 h488 h2781 h3069 h3105 h3152 h3937 h3946 h3976 h4059 h4156 h4199 h4306 h4369 h4398 h4434 h4491 h4567 h4608 h4653 h4675 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h5208 h6571 h7807 h8038 h8045
  exact p20191
theorem n20196 (_v : Vars) (_q : Query _v) (h2061 : (e2061 _v)) (h6784 : (e6784 _v)) : (e2592 _v) := by
  have p11473 := n11473 _v _q h6784
  have p16858 := n16858 _v _q 
  have p20193 := n20193 _v _q h2061 h6784
  have p16578 := n16578 _v _q 
  exact FloorCertificate.node_20196 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) (e2863 _v) (e2935 _v) p11473 p16858 p20193 p16578
theorem n20197 (_v : Vars) (_q : Query _v) (h2061 : (e2061 _v)) (h6784 : (e6784 _v)) : (e2132 _v) := by
  have p16858 := n16858 _v _q 
  have p20193 := n20193 _v _q h2061 h6784
  have p16578 := n16578 _v _q 
  have p11473 := n11473 _v _q h6784
  have p10893 := n10893 _v _q 
  exact FloorCertificate.node_20197 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) (e2863 _v) (e2935 _v) p16858 p20193 p16578 p11473 p10893
theorem n20198 (_v : Vars) (_q : Query _v) (h2061 : (e2061 _v)) (h6784 : (e6784 _v)) : (e7739 _v) := by
  have p14833 := n14833 _v _q 
  have p20197 := n20197 _v _q h2061 h6784
  simp only [e2132, e4218, e4219, e4220, e4221, e7733, e7739, e7742, e7744] at *
  tauto
theorem n20199 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2733 : (e2733 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4306 : (e4306 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4434 : (e4434 _v)) (h4491 : (e4491 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5100 : (e5100 _v)) (h5208 : (e5208 _v)) (h6571 : (e6571 _v)) (h7807 : (e7807 _v)) (h8038 : (e8038 _v)) (h8045 : (e8045 _v)) : (e6776 _v) := by
  have p20195 := n20195 _v _q 
  have p16017 := n16017 _v _q h2733
  have p8602 := n8602 _v _q h8038
  have p5003 := n5003 _v _q h4199
  have p17129 := n17129 _v _q h4903
  have p5008 := n5008 _v _q h4787
  have p4996 := n4996 _v _q h3937
  have p17157 := n17157 _v _q h8045
  have p4999 := n4999 _v _q h91
  have p5007 := n5007 _v _q h225
  have p4992 := n4992 _v _q h442
  have p17056 := n17056 _v _q h3946
  have p17061 := n17061 _v _q h4747
  have p4995 := n4995 _v _q h4369
  have p17076 := n17076 _v _q h3976
  have p4985 := n4985 _v _q h4156
  have p4988 := n4988 _v _q h488
  have p4986 := n4986 _v _q h3105
  have p4984 := n4984 _v _q h4872
  have p4994 := n4994 _v _q h3069
  have p4998 := n4998 _v _q h3152
  have p5006 := n5006 _v _q h4675
  have p17159 := n17159 _v _q h5100
  have p4987 := n4987 _v _q h4434
  have p4991 := n4991 _v _q h4608
  have p17128 := n17128 _v _q h4491
  have p17134 := n17134 _v _q h4398
  have p17137 := n17137 _v _q h4059
  have p17138 := n17138 _v _q h4306
  have p17175 := n17175 _v _q h5208
  have p17060 := n17060 _v _q h4653
  have p17094 := n17094 _v _q h4724
  have p11350 := n11350 _v _q h7807
  have p17143 := n17143 _v _q h4567
  have p8447 := n8447 _v _q h6571
  have p4983 := n4983 _v _q h4813
  simp only [e51, e57, e91, e95, e225, e230, e442, e443, e488, e493, e2303, e2358, e2475, e2781, e3069, e3074, e3105, e3106, e3152, e3156, e3937, e3942, e3946, e3947, e3976, e3981, e4059, e4064, e4156, e4157, e4199, e4200, e4306, e4311, e4369, e4370, e4398, e4403, e4434, e4435, e4491, e4496, e4567, e4572, e4608, e4609, e4653, e4658, e4675, e4676, e4724, e4729, e4747, e4752, e4787, e4788, e4813, e4814, e4872, e4873, e4903, e4908, e5100, e5103, e5208, e5218, e6571, e6776, e7807, e8038, e8045, e8048, e20194] at *
  tauto
theorem n20200 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2733 : (e2733 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4306 : (e4306 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4434 : (e4434 _v)) (h4491 : (e4491 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5100 : (e5100 _v)) (h5208 : (e5208 _v)) (h6571 : (e6571 _v)) (h7807 : (e7807 _v)) (h8038 : (e8038 _v)) (h8045 : (e8045 _v)) : (e7789 _v) := by
  have p14570 := n14570 _v _q 
  have p20199 := n20199 _v _q h91 h225 h442 h488 h2733 h3069 h3105 h3152 h3937 h3946 h3976 h4059 h4156 h4199 h4306 h4369 h4398 h4434 h4491 h4567 h4608 h4653 h4675 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h5208 h6571 h7807 h8038 h8045
  simp only [e2781, e4258, e4259, e4260, e4261, e6776, e7781, e7789, e7792] at *
  tauto
theorem n20201 (_v : Vars) (_q : Query _v) (h2061 : (e2061 _v)) (h6784 : (e6784 _v)) : (e8330 _v) := by
  have p14907 := n14907 _v _q 
  have p20196 := n20196 _v _q h2061 h6784
  simp only [e2592, e4855, e4856, e4857, e4858, e6672, e8324, e8330, e8333] at *
  tauto
theorem n20202 (_v : Vars) (_q : Query _v) (h2061 : (e2061 _v)) (h6784 : (e6784 _v)) : (e4855 _v) := by
  have p16317 := n16317 _v _q 
  have p20201 := n20201 _v _q h2061 h6784
  simp only [e4855, e4856, e4857, e4858, e8324, e8325, e8330] at *
  tauto
theorem n20203 (_v : Vars) (_q : Query _v) (h2061 : (e2061 _v)) (h6784 : (e6784 _v)) : (e13 _v) := by
  have p11443 := n11443 _v _q 
  have p20196 := n20196 _v _q h2061 h6784
  simp only [e13, e2592, e6672, e11442] at *
  tauto
theorem n20204 (_v : Vars) (_q : Query _v) (h2061 : (e2061 _v)) (h6784 : (e6784 _v)) : (e2475 _v) := by
  have p11399 := n11399 _v _q 
  have p20203 := n20203 _v _q h2061 h6784
  simp only [e13, e2475, e5093, e11398] at *
  tauto
theorem n20205 (_v : Vars) (_q : Query _v) (h2061 : (e2061 _v)) (h6784 : (e6784 _v)) : (e8035 _v) := by
  have p14871 := n14871 _v _q 
  have p20204 := n20204 _v _q h2061 h6784
  simp only [e2475, e4544, e4545, e4546, e4547, e8029, e8035, e8038, e8040] at *
  tauto
theorem n20206 (_v : Vars) (_q : Query _v) (h2061 : (e2061 _v)) (h6784 : (e6784 _v)) : (e4546 _v) := by
  have p16307 := n16307 _v _q 
  have p20205 := n20205 _v _q h2061 h6784
  simp only [e4544, e4545, e4546, e4547, e8029, e8030, e8035] at *
  tauto
theorem n20207 (_v : Vars) (_q : Query _v) (h2061 : (e2061 _v)) (h6784 : (e6784 _v)) : (e5090 _v) := by
  have p14728 := n14728 _v _q 
  have p20203 := n20203 _v _q h2061 h6784
  simp only [e13, e28, e30, e34, e35, e5089, e5090, e5093, e5095] at *
  tauto
theorem n20208 (_v : Vars) (_q : Query _v) (h2061 : (e2061 _v)) (h6784 : (e6784 _v)) : (e30 _v) := by
  have p16290 := n16290 _v _q 
  have p20207 := n20207 _v _q h2061 h6784
  simp only [e28, e30, e34, e35, e5089, e5090, e5107] at *
  tauto
theorem n20209 (_v : Vars) (_q : Query _v) (h2061 : (e2061 _v)) (h6784 : (e6784 _v)) : (e4220 _v) := by
  have p16334 := n16334 _v _q 
  have p20198 := n20198 _v _q h2061 h6784
  simp only [e4218, e4219, e4220, e4221, e7733, e7734, e7739] at *
  tauto
theorem n20210 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2733 : (e2733 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4306 : (e4306 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4434 : (e4434 _v)) (h4491 : (e4491 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5100 : (e5100 _v)) (h5208 : (e5208 _v)) (h6571 : (e6571 _v)) (h7807 : (e7807 _v)) (h8038 : (e8038 _v)) (h8045 : (e8045 _v)) : (e4260 _v) := by
  have p15824 := n15824 _v _q 
  have p20200 := n20200 _v _q h91 h225 h442 h488 h2733 h3069 h3105 h3152 h3937 h3946 h3976 h4059 h4156 h4199 h4306 h4369 h4398 h4434 h4491 h4567 h4608 h4653 h4675 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h5208 h6571 h7807 h8038 h8045
  simp only [e4258, e4259, e4260, e4261, e7781, e7782, e7789] at *
  tauto
theorem n20211 (_v : Vars) (_q : Query _v) (h2061 : (e2061 _v)) (h3919 : (e3919 _v)) (h6780 : (e6780 _v)) (h6784 : (e6784 _v)) : (e7489 _v) := by
  have p17079 := n17079 _v _q h3919
  have p16578 := n16578 _v _q 
  have p19762 := n19762 _v _q h6784
  have p17050 := n17050 _v _q 
  have p11473 := n11473 _v _q h6784
  have p16858 := n16858 _v _q 
  have p20193 := n20193 _v _q h2061 h6784
  have p15720 := n15720 _v _q h6780
  have p17089 := n17089 _v _q 
  have p19665 := n19665 _v _q 
  have p20111 := n20111 _v _q h6784
  have p11409 := n11409 _v _q h2061
  have p16513 := n16513 _v _q h6784
  have p20120 := n20120 _v _q h6784
  have p17108 := n17108 _v _q 
  have p15560 := n15560 _v _q h6784
  have p16598 := n16598 _v _q h6784
  have p16549 := n16549 _v _q h6784
  have p20206 := n20206 _v _q h2061 h6784
  have p20126 := n20126 _v _q 
  have p13951 := n13951 _v _q 
  have p17009 := n17009 _v _q 
  have p19771 := n19771 _v _q h6784
  have p16607 := n16607 _v _q h6784
  have p16619 := n16619 _v _q h6784
  have p16911 := n16911 _v _q 
  have p16620 := n16620 _v _q h6784
  have p16856 := n16856 _v _q h6784
  have p15705 := n15705 _v _q h6784
  have p19747 := n19747 _v _q h6784
  have p19750 := n19750 _v _q h6784
  have p15702 := n15702 _v _q h6784
  have p20208 := n20208 _v _q h2061 h6784
  have p19752 := n19752 _v _q h6784
  have p20169 := n20169 _v _q h6784
  have p17058 := n17058 _v _q 
  have p17064 := n17064 _v _q 
  have p17067 := n17067 _v _q 
  have p17069 := n17069 _v _q 
  have p17072 := n17072 _v _q 
  have p16854 := n16854 _v _q h6784
  have p19772 := n19772 _v _q h6784
  have p17078 := n17078 _v _q 
  have p17080 := n17080 _v _q 
  have p17083 := n17083 _v _q 
  have p17074 := n17074 _v _q 
  have p17087 := n17087 _v _q 
  have p17758 := n17758 _v _q 
  have p17091 := n17091 _v _q 
  have p17093 := n17093 _v _q 
  have p15713 := n15713 _v _q h6784
  have p17221 := n17221 _v _q 
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p17100 := n17100 _v _q 
  have p17102 := n17102 _v _q 
  have p19610 := n19610 _v _q 
  have p17104 := n17104 _v _q 
  have p17096 := n17096 _v _q 
  have p16625 := n16625 _v _q h6784
  have p16626 := n16626 _v _q h6784
  have p17113 := n17113 _v _q 
  have p19758 := n19758 _v _q h6784
  have p17122 := n17122 _v _q 
  have p17117 := n17117 _v _q 
  have p17124 := n17124 _v _q 
  have p17115 := n17115 _v _q 
  have p17120 := n17120 _v _q 
  have p19760 := n19760 _v _q h6784
  have p17127 := n17127 _v _q 
  have p16778 := n16778 _v _q 
  have p17874 := n17874 _v _q 
  have p17131 := n17131 _v _q 
  have p17110 := n17110 _v _q 
  have p17133 := n17133 _v _q 
  have p16603 := n16603 _v _q h6784
  have p16816 := n16816 _v _q h6784
  have p17111 := n17111 _v _q 
  have p17294 := n17294 _v _q 
  have p17136 := n17136 _v _q 
  have p17141 := n17141 _v _q 
  have p16913 := n16913 _v _q 
  have p20209 := n20209 _v _q h2061 h6784
  have p20096 := n20096 _v _q 
  have p17053 := n17053 _v _q 
  have p15217 := n15217 _v _q h2061
  have p17055 := n17055 _v _q 
  have p20202 := n20202 _v _q h2061 h6784
  have p15718 := n15718 _v _q h6780
  exact FloorCertificate.node_20211 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e61 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2863 _v) (e2877 _v) (e2879 _v) (e2898 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2913 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p17079 p16578 p19762 p17050 p11473 p16858 p20193 p15720 p17089 p19665 p20111 p11409 p16513 p20120 p17108 p15560 p16598 p16549 p20206 p20126 p13951 p17009 p19771 p16607 p16619 p16911 p16620 p16856 p15705 p19747 p19750 p15702 p20208 p19752 p20169 p17058 p17064 p17067 p17069 p17072 p16854 p19772 p17078 p17080 p17083 p17074 p17087 p17758 p17091 p17093 p15713 p17221 p17098 p17106 p17100 p17102 p19610 p17104 p17096 p16625 p16626 p17113 p19758 p17122 p17117 p17124 p17115 p17120 p19760 p17127 p16778 p17874 p17131 p17110 p17133 p16603 p16816 p17111 p17294 p17136 p17141 p16913 p20209 p20096 p17053 p15217 p17055 p20202 p15718
theorem n20212 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2733 : (e2733 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4306 : (e4306 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4434 : (e4434 _v)) (h4491 : (e4491 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5100 : (e5100 _v)) (h5208 : (e5208 _v)) (h6571 : (e6571 _v)) (h7807 : (e7807 _v)) (h8038 : (e8038 _v)) (h8045 : (e8045 _v)) : (e4839 _v) := by
  have p17372 := n17372 _v _q 
  have p15986 := n15986 _v _q h2733
  have p20186 := n20186 _v _q h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h3976 h4059 h4156 h4199 h4306 h4369 h4398 h4434 h4491 h4567 h4608 h4653 h4675 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h5208 h6571 h7807 h8045
  have p16017 := n16017 _v _q h2733
  have p8602 := n8602 _v _q h8038
  have p4994 := n4994 _v _q h3069
  have p17255 := n17255 _v _q h6571
  have p4987 := n4987 _v _q h4434
  have p17786 := n17786 _v _q h7807
  have p4991 := n4991 _v _q h4608
  have p4999 := n4999 _v _q h91
  have p4996 := n4996 _v _q h3937
  have p20210 := n20210 _v _q h91 h225 h442 h488 h2733 h3069 h3105 h3152 h3937 h3946 h3976 h4059 h4156 h4199 h4306 h4369 h4398 h4434 h4491 h4567 h4608 h4653 h4675 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h5208 h6571 h7807 h8038 h8045
  have p5003 := n5003 _v _q h4199
  have p4998 := n4998 _v _q h3152
  have p17128 := n17128 _v _q h4491
  have p4983 := n4983 _v _q h4813
  have p5008 := n5008 _v _q h4787
  have p17129 := n17129 _v _q h4903
  have p17175 := n17175 _v _q h5208
  have p5006 := n5006 _v _q h4675
  have p17159 := n17159 _v _q h5100
  have p15373 := n15373 _v _q h7807
  have p17134 := n17134 _v _q h4398
  have p17157 := n17157 _v _q h8045
  have p17137 := n17137 _v _q h4059
  have p17138 := n17138 _v _q h4306
  have p5007 := n5007 _v _q h225
  have p4992 := n4992 _v _q h442
  have p17143 := n17143 _v _q h4567
  have p17056 := n17056 _v _q h3946
  have p17060 := n17060 _v _q h4653
  have p17061 := n17061 _v _q h4747
  have p4995 := n4995 _v _q h4369
  have p17076 := n17076 _v _q h3976
  have p4985 := n4985 _v _q h4156
  have p4988 := n4988 _v _q h488
  have p4986 := n4986 _v _q h3105
  have p4984 := n4984 _v _q h4872
  have p17094 := n17094 _v _q h4724
  simp only [e51, e57, e91, e95, e196, e225, e230, e442, e443, e488, e493, e2475, e3069, e3074, e3105, e3106, e3152, e3156, e3937, e3942, e3946, e3947, e3976, e3981, e4059, e4064, e4101, e4106, e4156, e4157, e4199, e4200, e4260, e4261, e4306, e4311, e4369, e4370, e4398, e4403, e4434, e4435, e4491, e4496, e4567, e4572, e4608, e4609, e4653, e4658, e4675, e4676, e4724, e4729, e4747, e4752, e4787, e4788, e4813, e4814, e4838, e4839, e4872, e4873, e4903, e4908, e5100, e5103, e5195, e5208, e5218, e7749, e7752, e7814, e7817, e7935, e7943, e8038, e8045, e8048, e17371] at *
  tauto
theorem n20213 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2733 : (e2733 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4306 : (e4306 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4434 : (e4434 _v)) (h4491 : (e4491 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5100 : (e5100 _v)) (h5208 : (e5208 _v)) (h6571 : (e6571 _v)) (h7807 : (e7807 _v)) (h8038 : (e8038 _v)) (h8045 : (e8045 _v)) : (e8301 _v) := by
  have p16285 := n16285 _v _q 
  have p20212 := n20212 _v _q h91 h225 h442 h488 h2733 h3069 h3105 h3152 h3937 h3946 h3976 h4059 h4156 h4199 h4306 h4369 h4398 h4434 h4491 h4567 h4608 h4653 h4675 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h5208 h6571 h7807 h8038 h8045
  simp only [e4836, e4837, e4838, e4839, e8301, e8302] at *
  tauto
theorem n20215 (_v : Vars) (_q : Query _v)  : (e20214 _v) := by
  by_contra hc
  change ¬ ((e2799 _v) ∨ (¬ (e3919 _v)) ∨ (e2793 _v) ∨ (¬ (e2061 _v))) at hc
  have h2061 : (e2061 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr hn))))
  have h3919 : (e3919 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h6780 : (e6780 _v) := (fun hn => hc (Or.inl hn))
  have h6784 : (e6784 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have p20211 := n20211 _v _q h2061 h3919 h6780 h6784
  exact p20211
theorem n20216 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2733 : (e2733 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4306 : (e4306 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4434 : (e4434 _v)) (h4491 : (e4491 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5100 : (e5100 _v)) (h5208 : (e5208 _v)) (h6571 : (e6571 _v)) (h7807 : (e7807 _v)) (h8038 : (e8038 _v)) (h8045 : (e8045 _v)) : (e8310 _v) := by
  have p14906 := n14906 _v _q 
  have p20213 := n20213 _v _q h91 h225 h442 h488 h2733 h3069 h3105 h3152 h3937 h3946 h3976 h4059 h4156 h4199 h4306 h4369 h4398 h4434 h4491 h4567 h4608 h4653 h4675 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h5208 h6571 h7807 h8038 h8045
  simp only [e2529, e4836, e4837, e4838, e4839, e8301, e8307, e8310, e8312] at *
  tauto
theorem n20217 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2733 : (e2733 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4306 : (e4306 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4434 : (e4434 _v)) (h4491 : (e4491 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5100 : (e5100 _v)) (h5208 : (e5208 _v)) (h6571 : (e6571 _v)) (h7807 : (e7807 _v)) (h8038 : (e8038 _v)) (h8045 : (e8045 _v)) : (e8322 _v) := by
  have p15218 := n15218 _v _q 
  have p20216 := n20216 _v _q h91 h225 h442 h488 h2733 h3069 h3105 h3152 h3937 h3946 h3976 h4059 h4156 h4199 h4306 h4369 h4398 h4434 h4491 h4567 h4608 h4653 h4675 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h5208 h6571 h7807 h8038 h8045
  simp only [e2529, e8310, e8315, e8317, e8319, e8320, e8321, e8322, e11298] at *
  tauto
theorem n20218 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2733 : (e2733 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4306 : (e4306 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4434 : (e4434 _v)) (h4491 : (e4491 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5100 : (e5100 _v)) (h5208 : (e5208 _v)) (h6571 : (e6571 _v)) (h7807 : (e7807 _v)) (h8038 : (e8038 _v)) (h8045 : (e8045 _v)) : (e8317 _v) := by
  have p11541 := n11541 _v _q 
  have p20217 := n20217 _v _q h91 h225 h442 h488 h2733 h3069 h3105 h3152 h3937 h3946 h3976 h4059 h4156 h4199 h4306 h4369 h4398 h4434 h4491 h4567 h4608 h4653 h4675 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h5208 h6571 h7807 h8038 h8045
  simp only [e8315, e8317, e8319, e8320, e8321, e8322, e8491] at *
  tauto
theorem n20219 (_v : Vars) (_q : Query _v) (h2061 : (e2061 _v)) (h3919 : (e3919 _v)) (h6784 : (e6784 _v)) : (e2799 _v) := by
  have p20215 := n20215 _v _q 
  have p17079 := n17079 _v _q h3919
  have p11473 := n11473 _v _q h6784
  have p11409 := n11409 _v _q h2061
  simp only [e2061, e2793, e2799, e3919, e3920, e6454, e6784, e20214] at *
  tauto
theorem n20220 (_v : Vars) (_q : Query _v) (h2061 : (e2061 _v)) (h3919 : (e3919 _v)) (h6784 : (e6784 _v)) : (e8390 _v) := by
  have p14912 := n14912 _v _q 
  have p20219 := n20219 _v _q h2061 h3919 h6784
  simp only [e2799, e4922, e4923, e4924, e4925, e6780, e8384, e8390, e8393] at *
  tauto
theorem n20221 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4306 : (e4306 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4434 : (e4434 _v)) (h4491 : (e4491 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5100 : (e5100 _v)) (h5208 : (e5208 _v)) (h6571 : (e6571 _v)) (h7807 : (e7807 _v)) (h8045 : (e8045 _v)) : (e4440 _v) := by
  have p16928 := n16928 _v _q 
  have p20129 := n20129 _v _q h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h3976 h4059 h4156 h4199 h4306 h4369 h4398 h4434 h4491 h4567 h4608 h4653 h4675 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h5208 h6571 h7807 h8045
  simp only [e4439, e4440, e4444, e4445, e4446, e4447, e5023] at *
  tauto
theorem n20222 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2733 : (e2733 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4306 : (e4306 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4434 : (e4434 _v)) (h4491 : (e4491 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5100 : (e5100 _v)) (h5208 : (e5208 _v)) (h6571 : (e6571 _v)) (h7807 : (e7807 _v)) (h8038 : (e8038 _v)) (h8045 : (e8045 _v)) : (e7489 _v) := by
  have p20218 := n20218 _v _q h91 h225 h442 h488 h2733 h3069 h3105 h3152 h3937 h3946 h3976 h4059 h4156 h4199 h4306 h4369 h4398 h4434 h4491 h4567 h4608 h4653 h4675 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h5208 h6571 h7807 h8038 h8045
  have p8447 := n8447 _v _q h6571
  have p20186 := n20186 _v _q h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h3976 h4059 h4156 h4199 h4306 h4369 h4398 h4434 h4491 h4567 h4608 h4653 h4675 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h5208 h6571 h7807 h8045
  have p4987 := n4987 _v _q h4434
  have p16929 := n16929 _v _q 
  have p20221 := n20221 _v _q h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h3976 h4059 h4156 h4199 h4306 h4369 h4398 h4434 h4491 h4567 h4608 h4653 h4675 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h5208 h6571 h7807 h8045
  have p5255 := n5255 _v _q 
  have p8602 := n8602 _v _q h8038
  have p16017 := n16017 _v _q h2733
  have p17102 := n17102 _v _q 
  have p17104 := n17104 _v _q 
  have p17106 := n17106 _v _q 
  have p17108 := n17108 _v _q 
  have p17110 := n17110 _v _q 
  have p13951 := n13951 _v _q 
  have p17113 := n17113 _v _q 
  have p4994 := n4994 _v _q h3069
  have p17117 := n17117 _v _q 
  have p17255 := n17255 _v _q h6571
  have p17120 := n17120 _v _q 
  have p17786 := n17786 _v _q h7807
  have p17009 := n17009 _v _q 
  have p17122 := n17122 _v _q 
  have p4991 := n4991 _v _q h4608
  have p16576 := n16576 _v _q 
  have p17124 := n17124 _v _q 
  have p4999 := n4999 _v _q h91
  have p4996 := n4996 _v _q h3937
  have p20210 := n20210 _v _q h91 h225 h442 h488 h2733 h3069 h3105 h3152 h3937 h3946 h3976 h4059 h4156 h4199 h4306 h4369 h4398 h4434 h4491 h4567 h4608 h4653 h4675 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h5208 h6571 h7807 h8038 h8045
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
  have p15373 := n15373 _v _q h7807
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
  have p15986 := n15986 _v _q h2733
  have p20216 := n20216 _v _q h91 h225 h442 h488 h2733 h3069 h3105 h3152 h3937 h3946 h3976 h4059 h4156 h4199 h4306 h4369 h4398 h4434 h4491 h4567 h4608 h4653 h4675 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h5208 h6571 h7807 h8038 h8045
  exact FloorCertificate.node_20222 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2849 _v) (e2863 _v) (e2877 _v) (e2883 _v) (e2902 _v) (e2911 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p20218 p8447 p20186 p4987 p16929 p20221 p5255 p8602 p16017 p17102 p17104 p17106 p17108 p17110 p13951 p17113 p4994 p17117 p17255 p17120 p17786 p17009 p17122 p4991 p16576 p17124 p4999 p4996 p20210 p17147 p5003 p4998 p17127 p17128 p4983 p5008 p17256 p17129 p17175 p5006 p17159 p17131 p15373 p17133 p17134 p17136 p17157 p17137 p17138 p5007 p16778 p17141 p4992 p17143 p17050 p17053 p17055 p17056 p17058 p17060 p17061 p17064 p4995 p17067 p17069 p17072 p17074 p17076 p4985 p4988 p17078 p4986 p17080 p17083 p4984 p17087 p17091 p17094 p17093 p17111 p17115 p17089 p17100 p17098 p17096 p15986 p20216
theorem n20223 (_v : Vars) (_q : Query _v) (h2061 : (e2061 _v)) (h3919 : (e3919 _v)) (h6784 : (e6784 _v)) : (e4924 _v) := by
  have p16462 := n16462 _v _q 
  have p20220 := n20220 _v _q h2061 h3919 h6784
  simp only [e4922, e4923, e4924, e4925, e8384, e8385, e8390] at *
  tauto
theorem n20225 (_v : Vars) (_q : Query _v)  : (e20224 _v) := by
  by_contra hc
  change ¬ ((¬ (e2733 _v)) ∨ (e2358 _v) ∨ (¬ (e4434 _v)) ∨ (e2475 _v) ∨ (¬ (e3069 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4491 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4903 _v)) ∨ (¬ (e5208 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e5100 _v)) ∨ (¬ (e4398 _v)) ∨ (¬ (e8045 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e4567 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e3976 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4724 _v)) ∨ (e2303 _v)) at hc
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h225 : (e225 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))
  have h442 : (e442 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))
  have h488 : (e488 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))
  have h2733 : (e2733 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h3069 : (e3069 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h3105 : (e3105 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h3946 : (e3946 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))
  have h3976 : (e3976 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))
  have h4059 : (e4059 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))
  have h4156 : (e4156 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))
  have h4199 : (e4199 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h4306 : (e4306 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))
  have h4369 : (e4369 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))
  have h4398 : (e4398 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))
  have h4434 : (e4434 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4491 : (e4491 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h4567 : (e4567 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))
  have h4608 : (e4608 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h4653 : (e4653 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))
  have h4675 : (e4675 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))
  have h4724 : (e4724 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))))))))))
  have h4747 : (e4747 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h4872 : (e4872 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))))))))
  have h4903 : (e4903 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h5100 : (e5100 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))
  have h5208 : (e5208 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h6571 : (e6571 _v) := (fun hn => hc (Or.inr (Or.inl hn)))
  have h7807 : (e7807 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn)))))))))))))))))))))))))))))))))))
  have h8038 : (e8038 _v) := (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h8045 : (e8045 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))
  have p20222 := n20222 _v _q h91 h225 h442 h488 h2733 h3069 h3105 h3152 h3937 h3946 h3976 h4059 h4156 h4199 h4306 h4369 h4398 h4434 h4491 h4567 h4608 h4653 h4675 h4724 h4747 h4787 h4813 h4872 h4903 h5100 h5208 h6571 h7807 h8038 h8045
  exact p20222
theorem n20226 (_v : Vars) (_q : Query _v) (h2061 : (e2061 _v)) (h3919 : (e3919 _v)) (h6784 : (e6784 _v)) : (e7489 _v) := by
  have p258 := n258 _v _q 
  have p15217 := n15217 _v _q h2061
  have p20202 := n20202 _v _q h2061 h6784
  have p16578 := n16578 _v _q 
  have p17055 := n17055 _v _q 
  have p20223 := n20223 _v _q h2061 h3919 h6784
  have p16858 := n16858 _v _q 
  have p20193 := n20193 _v _q h2061 h6784
  have p17079 := n17079 _v _q h3919
  have p19762 := n19762 _v _q h6784
  have p17050 := n17050 _v _q 
  have p17089 := n17089 _v _q 
  have p19665 := n19665 _v _q 
  have p20111 := n20111 _v _q h6784
  have p11409 := n11409 _v _q h2061
  have p16513 := n16513 _v _q h6784
  have p20120 := n20120 _v _q h6784
  have p17108 := n17108 _v _q 
  have p15560 := n15560 _v _q h6784
  have p16598 := n16598 _v _q h6784
  have p16549 := n16549 _v _q h6784
  have p20206 := n20206 _v _q h2061 h6784
  have p20126 := n20126 _v _q 
  have p13951 := n13951 _v _q 
  have p17009 := n17009 _v _q 
  have p19771 := n19771 _v _q h6784
  have p16607 := n16607 _v _q h6784
  have p16619 := n16619 _v _q h6784
  have p16911 := n16911 _v _q 
  have p16620 := n16620 _v _q h6784
  have p16856 := n16856 _v _q h6784
  have p15705 := n15705 _v _q h6784
  have p19747 := n19747 _v _q h6784
  have p19750 := n19750 _v _q h6784
  have p15702 := n15702 _v _q h6784
  have p20208 := n20208 _v _q h2061 h6784
  have p19752 := n19752 _v _q h6784
  have p20169 := n20169 _v _q h6784
  have p17058 := n17058 _v _q 
  have p17064 := n17064 _v _q 
  have p17067 := n17067 _v _q 
  have p17069 := n17069 _v _q 
  have p17072 := n17072 _v _q 
  have p16854 := n16854 _v _q h6784
  have p19772 := n19772 _v _q h6784
  have p17078 := n17078 _v _q 
  have p17080 := n17080 _v _q 
  have p17083 := n17083 _v _q 
  have p17074 := n17074 _v _q 
  have p17087 := n17087 _v _q 
  have p17758 := n17758 _v _q 
  have p17091 := n17091 _v _q 
  have p17093 := n17093 _v _q 
  have p15713 := n15713 _v _q h6784
  have p17221 := n17221 _v _q 
  have p17098 := n17098 _v _q 
  have p17106 := n17106 _v _q 
  have p17100 := n17100 _v _q 
  have p17102 := n17102 _v _q 
  have p19610 := n19610 _v _q 
  have p17104 := n17104 _v _q 
  have p17096 := n17096 _v _q 
  have p16625 := n16625 _v _q h6784
  have p16626 := n16626 _v _q h6784
  have p17113 := n17113 _v _q 
  have p19758 := n19758 _v _q h6784
  have p17122 := n17122 _v _q 
  have p17117 := n17117 _v _q 
  have p17124 := n17124 _v _q 
  have p17115 := n17115 _v _q 
  have p17120 := n17120 _v _q 
  have p19760 := n19760 _v _q h6784
  have p17127 := n17127 _v _q 
  have p16778 := n16778 _v _q 
  have p17874 := n17874 _v _q 
  have p17131 := n17131 _v _q 
  have p17110 := n17110 _v _q 
  have p17133 := n17133 _v _q 
  have p16603 := n16603 _v _q h6784
  have p16816 := n16816 _v _q h6784
  have p17111 := n17111 _v _q 
  have p17294 := n17294 _v _q 
  have p17136 := n17136 _v _q 
  have p17141 := n17141 _v _q 
  have p16913 := n16913 _v _q 
  have p20209 := n20209 _v _q h2061 h6784
  have p20096 := n20096 _v _q 
  have p17053 := n17053 _v _q 
  exact FloorCertificate.node_20226 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e49 _v) (e61 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2863 _v) (e2877 _v) (e2879 _v) (e2898 _v) (e2902 _v) (e2907 _v) (e2911 _v) (e2913 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e4215 _v) (e4541 _v) (e4808 _v) p258 p15217 p20202 p16578 p17055 p20223 p16858 p20193 p17079 p19762 p17050 p17089 p19665 p20111 p11409 p16513 p20120 p17108 p15560 p16598 p16549 p20206 p20126 p13951 p17009 p19771 p16607 p16619 p16911 p16620 p16856 p15705 p19747 p19750 p15702 p20208 p19752 p20169 p17058 p17064 p17067 p17069 p17072 p16854 p19772 p17078 p17080 p17083 p17074 p17087 p17758 p17091 p17093 p15713 p17221 p17098 p17106 p17100 p17102 p19610 p17104 p17096 p16625 p16626 p17113 p19758 p17122 p17117 p17124 p17115 p17120 p19760 p17127 p16778 p17874 p17131 p17110 p17133 p16603 p16816 p17111 p17294 p17136 p17141 p16913 p20209 p20096 p17053
theorem n20227 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3976 : (e3976 _v)) (h4059 : (e4059 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4306 : (e4306 _v)) (h4369 : (e4369 _v)) (h4398 : (e4398 _v)) (h4434 : (e4434 _v)) (h4491 : (e4491 _v)) (h4567 : (e4567 _v)) (h4608 : (e4608 _v)) (h4653 : (e4653 _v)) (h4675 : (e4675 _v)) (h4724 : (e4724 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h4903 : (e4903 _v)) (h5100 : (e5100 _v)) (h5208 : (e5208 _v)) (h6571 : (e6571 _v)) (h7807 : (e7807 _v)) (h8038 : (e8038 _v)) (h8045 : (e8045 _v)) : (e6750 _v) := by
  have p20225 := n20225 _v _q 
  have p17143 := n17143 _v _q h4567
  have p4987 := n4987 _v _q h4434
  have p8602 := n8602 _v _q h8038
  have p4994 := n4994 _v _q h3069
  have p4991 := n4991 _v _q h4608
  have p4999 := n4999 _v _q h91
  have p4996 := n4996 _v _q h3937
  have p5003 := n5003 _v _q h4199
  have p4998 := n4998 _v _q h3152
  have p17128 := n17128 _v _q h4491
  have p4983 := n4983 _v _q h4813
  have p5008 := n5008 _v _q h4787
  have p17129 := n17129 _v _q h4903
  have p17175 := n17175 _v _q h5208
  have p5006 := n5006 _v _q h4675
  have p17159 := n17159 _v _q h5100
  have p17134 := n17134 _v _q h4398
  have p17157 := n17157 _v _q h8045
  have p17137 := n17137 _v _q h4059
  have p17138 := n17138 _v _q h4306
  have p5007 := n5007 _v _q h225
  have p4992 := n4992 _v _q h442
  have p8447 := n8447 _v _q h6571
  have p17056 := n17056 _v _q h3946
  have p17060 := n17060 _v _q h4653
  have p17061 := n17061 _v _q h4747
  have p4995 := n4995 _v _q h4369
  have p17076 := n17076 _v _q h3976
  have p4985 := n4985 _v _q h4156
  have p4988 := n4988 _v _q h488
  have p4986 := n4986 _v _q h3105
  have p4984 := n4984 _v _q h4872
  have p17094 := n17094 _v _q h4724
  have p11350 := n11350 _v _q h7807
  simp only [e91, e95, e225, e230, e442, e443, e488, e493, e2303, e2358, e2475, e2733, e3069, e3074, e3105, e3106, e3152, e3156, e3937, e3942, e3946, e3947, e3976, e3981, e4059, e4064, e4156, e4157, e4199, e4200, e4306, e4311, e4369, e4370, e4398, e4403, e4434, e4435, e4491, e4496, e4567, e4572, e4608, e4609, e4653, e4658, e4675, e4676, e4724, e4729, e4747, e4752, e4787, e4788, e4813, e4814, e4872, e4873, e4903, e4908, e5100, e5103, e5208, e5218, e6571, e6750, e7807, e8038, e8045, e8048, e20224] at *
  tauto
theorem n20229 (_v : Vars) (_q : Query _v)  : (e20228 _v) := by
  by_contra hc
  change ¬ ((¬ (e3919 _v)) ∨ (¬ (e2061 _v)) ∨ (e2793 _v)) at hc
  have h2061 : (e2061 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h3919 : (e3919 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h6784 : (e6784 _v) := (fun hn => hc (Or.inr (Or.inr hn)))
  have p20226 := n20226 _v _q h2061 h3919 h6784
  exact p20226
end
end Assembly
