import Dag212
import generated.th_lemma_26
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n19546 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e4546 _v) := by
  have p16307 := n16307 _v _q 
  have p19521 := n19521 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (e8029 _v) ∨ (e4546 _v) at p16307
  change (¬ (e8029 _v)) at p19521
  rcases p16307 with hlit | hlit
  · exact (False.elim (p19521 hlit))
  · exact hlit
theorem n19547 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e2303 _v) := by
  have p11353 := n11353 _v _q 
  have p19522 := n19522 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (¬ (e2132 _v)) ∨ (e2303 _v) at p11353
  rcases p11353 with hlit | hlit
  · exact (False.elim (hlit p19522))
  · exact hlit
theorem n19548 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e7804 _v) := by
  have p14837 := n14837 _v _q 
  have p19547 := n19547 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (¬ (e2303 _v)) ∨ (¬ (e7798 _v)) at p14837
  rcases p14837 with hlit | hlit
  · exact (False.elim (hlit p19547))
  · exact hlit
theorem n19549 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e4285 _v) := by
  have p16274 := n16274 _v _q 
  have p19548 := n19548 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (e7798 _v) ∨ (e4285 _v) at p16274
  change (¬ (e7798 _v)) at p19548
  rcases p16274 with hlit | hlit
  · exact (False.elim (p19548 hlit))
  · exact hlit
theorem n19550 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e4301 _v) := by
  have p14840 := n14840 _v _q 
  have p19524 := n19524 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (e7822 _v) ∨ (e4301 _v) at p14840
  change (¬ (e7822 _v)) at p19524
  rcases p14840 with hlit | hlit
  · exact (False.elim (p19524 hlit))
  · exact hlit
theorem n19551 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e3585 _v) := by
  have p14783 := n14783 _v _q 
  have p19526 := n19526 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (e7169 _v) ∨ (e3585 _v) at p14783
  change (¬ (e7169 _v)) at p19526
  rcases p14783 with hlit | hlit
  · exact (False.elim (p19526 hlit))
  · exact hlit
theorem n19552 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e4855 _v) := by
  have p16317 := n16317 _v _q 
  have p19528 := n19528 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (e8324 _v) ∨ (e4855 _v) at p16317
  change (¬ (e8324 _v)) at p19528
  rcases p16317 with hlit | hlit
  · exact (False.elim (p19528 hlit))
  · exact hlit
theorem n19553 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e30 _v) := by
  have p16290 := n16290 _v _q 
  have p19530 := n19530 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (e5089 _v) ∨ (e30 _v) at p16290
  change (¬ (e5089 _v)) at p19530
  rcases p16290 with hlit | hlit
  · exact (False.elim (p19530 hlit))
  · exact hlit
theorem n19554 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e4486 _v) := by
  have p15502 := n15502 _v _q 
  have p19532 := n19532 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (e7984 _v) ∨ (e4486 _v) at p15502
  change (¬ (e7984 _v)) at p19532
  rcases p15502 with hlit | hlit
  · exact (False.elim (p19532 hlit))
  · exact hlit
theorem n19555 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e3169 _v) := by
  have p14769 := n14769 _v _q 
  have p19534 := n19534 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (e6888 _v) ∨ (e3169 _v) at p14769
  change (¬ (e6888 _v)) at p19534
  rcases p14769 with hlit | hlit
  · exact (False.elim (p19534 hlit))
  · exact hlit
theorem n19556 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e6973 _v) := by
  have p14377 := n14377 _v _q 
  have p19536 := n19536 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (e2310 _v) ∨ (¬ (e6965 _v)) at p14377
  change (¬ (e2310 _v)) at p19536
  rcases p14377 with hlit | hlit
  · exact (False.elim (p19536 hlit))
  · exact hlit
theorem n19557 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e3267 _v) := by
  have p14776 := n14776 _v _q 
  have p19556 := n19556 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (e6965 _v) ∨ (e3267 _v) at p14776
  change (¬ (e6965 _v)) at p19556
  rcases p14776 with hlit | hlit
  · exact (False.elim (p19556 hlit))
  · exact hlit
theorem n19558 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e4394 _v) := by
  have p14852 := n14852 _v _q 
  have p19540 := n19540 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (e7904 _v) ∨ (e4394 _v) at p14852
  change (¬ (e7904 _v)) at p19540
  rcases p14852 with hlit | hlit
  · exact (False.elim (p19540 hlit))
  · exact hlit
theorem n19559 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e7739 _v) := by
  have p14833 := n14833 _v _q 
  have p19522 := n19522 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (¬ (e2132 _v)) ∨ (¬ (e7733 _v)) at p14833
  rcases p14833 with hlit | hlit
  · exact (False.elim (hlit p19522))
  · exact hlit
theorem n19560 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e4220 _v) := by
  have p16334 := n16334 _v _q 
  have p19559 := n19559 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (e7733 _v) ∨ (e4220 _v) at p16334
  change (¬ (e7733 _v)) at p19559
  rcases p16334 with hlit | hlit
  · exact (False.elim (p19559 hlit))
  · exact hlit
theorem n19561 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e4720 _v) := by
  have p15030 := n15030 _v _q 
  have p19542 := n19542 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (e8206 _v) ∨ (e4720 _v) at p15030
  change (¬ (e8206 _v)) at p19542
  rcases p15030 with hlit | hlit
  · exact (False.elim (p19542 hlit))
  · exact hlit
theorem n19562 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3971 : (e3971 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e6780 _v) := by
  have p17867 := n17867 _v _q 
  have p5002 := n5002 _v _q h3971
  have p19513 := n19513 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p4971 := n4971 _v _q h4419
  have p19544 := n19544 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p19545 := n19545 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p19546 := n19546 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p19549 := n19549 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p4978 := n4978 _v _q h4477
  have p4979 := n4979 _v _q h4139
  have p19550 := n19550 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p4981 := n4981 _v _q h4260
  have p4983 := n4983 _v _q h4813
  have p4984 := n4984 _v _q h4872
  have p4985 := n4985 _v _q h4156
  have p4986 := n4986 _v _q h3105
  have p4987 := n4987 _v _q h4434
  have p4988 := n4988 _v _q h488
  have p4989 := n4989 _v _q h4838
  have p19551 := n19551 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p253 := n253 _v _q h191
  have p19543 := n19543 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p4991 := n4991 _v _q h4608
  have p4992 := n4992 _v _q h442
  have p17061 := n17061 _v _q h4747
  have p4994 := n4994 _v _q h3069
  have p4995 := n4995 _v _q h4369
  have p4996 := n4996 _v _q h3937
  have p19552 := n19552 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p4998 := n4998 _v _q h3152
  have p4999 := n4999 _v _q h91
  have p19553 := n19553 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p5001 := n5001 _v _q h4096
  have p19554 := n19554 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p17056 := n17056 _v _q h3946
  have p5003 := n5003 _v _q h4199
  have p19555 := n19555 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p5006 := n5006 _v _q h4675
  have p5007 := n5007 _v _q h225
  have p5008 := n5008 _v _q h4787
  have p5010 := n5010 _v _q h70
  have p19557 := n19557 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (e2598 _v) ∨ (¬ (e3267 _v)) ∨ (¬ (e3585 _v)) ∨ (¬ (e4419 _v)) ∨ (¬ (e4899 _v)) ∨ (¬ (e4562 _v)) ∨ (¬ (e4546 _v)) ∨ (¬ (e4285 _v)) ∨ (¬ (e4477 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e4301 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e2799 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e4648 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e4855 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e30 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e3971 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e3169 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4486 _v)) at p17867
  change (¬ (e2598 _v)) at p19513
  rcases p17867 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact (False.elim (p19513 hlit))
  · exact (False.elim (hlit p19557))
  · exact (False.elim (hlit p19551))
  · exact (False.elim (hlit p4971))
  · exact (False.elim (hlit p19544))
  · exact (False.elim (hlit p19545))
  · exact (False.elim (hlit p19546))
  · exact (False.elim (hlit p19549))
  · exact (False.elim (hlit p4978))
  · exact (False.elim (hlit p4979))
  · exact (False.elim (hlit p19550))
  · exact (False.elim (hlit p4981))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p4984))
  · exact (False.elim (hlit p4985))
  · exact (False.elim (hlit p4986))
  · exact (False.elim (hlit p4987))
  · exact (False.elim (hlit p4988))
  · exact (False.elim (hlit p4989))
  · exact hlit
  · exact (False.elim (hlit p253))
  · exact (False.elim (hlit p19543))
  · exact (False.elim (hlit p4991))
  · exact (False.elim (hlit p4992))
  · exact (False.elim (hlit p17061))
  · exact (False.elim (hlit p4994))
  · exact (False.elim (hlit p4995))
  · exact (False.elim (hlit p4996))
  · exact (False.elim (hlit p19552))
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p4999))
  · exact (False.elim (hlit p19553))
  · exact (False.elim (hlit p5001))
  · exact (False.elim (hlit p5002))
  · exact (False.elim (hlit p17056))
  · exact (False.elim (hlit p5003))
  · exact (False.elim (hlit p19555))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p5007))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p5010))
  · exact (False.elim (hlit p19554))
theorem n19563 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3971 : (e3971 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e8408 _v) := by
  have p15435 := n15435 _v _q 
  have p19562 := n19562 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h3971 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (e2799 _v) ∨ (¬ (e8407 _v)) at p15435
  change (¬ (e2799 _v)) at p19562
  rcases p15435 with hlit | hlit
  · exact (False.elim (p19562 hlit))
  · exact hlit
theorem n19564 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3971 : (e3971 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e8398 _v) := by
  have p11470 := n11470 _v _q 
  have p19563 := n19563 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h3971 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (e8407 _v) ∨ (e8398 _v) at p11470
  change (¬ (e8407 _v)) at p19563
  rcases p11470 with hlit | hlit
  · exact (False.elim (p19563 hlit))
  · exact hlit
theorem n19565 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h3971 : (e3971 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e7489 _v) := by
  have p19543 := n19543 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p17221 := n17221 _v _q 
  have p14849 := n14849 _v _q 
  have p19562 := n19562 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h3971 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p19551 := n19551 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p19554 := n19554 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p8663 := n8663 _v _q 
  have p19538 := n19538 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p14821 := n14821 _v _q 
  have p5002 := n5002 _v _q h3971
  have p19558 := n19558 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p17146 := n17146 _v _q 
  have p14810 := n14810 _v _q 
  have p16178 := n16178 _v _q 
  have p19553 := n19553 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p16911 := n16911 _v _q 
  have p16394 := n16394 _v _q 
  have p19555 := n19555 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p16175 := n16175 _v _q 
  have p4983 := n4983 _v _q h4813
  have p17053 := n17053 _v _q 
  have p17127 := n17127 _v _q 
  have p4995 := n4995 _v _q h4369
  have p5003 := n5003 _v _q h4199
  have p4998 := n4998 _v _q h3152
  have p16913 := n16913 _v _q 
  have p19546 := n19546 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p19549 := n19549 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p16576 := n16576 _v _q 
  have p19560 := n19560 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p5008 := n5008 _v _q h4787
  have p19550 := n19550 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p17055 := n17055 _v _q 
  have p17058 := n17058 _v _q 
  have p5006 := n5006 _v _q h4675
  have p17056 := n17056 _v _q h3946
  have p17061 := n17061 _v _q h4747
  have p17147 := n17147 _v _q 
  have p17064 := n17064 _v _q 
  have p19545 := n19545 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p19561 := n19561 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p16929 := n16929 _v _q 
  have p17067 := n17067 _v _q 
  have p17072 := n17072 _v _q 
  have p19552 := n19552 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p5007 := n5007 _v _q h225
  have p17074 := n17074 _v _q 
  have p4985 := n4985 _v _q h4156
  have p4987 := n4987 _v _q h4434
  have p5010 := n5010 _v _q h70
  have p4981 := n4981 _v _q h4260
  have p4988 := n4988 _v _q h488
  have p17080 := n17080 _v _q 
  have p17078 := n17078 _v _q 
  have p4989 := n4989 _v _q h4838
  have p4971 := n4971 _v _q h4419
  have p17091 := n17091 _v _q 
  have p4979 := n4979 _v _q h4139
  have p4986 := n4986 _v _q h3105
  have p4978 := n4978 _v _q h4477
  have p4992 := n4992 _v _q h442
  have p16181 := n16181 _v _q 
  have p4984 := n4984 _v _q h4872
  have p17083 := n17083 _v _q 
  have p4991 := n4991 _v _q h4608
  have p17087 := n17087 _v _q 
  have p17115 := n17115 _v _q 
  have p19557 := n19557 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p253 := n253 _v _q h191
  have p17098 := n17098 _v _q 
  have p17104 := n17104 _v _q 
  have p17110 := n17110 _v _q 
  have p17096 := n17096 _v _q 
  have p17106 := n17106 _v _q 
  have p17102 := n17102 _v _q 
  have p17108 := n17108 _v _q 
  have p4994 := n4994 _v _q h3069
  have p17117 := n17117 _v _q 
  have p17120 := n17120 _v _q 
  have p17113 := n17113 _v _q 
  have p17124 := n17124 _v _q 
  have p17122 := n17122 _v _q 
  have p17093 := n17093 _v _q 
  have p17141 := n17141 _v _q 
  have p17131 := n17131 _v _q 
  have p17069 := n17069 _v _q 
  have p5001 := n5001 _v _q h4096
  have p4996 := n4996 _v _q h3937
  have p17100 := n17100 _v _q 
  have p4999 := n4999 _v _q h91
  have p17133 := n17133 _v _q 
  have p17136 := n17136 _v _q 
  have p13951 := n13951 _v _q 
  have p16779 := n16779 _v _q 
  have p16184 := n16184 _v _q 
  have p17151 := n17151 _v _q 
  have p19564 := n19564 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h3971 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p19544 := n19544 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p5255 := n5255 _v _q 
  have p19513 := n19513 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p10893 := n10893 _v _q 
  have p5257 := n5257 _v _q 
  exact FloorCertificate.node_19565 (e2 _v) (e7 _v) (e9 _v) (e16 _v) (e17 _v) (e45 _v) (e49 _v) (e61 _v) (e80 _v) (e101 _v) (e110 _v) (e188 _v) (e211 _v) (e259 _v) (e291 _v) (e297 _v) (e332 _v) (e362 _v) (e403 _v) (e437 _v) (e466 _v) (e497 _v) (e2817 _v) (e2831 _v) (e2834 _v) (e2849 _v) (e2863 _v) (e2877 _v) (e2879 _v) (e2883 _v) (e2898 _v) (e2900 _v) (e2902 _v) (e2905 _v) (e2907 _v) (e2909 _v) (e2911 _v) (e2913 _v) (e2918 _v) (e2920 _v) (e2922 _v) (e2924 _v) (e2926 _v) (e2928 _v) (e2930 _v) (e2932 _v) (e2933 _v) (e2934 _v) (e2935 _v) (e2937 _v) (e2939 _v) (e2941 _v) (e2942 _v) (e2943 _v) (e2944 _v) (e2945 _v) (e2946 _v) (e2947 _v) (e2948 _v) (e2949 _v) (e2951 _v) (e2953 _v) (e2955 _v) (e2957 _v) (e2959 _v) (e2961 _v) (e2963 _v) (e2964 _v) (e2965 _v) (e2966 _v) (e2967 _v) (e2968 _v) (e2969 _v) (e2970 _v) (e2972 _v) (e2974 _v) (e2976 _v) (e2977 _v) (e2978 _v) (e2979 _v) (e2980 _v) (e2982 _v) (e2984 _v) (e2986 _v) (e2988 _v) (e2990 _v) (e2992 _v) (e2994 _v) (e2995 _v) (e2996 _v) (e2997 _v) (e3141 _v) (e3164 _v) (e3262 _v) (e3574 _v) (e3846 _v) (e4215 _v) (e4324 _v) (e4541 _v) (e4696 _v) (e4808 _v) p19543 p17221 p14849 p19562 p19551 p19554 p8663 p19538 p14821 p5002 p19558 p17146 p14810 p16178 p19553 p16911 p16394 p19555 p16175 p4983 p17053 p17127 p4995 p5003 p4998 p16913 p19546 p19549 p16576 p19560 p5008 p19550 p17055 p17058 p5006 p17056 p17061 p17147 p17064 p19545 p19561 p16929 p17067 p17072 p19552 p5007 p17074 p4985 p4987 p5010 p4981 p4988 p17080 p17078 p4989 p4971 p17091 p4979 p4986 p4978 p4992 p16181 p4984 p17083 p4991 p17087 p17115 p19557 p253 p17098 p17104 p17110 p17096 p17106 p17102 p17108 p4994 p17117 p17120 p17113 p17124 p17122 p17093 p17141 p17131 p17069 p5001 p4996 p17100 p4999 p17133 p17136 p13951 p16779 p16184 p17151 p19564 p19544 p5255 p19513 p10893 p5257
theorem n19567 (_v : Vars) (_q : Query _v)  : (e19566 _v) := by
  by_contra hc
  change ¬ ((¬ (e3971 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4419 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4477 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e91 _v))) at hc
  have h70 : (e70 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn))))))))))))))))))))))))))))
  have h191 : (e191 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))
  have h225 : (e225 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h442 : (e442 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))
  have h488 : (e488 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h3069 : (e3069 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))
  have h3105 : (e3105 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))))
  have h3946 : (e3946 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h3971 : (e3971 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h4096 : (e4096 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))
  have h4139 : (e4139 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))
  have h4156 : (e4156 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h4199 : (e4199 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h4260 : (e4260 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h4369 : (e4369 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4419 : (e4419 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))
  have h4434 : (e4434 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h4477 : (e4477 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))
  have h4608 : (e4608 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))
  have h4675 : (e4675 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h4747 : (e4747 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h4838 : (e4838 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))
  have h4872 : (e4872 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))
  have p19565 := n19565 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h3971 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  exact p19565
theorem n19568 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e3972 _v) := by
  have p19567 := n19567 _v _q 
  have p4978 := n4978 _v _q h4477
  have p4995 := n4995 _v _q h4369
  have p5003 := n5003 _v _q h4199
  have p4998 := n4998 _v _q h3152
  have p5008 := n5008 _v _q h4787
  have p5006 := n5006 _v _q h4675
  have p17056 := n17056 _v _q h3946
  have p17061 := n17061 _v _q h4747
  have p5007 := n5007 _v _q h225
  have p4985 := n4985 _v _q h4156
  have p4987 := n4987 _v _q h4434
  have p5010 := n5010 _v _q h70
  have p4981 := n4981 _v _q h4260
  have p4988 := n4988 _v _q h488
  have p4989 := n4989 _v _q h4838
  have p4971 := n4971 _v _q h4419
  have p4979 := n4979 _v _q h4139
  have p4986 := n4986 _v _q h3105
  have p4983 := n4983 _v _q h4813
  have p4992 := n4992 _v _q h442
  have p4984 := n4984 _v _q h4872
  have p4991 := n4991 _v _q h4608
  have p253 := n253 _v _q h191
  have p4994 := n4994 _v _q h3069
  have p5001 := n5001 _v _q h4096
  have p4996 := n4996 _v _q h3937
  have p4999 := n4999 _v _q h91
  change (¬ (e3971 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4419 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4477 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e91 _v)) at p19567
  rcases p19567 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p4995))
  · exact (False.elim (hlit p5003))
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p17056))
  · exact (False.elim (hlit p17061))
  · exact (False.elim (hlit p5007))
  · exact (False.elim (hlit p4985))
  · exact (False.elim (hlit p4987))
  · exact (False.elim (hlit p5010))
  · exact (False.elim (hlit p4981))
  · exact (False.elim (hlit p4988))
  · exact (False.elim (hlit p4989))
  · exact (False.elim (hlit p4971))
  · exact (False.elim (hlit p4979))
  · exact (False.elim (hlit p4986))
  · exact (False.elim (hlit p4978))
  · exact (False.elim (hlit p4992))
  · exact (False.elim (hlit p4984))
  · exact (False.elim (hlit p4991))
  · exact (False.elim (hlit p253))
  · exact (False.elim (hlit p4994))
  · exact (False.elim (hlit p5001))
  · exact (False.elim (hlit p4996))
  · exact (False.elim (hlit p4999))
theorem n19569 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e7442 _v) := by
  have p15486 := n15486 _v _q 
  have p19568 := n19568 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (e7442 _v) ∨ (e3971 _v) at p15486
  change (¬ (e3971 _v)) at p19568
  rcases p15486 with hlit | hlit
  · exact hlit
  · exact (False.elim (p19568 hlit))
theorem n19570 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e2746 _v) := by
  have p14489 := n14489 _v _q 
  have p19569 := n19569 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (e2746 _v) ∨ (¬ (e7442 _v)) at p14489
  rcases p14489 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p19569))
theorem n19571 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e3984 _v) := by
  have p14691 := n14691 _v _q 
  have p19570 := n19570 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (¬ (e2746 _v)) ∨ (¬ (e3983 _v)) at p14691
  rcases p14691 with hlit | hlit
  · exact (False.elim (hlit p19570))
  · exact hlit
theorem n19572 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e3976 _v) := by
  have p14935 := n14935 _v _q 
  have p19571 := n19571 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  change (e3983 _v) ∨ (e3976 _v) at p14935
  change (¬ (e3983 _v)) at p19571
  rcases p14935 with hlit | hlit
  · exact (False.elim (p19571 hlit))
  · exact hlit
theorem n19573 (_v : Vars) (_q : Query _v)  : (e8520 _v) := by
  simp only [e7520, e7521, e7522, e7523, e7524, e8520] at *
  tauto
theorem n19574 (_v : Vars) (_q : Query _v)  : (e7522 _v) := by
  have p19573 := n19573 _v _q 
  have p14814 := n14814 _v _q 
  change (e7524 _v) ∨ (e7522 _v) at p19573
  change (¬ (e7524 _v)) at p14814
  rcases p19573 with hlit | hlit
  · exact (False.elim (p14814 hlit))
  · exact hlit
theorem n19575 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4139 : (e4139 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4477 : (e4477 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) : (e7489 _v) := by
  have p19568 := n19568 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p19572 := n19572 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p19513 := n19513 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  have p19574 := n19574 _v _q 
  have p5255 := n5255 _v _q 
  have p5257 := n5257 _v _q 
  exact FloorCertificate.node_19575 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) (e2909 _v) (e2990 _v) p19568 p19572 p19513 p19574 p5255 p5257
theorem n19577 (_v : Vars) (_q : Query _v)  : (e19576 _v) := by
  by_contra hc
  change ¬ ((¬ (e4477 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4419 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e91 _v))) at hc
  have h70 : (e70 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))
  have h91 : (e91 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn)))))))))))))))))))))))))))
  have h191 : (e191 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))
  have h225 : (e225 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))
  have h442 : (e442 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))
  have h488 : (e488 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))
  have h3069 : (e3069 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))
  have h3105 : (e3105 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))
  have h3152 : (e3152 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inl hn)))))
  have h3937 : (e3937 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))))))
  have h3946 : (e3946 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))
  have h4096 : (e4096 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))))))
  have h4139 : (e4139 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))
  have h4156 : (e4156 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))
  have h4199 : (e4199 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inl hn))))
  have h4260 : (e4260 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))
  have h4369 : (e4369 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inl hn)))
  have h4419 : (e4419 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))
  have h4434 : (e4434 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))
  have h4477 : (e4477 _v) := Classical.byContradiction (fun hn => hc (Or.inl hn))
  have h4608 : (e4608 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))))))))))))))))
  have h4675 : (e4675 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))
  have h4747 : (e4747 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn)))))))))
  have h4787 : (e4787 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))
  have h4813 : (e4813 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))
  have h4838 : (e4838 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))
  have h4872 : (e4872 _v) := Classical.byContradiction (fun hn => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hn))))))))))))))))))))))
  have p19575 := n19575 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4139 h4156 h4199 h4260 h4369 h4419 h4434 h4477 h4608 h4675 h4747 h4787 h4813 h4838 h4872
  exact p19575
theorem n19579 (_v : Vars) (_q : Query _v)  : (e19578 _v) := by
  have p19577 := n19577 _v _q 
  have p17009 := n17009 _v _q 
  change (¬ (e4477 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4419 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e91 _v)) at p19577
  rcases p19577 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact (False.elim (hlit p17009))
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
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hlit)))))))))))))))))))))))))
theorem n19580 (_v : Vars) (_q : Query _v) (h4302 : (e4302 _v)) : (e4747 _v) := by
  have p14920 := n14920 _v _q 
  have p16524 := n16524 _v _q h4302
  change (e4754 _v) ∨ (e4747 _v) at p14920
  change (¬ (e4754 _v)) at p16524
  rcases p14920 with hlit | hlit
  · exact (False.elim (p16524 hlit))
  · exact hlit
theorem n19581 (_v : Vars) (_q : Query _v) (h4302 : (e4302 _v)) : (e3946 _v) := by
  have p15201 := n15201 _v _q 
  have p16526 := n16526 _v _q h4302
  change (e3948 _v) ∨ (e3946 _v) at p15201
  change (¬ (e3948 _v)) at p16526
  rcases p15201 with hlit | hlit
  · exact (False.elim (p16526 hlit))
  · exact hlit
theorem n19582 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4302 : (e4302 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e4839 _v) := by
  have p19577 := n19577 _v _q 
  have p17032 := n17032 _v _q h4302 h4419 h4434
  have p17009 := n17009 _v _q 
  have p4998 := n4998 _v _q h3152
  have p5008 := n5008 _v _q h4787
  have p5003 := n5003 _v _q h4199
  have p5006 := n5006 _v _q h4675
  have p4995 := n4995 _v _q h4369
  have p5007 := n5007 _v _q h225
  have p4985 := n4985 _v _q h4156
  have p4987 := n4987 _v _q h4434
  have p5010 := n5010 _v _q h70
  have p4981 := n4981 _v _q h4260
  have p4988 := n4988 _v _q h488
  have p19580 := n19580 _v _q h4302
  have p19581 := n19581 _v _q h4302
  have p4971 := n4971 _v _q h4419
  have p4986 := n4986 _v _q h3105
  have p4983 := n4983 _v _q h4813
  have p4992 := n4992 _v _q h442
  have p4984 := n4984 _v _q h4872
  have p4991 := n4991 _v _q h4608
  have p17034 := n17034 _v _q h4302 h4419 h4434
  have p4994 := n4994 _v _q h3069
  have p5001 := n5001 _v _q h4096
  have p4996 := n4996 _v _q h3937
  have p4999 := n4999 _v _q h91
  change (¬ (e4477 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4419 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e91 _v)) at p19577
  rcases p19577 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact (False.elim (hlit p17009))
  · exact (False.elim (hlit p4995))
  · exact (False.elim (hlit p5003))
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p19581))
  · exact (False.elim (hlit p19580))
  · exact (False.elim (hlit p5007))
  · exact (False.elim (hlit p4985))
  · exact (False.elim (hlit p4987))
  · exact (False.elim (hlit p5010))
  · exact (False.elim (hlit p4981))
  · exact (False.elim (hlit p4988))
  · exact hlit
  · exact (False.elim (hlit p4971))
  · exact (False.elim (hlit p17034))
  · exact (False.elim (hlit p4986))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p4992))
  · exact (False.elim (hlit p4984))
  · exact (False.elim (hlit p4991))
  · exact (False.elim (hlit p17032))
  · exact (False.elim (hlit p4994))
  · exact (False.elim (hlit p5001))
  · exact (False.elim (hlit p4996))
  · exact (False.elim (hlit p4999))
theorem n19583 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4302 : (e4302 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e8301 _v) := by
  have p16285 := n16285 _v _q 
  have p19582 := n19582 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h4096 h4156 h4199 h4260 h4302 h4369 h4419 h4434 h4608 h4675 h4787 h4813 h4872
  change (e8301 _v) ∨ (e4838 _v) at p16285
  change (¬ (e4838 _v)) at p19582
  rcases p16285 with hlit | hlit
  · exact hlit
  · exact (False.elim (p19582 hlit))
theorem n19584 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h6784 : (e6784 _v)) : (e4420 _v) := by
  have p19577 := n19577 _v _q 
  have p16549 := n16549 _v _q h6784
  have p17009 := n17009 _v _q 
  have p4998 := n4998 _v _q h3152
  have p5008 := n5008 _v _q h4787
  have p5003 := n5003 _v _q h4199
  have p5006 := n5006 _v _q h4675
  have p4995 := n4995 _v _q h4369
  have p5007 := n5007 _v _q h225
  have p4985 := n4985 _v _q h4156
  have p4987 := n4987 _v _q h4434
  have p5010 := n5010 _v _q h70
  have p4981 := n4981 _v _q h4260
  have p4988 := n4988 _v _q h488
  have p17061 := n17061 _v _q h4747
  have p17056 := n17056 _v _q h3946
  have p4989 := n4989 _v _q h4838
  have p4986 := n4986 _v _q h3105
  have p4983 := n4983 _v _q h4813
  have p4992 := n4992 _v _q h442
  have p4984 := n4984 _v _q h4872
  have p4991 := n4991 _v _q h4608
  have p253 := n253 _v _q h191
  have p4994 := n4994 _v _q h3069
  have p5001 := n5001 _v _q h4096
  have p4996 := n4996 _v _q h3937
  have p4999 := n4999 _v _q h91
  change (¬ (e4477 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4419 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e91 _v)) at p19577
  rcases p19577 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact (False.elim (hlit p17009))
  · exact (False.elim (hlit p4995))
  · exact (False.elim (hlit p5003))
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p17056))
  · exact (False.elim (hlit p17061))
  · exact (False.elim (hlit p5007))
  · exact (False.elim (hlit p4985))
  · exact (False.elim (hlit p4987))
  · exact (False.elim (hlit p5010))
  · exact (False.elim (hlit p4981))
  · exact (False.elim (hlit p4988))
  · exact (False.elim (hlit p4989))
  · exact hlit
  · exact (False.elim (hlit p16549))
  · exact (False.elim (hlit p4986))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p4992))
  · exact (False.elim (hlit p4984))
  · exact (False.elim (hlit p4991))
  · exact (False.elim (hlit p253))
  · exact (False.elim (hlit p4994))
  · exact (False.elim (hlit p5001))
  · exact (False.elim (hlit p4996))
  · exact (False.elim (hlit p4999))
theorem n19585 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4838 : (e4838 _v)) (h4872 : (e4872 _v)) (h6784 : (e6784 _v)) : (e7921 _v) := by
  have p16347 := n16347 _v _q 
  have p19584 := n19584 _v _q h70 h91 h191 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4260 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4838 h4872 h6784
  change (e7921 _v) ∨ (e4419 _v) at p16347
  change (¬ (e4419 _v)) at p19584
  rcases p16347 with hlit | hlit
  · exact hlit
  · exact (False.elim (p19584 hlit))
theorem n19586 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h6531 : (e6531 _v)) : (e4420 _v) := by
  have p19577 := n19577 _v _q 
  have p16557 := n16557 _v _q h6531
  have p17009 := n17009 _v _q 
  have p4998 := n4998 _v _q h3152
  have p5008 := n5008 _v _q h4787
  have p5003 := n5003 _v _q h4199
  have p5006 := n5006 _v _q h4675
  have p4995 := n4995 _v _q h4369
  have p5007 := n5007 _v _q h225
  have p4985 := n4985 _v _q h4156
  have p4987 := n4987 _v _q h4434
  have p5010 := n5010 _v _q h70
  have p4981 := n4981 _v _q h4260
  have p4988 := n4988 _v _q h488
  have p17061 := n17061 _v _q h4747
  have p17056 := n17056 _v _q h3946
  have p16560 := n16560 _v _q h6531
  have p4986 := n4986 _v _q h3105
  have p4983 := n4983 _v _q h4813
  have p4992 := n4992 _v _q h442
  have p4984 := n4984 _v _q h4872
  have p4991 := n4991 _v _q h4608
  have p16563 := n16563 _v _q h6531
  have p4994 := n4994 _v _q h3069
  have p5001 := n5001 _v _q h4096
  have p4996 := n4996 _v _q h3937
  have p4999 := n4999 _v _q h91
  change (¬ (e4477 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4419 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e91 _v)) at p19577
  rcases p19577 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact (False.elim (hlit p17009))
  · exact (False.elim (hlit p4995))
  · exact (False.elim (hlit p5003))
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p17056))
  · exact (False.elim (hlit p17061))
  · exact (False.elim (hlit p5007))
  · exact (False.elim (hlit p4985))
  · exact (False.elim (hlit p4987))
  · exact (False.elim (hlit p5010))
  · exact (False.elim (hlit p4981))
  · exact (False.elim (hlit p4988))
  · exact (False.elim (hlit p16560))
  · exact hlit
  · exact (False.elim (hlit p16563))
  · exact (False.elim (hlit p4986))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p4992))
  · exact (False.elim (hlit p4984))
  · exact (False.elim (hlit p4991))
  · exact (False.elim (hlit p16557))
  · exact (False.elim (hlit p4994))
  · exact (False.elim (hlit p5001))
  · exact (False.elim (hlit p4996))
  · exact (False.elim (hlit p4999))
theorem n19587 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) (h6531 : (e6531 _v)) : (e7921 _v) := by
  have p16347 := n16347 _v _q 
  have p19586 := n19586 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4260 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872 h6531
  change (e7921 _v) ∨ (e4419 _v) at p16347
  change (¬ (e4419 _v)) at p19586
  rcases p16347 with hlit | hlit
  · exact hlit
  · exact (False.elim (p19586 hlit))
theorem n19588 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2132 : (e2132 _v)) (h2529 : (e2529 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e4420 _v) := by
  have p19577 := n19577 _v _q 
  have p16850 := n16850 _v _q h2132
  have p17009 := n17009 _v _q 
  have p4998 := n4998 _v _q h3152
  have p5008 := n5008 _v _q h4787
  have p5003 := n5003 _v _q h4199
  have p5006 := n5006 _v _q h4675
  have p4995 := n4995 _v _q h4369
  have p5007 := n5007 _v _q h225
  have p4985 := n4985 _v _q h4156
  have p4987 := n4987 _v _q h4434
  have p5010 := n5010 _v _q h70
  have p4981 := n4981 _v _q h4260
  have p4988 := n4988 _v _q h488
  have p17061 := n17061 _v _q h4747
  have p17056 := n17056 _v _q h3946
  have p16572 := n16572 _v _q h2529
  have p4986 := n4986 _v _q h3105
  have p4983 := n4983 _v _q h4813
  have p4992 := n4992 _v _q h442
  have p4984 := n4984 _v _q h4872
  have p4991 := n4991 _v _q h4608
  have p253 := n253 _v _q h191
  have p4994 := n4994 _v _q h3069
  have p5001 := n5001 _v _q h4096
  have p4996 := n4996 _v _q h3937
  have p4999 := n4999 _v _q h91
  change (¬ (e4477 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4419 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e91 _v)) at p19577
  rcases p19577 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact (False.elim (hlit p17009))
  · exact (False.elim (hlit p4995))
  · exact (False.elim (hlit p5003))
  · exact (False.elim (hlit p4998))
  · exact (False.elim (hlit p5008))
  · exact (False.elim (hlit p5006))
  · exact (False.elim (hlit p17056))
  · exact (False.elim (hlit p17061))
  · exact (False.elim (hlit p5007))
  · exact (False.elim (hlit p4985))
  · exact (False.elim (hlit p4987))
  · exact (False.elim (hlit p5010))
  · exact (False.elim (hlit p4981))
  · exact (False.elim (hlit p4988))
  · exact (False.elim (hlit p16572))
  · exact hlit
  · exact (False.elim (hlit p16850))
  · exact (False.elim (hlit p4986))
  · exact (False.elim (hlit p4983))
  · exact (False.elim (hlit p4992))
  · exact (False.elim (hlit p4984))
  · exact (False.elim (hlit p4991))
  · exact (False.elim (hlit p253))
  · exact (False.elim (hlit p4994))
  · exact (False.elim (hlit p5001))
  · exact (False.elim (hlit p4996))
  · exact (False.elim (hlit p4999))
theorem n19589 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h191 : (e191 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h2132 : (e2132 _v)) (h2529 : (e2529 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h3946 : (e3946 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4369 : (e4369 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4747 : (e4747 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e7921 _v) := by
  have p16347 := n16347 _v _q 
  have p19588 := n19588 _v _q h70 h91 h191 h225 h442 h488 h2132 h2529 h3069 h3105 h3152 h3937 h3946 h4096 h4156 h4199 h4260 h4369 h4434 h4608 h4675 h4747 h4787 h4813 h4872
  change (e7921 _v) ∨ (e4419 _v) at p16347
  change (¬ (e4419 _v)) at p19588
  rcases p16347 with hlit | hlit
  · exact hlit
  · exact (False.elim (p19588 hlit))
theorem n19590 (_v : Vars) (_q : Query _v) (h6684 : (e6684 _v)) : (e7489 _v) := by
  have p19579 := n19579 _v _q 
  have p17979 := n17979 _v _q h6684
  have p17980 := n17980 _v _q h6684
  have p17294 := n17294 _v _q 
  have p17874 := n17874 _v _q 
  have p17981 := n17981 _v _q h6684
  have p17982 := n17982 _v _q h6684
  have p17983 := n17983 _v _q h6684
  have p17984 := n17984 _v _q h6684
  have p17985 := n17985 _v _q h6684
  have p17986 := n17986 _v _q h6684
  have p17987 := n17987 _v _q h6684
  have p17988 := n17988 _v _q h6684
  have p17989 := n17989 _v _q h6684
  have p17990 := n17990 _v _q h6684
  have p17991 := n17991 _v _q h6684
  have p17992 := n17992 _v _q h6684
  have p17758 := n17758 _v _q 
  have p17993 := n17993 _v _q h6684
  have p17994 := n17994 _v _q h6684
  have p17995 := n17995 _v _q h6684
  have p17996 := n17996 _v _q h6684
  have p16838 := n16838 _v _q h6684
  have p15588 := n15588 _v _q h6684
  have p17997 := n17997 _v _q h6684
  have p17998 := n17998 _v _q h6684
  have p17999 := n17999 _v _q h6684
  change (¬ (e4369 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e4838 _v)) ∨ (¬ (e4419 _v)) ∨ (¬ (e4139 _v)) ∨ (¬ (e3105 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e191 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e91 _v)) at p19579
  rcases p19579 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact (False.elim (hlit p17980))
  · exact (False.elim (hlit p17984))
  · exact (False.elim (hlit p17990))
  · exact (False.elim (hlit p17983))
  · exact (False.elim (hlit p17982))
  · exact (False.elim (hlit p17294))
  · exact (False.elim (hlit p17874))
  · exact (False.elim (hlit p17985))
  · exact (False.elim (hlit p17979))
  · exact (False.elim (hlit p17986))
  · exact (False.elim (hlit p17987))
  · exact (False.elim (hlit p17981))
  · exact (False.elim (hlit p17989))
  · exact (False.elim (hlit p17992))
  · exact (False.elim (hlit p17991))
  · exact (False.elim (hlit p17988))
  · exact (False.elim (hlit p17758))
  · exact (False.elim (hlit p17993))
  · exact (False.elim (hlit p17994))
  · exact (False.elim (hlit p17995))
  · exact (False.elim (hlit p17996))
  · exact (False.elim (hlit p16838))
  · exact (False.elim (hlit p15588))
  · exact (False.elim (hlit p17997))
  · exact (False.elim (hlit p17998))
  · exact (False.elim (hlit p17999))
theorem n19591 (_v : Vars) (_q : Query _v)  : (e2598 _v) := by
  by_contra hc
  change ¬ (e2598 _v) at hc
  have h6684 : (e6684 _v) := (fun hn => hc hn)
  have p19590 := n19590 _v _q h6684
  exact p19590
theorem n19592 (_v : Vars) (_q : Query _v)  : (e4067 _v) := by
  have p14703 := n14703 _v _q 
  have p19591 := n19591 _v _q 
  change (¬ (e2598 _v)) ∨ (¬ (e4066 _v)) at p14703
  rcases p14703 with hlit | hlit
  · exact (False.elim (hlit p19591))
  · exact hlit
theorem n19593 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) (h91 : (e91 _v)) (h225 : (e225 _v)) (h442 : (e442 _v)) (h488 : (e488 _v)) (h3069 : (e3069 _v)) (h3105 : (e3105 _v)) (h3152 : (e3152 _v)) (h3937 : (e3937 _v)) (h4096 : (e4096 _v)) (h4156 : (e4156 _v)) (h4199 : (e4199 _v)) (h4260 : (e4260 _v)) (h4302 : (e4302 _v)) (h4369 : (e4369 _v)) (h4419 : (e4419 _v)) (h4434 : (e4434 _v)) (h4608 : (e4608 _v)) (h4675 : (e4675 _v)) (h4787 : (e4787 _v)) (h4813 : (e4813 _v)) (h4872 : (e4872 _v)) : (e8310 _v) := by
  have p14906 := n14906 _v _q 
  have p19583 := n19583 _v _q h70 h91 h225 h442 h488 h3069 h3105 h3152 h3937 h4096 h4156 h4199 h4260 h4302 h4369 h4419 h4434 h4608 h4675 h4787 h4813 h4872
  change (¬ (e2529 _v)) ∨ (¬ (e8301 _v)) at p14906
  rcases p14906 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p19583))
end
end Assembly
