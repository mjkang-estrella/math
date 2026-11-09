import Dag230
import generated.th_lemma_30
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n20423 (_v : Vars) (_q : Query _v) (h496 : (e496 _v)) : (e4447 _v) := by
  have p14688 := n14688 _v _q 
  have p20422 := n20422 _v _q h496
  change (¬ (e2061 _v)) ∨ (¬ (e4446 _v)) at p14688
  rcases p14688 with hlit | hlit
  · exact (False.elim (hlit p20422))
  · exact hlit
theorem n20424 (_v : Vars) (_q : Query _v) (h496 : (e496 _v)) : (e4439 _v) := by
  have p14925 := n14925 _v _q 
  have p20423 := n20423 _v _q h496
  change (e4446 _v) ∨ (e4439 _v) at p14925
  change (¬ (e4446 _v)) at p20423
  rcases p14925 with hlit | hlit
  · exact (False.elim (p20423 hlit))
  · exact hlit
theorem n20425 (_v : Vars) (_q : Query _v)  : (e5370 _v) := by
  have p14735 := n14735 _v _q 
  have p20397 := n20397 _v _q 
  change (¬ (e436 _v)) ∨ (¬ (e5360 _v)) at p14735
  rcases p14735 with hlit | hlit
  · exact (False.elim (hlit p20397))
  · exact hlit
theorem n20426 (_v : Vars) (_q : Query _v)  : (e442 _v) := by
  have p16149 := n16149 _v _q 
  have p20425 := n20425 _v _q 
  change (e5360 _v) ∨ (e442 _v) at p16149
  change (¬ (e5360 _v)) at p20425
  rcases p16149 with hlit | hlit
  · exact (False.elim (p20425 hlit))
  · exact hlit
theorem n20427 (_v : Vars) (_q : Query _v)  : (e8559 _v) := by
  simp only [e440, e441, e442, e443, e5360, e8559] at *
  tauto
theorem n20428 (_v : Vars) (_q : Query _v)  : (e440 _v) := by
  have p20427 := n20427 _v _q 
  have p20425 := n20425 _v _q 
  change (e5360 _v) ∨ (e440 _v) at p20427
  change (¬ (e5360 _v)) at p20425
  rcases p20427 with hlit | hlit
  · exact (False.elim (p20425 hlit))
  · exact hlit
theorem n20429 (_v : Vars) (_q : Query _v) (h496 : (e496 _v)) : (e2585 _v) := by
  have p12900 := n12900 _v _q 
  have p14137 := n14137 _v _q h496
  change (e2585 _v) ∨ (e196 _v) at p12900
  change (¬ (e196 _v)) at p14137
  rcases p12900 with hlit | hlit
  · exact hlit
  · exact (False.elim (p14137 hlit))
theorem n20430 (_v : Vars) (_q : Query _v) (h496 : (e496 _v)) : (e4314 _v) := by
  have p14704 := n14704 _v _q 
  have p20429 := n20429 _v _q h496
  change (¬ (e2585 _v)) ∨ (¬ (e4313 _v)) at p14704
  rcases p14704 with hlit | hlit
  · exact (False.elim (hlit p20429))
  · exact hlit
theorem n20431 (_v : Vars) (_q : Query _v) (h496 : (e496 _v)) : (e4306 _v) := by
  have p14984 := n14984 _v _q 
  have p20430 := n20430 _v _q h496
  change (e4313 _v) ∨ (e4306 _v) at p14984
  change (¬ (e4313 _v)) at p20430
  rcases p14984 with hlit | hlit
  · exact (False.elim (p20430 hlit))
  · exact hlit
theorem n20432 (_v : Vars) (_q : Query _v) (h496 : (e496 _v)) : (e4459 _v) := by
  have p16784 := n16784 _v _q 
  have p15801 := n15801 _v _q h496
  change (e4459 _v) ∨ (¬ (e7749 _v)) at p16784
  rcases p16784 with hlit | hlit
  · exact hlit
  · exact (False.elim (hlit p15801))
theorem n20433 (_v : Vars) (_q : Query _v) (h496 : (e496 _v)) : (e4653 _v) := by
  have p15168 := n15168 _v _q 
  have p15802 := n15802 _v _q h496
  change (e4660 _v) ∨ (e4653 _v) at p15168
  change (¬ (e4660 _v)) at p15802
  rcases p15168 with hlit | hlit
  · exact (False.elim (p15802 hlit))
  · exact hlit
theorem n20434 (_v : Vars) (_q : Query _v) (h496 : (e496 _v)) : (e4731 _v) := by
  have p14698 := n14698 _v _q 
  have p14726 := n14726 _v _q h496
  change (¬ (e2254 _v)) ∨ (¬ (e4730 _v)) at p14698
  rcases p14698 with hlit | hlit
  · exact (False.elim (hlit p14726))
  · exact hlit
theorem n20435 (_v : Vars) (_q : Query _v) (h496 : (e496 _v)) : (e4724 _v) := by
  have p15518 := n15518 _v _q 
  have p20434 := n20434 _v _q h496
  change (e4730 _v) ∨ (e4724 _v) at p15518
  change (¬ (e4730 _v)) at p20434
  rcases p15518 with hlit | hlit
  · exact (False.elim (p20434 hlit))
  · exact hlit
theorem n20436 (_v : Vars) (_q : Query _v) (h496 : (e496 _v)) : (e7489 _v) := by
  have p18101 := n18101 _v _q 
  have p20400 := n20400 _v _q h496
  have p15799 := n15799 _v _q h496
  have p20397 := n20397 _v _q 
  have p8144 := n8144 _v _q h496
  have p20431 := n20431 _v _q h496
  have p20432 := n20432 _v _q h496
  have p20433 := n20433 _v _q h496
  have p19610 := n19610 _v _q 
  have p20403 := n20403 _v _q h496
  have p20406 := n20406 _v _q h496
  have p15805 := n15805 _v _q h496
  have p20096 := n20096 _v _q 
  have p20435 := n20435 _v _q h496
  have p20409 := n20409 _v _q h496
  have p20412 := n20412 _v _q h496
  have p15809 := n15809 _v _q h496
  have p20415 := n20415 _v _q h496
  have p15812 := n15812 _v _q h496
  have p20418 := n20418 _v _q h496
  have p20421 := n20421 _v _q h496
  have p20274 := n20274 _v _q 
  have p20424 := n20424 _v _q h496
  have p20126 := n20126 _v _q 
  have p19630 := n19630 _v _q 
  change (¬ (e496 _v)) ∨ (¬ (e3976 _v)) ∨ (¬ (e4373 _v)) ∨ (¬ (e4306 _v)) ∨ (¬ (e3158 _v)) ∨ (¬ (e4459 _v)) ∨ (¬ (e4653 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e3919 _v)) ∨ (¬ (e51 _v)) ∨ (¬ (e3133 _v)) ∨ (¬ (e4491 _v)) ∨ (¬ (e4724 _v)) ∨ (¬ (e4567 _v)) ∨ (¬ (e4791 _v)) ∨ (¬ (e4398 _v)) ∨ (¬ (e4679 _v)) ∨ (¬ (e4817 _v)) ∨ (¬ (e4264 _v)) ∨ (¬ (e4101 _v)) ∨ (¬ (e4903 _v)) ∨ (¬ (e4439 _v)) ∨ (¬ (e436 _v)) ∨ (e2722 _v) at p18101
  change (¬ (e2722 _v)) at p19630
  rcases p18101 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact (False.elim (hlit p8144))
  · exact (False.elim (hlit p20126))
  · exact (False.elim (hlit p15799))
  · exact (False.elim (hlit p20431))
  · exact (False.elim (hlit p20400))
  · exact (False.elim (hlit p20432))
  · exact (False.elim (hlit p20433))
  · exact (False.elim (hlit p19610))
  · exact (False.elim (hlit p20403))
  · exact (False.elim (hlit p20406))
  · exact (False.elim (hlit p15805))
  · exact (False.elim (hlit p20096))
  · exact (False.elim (hlit p20435))
  · exact (False.elim (hlit p20409))
  · exact (False.elim (hlit p20412))
  · exact (False.elim (hlit p15809))
  · exact (False.elim (hlit p20415))
  · exact (False.elim (hlit p15812))
  · exact (False.elim (hlit p20418))
  · exact (False.elim (hlit p20421))
  · exact (False.elim (hlit p20274))
  · exact (False.elim (hlit p20424))
  · exact (False.elim (hlit p20397))
  · exact (False.elim (p19630 hlit))
theorem n20437 (_v : Vars) (_q : Query _v)  : (e6720 _v) := by
  by_contra hc
  change ¬ (¬ (e496 _v)) at hc
  have h496 : (e496 _v) := Classical.byContradiction (fun hn => hc hn)
  have p20436 := n20436 _v _q h496
  exact p20436
theorem n20438 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e2179 _v) := by
  have p11374 := n11374 _v _q h251
  have p5391 := n5391 _v _q 
  have p5255 := n5255 _v _q 
  have p20437 := n20437 _v _q 
  have p5257 := n5257 _v _q 
  exact FloorCertificate.node_20438 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p11374 p5391 p5255 p20437 p5257
theorem n20439 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e4616 _v) := by
  have p14684 := n14684 _v _q 
  have p20438 := n20438 _v _q h251
  change (¬ (e2179 _v)) ∨ (¬ (e3162 _v)) at p14684
  rcases p14684 with hlit | hlit
  · exact (False.elim (hlit p20438))
  · exact hlit
theorem n20440 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e2061 _v) := by
  have p5255 := n5255 _v _q 
  have p11374 := n11374 _v _q h251
  have p5391 := n5391 _v _q 
  have p20437 := n20437 _v _q 
  have p5257 := n5257 _v _q 
  exact FloorCertificate.node_20440 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p5255 p11374 p5391 p20437 p5257
theorem n20441 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e4447 _v) := by
  have p14688 := n14688 _v _q 
  have p20440 := n20440 _v _q h251
  change (¬ (e2061 _v)) ∨ (¬ (e4446 _v)) at p14688
  rcases p14688 with hlit | hlit
  · exact (False.elim (hlit p20440))
  · exact hlit
theorem n20442 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e2402 _v) := by
  have p11374 := n11374 _v _q h251
  have p5255 := n5255 _v _q 
  have p20437 := n20437 _v _q 
  have p5257 := n5257 _v _q 
  exact FloorCertificate.node_20442 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p11374 p5255 p20437 p5257
theorem n20443 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e3929 _v) := by
  have p14484 := n14484 _v _q 
  have p20442 := n20442 _v _q h251
  change (¬ (e2402 _v)) ∨ (¬ (e3923 _v)) at p14484
  rcases p14484 with hlit | hlit
  · exact (False.elim (hlit p20442))
  · exact hlit
theorem n20444 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e2733 _v) := by
  have p11374 := n11374 _v _q h251
  have p5255 := n5255 _v _q 
  have p258 := n258 _v _q 
  have p5391 := n5391 _v _q 
  have p20437 := n20437 _v _q 
  have p5257 := n5257 _v _q 
  exact FloorCertificate.node_20444 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p11374 p5255 p258 p5391 p20437 p5257
theorem n20445 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e4109 _v) := by
  have p14689 := n14689 _v _q 
  have p20444 := n20444 _v _q h251
  change (¬ (e2733 _v)) ∨ (¬ (e4108 _v)) at p14689
  rcases p14689 with hlit | hlit
  · exact (False.elim (hlit p20444))
  · exact hlit
theorem n20446 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e1995 _v) := by
  have p5257 := n5257 _v _q 
  have p11374 := n11374 _v _q h251
  have p5255 := n5255 _v _q 
  have p5391 := n5391 _v _q 
  have p20437 := n20437 _v _q 
  exact FloorCertificate.node_20446 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p5257 p11374 p5255 p5391 p20437
theorem n20447 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e4575 _v) := by
  have p14696 := n14696 _v _q 
  have p20446 := n20446 _v _q h251
  change (¬ (e1995 _v)) ∨ (¬ (e4574 _v)) at p14696
  rcases p14696 with hlit | hlit
  · exact (False.elim (hlit p20446))
  · exact hlit
theorem n20448 (_v : Vars) (_q : Query _v)  : (e6830 _v) := by
  have p14629 := n14629 _v _q 
  have p20437 := n20437 _v _q 
  change (e496 _v) ∨ (¬ (e6829 _v)) at p14629
  change (¬ (e496 _v)) at p20437
  rcases p14629 with hlit | hlit
  · exact (False.elim (p20437 hlit))
  · exact hlit
theorem n20449 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e2585 _v) := by
  have p11374 := n11374 _v _q h251
  have p5257 := n5257 _v _q 
  have p5255 := n5255 _v _q 
  have p258 := n258 _v _q 
  have p5391 := n5391 _v _q 
  have p20437 := n20437 _v _q 
  exact FloorCertificate.node_20449 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p11374 p5257 p5255 p258 p5391 p20437
theorem n20450 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e4314 _v) := by
  have p14704 := n14704 _v _q 
  have p20449 := n20449 _v _q h251
  change (¬ (e2585 _v)) ∨ (¬ (e4313 _v)) at p14704
  rcases p14704 with hlit | hlit
  · exact (False.elim (hlit p20449))
  · exact hlit
theorem n20451 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e48 _v) := by
  have p5257 := n5257 _v _q 
  have p11374 := n11374 _v _q h251
  have p258 := n258 _v _q 
  have p5255 := n5255 _v _q 
  have p5391 := n5391 _v _q 
  have p20437 := n20437 _v _q 
  exact FloorCertificate.node_20451 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p5257 p11374 p258 p5255 p5391 p20437
theorem n20452 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e60 _v) := by
  have p14152 := n14152 _v _q 
  have p20451 := n20451 _v _q h251
  change (¬ (e48 _v)) ∨ (¬ (e59 _v)) at p14152
  rcases p14152 with hlit | hlit
  · exact (False.elim (hlit p20451))
  · exact hlit
theorem n20453 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e2364 _v) := by
  have p20437 := n20437 _v _q 
  have p5255 := n5255 _v _q 
  have p258 := n258 _v _q 
  have p11374 := n11374 _v _q h251
  have p5391 := n5391 _v _q 
  have p5257 := n5257 _v _q 
  exact FloorCertificate.node_20453 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p20437 p5255 p258 p11374 p5391 p5257
theorem n20454 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e4661 _v) := by
  have p14686 := n14686 _v _q 
  have p20453 := n20453 _v _q h251
  change (¬ (e2364 _v)) ∨ (¬ (e4660 _v)) at p14686
  rcases p14686 with hlit | hlit
  · exact (False.elim (hlit p20453))
  · exact hlit
theorem n20455 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e2061 _v) := by
  have p5257 := n5257 _v _q 
  have p5255 := n5255 _v _q 
  have p11374 := n11374 _v _q h251
  have p5391 := n5391 _v _q 
  have p20437 := n20437 _v _q 
  exact FloorCertificate.node_20455 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p5257 p5255 p11374 p5391 p20437
theorem n20456 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e4447 _v) := by
  have p14688 := n14688 _v _q 
  have p20455 := n20455 _v _q h251
  change (¬ (e2061 _v)) ∨ (¬ (e4446 _v)) at p14688
  rcases p14688 with hlit | hlit
  · exact (False.elim (hlit p20455))
  · exact hlit
theorem n20457 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e2179 _v) := by
  have p11374 := n11374 _v _q h251
  have p5391 := n5391 _v _q 
  have p20437 := n20437 _v _q 
  have p5255 := n5255 _v _q 
  have p5257 := n5257 _v _q 
  exact FloorCertificate.node_20457 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p11374 p5391 p20437 p5255 p5257
theorem n20458 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e4616 _v) := by
  have p14684 := n14684 _v _q 
  have p20457 := n20457 _v _q h251
  change (¬ (e2179 _v)) ∨ (¬ (e3162 _v)) at p14684
  rcases p14684 with hlit | hlit
  · exact (False.elim (hlit p20457))
  · exact hlit
theorem n20459 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e2402 _v) := by
  have p11374 := n11374 _v _q h251
  have p5257 := n5257 _v _q 
  have p20437 := n20437 _v _q 
  have p5255 := n5255 _v _q 
  exact FloorCertificate.node_20459 (e2 _v) (e7 _v) (e9 _v) (e17 _v) (e45 _v) (e110 _v) p11374 p5257 p20437 p5255
theorem n20460 (_v : Vars) (_q : Query _v) (h251 : (e251 _v)) : (e3929 _v) := by
  have p14484 := n14484 _v _q 
  have p20459 := n20459 _v _q h251
  change (¬ (e2402 _v)) ∨ (¬ (e3923 _v)) at p14484
  rcases p14484 with hlit | hlit
  · exact (False.elim (hlit p20459))
  · exact hlit
theorem n20461 (_v : Vars) (_q : Query _v)  : (e3069 _v) := by
  have p14878 := n14878 _v _q 
  have p20448 := n20448 _v _q 
  change (e6829 _v) ∨ (e3069 _v) at p14878
  change (¬ (e6829 _v)) at p20448
  rcases p14878 with hlit | hlit
  · exact (False.elim (p20448 hlit))
  · exact hlit
theorem n20462 (_v : Vars) (_q : Query _v)  : (e8566 _v) := by
  simp only [e3069, e3071, e3074, e3075, e6829, e8566] at *
  tauto
theorem n20463 (_v : Vars) (_q : Query _v)  : (e3071 _v) := by
  have p20462 := n20462 _v _q 
  have p20448 := n20448 _v _q 
  change (e6829 _v) ∨ (e3071 _v) at p20462
  change (¬ (e6829 _v)) at p20448
  rcases p20462 with hlit | hlit
  · exact (False.elim (p20448 hlit))
  · exact hlit
theorem n20464 (_v : Vars) (_q : Query _v) (h6636 : (e6636 _v)) : (e7489 _v) := by
  have p19832 := n19832 _v _q 
  have p20296 := n20296 _v _q h6636
  have p20297 := n20297 _v _q h6636
  have p17294 := n17294 _v _q 
  have p17874 := n17874 _v _q 
  have p19610 := n19610 _v _q 
  have p11031 := n11031 _v _q h6636
  have p15823 := n15823 _v _q h6636
  have p15826 := n15826 _v _q h6636
  have p16855 := n16855 _v _q h6636
  have p20461 := n20461 _v _q 
  have p20426 := n20426 _v _q 
  have p16602 := n16602 _v _q h6636
  have p16634 := n16634 _v _q h6636
  have p19665 := n19665 _v _q 
  have p16635 := n16635 _v _q h6636
  have p20298 := n20298 _v _q h6636
  have p16636 := n16636 _v _q h6636
  have p20299 := n20299 _v _q h6636
  have p16853 := n16853 _v _q h6636
  have p16637 := n16637 _v _q h6636
  have p16638 := n16638 _v _q h6636
  have p20300 := n20300 _v _q h6636
  have p16639 := n16639 _v _q h6636
  have p17758 := n17758 _v _q 
  change (e2482 _v) ∨ (¬ (e4872 _v)) ∨ (¬ (e4608 _v)) ∨ (¬ (e3069 _v)) ∨ (¬ (e4260 _v)) ∨ (¬ (e4096 _v)) ∨ (¬ (e91 _v)) ∨ (¬ (e70 _v)) ∨ (¬ (e4199 _v)) ∨ (¬ (e225 _v)) ∨ (¬ (e442 _v)) ∨ (¬ (e3937 _v)) ∨ (¬ (e4434 _v)) ∨ (¬ (e4059 _v)) ∨ (¬ (e4813 _v)) ∨ (¬ (e4369 _v)) ∨ (¬ (e3152 _v)) ∨ (¬ (e4787 _v)) ∨ (¬ (e4675 _v)) ∨ (¬ (e3946 _v)) ∨ (¬ (e4747 _v)) ∨ (¬ (e4156 _v)) ∨ (¬ (e488 _v)) ∨ (¬ (e3105 _v)) at p19832
  change (¬ (e2482 _v)) at p11031
  rcases p19832 with hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit | hlit
  · exact (False.elim (p11031 hlit))
  · exact (False.elim (hlit p19665))
  · exact (False.elim (hlit p16637))
  · exact (False.elim (hlit p20461))
  · exact (False.elim (hlit p15826))
  · exact (False.elim (hlit p15823))
  · exact (False.elim (hlit p16855))
  · exact (False.elim (hlit p16635))
  · exact (False.elim (hlit p16602))
  · exact (False.elim (hlit p16853))
  · exact (False.elim (hlit p20426))
  · exact (False.elim (hlit p20296))
  · exact (False.elim (hlit p16634))
  · exact (False.elim (hlit p19610))
  · exact (False.elim (hlit p20297))
  · exact (False.elim (hlit p20298))
  · exact (False.elim (hlit p16636))
  · exact (False.elim (hlit p20299))
  · exact (False.elim (hlit p16639))
  · exact (False.elim (hlit p17294))
  · exact (False.elim (hlit p17874))
  · exact (False.elim (hlit p16638))
  · exact (False.elim (hlit p20300))
  · exact (False.elim (hlit p17758))
theorem n20465 (_v : Vars) (_q : Query _v)  : (e2482 _v) := by
  by_contra hc
  change ¬ (e2482 _v) at hc
  have h6636 : (e6636 _v) := (fun hn => hc hn)
  have p20464 := n20464 _v _q h6636
  exact p20464
theorem n20466 (_v : Vars) (_q : Query _v)  : (e4405 _v) := by
  have p14702 := n14702 _v _q 
  have p20465 := n20465 _v _q 
  change (¬ (e2482 _v)) ∨ (¬ (e4404 _v)) at p14702
  rcases p14702 with hlit | hlit
  · exact (False.elim (hlit p20465))
  · exact hlit
theorem n20467 (_v : Vars) (_q : Query _v)  : (e4398 _v) := by
  have p14976 := n14976 _v _q 
  have p20466 := n20466 _v _q 
  change (e4404 _v) ∨ (e4398 _v) at p14976
  change (¬ (e4404 _v)) at p20466
  rcases p14976 with hlit | hlit
  · exact (False.elim (p20466 hlit))
  · exact hlit
end
end Assembly
