import NReplay046
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_50548 : CNF.NClause := [(82,false),(74,true),(37,false),(6,true)]
theorem der_50548 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50548 :=
  CNF.rup_sound cl_50548 [cl_49707,cl_50547] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49707 v h) (hints_cons _ _ _ (der_50547 v h) (by intro d hd; cases hd)))
def cl_50549 : CNF.NClause := [(70,false),(66,true),(37,false),(6,true)]
theorem der_50549 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50549 :=
  CNF.rup_sound cl_50549 [cl_49709,cl_43014] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49709 v h) (hints_cons _ _ _ (der_43014 v h) (by intro d hd; cases hd)))
def cl_50550 : CNF.NClause := [(37,false),(66,false),(82,false),(6,true)]
theorem der_50550 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50550 :=
  CNF.rup_sound cl_50550 [cl_49710,cl_50548] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49710 v h) (hints_cons _ _ _ (der_50548 v h) (by intro d hd; cases hd)))
def cl_50551 : CNF.NClause := [(65,false),(73,true),(49,false),(18,true)]
theorem der_50551 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50551 :=
  CNF.rup_sound cl_50551 [cl_49718,cl_49719] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49718 v h) (hints_cons _ _ _ (der_49719 v h) (by intro d hd; cases hd)))
def cl_50554 : CNF.NClause := [(6,false),(2,true),(74,true),(19,true),(10,false)]
theorem der_50554 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50554 :=
  CNF.rup_sound cl_50554 [cl_23529,cl_45005] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23529 v h) (hints_cons _ _ _ (der_45005 v h) (by intro d hd; cases hd)))
def cl_50559 : CNF.NClause := [(29,false),(16,true),(12,true),(68,true),(4,false)]
theorem der_50559 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50559 :=
  CNF.rup_sound cl_50559 [cl_23554,cl_42497] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23554 v h) (hints_cons _ _ _ (der_42497 v h) (by intro d hd; cases hd)))
def cl_50563 : CNF.NClause := [(68,true),(66,false),(16,true),(47,false),(89,false)]
theorem der_50563 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50563 :=
  CNF.rup_sound cl_50563 [cl_32029,cl_32026] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32029 v h) (hints_cons _ _ _ (der_32026 v h) (by intro d hd; cases hd)))
def cl_50565 : CNF.NClause := [(68,true),(16,true),(47,false),(77,false),(66,false)]
theorem der_50565 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50565 :=
  CNF.rup_sound cl_50565 [cl_32034,cl_50563] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32034 v h) (hints_cons _ _ _ (der_50563 v h) (by intro d hd; cases hd)))
def cl_50566 : CNF.NClause := [(68,true),(66,false),(75,false),(16,true),(47,false)]
theorem der_50566 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50566 :=
  CNF.rup_sound cl_50566 [cl_32035,cl_50565] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32035 v h) (hints_cons _ _ _ (der_50565 v h) (by intro d hd; cases hd)))
def cl_50567 : CNF.NClause := [(66,false),(68,true),(16,true),(47,false),(75,true)]
theorem der_50567 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50567 :=
  CNF.rup_sound cl_50567 [cl_32036,cl_50565] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32036 v h) (hints_cons _ _ _ (der_50565 v h) (by intro d hd; cases hd)))
def cl_50568 : CNF.NClause := [(8,true),(28,true),(22,true),(11,true),(90,false)]
theorem der_50568 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50568 :=
  CNF.rup_sound cl_50568 [cl_15372,cl_45805] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15372 v h) (hints_cons _ _ _ (der_45805 v h) (by intro d hd; cases hd)))
def cl_50570 : CNF.NClause := [(22,false),(10,false),(26,true),(9,true),(75,true)]
theorem der_50570 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50570 :=
  CNF.rup_sound cl_50570 [cl_23572,cl_50468] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23572 v h) (hints_cons _ _ _ (der_50468 v h) (by intro d hd; cases hd)))
def cl_50573 : CNF.NClause := [(18,true),(9,false),(20,false),(11,true),(69,true)]
theorem der_50573 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50573 :=
  CNF.rup_sound cl_50573 [cl_23576,cl_48465] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23576 v h) (hints_cons _ _ _ (der_48465 v h) (by intro d hd; cases hd)))
def cl_50574 : CNF.NClause := [(11,false),(20,false),(18,true),(27,true),(69,true)]
theorem der_50574 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50574 :=
  CNF.rup_sound cl_50574 [cl_23587,cl_48465] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23587 v h) (hints_cons _ _ _ (der_48465 v h) (by intro d hd; cases hd)))
def cl_50586 : CNF.NClause := [(23,true),(22,true),(24,true),(67,false),(21,true)]
theorem der_50586 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50586 :=
  CNF.rup_sound cl_50586 [cl_15173,cl_36294] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15173 v h) (hints_cons _ _ _ (der_36294 v h) (by intro d hd; cases hd)))
def cl_50587 : CNF.NClause := [(8,true),(22,true),(11,true),(19,true),(90,false)]
theorem der_50587 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50587 :=
  CNF.rup_sound cl_50587 [cl_15360,cl_45805] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15360 v h) (hints_cons _ _ _ (der_45805 v h) (by intro d hd; cases hd)))
def cl_50588 : CNF.NClause := [(8,true),(28,true),(11,true),(19,true),(90,false)]
theorem der_50588 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50588 :=
  CNF.rup_sound cl_50588 [cl_15368,cl_45805] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15368 v h) (hints_cons _ _ _ (der_45805 v h) (by intro d hd; cases hd)))
def cl_50589 : CNF.NClause := [(28,true),(22,true),(11,true),(19,true),(90,false)]
theorem der_50589 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50589 :=
  CNF.rup_sound cl_50589 [cl_15375,cl_50588] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15375 v h) (hints_cons _ _ _ (der_50588 v h) (by intro d hd; cases hd)))
def cl_50590 : CNF.NClause := [(90,true),(62,true),(28,true),(59,false),(70,false)]
theorem der_50590 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50590 :=
  CNF.rup_sound cl_50590 [cl_32085,cl_47860] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32085 v h) (hints_cons _ _ _ (der_47860 v h) (by intro d hd; cases hd)))
def cl_50591 : CNF.NClause := [(66,false),(88,false),(67,true),(21,true),(52,false)]
theorem der_50591 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50591 :=
  CNF.rup_sound cl_50591 [cl_32097,cl_32096] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32097 v h) (hints_cons _ _ _ (der_32096 v h) (by intro d hd; cases hd)))
def cl_50592 : CNF.NClause := [(21,true),(66,false),(85,false),(67,true),(52,false)]
theorem der_50592 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50592 :=
  CNF.rup_sound cl_50592 [cl_32100,cl_46980] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32100 v h) (hints_cons _ _ _ (der_46980 v h) (by intro d hd; cases hd)))
def cl_50593 : CNF.NClause := [(66,false),(52,false),(79,false),(67,true),(21,true)]
theorem der_50593 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50593 :=
  CNF.rup_sound cl_50593 [cl_32102,cl_40159] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32102 v h) (hints_cons _ _ _ (der_40159 v h) (by intro d hd; cases hd)))
def cl_50594 : CNF.NClause := [(67,true),(21,true),(52,false),(73,false),(66,false)]
theorem der_50594 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50594 :=
  CNF.rup_sound cl_50594 [cl_32103,cl_50592] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32103 v h) (hints_cons _ _ _ (der_50592 v h) (by intro d hd; cases hd)))
def cl_50595 : CNF.NClause := [(66,false),(88,true),(52,false),(67,true),(21,true)]
theorem der_50595 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50595 :=
  CNF.rup_sound cl_50595 [cl_32104,cl_50593] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32104 v h) (hints_cons _ _ _ (der_50593 v h) (by intro d hd; cases hd)))
def cl_50596 : CNF.NClause := [(76,true),(39,false),(82,false),(68,false),(90,false)]
theorem der_50596 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50596 :=
  CNF.rup_sound cl_50596 [cl_32116,cl_32107] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32116 v h) (hints_cons _ _ _ (der_32107 v h) (by intro d hd; cases hd)))
def cl_50597 : CNF.NClause := [(90,false),(82,false),(39,false),(79,true),(8,false)]
theorem der_50597 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50597 :=
  CNF.rup_sound cl_50597 [cl_32119,cl_32112] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32119 v h) (hints_cons _ _ _ (der_32112 v h) (by intro d hd; cases hd)))
def cl_50598 : CNF.NClause := [(65,false),(79,false),(90,false),(8,true),(39,false)]
theorem der_50598 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50598 :=
  CNF.rup_sound cl_50598 [cl_32122,cl_42425] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32122 v h) (hints_cons _ _ _ (der_42425 v h) (by intro d hd; cases hd)))
def cl_50599 : CNF.NClause := [(8,true),(68,false),(39,false),(79,false),(90,false)]
theorem der_50599 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50599 :=
  CNF.rup_sound cl_50599 [cl_32126,cl_50598] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32126 v h) (hints_cons _ _ _ (der_50598 v h) (by intro d hd; cases hd)))
def cl_50601 : CNF.NClause := [(68,true),(90,false),(8,true),(39,false),(79,false)]
theorem der_50601 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50601 :=
  CNF.rup_sound cl_50601 [cl_32130,cl_32110] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32130 v h) (hints_cons _ _ _ (der_32110 v h) (by intro d hd; cases hd)))
def cl_50602 : CNF.NClause := [(76,false),(39,false),(68,false),(90,false),(79,true)]
theorem der_50602 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50602 :=
  CNF.rup_sound cl_50602 [cl_32132,cl_32131] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32132 v h) (hints_cons _ _ _ (der_32131 v h) (by intro d hd; cases hd)))
def cl_50603 : CNF.NClause := [(90,false),(39,false),(76,false),(8,true),(65,false)]
theorem der_50603 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50603 :=
  CNF.rup_sound cl_50603 [cl_32133,cl_50598] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32133 v h) (hints_cons _ _ _ (der_50598 v h) (by intro d hd; cases hd)))
def cl_50604 : CNF.NClause := [(90,false),(68,false),(8,true),(39,false),(65,false)]
theorem der_50604 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50604 :=
  CNF.rup_sound cl_50604 [cl_32136,cl_50599] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32136 v h) (hints_cons _ _ _ (der_50599 v h) (by intro d hd; cases hd)))
def cl_50605 : CNF.NClause := [(90,false),(39,false),(68,false),(8,true),(79,true)]
theorem der_50605 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50605 :=
  CNF.rup_sound cl_50605 [cl_32138,cl_50602] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32138 v h) (hints_cons _ _ _ (der_50602 v h) (by intro d hd; cases hd)))
def cl_50606 : CNF.NClause := [(90,false),(39,false),(8,true),(65,false),(82,true)]
theorem der_50606 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50606 :=
  CNF.rup_sound cl_50606 [cl_32140,cl_50598] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32140 v h) (hints_cons _ _ _ (der_50598 v h) (by intro d hd; cases hd)))
def cl_50607 : CNF.NClause := [(90,false),(76,true),(79,true),(8,false),(39,false)]
theorem der_50607 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50607 :=
  CNF.rup_sound cl_50607 [cl_32141,cl_50597] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32141 v h) (hints_cons _ _ _ (der_50597 v h) (by intro d hd; cases hd)))
def cl_50608 : CNF.NClause := [(68,true),(90,false),(39,false),(82,true),(8,true)]
theorem der_50608 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50608 :=
  CNF.rup_sound cl_50608 [cl_32142,cl_50606] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32142 v h) (hints_cons _ _ _ (der_50606 v h) (by intro d hd; cases hd)))
def cl_50609 : CNF.NClause := [(76,false),(82,false),(79,false),(39,false),(65,true)]
theorem der_50609 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50609 :=
  CNF.rup_sound cl_50609 [cl_32145,cl_32144] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32145 v h) (hints_cons _ _ _ (der_32144 v h) (by intro d hd; cases hd)))
def cl_50610 : CNF.NClause := [(65,true),(79,false),(68,false),(82,false),(39,false)]
theorem der_50610 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50610 :=
  CNF.rup_sound cl_50610 [cl_32148,cl_32147] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32148 v h) (hints_cons _ _ _ (der_32147 v h) (by intro d hd; cases hd)))
def cl_50611 : CNF.NClause := [(65,true),(82,false),(39,false),(8,false),(79,false)]
theorem der_50611 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50611 :=
  CNF.rup_sound cl_50611 [cl_32151,cl_50610] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32151 v h) (hints_cons _ _ _ (der_50610 v h) (by intro d hd; cases hd)))
def cl_50612 : CNF.NClause := [(76,false),(82,false),(39,false),(79,true),(65,false)]
theorem der_50612 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50612 :=
  CNF.rup_sound cl_50612 [cl_32157,cl_32156] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32157 v h) (hints_cons _ _ _ (der_32156 v h) (by intro d hd; cases hd)))
def cl_50613 : CNF.NClause := [(65,true),(68,false),(82,false),(39,false),(76,true)]
theorem der_50613 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50613 :=
  CNF.rup_sound cl_50613 [cl_32163,cl_50610] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32163 v h) (hints_cons _ _ _ (der_50610 v h) (by intro d hd; cases hd)))
def cl_50614 : CNF.NClause := [(82,false),(39,false),(79,true),(65,false),(8,false)]
theorem der_50614 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50614 :=
  CNF.rup_sound cl_50614 [cl_32164,cl_50612] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32164 v h) (hints_cons _ _ _ (der_50612 v h) (by intro d hd; cases hd)))
def cl_50615 : CNF.NClause := [(76,false),(65,true),(39,false),(68,false),(79,false)]
theorem der_50615 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50615 :=
  CNF.rup_sound cl_50615 [cl_32169,cl_50609] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32169 v h) (hints_cons _ _ _ (der_50609 v h) (by intro d hd; cases hd)))
def cl_50616 : CNF.NClause := [(76,false),(39,false),(79,false),(65,false),(8,true)]
theorem der_50616 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50616 :=
  CNF.rup_sound cl_50616 [cl_32171,cl_50603] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32171 v h) (hints_cons _ _ _ (der_50603 v h) (by intro d hd; cases hd)))
def cl_50617 : CNF.NClause := [(76,false),(65,true),(39,false),(8,false),(79,false)]
theorem der_50617 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50617 :=
  CNF.rup_sound cl_50617 [cl_32172,cl_32168] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32172 v h) (hints_cons _ _ _ (der_32168 v h) (by intro d hd; cases hd)))
def cl_50618 : CNF.NClause := [(65,false),(8,true),(39,false),(79,false),(68,false)]
theorem der_50618 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50618 :=
  CNF.rup_sound cl_50618 [cl_32175,cl_50616] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32175 v h) (hints_cons _ _ _ (der_50616 v h) (by intro d hd; cases hd)))
def cl_50619 : CNF.NClause := [(65,true),(8,false),(39,false),(79,false),(68,false)]
theorem der_50619 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50619 :=
  CNF.rup_sound cl_50619 [cl_32176,cl_32168] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32176 v h) (hints_cons _ _ _ (der_32168 v h) (by intro d hd; cases hd)))
def cl_50620 : CNF.NClause := [(65,false),(39,false),(79,false),(8,false),(90,true)]
theorem der_50620 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50620 :=
  CNF.rup_sound cl_50620 [cl_32178,cl_32174] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32178 v h) (hints_cons _ _ _ (der_32174 v h) (by intro d hd; cases hd)))
def cl_50621 : CNF.NClause := [(65,false),(8,true),(39,false),(79,false),(68,true)]
theorem der_50621 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50621 :=
  CNF.rup_sound cl_50621 [cl_32179,cl_50616] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32179 v h) (hints_cons _ _ _ (der_50616 v h) (by intro d hd; cases hd)))
def cl_50623 : CNF.NClause := [(8,true),(39,false),(79,false),(76,true),(68,true)]
theorem der_50623 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50623 :=
  CNF.rup_sound cl_50623 [cl_32181,cl_50621] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32181 v h) (hints_cons _ _ _ (der_50621 v h) (by intro d hd; cases hd)))
def cl_50624 : CNF.NClause := [(76,false),(68,false),(8,true),(39,false),(65,false)]
theorem der_50624 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50624 :=
  CNF.rup_sound cl_50624 [cl_32183,cl_50604] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32183 v h) (hints_cons _ _ _ (der_50604 v h) (by intro d hd; cases hd)))
def cl_50625 : CNF.NClause := [(76,false),(68,false),(8,true),(39,false),(82,true)]
theorem der_50625 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50625 :=
  CNF.rup_sound cl_50625 [cl_32184,cl_50624] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32184 v h) (hints_cons _ _ _ (der_50624 v h) (by intro d hd; cases hd)))
def cl_50626 : CNF.NClause := [(90,true),(76,false),(65,false),(8,false),(39,false)]
theorem der_50626 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50626 :=
  CNF.rup_sound cl_50626 [cl_32185,cl_50620] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32185 v h) (hints_cons _ _ _ (der_50620 v h) (by intro d hd; cases hd)))
def cl_50627 : CNF.NClause := [(65,false),(76,false),(39,false),(82,true),(90,true)]
theorem der_50627 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50627 :=
  CNF.rup_sound cl_50627 [cl_32186,cl_50626] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32186 v h) (hints_cons _ _ _ (der_50626 v h) (by intro d hd; cases hd)))
def cl_50628 : CNF.NClause := [(90,true),(68,false),(65,false),(8,false),(39,false)]
theorem der_50628 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50628 :=
  CNF.rup_sound cl_50628 [cl_32188,cl_32174] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32188 v h) (hints_cons _ _ _ (der_32174 v h) (by intro d hd; cases hd)))
def cl_50629 : CNF.NClause := [(65,false),(68,false),(8,true),(39,false),(82,true)]
theorem der_50629 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50629 :=
  CNF.rup_sound cl_50629 [cl_32189,cl_50624] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32189 v h) (hints_cons _ _ _ (der_50624 v h) (by intro d hd; cases hd)))
def cl_50630 : CNF.NClause := [(76,true),(68,false),(79,true),(8,false),(39,false)]
theorem der_50630 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50630 :=
  CNF.rup_sound cl_50630 [cl_32190,cl_50607] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32190 v h) (hints_cons _ _ _ (der_50607 v h) (by intro d hd; cases hd)))
def cl_50631 : CNF.NClause := [(65,false),(76,true),(79,true),(8,false),(39,false)]
theorem der_50631 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50631 :=
  CNF.rup_sound cl_50631 [cl_32192,cl_50614] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32192 v h) (hints_cons _ _ _ (der_50614 v h) (by intro d hd; cases hd)))
def cl_50634 : CNF.NClause := [(37,false),(70,false),(66,true),(82,false),(91,false)]
theorem der_50634 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50634 :=
  CNF.rup_sound cl_50634 [cl_32203,cl_50549] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32203 v h) (hints_cons _ _ _ (der_50549 v h) (by intro d hd; cases hd)))
def cl_50635 : CNF.NClause := [(37,false),(70,true),(82,false),(66,false),(91,false)]
theorem der_50635 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50635 :=
  CNF.rup_sound cl_50635 [cl_32205,cl_50550] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32205 v h) (hints_cons _ _ _ (der_50550 v h) (by intro d hd; cases hd)))
def cl_50636 : CNF.NClause := [(37,false),(70,true),(78,true),(82,false),(91,false)]
theorem der_50636 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50636 :=
  CNF.rup_sound cl_50636 [cl_32207,cl_49706] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32207 v h) (hints_cons _ _ _ (der_49706 v h) (by intro d hd; cases hd)))
def cl_50637 : CNF.NClause := [(37,false),(91,false),(66,true),(78,false),(74,false)]
theorem der_50637 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50637 :=
  CNF.rup_sound cl_50637 [cl_32212,cl_49711] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32212 v h) (hints_cons _ _ _ (der_49711 v h) (by intro d hd; cases hd)))
def cl_50639 : CNF.NClause := [(37,false),(66,false),(70,true),(91,false),(78,false)]
theorem der_50639 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50639 :=
  CNF.rup_sound cl_50639 [cl_32218,cl_50635] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32218 v h) (hints_cons _ _ _ (der_50635 v h) (by intro d hd; cases hd)))
def cl_50640 : CNF.NClause := [(37,false),(78,false),(6,false),(91,false),(66,true)]
theorem der_50640 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50640 :=
  CNF.rup_sound cl_50640 [cl_32219,cl_50637] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32219 v h) (hints_cons _ _ _ (der_50637 v h) (by intro d hd; cases hd)))
def cl_50641 : CNF.NClause := [(37,false),(78,false),(70,true),(74,true),(91,false)]
theorem der_50641 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50641 :=
  CNF.rup_sound cl_50641 [cl_32220,cl_50639] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32220 v h) (hints_cons _ _ _ (der_50639 v h) (by intro d hd; cases hd)))
def cl_50642 : CNF.NClause := [(74,false),(37,false),(66,true),(91,false),(70,false)]
theorem der_50642 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50642 :=
  CNF.rup_sound cl_50642 [cl_32222,cl_50634] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32222 v h) (hints_cons _ _ _ (der_50634 v h) (by intro d hd; cases hd)))
def cl_50643 : CNF.NClause := [(70,true),(66,false),(74,false),(91,false),(37,false)]
theorem der_50643 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50643 :=
  CNF.rup_sound cl_50643 [cl_32223,cl_50635] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32223 v h) (hints_cons _ _ _ (der_50635 v h) (by intro d hd; cases hd)))
def cl_50645 : CNF.NClause := [(37,false),(70,false),(66,true),(74,true),(91,false)]
theorem der_50645 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50645 :=
  CNF.rup_sound cl_50645 [cl_32228,cl_50549] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32228 v h) (hints_cons _ _ _ (der_50549 v h) (by intro d hd; cases hd)))
def cl_50646 : CNF.NClause := [(91,false),(70,true),(66,false),(78,true),(37,false)]
theorem der_50646 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50646 :=
  CNF.rup_sound cl_50646 [cl_32231,cl_50636] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32231 v h) (hints_cons _ _ _ (der_50636 v h) (by intro d hd; cases hd)))
def cl_50647 : CNF.NClause := [(91,false),(70,true),(78,true),(37,false),(6,false)]
theorem der_50647 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50647 :=
  CNF.rup_sound cl_50647 [cl_32232,cl_50636] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32232 v h) (hints_cons _ _ _ (der_50636 v h) (by intro d hd; cases hd)))
def cl_50648 : CNF.NClause := [(91,false),(82,true),(74,true),(66,true),(37,false)]
theorem der_50648 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50648 :=
  CNF.rup_sound cl_50648 [cl_32233,cl_50645] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32233 v h) (hints_cons _ _ _ (der_50645 v h) (by intro d hd; cases hd)))
def cl_50649 : CNF.NClause := [(37,false),(70,true),(82,false),(78,false),(74,false)]
theorem der_50649 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50649 :=
  CNF.rup_sound cl_50649 [cl_32236,cl_50547] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32236 v h) (hints_cons _ _ _ (der_50547 v h) (by intro d hd; cases hd)))
def cl_50650 : CNF.NClause := [(37,false),(78,false),(82,false),(70,false),(74,true)]
theorem der_50650 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50650 :=
  CNF.rup_sound cl_50650 [cl_32238,cl_43014] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32238 v h) (hints_cons _ _ _ (der_43014 v h) (by intro d hd; cases hd)))
def cl_50651 : CNF.NClause := [(82,false),(37,false),(66,true),(70,true),(78,false)]
theorem der_50651 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50651 :=
  CNF.rup_sound cl_50651 [cl_32241,cl_50547] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32241 v h) (hints_cons _ _ _ (der_50547 v h) (by intro d hd; cases hd)))
def cl_50652 : CNF.NClause := [(37,false),(74,false),(82,false),(70,false),(66,true)]
theorem der_50652 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50652 :=
  CNF.rup_sound cl_50652 [cl_32244,cl_50549] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32244 v h) (hints_cons _ _ _ (der_50549 v h) (by intro d hd; cases hd)))
def cl_50653 : CNF.NClause := [(82,false),(37,false),(66,true),(70,false),(74,false)]
theorem der_50653 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50653 :=
  CNF.rup_sound cl_50653 [cl_32245,cl_50634] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32245 v h) (hints_cons _ _ _ (der_50634 v h) (by intro d hd; cases hd)))
def cl_50654 : CNF.NClause := [(37,false),(82,false),(70,false),(78,true),(66,false)]
theorem der_50654 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50654 :=
  CNF.rup_sound cl_50654 [cl_32248,cl_50550] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32248 v h) (hints_cons _ _ _ (der_50550 v h) (by intro d hd; cases hd)))
def cl_50656 : CNF.NClause := [(82,false),(70,false),(37,false),(74,true),(91,true)]
theorem der_50656 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50656 :=
  CNF.rup_sound cl_50656 [cl_32250,cl_50548] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32250 v h) (hints_cons _ _ _ (der_50548 v h) (by intro d hd; cases hd)))
def cl_50660 : CNF.NClause := [(78,false),(74,false),(70,false),(66,true),(37,false)]
theorem der_50660 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50660 :=
  CNF.rup_sound cl_50660 [cl_32258,cl_50652] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32258 v h) (hints_cons _ _ _ (der_50652 v h) (by intro d hd; cases hd)))
def cl_50661 : CNF.NClause := [(70,true),(66,false),(78,false),(74,false),(37,false)]
theorem der_50661 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50661 :=
  CNF.rup_sound cl_50661 [cl_32260,cl_32235] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32260 v h) (hints_cons _ _ _ (der_32235 v h) (by intro d hd; cases hd)))
def cl_50662 : CNF.NClause := [(37,false),(78,false),(66,false),(70,false),(82,true)]
theorem der_50662 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50662 :=
  CNF.rup_sound cl_50662 [cl_32263,cl_43014] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32263 v h) (hints_cons _ _ _ (der_43014 v h) (by intro d hd; cases hd)))
def cl_50663 : CNF.NClause := [(78,false),(82,true),(37,false),(70,false),(66,true)]
theorem der_50663 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50663 :=
  CNF.rup_sound cl_50663 [cl_32265,cl_43014] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32265 v h) (hints_cons _ _ _ (der_43014 v h) (by intro d hd; cases hd)))
def cl_50666 : CNF.NClause := [(66,false),(78,false),(91,true),(37,false),(82,true)]
theorem der_50666 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50666 :=
  CNF.rup_sound cl_50666 [cl_32268,cl_50662] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32268 v h) (hints_cons _ _ _ (der_50662 v h) (by intro d hd; cases hd)))
def cl_50667 : CNF.NClause := [(91,true),(78,false),(66,true),(37,false),(82,true)]
theorem der_50667 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50667 :=
  CNF.rup_sound cl_50667 [cl_32270,cl_50663] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32270 v h) (hints_cons _ _ _ (der_50663 v h) (by intro d hd; cases hd)))
def cl_50668 : CNF.NClause := [(74,false),(37,false),(70,false),(6,false),(66,true)]
theorem der_50668 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50668 :=
  CNF.rup_sound cl_50668 [cl_32272,cl_50652] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32272 v h) (hints_cons _ _ _ (der_50652 v h) (by intro d hd; cases hd)))
def cl_50669 : CNF.NClause := [(37,false),(74,false),(82,true),(66,false),(6,false)]
theorem der_50669 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50669 :=
  CNF.rup_sound cl_50669 [cl_32274,cl_32271] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32274 v h) (hints_cons _ _ _ (der_32271 v h) (by intro d hd; cases hd)))
def cl_50670 : CNF.NClause := [(37,false),(70,false),(74,true),(78,true),(66,false)]
theorem der_50670 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50670 :=
  CNF.rup_sound cl_50670 [cl_32277,cl_49708] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32277 v h) (hints_cons _ _ _ (der_49708 v h) (by intro d hd; cases hd)))
def cl_50671 : CNF.NClause := [(70,false),(82,true),(66,true),(74,true),(37,false)]
theorem der_50671 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50671 :=
  CNF.rup_sound cl_50671 [cl_32279,cl_50549] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32279 v h) (hints_cons _ _ _ (der_50549 v h) (by intro d hd; cases hd)))
def cl_50672 : CNF.NClause := [(78,true),(37,false),(91,true),(74,true),(66,false)]
theorem der_50672 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50672 :=
  CNF.rup_sound cl_50672 [cl_32281,cl_49708] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32281 v h) (hints_cons _ _ _ (der_49708 v h) (by intro d hd; cases hd)))
def cl_50676 : CNF.NClause := [(85,true),(92,false),(84,false),(86,false),(36,false)]
theorem der_50676 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50676 :=
  CNF.rup_sound cl_50676 [cl_32290,cl_49536] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32290 v h) (hints_cons _ _ _ (der_49536 v h) (by intro d hd; cases hd)))
def cl_50678 : CNF.NClause := [(92,false),(86,false),(5,false),(85,true),(36,false)]
theorem der_50678 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50678 :=
  CNF.rup_sound cl_50678 [cl_32295,cl_32293] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32295 v h) (hints_cons _ _ _ (der_32293 v h) (by intro d hd; cases hd)))
def cl_50679 : CNF.NClause := [(85,true),(92,false),(86,false),(36,false),(82,true)]
theorem der_50679 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50679 :=
  CNF.rup_sound cl_50679 [cl_32296,cl_50676] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32296 v h) (hints_cons _ _ _ (der_50676 v h) (by intro d hd; cases hd)))
def cl_50680 : CNF.NClause := [(83,false),(92,false),(84,false),(5,true),(36,false)]
theorem der_50680 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50680 :=
  CNF.rup_sound cl_50680 [cl_32306,cl_32305] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32306 v h) (hints_cons _ _ _ (der_32305 v h) (by intro d hd; cases hd)))
def cl_50681 : CNF.NClause := [(92,false),(5,true),(36,false),(82,false),(84,false)]
theorem der_50681 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50681 :=
  CNF.rup_sound cl_50681 [cl_32308,cl_32305] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32308 v h) (hints_cons _ _ _ (der_32305 v h) (by intro d hd; cases hd)))
def cl_50682 : CNF.NClause := [(85,true),(83,true),(36,false),(84,false),(92,false)]
theorem der_50682 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50682 :=
  CNF.rup_sound cl_50682 [cl_32310,cl_32309] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32310 v h) (hints_cons _ _ _ (der_32309 v h) (by intro d hd; cases hd)))
def cl_50683 : CNF.NClause := [(85,true),(83,true),(36,false),(92,false),(82,true)]
theorem der_50683 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50683 :=
  CNF.rup_sound cl_50683 [cl_32317,cl_32316] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32317 v h) (hints_cons _ _ _ (der_32316 v h) (by intro d hd; cases hd)))
def cl_50684 : CNF.NClause := [(82,false),(36,false),(5,true),(86,false),(85,false)]
theorem der_50684 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50684 :=
  CNF.rup_sound cl_50684 [cl_32322,cl_49536] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32322 v h) (hints_cons _ _ _ (der_49536 v h) (by intro d hd; cases hd)))
def cl_50685 : CNF.NClause := [(86,false),(85,false),(36,false),(83,true),(5,true)]
theorem der_50685 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50685 :=
  CNF.rup_sound cl_50685 [cl_32324,cl_50684] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32324 v h) (hints_cons _ _ _ (der_50684 v h) (by intro d hd; cases hd)))
def cl_50686 : CNF.NClause := [(85,true),(84,false),(36,false),(86,false),(82,true)]
theorem der_50686 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50686 :=
  CNF.rup_sound cl_50686 [cl_32327,cl_49536] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32327 v h) (hints_cons _ _ _ (der_49536 v h) (by intro d hd; cases hd)))
def cl_50687 : CNF.NClause := [(85,true),(83,true),(86,false),(36,false),(84,false)]
theorem der_50687 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50687 :=
  CNF.rup_sound cl_50687 [cl_32328,cl_50682] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32328 v h) (hints_cons _ _ _ (der_50682 v h) (by intro d hd; cases hd)))
def cl_50688 : CNF.NClause := [(85,true),(83,true),(82,false),(36,false),(86,false)]
theorem der_50688 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50688 :=
  CNF.rup_sound cl_50688 [cl_32331,cl_50687] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32331 v h) (hints_cons _ _ _ (der_50687 v h) (by intro d hd; cases hd)))
def cl_50689 : CNF.NClause := [(83,true),(82,true),(85,true),(36,false),(86,false)]
theorem der_50689 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50689 :=
  CNF.rup_sound cl_50689 [cl_32333,cl_50687] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32333 v h) (hints_cons _ _ _ (der_50687 v h) (by intro d hd; cases hd)))
def cl_50690 : CNF.NClause := [(83,false),(85,false),(84,false),(5,true),(36,false)]
theorem der_50690 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50690 :=
  CNF.rup_sound cl_50690 [cl_32335,cl_32334] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32335 v h) (hints_cons _ _ _ (der_32334 v h) (by intro d hd; cases hd)))
def cl_50691 : CNF.NClause := [(82,false),(84,false),(85,false),(5,true),(36,false)]
theorem der_50691 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50691 :=
  CNF.rup_sound cl_50691 [cl_32336,cl_32334] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32336 v h) (hints_cons _ _ _ (der_32334 v h) (by intro d hd; cases hd)))
def cl_50692 : CNF.NClause := [(84,false),(85,false),(36,false),(92,true),(5,true)]
theorem der_50692 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50692 :=
  CNF.rup_sound cl_50692 [cl_32338,cl_50690] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32338 v h) (hints_cons _ _ _ (der_50690 v h) (by intro d hd; cases hd)))
def cl_50693 : CNF.NClause := [(83,false),(82,false),(5,true),(85,false),(36,false)]
theorem der_50693 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50693 :=
  CNF.rup_sound cl_50693 [cl_32339,cl_32334] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32339 v h) (hints_cons _ _ _ (der_32334 v h) (by intro d hd; cases hd)))
def cl_50694 : CNF.NClause := [(85,false),(36,false),(5,true),(86,true),(83,false)]
theorem der_50694 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50694 :=
  CNF.rup_sound cl_50694 [cl_32341,cl_50690] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32341 v h) (hints_cons _ _ _ (der_50690 v h) (by intro d hd; cases hd)))
def cl_50695 : CNF.NClause := [(85,false),(36,false),(5,true),(82,false),(84,true)]
theorem der_50695 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50695 :=
  CNF.rup_sound cl_50695 [cl_32343,cl_50684] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32343 v h) (hints_cons _ _ _ (der_50684 v h) (by intro d hd; cases hd)))
def cl_50696 : CNF.NClause := [(83,true),(85,false),(86,true),(5,false),(36,false)]
theorem der_50696 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50696 :=
  CNF.rup_sound cl_50696 [cl_32344,cl_32303] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32344 v h) (hints_cons _ _ _ (der_32303 v h) (by intro d hd; cases hd)))
def cl_50697 : CNF.NClause := [(85,false),(36,false),(92,true),(86,true),(5,true)]
theorem der_50697 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50697 :=
  CNF.rup_sound cl_50697 [cl_32345,cl_50692] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32345 v h) (hints_cons _ _ _ (der_50692 v h) (by intro d hd; cases hd)))
def cl_50698 : CNF.NClause := [(83,false),(82,true),(36,false),(84,false),(5,true)]
theorem der_50698 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50698 :=
  CNF.rup_sound cl_50698 [cl_32348,cl_50680] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32348 v h) (hints_cons _ _ _ (der_50680 v h) (by intro d hd; cases hd)))
def cl_50699 : CNF.NClause := [(83,true),(82,false),(84,false),(5,true),(36,false)]
theorem der_50699 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50699 :=
  CNF.rup_sound cl_50699 [cl_32350,cl_49536] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32350 v h) (hints_cons _ _ _ (der_49536 v h) (by intro d hd; cases hd)))
def cl_50700 : CNF.NClause := [(84,false),(86,true),(5,false),(36,false),(83,true)]
theorem der_50700 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50700 :=
  CNF.rup_sound cl_50700 [cl_32351,cl_50696] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32351 v h) (hints_cons _ _ _ (der_50696 v h) (by intro d hd; cases hd)))
def cl_50701 : CNF.NClause := [(84,false),(82,true),(85,true),(83,true),(36,false)]
theorem der_50701 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50701 :=
  CNF.rup_sound cl_50701 [cl_32352,cl_50686] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32352 v h) (hints_cons _ _ _ (der_50686 v h) (by intro d hd; cases hd)))
def cl_50704 : CNF.NClause := [(62,true),(79,false),(26,true),(57,false),(91,false)]
theorem der_50704 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50704 :=
  CNF.rup_sound cl_50704 [cl_32371,cl_49554] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32371 v h) (hints_cons _ _ _ (der_49554 v h) (by intro d hd; cases hd)))
def cl_50706 : CNF.NClause := [(62,true),(83,false),(57,false),(79,false),(26,true)]
theorem der_50706 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50706 :=
  CNF.rup_sound cl_50706 [cl_32374,cl_49554] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32374 v h) (hints_cons _ _ _ (der_49554 v h) (by intro d hd; cases hd)))
def cl_50707 : CNF.NClause := [(83,false),(62,true),(71,false),(26,true),(57,false)]
theorem der_50707 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50707 :=
  CNF.rup_sound cl_50707 [cl_32376,cl_32375] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32376 v h) (hints_cons _ _ _ (der_32375 v h) (by intro d hd; cases hd)))
def cl_50708 : CNF.NClause := [(75,false),(62,true),(26,true),(57,false),(79,false)]
theorem der_50708 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50708 :=
  CNF.rup_sound cl_50708 [cl_32377,cl_49554] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32377 v h) (hints_cons _ _ _ (der_49554 v h) (by intro d hd; cases hd)))
def cl_50709 : CNF.NClause := [(62,true),(79,false),(26,true),(57,false),(75,true)]
theorem der_50709 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50709 :=
  CNF.rup_sound cl_50709 [cl_32378,cl_49554] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32378 v h) (hints_cons _ _ _ (der_49554 v h) (by intro d hd; cases hd)))
def cl_50712 : CNF.NClause := [(65,false),(72,false),(13,true),(44,false),(71,false)]
theorem der_50712 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50712 :=
  CNF.rup_sound cl_50712 [cl_32381,cl_49563] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32381 v h) (hints_cons _ _ _ (der_49563 v h) (by intro d hd; cases hd)))
def cl_50713 : CNF.NClause := [(85,false),(63,false),(19,true),(50,false),(71,false)]
theorem der_50713 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50713 :=
  CNF.rup_sound cl_50713 [cl_32386,cl_32385] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32386 v h) (hints_cons _ _ _ (der_32385 v h) (by intro d hd; cases hd)))
def cl_50714 : CNF.NClause := [(50,false),(74,true),(19,true),(71,false),(63,false)]
theorem der_50714 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50714 :=
  CNF.rup_sound cl_50714 [cl_32388,cl_50713] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32388 v h) (hints_cons _ _ _ (der_50713 v h) (by intro d hd; cases hd)))
def cl_50718 : CNF.NClause := [(67,false),(23,true),(20,true),(22,true),(21,true)]
theorem der_50718 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50718 :=
  CNF.rup_sound cl_50718 [cl_15158,cl_36294] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15158 v h) (hints_cons _ _ _ (der_36294 v h) (by intro d hd; cases hd)))
def cl_50719 : CNF.NClause := [(67,false),(21,true),(20,true),(22,true),(24,true)]
theorem der_50719 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50719 :=
  CNF.rup_sound cl_50719 [cl_15166,cl_36294] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15166 v h) (hints_cons _ _ _ (der_36294 v h) (by intro d hd; cases hd)))
def cl_50720 : CNF.NClause := [(67,false),(21,true),(23,true),(20,true),(24,true)]
theorem der_50720 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50720 :=
  CNF.rup_sound cl_50720 [cl_15170,cl_36294] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15170 v h) (hints_cons _ _ _ (der_36294 v h) (by intro d hd; cases hd)))
def cl_50721 : CNF.NClause := [(90,false),(64,false),(22,true),(53,false),(67,false)]
theorem der_50721 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50721 :=
  CNF.rup_sound cl_50721 [cl_32409,cl_49558] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32409 v h) (hints_cons _ _ _ (der_49558 v h) (by intro d hd; cases hd)))
def cl_50722 : CNF.NClause := [(86,false),(53,false),(64,false),(67,false),(22,true)]
theorem der_50722 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50722 :=
  CNF.rup_sound cl_50722 [cl_32412,cl_32406] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32412 v h) (hints_cons _ _ _ (der_32406 v h) (by intro d hd; cases hd)))
def cl_50724 : CNF.NClause := [(90,true),(67,false),(22,true),(53,false),(64,false)]
theorem der_50724 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50724 :=
  CNF.rup_sound cl_50724 [cl_32416,cl_50722] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32416 v h) (hints_cons _ _ _ (der_50722 v h) (by intro d hd; cases hd)))
def cl_50726 : CNF.NClause := [(88,false),(82,false),(63,false),(9,true),(40,false)]
theorem der_50726 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50726 :=
  CNF.rup_sound cl_50726 [cl_32420,cl_32418] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32420 v h) (hints_cons _ _ _ (der_32418 v h) (by intro d hd; cases hd)))
def cl_50727 : CNF.NClause := [(40,false),(69,false),(88,false),(9,true),(63,false)]
theorem der_50727 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50727 :=
  CNF.rup_sound cl_50727 [cl_32423,cl_45302] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32423 v h) (hints_cons _ _ _ (der_45302 v h) (by intro d hd; cases hd)))
def cl_50728 : CNF.NClause := [(63,false),(75,true),(9,true),(40,false),(88,false)]
theorem der_50728 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50728 :=
  CNF.rup_sound cl_50728 [cl_32424,cl_50727] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32424 v h) (hints_cons _ _ _ (der_50727 v h) (by intro d hd; cases hd)))
def cl_50729 : CNF.NClause := [(82,false),(9,true),(40,false),(69,false),(63,false)]
theorem der_50729 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50729 :=
  CNF.rup_sound cl_50729 [cl_32427,cl_47453] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32427 v h) (hints_cons _ _ _ (der_47453 v h) (by intro d hd; cases hd)))
def cl_50730 : CNF.NClause := [(81,true),(82,false),(9,true),(40,false),(63,false)]
theorem der_50730 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50730 :=
  CNF.rup_sound cl_50730 [cl_32428,cl_50726] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32428 v h) (hints_cons _ _ _ (der_50726 v h) (by intro d hd; cases hd)))
def cl_50731 : CNF.NClause := [(63,false),(69,true),(81,false),(9,true),(40,false)]
theorem der_50731 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50731 :=
  CNF.rup_sound cl_50731 [cl_32431,cl_32429] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32431 v h) (hints_cons _ _ _ (der_32429 v h) (by intro d hd; cases hd)))
def cl_50732 : CNF.NClause := [(75,false),(40,false),(63,false),(81,true),(9,true)]
theorem der_50732 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50732 :=
  CNF.rup_sound cl_50732 [cl_32433,cl_32422] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32433 v h) (hints_cons _ _ _ (der_32422 v h) (by intro d hd; cases hd)))
def cl_50734 : CNF.NClause := [(89,false),(63,false),(14,true),(45,false),(79,false)]
theorem der_50734 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50734 :=
  CNF.rup_sound cl_50734 [cl_32438,cl_47228] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32438 v h) (hints_cons _ _ _ (der_47228 v h) (by intro d hd; cases hd)))
def cl_50736 : CNF.NClause := [(70,true),(86,false),(63,false),(14,true),(45,false)]
theorem der_50736 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50736 :=
  CNF.rup_sound cl_50736 [cl_32443,cl_49539] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32443 v h) (hints_cons _ _ _ (der_49539 v h) (by intro d hd; cases hd)))
def cl_50738 : CNF.NClause := [(63,false),(45,false),(14,true),(70,true),(86,true)]
theorem der_50738 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50738 :=
  CNF.rup_sound cl_50738 [cl_32447,cl_49539] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32447 v h) (hints_cons _ _ _ (der_49539 v h) (by intro d hd; cases hd)))
def cl_50739 : CNF.NClause := [(78,false),(58,false),(85,false),(89,false),(62,true)]
theorem der_50739 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50739 :=
  CNF.rup_sound cl_50739 [cl_32453,cl_32450] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32453 v h) (hints_cons _ _ _ (der_32450 v h) (by intro d hd; cases hd)))
def cl_50740 : CNF.NClause := [(76,false),(85,false),(78,true),(58,false),(89,false)]
theorem der_50740 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50740 :=
  CNF.rup_sound cl_50740 [cl_32457,cl_32456] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32457 v h) (hints_cons _ _ _ (der_32456 v h) (by intro d hd; cases hd)))
def cl_50741 : CNF.NClause := [(78,true),(85,false),(58,false),(89,false),(62,false)]
theorem der_50741 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50741 :=
  CNF.rup_sound cl_50741 [cl_32461,cl_50740] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32461 v h) (hints_cons _ _ _ (der_50740 v h) (by intro d hd; cases hd)))
def cl_50742 : CNF.NClause := [(78,false),(58,false),(69,true),(76,false),(89,false)]
theorem der_50742 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50742 :=
  CNF.rup_sound cl_50742 [cl_32466,cl_32464] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32466 v h) (hints_cons _ _ _ (der_32464 v h) (by intro d hd; cases hd)))
def cl_50743 : CNF.NClause := [(78,false),(58,false),(69,true),(89,false),(62,true)]
theorem der_50743 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50743 :=
  CNF.rup_sound cl_50743 [cl_32472,cl_50739] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32472 v h) (hints_cons _ _ _ (der_50739 v h) (by intro d hd; cases hd)))
def cl_50744 : CNF.NClause := [(89,false),(58,false),(76,false),(69,true),(85,true)]
theorem der_50744 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50744 :=
  CNF.rup_sound cl_50744 [cl_32476,cl_32474] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32476 v h) (hints_cons _ _ _ (der_32474 v h) (by intro d hd; cases hd)))
def cl_50745 : CNF.NClause := [(76,true),(69,false),(58,false),(89,false),(62,false)]
theorem der_50745 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50745 :=
  CNF.rup_sound cl_50745 [cl_32478,cl_32467] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32478 v h) (hints_cons _ _ _ (der_32467 v h) (by intro d hd; cases hd)))
def cl_50746 : CNF.NClause := [(27,true),(69,false),(76,true),(89,false),(58,false)]
theorem der_50746 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50746 :=
  CNF.rup_sound cl_50746 [cl_32480,cl_50745] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32480 v h) (hints_cons _ _ _ (der_50745 v h) (by intro d hd; cases hd)))
def cl_50747 : CNF.NClause := [(85,false),(78,false),(69,false),(27,true),(58,false)]
theorem der_50747 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50747 :=
  CNF.rup_sound cl_50747 [cl_32490,cl_32485] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32490 v h) (hints_cons _ _ _ (der_32485 v h) (by intro d hd; cases hd)))
def cl_50750 : CNF.NClause := [(85,false),(58,false),(78,false),(69,true),(62,true)]
theorem der_50750 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50750 :=
  CNF.rup_sound cl_50750 [cl_32494,cl_32488] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32494 v h) (hints_cons _ _ _ (der_32488 v h) (by intro d hd; cases hd)))
def cl_50751 : CNF.NClause := [(62,false),(69,false),(85,false),(27,true),(58,false)]
theorem der_50751 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50751 :=
  CNF.rup_sound cl_50751 [cl_32501,cl_32495] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32501 v h) (hints_cons _ _ _ (der_32495 v h) (by intro d hd; cases hd)))
def cl_50753 : CNF.NClause := [(78,true),(62,false),(85,false),(27,false),(58,false)]
theorem der_50753 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50753 :=
  CNF.rup_sound cl_50753 [cl_32504,cl_32460] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32504 v h) (hints_cons _ _ _ (der_32460 v h) (by intro d hd; cases hd)))
def cl_50754 : CNF.NClause := [(27,true),(62,false),(85,false),(76,true),(58,false)]
theorem der_50754 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50754 :=
  CNF.rup_sound cl_50754 [cl_32505,cl_50751] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32505 v h) (hints_cons _ _ _ (der_50751 v h) (by intro d hd; cases hd)))
def cl_50755 : CNF.NClause := [(78,false),(58,false),(69,true),(27,false),(76,false)]
theorem der_50755 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50755 :=
  CNF.rup_sound cl_50755 [cl_32511,cl_32509] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32511 v h) (hints_cons _ _ _ (der_32509 v h) (by intro d hd; cases hd)))
def cl_50756 : CNF.NClause := [(62,true),(69,true),(78,false),(76,false),(58,false)]
theorem der_50756 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50756 :=
  CNF.rup_sound cl_50756 [cl_32512,cl_50755] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32512 v h) (hints_cons _ _ _ (der_50755 v h) (by intro d hd; cases hd)))
def cl_50758 : CNF.NClause := [(78,false),(69,false),(76,true),(27,false),(58,false)]
theorem der_50758 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50758 :=
  CNF.rup_sound cl_50758 [cl_32515,cl_32513] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32515 v h) (hints_cons _ _ _ (der_32513 v h) (by intro d hd; cases hd)))
def cl_50760 : CNF.NClause := [(78,false),(58,false),(76,true),(27,false),(62,true)]
theorem der_50760 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50760 :=
  CNF.rup_sound cl_50760 [cl_32519,cl_50758] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32519 v h) (hints_cons _ _ _ (der_50758 v h) (by intro d hd; cases hd)))
def cl_50761 : CNF.NClause := [(62,true),(78,false),(69,true),(27,true),(58,false)]
theorem der_50761 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50761 :=
  CNF.rup_sound cl_50761 [cl_32520,cl_50750] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32520 v h) (hints_cons _ _ _ (der_50750 v h) (by intro d hd; cases hd)))
def cl_50762 : CNF.NClause := [(76,false),(27,false),(69,false),(78,true),(58,false)]
theorem der_50762 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50762 :=
  CNF.rup_sound cl_50762 [cl_32523,cl_32496] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32523 v h) (hints_cons _ _ _ (der_32496 v h) (by intro d hd; cases hd)))
def cl_50765 : CNF.NClause := [(85,true),(58,false),(27,false),(76,false),(69,true)]
theorem der_50765 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50765 :=
  CNF.rup_sound cl_50765 [cl_32527,cl_50755] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32527 v h) (hints_cons _ _ _ (der_50755 v h) (by intro d hd; cases hd)))
def cl_50766 : CNF.NClause := [(62,false),(27,false),(69,false),(78,true),(58,false)]
theorem der_50766 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50766 :=
  CNF.rup_sound cl_50766 [cl_32529,cl_32500] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32529 v h) (hints_cons _ _ _ (der_32500 v h) (by intro d hd; cases hd)))
def cl_50767 : CNF.NClause := [(89,true),(69,false),(58,false),(62,false),(27,true)]
theorem der_50767 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50767 :=
  CNF.rup_sound cl_50767 [cl_32530,cl_32522] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32530 v h) (hints_cons _ _ _ (der_32522 v h) (by intro d hd; cases hd)))
def cl_50769 : CNF.NClause := [(78,true),(76,true),(27,false),(62,false),(58,false)]
theorem der_50769 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50769 :=
  CNF.rup_sound cl_50769 [cl_32532,cl_50753] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32532 v h) (hints_cons _ _ _ (der_50753 v h) (by intro d hd; cases hd)))
def cl_50770 : CNF.NClause := [(89,false),(81,false),(54,false),(83,false),(65,true)]
theorem der_50770 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50770 :=
  CNF.rup_sound cl_50770 [cl_32540,cl_32536] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32540 v h) (hints_cons _ _ _ (der_32536 v h) (by intro d hd; cases hd)))
def cl_50771 : CNF.NClause := [(65,false),(54,false),(89,false),(83,false),(23,true)]
theorem der_50771 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50771 :=
  CNF.rup_sound cl_50771 [cl_32549,cl_32538] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32549 v h) (hints_cons _ _ _ (der_32538 v h) (by intro d hd; cases hd)))
def cl_50772 : CNF.NClause := [(83,false),(54,false),(89,false),(65,true),(23,false)]
theorem der_50772 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50772 :=
  CNF.rup_sound cl_50772 [cl_32550,cl_32543] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32550 v h) (hints_cons _ _ _ (der_32543 v h) (by intro d hd; cases hd)))
def cl_50774 : CNF.NClause := [(65,true),(89,false),(54,false),(81,false),(67,true)]
theorem der_50774 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50774 :=
  CNF.rup_sound cl_50774 [cl_32560,cl_50770] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32560 v h) (hints_cons _ _ _ (der_50770 v h) (by intro d hd; cases hd)))
def cl_50775 : CNF.NClause := [(65,true),(54,false),(74,false),(89,false),(67,false)]
theorem der_50775 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50775 :=
  CNF.rup_sound cl_50775 [cl_32563,cl_32552] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32563 v h) (hints_cons _ _ _ (der_32552 v h) (by intro d hd; cases hd)))
def cl_50776 : CNF.NClause := [(89,false),(74,false),(67,true),(65,false),(54,false)]
theorem der_50776 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50776 :=
  CNF.rup_sound cl_50776 [cl_32565,cl_32553] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32565 v h) (hints_cons _ _ _ (der_32553 v h) (by intro d hd; cases hd)))
def cl_50777 : CNF.NClause := [(67,true),(23,true),(74,false),(54,false),(89,false)]
theorem der_50777 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50777 :=
  CNF.rup_sound cl_50777 [cl_32567,cl_50776] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32567 v h) (hints_cons _ _ _ (der_50776 v h) (by intro d hd; cases hd)))
def cl_50778 : CNF.NClause := [(65,false),(54,false),(67,false),(89,false),(74,true)]
theorem der_50778 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50778 :=
  CNF.rup_sound cl_50778 [cl_32569,cl_32555] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32569 v h) (hints_cons _ _ _ (der_32555 v h) (by intro d hd; cases hd)))
def cl_50780 : CNF.NClause := [(83,true),(54,false),(89,false),(23,false),(65,false)]
theorem der_50780 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50780 :=
  CNF.rup_sound cl_50780 [cl_32571,cl_32564] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32571 v h) (hints_cons _ _ _ (der_32564 v h) (by intro d hd; cases hd)))
def cl_50781 : CNF.NClause := [(83,false),(74,false),(54,false),(81,false),(67,true)]
theorem der_50781 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50781 :=
  CNF.rup_sound cl_50781 [cl_32577,cl_32576] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32577 v h) (hints_cons _ _ _ (der_32576 v h) (by intro d hd; cases hd)))
def cl_50782 : CNF.NClause := [(83,false),(54,false),(81,false),(74,true),(23,false)]
theorem der_50782 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50782 :=
  CNF.rup_sound cl_50782 [cl_32583,cl_32581] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32583 v h) (hints_cons _ _ _ (der_32581 v h) (by intro d hd; cases hd)))
def cl_50783 : CNF.NClause := [(54,false),(81,false),(83,false),(65,true),(67,true)]
theorem der_50783 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50783 :=
  CNF.rup_sound cl_50783 [cl_32584,cl_50781] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32584 v h) (hints_cons _ _ _ (der_50781 v h) (by intro d hd; cases hd)))
def cl_50784 : CNF.NClause := [(83,false),(74,false),(67,true),(65,false),(54,false)]
theorem der_50784 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50784 :=
  CNF.rup_sound cl_50784 [cl_32589,cl_50781] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32589 v h) (hints_cons _ _ _ (der_50781 v h) (by intro d hd; cases hd)))
def cl_50785 : CNF.NClause := [(83,false),(54,false),(74,false),(67,true),(89,true)]
theorem der_50785 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50785 :=
  CNF.rup_sound cl_50785 [cl_32591,cl_50781] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32591 v h) (hints_cons _ _ _ (der_50781 v h) (by intro d hd; cases hd)))
def cl_50786 : CNF.NClause := [(54,false),(67,false),(83,false),(74,true),(65,false)]
theorem der_50786 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50786 :=
  CNF.rup_sound cl_50786 [cl_32593,cl_32578] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32593 v h) (hints_cons _ _ _ (der_32578 v h) (by intro d hd; cases hd)))
def cl_50787 : CNF.NClause := [(83,false),(54,false),(67,false),(74,true),(81,true)]
theorem der_50787 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50787 :=
  CNF.rup_sound cl_50787 [cl_32595,cl_50786] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32595 v h) (hints_cons _ _ _ (der_50786 v h) (by intro d hd; cases hd)))
def cl_50788 : CNF.NClause := [(83,false),(65,true),(81,true),(23,false),(54,false)]
theorem der_50788 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50788 :=
  CNF.rup_sound cl_50788 [cl_32597,cl_50772] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32597 v h) (hints_cons _ _ _ (der_50772 v h) (by intro d hd; cases hd)))
def cl_50789 : CNF.NClause := [(65,true),(54,false),(83,false),(67,true),(89,true)]
theorem der_50789 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50789 :=
  CNF.rup_sound cl_50789 [cl_32598,cl_50783] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32598 v h) (hints_cons _ _ _ (der_50783 v h) (by intro d hd; cases hd)))
def cl_50790 : CNF.NClause := [(89,true),(65,false),(81,false),(74,false),(54,false)]
theorem der_50790 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50790 :=
  CNF.rup_sound cl_50790 [cl_32603,cl_32599] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32603 v h) (hints_cons _ _ _ (der_32599 v h) (by intro d hd; cases hd)))
def cl_50791 : CNF.NClause := [(67,true),(54,false),(23,false),(81,false),(74,false)]
theorem der_50791 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50791 :=
  CNF.rup_sound cl_50791 [cl_32604,cl_32576] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32604 v h) (hints_cons _ _ _ (der_32576 v h) (by intro d hd; cases hd)))
def cl_50792 : CNF.NClause := [(65,true),(81,false),(54,false),(74,false),(67,true)]
theorem der_50792 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50792 :=
  CNF.rup_sound cl_50792 [cl_32605,cl_50791] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32605 v h) (hints_cons _ _ _ (der_50791 v h) (by intro d hd; cases hd)))
def cl_50793 : CNF.NClause := [(65,false),(54,false),(81,false),(67,false),(74,true)]
theorem der_50793 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50793 :=
  CNF.rup_sound cl_50793 [cl_32607,cl_32578] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32607 v h) (hints_cons _ _ _ (der_32578 v h) (by intro d hd; cases hd)))
def cl_50794 : CNF.NClause := [(67,false),(81,false),(54,false),(74,true),(23,false)]
theorem der_50794 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50794 :=
  CNF.rup_sound cl_50794 [cl_32608,cl_32556] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32608 v h) (hints_cons _ _ _ (der_32556 v h) (by intro d hd; cases hd)))
def cl_50796 : CNF.NClause := [(65,false),(81,false),(54,false),(83,true),(89,true)]
theorem der_50796 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50796 :=
  CNF.rup_sound cl_50796 [cl_32610,cl_50790] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32610 v h) (hints_cons _ _ _ (der_50790 v h) (by intro d hd; cases hd)))
def cl_50798 : CNF.NClause := [(65,true),(81,false),(23,true),(54,false),(67,true)]
theorem der_50798 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50798 :=
  CNF.rup_sound cl_50798 [cl_32612,cl_50792] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32612 v h) (hints_cons _ _ _ (der_50792 v h) (by intro d hd; cases hd)))
def cl_50799 : CNF.NClause := [(65,false),(67,false),(74,false),(23,true),(54,false)]
theorem der_50799 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50799 :=
  CNF.rup_sound cl_50799 [cl_32614,cl_32561] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32614 v h) (hints_cons _ _ _ (der_32561 v h) (by intro d hd; cases hd)))
def cl_50800 : CNF.NClause := [(83,true),(67,false),(65,true),(54,false),(74,false)]
theorem der_50800 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50800 :=
  CNF.rup_sound cl_50800 [cl_32616,cl_50775] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32616 v h) (hints_cons _ _ _ (der_50775 v h) (by intro d hd; cases hd)))
def cl_50801 : CNF.NClause := [(65,false),(74,false),(54,false),(23,false),(67,true)]
theorem der_50801 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50801 :=
  CNF.rup_sound cl_50801 [cl_32617,cl_50776] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32617 v h) (hints_cons _ _ _ (der_50776 v h) (by intro d hd; cases hd)))
def cl_50802 : CNF.NClause := [(65,false),(54,false),(74,false),(23,true),(89,true)]
theorem der_50802 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50802 :=
  CNF.rup_sound cl_50802 [cl_32618,cl_50799] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32618 v h) (hints_cons _ _ _ (der_50799 v h) (by intro d hd; cases hd)))
def cl_50803 : CNF.NClause := [(89,true),(74,false),(23,false),(54,false),(67,true)]
theorem der_50803 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50803 :=
  CNF.rup_sound cl_50803 [cl_32619,cl_50791] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32619 v h) (hints_cons _ _ _ (der_50791 v h) (by intro d hd; cases hd)))
def cl_50804 : CNF.NClause := [(89,true),(74,false),(65,true),(54,false),(67,true)]
theorem der_50804 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50804 :=
  CNF.rup_sound cl_50804 [cl_32620,cl_50792] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32620 v h) (hints_cons _ _ _ (der_50792 v h) (by intro d hd; cases hd)))
def cl_50805 : CNF.NClause := [(65,false),(67,false),(54,false),(74,true),(23,false)]
theorem der_50805 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50805 :=
  CNF.rup_sound cl_50805 [cl_32621,cl_50794] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32621 v h) (hints_cons _ _ _ (der_50794 v h) (by intro d hd; cases hd)))
def cl_50807 : CNF.NClause := [(83,true),(89,true),(67,false),(23,true),(54,false)]
theorem der_50807 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50807 :=
  CNF.rup_sound cl_50807 [cl_32624,cl_32622] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32624 v h) (hints_cons _ _ _ (der_32622 v h) (by intro d hd; cases hd)))
def cl_50809 : CNF.NClause := [(89,true),(65,true),(23,true),(54,false),(67,true)]
theorem der_50809 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50809 :=
  CNF.rup_sound cl_50809 [cl_32628,cl_50804] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32628 v h) (hints_cons _ _ _ (der_50804 v h) (by intro d hd; cases hd)))
def cl_50810 : CNF.NClause := [(108,true),(46,false),(50,false),(49,false),(47,true)]
theorem der_50810 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50810 :=
  CNF.rup_sound cl_50810 [cl_32629,cl_36297] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32629 v h) (hints_cons _ _ _ (der_36297 v h) (by intro d hd; cases hd)))
def cl_50814 : CNF.NClause := [(120,true),(31,true),(54,true),(38,false),(58,false)]
theorem der_50814 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50814 :=
  CNF.rup_sound cl_50814 [cl_32633,cl_45954] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32633 v h) (hints_cons _ _ _ (der_45954 v h) (by intro d hd; cases hd)))
def cl_50815 : CNF.NClause := [(120,true),(31,true),(47,true),(38,false),(58,false)]
theorem der_50815 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50815 :=
  CNF.rup_sound cl_50815 [cl_23703,cl_45954] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23703 v h) (hints_cons _ _ _ (der_45954 v h) (by intro d hd; cases hd)))
def cl_50818 : CNF.NClause := [(120,true),(54,false),(58,false),(31,true),(45,true)]
theorem der_50818 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50818 :=
  CNF.rup_sound cl_50818 [cl_23706,cl_44945] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23706 v h) (hints_cons _ _ _ (der_44945 v h) (by intro d hd; cases hd)))
def cl_50820 : CNF.NClause := [(120,true),(38,true),(54,false),(31,true),(45,false)]
theorem der_50820 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50820 :=
  CNF.rup_sound cl_50820 [cl_23710,cl_45954] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23710 v h) (hints_cons _ _ _ (der_45954 v h) (by intro d hd; cases hd)))
def cl_50821 : CNF.NClause := [(120,true),(31,true),(45,false),(47,false),(38,true)]
theorem der_50821 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50821 :=
  CNF.rup_sound cl_50821 [cl_23711,cl_44945] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23711 v h) (hints_cons _ _ _ (der_44945 v h) (by intro d hd; cases hd)))
def cl_50823 : CNF.NClause := [(88,false),(82,false),(75,true),(81,false),(40,false)]
theorem der_50823 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50823 :=
  CNF.rup_sound cl_50823 [cl_32644,cl_32643] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32644 v h) (hints_cons _ _ _ (der_32643 v h) (by intro d hd; cases hd)))
def cl_50824 : CNF.NClause := [(88,false),(82,false),(40,false),(69,false),(75,true)]
theorem der_50824 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50824 :=
  CNF.rup_sound cl_50824 [cl_32651,cl_32650] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32651 v h) (hints_cons _ _ _ (der_32650 v h) (by intro d hd; cases hd)))
def cl_50826 : CNF.NClause := [(88,false),(82,false),(40,false),(75,true),(9,false)]
theorem der_50826 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50826 :=
  CNF.rup_sound cl_50826 [cl_32653,cl_50824] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32653 v h) (hints_cons _ _ _ (der_50824 v h) (by intro d hd; cases hd)))
def cl_50827 : CNF.NClause := [(69,false),(88,false),(63,false),(9,true),(40,false)]
theorem der_50827 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50827 :=
  CNF.rup_sound cl_50827 [cl_32654,cl_50728] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32654 v h) (hints_cons _ _ _ (der_50728 v h) (by intro d hd; cases hd)))
def cl_50828 : CNF.NClause := [(75,false),(40,false),(88,false),(81,false),(82,true)]
theorem der_50828 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50828 :=
  CNF.rup_sound cl_50828 [cl_32658,cl_32655] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32658 v h) (hints_cons _ _ _ (der_32655 v h) (by intro d hd; cases hd)))
def cl_50829 : CNF.NClause := [(88,false),(75,true),(81,false),(40,false),(69,false)]
theorem der_50829 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50829 :=
  CNF.rup_sound cl_50829 [cl_32661,cl_32659] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32661 v h) (hints_cons _ _ _ (der_32659 v h) (by intro d hd; cases hd)))
def cl_50830 : CNF.NClause := [(40,false),(69,true),(88,false),(81,false),(63,false)]
theorem der_50830 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50830 :=
  CNF.rup_sound cl_50830 [cl_32662,cl_32656] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32662 v h) (hints_cons _ _ _ (der_32656 v h) (by intro d hd; cases hd)))
def cl_50831 : CNF.NClause := [(81,false),(69,true),(88,false),(40,false),(75,true)]
theorem der_50831 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50831 :=
  CNF.rup_sound cl_50831 [cl_32663,cl_50823] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32663 v h) (hints_cons _ _ _ (der_50823 v h) (by intro d hd; cases hd)))
def cl_50832 : CNF.NClause := [(88,false),(75,false),(69,false),(81,true),(40,false)]
theorem der_50832 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50832 :=
  CNF.rup_sound cl_50832 [cl_32666,cl_32664] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32666 v h) (hints_cons _ _ _ (der_32664 v h) (by intro d hd; cases hd)))
def cl_50833 : CNF.NClause := [(75,false),(40,false),(88,false),(63,false),(81,true)]
theorem der_50833 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50833 :=
  CNF.rup_sound cl_50833 [cl_32667,cl_32422] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32667 v h) (hints_cons _ _ _ (der_32422 v h) (by intro d hd; cases hd)))
def cl_50834 : CNF.NClause := [(88,false),(81,true),(9,true),(40,false),(75,false)]
theorem der_50834 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50834 :=
  CNF.rup_sound cl_50834 [cl_32669,cl_32422] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32669 v h) (hints_cons _ _ _ (der_32422 v h) (by intro d hd; cases hd)))
def cl_50835 : CNF.NClause := [(88,false),(69,false),(63,false),(40,false),(75,true)]
theorem der_50835 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50835 :=
  CNF.rup_sound cl_50835 [cl_32670,cl_50827] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32670 v h) (hints_cons _ _ _ (der_50827 v h) (by intro d hd; cases hd)))
def cl_50836 : CNF.NClause := [(88,false),(63,true),(75,true),(40,false),(69,false)]
theorem der_50836 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50836 :=
  CNF.rup_sound cl_50836 [cl_32671,cl_50824] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32671 v h) (hints_cons _ _ _ (der_50824 v h) (by intro d hd; cases hd)))
def cl_50838 : CNF.NClause := [(88,false),(69,true),(40,false),(75,true),(9,false)]
theorem der_50838 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50838 :=
  CNF.rup_sound cl_50838 [cl_32673,cl_50826] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32673 v h) (hints_cons _ _ _ (der_50826 v h) (by intro d hd; cases hd)))
def cl_50839 : CNF.NClause := [(40,false),(82,true),(69,true),(88,false),(75,true)]
theorem der_50839 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50839 :=
  CNF.rup_sound cl_50839 [cl_32674,cl_50838] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32674 v h) (hints_cons _ _ _ (der_50838 v h) (by intro d hd; cases hd)))
def cl_50840 : CNF.NClause := [(82,false),(75,false),(40,false),(81,false),(69,true)]
theorem der_50840 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50840 :=
  CNF.rup_sound cl_50840 [cl_32679,cl_32677] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32679 v h) (hints_cons _ _ _ (der_32677 v h) (by intro d hd; cases hd)))
def cl_50841 : CNF.NClause := [(40,false),(69,true),(81,false),(63,false),(82,false)]
theorem der_50841 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50841 :=
  CNF.rup_sound cl_50841 [cl_32682,cl_32677] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32682 v h) (hints_cons _ _ _ (der_32677 v h) (by intro d hd; cases hd)))
def cl_50842 : CNF.NClause := [(82,false),(40,false),(81,false),(69,true),(88,true)]
theorem der_50842 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50842 :=
  CNF.rup_sound cl_50842 [cl_32684,cl_50841] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32684 v h) (hints_cons _ _ _ (der_50841 v h) (by intro d hd; cases hd)))
def cl_50843 : CNF.NClause := [(75,false),(40,false),(69,false),(82,false),(81,true)]
theorem der_50843 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50843 :=
  CNF.rup_sound cl_50843 [cl_32687,cl_32645] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32687 v h) (hints_cons _ _ _ (der_32645 v h) (by intro d hd; cases hd)))
def cl_50844 : CNF.NClause := [(75,false),(40,false),(63,false),(82,false),(81,true)]
theorem der_50844 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50844 :=
  CNF.rup_sound cl_50844 [cl_32688,cl_50730] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32688 v h) (hints_cons _ _ _ (der_50730 v h) (by intro d hd; cases hd)))
def cl_50845 : CNF.NClause := [(81,true),(75,false),(40,false),(82,false),(9,true)]
theorem der_50845 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50845 :=
  CNF.rup_sound cl_50845 [cl_32690,cl_50730] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32690 v h) (hints_cons _ _ _ (der_50730 v h) (by intro d hd; cases hd)))
def cl_50846 : CNF.NClause := [(81,true),(69,false),(63,false),(82,false),(40,false)]
theorem der_50846 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50846 :=
  CNF.rup_sound cl_50846 [cl_32691,cl_50730] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32691 v h) (hints_cons _ _ _ (der_50730 v h) (by intro d hd; cases hd)))
def cl_50847 : CNF.NClause := [(69,false),(9,true),(40,false),(82,false),(88,true)]
theorem der_50847 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50847 :=
  CNF.rup_sound cl_50847 [cl_32693,cl_47453] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32693 v h) (hints_cons _ _ _ (der_47453 v h) (by intro d hd; cases hd)))
def cl_50848 : CNF.NClause := [(81,true),(82,false),(40,false),(63,false),(69,true)]
theorem der_50848 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50848 :=
  CNF.rup_sound cl_50848 [cl_32694,cl_50730] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32694 v h) (hints_cons _ _ _ (der_50730 v h) (by intro d hd; cases hd)))
def cl_50849 : CNF.NClause := [(81,true),(40,false),(82,false),(69,true),(9,false)]
theorem der_50849 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50849 :=
  CNF.rup_sound cl_50849 [cl_32695,cl_50848] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32695 v h) (hints_cons _ _ _ (der_50848 v h) (by intro d hd; cases hd)))
def cl_50850 : CNF.NClause := [(82,false),(40,false),(69,true),(81,true),(75,true)]
theorem der_50850 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50850 :=
  CNF.rup_sound cl_50850 [cl_32696,cl_50848] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32696 v h) (hints_cons _ _ _ (der_50848 v h) (by intro d hd; cases hd)))
def cl_50851 : CNF.NClause := [(75,false),(40,false),(88,true),(69,false),(81,false)]
theorem der_50851 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50851 :=
  CNF.rup_sound cl_50851 [cl_32699,cl_32698] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32699 v h) (hints_cons _ _ _ (der_32698 v h) (by intro d hd; cases hd)))
def cl_50852 : CNF.NClause := [(75,false),(63,false),(40,false),(81,false),(69,true)]
theorem der_50852 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50852 :=
  CNF.rup_sound cl_50852 [cl_32700,cl_50731] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32700 v h) (hints_cons _ _ _ (der_50731 v h) (by intro d hd; cases hd)))
def cl_50854 : CNF.NClause := [(40,false),(75,false),(81,false),(69,true),(82,true)]
theorem der_50854 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50854 :=
  CNF.rup_sound cl_50854 [cl_32702,cl_50852] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32702 v h) (hints_cons _ _ _ (der_50852 v h) (by intro d hd; cases hd)))
def cl_50855 : CNF.NClause := [(40,false),(63,true),(81,false),(69,true),(88,true)]
theorem der_50855 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50855 :=
  CNF.rup_sound cl_50855 [cl_32707,cl_50842] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32707 v h) (hints_cons _ _ _ (der_50842 v h) (by intro d hd; cases hd)))
def cl_50856 : CNF.NClause := [(75,false),(40,false),(69,false),(81,true),(9,true)]
theorem der_50856 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50856 :=
  CNF.rup_sound cl_50856 [cl_32709,cl_50832] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32709 v h) (hints_cons _ _ _ (der_50832 v h) (by intro d hd; cases hd)))
def cl_50857 : CNF.NClause := [(81,true),(63,false),(75,false),(40,false),(69,true)]
theorem der_50857 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50857 :=
  CNF.rup_sound cl_50857 [cl_32710,cl_50732] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32710 v h) (hints_cons _ _ _ (der_50732 v h) (by intro d hd; cases hd)))
def cl_50858 : CNF.NClause := [(81,true),(75,false),(69,true),(9,true),(40,false)]
theorem der_50858 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50858 :=
  CNF.rup_sound cl_50858 [cl_32711,cl_50732] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32711 v h) (hints_cons _ _ _ (der_50732 v h) (by intro d hd; cases hd)))
def cl_50859 : CNF.NClause := [(81,true),(40,false),(88,true),(69,false),(9,true)]
theorem der_50859 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50859 :=
  CNF.rup_sound cl_50859 [cl_32713,cl_50856] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32713 v h) (hints_cons _ _ _ (der_50856 v h) (by intro d hd; cases hd)))
def cl_50860 : CNF.NClause := [(81,true),(40,false),(63,false),(69,true),(82,true)]
theorem der_50860 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50860 :=
  CNF.rup_sound cl_50860 [cl_32714,cl_50857] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32714 v h) (hints_cons _ _ _ (der_50857 v h) (by intro d hd; cases hd)))
def cl_50862 : CNF.NClause := [(88,false),(68,false),(60,false),(74,false),(29,true)]
theorem der_50862 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50862 :=
  CNF.rup_sound cl_50862 [cl_32741,cl_37956] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32741 v h) (hints_cons _ _ _ (der_37956 v h) (by intro d hd; cases hd)))
def cl_50863 : CNF.NClause := [(60,false),(88,false),(68,false),(74,true),(29,false)]
theorem der_50863 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50863 :=
  CNF.rup_sound cl_50863 [cl_32748,cl_32746] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32748 v h) (hints_cons _ _ _ (der_32746 v h) (by intro d hd; cases hd)))
def cl_50864 : CNF.NClause := [(60,false),(88,false),(68,true),(86,true),(62,false)]
theorem der_50864 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50864 :=
  CNF.rup_sound cl_50864 [cl_32751,cl_32743] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32751 v h) (hints_cons _ _ _ (der_32743 v h) (by intro d hd; cases hd)))
def cl_50865 : CNF.NClause := [(88,false),(68,true),(86,true),(29,false),(60,false)]
theorem der_50865 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50865 :=
  CNF.rup_sound cl_50865 [cl_32752,cl_50864] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32752 v h) (hints_cons _ _ _ (der_50864 v h) (by intro d hd; cases hd)))
def cl_50866 : CNF.NClause := [(62,false),(74,false),(29,false),(60,false),(68,true)]
theorem der_50866 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50866 :=
  CNF.rup_sound cl_50866 [cl_32796,cl_32767] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32796 v h) (hints_cons _ _ _ (der_32767 v h) (by intro d hd; cases hd)))
def cl_50867 : CNF.NClause := [(60,false),(29,false),(74,false),(68,true),(86,true)]
theorem der_50867 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50867 :=
  CNF.rup_sound cl_50867 [cl_32798,cl_50866] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32798 v h) (hints_cons _ _ _ (der_50866 v h) (by intro d hd; cases hd)))
def cl_50868 : CNF.NClause := [(60,false),(68,true),(80,true),(74,false),(86,true)]
theorem der_50868 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50868 :=
  CNF.rup_sound cl_50868 [cl_32799,cl_50867] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32799 v h) (hints_cons _ _ _ (der_50867 v h) (by intro d hd; cases hd)))
def cl_50869 : CNF.NClause := [(76,false),(91,false),(84,false),(55,false),(63,true)]
theorem der_50869 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50869 :=
  CNF.rup_sound cl_50869 [cl_32814,cl_32813] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32814 v h) (hints_cons _ _ _ (der_32813 v h) (by intro d hd; cases hd)))
def cl_50870 : CNF.NClause := [(76,true),(63,false),(84,false),(55,false),(91,false)]
theorem der_50870 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50870 :=
  CNF.rup_sound cl_50870 [cl_32818,cl_32817] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32818 v h) (hints_cons _ _ _ (der_32817 v h) (by intro d hd; cases hd)))
def cl_50874 : CNF.NClause := [(63,true),(67,true),(91,false),(55,false),(76,false)]
theorem der_50874 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50874 :=
  CNF.rup_sound cl_50874 [cl_32836,cl_50869] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32836 v h) (hints_cons _ _ _ (der_50869 v h) (by intro d hd; cases hd)))
def cl_50875 : CNF.NClause := [(63,false),(76,true),(67,false),(91,false),(55,false)]
theorem der_50875 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50875 :=
  CNF.rup_sound cl_50875 [cl_32838,cl_32825] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32838 v h) (hints_cons _ _ _ (der_32825 v h) (by intro d hd; cases hd)))
def cl_50876 : CNF.NClause := [(76,true),(63,false),(55,false),(91,false),(24,false)]
theorem der_50876 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50876 :=
  CNF.rup_sound cl_50876 [cl_32840,cl_50870] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32840 v h) (hints_cons _ _ _ (der_50870 v h) (by intro d hd; cases hd)))
def cl_50877 : CNF.NClause := [(76,true),(63,false),(55,false),(91,false),(84,true)]
theorem der_50877 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50877 :=
  CNF.rup_sound cl_50877 [cl_32841,cl_50875] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32841 v h) (hints_cons _ _ _ (der_50875 v h) (by intro d hd; cases hd)))
def cl_50878 : CNF.NClause := [(76,true),(55,false),(91,false),(84,true),(24,true)]
theorem der_50878 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50878 :=
  CNF.rup_sound cl_50878 [cl_32843,cl_50877] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32843 v h) (hints_cons _ _ _ (der_50877 v h) (by intro d hd; cases hd)))
def cl_50879 : CNF.NClause := [(80,false),(67,false),(84,false),(24,true),(55,false)]
theorem der_50879 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50879 :=
  CNF.rup_sound cl_50879 [cl_32849,cl_32847] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32849 v h) (hints_cons _ _ _ (der_32847 v h) (by intro d hd; cases hd)))
def cl_50880 : CNF.NClause := [(80,false),(55,false),(63,false),(84,false),(67,true)]
theorem der_50880 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50880 :=
  CNF.rup_sound cl_50880 [cl_32851,cl_32845] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32851 v h) (hints_cons _ _ _ (der_32845 v h) (by intro d hd; cases hd)))
def cl_50881 : CNF.NClause := [(80,false),(24,true),(55,false),(84,false),(67,true)]
theorem der_50881 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50881 :=
  CNF.rup_sound cl_50881 [cl_32853,cl_50880] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32853 v h) (hints_cons _ _ _ (der_50880 v h) (by intro d hd; cases hd)))
def cl_50882 : CNF.NClause := [(80,true),(76,false),(55,false),(84,false),(63,true)]
theorem der_50882 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50882 :=
  CNF.rup_sound cl_50882 [cl_32859,cl_32858] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32859 v h) (hints_cons _ _ _ (der_32858 v h) (by intro d hd; cases hd)))
def cl_50883 : CNF.NClause := [(67,false),(63,true),(55,false),(84,false),(24,true)]
theorem der_50883 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50883 :=
  CNF.rup_sound cl_50883 [cl_32863,cl_50879] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32863 v h) (hints_cons _ _ _ (der_50879 v h) (by intro d hd; cases hd)))
def cl_50884 : CNF.NClause := [(84,false),(55,false),(63,false),(24,false),(67,true)]
theorem der_50884 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50884 :=
  CNF.rup_sound cl_50884 [cl_32864,cl_32857] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32864 v h) (hints_cons _ _ _ (der_32857 v h) (by intro d hd; cases hd)))
def cl_50885 : CNF.NClause := [(84,false),(67,true),(63,false),(76,true),(55,false)]
theorem der_50885 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50885 :=
  CNF.rup_sound cl_50885 [cl_32865,cl_50880] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32865 v h) (hints_cons _ _ _ (der_50880 v h) (by intro d hd; cases hd)))
def cl_50886 : CNF.NClause := [(80,false),(76,false),(55,false),(63,false),(84,true)]
theorem der_50886 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50886 :=
  CNF.rup_sound cl_50886 [cl_32872,cl_32822] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32872 v h) (hints_cons _ _ _ (der_32822 v h) (by intro d hd; cases hd)))
def cl_50888 : CNF.NClause := [(63,true),(91,true),(24,false),(55,false),(80,false)]
theorem der_50888 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50888 :=
  CNF.rup_sound cl_50888 [cl_32880,cl_32876] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32880 v h) (hints_cons _ _ _ (der_32876 v h) (by intro d hd; cases hd)))
def cl_50889 : CNF.NClause := [(76,false),(55,false),(67,false),(24,false),(63,true)]
theorem der_50889 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50889 :=
  CNF.rup_sound cl_50889 [cl_32882,cl_32869] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32882 v h) (hints_cons _ _ _ (der_32869 v h) (by intro d hd; cases hd)))
def cl_50890 : CNF.NClause := [(76,false),(67,false),(55,false),(63,true),(91,true)]
theorem der_50890 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50890 :=
  CNF.rup_sound cl_50890 [cl_32883,cl_32870] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32883 v h) (hints_cons _ _ _ (der_32870 v h) (by intro d hd; cases hd)))
def cl_50892 : CNF.NClause := [(63,true),(24,true),(55,false),(76,false),(67,true)]
theorem der_50892 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50892 :=
  CNF.rup_sound cl_50892 [cl_32886,cl_50874] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32886 v h) (hints_cons _ _ _ (der_50874 v h) (by intro d hd; cases hd)))
def cl_50893 : CNF.NClause := [(63,false),(91,true),(55,false),(67,false),(24,true)]
theorem der_50893 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50893 :=
  CNF.rup_sound cl_50893 [cl_32888,cl_32875] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32888 v h) (hints_cons _ _ _ (der_32875 v h) (by intro d hd; cases hd)))
def cl_50894 : CNF.NClause := [(67,false),(63,true),(80,true),(24,false),(55,false)]
theorem der_50894 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50894 :=
  CNF.rup_sound cl_50894 [cl_32889,cl_32839] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32889 v h) (hints_cons _ _ _ (der_32839 v h) (by intro d hd; cases hd)))
def cl_50895 : CNF.NClause := [(67,false),(55,false),(76,true),(80,true),(63,true)]
theorem der_50895 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50895 :=
  CNF.rup_sound cl_50895 [cl_32890,cl_50894] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32890 v h) (hints_cons _ _ _ (der_50894 v h) (by intro d hd; cases hd)))
def cl_50896 : CNF.NClause := [(76,true),(63,false),(55,false),(80,true),(24,false)]
theorem der_50896 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50896 :=
  CNF.rup_sound cl_50896 [cl_32891,cl_50876] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32891 v h) (hints_cons _ _ _ (der_50876 v h) (by intro d hd; cases hd)))
def cl_50897 : CNF.NClause := [(91,true),(55,false),(63,false),(76,true),(24,true)]
theorem der_50897 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50897 :=
  CNF.rup_sound cl_50897 [cl_32892,cl_50893] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32892 v h) (hints_cons _ _ _ (der_50893 v h) (by intro d hd; cases hd)))
def cl_50899 : CNF.NClause := [(15,true),(79,false),(46,false),(81,false),(92,false)]
theorem der_50899 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50899 :=
  CNF.rup_sound cl_50899 [cl_32902,cl_37617] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32902 v h) (hints_cons _ _ _ (der_37617 v h) (by intro d hd; cases hd)))
def cl_50900 : CNF.NClause := [(15,true),(81,false),(77,false),(46,false),(92,false)]
theorem der_50900 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50900 :=
  CNF.rup_sound cl_50900 [cl_32907,cl_50899] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32907 v h) (hints_cons _ _ _ (der_50899 v h) (by intro d hd; cases hd)))
def cl_50901 : CNF.NClause := [(77,true),(79,false),(92,false),(80,false),(46,false)]
theorem der_50901 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50901 :=
  CNF.rup_sound cl_50901 [cl_32914,cl_32894] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32914 v h) (hints_cons _ _ _ (der_32894 v h) (by intro d hd; cases hd)))
def cl_50902 : CNF.NClause := [(92,false),(46,false),(78,false),(80,false),(77,true)]
theorem der_50902 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50902 :=
  CNF.rup_sound cl_50902 [cl_32917,cl_32895] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32917 v h) (hints_cons _ _ _ (der_32895 v h) (by intro d hd; cases hd)))
def cl_50903 : CNF.NClause := [(92,false),(46,false),(15,false),(80,false),(77,true)]
theorem der_50903 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50903 :=
  CNF.rup_sound cl_50903 [cl_32918,cl_50901] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32918 v h) (hints_cons _ _ _ (der_50901 v h) (by intro d hd; cases hd)))
def cl_50904 : CNF.NClause := [(77,true),(46,false),(78,false),(79,false),(92,false)]
theorem der_50904 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50904 :=
  CNF.rup_sound cl_50904 [cl_32922,cl_32910] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32922 v h) (hints_cons _ _ _ (der_32910 v h) (by intro d hd; cases hd)))
def cl_50905 : CNF.NClause := [(46,false),(78,false),(15,false),(92,false),(77,true)]
theorem der_50905 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50905 :=
  CNF.rup_sound cl_50905 [cl_32927,cl_32910] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32927 v h) (hints_cons _ _ _ (der_32910 v h) (by intro d hd; cases hd)))
def cl_50906 : CNF.NClause := [(92,false),(46,false),(78,false),(81,true),(77,true)]
theorem der_50906 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50906 :=
  CNF.rup_sound cl_50906 [cl_32928,cl_50905] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32928 v h) (hints_cons _ _ _ (der_50905 v h) (by intro d hd; cases hd)))
def cl_50907 : CNF.NClause := [(78,true),(77,false),(46,false),(15,false),(92,false)]
theorem der_50907 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50907 :=
  CNF.rup_sound cl_50907 [cl_32929,cl_32906] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32929 v h) (hints_cons _ _ _ (der_32906 v h) (by intro d hd; cases hd)))
def cl_50908 : CNF.NClause := [(78,true),(15,false),(92,false),(79,true),(46,false)]
theorem der_50908 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50908 :=
  CNF.rup_sound cl_50908 [cl_32931,cl_50907] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32931 v h) (hints_cons _ _ _ (der_50907 v h) (by intro d hd; cases hd)))
def cl_50909 : CNF.NClause := [(79,false),(46,false),(81,false),(80,false),(77,true)]
theorem der_50909 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50909 :=
  CNF.rup_sound cl_50909 [cl_32936,cl_32933] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32936 v h) (hints_cons _ _ _ (der_32933 v h) (by intro d hd; cases hd)))
def cl_50910 : CNF.NClause := [(80,false),(46,false),(81,false),(78,false),(92,true)]
theorem der_50910 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50910 :=
  CNF.rup_sound cl_50910 [cl_32939,cl_32938] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32939 v h) (hints_cons _ _ _ (der_32938 v h) (by intro d hd; cases hd)))
def cl_50911 : CNF.NClause := [(81,false),(77,false),(46,false),(80,false),(92,true)]
theorem der_50911 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50911 :=
  CNF.rup_sound cl_50911 [cl_32941,cl_32937] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32941 v h) (hints_cons _ _ _ (der_32937 v h) (by intro d hd; cases hd)))
def cl_50912 : CNF.NClause := [(80,false),(78,true),(15,false),(81,false),(46,false)]
theorem der_50912 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50912 :=
  CNF.rup_sound cl_50912 [cl_32942,cl_32940] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32942 v h) (hints_cons _ _ _ (der_32940 v h) (by intro d hd; cases hd)))
def cl_50913 : CNF.NClause := [(79,false),(78,false),(46,false),(81,false),(77,true)]
theorem der_50913 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50913 :=
  CNF.rup_sound cl_50913 [cl_32945,cl_32070] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32945 v h) (hints_cons _ _ _ (der_32070 v h) (by intro d hd; cases hd)))
def cl_50914 : CNF.NClause := [(77,false),(79,false),(46,false),(81,false),(92,true)]
theorem der_50914 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50914 :=
  CNF.rup_sound cl_50914 [cl_32947,cl_50911] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32947 v h) (hints_cons _ _ _ (der_50911 v h) (by intro d hd; cases hd)))
def cl_50915 : CNF.NClause := [(15,true),(79,false),(46,false),(81,false),(77,true)]
theorem der_50915 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50915 :=
  CNF.rup_sound cl_50915 [cl_32949,cl_50909] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32949 v h) (hints_cons _ _ _ (der_50909 v h) (by intro d hd; cases hd)))
def cl_50917 : CNF.NClause := [(78,true),(81,false),(77,false),(46,false),(92,true)]
theorem der_50917 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50917 :=
  CNF.rup_sound cl_50917 [cl_32954,cl_50914] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32954 v h) (hints_cons _ _ _ (der_50914 v h) (by intro d hd; cases hd)))
def cl_50918 : CNF.NClause := [(79,false),(78,false),(46,false),(80,false),(77,true)]
theorem der_50918 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50918 :=
  CNF.rup_sound cl_50918 [cl_32958,cl_32957] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32958 v h) (hints_cons _ _ _ (der_32957 v h) (by intro d hd; cases hd)))
def cl_50919 : CNF.NClause := [(79,false),(46,false),(15,false),(80,false),(77,true)]
theorem der_50919 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50919 :=
  CNF.rup_sound cl_50919 [cl_32961,cl_50918] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32961 v h) (hints_cons _ _ _ (der_50918 v h) (by intro d hd; cases hd)))
def cl_50921 : CNF.NClause := [(80,false),(46,false),(15,true),(78,false),(77,true)]
theorem der_50921 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50921 :=
  CNF.rup_sound cl_50921 [cl_32966,cl_50902] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32966 v h) (hints_cons _ _ _ (der_50902 v h) (by intro d hd; cases hd)))
def cl_50922 : CNF.NClause := [(78,true),(46,false),(77,false),(15,false),(80,false)]
theorem der_50922 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50922 :=
  CNF.rup_sound cl_50922 [cl_32967,cl_32959] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32967 v h) (hints_cons _ _ _ (der_32959 v h) (by intro d hd; cases hd)))
def cl_50923 : CNF.NClause := [(80,false),(78,true),(77,false),(46,false),(92,true)]
theorem der_50923 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50923 :=
  CNF.rup_sound cl_50923 [cl_32968,cl_32960] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32968 v h) (hints_cons _ _ _ (der_32960 v h) (by intro d hd; cases hd)))
def cl_50924 : CNF.NClause := [(78,true),(15,false),(80,false),(79,true),(46,false)]
theorem der_50924 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50924 :=
  CNF.rup_sound cl_50924 [cl_32969,cl_50922] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32969 v h) (hints_cons _ _ _ (der_50922 v h) (by intro d hd; cases hd)))
def cl_50925 : CNF.NClause := [(77,true),(79,false),(15,true),(78,false),(46,false)]
theorem der_50925 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50925 :=
  CNF.rup_sound cl_50925 [cl_32973,cl_50904] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32973 v h) (hints_cons _ _ _ (der_50904 v h) (by intro d hd; cases hd)))
def cl_50926 : CNF.NClause := [(79,false),(46,false),(78,true),(77,false),(15,false)]
theorem der_50926 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50926 :=
  CNF.rup_sound cl_50926 [cl_32974,cl_50922] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32974 v h) (hints_cons _ _ _ (der_50922 v h) (by intro d hd; cases hd)))
def cl_50927 : CNF.NClause := [(80,false),(42,false),(66,true),(83,false),(90,false)]
theorem der_50927 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50927 :=
  CNF.rup_sound cl_50927 [cl_32988,cl_32987] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32988 v h) (hints_cons _ _ _ (der_32987 v h) (by intro d hd; cases hd)))
def cl_50929 : CNF.NClause := [(83,false),(90,false),(11,false),(42,false),(66,true)]
theorem der_50929 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50929 :=
  CNF.rup_sound cl_50929 [cl_32995,cl_32987] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32995 v h) (hints_cons _ _ _ (der_32987 v h) (by intro d hd; cases hd)))
def cl_50930 : CNF.NClause := [(83,false),(42,false),(90,false),(66,true),(72,true)]
theorem der_50930 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50930 :=
  CNF.rup_sound cl_50930 [cl_32996,cl_50929] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32996 v h) (hints_cons _ _ _ (der_50929 v h) (by intro d hd; cases hd)))
def cl_50931 : CNF.NClause := [(80,false),(90,false),(11,false),(66,true),(42,false)]
theorem der_50931 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50931 :=
  CNF.rup_sound cl_50931 [cl_33004,cl_32987] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33004 v h) (hints_cons _ _ _ (der_32987 v h) (by intro d hd; cases hd)))
def cl_50932 : CNF.NClause := [(90,false),(42,false),(69,true),(80,false),(66,true)]
theorem der_50932 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50932 :=
  CNF.rup_sound cl_50932 [cl_33005,cl_50931] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33005 v h) (hints_cons _ _ _ (der_50931 v h) (by intro d hd; cases hd)))
def cl_50933 : CNF.NClause := [(90,false),(42,false),(69,false),(72,false),(66,true)]
theorem der_50933 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50933 :=
  CNF.rup_sound cl_50933 [cl_33008,cl_33007] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33008 v h) (hints_cons _ _ _ (der_33007 v h) (by intro d hd; cases hd)))
def cl_50934 : CNF.NClause := [(69,false),(42,false),(90,false),(11,false),(66,true)]
theorem der_50934 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50934 :=
  CNF.rup_sound cl_50934 [cl_33014,cl_50933] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33014 v h) (hints_cons _ _ _ (der_50933 v h) (by intro d hd; cases hd)))
def cl_50935 : CNF.NClause := [(69,false),(42,false),(90,false),(80,true),(66,true)]
theorem der_50935 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50935 :=
  CNF.rup_sound cl_50935 [cl_33015,cl_50933] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33015 v h) (hints_cons _ _ _ (der_50933 v h) (by intro d hd; cases hd)))
def cl_50936 : CNF.NClause := [(42,false),(90,false),(11,false),(66,false),(69,true)]
theorem der_50936 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50936 :=
  CNF.rup_sound cl_50936 [cl_33016,cl_32993] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33016 v h) (hints_cons _ _ _ (der_32993 v h) (by intro d hd; cases hd)))
def cl_50937 : CNF.NClause := [(83,true),(42,false),(90,false),(80,true),(69,true)]
theorem der_50937 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50937 :=
  CNF.rup_sound cl_50937 [cl_33018,cl_33012] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33018 v h) (hints_cons _ _ _ (der_33012 v h) (by intro d hd; cases hd)))
def cl_50938 : CNF.NClause := [(69,false),(42,false),(80,false),(83,false),(66,true)]
theorem der_50938 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50938 :=
  CNF.rup_sound cl_50938 [cl_33023,cl_33019] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33023 v h) (hints_cons _ _ _ (der_33019 v h) (by intro d hd; cases hd)))
def cl_50939 : CNF.NClause := [(80,false),(83,false),(11,true),(42,false),(90,true)]
theorem der_50939 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50939 :=
  CNF.rup_sound cl_50939 [cl_33026,cl_46235] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33026 v h) (hints_cons _ _ _ (der_46235 v h) (by intro d hd; cases hd)))
def cl_50940 : CNF.NClause := [(69,false),(42,false),(72,false),(83,false),(66,true)]
theorem der_50940 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50940 :=
  CNF.rup_sound cl_50940 [cl_33029,cl_33019] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33029 v h) (hints_cons _ _ _ (der_33019 v h) (by intro d hd; cases hd)))
def cl_50941 : CNF.NClause := [(83,false),(69,false),(42,false),(11,false),(66,true)]
theorem der_50941 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50941 :=
  CNF.rup_sound cl_50941 [cl_33035,cl_50940] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33035 v h) (hints_cons _ _ _ (der_50940 v h) (by intro d hd; cases hd)))
def cl_50942 : CNF.NClause := [(80,true),(83,false),(69,false),(42,false),(66,true)]
theorem der_50942 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50942 :=
  CNF.rup_sound cl_50942 [cl_33036,cl_50941] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33036 v h) (hints_cons _ _ _ (der_50941 v h) (by intro d hd; cases hd)))
def cl_50943 : CNF.NClause := [(83,true),(66,false),(69,false),(80,false),(42,false)]
theorem der_50943 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50943 :=
  CNF.rup_sound cl_50943 [cl_33046,cl_33045] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33046 v h) (hints_cons _ _ _ (der_33045 v h) (by intro d hd; cases hd)))
def cl_50944 : CNF.NClause := [(69,false),(42,false),(80,false),(11,false),(83,true)]
theorem der_50944 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50944 :=
  CNF.rup_sound cl_50944 [cl_33047,cl_50943] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33047 v h) (hints_cons _ _ _ (der_50943 v h) (by intro d hd; cases hd)))
def cl_50945 : CNF.NClause := [(83,true),(66,false),(80,false),(11,false),(42,false)]
theorem der_50945 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50945 :=
  CNF.rup_sound cl_50945 [cl_33049,cl_50944] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33049 v h) (hints_cons _ _ _ (der_50944 v h) (by intro d hd; cases hd)))
def cl_50946 : CNF.NClause := [(83,true),(42,false),(80,false),(66,false),(72,true)]
theorem der_50946 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50946 :=
  CNF.rup_sound cl_50946 [cl_33050,cl_50943] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33050 v h) (hints_cons _ _ _ (der_50943 v h) (by intro d hd; cases hd)))
def cl_50947 : CNF.NClause := [(83,true),(80,false),(11,false),(72,true),(42,false)]
theorem der_50947 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50947 :=
  CNF.rup_sound cl_50947 [cl_33051,cl_50945] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33051 v h) (hints_cons _ _ _ (der_50945 v h) (by intro d hd; cases hd)))
def cl_50948 : CNF.NClause := [(42,false),(66,true),(69,true),(80,false),(11,true)]
theorem der_50948 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50948 :=
  CNF.rup_sound cl_50948 [cl_33052,cl_33044] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33052 v h) (hints_cons _ _ _ (der_33044 v h) (by intro d hd; cases hd)))
def cl_50950 : CNF.NClause := [(69,false),(42,false),(72,false),(80,true),(66,true)]
theorem der_50950 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50950 :=
  CNF.rup_sound cl_50950 [cl_33056,cl_50933] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33056 v h) (hints_cons _ _ _ (der_50933 v h) (by intro d hd; cases hd)))
def cl_50951 : CNF.NClause := [(66,false),(42,false),(72,false),(11,false),(69,true)]
theorem der_50951 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50951 :=
  CNF.rup_sound cl_50951 [cl_33057,cl_33030] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33057 v h) (hints_cons _ _ _ (der_33030 v h) (by intro d hd; cases hd)))
def cl_50953 : CNF.NClause := [(69,false),(66,false),(42,false),(83,true),(90,true)]
theorem der_50953 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50953 :=
  CNF.rup_sound cl_50953 [cl_33061,cl_50943] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33061 v h) (hints_cons _ _ _ (der_50943 v h) (by intro d hd; cases hd)))
def cl_50955 : CNF.NClause := [(66,false),(69,true),(11,false),(42,false),(83,true)]
theorem der_50955 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50955 :=
  CNF.rup_sound cl_50955 [cl_33063,cl_50945] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33063 v h) (hints_cons _ _ _ (der_50945 v h) (by intro d hd; cases hd)))
def cl_50956 : CNF.NClause := [(66,false),(42,false),(69,true),(72,true),(83,true)]
theorem der_50956 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50956 :=
  CNF.rup_sound cl_50956 [cl_33064,cl_50955] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33064 v h) (hints_cons _ _ _ (der_50955 v h) (by intro d hd; cases hd)))
def cl_50961 : CNF.NClause := [(75,false),(34,false),(80,true),(85,false),(87,false)]
theorem der_50961 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50961 :=
  CNF.rup_sound cl_50961 [cl_33073,cl_33071] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33073 v h) (hints_cons _ _ _ (der_33071 v h) (by intro d hd; cases hd)))
def cl_50962 : CNF.NClause := [(87,false),(85,false),(34,false),(80,true),(70,false)]
theorem der_50962 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50962 :=
  CNF.rup_sound cl_50962 [cl_33075,cl_50425] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33075 v h) (hints_cons _ _ _ (der_50425 v h) (by intro d hd; cases hd)))
def cl_50965 : CNF.NClause := [(70,true),(34,false),(85,false),(87,false),(80,true)]
theorem der_50965 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50965 :=
  CNF.rup_sound cl_50965 [cl_33079,cl_50961] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33079 v h) (hints_cons _ _ _ (der_50961 v h) (by intro d hd; cases hd)))
def cl_50968 : CNF.NClause := [(75,false),(34,false),(87,false),(65,true),(70,false)]
theorem der_50968 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50968 :=
  CNF.rup_sound cl_50968 [cl_33088,cl_50425] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33088 v h) (hints_cons _ _ _ (der_50425 v h) (by intro d hd; cases hd)))
def cl_50970 : CNF.NClause := [(65,false),(34,false),(87,false),(80,true),(70,false)]
theorem der_50970 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50970 :=
  CNF.rup_sound cl_50970 [cl_33094,cl_49393] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33094 v h) (hints_cons _ _ _ (der_49393 v h) (by intro d hd; cases hd)))
def cl_50971 : CNF.NClause := [(87,false),(34,false),(3,false),(65,true),(70,false)]
theorem der_50971 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50971 :=
  CNF.rup_sound cl_50971 [cl_33096,cl_50968] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33096 v h) (hints_cons _ _ _ (der_50968 v h) (by intro d hd; cases hd)))
def cl_50973 : CNF.NClause := [(87,false),(70,true),(34,false),(75,true),(65,false)]
theorem der_50973 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50973 :=
  CNF.rup_sound cl_50973 [cl_33099,cl_33085] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33099 v h) (hints_cons _ _ _ (der_33085 v h) (by intro d hd; cases hd)))
def cl_50975 : CNF.NClause := [(85,true),(70,true),(87,false),(75,true),(34,false)]
theorem der_50975 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50975 :=
  CNF.rup_sound cl_50975 [cl_33101,cl_50973] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33101 v h) (hints_cons _ _ _ (der_50973 v h) (by intro d hd; cases hd)))
def cl_50976 : CNF.NClause := [(65,false),(70,true),(85,false),(3,false),(34,false)]
theorem der_50976 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50976 :=
  CNF.rup_sound cl_50976 [cl_33119,cl_33113] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33119 v h) (hints_cons _ _ _ (der_33113 v h) (by intro d hd; cases hd)))
def cl_50977 : CNF.NClause := [(85,false),(34,false),(3,false),(70,true),(80,true)]
theorem der_50977 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50977 :=
  CNF.rup_sound cl_50977 [cl_33121,cl_50976] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33121 v h) (hints_cons _ _ _ (der_50976 v h) (by intro d hd; cases hd)))
def cl_50978 : CNF.NClause := [(65,true),(70,true),(80,true),(85,false),(34,false)]
theorem der_50978 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50978 :=
  CNF.rup_sound cl_50978 [cl_33122,cl_50977] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33122 v h) (hints_cons _ _ _ (der_50977 v h) (by intro d hd; cases hd)))
def cl_50979 : CNF.NClause := [(80,false),(65,false),(70,true),(34,false),(75,false)]
theorem der_50979 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50979 :=
  CNF.rup_sound cl_50979 [cl_33126,cl_33125] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33126 v h) (hints_cons _ _ _ (der_33125 v h) (by intro d hd; cases hd)))
def cl_50980 : CNF.NClause := [(80,false),(75,false),(34,false),(70,true),(85,true)]
theorem der_50980 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50980 :=
  CNF.rup_sound cl_50980 [cl_33128,cl_50979] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33128 v h) (hints_cons _ _ _ (der_50979 v h) (by intro d hd; cases hd)))
def cl_50981 : CNF.NClause := [(85,true),(34,false),(80,false),(70,false),(3,true)]
theorem der_50981 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50981 :=
  CNF.rup_sound cl_50981 [cl_33131,cl_50425] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33131 v h) (hints_cons _ _ _ (der_50425 v h) (by intro d hd; cases hd)))
def cl_50982 : CNF.NClause := [(80,false),(65,false),(70,true),(3,false),(34,false)]
theorem der_50982 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50982 :=
  CNF.rup_sound cl_50982 [cl_33132,cl_50979] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33132 v h) (hints_cons _ _ _ (der_50979 v h) (by intro d hd; cases hd)))
def cl_50983 : CNF.NClause := [(85,true),(65,true),(3,false),(34,false),(80,false)]
theorem der_50983 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50983 :=
  CNF.rup_sound cl_50983 [cl_33133,cl_33130] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33133 v h) (hints_cons _ _ _ (der_33130 v h) (by intro d hd; cases hd)))
def cl_50984 : CNF.NClause := [(65,false),(75,false),(34,false),(80,true),(70,false)]
theorem der_50984 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50984 :=
  CNF.rup_sound cl_50984 [cl_33136,cl_33135] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33136 v h) (hints_cons _ _ _ (der_33135 v h) (by intro d hd; cases hd)))
def cl_50985 : CNF.NClause := [(75,false),(34,false),(3,false),(65,true),(70,false)]
theorem der_50985 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50985 :=
  CNF.rup_sound cl_50985 [cl_33137,cl_33111] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33137 v h) (hints_cons _ _ _ (der_33111 v h) (by intro d hd; cases hd)))
def cl_50986 : CNF.NClause := [(75,false),(70,false),(3,true),(34,false),(80,true)]
theorem der_50986 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50986 :=
  CNF.rup_sound cl_50986 [cl_33138,cl_33112] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33138 v h) (hints_cons _ _ _ (der_33112 v h) (by intro d hd; cases hd)))
def cl_50987 : CNF.NClause := [(75,false),(65,false),(34,false),(3,false),(80,true)]
theorem der_50987 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50987 :=
  CNF.rup_sound cl_50987 [cl_33139,cl_50984] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33139 v h) (hints_cons _ _ _ (der_50984 v h) (by intro d hd; cases hd)))
def cl_50988 : CNF.NClause := [(65,true),(75,false),(34,false),(3,false),(80,true)]
theorem der_50988 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50988 :=
  CNF.rup_sound cl_50988 [cl_33140,cl_50985] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33140 v h) (hints_cons _ _ _ (der_50985 v h) (by intro d hd; cases hd)))
def cl_50989 : CNF.NClause := [(65,true),(75,false),(70,true),(34,false),(80,true)]
theorem der_50989 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50989 :=
  CNF.rup_sound cl_50989 [cl_33141,cl_50988] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33141 v h) (hints_cons _ _ _ (der_50988 v h) (by intro d hd; cases hd)))
def cl_50990 : CNF.NClause := [(85,true),(65,true),(3,false),(34,false),(70,false)]
theorem der_50990 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50990 :=
  CNF.rup_sound cl_50990 [cl_33143,cl_50985] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33143 v h) (hints_cons _ _ _ (der_50985 v h) (by intro d hd; cases hd)))
def cl_50992 : CNF.NClause := [(70,true),(34,false),(80,true),(75,true),(85,true)]
theorem der_50992 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50992 :=
  CNF.rup_sound cl_50992 [cl_33147,cl_50975] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33147 v h) (hints_cons _ _ _ (der_50975 v h) (by intro d hd; cases hd)))
def cl_50998 : CNF.NClause := [(121,true),(50,false),(31,true),(53,true),(59,false)]
theorem der_50998 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_50998 :=
  CNF.rup_sound cl_50998 [cl_23743,cl_50037] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23743 v h) (hints_cons _ _ _ (der_50037 v h) (by intro d hd; cases hd)))
def cl_51006 : CNF.NClause := [(88,false),(77,false),(70,true),(48,false),(83,false)]
theorem der_51006 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51006 :=
  CNF.rup_sound cl_51006 [cl_33160,cl_33159] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33160 v h) (hints_cons _ _ _ (der_33159 v h) (by intro d hd; cases hd)))
def cl_51007 : CNF.NClause := [(88,false),(70,true),(48,false),(76,false),(83,false)]
theorem der_51007 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51007 :=
  CNF.rup_sound cl_51007 [cl_33164,cl_33163] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33164 v h) (hints_cons _ _ _ (der_33163 v h) (by intro d hd; cases hd)))
def cl_51008 : CNF.NClause := [(70,true),(88,false),(48,false),(83,false),(17,false)]
theorem der_51008 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51008 :=
  CNF.rup_sound cl_51008 [cl_33170,cl_51007] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33170 v h) (hints_cons _ _ _ (der_51007 v h) (by intro d hd; cases hd)))
def cl_51009 : CNF.NClause := [(70,true),(64,false),(77,false),(88,false),(48,false)]
theorem der_51009 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51009 :=
  CNF.rup_sound cl_51009 [cl_33179,cl_33158] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33179 v h) (hints_cons _ _ _ (der_33158 v h) (by intro d hd; cases hd)))
def cl_51010 : CNF.NClause := [(83,true),(77,false),(88,false),(17,false),(48,false)]
theorem der_51010 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51010 :=
  CNF.rup_sound cl_51010 [cl_33180,cl_33173] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33180 v h) (hints_cons _ _ _ (der_33173 v h) (by intro d hd; cases hd)))
def cl_51011 : CNF.NClause := [(88,false),(70,true),(77,false),(48,false),(76,true)]
theorem der_51011 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51011 :=
  CNF.rup_sound cl_51011 [cl_33181,cl_51006] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33181 v h) (hints_cons _ _ _ (der_51006 v h) (by intro d hd; cases hd)))
def cl_51013 : CNF.NClause := [(70,true),(88,false),(76,true),(17,false),(48,false)]
theorem der_51013 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51013 :=
  CNF.rup_sound cl_51013 [cl_33194,cl_51008] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33194 v h) (hints_cons _ _ _ (der_51008 v h) (by intro d hd; cases hd)))
def cl_51016 : CNF.NClause := [(64,false),(17,true),(48,false),(70,false),(88,true)]
theorem der_51016 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51016 :=
  CNF.rup_sound cl_51016 [cl_33204,cl_32089] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33204 v h) (hints_cons _ _ _ (der_32089 v h) (by intro d hd; cases hd)))
def cl_51017 : CNF.NClause := [(77,true),(76,false),(48,false),(83,false),(17,false)]
theorem der_51017 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51017 :=
  CNF.rup_sound cl_51017 [cl_33209,cl_33205] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33209 v h) (hints_cons _ _ _ (der_33205 v h) (by intro d hd; cases hd)))
def cl_51018 : CNF.NClause := [(76,true),(64,false),(83,false),(70,false),(48,false)]
theorem der_51018 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51018 :=
  CNF.rup_sound cl_51018 [cl_33211,cl_33198] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33211 v h) (hints_cons _ _ _ (der_33198 v h) (by intro d hd; cases hd)))
def cl_51019 : CNF.NClause := [(76,true),(83,false),(48,false),(70,false),(17,false)]
theorem der_51019 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51019 :=
  CNF.rup_sound cl_51019 [cl_33212,cl_51018] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33212 v h) (hints_cons _ _ _ (der_51018 v h) (by intro d hd; cases hd)))
def cl_51020 : CNF.NClause := [(83,false),(70,false),(76,true),(48,false),(77,true)]
theorem der_51020 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51020 :=
  CNF.rup_sound cl_51020 [cl_33213,cl_51019] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33213 v h) (hints_cons _ _ _ (der_51019 v h) (by intro d hd; cases hd)))
def cl_51021 : CNF.NClause := [(64,false),(48,false),(83,false),(17,false),(77,true)]
theorem der_51021 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51021 :=
  CNF.rup_sound cl_51021 [cl_33214,cl_51017] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33214 v h) (hints_cons _ _ _ (der_51017 v h) (by intro d hd; cases hd)))
def cl_51022 : CNF.NClause := [(83,false),(70,true),(48,false),(17,false),(77,true)]
theorem der_51022 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51022 :=
  CNF.rup_sound cl_51022 [cl_33216,cl_51008] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33216 v h) (hints_cons _ _ _ (der_51008 v h) (by intro d hd; cases hd)))
def cl_51023 : CNF.NClause := [(83,false),(76,true),(17,true),(48,false),(88,true)]
theorem der_51023 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51023 :=
  CNF.rup_sound cl_51023 [cl_33217,cl_33215] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33217 v h) (hints_cons _ _ _ (der_33215 v h) (by intro d hd; cases hd)))
def cl_51024 : CNF.NClause := [(77,false),(76,false),(64,true),(17,false),(48,false)]
theorem der_51024 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51024 :=
  CNF.rup_sound cl_51024 [cl_33223,cl_33196] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33223 v h) (hints_cons _ _ _ (der_33196 v h) (by intro d hd; cases hd)))
def cl_51025 : CNF.NClause := [(76,false),(77,false),(48,false),(64,true),(88,true)]
theorem der_51025 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51025 :=
  CNF.rup_sound cl_51025 [cl_33224,cl_51024] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33224 v h) (hints_cons _ _ _ (der_51024 v h) (by intro d hd; cases hd)))
def cl_51026 : CNF.NClause := [(70,true),(77,false),(48,false),(64,false),(17,false)]
theorem der_51026 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51026 :=
  CNF.rup_sound cl_51026 [cl_33227,cl_33221] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33227 v h) (hints_cons _ _ _ (der_33221 v h) (by intro d hd; cases hd)))
def cl_51027 : CNF.NClause := [(64,false),(48,false),(76,false),(70,true),(17,false)]
theorem der_51027 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51027 :=
  CNF.rup_sound cl_51027 [cl_33233,cl_33221] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33233 v h) (hints_cons _ _ _ (der_33221 v h) (by intro d hd; cases hd)))
def cl_51029 : CNF.NClause := [(77,true),(70,true),(64,false),(17,false),(48,false)]
theorem der_51029 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51029 :=
  CNF.rup_sound cl_51029 [cl_33239,cl_51021] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33239 v h) (hints_cons _ _ _ (der_51021 v h) (by intro d hd; cases hd)))
def cl_51030 : CNF.NClause := [(108,true),(61,true),(50,false),(47,true),(49,false)]
theorem der_51030 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51030 :=
  CNF.rup_sound cl_51030 [cl_33242,cl_36297] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33242 v h) (hints_cons _ _ _ (der_36297 v h) (by intro d hd; cases hd)))
def cl_51032 : CNF.NClause := [(31,true),(60,true),(52,false),(48,false),(119,true)]
theorem der_51032 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51032 :=
  CNF.rup_sound cl_51032 [cl_23774,cl_42547] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23774 v h) (hints_cons _ _ _ (der_42547 v h) (by intro d hd; cases hd)))
def cl_51033 : CNF.NClause := [(68,true),(91,false),(81,false),(85,false),(43,false)]
theorem der_51033 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51033 :=
  CNF.rup_sound cl_51033 [cl_33250,cl_48970] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33250 v h) (hints_cons _ _ _ (der_48970 v h) (by intro d hd; cases hd)))
def cl_51034 : CNF.NClause := [(68,true),(72,false),(85,false),(91,false),(43,false)]
theorem der_51034 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51034 :=
  CNF.rup_sound cl_51034 [cl_33254,cl_51033] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33254 v h) (hints_cons _ _ _ (der_51033 v h) (by intro d hd; cases hd)))
def cl_51036 : CNF.NClause := [(85,false),(12,false),(91,false),(64,true),(43,false)]
theorem der_51036 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51036 :=
  CNF.rup_sound cl_51036 [cl_33260,cl_33253] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33260 v h) (hints_cons _ _ _ (der_33253 v h) (by intro d hd; cases hd)))
def cl_51037 : CNF.NClause := [(91,false),(64,true),(85,false),(43,false),(72,true)]
theorem der_51037 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51037 :=
  CNF.rup_sound cl_51037 [cl_33261,cl_51036] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33261 v h) (hints_cons _ _ _ (der_51036 v h) (by intro d hd; cases hd)))
def cl_51038 : CNF.NClause := [(64,true),(72,false),(81,false),(91,false),(43,false)]
theorem der_51038 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51038 :=
  CNF.rup_sound cl_51038 [cl_33265,cl_33262] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33265 v h) (hints_cons _ _ _ (der_33262 v h) (by intro d hd; cases hd)))
def cl_51039 : CNF.NClause := [(64,false),(81,false),(72,true),(91,false),(43,false)]
theorem der_51039 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51039 :=
  CNF.rup_sound cl_51039 [cl_33266,cl_48970] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33266 v h) (hints_cons _ _ _ (der_48970 v h) (by intro d hd; cases hd)))
def cl_51040 : CNF.NClause := [(91,false),(64,true),(43,false),(81,false),(68,false)]
theorem der_51040 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51040 :=
  CNF.rup_sound cl_51040 [cl_33268,cl_51038] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33268 v h) (hints_cons _ _ _ (der_51038 v h) (by intro d hd; cases hd)))
def cl_51041 : CNF.NClause := [(91,false),(43,false),(81,false),(12,false),(68,true)]
theorem der_51041 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51041 :=
  CNF.rup_sound cl_51041 [cl_33271,cl_48970] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33271 v h) (hints_cons _ _ _ (der_48970 v h) (by intro d hd; cases hd)))
def cl_51042 : CNF.NClause := [(91,false),(64,true),(12,true),(43,false),(81,false)]
theorem der_51042 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51042 :=
  CNF.rup_sound cl_51042 [cl_33272,cl_51040] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33272 v h) (hints_cons _ _ _ (der_51040 v h) (by intro d hd; cases hd)))
def cl_51043 : CNF.NClause := [(91,false),(68,false),(64,true),(43,false),(72,false)]
theorem der_51043 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51043 :=
  CNF.rup_sound cl_51043 [cl_33274,cl_49549] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33274 v h) (hints_cons _ _ _ (der_49549 v h) (by intro d hd; cases hd)))
def cl_51044 : CNF.NClause := [(72,false),(64,true),(43,false),(91,false),(12,false)]
theorem der_51044 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51044 :=
  CNF.rup_sound cl_51044 [cl_33276,cl_51043] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33276 v h) (hints_cons _ _ _ (der_51043 v h) (by intro d hd; cases hd)))
def cl_51045 : CNF.NClause := [(68,true),(91,false),(43,false),(72,false),(64,true)]
theorem der_51045 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51045 :=
  CNF.rup_sound cl_51045 [cl_33277,cl_51038] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33277 v h) (hints_cons _ _ _ (der_51038 v h) (by intro d hd; cases hd)))
def cl_51046 : CNF.NClause := [(91,false),(68,false),(43,false),(64,true),(12,true)]
theorem der_51046 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51046 :=
  CNF.rup_sound cl_51046 [cl_33280,cl_51043] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33280 v h) (hints_cons _ _ _ (der_51043 v h) (by intro d hd; cases hd)))
def cl_51047 : CNF.NClause := [(91,false),(64,false),(72,true),(12,false),(43,false)]
theorem der_51047 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51047 :=
  CNF.rup_sound cl_51047 [cl_33281,cl_51039] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33281 v h) (hints_cons _ _ _ (der_51039 v h) (by intro d hd; cases hd)))
def cl_51048 : CNF.NClause := [(68,true),(64,false),(91,false),(43,false),(72,true)]
theorem der_51048 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51048 :=
  CNF.rup_sound cl_51048 [cl_33282,cl_48970] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33282 v h) (hints_cons _ _ _ (der_48970 v h) (by intro d hd; cases hd)))
def cl_51049 : CNF.NClause := [(91,false),(64,true),(43,false),(12,false),(68,true)]
theorem der_51049 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51049 :=
  CNF.rup_sound cl_51049 [cl_33283,cl_51036] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33283 v h) (hints_cons _ _ _ (der_51036 v h) (by intro d hd; cases hd)))
def cl_51050 : CNF.NClause := [(81,false),(68,false),(12,true),(85,false),(43,false)]
theorem der_51050 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51050 :=
  CNF.rup_sound cl_51050 [cl_35551,cl_44340] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35551 v h) (hints_cons _ _ _ (der_44340 v h) (by intro d hd; cases hd)))
def cl_51051 : CNF.NClause := [(64,true),(43,false),(68,false),(81,false),(85,false)]
theorem der_51051 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51051 :=
  CNF.rup_sound cl_51051 [cl_33285,cl_44340] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33285 v h) (hints_cons _ _ _ (der_44340 v h) (by intro d hd; cases hd)))
def cl_51052 : CNF.NClause := [(85,false),(43,false),(64,true),(72,false),(81,false)]
theorem der_51052 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51052 :=
  CNF.rup_sound cl_51052 [cl_33288,cl_51051] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33288 v h) (hints_cons _ _ _ (der_51051 v h) (by intro d hd; cases hd)))
def cl_51053 : CNF.NClause := [(64,false),(43,false),(81,false),(72,true),(85,false)]
theorem der_51053 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51053 :=
  CNF.rup_sound cl_51053 [cl_33293,cl_51039] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33293 v h) (hints_cons _ _ _ (der_51039 v h) (by intro d hd; cases hd)))
def cl_51054 : CNF.NClause := [(85,false),(81,false),(43,false),(64,true),(12,false)]
theorem der_51054 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51054 :=
  CNF.rup_sound cl_51054 [cl_33294,cl_51051] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33294 v h) (hints_cons _ _ _ (der_51051 v h) (by intro d hd; cases hd)))
def cl_51057 : CNF.NClause := [(85,false),(43,false),(64,false),(72,false),(12,true)]
theorem der_51057 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51057 :=
  CNF.rup_sound cl_51057 [cl_33299,cl_49549] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33299 v h) (hints_cons _ _ _ (der_49549 v h) (by intro d hd; cases hd)))
def cl_51058 : CNF.NClause := [(64,true),(72,false),(85,false),(43,false),(12,false)]
theorem der_51058 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51058 :=
  CNF.rup_sound cl_51058 [cl_33300,cl_51054] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33300 v h) (hints_cons _ _ _ (der_51054 v h) (by intro d hd; cases hd)))
def cl_51059 : CNF.NClause := [(68,true),(43,false),(72,false),(85,false),(64,true)]
theorem der_51059 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51059 :=
  CNF.rup_sound cl_51059 [cl_33301,cl_51052] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33301 v h) (hints_cons _ _ _ (der_51052 v h) (by intro d hd; cases hd)))
def cl_51060 : CNF.NClause := [(85,false),(12,true),(43,false),(64,false),(68,false)]
theorem der_51060 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51060 :=
  CNF.rup_sound cl_51060 [cl_33303,cl_51050] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33303 v h) (hints_cons _ _ _ (der_51050 v h) (by intro d hd; cases hd)))
def cl_51061 : CNF.NClause := [(64,true),(68,false),(43,false),(85,false),(12,false)]
theorem der_51061 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51061 :=
  CNF.rup_sound cl_51061 [cl_33304,cl_51058] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33304 v h) (hints_cons _ _ _ (der_51058 v h) (by intro d hd; cases hd)))
def cl_51062 : CNF.NClause := [(81,true),(85,false),(43,false),(68,false),(64,true)]
theorem der_51062 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51062 :=
  CNF.rup_sound cl_51062 [cl_33305,cl_51061] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33305 v h) (hints_cons _ _ _ (der_51061 v h) (by intro d hd; cases hd)))
def cl_51064 : CNF.NClause := [(85,false),(68,true),(64,false),(72,true),(43,false)]
theorem der_51064 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51064 :=
  CNF.rup_sound cl_51064 [cl_33307,cl_51053] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33307 v h) (hints_cons _ _ _ (der_51053 v h) (by intro d hd; cases hd)))
def cl_51066 : CNF.NClause := [(68,true),(85,false),(43,false),(64,true),(91,true)]
theorem der_51066 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51066 :=
  CNF.rup_sound cl_51066 [cl_33309,cl_51059] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33309 v h) (hints_cons _ _ _ (der_51059 v h) (by intro d hd; cases hd)))
def cl_51067 : CNF.NClause := [(64,true),(72,false),(81,false),(43,false),(68,false)]
theorem der_51067 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51067 :=
  CNF.rup_sound cl_51067 [cl_33311,cl_49549] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33311 v h) (hints_cons _ _ _ (der_49549 v h) (by intro d hd; cases hd)))
def cl_51068 : CNF.NClause := [(64,true),(43,false),(72,false),(81,false),(12,false)]
theorem der_51068 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51068 :=
  CNF.rup_sound cl_51068 [cl_33314,cl_51054] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33314 v h) (hints_cons _ _ _ (der_51054 v h) (by intro d hd; cases hd)))
def cl_51069 : CNF.NClause := [(64,true),(81,false),(72,false),(12,true),(43,false)]
theorem der_51069 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51069 :=
  CNF.rup_sound cl_51069 [cl_33315,cl_51067] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33315 v h) (hints_cons _ _ _ (der_51067 v h) (by intro d hd; cases hd)))
def cl_51070 : CNF.NClause := [(64,true),(81,false),(68,false),(12,true),(43,false)]
theorem der_51070 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51070 :=
  CNF.rup_sound cl_51070 [cl_33318,cl_51051] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33318 v h) (hints_cons _ _ _ (der_51051 v h) (by intro d hd; cases hd)))
def cl_51071 : CNF.NClause := [(64,false),(12,false),(43,false),(81,false),(72,true)]
theorem der_51071 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51071 :=
  CNF.rup_sound cl_51071 [cl_33319,cl_51039] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33319 v h) (hints_cons _ _ _ (der_51039 v h) (by intro d hd; cases hd)))
def cl_51072 : CNF.NClause := [(12,false),(81,false),(43,false),(68,true),(72,true)]
theorem der_51072 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51072 :=
  CNF.rup_sound cl_51072 [cl_33321,cl_51071] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33321 v h) (hints_cons _ _ _ (der_51071 v h) (by intro d hd; cases hd)))
def cl_51073 : CNF.NClause := [(72,false),(81,true),(64,false),(68,false),(43,false)]
theorem der_51073 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51073 :=
  CNF.rup_sound cl_51073 [cl_33323,cl_49549] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33323 v h) (hints_cons _ _ _ (der_49549 v h) (by intro d hd; cases hd)))
def cl_51074 : CNF.NClause := [(64,true),(72,false),(43,false),(12,false),(68,false)]
theorem der_51074 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51074 :=
  CNF.rup_sound cl_51074 [cl_33325,cl_51058] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33325 v h) (hints_cons _ _ _ (der_51058 v h) (by intro d hd; cases hd)))
def cl_51076 : CNF.NClause := [(68,true),(81,true),(72,false),(43,false),(64,true)]
theorem der_51076 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51076 :=
  CNF.rup_sound cl_51076 [cl_33330,cl_51059] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33330 v h) (hints_cons _ _ _ (der_51059 v h) (by intro d hd; cases hd)))
def cl_51078 : CNF.NClause := [(68,false),(64,false),(12,true),(43,false),(91,true)]
theorem der_51078 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51078 :=
  CNF.rup_sound cl_51078 [cl_33332,cl_51060] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33332 v h) (hints_cons _ _ _ (der_51060 v h) (by intro d hd; cases hd)))
def cl_51079 : CNF.NClause := [(81,true),(68,false),(43,false),(64,true),(12,true)]
theorem der_51079 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51079 :=
  CNF.rup_sound cl_51079 [cl_33334,cl_49549] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33334 v h) (hints_cons _ _ _ (der_49549 v h) (by intro d hd; cases hd)))
def cl_51080 : CNF.NClause := [(64,false),(12,false),(72,true),(43,false),(68,true)]
theorem der_51080 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51080 :=
  CNF.rup_sound cl_51080 [cl_33335,cl_51071] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33335 v h) (hints_cons _ _ _ (der_51071 v h) (by intro d hd; cases hd)))
def cl_51081 : CNF.NClause := [(81,true),(43,false),(68,true),(64,false),(72,true)]
theorem der_51081 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51081 :=
  CNF.rup_sound cl_51081 [cl_33336,cl_51080] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33336 v h) (hints_cons _ _ _ (der_51080 v h) (by intro d hd; cases hd)))
def cl_51084 : CNF.NClause := [(87,false),(33,false),(64,true),(74,false),(84,false)]
theorem der_51084 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51084 :=
  CNF.rup_sound cl_51084 [cl_33344,cl_33342] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33344 v h) (hints_cons _ _ _ (der_33342 v h) (by intro d hd; cases hd)))
def cl_51085 : CNF.NClause := [(87,false),(64,false),(84,false),(74,true),(33,false)]
theorem der_51085 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51085 :=
  CNF.rup_sound cl_51085 [cl_33345,cl_50545] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33345 v h) (hints_cons _ _ _ (der_50545 v h) (by intro d hd; cases hd)))
def cl_51086 : CNF.NClause := [(87,false),(69,false),(74,true),(33,false),(84,false)]
theorem der_51086 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51086 :=
  CNF.rup_sound cl_51086 [cl_33347,cl_51085] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33347 v h) (hints_cons _ _ _ (der_51085 v h) (by intro d hd; cases hd)))
def cl_51087 : CNF.NClause := [(87,false),(64,true),(79,false),(33,false),(69,false)]
theorem der_51087 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51087 :=
  CNF.rup_sound cl_51087 [cl_33352,cl_45654] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33352 v h) (hints_cons _ _ _ (der_45654 v h) (by intro d hd; cases hd)))
def cl_51088 : CNF.NClause := [(87,false),(33,false),(64,true),(74,false),(79,false)]
theorem der_51088 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51088 :=
  CNF.rup_sound cl_51088 [cl_33354,cl_51087] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33354 v h) (hints_cons _ _ _ (der_51087 v h) (by intro d hd; cases hd)))
def cl_51089 : CNF.NClause := [(33,false),(64,true),(69,true),(87,false),(2,false)]
theorem der_51089 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51089 :=
  CNF.rup_sound cl_51089 [cl_33360,cl_49995] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33360 v h) (hints_cons _ _ _ (der_49995 v h) (by intro d hd; cases hd)))
def cl_51090 : CNF.NClause := [(87,false),(33,false),(64,false),(74,false),(79,true)]
theorem der_51090 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51090 :=
  CNF.rup_sound cl_51090 [cl_33362,cl_50546] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33362 v h) (hints_cons _ _ _ (der_50546 v h) (by intro d hd; cases hd)))
def cl_51092 : CNF.NClause := [(87,false),(69,true),(64,true),(33,false),(74,false)]
theorem der_51092 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51092 :=
  CNF.rup_sound cl_51092 [cl_33368,cl_51089] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33368 v h) (hints_cons _ _ _ (der_51089 v h) (by intro d hd; cases hd)))
def cl_51094 : CNF.NClause := [(87,false),(69,false),(64,true),(33,false),(2,false)]
theorem der_51094 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51094 :=
  CNF.rup_sound cl_51094 [cl_33371,cl_51087] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33371 v h) (hints_cons _ _ _ (der_51087 v h) (by intro d hd; cases hd)))
def cl_51095 : CNF.NClause := [(87,false),(79,true),(64,false),(33,false),(2,false)]
theorem der_51095 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51095 :=
  CNF.rup_sound cl_51095 [cl_33373,cl_51090] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33373 v h) (hints_cons _ _ _ (der_51090 v h) (by intro d hd; cases hd)))
def cl_51099 : CNF.NClause := [(84,false),(33,false),(74,false),(69,true),(79,false)]
theorem der_51099 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51099 :=
  CNF.rup_sound cl_51099 [cl_33380,cl_49698] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33380 v h) (hints_cons _ _ _ (der_49698 v h) (by intro d hd; cases hd)))
def cl_51100 : CNF.NClause := [(84,false),(79,false),(33,false),(74,true),(69,false)]
theorem der_51100 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51100 :=
  CNF.rup_sound cl_51100 [cl_33383,cl_49698] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33383 v h) (hints_cons _ _ _ (der_49698 v h) (by intro d hd; cases hd)))
def cl_51104 : CNF.NClause := [(33,false),(79,true),(74,false),(84,false),(64,false)]
theorem der_51104 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51104 :=
  CNF.rup_sound cl_51104 [cl_33389,cl_50546] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33389 v h) (hints_cons _ _ _ (der_50546 v h) (by intro d hd; cases hd)))
def cl_51105 : CNF.NClause := [(84,false),(79,true),(74,false),(2,false),(33,false)]
theorem der_51105 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51105 :=
  CNF.rup_sound cl_51105 [cl_33390,cl_49995] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33390 v h) (hints_cons _ _ _ (der_49995 v h) (by intro d hd; cases hd)))
def cl_51108 : CNF.NClause := [(79,true),(69,true),(74,false),(84,false),(33,false)]
theorem der_51108 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51108 :=
  CNF.rup_sound cl_51108 [cl_33395,cl_51104] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33395 v h) (hints_cons _ _ _ (der_51104 v h) (by intro d hd; cases hd)))
def cl_51109 : CNF.NClause := [(87,true),(79,true),(64,false),(84,false),(33,false)]
theorem der_51109 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51109 :=
  CNF.rup_sound cl_51109 [cl_33396,cl_50546] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33396 v h) (hints_cons _ _ _ (der_50546 v h) (by intro d hd; cases hd)))
def cl_51111 : CNF.NClause := [(79,true),(64,true),(33,false),(74,true),(84,false)]
theorem der_51111 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51111 :=
  CNF.rup_sound cl_51111 [cl_33398,cl_50545] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33398 v h) (hints_cons _ _ _ (der_50545 v h) (by intro d hd; cases hd)))
def cl_51112 : CNF.NClause := [(79,false),(33,false),(64,true),(69,false),(74,false)]
theorem der_51112 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51112 :=
  CNF.rup_sound cl_51112 [cl_33404,cl_49699] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33404 v h) (hints_cons _ _ _ (der_49699 v h) (by intro d hd; cases hd)))
def cl_51113 : CNF.NClause := [(79,false),(64,false),(69,true),(33,false),(2,false)]
theorem der_51113 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51113 :=
  CNF.rup_sound cl_51113 [cl_33406,cl_50544] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33406 v h) (hints_cons _ _ _ (der_50544 v h) (by intro d hd; cases hd)))
def cl_51114 : CNF.NClause := [(64,false),(84,true),(74,false),(33,false),(79,false)]
theorem der_51114 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51114 :=
  CNF.rup_sound cl_51114 [cl_33407,cl_33353] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33407 v h) (hints_cons _ _ _ (der_33353 v h) (by intro d hd; cases hd)))
def cl_51115 : CNF.NClause := [(33,false),(74,false),(69,true),(79,false),(2,false)]
theorem der_51115 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51115 :=
  CNF.rup_sound cl_51115 [cl_33408,cl_51099] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33408 v h) (hints_cons _ _ _ (der_51099 v h) (by intro d hd; cases hd)))
def cl_51116 : CNF.NClause := [(87,true),(69,true),(79,false),(33,false),(84,true)]
theorem der_51116 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51116 :=
  CNF.rup_sound cl_51116 [cl_33409,cl_50544] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33409 v h) (hints_cons _ _ _ (der_50544 v h) (by intro d hd; cases hd)))
def cl_51117 : CNF.NClause := [(64,false),(79,false),(33,false),(2,false),(74,true)]
theorem der_51117 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51117 :=
  CNF.rup_sound cl_51117 [cl_33410,cl_48905] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33410 v h) (hints_cons _ _ _ (der_48905 v h) (by intro d hd; cases hd)))
def cl_51119 : CNF.NClause := [(64,false),(74,true),(84,true),(69,true),(33,false)]
theorem der_51119 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51119 :=
  CNF.rup_sound cl_51119 [cl_33414,cl_50546] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33414 v h) (hints_cons _ _ _ (der_50546 v h) (by intro d hd; cases hd)))
def cl_51121 : CNF.NClause := [(64,false),(79,true),(74,false),(2,false),(33,false)]
theorem der_51121 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51121 :=
  CNF.rup_sound cl_51121 [cl_33417,cl_50546] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33417 v h) (hints_cons _ _ _ (der_50546 v h) (by intro d hd; cases hd)))
def cl_51122 : CNF.NClause := [(69,false),(79,true),(33,false),(74,false),(64,false)]
theorem der_51122 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51122 :=
  CNF.rup_sound cl_51122 [cl_33418,cl_51104] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33418 v h) (hints_cons _ _ _ (der_51104 v h) (by intro d hd; cases hd)))
def cl_51125 : CNF.NClause := [(64,true),(79,true),(33,false),(69,true),(74,false)]
theorem der_51125 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51125 :=
  CNF.rup_sound cl_51125 [cl_33423,cl_51092] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33423 v h) (hints_cons _ _ _ (der_51092 v h) (by intro d hd; cases hd)))
def cl_51129 : CNF.NClause := [(74,true),(79,true),(69,true),(84,true),(33,false)]
theorem der_51129 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51129 :=
  CNF.rup_sound cl_51129 [cl_33431,cl_50546] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33431 v h) (hints_cons _ _ _ (der_50546 v h) (by intro d hd; cases hd)))
def cl_51130 : CNF.NClause := [(38,false),(71,false),(89,false),(82,false),(64,true)]
theorem der_51130 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51130 :=
  CNF.rup_sound cl_51130 [cl_33441,cl_39150] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33441 v h) (hints_cons _ _ _ (der_39150 v h) (by intro d hd; cases hd)))
def cl_51131 : CNF.NClause := [(89,false),(64,true),(38,false),(82,false),(7,false)]
theorem der_51131 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51131 :=
  CNF.rup_sound cl_51131 [cl_33442,cl_51130] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33442 v h) (hints_cons _ _ _ (der_51130 v h) (by intro d hd; cases hd)))
def cl_51132 : CNF.NClause := [(73,true),(38,false),(64,true),(89,false),(82,false)]
theorem der_51132 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51132 :=
  CNF.rup_sound cl_51132 [cl_33443,cl_51131] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33443 v h) (hints_cons _ _ _ (der_51131 v h) (by intro d hd; cases hd)))
def cl_51133 : CNF.NClause := [(80,false),(38,false),(71,false),(89,false),(7,true)]
theorem der_51133 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51133 :=
  CNF.rup_sound cl_51133 [cl_33449,cl_33444] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33449 v h) (hints_cons _ _ _ (der_33444 v h) (by intro d hd; cases hd)))
def cl_51134 : CNF.NClause := [(73,false),(89,false),(7,false),(38,false),(80,true)]
theorem der_51134 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51134 :=
  CNF.rup_sound cl_51134 [cl_33455,cl_33452] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33455 v h) (hints_cons _ _ _ (der_33452 v h) (by intro d hd; cases hd)))
def cl_51135 : CNF.NClause := [(73,true),(89,false),(38,false),(64,false),(71,false)]
theorem der_51135 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51135 :=
  CNF.rup_sound cl_51135 [cl_33458,cl_33457] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33458 v h) (hints_cons _ _ _ (der_33457 v h) (by intro d hd; cases hd)))
def cl_51136 : CNF.NClause := [(7,false),(71,false),(38,false),(89,false),(73,true)]
theorem der_51136 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51136 :=
  CNF.rup_sound cl_51136 [cl_33459,cl_33457] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33459 v h) (hints_cons _ _ _ (der_33457 v h) (by intro d hd; cases hd)))
def cl_51137 : CNF.NClause := [(89,false),(71,false),(73,true),(7,true),(38,false)]
theorem der_51137 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51137 :=
  CNF.rup_sound cl_51137 [cl_33460,cl_51133] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33460 v h) (hints_cons _ _ _ (der_51133 v h) (by intro d hd; cases hd)))
def cl_51139 : CNF.NClause := [(82,false),(38,false),(73,false),(80,false),(7,true)]
theorem der_51139 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51139 :=
  CNF.rup_sound cl_51139 [cl_33468,cl_33466] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33468 v h) (hints_cons _ _ _ (der_33466 v h) (by intro d hd; cases hd)))
def cl_51140 : CNF.NClause := [(80,false),(38,false),(71,false),(82,false),(7,true)]
theorem der_51140 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51140 :=
  CNF.rup_sound cl_51140 [cl_33471,cl_33465] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33471 v h) (hints_cons _ _ _ (der_33465 v h) (by intro d hd; cases hd)))
def cl_51141 : CNF.NClause := [(80,false),(64,true),(82,false),(38,false),(7,false)]
theorem der_51141 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51141 :=
  CNF.rup_sound cl_51141 [cl_33473,cl_51131] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33473 v h) (hints_cons _ _ _ (der_51131 v h) (by intro d hd; cases hd)))
def cl_51142 : CNF.NClause := [(80,false),(82,false),(7,true),(38,false),(64,true)]
theorem der_51142 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51142 :=
  CNF.rup_sound cl_51142 [cl_33474,cl_51140] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33474 v h) (hints_cons _ _ _ (der_51140 v h) (by intro d hd; cases hd)))
def cl_51143 : CNF.NClause := [(73,false),(82,false),(64,true),(38,false),(7,false)]
theorem der_51143 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51143 :=
  CNF.rup_sound cl_51143 [cl_33480,cl_33467] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33480 v h) (hints_cons _ _ _ (der_33467 v h) (by intro d hd; cases hd)))
def cl_51144 : CNF.NClause := [(73,false),(82,false),(38,false),(64,true),(89,true)]
theorem der_51144 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51144 :=
  CNF.rup_sound cl_51144 [cl_33481,cl_51143] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33481 v h) (hints_cons _ _ _ (der_51143 v h) (by intro d hd; cases hd)))
def cl_51145 : CNF.NClause := [(7,false),(82,false),(38,false),(71,false),(64,true)]
theorem der_51145 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51145 :=
  CNF.rup_sound cl_51145 [cl_33484,cl_51131] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33484 v h) (hints_cons _ _ _ (der_51131 v h) (by intro d hd; cases hd)))
def cl_51146 : CNF.NClause := [(73,true),(71,false),(7,true),(38,false),(82,false)]
theorem der_51146 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51146 :=
  CNF.rup_sound cl_51146 [cl_33485,cl_51140] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33485 v h) (hints_cons _ _ _ (der_51140 v h) (by intro d hd; cases hd)))
def cl_51147 : CNF.NClause := [(80,true),(82,false),(7,false),(64,false),(38,false)]
theorem der_51147 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51147 :=
  CNF.rup_sound cl_51147 [cl_33486,cl_33478] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33486 v h) (hints_cons _ _ _ (der_33478 v h) (by intro d hd; cases hd)))
def cl_51148 : CNF.NClause := [(82,false),(38,false),(64,true),(7,false),(89,true)]
theorem der_51148 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51148 :=
  CNF.rup_sound cl_51148 [cl_33488,cl_51143] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33488 v h) (hints_cons _ _ _ (der_51143 v h) (by intro d hd; cases hd)))
def cl_51149 : CNF.NClause := [(82,false),(38,false),(73,true),(7,true),(64,true)]
theorem der_51149 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51149 :=
  CNF.rup_sound cl_51149 [cl_33489,cl_51146] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33489 v h) (hints_cons _ _ _ (der_51146 v h) (by intro d hd; cases hd)))
def cl_51150 : CNF.NClause := [(80,false),(73,false),(7,true),(38,false),(64,true)]
theorem der_51150 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51150 :=
  CNF.rup_sound cl_51150 [cl_33493,cl_33490] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33493 v h) (hints_cons _ _ _ (der_33490 v h) (by intro d hd; cases hd)))
def cl_51151 : CNF.NClause := [(82,true),(64,false),(71,true),(80,false),(38,false)]
theorem der_51151 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51151 :=
  CNF.rup_sound cl_51151 [cl_33497,cl_33491] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33497 v h) (hints_cons _ _ _ (der_33491 v h) (by intro d hd; cases hd)))
def cl_51152 : CNF.NClause := [(82,true),(73,false),(64,false),(38,false),(71,true)]
theorem der_51152 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51152 :=
  CNF.rup_sound cl_51152 [cl_33503,cl_33491] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33503 v h) (hints_cons _ _ _ (der_33491 v h) (by intro d hd; cases hd)))
def cl_51153 : CNF.NClause := [(73,true),(71,false),(38,false),(64,false),(80,true)]
theorem der_51153 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51153 :=
  CNF.rup_sound cl_51153 [cl_33507,cl_51135] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33507 v h) (hints_cons _ _ _ (der_51135 v h) (by intro d hd; cases hd)))
def cl_51154 : CNF.NClause := [(73,true),(71,false),(38,false),(64,true),(7,false)]
theorem der_51154 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51154 :=
  CNF.rup_sound cl_51154 [cl_33508,cl_51136] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33508 v h) (hints_cons _ _ _ (der_51136 v h) (by intro d hd; cases hd)))
def cl_51155 : CNF.NClause := [(82,true),(64,false),(38,false),(71,true),(89,true)]
theorem der_51155 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51155 :=
  CNF.rup_sound cl_51155 [cl_33510,cl_51152] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33510 v h) (hints_cons _ _ _ (der_51152 v h) (by intro d hd; cases hd)))
def cl_51156 : CNF.NClause := [(73,true),(64,true),(38,false),(7,false),(82,true)]
theorem der_51156 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51156 :=
  CNF.rup_sound cl_51156 [cl_33511,cl_51154] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33511 v h) (hints_cons _ _ _ (der_51154 v h) (by intro d hd; cases hd)))
def cl_51157 : CNF.NClause := [(89,true),(38,false),(71,true),(64,true),(7,true)]
theorem der_51157 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51157 :=
  CNF.rup_sound cl_51157 [cl_33512,cl_33499] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33512 v h) (hints_cons _ _ _ (der_33499 v h) (by intro d hd; cases hd)))
def cl_51158 : CNF.NClause := [(90,false),(81,false),(84,false),(59,false),(70,true)]
theorem der_51158 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51158 :=
  CNF.rup_sound cl_51158 [cl_33517,cl_33515] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33517 v h) (hints_cons _ _ _ (der_33515 v h) (by intro d hd; cases hd)))
def cl_51160 : CNF.NClause := [(70,true),(59,false),(84,false),(28,false),(90,false)]
theorem der_51160 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51160 :=
  CNF.rup_sound cl_51160 [cl_33527,cl_33520] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33527 v h) (hints_cons _ _ _ (der_33520 v h) (by intro d hd; cases hd)))
def cl_51161 : CNF.NClause := [(73,true),(70,true),(84,false),(59,false),(90,false)]
theorem der_51161 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51161 :=
  CNF.rup_sound cl_51161 [cl_33528,cl_51160] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33528 v h) (hints_cons _ _ _ (der_51160 v h) (by intro d hd; cases hd)))
def cl_51162 : CNF.NClause := [(90,false),(81,false),(73,false),(59,false),(70,true)]
theorem der_51162 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51162 :=
  CNF.rup_sound cl_51162 [cl_33532,cl_33530] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33532 v h) (hints_cons _ _ _ (der_33530 v h) (by intro d hd; cases hd)))
def cl_51163 : CNF.NClause := [(70,true),(81,false),(59,false),(90,false),(62,false)]
theorem der_51163 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51163 :=
  CNF.rup_sound cl_51163 [cl_33537,cl_51162] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33537 v h) (hints_cons _ _ _ (der_51162 v h) (by intro d hd; cases hd)))
def cl_51164 : CNF.NClause := [(59,false),(90,false),(81,false),(70,true),(28,false)]
theorem der_51164 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51164 :=
  CNF.rup_sound cl_51164 [cl_33538,cl_51163] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33538 v h) (hints_cons _ _ _ (der_51163 v h) (by intro d hd; cases hd)))
def cl_51165 : CNF.NClause := [(62,true),(70,true),(90,false),(59,false),(81,false)]
theorem der_51165 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51165 :=
  CNF.rup_sound cl_51165 [cl_33539,cl_51164] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33539 v h) (hints_cons _ _ _ (der_51164 v h) (by intro d hd; cases hd)))
def cl_51166 : CNF.NClause := [(73,false),(59,false),(62,true),(70,false),(28,true)]
theorem der_51166 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51166 :=
  CNF.rup_sound cl_51166 [cl_33542,cl_45283] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33542 v h) (hints_cons _ _ _ (der_45283 v h) (by intro d hd; cases hd)))
def cl_51167 : CNF.NClause := [(62,false),(73,false),(59,false),(70,true),(90,false)]
theorem der_51167 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51167 :=
  CNF.rup_sound cl_51167 [cl_33544,cl_51162] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33544 v h) (hints_cons _ _ _ (der_51162 v h) (by intro d hd; cases hd)))
def cl_51168 : CNF.NClause := [(59,false),(90,false),(73,false),(70,true),(28,false)]
theorem der_51168 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51168 :=
  CNF.rup_sound cl_51168 [cl_33545,cl_33543] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33545 v h) (hints_cons _ _ _ (der_33543 v h) (by intro d hd; cases hd)))
def cl_51169 : CNF.NClause := [(62,true),(90,false),(70,true),(59,false),(73,false)]
theorem der_51169 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51169 :=
  CNF.rup_sound cl_51169 [cl_33546,cl_51168] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33546 v h) (hints_cons _ _ _ (der_51168 v h) (by intro d hd; cases hd)))
def cl_51170 : CNF.NClause := [(62,true),(90,false),(28,false),(70,false),(59,false)]
theorem der_51170 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51170 :=
  CNF.rup_sound cl_51170 [cl_33549,cl_33541] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33549 v h) (hints_cons _ _ _ (der_33541 v h) (by intro d hd; cases hd)))
def cl_51171 : CNF.NClause := [(62,true),(84,true),(28,true),(59,false),(70,false)]
theorem der_51171 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51171 :=
  CNF.rup_sound cl_51171 [cl_33550,cl_47860] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33550 v h) (hints_cons _ _ _ (der_47860 v h) (by intro d hd; cases hd)))
def cl_51172 : CNF.NClause := [(62,false),(59,false),(70,true),(28,false),(90,false)]
theorem der_51172 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51172 :=
  CNF.rup_sound cl_51172 [cl_33551,cl_51163] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33551 v h) (hints_cons _ _ _ (der_51163 v h) (by intro d hd; cases hd)))
def cl_51173 : CNF.NClause := [(73,true),(70,true),(90,false),(62,false),(59,false)]
theorem der_51173 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51173 :=
  CNF.rup_sound cl_51173 [cl_33552,cl_51163] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33552 v h) (hints_cons _ _ _ (der_51163 v h) (by intro d hd; cases hd)))
def cl_51175 : CNF.NClause := [(73,true),(70,true),(90,false),(81,true),(59,false)]
theorem der_51175 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51175 :=
  CNF.rup_sound cl_51175 [cl_33554,cl_51161] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33554 v h) (hints_cons _ _ _ (der_51161 v h) (by intro d hd; cases hd)))
def cl_51176 : CNF.NClause := [(84,false),(59,false),(81,false),(70,false),(28,true)]
theorem der_51176 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51176 :=
  CNF.rup_sound cl_51176 [cl_33560,cl_45283] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33560 v h) (hints_cons _ _ _ (der_45283 v h) (by intro d hd; cases hd)))
def cl_51177 : CNF.NClause := [(62,true),(84,false),(81,false),(70,false),(59,false)]
theorem der_51177 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51177 :=
  CNF.rup_sound cl_51177 [cl_33561,cl_47860] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33561 v h) (hints_cons _ _ _ (der_47860 v h) (by intro d hd; cases hd)))
def cl_51178 : CNF.NClause := [(62,false),(59,false),(81,false),(70,true),(84,false)]
theorem der_51178 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51178 :=
  CNF.rup_sound cl_51178 [cl_33563,cl_33557] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33563 v h) (hints_cons _ _ _ (der_33557 v h) (by intro d hd; cases hd)))
def cl_51179 : CNF.NClause := [(59,false),(84,false),(28,false),(81,false),(70,true)]
theorem der_51179 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51179 :=
  CNF.rup_sound cl_51179 [cl_33564,cl_33558] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33564 v h) (hints_cons _ _ _ (der_33558 v h) (by intro d hd; cases hd)))
def cl_51180 : CNF.NClause := [(73,true),(84,false),(70,true),(59,false),(81,false)]
theorem der_51180 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51180 :=
  CNF.rup_sound cl_51180 [cl_33565,cl_51179] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33565 v h) (hints_cons _ _ _ (der_51179 v h) (by intro d hd; cases hd)))
def cl_51181 : CNF.NClause := [(73,false),(62,true),(84,false),(70,false),(59,false)]
theorem der_51181 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51181 :=
  CNF.rup_sound cl_51181 [cl_33567,cl_33518] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33567 v h) (hints_cons _ _ _ (der_33518 v h) (by intro d hd; cases hd)))
def cl_51182 : CNF.NClause := [(62,false),(59,false),(73,false),(70,true),(84,false)]
theorem der_51182 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51182 :=
  CNF.rup_sound cl_51182 [cl_33569,cl_33568] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33569 v h) (hints_cons _ _ _ (der_33568 v h) (by intro d hd; cases hd)))
def cl_51183 : CNF.NClause := [(81,true),(73,false),(84,false),(62,true),(59,false)]
theorem der_51183 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51183 :=
  CNF.rup_sound cl_51183 [cl_33571,cl_51181] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33571 v h) (hints_cons _ _ _ (der_51181 v h) (by intro d hd; cases hd)))
def cl_51184 : CNF.NClause := [(62,false),(59,false),(84,false),(81,true),(70,false)]
theorem der_51184 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51184 :=
  CNF.rup_sound cl_51184 [cl_33573,cl_33566] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33573 v h) (hints_cons _ _ _ (der_33566 v h) (by intro d hd; cases hd)))
def cl_51185 : CNF.NClause := [(62,false),(59,false),(28,false),(84,false),(70,true)]
theorem der_51185 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51185 :=
  CNF.rup_sound cl_51185 [cl_33575,cl_51182] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33575 v h) (hints_cons _ _ _ (der_51182 v h) (by intro d hd; cases hd)))
def cl_51186 : CNF.NClause := [(81,true),(62,true),(59,false),(28,false),(84,false)]
theorem der_51186 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51186 :=
  CNF.rup_sound cl_51186 [cl_33576,cl_51183] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33576 v h) (hints_cons _ _ _ (der_51183 v h) (by intro d hd; cases hd)))
def cl_51187 : CNF.NClause := [(73,false),(62,true),(81,false),(70,false),(59,false)]
theorem der_51187 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51187 :=
  CNF.rup_sound cl_51187 [cl_33579,cl_45283] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33579 v h) (hints_cons _ _ _ (der_45283 v h) (by intro d hd; cases hd)))
def cl_51188 : CNF.NClause := [(62,false),(70,true),(59,false),(81,false),(73,false)]
theorem der_51188 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51188 :=
  CNF.rup_sound cl_51188 [cl_33581,cl_33557] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33581 v h) (hints_cons _ _ _ (der_33557 v h) (by intro d hd; cases hd)))
def cl_51190 : CNF.NClause := [(70,true),(81,false),(59,false),(73,false),(84,true)]
theorem der_51190 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51190 :=
  CNF.rup_sound cl_51190 [cl_33583,cl_51162] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33583 v h) (hints_cons _ _ _ (der_51162 v h) (by intro d hd; cases hd)))
def cl_51191 : CNF.NClause := [(62,false),(59,false),(81,false),(70,false),(84,true)]
theorem der_51191 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51191 :=
  CNF.rup_sound cl_51191 [cl_33585,cl_33578] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33585 v h) (hints_cons _ _ _ (der_33578 v h) (by intro d hd; cases hd)))
def cl_51193 : CNF.NClause := [(62,false),(70,true),(81,false),(73,true),(59,false)]
theorem der_51193 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51193 :=
  CNF.rup_sound cl_51193 [cl_33588,cl_51178] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33588 v h) (hints_cons _ _ _ (der_51178 v h) (by intro d hd; cases hd)))
def cl_51194 : CNF.NClause := [(73,false),(28,true),(59,false),(62,false),(70,false)]
theorem der_51194 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51194 :=
  CNF.rup_sound cl_51194 [cl_33590,cl_45283] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33590 v h) (hints_cons _ _ _ (der_45283 v h) (by intro d hd; cases hd)))
def cl_51195 : CNF.NClause := [(73,false),(59,false),(70,false),(62,true),(90,true)]
theorem der_51195 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51195 :=
  CNF.rup_sound cl_51195 [cl_33591,cl_51187] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33591 v h) (hints_cons _ _ _ (der_51187 v h) (by intro d hd; cases hd)))
def cl_51196 : CNF.NClause := [(73,false),(62,false),(59,false),(70,true),(28,false)]
theorem der_51196 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51196 :=
  CNF.rup_sound cl_51196 [cl_33592,cl_51185] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33592 v h) (hints_cons _ _ _ (der_51185 v h) (by intro d hd; cases hd)))
def cl_51197 : CNF.NClause := [(81,true),(62,false),(28,true),(59,false),(73,false)]
theorem der_51197 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51197 :=
  CNF.rup_sound cl_51197 [cl_33593,cl_51194] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33593 v h) (hints_cons _ _ _ (der_51194 v h) (by intro d hd; cases hd)))
def cl_51198 : CNF.NClause := [(59,false),(73,false),(70,true),(28,false),(84,true)]
theorem der_51198 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_51198 :=
  CNF.rup_sound cl_51198 [cl_33594,cl_51196] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33594 v h) (hints_cons _ _ _ (der_51196 v h) (by intro d hd; cases hd)))
def chunk047 : List CNF.NClause := [cl_50548,cl_50549,cl_50550,cl_50551,cl_50554,cl_50559,cl_50563,cl_50565,cl_50566,cl_50567,cl_50568,cl_50570,cl_50573,cl_50574,cl_50586,cl_50587,cl_50588,cl_50589,cl_50590,cl_50591,cl_50592,cl_50593,cl_50594,cl_50595,cl_50596,cl_50597,cl_50598,cl_50599,cl_50601,cl_50602,cl_50603,cl_50604,cl_50605,cl_50606,cl_50607,cl_50608,cl_50609,cl_50610,cl_50611,cl_50612,cl_50613,cl_50614,cl_50615,cl_50616,cl_50617,cl_50618,cl_50619,cl_50620,cl_50621,cl_50623,cl_50624,cl_50625,cl_50626,cl_50627,cl_50628,cl_50629,cl_50630,cl_50631,cl_50634,cl_50635,cl_50636,cl_50637,cl_50639,cl_50640,cl_50641,cl_50642,cl_50643,cl_50645,cl_50646,cl_50647,cl_50648,cl_50649,cl_50650,cl_50651,cl_50652,cl_50653,cl_50654,cl_50656,cl_50660,cl_50661,cl_50662,cl_50663,cl_50666,cl_50667,cl_50668,cl_50669,cl_50670,cl_50671,cl_50672,cl_50676,cl_50678,cl_50679,cl_50680,cl_50681,cl_50682,cl_50683,cl_50684,cl_50685,cl_50686,cl_50687,cl_50688,cl_50689,cl_50690,cl_50691,cl_50692,cl_50693,cl_50694,cl_50695,cl_50696,cl_50697,cl_50698,cl_50699,cl_50700,cl_50701,cl_50704,cl_50706,cl_50707,cl_50708,cl_50709,cl_50712,cl_50713,cl_50714,cl_50718,cl_50719,cl_50720,cl_50721,cl_50722,cl_50724,cl_50726,cl_50727,cl_50728,cl_50729,cl_50730,cl_50731,cl_50732,cl_50734,cl_50736,cl_50738,cl_50739,cl_50740,cl_50741,cl_50742,cl_50743,cl_50744,cl_50745,cl_50746,cl_50747,cl_50750,cl_50751,cl_50753,cl_50754,cl_50755,cl_50756,cl_50758,cl_50760,cl_50761,cl_50762,cl_50765,cl_50766,cl_50767,cl_50769,cl_50770,cl_50771,cl_50772,cl_50774,cl_50775,cl_50776,cl_50777,cl_50778,cl_50780,cl_50781,cl_50782,cl_50783,cl_50784,cl_50785,cl_50786,cl_50787,cl_50788,cl_50789,cl_50790,cl_50791,cl_50792,cl_50793,cl_50794,cl_50796,cl_50798,cl_50799,cl_50800,cl_50801,cl_50802,cl_50803,cl_50804,cl_50805,cl_50807,cl_50809,cl_50810,cl_50814,cl_50815,cl_50818,cl_50820,cl_50821,cl_50823,cl_50824,cl_50826,cl_50827,cl_50828,cl_50829,cl_50830,cl_50831,cl_50832,cl_50833,cl_50834,cl_50835,cl_50836,cl_50838,cl_50839,cl_50840,cl_50841,cl_50842,cl_50843,cl_50844,cl_50845,cl_50846,cl_50847,cl_50848,cl_50849,cl_50850,cl_50851,cl_50852,cl_50854,cl_50855,cl_50856,cl_50857,cl_50858,cl_50859,cl_50860,cl_50862,cl_50863,cl_50864,cl_50865,cl_50866,cl_50867,cl_50868,cl_50869,cl_50870,cl_50874,cl_50875,cl_50876,cl_50877,cl_50878,cl_50879,cl_50880,cl_50881,cl_50882,cl_50883,cl_50884,cl_50885,cl_50886,cl_50888,cl_50889,cl_50890,cl_50892,cl_50893,cl_50894,cl_50895,cl_50896,cl_50897,cl_50899,cl_50900,cl_50901,cl_50902,cl_50903,cl_50904,cl_50905,cl_50906,cl_50907,cl_50908,cl_50909,cl_50910,cl_50911,cl_50912,cl_50913,cl_50914,cl_50915,cl_50917,cl_50918,cl_50919,cl_50921,cl_50922,cl_50923,cl_50924,cl_50925,cl_50926,cl_50927,cl_50929,cl_50930,cl_50931,cl_50932,cl_50933,cl_50934,cl_50935,cl_50936,cl_50937,cl_50938,cl_50939,cl_50940,cl_50941,cl_50942,cl_50943,cl_50944,cl_50945,cl_50946,cl_50947,cl_50948,cl_50950,cl_50951,cl_50953,cl_50955,cl_50956,cl_50961,cl_50962,cl_50965,cl_50968,cl_50970,cl_50971,cl_50973,cl_50975,cl_50976,cl_50977,cl_50978,cl_50979,cl_50980,cl_50981,cl_50982,cl_50983,cl_50984,cl_50985,cl_50986,cl_50987,cl_50988,cl_50989,cl_50990,cl_50992,cl_50998,cl_51006,cl_51007,cl_51008,cl_51009,cl_51010,cl_51011,cl_51013,cl_51016,cl_51017,cl_51018,cl_51019,cl_51020,cl_51021,cl_51022,cl_51023,cl_51024,cl_51025,cl_51026,cl_51027,cl_51029,cl_51030,cl_51032,cl_51033,cl_51034,cl_51036,cl_51037,cl_51038,cl_51039,cl_51040,cl_51041,cl_51042,cl_51043,cl_51044,cl_51045,cl_51046,cl_51047,cl_51048,cl_51049,cl_51050,cl_51051,cl_51052,cl_51053,cl_51054,cl_51057,cl_51058,cl_51059,cl_51060,cl_51061,cl_51062,cl_51064,cl_51066,cl_51067,cl_51068,cl_51069,cl_51070,cl_51071,cl_51072,cl_51073,cl_51074,cl_51076,cl_51078,cl_51079,cl_51080,cl_51081,cl_51084,cl_51085,cl_51086,cl_51087,cl_51088,cl_51089,cl_51090,cl_51092,cl_51094,cl_51095,cl_51099,cl_51100,cl_51104,cl_51105,cl_51108,cl_51109,cl_51111,cl_51112,cl_51113,cl_51114,cl_51115,cl_51116,cl_51117,cl_51119,cl_51121,cl_51122,cl_51125,cl_51129,cl_51130,cl_51131,cl_51132,cl_51133,cl_51134,cl_51135,cl_51136,cl_51137,cl_51139,cl_51140,cl_51141,cl_51142,cl_51143,cl_51144,cl_51145,cl_51146,cl_51147,cl_51148,cl_51149,cl_51150,cl_51151,cl_51152,cl_51153,cl_51154,cl_51155,cl_51156,cl_51157,cl_51158,cl_51160,cl_51161,cl_51162,cl_51163,cl_51164,cl_51165,cl_51166,cl_51167,cl_51168,cl_51169,cl_51170,cl_51171,cl_51172,cl_51173,cl_51175,cl_51176,cl_51177,cl_51178,cl_51179,cl_51180,cl_51181,cl_51182,cl_51183,cl_51184,cl_51185,cl_51186,cl_51187,cl_51188,cl_51190,cl_51191,cl_51193,cl_51194,cl_51195,cl_51196,cl_51197,cl_51198]
theorem chunk_sound047 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : ∀ c ∈ chunk047, CNF.Holds (v ∘ decodeVar) c :=
  (hints_cons _ _ _ (der_50548 v h) (hints_cons _ _ _ (der_50549 v h) (hints_cons _ _ _ (der_50550 v h) (hints_cons _ _ _ (der_50551 v h) (hints_cons _ _ _ (der_50554 v h) (hints_cons _ _ _ (der_50559 v h) (hints_cons _ _ _ (der_50563 v h) (hints_cons _ _ _ (der_50565 v h) (hints_cons _ _ _ (der_50566 v h) (hints_cons _ _ _ (der_50567 v h) (hints_cons _ _ _ (der_50568 v h) (hints_cons _ _ _ (der_50570 v h) (hints_cons _ _ _ (der_50573 v h) (hints_cons _ _ _ (der_50574 v h) (hints_cons _ _ _ (der_50586 v h) (hints_cons _ _ _ (der_50587 v h) (hints_cons _ _ _ (der_50588 v h) (hints_cons _ _ _ (der_50589 v h) (hints_cons _ _ _ (der_50590 v h) (hints_cons _ _ _ (der_50591 v h) (hints_cons _ _ _ (der_50592 v h) (hints_cons _ _ _ (der_50593 v h) (hints_cons _ _ _ (der_50594 v h) (hints_cons _ _ _ (der_50595 v h) (hints_cons _ _ _ (der_50596 v h) (hints_cons _ _ _ (der_50597 v h) (hints_cons _ _ _ (der_50598 v h) (hints_cons _ _ _ (der_50599 v h) (hints_cons _ _ _ (der_50601 v h) (hints_cons _ _ _ (der_50602 v h) (hints_cons _ _ _ (der_50603 v h) (hints_cons _ _ _ (der_50604 v h) (hints_cons _ _ _ (der_50605 v h) (hints_cons _ _ _ (der_50606 v h) (hints_cons _ _ _ (der_50607 v h) (hints_cons _ _ _ (der_50608 v h) (hints_cons _ _ _ (der_50609 v h) (hints_cons _ _ _ (der_50610 v h) (hints_cons _ _ _ (der_50611 v h) (hints_cons _ _ _ (der_50612 v h) (hints_cons _ _ _ (der_50613 v h) (hints_cons _ _ _ (der_50614 v h) (hints_cons _ _ _ (der_50615 v h) (hints_cons _ _ _ (der_50616 v h) (hints_cons _ _ _ (der_50617 v h) (hints_cons _ _ _ (der_50618 v h) (hints_cons _ _ _ (der_50619 v h) (hints_cons _ _ _ (der_50620 v h) (hints_cons _ _ _ (der_50621 v h) (hints_cons _ _ _ (der_50623 v h) (hints_cons _ _ _ (der_50624 v h) (hints_cons _ _ _ (der_50625 v h) (hints_cons _ _ _ (der_50626 v h) (hints_cons _ _ _ (der_50627 v h) (hints_cons _ _ _ (der_50628 v h) (hints_cons _ _ _ (der_50629 v h) (hints_cons _ _ _ (der_50630 v h) (hints_cons _ _ _ (der_50631 v h) (hints_cons _ _ _ (der_50634 v h) (hints_cons _ _ _ (der_50635 v h) (hints_cons _ _ _ (der_50636 v h) (hints_cons _ _ _ (der_50637 v h) (hints_cons _ _ _ (der_50639 v h) (hints_cons _ _ _ (der_50640 v h) (hints_cons _ _ _ (der_50641 v h) (hints_cons _ _ _ (der_50642 v h) (hints_cons _ _ _ (der_50643 v h) (hints_cons _ _ _ (der_50645 v h) (hints_cons _ _ _ (der_50646 v h) (hints_cons _ _ _ (der_50647 v h) (hints_cons _ _ _ (der_50648 v h) (hints_cons _ _ _ (der_50649 v h) (hints_cons _ _ _ (der_50650 v h) (hints_cons _ _ _ (der_50651 v h) (hints_cons _ _ _ (der_50652 v h) (hints_cons _ _ _ (der_50653 v h) (hints_cons _ _ _ (der_50654 v h) (hints_cons _ _ _ (der_50656 v h) (hints_cons _ _ _ (der_50660 v h) (hints_cons _ _ _ (der_50661 v h) (hints_cons _ _ _ (der_50662 v h) (hints_cons _ _ _ (der_50663 v h) (hints_cons _ _ _ (der_50666 v h) (hints_cons _ _ _ (der_50667 v h) (hints_cons _ _ _ (der_50668 v h) (hints_cons _ _ _ (der_50669 v h) (hints_cons _ _ _ (der_50670 v h) (hints_cons _ _ _ (der_50671 v h) (hints_cons _ _ _ (der_50672 v h) (hints_cons _ _ _ (der_50676 v h) (hints_cons _ _ _ (der_50678 v h) (hints_cons _ _ _ (der_50679 v h) (hints_cons _ _ _ (der_50680 v h) (hints_cons _ _ _ (der_50681 v h) (hints_cons _ _ _ (der_50682 v h) (hints_cons _ _ _ (der_50683 v h) (hints_cons _ _ _ (der_50684 v h) (hints_cons _ _ _ (der_50685 v h) (hints_cons _ _ _ (der_50686 v h) (hints_cons _ _ _ (der_50687 v h) (hints_cons _ _ _ (der_50688 v h) (hints_cons _ _ _ (der_50689 v h) (hints_cons _ _ _ (der_50690 v h) (hints_cons _ _ _ (der_50691 v h) (hints_cons _ _ _ (der_50692 v h) (hints_cons _ _ _ (der_50693 v h) (hints_cons _ _ _ (der_50694 v h) (hints_cons _ _ _ (der_50695 v h) (hints_cons _ _ _ (der_50696 v h) (hints_cons _ _ _ (der_50697 v h) (hints_cons _ _ _ (der_50698 v h) (hints_cons _ _ _ (der_50699 v h) (hints_cons _ _ _ (der_50700 v h) (hints_cons _ _ _ (der_50701 v h) (hints_cons _ _ _ (der_50704 v h) (hints_cons _ _ _ (der_50706 v h) (hints_cons _ _ _ (der_50707 v h) (hints_cons _ _ _ (der_50708 v h) (hints_cons _ _ _ (der_50709 v h) (hints_cons _ _ _ (der_50712 v h) (hints_cons _ _ _ (der_50713 v h) (hints_cons _ _ _ (der_50714 v h) (hints_cons _ _ _ (der_50718 v h) (hints_cons _ _ _ (der_50719 v h) (hints_cons _ _ _ (der_50720 v h) (hints_cons _ _ _ (der_50721 v h) (hints_cons _ _ _ (der_50722 v h) (hints_cons _ _ _ (der_50724 v h) (hints_cons _ _ _ (der_50726 v h) (hints_cons _ _ _ (der_50727 v h) (hints_cons _ _ _ (der_50728 v h) (hints_cons _ _ _ (der_50729 v h) (hints_cons _ _ _ (der_50730 v h) (hints_cons _ _ _ (der_50731 v h) (hints_cons _ _ _ (der_50732 v h) (hints_cons _ _ _ (der_50734 v h) (hints_cons _ _ _ (der_50736 v h) (hints_cons _ _ _ (der_50738 v h) (hints_cons _ _ _ (der_50739 v h) (hints_cons _ _ _ (der_50740 v h) (hints_cons _ _ _ (der_50741 v h) (hints_cons _ _ _ (der_50742 v h) (hints_cons _ _ _ (der_50743 v h) (hints_cons _ _ _ (der_50744 v h) (hints_cons _ _ _ (der_50745 v h) (hints_cons _ _ _ (der_50746 v h) (hints_cons _ _ _ (der_50747 v h) (hints_cons _ _ _ (der_50750 v h) (hints_cons _ _ _ (der_50751 v h) (hints_cons _ _ _ (der_50753 v h) (hints_cons _ _ _ (der_50754 v h) (hints_cons _ _ _ (der_50755 v h) (hints_cons _ _ _ (der_50756 v h) (hints_cons _ _ _ (der_50758 v h) (hints_cons _ _ _ (der_50760 v h) (hints_cons _ _ _ (der_50761 v h) (hints_cons _ _ _ (der_50762 v h) (hints_cons _ _ _ (der_50765 v h) (hints_cons _ _ _ (der_50766 v h) (hints_cons _ _ _ (der_50767 v h) (hints_cons _ _ _ (der_50769 v h) (hints_cons _ _ _ (der_50770 v h) (hints_cons _ _ _ (der_50771 v h) (hints_cons _ _ _ (der_50772 v h) (hints_cons _ _ _ (der_50774 v h) (hints_cons _ _ _ (der_50775 v h) (hints_cons _ _ _ (der_50776 v h) (hints_cons _ _ _ (der_50777 v h) (hints_cons _ _ _ (der_50778 v h) (hints_cons _ _ _ (der_50780 v h) (hints_cons _ _ _ (der_50781 v h) (hints_cons _ _ _ (der_50782 v h) (hints_cons _ _ _ (der_50783 v h) (hints_cons _ _ _ (der_50784 v h) (hints_cons _ _ _ (der_50785 v h) (hints_cons _ _ _ (der_50786 v h) (hints_cons _ _ _ (der_50787 v h) (hints_cons _ _ _ (der_50788 v h) (hints_cons _ _ _ (der_50789 v h) (hints_cons _ _ _ (der_50790 v h) (hints_cons _ _ _ (der_50791 v h) (hints_cons _ _ _ (der_50792 v h) (hints_cons _ _ _ (der_50793 v h) (hints_cons _ _ _ (der_50794 v h) (hints_cons _ _ _ (der_50796 v h) (hints_cons _ _ _ (der_50798 v h) (hints_cons _ _ _ (der_50799 v h) (hints_cons _ _ _ (der_50800 v h) (hints_cons _ _ _ (der_50801 v h) (hints_cons _ _ _ (der_50802 v h) (hints_cons _ _ _ (der_50803 v h) (hints_cons _ _ _ (der_50804 v h) (hints_cons _ _ _ (der_50805 v h) (hints_cons _ _ _ (der_50807 v h) (hints_cons _ _ _ (der_50809 v h) (hints_cons _ _ _ (der_50810 v h) (hints_cons _ _ _ (der_50814 v h) (hints_cons _ _ _ (der_50815 v h) (hints_cons _ _ _ (der_50818 v h) (hints_cons _ _ _ (der_50820 v h) (hints_cons _ _ _ (der_50821 v h) (hints_cons _ _ _ (der_50823 v h) (hints_cons _ _ _ (der_50824 v h) (hints_cons _ _ _ (der_50826 v h) (hints_cons _ _ _ (der_50827 v h) (hints_cons _ _ _ (der_50828 v h) (hints_cons _ _ _ (der_50829 v h) (hints_cons _ _ _ (der_50830 v h) (hints_cons _ _ _ (der_50831 v h) (hints_cons _ _ _ (der_50832 v h) (hints_cons _ _ _ (der_50833 v h) (hints_cons _ _ _ (der_50834 v h) (hints_cons _ _ _ (der_50835 v h) (hints_cons _ _ _ (der_50836 v h) (hints_cons _ _ _ (der_50838 v h) (hints_cons _ _ _ (der_50839 v h) (hints_cons _ _ _ (der_50840 v h) (hints_cons _ _ _ (der_50841 v h) (hints_cons _ _ _ (der_50842 v h) (hints_cons _ _ _ (der_50843 v h) (hints_cons _ _ _ (der_50844 v h) (hints_cons _ _ _ (der_50845 v h) (hints_cons _ _ _ (der_50846 v h) (hints_cons _ _ _ (der_50847 v h) (hints_cons _ _ _ (der_50848 v h) (hints_cons _ _ _ (der_50849 v h) (hints_cons _ _ _ (der_50850 v h) (hints_cons _ _ _ (der_50851 v h) (hints_cons _ _ _ (der_50852 v h) (hints_cons _ _ _ (der_50854 v h) (hints_cons _ _ _ (der_50855 v h) (hints_cons _ _ _ (der_50856 v h) (hints_cons _ _ _ (der_50857 v h) (hints_cons _ _ _ (der_50858 v h) (hints_cons _ _ _ (der_50859 v h) (hints_cons _ _ _ (der_50860 v h) (hints_cons _ _ _ (der_50862 v h) (hints_cons _ _ _ (der_50863 v h) (hints_cons _ _ _ (der_50864 v h) (hints_cons _ _ _ (der_50865 v h) (hints_cons _ _ _ (der_50866 v h) (hints_cons _ _ _ (der_50867 v h) (hints_cons _ _ _ (der_50868 v h) (hints_cons _ _ _ (der_50869 v h) (hints_cons _ _ _ (der_50870 v h) (hints_cons _ _ _ (der_50874 v h) (hints_cons _ _ _ (der_50875 v h) (hints_cons _ _ _ (der_50876 v h) (hints_cons _ _ _ (der_50877 v h) (hints_cons _ _ _ (der_50878 v h) (hints_cons _ _ _ (der_50879 v h) (hints_cons _ _ _ (der_50880 v h) (hints_cons _ _ _ (der_50881 v h) (hints_cons _ _ _ (der_50882 v h) (hints_cons _ _ _ (der_50883 v h) (hints_cons _ _ _ (der_50884 v h) (hints_cons _ _ _ (der_50885 v h) (hints_cons _ _ _ (der_50886 v h) (hints_cons _ _ _ (der_50888 v h) (hints_cons _ _ _ (der_50889 v h) (hints_cons _ _ _ (der_50890 v h) (hints_cons _ _ _ (der_50892 v h) (hints_cons _ _ _ (der_50893 v h) (hints_cons _ _ _ (der_50894 v h) (hints_cons _ _ _ (der_50895 v h) (hints_cons _ _ _ (der_50896 v h) (hints_cons _ _ _ (der_50897 v h) (hints_cons _ _ _ (der_50899 v h) (hints_cons _ _ _ (der_50900 v h) (hints_cons _ _ _ (der_50901 v h) (hints_cons _ _ _ (der_50902 v h) (hints_cons _ _ _ (der_50903 v h) (hints_cons _ _ _ (der_50904 v h) (hints_cons _ _ _ (der_50905 v h) (hints_cons _ _ _ (der_50906 v h) (hints_cons _ _ _ (der_50907 v h) (hints_cons _ _ _ (der_50908 v h) (hints_cons _ _ _ (der_50909 v h) (hints_cons _ _ _ (der_50910 v h) (hints_cons _ _ _ (der_50911 v h) (hints_cons _ _ _ (der_50912 v h) (hints_cons _ _ _ (der_50913 v h) (hints_cons _ _ _ (der_50914 v h) (hints_cons _ _ _ (der_50915 v h) (hints_cons _ _ _ (der_50917 v h) (hints_cons _ _ _ (der_50918 v h) (hints_cons _ _ _ (der_50919 v h) (hints_cons _ _ _ (der_50921 v h) (hints_cons _ _ _ (der_50922 v h) (hints_cons _ _ _ (der_50923 v h) (hints_cons _ _ _ (der_50924 v h) (hints_cons _ _ _ (der_50925 v h) (hints_cons _ _ _ (der_50926 v h) (hints_cons _ _ _ (der_50927 v h) (hints_cons _ _ _ (der_50929 v h) (hints_cons _ _ _ (der_50930 v h) (hints_cons _ _ _ (der_50931 v h) (hints_cons _ _ _ (der_50932 v h) (hints_cons _ _ _ (der_50933 v h) (hints_cons _ _ _ (der_50934 v h) (hints_cons _ _ _ (der_50935 v h) (hints_cons _ _ _ (der_50936 v h) (hints_cons _ _ _ (der_50937 v h) (hints_cons _ _ _ (der_50938 v h) (hints_cons _ _ _ (der_50939 v h) (hints_cons _ _ _ (der_50940 v h) (hints_cons _ _ _ (der_50941 v h) (hints_cons _ _ _ (der_50942 v h) (hints_cons _ _ _ (der_50943 v h) (hints_cons _ _ _ (der_50944 v h) (hints_cons _ _ _ (der_50945 v h) (hints_cons _ _ _ (der_50946 v h) (hints_cons _ _ _ (der_50947 v h) (hints_cons _ _ _ (der_50948 v h) (hints_cons _ _ _ (der_50950 v h) (hints_cons _ _ _ (der_50951 v h) (hints_cons _ _ _ (der_50953 v h) (hints_cons _ _ _ (der_50955 v h) (hints_cons _ _ _ (der_50956 v h) (hints_cons _ _ _ (der_50961 v h) (hints_cons _ _ _ (der_50962 v h) (hints_cons _ _ _ (der_50965 v h) (hints_cons _ _ _ (der_50968 v h) (hints_cons _ _ _ (der_50970 v h) (hints_cons _ _ _ (der_50971 v h) (hints_cons _ _ _ (der_50973 v h) (hints_cons _ _ _ (der_50975 v h) (hints_cons _ _ _ (der_50976 v h) (hints_cons _ _ _ (der_50977 v h) (hints_cons _ _ _ (der_50978 v h) (hints_cons _ _ _ (der_50979 v h) (hints_cons _ _ _ (der_50980 v h) (hints_cons _ _ _ (der_50981 v h) (hints_cons _ _ _ (der_50982 v h) (hints_cons _ _ _ (der_50983 v h) (hints_cons _ _ _ (der_50984 v h) (hints_cons _ _ _ (der_50985 v h) (hints_cons _ _ _ (der_50986 v h) (hints_cons _ _ _ (der_50987 v h) (hints_cons _ _ _ (der_50988 v h) (hints_cons _ _ _ (der_50989 v h) (hints_cons _ _ _ (der_50990 v h) (hints_cons _ _ _ (der_50992 v h) (hints_cons _ _ _ (der_50998 v h) (hints_cons _ _ _ (der_51006 v h) (hints_cons _ _ _ (der_51007 v h) (hints_cons _ _ _ (der_51008 v h) (hints_cons _ _ _ (der_51009 v h) (hints_cons _ _ _ (der_51010 v h) (hints_cons _ _ _ (der_51011 v h) (hints_cons _ _ _ (der_51013 v h) (hints_cons _ _ _ (der_51016 v h) (hints_cons _ _ _ (der_51017 v h) (hints_cons _ _ _ (der_51018 v h) (hints_cons _ _ _ (der_51019 v h) (hints_cons _ _ _ (der_51020 v h) (hints_cons _ _ _ (der_51021 v h) (hints_cons _ _ _ (der_51022 v h) (hints_cons _ _ _ (der_51023 v h) (hints_cons _ _ _ (der_51024 v h) (hints_cons _ _ _ (der_51025 v h) (hints_cons _ _ _ (der_51026 v h) (hints_cons _ _ _ (der_51027 v h) (hints_cons _ _ _ (der_51029 v h) (hints_cons _ _ _ (der_51030 v h) (hints_cons _ _ _ (der_51032 v h) (hints_cons _ _ _ (der_51033 v h) (hints_cons _ _ _ (der_51034 v h) (hints_cons _ _ _ (der_51036 v h) (hints_cons _ _ _ (der_51037 v h) (hints_cons _ _ _ (der_51038 v h) (hints_cons _ _ _ (der_51039 v h) (hints_cons _ _ _ (der_51040 v h) (hints_cons _ _ _ (der_51041 v h) (hints_cons _ _ _ (der_51042 v h) (hints_cons _ _ _ (der_51043 v h) (hints_cons _ _ _ (der_51044 v h) (hints_cons _ _ _ (der_51045 v h) (hints_cons _ _ _ (der_51046 v h) (hints_cons _ _ _ (der_51047 v h) (hints_cons _ _ _ (der_51048 v h) (hints_cons _ _ _ (der_51049 v h) (hints_cons _ _ _ (der_51050 v h) (hints_cons _ _ _ (der_51051 v h) (hints_cons _ _ _ (der_51052 v h) (hints_cons _ _ _ (der_51053 v h) (hints_cons _ _ _ (der_51054 v h) (hints_cons _ _ _ (der_51057 v h) (hints_cons _ _ _ (der_51058 v h) (hints_cons _ _ _ (der_51059 v h) (hints_cons _ _ _ (der_51060 v h) (hints_cons _ _ _ (der_51061 v h) (hints_cons _ _ _ (der_51062 v h) (hints_cons _ _ _ (der_51064 v h) (hints_cons _ _ _ (der_51066 v h) (hints_cons _ _ _ (der_51067 v h) (hints_cons _ _ _ (der_51068 v h) (hints_cons _ _ _ (der_51069 v h) (hints_cons _ _ _ (der_51070 v h) (hints_cons _ _ _ (der_51071 v h) (hints_cons _ _ _ (der_51072 v h) (hints_cons _ _ _ (der_51073 v h) (hints_cons _ _ _ (der_51074 v h) (hints_cons _ _ _ (der_51076 v h) (hints_cons _ _ _ (der_51078 v h) (hints_cons _ _ _ (der_51079 v h) (hints_cons _ _ _ (der_51080 v h) (hints_cons _ _ _ (der_51081 v h) (hints_cons _ _ _ (der_51084 v h) (hints_cons _ _ _ (der_51085 v h) (hints_cons _ _ _ (der_51086 v h) (hints_cons _ _ _ (der_51087 v h) (hints_cons _ _ _ (der_51088 v h) (hints_cons _ _ _ (der_51089 v h) (hints_cons _ _ _ (der_51090 v h) (hints_cons _ _ _ (der_51092 v h) (hints_cons _ _ _ (der_51094 v h) (hints_cons _ _ _ (der_51095 v h) (hints_cons _ _ _ (der_51099 v h) (hints_cons _ _ _ (der_51100 v h) (hints_cons _ _ _ (der_51104 v h) (hints_cons _ _ _ (der_51105 v h) (hints_cons _ _ _ (der_51108 v h) (hints_cons _ _ _ (der_51109 v h) (hints_cons _ _ _ (der_51111 v h) (hints_cons _ _ _ (der_51112 v h) (hints_cons _ _ _ (der_51113 v h) (hints_cons _ _ _ (der_51114 v h) (hints_cons _ _ _ (der_51115 v h) (hints_cons _ _ _ (der_51116 v h) (hints_cons _ _ _ (der_51117 v h) (hints_cons _ _ _ (der_51119 v h) (hints_cons _ _ _ (der_51121 v h) (hints_cons _ _ _ (der_51122 v h) (hints_cons _ _ _ (der_51125 v h) (hints_cons _ _ _ (der_51129 v h) (hints_cons _ _ _ (der_51130 v h) (hints_cons _ _ _ (der_51131 v h) (hints_cons _ _ _ (der_51132 v h) (hints_cons _ _ _ (der_51133 v h) (hints_cons _ _ _ (der_51134 v h) (hints_cons _ _ _ (der_51135 v h) (hints_cons _ _ _ (der_51136 v h) (hints_cons _ _ _ (der_51137 v h) (hints_cons _ _ _ (der_51139 v h) (hints_cons _ _ _ (der_51140 v h) (hints_cons _ _ _ (der_51141 v h) (hints_cons _ _ _ (der_51142 v h) (hints_cons _ _ _ (der_51143 v h) (hints_cons _ _ _ (der_51144 v h) (hints_cons _ _ _ (der_51145 v h) (hints_cons _ _ _ (der_51146 v h) (hints_cons _ _ _ (der_51147 v h) (hints_cons _ _ _ (der_51148 v h) (hints_cons _ _ _ (der_51149 v h) (hints_cons _ _ _ (der_51150 v h) (hints_cons _ _ _ (der_51151 v h) (hints_cons _ _ _ (der_51152 v h) (hints_cons _ _ _ (der_51153 v h) (hints_cons _ _ _ (der_51154 v h) (hints_cons _ _ _ (der_51155 v h) (hints_cons _ _ _ (der_51156 v h) (hints_cons _ _ _ (der_51157 v h) (hints_cons _ _ _ (der_51158 v h) (hints_cons _ _ _ (der_51160 v h) (hints_cons _ _ _ (der_51161 v h) (hints_cons _ _ _ (der_51162 v h) (hints_cons _ _ _ (der_51163 v h) (hints_cons _ _ _ (der_51164 v h) (hints_cons _ _ _ (der_51165 v h) (hints_cons _ _ _ (der_51166 v h) (hints_cons _ _ _ (der_51167 v h) (hints_cons _ _ _ (der_51168 v h) (hints_cons _ _ _ (der_51169 v h) (hints_cons _ _ _ (der_51170 v h) (hints_cons _ _ _ (der_51171 v h) (hints_cons _ _ _ (der_51172 v h) (hints_cons _ _ _ (der_51173 v h) (hints_cons _ _ _ (der_51175 v h) (hints_cons _ _ _ (der_51176 v h) (hints_cons _ _ _ (der_51177 v h) (hints_cons _ _ _ (der_51178 v h) (hints_cons _ _ _ (der_51179 v h) (hints_cons _ _ _ (der_51180 v h) (hints_cons _ _ _ (der_51181 v h) (hints_cons _ _ _ (der_51182 v h) (hints_cons _ _ _ (der_51183 v h) (hints_cons _ _ _ (der_51184 v h) (hints_cons _ _ _ (der_51185 v h) (hints_cons _ _ _ (der_51186 v h) (hints_cons _ _ _ (der_51187 v h) (hints_cons _ _ _ (der_51188 v h) (hints_cons _ _ _ (der_51190 v h) (hints_cons _ _ _ (der_51191 v h) (hints_cons _ _ _ (der_51193 v h) (hints_cons _ _ _ (der_51194 v h) (hints_cons _ _ _ (der_51195 v h) (hints_cons _ _ _ (der_51196 v h) (hints_cons _ _ _ (der_51197 v h) (hints_cons _ _ _ (der_51198 v h) (by intro d hd; cases hd)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def prefix047 := prefix046 ++ chunk047
theorem prefix_sound047 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : ∀ c ∈ prefix047, CNF.Holds (v ∘ decodeVar) c := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact prefix_sound046 v h c hc
  · exact chunk_sound047 v h c hc
end Percolation.NReplay
