import NReplay004
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_24678 : CNF.NClause := [(56,false),(66,false),(64,false),(65,false),(63,false),(62,false)]
theorem der_24678 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24678 :=
  CNF.rup_sound cl_24678 [cl_15521,cl_15489] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15521 v h) (hints_cons _ _ _ (der_15489 v h) (by intro d hd; cases hd)))
def cl_24679 : CNF.NClause := [(31,false),(87,true),(92,true),(89,true),(91,false),(88,false)]
theorem der_24679 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24679 :=
  CNF.rup_sound cl_24679 [cl_15470,cl_15462] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15470 v h) (hints_cons _ _ _ (der_15462 v h) (by intro d hd; cases hd)))
def cl_24680 : CNF.NClause := [(31,false),(88,false),(91,true),(87,true),(89,false),(90,false)]
theorem der_24680 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24680 :=
  CNF.rup_sound cl_24680 [cl_15474,cl_15442] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15474 v h) (hints_cons _ _ _ (der_15442 v h) (by intro d hd; cases hd)))
def cl_24681 : CNF.NClause := [(31,false),(90,true),(87,true),(89,true),(88,false),(92,true)]
theorem der_24681 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24681 :=
  CNF.rup_sound cl_24681 [cl_15486,cl_24679] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15486 v h) (hints_cons _ _ _ (der_24679 v h) (by intro d hd; cases hd)))
def cl_24682 : CNF.NClause := [(31,false),(88,false),(87,true),(91,true),(90,false),(92,false)]
theorem der_24682 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24682 :=
  CNF.rup_sound cl_24682 [cl_15446,cl_24680] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15446 v h) (hints_cons _ _ _ (der_24680 v h) (by intro d hd; cases hd)))
def cl_24683 : CNF.NClause := [(31,false),(92,true),(87,true),(89,true),(90,false),(88,false)]
theorem der_24683 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24683 :=
  CNF.rup_sound cl_24683 [cl_15478,cl_15462] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15478 v h) (hints_cons _ _ _ (der_15462 v h) (by intro d hd; cases hd)))
def cl_24684 : CNF.NClause := [(31,false),(92,false),(89,false),(87,false),(90,false),(88,false)]
theorem der_24684 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24684 :=
  CNF.rup_sound cl_24684 [cl_15441,cl_15425] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15441 v h) (hints_cons _ _ _ (der_15425 v h) (by intro d hd; cases hd)))
def cl_24685 : CNF.NClause := [(31,false),(88,false),(87,false),(91,true),(90,false),(89,false)]
theorem der_24685 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24685 :=
  CNF.rup_sound cl_24685 [cl_15473,cl_24684] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15473 v h) (hints_cons _ _ _ (der_24684 v h) (by intro d hd; cases hd)))
def cl_24686 : CNF.NClause := [(31,false),(87,true),(88,false),(89,false),(91,true),(92,false)]
theorem der_24686 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24686 :=
  CNF.rup_sound cl_24686 [cl_15450,cl_24682] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15450 v h) (hints_cons _ _ _ (der_24682 v h) (by intro d hd; cases hd)))
def cl_24687 : CNF.NClause := [(31,false),(87,true),(89,false),(92,true),(91,false),(88,false)]
theorem der_24687 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24687 :=
  CNF.rup_sound cl_24687 [cl_15466,cl_24677] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15466 v h) (hints_cons _ _ _ (der_24677 v h) (by intro d hd; cases hd)))
def cl_24688 : CNF.NClause := [(31,false),(90,true),(87,true),(88,false),(89,false),(92,true)]
theorem der_24688 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24688 :=
  CNF.rup_sound cl_24688 [cl_15482,cl_24687] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15482 v h) (hints_cons _ _ _ (der_24687 v h) (by intro d hd; cases hd)))
def cl_24689 : CNF.NClause := [(31,false),(87,false),(88,false),(89,false),(91,false),(92,false)]
theorem der_24689 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24689 :=
  CNF.rup_sound cl_24689 [cl_15433,cl_15425] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15433 v h) (hints_cons _ _ _ (der_15425 v h) (by intro d hd; cases hd)))
def cl_24690 : CNF.NClause := [(31,false),(87,false),(88,false),(89,false),(91,true),(92,false)]
theorem der_24690 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24690 :=
  CNF.rup_sound cl_24690 [cl_15449,cl_24685] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15449 v h) (hints_cons _ _ _ (der_24685 v h) (by intro d hd; cases hd)))
def cl_24691 : CNF.NClause := [(31,false),(90,true),(92,true),(89,false),(91,false),(88,false)]
theorem der_24691 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24691 :=
  CNF.rup_sound cl_24691 [cl_15465,cl_24687] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15465 v h) (hints_cons _ _ _ (der_24687 v h) (by intro d hd; cases hd)))
def cl_24692 : CNF.NClause := [(31,false),(87,false),(88,false),(89,false),(91,true),(92,true)]
theorem der_24692 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24692 :=
  CNF.rup_sound cl_24692 [cl_15481,cl_24685] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15481 v h) (hints_cons _ _ _ (der_24685 v h) (by intro d hd; cases hd)))
def cl_24693 : CNF.NClause := [(56,false),(64,false),(62,false),(92,true),(65,false),(63,false)]
theorem der_24693 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24693 :=
  CNF.rup_sound cl_24693 [cl_15537,cl_24678] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15537 v h) (hints_cons _ _ _ (der_24678 v h) (by intro d hd; cases hd)))
def cl_24694 : CNF.NClause := [(56,false),(63,false),(92,false),(62,false),(64,false),(65,false)]
theorem der_24694 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24694 :=
  CNF.rup_sound cl_24694 [cl_15505,cl_15489] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15505 v h) (hints_cons _ _ _ (der_15489 v h) (by intro d hd; cases hd)))
def cl_24695 : CNF.NClause := [(56,false),(65,false),(64,false),(63,false),(62,true),(92,false)]
theorem der_24695 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24695 :=
  CNF.rup_sound cl_24695 [cl_15506,cl_23668] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15506 v h) (hints_cons _ _ _ (der_23668 v h) (by intro d hd; cases hd)))
def cl_24696 : CNF.NClause := [(56,false),(65,false),(64,false),(63,false),(62,true),(92,true)]
theorem der_24696 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24696 :=
  CNF.rup_sound cl_24696 [cl_15538,cl_23669] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15538 v h) (hints_cons _ _ _ (der_23669 v h) (by intro d hd; cases hd)))
def cl_24697 : CNF.NClause := [(56,false),(64,false),(92,false),(63,false),(66,false),(62,false)]
theorem der_24697 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24697 :=
  CNF.rup_sound cl_24697 [cl_15497,cl_15489] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15497 v h) (hints_cons _ _ _ (der_15489 v h) (by intro d hd; cases hd)))
def cl_24698 : CNF.NClause := [(56,false),(66,true),(63,false),(62,false),(64,false),(92,false)]
theorem der_24698 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24698 :=
  CNF.rup_sound cl_24698 [cl_15513,cl_24694] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15513 v h) (hints_cons _ _ _ (der_24694 v h) (by intro d hd; cases hd)))
def cl_24699 : CNF.NClause := [(56,false),(92,true),(64,false),(62,false),(66,false),(63,false)]
theorem der_24699 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24699 :=
  CNF.rup_sound cl_24699 [cl_15529,cl_24693] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15529 v h) (hints_cons _ _ _ (der_24693 v h) (by intro d hd; cases hd)))
def cl_24700 : CNF.NClause := [(56,false),(65,true),(62,true),(63,true),(64,true),(92,false)]
theorem der_24700 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24700 :=
  CNF.rup_sound cl_24700 [cl_15520,cl_15504] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15520 v h) (hints_cons _ _ _ (der_15504 v h) (by intro d hd; cases hd)))
def cl_24701 : CNF.NClause := [(56,false),(65,true),(62,true),(63,true),(64,true),(66,false)]
theorem der_24701 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24701 :=
  CNF.rup_sound cl_24701 [cl_15536,cl_24700] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15536 v h) (hints_cons _ _ _ (der_24700 v h) (by intro d hd; cases hd)))
def cl_24702 : CNF.NClause := [(56,false),(65,true),(62,true),(63,true),(64,true),(66,true)]
theorem der_24702 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24702 :=
  CNF.rup_sound cl_24702 [cl_15552,cl_24700] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15552 v h) (hints_cons _ _ _ (der_24700 v h) (by intro d hd; cases hd)))
def cl_24703 : CNF.NClause := [(56,false),(92,true),(62,false),(65,true),(64,false),(63,false)]
theorem der_24703 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24703 :=
  CNF.rup_sound cl_24703 [cl_15545,cl_24699] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15545 v h) (hints_cons _ _ _ (der_24699 v h) (by intro d hd; cases hd)))
def cl_24704 : CNF.NClause := [(56,false),(63,false),(64,false),(62,true),(66,false),(92,false)]
theorem der_24704 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24704 :=
  CNF.rup_sound cl_24704 [cl_15498,cl_23668] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15498 v h) (hints_cons _ _ _ (der_23668 v h) (by intro d hd; cases hd)))
def cl_24705 : CNF.NClause := [(56,false),(63,false),(64,false),(62,true),(66,true),(92,false)]
theorem der_24705 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24705 :=
  CNF.rup_sound cl_24705 [cl_15514,cl_24695] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15514 v h) (hints_cons _ _ _ (der_24695 v h) (by intro d hd; cases hd)))
def cl_24706 : CNF.NClause := [(56,false),(63,false),(64,false),(62,true),(66,false),(92,true)]
theorem der_24706 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24706 :=
  CNF.rup_sound cl_24706 [cl_15530,cl_23669] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15530 v h) (hints_cons _ _ _ (der_23669 v h) (by intro d hd; cases hd)))
def cl_24707 : CNF.NClause := [(56,false),(63,false),(64,false),(62,true),(66,true),(92,true)]
theorem der_24707 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24707 :=
  CNF.rup_sound cl_24707 [cl_15546,cl_24696] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15546 v h) (hints_cons _ _ _ (der_24696 v h) (by intro d hd; cases hd)))
def cl_24708 : CNF.NClause := [(110,true),(33,false),(39,true),(46,false),(52,false),(57,false)]
theorem der_24708 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24708 :=
  CNF.rup_sound cl_24708 [cl_3079,cl_3075] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3079 v h) (hints_cons _ _ _ (inp_3075 v h) (by intro d hd; cases hd)))
def cl_24709 : CNF.NClause := [(110,true),(33,false),(39,true),(45,false),(52,false),(57,false)]
theorem der_24709 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24709 :=
  CNF.rup_sound cl_24709 [cl_3083,cl_3075] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3083 v h) (hints_cons _ _ _ (inp_3075 v h) (by intro d hd; cases hd)))
def cl_24710 : CNF.NClause := [(110,true),(33,false),(39,true),(45,true),(52,false),(57,false)]
theorem der_24710 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24710 :=
  CNF.rup_sound cl_24710 [cl_3087,cl_24708] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3087 v h) (hints_cons _ _ _ (der_24708 v h) (by intro d hd; cases hd)))
def cl_24711 : CNF.NClause := [(110,true),(33,false),(45,false),(46,false),(52,true),(57,false)]
theorem der_24711 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24711 :=
  CNF.rup_sound cl_24711 [cl_3091,cl_3089] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3091 v h) (hints_cons _ _ _ (inp_3089 v h) (by intro d hd; cases hd)))
def cl_24712 : CNF.NClause := [(110,true),(33,false),(45,true),(46,false),(52,true),(57,false)]
theorem der_24712 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24712 :=
  CNF.rup_sound cl_24712 [cl_3095,cl_23799] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3095 v h) (hints_cons _ _ _ (der_23799 v h) (by intro d hd; cases hd)))
def cl_24713 : CNF.NClause := [(110,true),(33,false),(39,true),(45,false),(46,true),(57,false)]
theorem der_24713 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24713 :=
  CNF.rup_sound cl_24713 [cl_3099,cl_24709] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3099 v h) (hints_cons _ _ _ (der_24709 v h) (by intro d hd; cases hd)))
def cl_24714 : CNF.NClause := [(110,true),(33,false),(45,true),(46,true),(52,true),(57,false)]
theorem der_24714 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24714 :=
  CNF.rup_sound cl_24714 [cl_3103,cl_3101] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3103 v h) (hints_cons _ _ _ (inp_3101 v h) (by intro d hd; cases hd)))
def cl_24715 : CNF.NClause := [(110,true),(33,false),(39,true),(45,false),(46,false),(52,false)]
theorem der_24715 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24715 :=
  CNF.rup_sound cl_24715 [cl_3107,cl_3075] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3107 v h) (hints_cons _ _ _ (inp_3075 v h) (by intro d hd; cases hd)))
def cl_24716 : CNF.NClause := [(110,true),(33,false),(39,true),(45,true),(46,false),(52,false)]
theorem der_24716 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24716 :=
  CNF.rup_sound cl_24716 [cl_3111,cl_24708] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3111 v h) (hints_cons _ _ _ (der_24708 v h) (by intro d hd; cases hd)))
def cl_24717 : CNF.NClause := [(110,true),(33,false),(39,true),(45,false),(46,true),(52,false)]
theorem der_24717 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24717 :=
  CNF.rup_sound cl_24717 [cl_3115,cl_24713] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3115 v h) (hints_cons _ _ _ (der_24713 v h) (by intro d hd; cases hd)))
def cl_24718 : CNF.NClause := [(110,true),(33,false),(39,true),(45,true),(52,false),(57,true)]
theorem der_24718 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24718 :=
  CNF.rup_sound cl_24718 [cl_3119,cl_24716] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3119 v h) (hints_cons _ _ _ (der_24716 v h) (by intro d hd; cases hd)))
def cl_24719 : CNF.NClause := [(110,true),(33,false),(39,true),(45,false),(46,false),(57,true)]
theorem der_24719 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24719 :=
  CNF.rup_sound cl_24719 [cl_3123,cl_24715] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3123 v h) (hints_cons _ _ _ (der_24715 v h) (by intro d hd; cases hd)))
def cl_24720 : CNF.NClause := [(110,true),(33,false),(39,true),(45,true),(46,false),(57,true)]
theorem der_24720 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24720 :=
  CNF.rup_sound cl_24720 [cl_3127,cl_24716] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3127 v h) (hints_cons _ _ _ (der_24716 v h) (by intro d hd; cases hd)))
def cl_24721 : CNF.NClause := [(110,true),(33,false),(39,true),(45,false),(46,true),(52,true)]
theorem der_24721 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24721 :=
  CNF.rup_sound cl_24721 [cl_3131,cl_24713] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3131 v h) (hints_cons _ _ _ (der_24713 v h) (by intro d hd; cases hd)))
def cl_24722 : CNF.NClause := [(107,true),(32,false),(41,false),(48,false),(55,false),(58,false)]
theorem der_24722 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24722 :=
  CNF.rup_sound cl_24722 [cl_2883,cl_23903] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2883 v h) (hints_cons _ _ _ (der_23903 v h) (by intro d hd; cases hd)))
def cl_24723 : CNF.NClause := [(107,true),(32,false),(39,true),(48,false),(55,false),(58,false)]
theorem der_24723 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24723 :=
  CNF.rup_sound cl_24723 [cl_2887,cl_24722] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2887 v h) (hints_cons _ _ _ (der_24722 v h) (by intro d hd; cases hd)))
def cl_24724 : CNF.NClause := [(107,true),(32,false),(41,false),(48,true),(55,false),(58,false)]
theorem der_24724 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24724 :=
  CNF.rup_sound cl_24724 [cl_2891,cl_2889] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2891 v h) (hints_cons _ _ _ (inp_2889 v h) (by intro d hd; cases hd)))
def cl_24725 : CNF.NClause := [(107,true),(32,false),(39,true),(41,true),(55,false),(58,false)]
theorem der_24725 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24725 :=
  CNF.rup_sound cl_24725 [cl_2895,cl_24723] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2895 v h) (hints_cons _ _ _ (der_24723 v h) (by intro d hd; cases hd)))
def cl_24726 : CNF.NClause := [(107,true),(32,false),(39,true),(41,false),(48,false),(58,false)]
theorem der_24726 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24726 :=
  CNF.rup_sound cl_24726 [cl_2899,cl_24722] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2899 v h) (hints_cons _ _ _ (der_24722 v h) (by intro d hd; cases hd)))
def cl_24727 : CNF.NClause := [(107,true),(32,false),(39,true),(41,true),(48,false),(58,false)]
theorem der_24727 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24727 :=
  CNF.rup_sound cl_24727 [cl_2903,cl_24723] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2903 v h) (hints_cons _ _ _ (der_24723 v h) (by intro d hd; cases hd)))
def cl_24728 : CNF.NClause := [(107,true),(32,false),(39,true),(41,false),(55,true),(58,false)]
theorem der_24728 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24728 :=
  CNF.rup_sound cl_24728 [cl_2907,cl_24726] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2907 v h) (hints_cons _ _ _ (der_24726 v h) (by intro d hd; cases hd)))
def cl_24729 : CNF.NClause := [(107,true),(32,false),(39,true),(41,true),(48,true),(58,false)]
theorem der_24729 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24729 :=
  CNF.rup_sound cl_24729 [cl_2911,cl_24725] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2911 v h) (hints_cons _ _ _ (der_24725 v h) (by intro d hd; cases hd)))
def cl_24730 : CNF.NClause := [(107,true),(32,false),(39,true),(41,false),(48,false),(55,false)]
theorem der_24730 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24730 :=
  CNF.rup_sound cl_24730 [cl_2915,cl_24722] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2915 v h) (hints_cons _ _ _ (der_24722 v h) (by intro d hd; cases hd)))
def cl_24731 : CNF.NClause := [(107,true),(32,false),(39,true),(41,true),(48,false),(55,false)]
theorem der_24731 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24731 :=
  CNF.rup_sound cl_24731 [cl_2919,cl_24723] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2919 v h) (hints_cons _ _ _ (der_24723 v h) (by intro d hd; cases hd)))
def cl_24732 : CNF.NClause := [(107,true),(32,false),(39,true),(41,false),(48,true),(55,false)]
theorem der_24732 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24732 :=
  CNF.rup_sound cl_24732 [cl_2923,cl_24724] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2923 v h) (hints_cons _ _ _ (der_24724 v h) (by intro d hd; cases hd)))
def cl_24733 : CNF.NClause := [(107,true),(32,false),(39,true),(41,true),(48,true),(55,false)]
theorem der_24733 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24733 :=
  CNF.rup_sound cl_24733 [cl_2927,cl_24725] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2927 v h) (hints_cons _ _ _ (der_24725 v h) (by intro d hd; cases hd)))
def cl_24734 : CNF.NClause := [(107,true),(32,false),(39,true),(41,false),(48,false),(55,true)]
theorem der_24734 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24734 :=
  CNF.rup_sound cl_24734 [cl_2931,cl_24728] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2931 v h) (hints_cons _ _ _ (der_24728 v h) (by intro d hd; cases hd)))
def cl_24735 : CNF.NClause := [(107,true),(32,false),(39,true),(41,true),(48,false),(58,true)]
theorem der_24735 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24735 :=
  CNF.rup_sound cl_24735 [cl_2935,cl_24731] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2935 v h) (hints_cons _ _ _ (der_24731 v h) (by intro d hd; cases hd)))
def cl_24736 : CNF.NClause := [(107,true),(32,false),(39,true),(41,false),(48,true),(55,true)]
theorem der_24736 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24736 :=
  CNF.rup_sound cl_24736 [cl_2939,cl_24728] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2939 v h) (hints_cons _ _ _ (der_24728 v h) (by intro d hd; cases hd)))
def cl_24737 : CNF.NClause := [(99,true),(47,false),(43,false),(35,false),(51,false),(60,false)]
theorem der_24737 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24737 :=
  CNF.rup_sound cl_24737 [cl_2371,cl_2369] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2371 v h) (hints_cons _ _ _ (inp_2369 v h) (by intro d hd; cases hd)))
def cl_24738 : CNF.NClause := [(99,true),(47,false),(39,true),(35,false),(51,false),(60,false)]
theorem der_24738 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24738 :=
  CNF.rup_sound cl_24738 [cl_2375,cl_24737] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2375 v h) (hints_cons _ _ _ (der_24737 v h) (by intro d hd; cases hd)))
def cl_24739 : CNF.NClause := [(99,true),(51,false),(43,false),(47,true),(35,false),(60,false)]
theorem der_24739 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24739 :=
  CNF.rup_sound cl_24739 [cl_2379,cl_23841] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2379 v h) (hints_cons _ _ _ (der_23841 v h) (by intro d hd; cases hd)))
def cl_24740 : CNF.NClause := [(99,true),(51,false),(39,true),(47,true),(35,false),(60,false)]
theorem der_24740 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24740 :=
  CNF.rup_sound cl_24740 [cl_2383,cl_24739] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2383 v h) (hints_cons _ _ _ (der_24739 v h) (by intro d hd; cases hd)))
def cl_24741 : CNF.NClause := [(99,true),(47,false),(39,true),(43,false),(35,false),(60,false)]
theorem der_24741 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24741 :=
  CNF.rup_sound cl_24741 [cl_2387,cl_24737] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2387 v h) (hints_cons _ _ _ (der_24737 v h) (by intro d hd; cases hd)))
def cl_24742 : CNF.NClause := [(99,true),(47,false),(39,true),(35,false),(51,true),(60,false)]
theorem der_24742 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24742 :=
  CNF.rup_sound cl_24742 [cl_2391,cl_24741] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2391 v h) (hints_cons _ _ _ (der_24741 v h) (by intro d hd; cases hd)))
def cl_24743 : CNF.NClause := [(99,true),(35,false),(39,true),(43,false),(47,true),(60,false)]
theorem der_24743 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24743 :=
  CNF.rup_sound cl_24743 [cl_2395,cl_24739] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2395 v h) (hints_cons _ _ _ (der_24739 v h) (by intro d hd; cases hd)))
def cl_24744 : CNF.NClause := [(99,true),(35,false),(39,true),(43,true),(51,true),(60,false)]
theorem der_24744 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24744 :=
  CNF.rup_sound cl_24744 [cl_2399,cl_24742] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2399 v h) (hints_cons _ _ _ (der_24742 v h) (by intro d hd; cases hd)))
def cl_24745 : CNF.NClause := [(99,true),(47,false),(39,true),(43,false),(35,false),(51,false)]
theorem der_24745 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24745 :=
  CNF.rup_sound cl_24745 [cl_2403,cl_24737] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2403 v h) (hints_cons _ _ _ (der_24737 v h) (by intro d hd; cases hd)))
def cl_24746 : CNF.NClause := [(99,true),(47,false),(39,true),(35,false),(51,false),(60,true)]
theorem der_24746 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24746 :=
  CNF.rup_sound cl_24746 [cl_2407,cl_24745] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2407 v h) (hints_cons _ _ _ (der_24745 v h) (by intro d hd; cases hd)))
def cl_24747 : CNF.NClause := [(99,true),(51,false),(43,false),(47,true),(35,false),(60,true)]
theorem der_24747 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24747 :=
  CNF.rup_sound cl_24747 [cl_2411,cl_2409] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2411 v h) (hints_cons _ _ _ (inp_2409 v h) (by intro d hd; cases hd)))
def cl_24748 : CNF.NClause := [(99,true),(51,false),(39,true),(43,true),(47,true),(35,false)]
theorem der_24748 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24748 :=
  CNF.rup_sound cl_24748 [cl_2415,cl_24740] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2415 v h) (hints_cons _ _ _ (der_24740 v h) (by intro d hd; cases hd)))
def cl_24749 : CNF.NClause := [(99,true),(47,false),(39,true),(43,false),(35,false),(60,true)]
theorem der_24749 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24749 :=
  CNF.rup_sound cl_24749 [cl_2419,cl_24745] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2419 v h) (hints_cons _ _ _ (der_24745 v h) (by intro d hd; cases hd)))
def cl_24750 : CNF.NClause := [(99,true),(47,false),(39,true),(43,true),(35,false),(60,true)]
theorem der_24750 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24750 :=
  CNF.rup_sound cl_24750 [cl_2423,cl_24746] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2423 v h) (hints_cons _ _ _ (der_24746 v h) (by intro d hd; cases hd)))
def cl_24751 : CNF.NClause := [(99,true),(35,false),(39,true),(43,false),(47,true),(51,true)]
theorem der_24751 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24751 :=
  CNF.rup_sound cl_24751 [cl_2427,cl_24743] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2427 v h) (hints_cons _ _ _ (der_24743 v h) (by intro d hd; cases hd)))
def cl_24752 : CNF.NClause := [(96,true),(34,false),(39,true),(44,false),(54,false),(56,true)]
theorem der_24752 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24752 :=
  CNF.rup_sound cl_24752 [cl_2211,cl_2219] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2211 v h) (hints_cons _ _ _ (inp_2219 v h) (by intro d hd; cases hd)))
def cl_24753 : CNF.NClause := [(96,true),(34,false),(39,true),(44,false),(49,false),(56,true)]
theorem der_24753 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24753 :=
  CNF.rup_sound cl_24753 [cl_2227,cl_24752] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2227 v h) (hints_cons _ _ _ (der_24752 v h) (by intro d hd; cases hd)))
def cl_24754 : CNF.NClause := [(96,true),(34,false),(39,true),(49,false),(54,true),(56,true)]
theorem der_24754 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24754 :=
  CNF.rup_sound cl_24754 [cl_2231,cl_24753] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2231 v h) (hints_cons _ _ _ (der_24753 v h) (by intro d hd; cases hd)))
def cl_24755 : CNF.NClause := [(96,true),(34,false),(39,true),(44,false),(49,true),(54,true)]
theorem der_24755 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24755 :=
  CNF.rup_sound cl_24755 [cl_2235,cl_23807] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2235 v h) (hints_cons _ _ _ (der_23807 v h) (by intro d hd; cases hd)))
def cl_24756 : CNF.NClause := [(113,true),(36,false),(37,false),(39,true),(40,false),(61,true)]
theorem der_24756 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24756 :=
  CNF.rup_sound cl_24756 [cl_3305,cl_23671] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3305 v h) (hints_cons _ _ _ (der_23671 v h) (by intro d hd; cases hd)))
def cl_24757 : CNF.NClause := [(113,true),(37,false),(38,false),(39,true),(36,false),(61,true)]
theorem der_24757 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24757 :=
  CNF.rup_sound cl_24757 [cl_3321,cl_24756] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3321 v h) (hints_cons _ _ _ (der_24756 v h) (by intro d hd; cases hd)))
def cl_24758 : CNF.NClause := [(121,true),(50,false),(59,false),(31,true),(53,false),(42,false)]
theorem der_24758 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24758 :=
  CNF.rup_sound cl_24758 [cl_3780,cl_23792] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3780 v h) (hints_cons _ _ _ (der_23792 v h) (by intro d hd; cases hd)))
def cl_24759 : CNF.NClause := [(121,true),(39,true),(42,true),(31,true),(59,false),(53,false)]
theorem der_24759 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24759 :=
  CNF.rup_sound cl_24759 [cl_3784,cl_3792] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3784 v h) (hints_cons _ _ _ (inp_3792 v h) (by intro d hd; cases hd)))
def cl_24760 : CNF.NClause := [(105,true),(41,false),(33,false),(50,false),(54,false),(60,false)]
theorem der_24760 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24760 :=
  CNF.rup_sound cl_24760 [cl_2755,cl_23850] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2755 v h) (hints_cons _ _ _ (der_23850 v h) (by intro d hd; cases hd)))
def cl_24761 : CNF.NClause := [(105,true),(50,false),(33,false),(37,true),(54,false),(60,false)]
theorem der_24761 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24761 :=
  CNF.rup_sound cl_24761 [cl_2759,cl_24760] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2759 v h) (hints_cons _ _ _ (der_24760 v h) (by intro d hd; cases hd)))
def cl_24762 : CNF.NClause := [(105,true),(41,false),(33,false),(37,true),(54,false),(60,false)]
theorem der_24762 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24762 :=
  CNF.rup_sound cl_24762 [cl_2763,cl_24760] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2763 v h) (hints_cons _ _ _ (der_24760 v h) (by intro d hd; cases hd)))
def cl_24763 : CNF.NClause := [(105,true),(33,false),(60,false),(41,true),(54,false),(37,true)]
theorem der_24763 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24763 :=
  CNF.rup_sound cl_24763 [cl_2767,cl_24761] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2767 v h) (hints_cons _ _ _ (der_24761 v h) (by intro d hd; cases hd)))
def cl_24764 : CNF.NClause := [(105,true),(41,false),(33,false),(37,true),(50,false),(60,false)]
theorem der_24764 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24764 :=
  CNF.rup_sound cl_24764 [cl_2771,cl_24760] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2771 v h) (hints_cons _ _ _ (der_24760 v h) (by intro d hd; cases hd)))
def cl_24765 : CNF.NClause := [(105,true),(50,false),(33,false),(41,true),(37,true),(60,false)]
theorem der_24765 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24765 :=
  CNF.rup_sound cl_24765 [cl_2775,cl_24761] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2775 v h) (hints_cons _ _ _ (der_24761 v h) (by intro d hd; cases hd)))
def cl_24766 : CNF.NClause := [(105,true),(41,false),(33,false),(37,true),(50,true),(60,false)]
theorem der_24766 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24766 :=
  CNF.rup_sound cl_24766 [cl_2779,cl_24762] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2779 v h) (hints_cons _ _ _ (der_24762 v h) (by intro d hd; cases hd)))
def cl_24767 : CNF.NClause := [(105,true),(54,true),(33,false),(41,true),(37,true),(60,false)]
theorem der_24767 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24767 :=
  CNF.rup_sound cl_24767 [cl_2783,cl_24765] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2783 v h) (hints_cons _ _ _ (der_24765 v h) (by intro d hd; cases hd)))
def cl_24768 : CNF.NClause := [(105,true),(41,false),(33,false),(50,false),(54,false),(60,true)]
theorem der_24768 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24768 :=
  CNF.rup_sound cl_24768 [cl_2787,cl_2785] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2787 v h) (hints_cons _ _ _ (inp_2785 v h) (by intro d hd; cases hd)))
def cl_24769 : CNF.NClause := [(105,true),(50,false),(33,false),(41,true),(37,true),(54,false)]
theorem der_24769 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24769 :=
  CNF.rup_sound cl_24769 [cl_2791,cl_24761] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2791 v h) (hints_cons _ _ _ (der_24761 v h) (by intro d hd; cases hd)))
def cl_24770 : CNF.NClause := [(105,true),(41,false),(33,false),(37,true),(50,true),(54,false)]
theorem der_24770 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24770 :=
  CNF.rup_sound cl_24770 [cl_2795,cl_24762] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2795 v h) (hints_cons _ _ _ (der_24762 v h) (by intro d hd; cases hd)))
def cl_24771 : CNF.NClause := [(105,true),(33,false),(37,true),(50,true),(54,false),(60,true)]
theorem der_24771 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24771 :=
  CNF.rup_sound cl_24771 [cl_2799,cl_24770] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2799 v h) (hints_cons _ _ _ (der_24770 v h) (by intro d hd; cases hd)))
def cl_24772 : CNF.NClause := [(105,true),(33,false),(37,true),(41,false),(50,false),(54,true)]
theorem der_24772 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24772 :=
  CNF.rup_sound cl_24772 [cl_2803,cl_24764] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2803 v h) (hints_cons _ _ _ (der_24764 v h) (by intro d hd; cases hd)))
def cl_24773 : CNF.NClause := [(105,true),(33,false),(37,true),(50,false),(54,true),(60,true)]
theorem der_24773 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24773 :=
  CNF.rup_sound cl_24773 [cl_2807,cl_24772] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2807 v h) (hints_cons _ _ _ (der_24772 v h) (by intro d hd; cases hd)))
def cl_24774 : CNF.NClause := [(105,true),(33,false),(37,true),(41,false),(54,true),(60,true)]
theorem der_24774 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24774 :=
  CNF.rup_sound cl_24774 [cl_2811,cl_24772] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2811 v h) (hints_cons _ _ _ (der_24772 v h) (by intro d hd; cases hd)))
def cl_24775 : CNF.NClause := [(97,true),(47,false),(32,false),(37,true),(52,false),(56,false)]
theorem der_24775 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24775 :=
  CNF.rup_sound cl_24775 [cl_2247,cl_2243] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2247 v h) (hints_cons _ _ _ (inp_2243 v h) (by intro d hd; cases hd)))
def cl_24776 : CNF.NClause := [(97,true),(56,false),(32,false),(42,false),(52,false),(37,true)]
theorem der_24776 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24776 :=
  CNF.rup_sound cl_24776 [cl_2251,cl_2243] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2251 v h) (hints_cons _ _ _ (inp_2243 v h) (by intro d hd; cases hd)))
def cl_24777 : CNF.NClause := [(97,true),(56,false),(32,false),(42,true),(52,false),(37,true)]
theorem der_24777 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24777 :=
  CNF.rup_sound cl_24777 [cl_2255,cl_24775] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2255 v h) (hints_cons _ _ _ (der_24775 v h) (by intro d hd; cases hd)))
def cl_24778 : CNF.NClause := [(97,true),(47,false),(32,false),(42,false),(37,true),(56,false)]
theorem der_24778 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24778 :=
  CNF.rup_sound cl_24778 [cl_2259,cl_2243] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2259 v h) (hints_cons _ _ _ (inp_2243 v h) (by intro d hd; cases hd)))
def cl_24779 : CNF.NClause := [(97,true),(47,false),(32,false),(42,true),(37,true),(56,false)]
theorem der_24779 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24779 :=
  CNF.rup_sound cl_24779 [cl_2263,cl_24775] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2263 v h) (hints_cons _ _ _ (der_24775 v h) (by intro d hd; cases hd)))
def cl_24780 : CNF.NClause := [(97,true),(56,false),(32,false),(42,false),(47,true),(37,true)]
theorem der_24780 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24780 :=
  CNF.rup_sound cl_24780 [cl_2267,cl_24776] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2267 v h) (hints_cons _ _ _ (der_24776 v h) (by intro d hd; cases hd)))
def cl_24782 : CNF.NClause := [(97,true),(47,false),(32,false),(42,false),(37,true),(52,false)]
theorem der_24782 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24782 :=
  CNF.rup_sound cl_24782 [cl_2275,cl_2243] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2275 v h) (hints_cons _ _ _ (inp_2243 v h) (by intro d hd; cases hd)))
def cl_24783 : CNF.NClause := [(97,true),(47,false),(32,false),(42,true),(37,true),(52,false)]
theorem der_24783 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24783 :=
  CNF.rup_sound cl_24783 [cl_2279,cl_24775] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2279 v h) (hints_cons _ _ _ (der_24775 v h) (by intro d hd; cases hd)))
def cl_24784 : CNF.NClause := [(97,true),(52,false),(32,false),(42,false),(47,true),(37,true)]
theorem der_24784 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24784 :=
  CNF.rup_sound cl_24784 [cl_2283,cl_24776] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2283 v h) (hints_cons _ _ _ (der_24776 v h) (by intro d hd; cases hd)))
def cl_24785 : CNF.NClause := [(97,true),(52,false),(32,false),(42,true),(47,true),(37,true)]
theorem der_24785 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24785 :=
  CNF.rup_sound cl_24785 [cl_2287,cl_24777] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2287 v h) (hints_cons _ _ _ (der_24777 v h) (by intro d hd; cases hd)))
def cl_24786 : CNF.NClause := [(97,true),(47,false),(32,false),(42,false),(52,true),(56,true)]
theorem der_24786 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24786 :=
  CNF.rup_sound cl_24786 [cl_2291,cl_2289] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2291 v h) (hints_cons _ _ _ (inp_2289 v h) (by intro d hd; cases hd)))
def cl_24787 : CNF.NClause := [(97,true),(47,false),(32,false),(42,true),(37,true),(52,true)]
theorem der_24787 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24787 :=
  CNF.rup_sound cl_24787 [cl_2295,cl_24779] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2295 v h) (hints_cons _ _ _ (der_24779 v h) (by intro d hd; cases hd)))
def cl_24788 : CNF.NClause := [(97,true),(32,false),(42,false),(47,true),(52,true),(56,true)]
theorem der_24788 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24788 :=
  CNF.rup_sound cl_24788 [cl_2299,cl_23798] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2299 v h) (hints_cons _ _ _ (der_23798 v h) (by intro d hd; cases hd)))
def cl_24789 : CNF.NClause := [(109,true),(58,false),(35,false),(44,true),(46,false),(53,false)]
theorem der_24789 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24789 :=
  CNF.rup_sound cl_24789 [cl_3015,cl_23874] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3015 v h) (hints_cons _ _ _ (der_23874 v h) (by intro d hd; cases hd)))
def cl_24790 : CNF.NClause := [(109,true),(58,false),(35,false),(44,false),(53,false),(37,true)]
theorem der_24790 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24790 :=
  CNF.rup_sound cl_24790 [cl_3019,cl_3011] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3019 v h) (hints_cons _ _ _ (inp_3011 v h) (by intro d hd; cases hd)))
def cl_24791 : CNF.NClause := [(109,true),(58,false),(35,false),(46,true),(53,false),(37,true)]
theorem der_24791 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24791 :=
  CNF.rup_sound cl_24791 [cl_3023,cl_24790] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3023 v h) (hints_cons _ _ _ (der_24790 v h) (by intro d hd; cases hd)))
def cl_24792 : CNF.NClause := [(109,true),(53,true),(35,false),(44,false),(46,false),(58,false)]
theorem der_24792 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24792 :=
  CNF.rup_sound cl_24792 [cl_3027,cl_3025] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3027 v h) (hints_cons _ _ _ (inp_3025 v h) (by intro d hd; cases hd)))
def cl_24793 : CNF.NClause := [(109,true),(35,false),(44,true),(46,false),(37,true),(58,false)]
theorem der_24793 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24793 :=
  CNF.rup_sound cl_24793 [cl_3031,cl_24789] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3031 v h) (hints_cons _ _ _ (der_24789 v h) (by intro d hd; cases hd)))
def cl_24794 : CNF.NClause := [(109,true),(53,true),(35,false),(44,false),(46,true),(58,false)]
theorem der_24794 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24794 :=
  CNF.rup_sound cl_24794 [cl_3035,cl_23746] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3035 v h) (hints_cons _ _ _ (der_23746 v h) (by intro d hd; cases hd)))
def cl_24795 : CNF.NClause := [(109,true),(53,true),(35,false),(46,true),(37,true),(58,false)]
theorem der_24795 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24795 :=
  CNF.rup_sound cl_24795 [cl_3039,cl_24794] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3039 v h) (hints_cons _ _ _ (der_24794 v h) (by intro d hd; cases hd)))
def cl_24796 : CNF.NClause := [(109,true),(46,false),(37,true),(44,false),(35,false),(53,false)]
theorem der_24796 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24796 :=
  CNF.rup_sound cl_24796 [cl_3043,cl_3011] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3043 v h) (hints_cons _ _ _ (inp_3011 v h) (by intro d hd; cases hd)))
def cl_24797 : CNF.NClause := [(109,true),(46,false),(44,true),(35,false),(53,false),(58,true)]
theorem der_24797 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24797 :=
  CNF.rup_sound cl_24797 [cl_3047,cl_23874] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3047 v h) (hints_cons _ _ _ (der_23874 v h) (by intro d hd; cases hd)))
def cl_24798 : CNF.NClause := [(109,true),(46,true),(35,false),(44,false),(37,true),(53,false)]
theorem der_24798 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24798 :=
  CNF.rup_sound cl_24798 [cl_3051,cl_24790] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3051 v h) (hints_cons _ _ _ (der_24790 v h) (by intro d hd; cases hd)))
def cl_24799 : CNF.NClause := [(109,true),(35,false),(37,true),(44,true),(53,false),(58,true)]
theorem der_24799 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24799 :=
  CNF.rup_sound cl_24799 [cl_3055,cl_24797] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3055 v h) (hints_cons _ _ _ (der_24797 v h) (by intro d hd; cases hd)))
def cl_24800 : CNF.NClause := [(109,true),(35,false),(46,false),(44,false),(53,true),(58,true)]
theorem der_24800 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24800 :=
  CNF.rup_sound cl_24800 [cl_3059,cl_23741] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3059 v h) (hints_cons _ _ _ (der_23741 v h) (by intro d hd; cases hd)))
def cl_24801 : CNF.NClause := [(109,true),(35,false),(37,true),(46,false),(44,true),(58,true)]
theorem der_24801 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24801 :=
  CNF.rup_sound cl_24801 [cl_3063,cl_24799] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3063 v h) (hints_cons _ _ _ (der_24799 v h) (by intro d hd; cases hd)))
def cl_24802 : CNF.NClause := [(109,true),(53,true),(44,false),(46,true),(35,false),(58,true)]
theorem der_24802 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24802 :=
  CNF.rup_sound cl_24802 [cl_3067,cl_23768] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3067 v h) (hints_cons _ _ _ (der_23768 v h) (by intro d hd; cases hd)))
def cl_24803 : CNF.NClause := [(101,true),(51,false),(34,false),(45,false),(48,false),(59,false)]
theorem der_24803 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24803 :=
  CNF.rup_sound cl_24803 [cl_2499,cl_23848] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2499 v h) (hints_cons _ _ _ (der_23848 v h) (by intro d hd; cases hd)))
def cl_24804 : CNF.NClause := [(101,true),(51,false),(34,false),(45,true),(48,false),(59,false)]
theorem der_24804 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24804 :=
  CNF.rup_sound cl_24804 [cl_2503,cl_23847] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2503 v h) (hints_cons _ _ _ (der_23847 v h) (by intro d hd; cases hd)))
def cl_24805 : CNF.NClause := [(101,true),(51,false),(34,false),(45,false),(37,true),(59,false)]
theorem der_24805 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24805 :=
  CNF.rup_sound cl_24805 [cl_2507,cl_24803] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2507 v h) (hints_cons _ _ _ (der_24803 v h) (by intro d hd; cases hd)))
def cl_24806 : CNF.NClause := [(101,true),(48,true),(34,false),(45,true),(51,false),(59,false)]
theorem der_24806 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24806 :=
  CNF.rup_sound cl_24806 [cl_2511,cl_2509] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2511 v h) (hints_cons _ _ _ (inp_2509 v h) (by intro d hd; cases hd)))
def cl_24807 : CNF.NClause := [(101,true),(59,false),(34,false),(45,false),(48,false),(37,true)]
theorem der_24807 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24807 :=
  CNF.rup_sound cl_24807 [cl_2515,cl_24803] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2515 v h) (hints_cons _ _ _ (der_24803 v h) (by intro d hd; cases hd)))
def cl_24808 : CNF.NClause := [(101,true),(59,false),(34,false),(45,true),(48,false),(37,true)]
theorem der_24808 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24808 :=
  CNF.rup_sound cl_24808 [cl_2519,cl_24804] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2519 v h) (hints_cons _ _ _ (der_24804 v h) (by intro d hd; cases hd)))
def cl_24809 : CNF.NClause := [(101,true),(59,false),(34,false),(45,false),(48,true),(37,true)]
theorem der_24809 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24809 :=
  CNF.rup_sound cl_24809 [cl_2523,cl_24805] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2523 v h) (hints_cons _ _ _ (der_24805 v h) (by intro d hd; cases hd)))
def cl_24810 : CNF.NClause := [(101,true),(48,true),(34,false),(45,true),(37,true),(59,false)]
theorem der_24810 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24810 :=
  CNF.rup_sound cl_24810 [cl_2527,cl_24806] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2527 v h) (hints_cons _ _ _ (der_24806 v h) (by intro d hd; cases hd)))
def cl_24811 : CNF.NClause := [(101,true),(51,false),(34,false),(45,false),(48,false),(37,true)]
theorem der_24811 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24811 :=
  CNF.rup_sound cl_24811 [cl_2531,cl_24803] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2531 v h) (hints_cons _ _ _ (der_24803 v h) (by intro d hd; cases hd)))
def cl_24812 : CNF.NClause := [(101,true),(51,false),(34,false),(45,true),(48,false),(37,true)]
theorem der_24812 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24812 :=
  CNF.rup_sound cl_24812 [cl_2535,cl_24804] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2535 v h) (hints_cons _ _ _ (der_24804 v h) (by intro d hd; cases hd)))
def cl_24813 : CNF.NClause := [(101,true),(51,false),(34,false),(45,false),(37,true),(59,true)]
theorem der_24813 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24813 :=
  CNF.rup_sound cl_24813 [cl_2539,cl_24811] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2539 v h) (hints_cons _ _ _ (der_24811 v h) (by intro d hd; cases hd)))
def cl_24814 : CNF.NClause := [(101,true),(48,true),(34,false),(45,true),(37,true),(51,false)]
theorem der_24814 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24814 :=
  CNF.rup_sound cl_24814 [cl_2543,cl_24806] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2543 v h) (hints_cons _ _ _ (der_24806 v h) (by intro d hd; cases hd)))
def cl_24815 : CNF.NClause := [(101,true),(45,false),(34,false),(37,true),(48,false),(59,true)]
theorem der_24815 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24815 :=
  CNF.rup_sound cl_24815 [cl_2547,cl_24811] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2547 v h) (hints_cons _ _ _ (der_24811 v h) (by intro d hd; cases hd)))
def cl_24816 : CNF.NClause := [(101,true),(34,false),(45,true),(37,true),(48,false),(51,true)]
theorem der_24816 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24816 :=
  CNF.rup_sound cl_24816 [cl_2551,cl_24808] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2551 v h) (hints_cons _ _ _ (der_24808 v h) (by intro d hd; cases hd)))
def cl_24817 : CNF.NClause := [(101,true),(34,false),(37,true),(45,false),(51,true),(59,true)]
theorem der_24817 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24817 :=
  CNF.rup_sound cl_24817 [cl_2555,cl_24815] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2555 v h) (hints_cons _ _ _ (der_24815 v h) (by intro d hd; cases hd)))
def cl_24818 : CNF.NClause := [(113,true),(61,false),(36,false),(38,false),(39,false),(40,false)]
theorem der_24818 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24818 :=
  CNF.rup_sound cl_24818 [cl_3267,cl_23675] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3267 v h) (hints_cons _ _ _ (der_23675 v h) (by intro d hd; cases hd)))
def cl_24819 : CNF.NClause := [(113,true),(61,false),(36,false),(38,true),(39,false),(40,false)]
theorem der_24819 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24819 :=
  CNF.rup_sound cl_24819 [cl_3271,cl_3269] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3271 v h) (hints_cons _ _ _ (inp_3269 v h) (by intro d hd; cases hd)))
def cl_24820 : CNF.NClause := [(113,true),(61,false),(36,false),(38,false),(40,false),(37,true)]
theorem der_24820 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24820 :=
  CNF.rup_sound cl_24820 [cl_3275,cl_24818] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3275 v h) (hints_cons _ _ _ (der_24818 v h) (by intro d hd; cases hd)))
def cl_24821 : CNF.NClause := [(113,true),(61,false),(36,false),(39,true),(37,true),(40,false)]
theorem der_24821 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24821 :=
  CNF.rup_sound cl_24821 [cl_3279,cl_24820] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3279 v h) (hints_cons _ _ _ (der_24820 v h) (by intro d hd; cases hd)))
def cl_24822 : CNF.NClause := [(113,true),(61,false),(36,false),(38,false),(39,false),(40,true)]
theorem der_24822 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24822 :=
  CNF.rup_sound cl_24822 [cl_3283,cl_23675] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3283 v h) (hints_cons _ _ _ (der_23675 v h) (by intro d hd; cases hd)))
def cl_24823 : CNF.NClause := [(113,true),(36,false),(38,true),(39,false),(37,true),(61,false)]
theorem der_24823 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24823 :=
  CNF.rup_sound cl_24823 [cl_3287,cl_24819] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3287 v h) (hints_cons _ _ _ (der_24819 v h) (by intro d hd; cases hd)))
def cl_24824 : CNF.NClause := [(113,true),(61,false),(36,false),(38,false),(39,true),(37,true)]
theorem der_24824 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24824 :=
  CNF.rup_sound cl_24824 [cl_3291,cl_24820] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3291 v h) (hints_cons _ _ _ (der_24820 v h) (by intro d hd; cases hd)))
def cl_24826 : CNF.NClause := [(113,true),(38,false),(36,false),(40,false),(39,false),(37,true)]
theorem der_24826 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24826 :=
  CNF.rup_sound cl_24826 [cl_3299,cl_24818] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3299 v h) (hints_cons _ _ _ (der_24818 v h) (by intro d hd; cases hd)))
def cl_24827 : CNF.NClause := [(113,true),(38,true),(40,false),(39,false),(36,false),(61,true)]
theorem der_24827 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24827 :=
  CNF.rup_sound cl_24827 [cl_3303,cl_23716] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3303 v h) (hints_cons _ _ _ (der_23716 v h) (by intro d hd; cases hd)))
def cl_24828 : CNF.NClause := [(113,true),(36,false),(40,false),(38,false),(39,true),(61,true)]
theorem der_24828 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24828 :=
  CNF.rup_sound cl_24828 [cl_3307,cl_24756] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3307 v h) (hints_cons _ _ _ (der_24756 v h) (by intro d hd; cases hd)))
def cl_24829 : CNF.NClause := [(113,true),(38,true),(40,false),(39,true),(36,false),(61,true)]
theorem der_24829 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24829 :=
  CNF.rup_sound cl_24829 [cl_3311,cl_24756] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3311 v h) (hints_cons _ _ _ (der_24756 v h) (by intro d hd; cases hd)))
def cl_24830 : CNF.NClause := [(113,true),(36,false),(38,false),(39,false),(37,true),(61,true)]
theorem der_24830 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24830 :=
  CNF.rup_sound cl_24830 [cl_3315,cl_24826] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3315 v h) (hints_cons _ _ _ (der_24826 v h) (by intro d hd; cases hd)))
def cl_24831 : CNF.NClause := [(113,true),(40,true),(36,false),(39,false),(37,true),(61,true)]
theorem der_24831 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24831 :=
  CNF.rup_sound cl_24831 [cl_3319,cl_24830] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3319 v h) (hints_cons _ _ _ (der_24830 v h) (by intro d hd; cases hd)))
def cl_24832 : CNF.NClause := [(113,true),(40,true),(36,false),(38,false),(39,true),(61,true)]
theorem der_24832 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24832 :=
  CNF.rup_sound cl_24832 [cl_3323,cl_24757] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3323 v h) (hints_cons _ _ _ (der_24757 v h) (by intro d hd; cases hd)))
def cl_24833 : CNF.NClause := [(122,true),(55,false),(31,true),(43,false),(49,true),(57,false)]
theorem der_24833 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24833 :=
  CNF.rup_sound cl_24833 [cl_3852,cl_23816] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3852 v h) (hints_cons _ _ _ (der_23816 v h) (by intro d hd; cases hd)))
def cl_24834 : CNF.NClause := [(122,true),(55,false),(31,true),(43,true),(37,true),(57,false)]
theorem der_24834 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24834 :=
  CNF.rup_sound cl_24834 [cl_3856,cl_3848] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3856 v h) (hints_cons _ _ _ (inp_3848 v h) (by intro d hd; cases hd)))
def cl_24835 : CNF.NClause := [(122,true),(57,false),(31,true),(43,true),(49,false),(37,true)]
theorem der_24835 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24835 :=
  CNF.rup_sound cl_24835 [cl_3864,cl_3848] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3864 v h) (hints_cons _ _ _ (inp_3848 v h) (by intro d hd; cases hd)))
def cl_24836 : CNF.NClause := [(122,true),(57,false),(31,true),(43,false),(49,true),(55,true)]
theorem der_24836 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24836 :=
  CNF.rup_sound cl_24836 [cl_3868,cl_3866] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3868 v h) (hints_cons _ _ _ (inp_3866 v h) (by intro d hd; cases hd)))
def cl_24837 : CNF.NClause := [(122,true),(55,false),(31,true),(43,true),(37,true),(49,false)]
theorem der_24837 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24837 :=
  CNF.rup_sound cl_24837 [cl_3880,cl_3848] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3880 v h) (hints_cons _ _ _ (inp_3848 v h) (by intro d hd; cases hd)))
def cl_24838 : CNF.NClause := [(122,true),(55,false),(31,true),(43,false),(49,true),(37,true)]
theorem der_24838 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24838 :=
  CNF.rup_sound cl_24838 [cl_3884,cl_24833] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3884 v h) (hints_cons _ _ _ (der_24833 v h) (by intro d hd; cases hd)))
def cl_24839 : CNF.NClause := [(122,true),(37,true),(31,true),(43,false),(49,false),(57,true)]
theorem der_24839 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24839 :=
  CNF.rup_sound cl_24839 [cl_3892,cl_3876] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3892 v h) (hints_cons _ _ _ (inp_3876 v h) (by intro d hd; cases hd)))
def cl_24840 : CNF.NClause := [(122,true),(57,false),(37,true),(31,true),(49,false),(55,false)]
theorem der_24840 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24840 :=
  CNF.rup_sound cl_24840 [cl_3844,cl_3848] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3844 v h) (hints_cons _ _ _ (inp_3848 v h) (by intro d hd; cases hd)))
def cl_24841 : CNF.NClause := [(113,true),(61,false),(38,false),(39,false),(37,false),(40,false)]
theorem der_24841 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24841 :=
  CNF.rup_sound cl_24841 [cl_3266,cl_23675] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3266 v h) (hints_cons _ _ _ (der_23675 v h) (by intro d hd; cases hd)))
def cl_24842 : CNF.NClause := [(113,true),(38,false),(37,true),(39,false),(40,false),(61,false)]
theorem der_24842 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24842 :=
  CNF.rup_sound cl_24842 [cl_3268,cl_24818] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3268 v h) (hints_cons _ _ _ (der_24818 v h) (by intro d hd; cases hd)))
def cl_24843 : CNF.NClause := [(113,true),(61,false),(38,true),(39,false),(37,false),(40,false)]
theorem der_24843 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24843 :=
  CNF.rup_sound cl_24843 [cl_3270,cl_3269] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3270 v h) (hints_cons _ _ _ (inp_3269 v h) (by intro d hd; cases hd)))
def cl_24844 : CNF.NClause := [(113,true),(39,false),(37,true),(38,true),(40,false),(61,false)]
theorem der_24844 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24844 :=
  CNF.rup_sound cl_24844 [cl_3272,cl_24823] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3272 v h) (hints_cons _ _ _ (der_24823 v h) (by intro d hd; cases hd)))
def cl_24845 : CNF.NClause := [(113,true),(61,false),(38,false),(39,true),(37,false),(40,false)]
theorem der_24845 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24845 :=
  CNF.rup_sound cl_24845 [cl_3274,cl_23673] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3274 v h) (hints_cons _ _ _ (der_23673 v h) (by intro d hd; cases hd)))
def cl_24846 : CNF.NClause := [(113,true),(38,false),(37,true),(39,true),(40,false),(61,false)]
theorem der_24846 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24846 :=
  CNF.rup_sound cl_24846 [cl_3276,cl_24820] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3276 v h) (hints_cons _ _ _ (der_24820 v h) (by intro d hd; cases hd)))
def cl_24847 : CNF.NClause := [(113,true),(61,false),(36,true),(38,true),(40,false),(37,false)]
theorem der_24847 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24847 :=
  CNF.rup_sound cl_24847 [cl_3278,cl_24843] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3278 v h) (hints_cons _ _ _ (der_24843 v h) (by intro d hd; cases hd)))
def cl_24849 : CNF.NClause := [(113,true),(40,true),(38,false),(39,false),(37,false),(61,false)]
theorem der_24849 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24849 :=
  CNF.rup_sound cl_24849 [cl_3282,cl_23675] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3282 v h) (hints_cons _ _ _ (der_23675 v h) (by intro d hd; cases hd)))
def cl_24850 : CNF.NClause := [(113,true),(38,false),(36,true),(39,false),(40,true),(61,false)]
theorem der_24850 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24850 :=
  CNF.rup_sound cl_24850 [cl_3284,cl_24849] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3284 v h) (hints_cons _ _ _ (der_24849 v h) (by intro d hd; cases hd)))
def cl_24851 : CNF.NClause := [(113,true),(36,true),(38,true),(39,false),(37,false),(61,false)]
theorem der_24851 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24851 :=
  CNF.rup_sound cl_24851 [cl_3286,cl_24847] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3286 v h) (hints_cons _ _ _ (der_24847 v h) (by intro d hd; cases hd)))
def cl_24852 : CNF.NClause := [(113,true),(39,false),(37,true),(38,true),(36,true),(61,false)]
theorem der_24852 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24852 :=
  CNF.rup_sound cl_24852 [cl_3288,cl_24844] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3288 v h) (hints_cons _ _ _ (der_24844 v h) (by intro d hd; cases hd)))
def cl_24856 : CNF.NClause := [(113,true),(38,false),(37,false),(36,true),(39,false),(40,false)]
theorem der_24856 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24856 :=
  CNF.rup_sound cl_24856 [cl_3298,cl_24841] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3298 v h) (hints_cons _ _ _ (der_24841 v h) (by intro d hd; cases hd)))
def cl_24857 : CNF.NClause := [(113,true),(39,false),(36,true),(40,false),(38,false),(61,true)]
theorem der_24857 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24857 :=
  CNF.rup_sound cl_24857 [cl_3300,cl_24856] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3300 v h) (hints_cons _ _ _ (der_24856 v h) (by intro d hd; cases hd)))
def cl_24858 : CNF.NClause := [(113,true),(39,false),(36,true),(38,true),(40,false),(37,false)]
theorem der_24858 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24858 :=
  CNF.rup_sound cl_24858 [cl_3302,cl_24847] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3302 v h) (hints_cons _ _ _ (der_24847 v h) (by intro d hd; cases hd)))
def cl_24859 : CNF.NClause := [(113,true),(40,false),(38,true),(37,true),(36,true),(39,false)]
theorem der_24859 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24859 :=
  CNF.rup_sound cl_24859 [cl_3304,cl_24844] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3304 v h) (hints_cons _ _ _ (der_24844 v h) (by intro d hd; cases hd)))
def cl_24860 : CNF.NClause := [(113,true),(38,false),(40,false),(39,true),(37,false),(61,true)]
theorem der_24860 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24860 :=
  CNF.rup_sound cl_24860 [cl_3306,cl_24756] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3306 v h) (hints_cons _ _ _ (der_24756 v h) (by intro d hd; cases hd)))
def cl_24861 : CNF.NClause := [(113,true),(38,false),(37,true),(36,true),(39,true),(40,false)]
theorem der_24861 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24861 :=
  CNF.rup_sound cl_24861 [cl_3308,cl_24846] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3308 v h) (hints_cons _ _ _ (der_24846 v h) (by intro d hd; cases hd)))
def cl_24862 : CNF.NClause := [(113,true),(39,true),(38,true),(37,false),(40,false),(61,true)]
theorem der_24862 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24862 :=
  CNF.rup_sound cl_24862 [cl_3310,cl_24756] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3310 v h) (hints_cons _ _ _ (der_24756 v h) (by intro d hd; cases hd)))
def cl_24863 : CNF.NClause := [(113,true),(40,true),(36,true),(38,false),(39,false),(37,false)]
theorem der_24863 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24863 :=
  CNF.rup_sound cl_24863 [cl_3314,cl_24850] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3314 v h) (hints_cons _ _ _ (der_24850 v h) (by intro d hd; cases hd)))
def cl_24864 : CNF.NClause := [(113,true),(40,true),(36,true),(39,false),(38,false),(61,true)]
theorem der_24864 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24864 :=
  CNF.rup_sound cl_24864 [cl_3316,cl_24863] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3316 v h) (hints_cons _ _ _ (der_24863 v h) (by intro d hd; cases hd)))
def cl_24865 : CNF.NClause := [(113,true),(40,true),(36,true),(39,false),(37,false),(61,true)]
theorem der_24865 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24865 :=
  CNF.rup_sound cl_24865 [cl_3318,cl_24863] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3318 v h) (hints_cons _ _ _ (der_24863 v h) (by intro d hd; cases hd)))
def cl_24866 : CNF.NClause := [(113,true),(40,true),(38,false),(39,true),(37,false),(61,true)]
theorem der_24866 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24866 :=
  CNF.rup_sound cl_24866 [cl_3322,cl_24757] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3322 v h) (hints_cons _ _ _ (der_24757 v h) (by intro d hd; cases hd)))
def cl_24867 : CNF.NClause := [(115,true),(47,false),(33,false),(44,true),(55,false),(59,false)]
theorem der_24867 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24867 :=
  CNF.rup_sound cl_24867 [cl_3399,cl_23865] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3399 v h) (hints_cons _ _ _ (der_23865 v h) (by intro d hd; cases hd)))
def cl_24868 : CNF.NClause := [(115,true),(55,false),(33,false),(44,false),(36,true),(59,false)]
theorem der_24868 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24868 :=
  CNF.rup_sound cl_24868 [cl_3403,cl_3395] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3403 v h) (hints_cons _ _ _ (inp_3395 v h) (by intro d hd; cases hd)))
def cl_24869 : CNF.NClause := [(115,true),(55,false),(33,false),(44,true),(47,true),(59,false)]
theorem der_24869 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24869 :=
  CNF.rup_sound cl_24869 [cl_3407,cl_23865] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3407 v h) (hints_cons _ _ _ (der_23865 v h) (by intro d hd; cases hd)))
def cl_24870 : CNF.NClause := [(115,true),(47,false),(33,false),(44,false),(36,true),(59,false)]
theorem der_24870 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24870 :=
  CNF.rup_sound cl_24870 [cl_3411,cl_3395] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3411 v h) (hints_cons _ _ _ (inp_3395 v h) (by intro d hd; cases hd)))
def cl_24871 : CNF.NClause := [(115,true),(47,false),(33,false),(44,true),(55,true),(59,false)]
theorem der_24871 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24871 :=
  CNF.rup_sound cl_24871 [cl_3415,cl_23866] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3415 v h) (hints_cons _ _ _ (der_23866 v h) (by intro d hd; cases hd)))
def cl_24872 : CNF.NClause := [(115,true),(59,false),(33,false),(44,false),(47,true),(55,true)]
theorem der_24872 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24872 :=
  CNF.rup_sound cl_24872 [cl_3419,cl_3417] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3419 v h) (hints_cons _ _ _ (inp_3417 v h) (by intro d hd; cases hd)))
def cl_24873 : CNF.NClause := [(115,true),(59,false),(33,false),(44,true),(47,true),(36,true)]
theorem der_24873 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24873 :=
  CNF.rup_sound cl_24873 [cl_3423,cl_24869] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3423 v h) (hints_cons _ _ _ (der_24869 v h) (by intro d hd; cases hd)))
def cl_24874 : CNF.NClause := [(115,true),(47,false),(33,false),(44,false),(36,true),(55,false)]
theorem der_24874 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24874 :=
  CNF.rup_sound cl_24874 [cl_3427,cl_3395] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3427 v h) (hints_cons _ _ _ (inp_3395 v h) (by intro d hd; cases hd)))
def cl_24875 : CNF.NClause := [(115,true),(47,false),(33,false),(44,true),(55,false),(59,true)]
theorem der_24875 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24875 :=
  CNF.rup_sound cl_24875 [cl_3431,cl_23868] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3431 v h) (hints_cons _ _ _ (der_23868 v h) (by intro d hd; cases hd)))
def cl_24876 : CNF.NClause := [(115,true),(55,false),(33,false),(44,false),(47,true),(36,true)]
theorem der_24876 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24876 :=
  CNF.rup_sound cl_24876 [cl_3435,cl_24868] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3435 v h) (hints_cons _ _ _ (der_24868 v h) (by intro d hd; cases hd)))
def cl_24877 : CNF.NClause := [(115,true),(55,false),(33,false),(44,true),(47,true),(36,true)]
theorem der_24877 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24877 :=
  CNF.rup_sound cl_24877 [cl_3439,cl_24869] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3439 v h) (hints_cons _ _ _ (der_24869 v h) (by intro d hd; cases hd)))
def cl_24878 : CNF.NClause := [(115,true),(47,false),(33,false),(44,false),(36,true),(55,true)]
theorem der_24878 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24878 :=
  CNF.rup_sound cl_24878 [cl_3443,cl_24870] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3443 v h) (hints_cons _ _ _ (der_24870 v h) (by intro d hd; cases hd)))
def cl_24879 : CNF.NClause := [(115,true),(47,false),(33,false),(44,true),(55,true),(59,true)]
theorem der_24879 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24879 :=
  CNF.rup_sound cl_24879 [cl_3447,cl_23869] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3447 v h) (hints_cons _ _ _ (der_23869 v h) (by intro d hd; cases hd)))
def cl_24880 : CNF.NClause := [(115,true),(33,false),(44,false),(47,true),(55,true),(59,true)]
theorem der_24880 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24880 :=
  CNF.rup_sound cl_24880 [cl_3451,cl_23698] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3451 v h) (hints_cons _ _ _ (der_23698 v h) (by intro d hd; cases hd)))
def cl_24881 : CNF.NClause := [(117,true),(32,false),(36,true),(49,false),(53,false),(60,false)]
theorem der_24881 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24881 :=
  CNF.rup_sound cl_24881 [cl_3527,cl_3523] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3527 v h) (hints_cons _ _ _ (inp_3523 v h) (by intro d hd; cases hd)))
def cl_24882 : CNF.NClause := [(117,true),(32,false),(45,false),(49,true),(53,false),(60,false)]
theorem der_24882 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24882 :=
  CNF.rup_sound cl_24882 [cl_3531,cl_23904] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3531 v h) (hints_cons _ _ _ (der_23904 v h) (by intro d hd; cases hd)))
def cl_24883 : CNF.NClause := [(117,true),(32,false),(36,true),(45,true),(53,false),(60,false)]
theorem der_24883 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24883 :=
  CNF.rup_sound cl_24883 [cl_3535,cl_24881] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3535 v h) (hints_cons _ _ _ (der_24881 v h) (by intro d hd; cases hd)))
def cl_24884 : CNF.NClause := [(117,true),(32,false),(45,false),(49,false),(53,true),(60,false)]
theorem der_24884 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24884 :=
  CNF.rup_sound cl_24884 [cl_3539,cl_3537] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3539 v h) (hints_cons _ _ _ (inp_3537 v h) (by intro d hd; cases hd)))
def cl_24885 : CNF.NClause := [(117,true),(32,false),(36,true),(45,true),(49,false),(60,false)]
theorem der_24885 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24885 :=
  CNF.rup_sound cl_24885 [cl_3543,cl_24881] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3543 v h) (hints_cons _ _ _ (der_24881 v h) (by intro d hd; cases hd)))
def cl_24886 : CNF.NClause := [(117,true),(32,false),(45,false),(49,true),(53,true),(60,false)]
theorem der_24886 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24886 :=
  CNF.rup_sound cl_24886 [cl_3547,cl_23752] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3547 v h) (hints_cons _ _ _ (der_23752 v h) (by intro d hd; cases hd)))
def cl_24887 : CNF.NClause := [(117,true),(32,false),(36,true),(45,true),(49,true),(60,false)]
theorem der_24887 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24887 :=
  CNF.rup_sound cl_24887 [cl_3551,cl_24883] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3551 v h) (hints_cons _ _ _ (der_24883 v h) (by intro d hd; cases hd)))
def cl_24888 : CNF.NClause := [(117,true),(32,false),(36,true),(45,false),(49,false),(53,false)]
theorem der_24888 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24888 :=
  CNF.rup_sound cl_24888 [cl_3555,cl_3523] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3555 v h) (hints_cons _ _ _ (inp_3523 v h) (by intro d hd; cases hd)))
def cl_24889 : CNF.NClause := [(117,true),(32,false),(36,true),(45,true),(49,false),(53,false)]
theorem der_24889 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24889 :=
  CNF.rup_sound cl_24889 [cl_3559,cl_24881] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3559 v h) (hints_cons _ _ _ (der_24881 v h) (by intro d hd; cases hd)))
def cl_24890 : CNF.NClause := [(117,true),(32,false),(45,false),(49,true),(53,false),(60,true)]
theorem der_24890 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24890 :=
  CNF.rup_sound cl_24890 [cl_3563,cl_23901] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3563 v h) (hints_cons _ _ _ (der_23901 v h) (by intro d hd; cases hd)))
def cl_24891 : CNF.NClause := [(117,true),(32,false),(36,true),(45,true),(49,true),(53,false)]
theorem der_24891 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24891 :=
  CNF.rup_sound cl_24891 [cl_3567,cl_24883] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3567 v h) (hints_cons _ _ _ (der_24883 v h) (by intro d hd; cases hd)))
def cl_24892 : CNF.NClause := [(117,true),(32,false),(45,false),(49,false),(53,true),(60,true)]
theorem der_24892 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24892 :=
  CNF.rup_sound cl_24892 [cl_3571,cl_23740] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3571 v h) (hints_cons _ _ _ (der_23740 v h) (by intro d hd; cases hd)))
def cl_24893 : CNF.NClause := [(117,true),(32,false),(36,true),(45,true),(49,false),(60,true)]
theorem der_24893 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24893 :=
  CNF.rup_sound cl_24893 [cl_3575,cl_24889] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3575 v h) (hints_cons _ _ _ (der_24889 v h) (by intro d hd; cases hd)))
def cl_24894 : CNF.NClause := [(117,true),(32,false),(45,false),(49,true),(53,true),(60,true)]
theorem der_24894 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24894 :=
  CNF.rup_sound cl_24894 [cl_3579,cl_23901] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3579 v h) (hints_cons _ _ _ (der_23901 v h) (by intro d hd; cases hd)))
def cl_24895 : CNF.NClause := [(114,true),(57,false),(42,false),(48,false),(54,false),(35,false)]
theorem der_24895 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24895 :=
  CNF.rup_sound cl_24895 [cl_3331,cl_23840] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3331 v h) (hints_cons _ _ _ (der_23840 v h) (by intro d hd; cases hd)))
def cl_24896 : CNF.NClause := [(114,true),(36,true),(35,false),(48,false),(54,false),(57,false)]
theorem der_24896 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24896 :=
  CNF.rup_sound cl_24896 [cl_3335,cl_24895] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3335 v h) (hints_cons _ _ _ (der_24895 v h) (by intro d hd; cases hd)))
def cl_24897 : CNF.NClause := [(114,true),(57,false),(42,false),(48,true),(54,false),(35,false)]
theorem der_24897 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24897 :=
  CNF.rup_sound cl_24897 [cl_3339,cl_3337] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3339 v h) (hints_cons _ _ _ (inp_3337 v h) (by intro d hd; cases hd)))
def cl_24898 : CNF.NClause := [(114,true),(42,true),(36,true),(35,false),(54,false),(57,false)]
theorem der_24898 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24898 :=
  CNF.rup_sound cl_24898 [cl_3343,cl_24896] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3343 v h) (hints_cons _ _ _ (der_24896 v h) (by intro d hd; cases hd)))
def cl_24899 : CNF.NClause := [(114,true),(57,false),(36,true),(42,false),(48,false),(35,false)]
theorem der_24899 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24899 :=
  CNF.rup_sound cl_24899 [cl_3347,cl_24895] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3347 v h) (hints_cons _ _ _ (der_24895 v h) (by intro d hd; cases hd)))
def cl_24900 : CNF.NClause := [(114,true),(42,true),(36,true),(35,false),(48,false),(57,false)]
theorem der_24900 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24900 :=
  CNF.rup_sound cl_24900 [cl_3351,cl_24896] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3351 v h) (hints_cons _ _ _ (der_24896 v h) (by intro d hd; cases hd)))
def cl_24901 : CNF.NClause := [(114,true),(57,false),(36,true),(42,false),(48,true),(35,false)]
theorem der_24901 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24901 :=
  CNF.rup_sound cl_24901 [cl_3355,cl_24897] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3355 v h) (hints_cons _ _ _ (der_24897 v h) (by intro d hd; cases hd)))
def cl_24902 : CNF.NClause := [(114,true),(42,true),(36,true),(35,false),(48,true),(57,false)]
theorem der_24902 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24902 :=
  CNF.rup_sound cl_24902 [cl_3359,cl_24898] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3359 v h) (hints_cons _ _ _ (der_24898 v h) (by intro d hd; cases hd)))
def cl_24903 : CNF.NClause := [(114,true),(54,false),(36,true),(42,false),(48,false),(35,false)]
theorem der_24903 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24903 :=
  CNF.rup_sound cl_24903 [cl_3363,cl_24895] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3363 v h) (hints_cons _ _ _ (der_24895 v h) (by intro d hd; cases hd)))
def cl_24904 : CNF.NClause := [(114,true),(42,true),(36,true),(35,false),(48,false),(54,false)]
theorem der_24904 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24904 :=
  CNF.rup_sound cl_24904 [cl_3367,cl_24896] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3367 v h) (hints_cons _ _ _ (der_24896 v h) (by intro d hd; cases hd)))
def cl_24905 : CNF.NClause := [(114,true),(48,true),(36,true),(42,false),(35,false),(54,false)]
theorem der_24905 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24905 :=
  CNF.rup_sound cl_24905 [cl_3371,cl_24897] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3371 v h) (hints_cons _ _ _ (der_24897 v h) (by intro d hd; cases hd)))
def cl_24906 : CNF.NClause := [(114,true),(42,true),(36,true),(35,false),(48,true),(54,false)]
theorem der_24906 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24906 :=
  CNF.rup_sound cl_24906 [cl_3375,cl_24898] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3375 v h) (hints_cons _ _ _ (der_24898 v h) (by intro d hd; cases hd)))
def cl_24907 : CNF.NClause := [(114,true),(35,false),(36,true),(42,false),(48,false),(54,true)]
theorem der_24907 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24907 :=
  CNF.rup_sound cl_24907 [cl_3379,cl_24899] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3379 v h) (hints_cons _ _ _ (der_24899 v h) (by intro d hd; cases hd)))
def cl_24908 : CNF.NClause := [(114,true),(35,false),(36,true),(42,true),(48,false),(57,true)]
theorem der_24908 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24908 :=
  CNF.rup_sound cl_24908 [cl_3383,cl_24904] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3383 v h) (hints_cons _ _ _ (der_24904 v h) (by intro d hd; cases hd)))
def cl_24909 : CNF.NClause := [(114,true),(35,false),(36,true),(42,false),(48,true),(54,true)]
theorem der_24909 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24909 :=
  CNF.rup_sound cl_24909 [cl_3387,cl_24901] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3387 v h) (hints_cons _ _ _ (der_24901 v h) (by intro d hd; cases hd)))
def cl_24910 : CNF.NClause := [(123,true),(41,false),(56,true),(31,true),(46,false),(51,false)]
theorem der_24910 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24910 :=
  CNF.rup_sound cl_24910 [cl_3940,cl_23818] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3940 v h) (hints_cons _ _ _ (der_23818 v h) (by intro d hd; cases hd)))
def cl_24911 : CNF.NClause := [(116,true),(34,false),(36,true),(50,false),(52,false),(58,false)]
theorem der_24911 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24911 :=
  CNF.rup_sound cl_24911 [cl_3463,cl_3459] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3463 v h) (hints_cons _ _ _ (inp_3459 v h) (by intro d hd; cases hd)))
def cl_24912 : CNF.NClause := [(116,true),(34,false),(36,true),(43,false),(52,false),(58,false)]
theorem der_24912 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24912 :=
  CNF.rup_sound cl_24912 [cl_3467,cl_3459] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3467 v h) (hints_cons _ _ _ (inp_3459 v h) (by intro d hd; cases hd)))
def cl_24913 : CNF.NClause := [(116,true),(34,false),(36,true),(43,true),(52,false),(58,false)]
theorem der_24913 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24913 :=
  CNF.rup_sound cl_24913 [cl_3471,cl_24911] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3471 v h) (hints_cons _ _ _ (der_24911 v h) (by intro d hd; cases hd)))
def cl_24914 : CNF.NClause := [(116,true),(34,false),(43,false),(50,false),(52,true),(58,false)]
theorem der_24914 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24914 :=
  CNF.rup_sound cl_24914 [cl_3475,cl_3473] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3475 v h) (hints_cons _ _ _ (inp_3473 v h) (by intro d hd; cases hd)))
def cl_24915 : CNF.NClause := [(116,true),(34,false),(36,true),(43,true),(50,false),(58,false)]
theorem der_24915 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24915 :=
  CNF.rup_sound cl_24915 [cl_3479,cl_24911] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3479 v h) (hints_cons _ _ _ (der_24911 v h) (by intro d hd; cases hd)))
def cl_24916 : CNF.NClause := [(116,true),(34,false),(36,true),(43,false),(50,true),(58,false)]
theorem der_24916 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24916 :=
  CNF.rup_sound cl_24916 [cl_3483,cl_24912] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3483 v h) (hints_cons _ _ _ (der_24912 v h) (by intro d hd; cases hd)))
def cl_24917 : CNF.NClause := [(116,true),(34,false),(36,true),(43,true),(50,true),(58,false)]
theorem der_24917 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24917 :=
  CNF.rup_sound cl_24917 [cl_3487,cl_24913] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3487 v h) (hints_cons _ _ _ (der_24913 v h) (by intro d hd; cases hd)))
def cl_24918 : CNF.NClause := [(116,true),(34,false),(36,true),(43,false),(50,false),(52,false)]
theorem der_24918 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24918 :=
  CNF.rup_sound cl_24918 [cl_3491,cl_3459] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3491 v h) (hints_cons _ _ _ (inp_3459 v h) (by intro d hd; cases hd)))
def cl_24919 : CNF.NClause := [(116,true),(34,false),(36,true),(43,true),(50,false),(52,false)]
theorem der_24919 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24919 :=
  CNF.rup_sound cl_24919 [cl_3495,cl_24911] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3495 v h) (hints_cons _ _ _ (der_24911 v h) (by intro d hd; cases hd)))
def cl_24920 : CNF.NClause := [(116,true),(34,false),(36,true),(43,false),(50,true),(52,false)]
theorem der_24920 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24920 :=
  CNF.rup_sound cl_24920 [cl_3499,cl_24912] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3499 v h) (hints_cons _ _ _ (der_24912 v h) (by intro d hd; cases hd)))
def cl_24921 : CNF.NClause := [(116,true),(34,false),(36,true),(43,true),(50,true),(52,false)]
theorem der_24921 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24921 :=
  CNF.rup_sound cl_24921 [cl_3503,cl_24913] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3503 v h) (hints_cons _ _ _ (der_24913 v h) (by intro d hd; cases hd)))
def cl_24922 : CNF.NClause := [(116,true),(34,false),(43,false),(50,false),(52,true),(58,true)]
theorem der_24922 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24922 :=
  CNF.rup_sound cl_24922 [cl_3507,cl_23800] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3507 v h) (hints_cons _ _ _ (der_23800 v h) (by intro d hd; cases hd)))
def cl_24923 : CNF.NClause := [(116,true),(34,false),(36,true),(43,true),(50,false),(58,true)]
theorem der_24923 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24923 :=
  CNF.rup_sound cl_24923 [cl_3511,cl_24919] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3511 v h) (hints_cons _ _ _ (der_24919 v h) (by intro d hd; cases hd)))
def cl_24924 : CNF.NClause := [(116,true),(34,false),(36,true),(43,false),(50,true),(58,true)]
theorem der_24924 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24924 :=
  CNF.rup_sound cl_24924 [cl_3515,cl_24920] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3515 v h) (hints_cons _ _ _ (der_24920 v h) (by intro d hd; cases hd)))
def cl_24925 : CNF.NClause := [(31,false),(90,true),(87,false),(88,false),(91,false),(92,false)]
theorem der_24925 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24925 :=
  CNF.rup_sound cl_24925 [cl_15437,cl_24689] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15437 v h) (hints_cons _ _ _ (der_24689 v h) (by intro d hd; cases hd)))
def cl_24926 : CNF.NClause := [(31,false),(92,false),(87,false),(90,false),(88,false),(91,true)]
theorem der_24926 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24926 :=
  CNF.rup_sound cl_24926 [cl_15445,cl_24684] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15445 v h) (hints_cons _ _ _ (der_24684 v h) (by intro d hd; cases hd)))
def cl_24927 : CNF.NClause := [(31,false),(87,false),(88,false),(89,true),(91,true),(92,false)]
theorem der_24927 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24927 :=
  CNF.rup_sound cl_24927 [cl_15453,cl_24926] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15453 v h) (hints_cons _ _ _ (der_24926 v h) (by intro d hd; cases hd)))
def cl_24928 : CNF.NClause := [(31,false),(92,true),(88,false),(90,false),(91,false),(89,true)]
theorem der_24928 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24928 :=
  CNF.rup_sound cl_24928 [cl_15461,cl_15462] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15461 v h) (hints_cons _ _ _ (der_15462 v h) (by intro d hd; cases hd)))
def cl_24929 : CNF.NClause := [(31,false),(87,false),(88,false),(89,true),(91,false),(92,true)]
theorem der_24929 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24929 :=
  CNF.rup_sound cl_24929 [cl_15469,cl_24928] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15469 v h) (hints_cons _ _ _ (der_24928 v h) (by intro d hd; cases hd)))
def cl_24930 : CNF.NClause := [(31,false),(92,true),(91,true),(88,false),(89,true),(90,false)]
theorem der_24930 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24930 :=
  CNF.rup_sound cl_24930 [cl_15477,cl_24683] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15477 v h) (hints_cons _ _ _ (der_24683 v h) (by intro d hd; cases hd)))
def cl_24931 : CNF.NClause := [(31,false),(90,true),(87,false),(88,false),(91,true),(92,true)]
theorem der_24931 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24931 :=
  CNF.rup_sound cl_24931 [cl_15485,cl_24692] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15485 v h) (hints_cons _ _ _ (der_24692 v h) (by intro d hd; cases hd)))
def cl_24932 : CNF.NClause := [(31,false),(92,false),(91,false),(90,false),(88,false),(87,false)]
theorem der_24932 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24932 :=
  CNF.rup_sound cl_24932 [cl_15429,cl_15425] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15429 v h) (hints_cons _ _ _ (der_15425 v h) (by intro d hd; cases hd)))
def cl_24933 : CNF.NClause := [(31,false),(88,false),(91,false),(89,true),(87,true),(90,false)]
theorem der_24933 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24933 :=
  CNF.rup_sound cl_24933 [cl_15430,cl_15462] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15430 v h) (hints_cons _ _ _ (der_15462 v h) (by intro d hd; cases hd)))
def cl_24934 : CNF.NClause := [(31,false),(88,true),(87,true),(90,false),(91,false),(92,false)]
theorem der_24934 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24934 :=
  CNF.rup_sound cl_24934 [cl_15432,cl_15428] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15432 v h) (hints_cons _ _ _ (der_15428 v h) (by intro d hd; cases hd)))
def cl_24935 : CNF.NClause := [(31,false),(88,true),(87,true),(89,false),(91,false),(92,false)]
theorem der_24935 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24935 :=
  CNF.rup_sound cl_24935 [cl_15436,cl_15428] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15436 v h) (hints_cons _ _ _ (der_15428 v h) (by intro d hd; cases hd)))
def cl_24936 : CNF.NClause := [(31,false),(88,true),(87,true),(90,true),(91,false),(92,false)]
theorem der_24936 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24936 :=
  CNF.rup_sound cl_24936 [cl_15440,cl_24935] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15440 v h) (hints_cons _ _ _ (der_24935 v h) (by intro d hd; cases hd)))
def cl_24937 : CNF.NClause := [(31,false),(87,true),(89,false),(90,false),(91,true),(92,false)]
theorem der_24937 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24937 :=
  CNF.rup_sound cl_24937 [cl_15444,cl_24680] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15444 v h) (hints_cons _ _ _ (der_24680 v h) (by intro d hd; cases hd)))
def cl_24938 : CNF.NClause := [(31,false),(88,true),(87,true),(90,false),(91,true),(92,false)]
theorem der_24938 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24938 :=
  CNF.rup_sound cl_24938 [cl_15448,cl_24937] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15448 v h) (hints_cons _ _ _ (der_24937 v h) (by intro d hd; cases hd)))
def cl_24939 : CNF.NClause := [(31,false),(88,true),(87,true),(89,false),(90,true),(92,false)]
theorem der_24939 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24939 :=
  CNF.rup_sound cl_24939 [cl_15452,cl_24936] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15452 v h) (hints_cons _ _ _ (der_24936 v h) (by intro d hd; cases hd)))
def cl_24940 : CNF.NClause := [(31,false),(88,true),(87,true),(89,true),(90,true),(92,false)]
theorem der_24940 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24940 :=
  CNF.rup_sound cl_24940 [cl_15456,cl_24936] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15456 v h) (hints_cons _ _ _ (der_24936 v h) (by intro d hd; cases hd)))
def cl_24941 : CNF.NClause := [(31,false),(87,true),(89,false),(90,false),(91,false),(92,true)]
theorem der_24941 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24941 :=
  CNF.rup_sound cl_24941 [cl_15460,cl_24687] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15460 v h) (hints_cons _ _ _ (der_24687 v h) (by intro d hd; cases hd)))
def cl_24942 : CNF.NClause := [(31,false),(87,true),(89,true),(90,false),(91,false),(92,true)]
theorem der_24942 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24942 :=
  CNF.rup_sound cl_24942 [cl_15464,cl_15462] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15464 v h) (hints_cons _ _ _ (der_15462 v h) (by intro d hd; cases hd)))
def cl_24943 : CNF.NClause := [(31,false),(87,true),(89,false),(90,true),(91,false),(92,true)]
theorem der_24943 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24943 :=
  CNF.rup_sound cl_24943 [cl_15468,cl_24688] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15468 v h) (hints_cons _ _ _ (der_24688 v h) (by intro d hd; cases hd)))
def cl_24944 : CNF.NClause := [(31,false),(88,true),(87,true),(90,true),(91,false),(92,true)]
theorem der_24944 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24944 :=
  CNF.rup_sound cl_24944 [cl_15472,cl_24943] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15472 v h) (hints_cons _ _ _ (der_24943 v h) (by intro d hd; cases hd)))
def cl_24945 : CNF.NClause := [(31,false),(87,true),(89,false),(90,false),(91,true),(92,true)]
theorem der_24945 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24945 :=
  CNF.rup_sound cl_24945 [cl_15476,cl_24680] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15476 v h) (hints_cons _ _ _ (der_24680 v h) (by intro d hd; cases hd)))
def cl_24946 : CNF.NClause := [(31,false),(87,true),(89,true),(90,false),(91,true),(92,true)]
theorem der_24946 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24946 :=
  CNF.rup_sound cl_24946 [cl_15480,cl_24683] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15480 v h) (hints_cons _ _ _ (der_24683 v h) (by intro d hd; cases hd)))
def cl_24947 : CNF.NClause := [(31,false),(88,true),(87,true),(89,false),(90,true),(92,true)]
theorem der_24947 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24947 :=
  CNF.rup_sound cl_24947 [cl_15484,cl_24943] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15484 v h) (hints_cons _ _ _ (der_24943 v h) (by intro d hd; cases hd)))
def cl_24948 : CNF.NClause := [(31,false),(88,true),(87,true),(89,true),(90,true),(92,true)]
theorem der_24948 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24948 :=
  CNF.rup_sound cl_24948 [cl_15488,cl_24944] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15488 v h) (hints_cons _ _ _ (der_24944 v h) (by intro d hd; cases hd)))
def cl_24949 : CNF.NClause := [(31,false),(87,false),(89,false),(90,false),(92,false),(91,false)]
theorem der_24949 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24949 :=
  CNF.rup_sound cl_24949 [cl_15427,cl_15425] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15427 v h) (hints_cons _ _ _ (der_15425 v h) (by intro d hd; cases hd)))
def cl_24950 : CNF.NClause := [(31,false),(88,true),(87,false),(90,false),(91,false),(92,false)]
theorem der_24950 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24950 :=
  CNF.rup_sound cl_24950 [cl_15431,cl_24949] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15431 v h) (hints_cons _ _ _ (der_24949 v h) (by intro d hd; cases hd)))
def cl_24951 : CNF.NClause := [(31,false),(88,true),(89,false),(90,true),(91,false),(92,false)]
theorem der_24951 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24951 :=
  CNF.rup_sound cl_24951 [cl_15435,cl_24936] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15435 v h) (hints_cons _ _ _ (der_24936 v h) (by intro d hd; cases hd)))
def cl_24952 : CNF.NClause := [(31,false),(88,true),(89,true),(90,true),(91,false),(92,false)]
theorem der_24952 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24952 :=
  CNF.rup_sound cl_24952 [cl_15439,cl_24936] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15439 v h) (hints_cons _ _ _ (der_24936 v h) (by intro d hd; cases hd)))
def cl_24953 : CNF.NClause := [(31,false),(87,false),(89,false),(90,false),(91,true),(92,false)]
theorem der_24953 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24953 :=
  CNF.rup_sound cl_24953 [cl_15443,cl_24685] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15443 v h) (hints_cons _ _ _ (der_24685 v h) (by intro d hd; cases hd)))
def cl_24954 : CNF.NClause := [(31,false),(87,false),(89,true),(90,false),(91,true),(92,false)]
theorem der_24954 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24954 :=
  CNF.rup_sound cl_24954 [cl_15447,cl_24927] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15447 v h) (hints_cons _ _ _ (der_24927 v h) (by intro d hd; cases hd)))
def cl_24955 : CNF.NClause := [(31,false),(88,true),(87,false),(89,false),(91,true),(92,false)]
theorem der_24955 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24955 :=
  CNF.rup_sound cl_24955 [cl_15451,cl_24953] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15451 v h) (hints_cons _ _ _ (der_24953 v h) (by intro d hd; cases hd)))
def cl_24956 : CNF.NClause := [(31,false),(87,false),(89,true),(90,true),(91,true),(92,false)]
theorem der_24956 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24956 :=
  CNF.rup_sound cl_24956 [cl_15455,cl_24927] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15455 v h) (hints_cons _ _ _ (der_24927 v h) (by intro d hd; cases hd)))
def cl_24957 : CNF.NClause := [(31,false),(87,false),(89,false),(90,false),(92,true),(91,false)]
theorem der_24957 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24957 :=
  CNF.rup_sound cl_24957 [cl_15459,cl_23680] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15459 v h) (hints_cons _ _ _ (der_23680 v h) (by intro d hd; cases hd)))
def cl_24958 : CNF.NClause := [(31,false),(87,false),(89,true),(90,false),(91,false),(92,true)]
theorem der_24958 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24958 :=
  CNF.rup_sound cl_24958 [cl_15463,cl_24928] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15463 v h) (hints_cons _ _ _ (der_24928 v h) (by intro d hd; cases hd)))
def cl_24959 : CNF.NClause := [(31,false),(88,true),(89,false),(90,true),(91,false),(92,true)]
theorem der_24959 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24959 :=
  CNF.rup_sound cl_24959 [cl_15467,cl_24943] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15467 v h) (hints_cons _ _ _ (der_24943 v h) (by intro d hd; cases hd)))
def cl_24960 : CNF.NClause := [(31,false),(88,true),(87,false),(89,true),(91,false),(92,true)]
theorem der_24960 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24960 :=
  CNF.rup_sound cl_24960 [cl_15471,cl_24958] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15471 v h) (hints_cons _ _ _ (der_24958 v h) (by intro d hd; cases hd)))
def cl_24961 : CNF.NClause := [(31,false),(87,false),(89,false),(90,false),(91,true),(92,true)]
theorem der_24961 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24961 :=
  CNF.rup_sound cl_24961 [cl_15475,cl_24692] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15475 v h) (hints_cons _ _ _ (der_24692 v h) (by intro d hd; cases hd)))
def cl_24962 : CNF.NClause := [(31,false),(88,true),(87,false),(89,true),(90,false),(92,true)]
theorem der_24962 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24962 :=
  CNF.rup_sound cl_24962 [cl_15479,cl_24958] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15479 v h) (hints_cons _ _ _ (der_24958 v h) (by intro d hd; cases hd)))
def cl_24963 : CNF.NClause := [(31,false),(87,false),(89,false),(90,true),(91,true),(92,true)]
theorem der_24963 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24963 :=
  CNF.rup_sound cl_24963 [cl_15483,cl_24692] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15483 v h) (hints_cons _ _ _ (der_24692 v h) (by intro d hd; cases hd)))
def cl_24964 : CNF.NClause := [(31,false),(87,false),(89,true),(90,true),(91,true),(92,true)]
theorem der_24964 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24964 :=
  CNF.rup_sound cl_24964 [cl_15487,cl_24931] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15487 v h) (hints_cons _ _ _ (der_24931 v h) (by intro d hd; cases hd)))
def cl_24965 : CNF.NClause := [(31,false),(88,false),(89,false),(92,false),(91,false),(90,false)]
theorem der_24965 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24965 :=
  CNF.rup_sound cl_24965 [cl_15426,cl_15425] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15426 v h) (hints_cons _ _ _ (der_15425 v h) (by intro d hd; cases hd)))
def cl_24966 : CNF.NClause := [(61,false),(77,false),(72,false),(82,false),(87,true),(67,false)]
theorem der_24966 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24966 :=
  CNF.rup_sound cl_24966 [cl_15585,cl_15586] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15585 v h) (hints_cons _ _ _ (der_15586 v h) (by intro d hd; cases hd)))
def cl_24967 : CNF.NClause := [(31,false),(90,true),(87,true),(89,true),(91,false),(92,false)]
theorem der_24967 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24967 :=
  CNF.rup_sound cl_24967 [cl_15438,cl_24936] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15438 v h) (hints_cons _ _ _ (der_24936 v h) (by intro d hd; cases hd)))
def cl_24968 : CNF.NClause := [(61,false),(72,true),(77,false),(62,false),(67,false),(87,true)]
theorem der_24968 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24968 :=
  CNF.rup_sound cl_24968 [cl_15605,cl_15589] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15605 v h) (hints_cons _ _ _ (der_15589 v h) (by intro d hd; cases hd)))
def cl_24969 : CNF.NClause := [(61,false),(62,false),(67,false),(77,true),(82,true),(87,true)]
theorem der_24969 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24969 :=
  CNF.rup_sound cl_24969 [cl_15613,cl_23683] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15613 v h) (hints_cons _ _ _ (der_23683 v h) (by intro d hd; cases hd)))
def cl_24970 : CNF.NClause := [(61,false),(72,true),(67,false),(62,false),(82,true),(77,false)]
theorem der_24970 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24970 :=
  CNF.rup_sound cl_24970 [cl_15573,cl_24968] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15573 v h) (hints_cons _ _ _ (der_24968 v h) (by intro d hd; cases hd)))
def cl_24971 : CNF.NClause := [(61,false),(82,false),(87,false),(67,false),(77,false),(62,false)]
theorem der_24971 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24971 :=
  CNF.rup_sound cl_24971 [cl_15557,cl_23689] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15557 v h) (hints_cons _ _ _ (der_23689 v h) (by intro d hd; cases hd)))
def cl_24972 : CNF.NClause := [(61,false),(62,true),(77,false),(67,false),(82,false),(87,false)]
theorem der_24972 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24972 :=
  CNF.rup_sound cl_24972 [cl_15558,cl_24145] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15558 v h) (hints_cons _ _ _ (der_24145 v h) (by intro d hd; cases hd)))
def cl_24973 : CNF.NClause := [(61,false),(62,true),(67,false),(72,true),(82,false),(87,false)]
theorem der_24973 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24973 :=
  CNF.rup_sound cl_24973 [cl_15566,cl_24972] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15566 v h) (hints_cons _ _ _ (der_24972 v h) (by intro d hd; cases hd)))
def cl_24974 : CNF.NClause := [(61,false),(62,true),(77,false),(67,false),(82,true),(87,false)]
theorem der_24974 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24974 :=
  CNF.rup_sound cl_24974 [cl_15574,cl_24145] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15574 v h) (hints_cons _ _ _ (der_24145 v h) (by intro d hd; cases hd)))
def cl_24975 : CNF.NClause := [(61,false),(77,true),(62,true),(67,false),(72,true),(87,false)]
theorem der_24975 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24975 :=
  CNF.rup_sound cl_24975 [cl_15582,cl_24973] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15582 v h) (hints_cons _ _ _ (der_24973 v h) (by intro d hd; cases hd)))
def cl_24976 : CNF.NClause := [(61,false),(62,true),(67,false),(87,true),(82,false),(77,false)]
theorem der_24976 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24976 :=
  CNF.rup_sound cl_24976 [cl_15590,cl_15586] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15590 v h) (hints_cons _ _ _ (der_15586 v h) (by intro d hd; cases hd)))
def cl_24977 : CNF.NClause := [(61,false),(77,true),(62,true),(67,false),(72,true),(82,false)]
theorem der_24977 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24977 :=
  CNF.rup_sound cl_24977 [cl_15598,cl_24975] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15598 v h) (hints_cons _ _ _ (der_24975 v h) (by intro d hd; cases hd)))
def cl_24978 : CNF.NClause := [(61,false),(77,false),(62,true),(67,false),(82,true),(87,true)]
theorem der_24978 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24978 :=
  CNF.rup_sound cl_24978 [cl_15606,cl_24146] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15606 v h) (hints_cons _ _ _ (der_24146 v h) (by intro d hd; cases hd)))
def cl_24979 : CNF.NClause := [(61,false),(77,true),(62,true),(67,false),(82,true),(87,true)]
theorem der_24979 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24979 :=
  CNF.rup_sound cl_24979 [cl_15614,cl_23686] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15614 v h) (hints_cons _ _ _ (der_23686 v h) (by intro d hd; cases hd)))
def cl_24980 : CNF.NClause := [(61,false),(77,true),(82,false),(67,false),(72,true),(87,false)]
theorem der_24980 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24980 :=
  CNF.rup_sound cl_24980 [cl_15565,cl_24975] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15565 v h) (hints_cons _ _ _ (der_24975 v h) (by intro d hd; cases hd)))
def cl_24981 : CNF.NClause := [(61,false),(77,true),(67,false),(62,false),(82,true),(87,false)]
theorem der_24981 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24981 :=
  CNF.rup_sound cl_24981 [cl_15581,cl_15577] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15581 v h) (hints_cons _ _ _ (der_15577 v h) (by intro d hd; cases hd)))
def cl_24982 : CNF.NClause := [(61,false),(67,false),(72,true),(62,false),(82,false),(87,true)]
theorem der_24982 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24982 :=
  CNF.rup_sound cl_24982 [cl_15597,cl_15589] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15597 v h) (hints_cons _ _ _ (der_15589 v h) (by intro d hd; cases hd)))
def cl_24983 : CNF.NClause := [(61,false),(82,false),(62,false),(87,false),(72,false),(77,false)]
theorem der_24983 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24983 :=
  CNF.rup_sound cl_24983 [cl_15555,cl_23689] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15555 v h) (hints_cons _ _ _ (der_23689 v h) (by intro d hd; cases hd)))
def cl_24984 : CNF.NClause := [(61,false),(67,true),(62,false),(77,false),(82,false),(87,false)]
theorem der_24984 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24984 :=
  CNF.rup_sound cl_24984 [cl_15559,cl_24983] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15559 v h) (hints_cons _ _ _ (der_24983 v h) (by intro d hd; cases hd)))
def cl_24985 : CNF.NClause := [(61,false),(67,true),(87,false),(62,false),(72,false),(82,false)]
theorem der_24985 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24985 :=
  CNF.rup_sound cl_24985 [cl_15563,cl_24984] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15563 v h) (hints_cons _ _ _ (der_24984 v h) (by intro d hd; cases hd)))
def cl_24986 : CNF.NClause := [(61,false),(67,true),(62,false),(72,true),(82,false),(87,false)]
theorem der_24986 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24986 :=
  CNF.rup_sound cl_24986 [cl_15567,cl_24984] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15567 v h) (hints_cons _ _ _ (der_24984 v h) (by intro d hd; cases hd)))
def cl_24987 : CNF.NClause := [(61,false),(67,true),(72,false),(77,false),(62,false),(87,false)]
theorem der_24987 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24987 :=
  CNF.rup_sound cl_24987 [cl_15571,cl_24984] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15571 v h) (hints_cons _ _ _ (der_24984 v h) (by intro d hd; cases hd)))
def cl_24988 : CNF.NClause := [(61,false),(67,true),(62,false),(72,true),(77,false),(87,false)]
theorem der_24988 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24988 :=
  CNF.rup_sound cl_24988 [cl_15575,cl_24984] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15575 v h) (hints_cons _ _ _ (der_24984 v h) (by intro d hd; cases hd)))
def cl_24989 : CNF.NClause := [(61,false),(82,true),(62,false),(72,false),(77,true),(87,false)]
theorem der_24989 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24989 :=
  CNF.rup_sound cl_24989 [cl_15579,cl_15577] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15579 v h) (hints_cons _ _ _ (der_15577 v h) (by intro d hd; cases hd)))
def cl_24990 : CNF.NClause := [(61,false),(67,true),(62,false),(72,true),(77,true),(87,false)]
theorem der_24990 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24990 :=
  CNF.rup_sound cl_24990 [cl_15583,cl_24986] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15583 v h) (hints_cons _ _ _ (der_24986 v h) (by intro d hd; cases hd)))
def cl_24991 : CNF.NClause := [(61,false),(62,false),(67,true),(77,false),(82,false),(72,false)]
theorem der_24991 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24991 :=
  CNF.rup_sound cl_24991 [cl_15587,cl_24984] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15587 v h) (hints_cons _ _ _ (der_24984 v h) (by intro d hd; cases hd)))
def cl_24992 : CNF.NClause := [(61,false),(67,true),(62,false),(72,true),(77,false),(82,false)]
theorem der_24992 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24992 :=
  CNF.rup_sound cl_24992 [cl_15591,cl_24984] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15591 v h) (hints_cons _ _ _ (der_24984 v h) (by intro d hd; cases hd)))
def cl_24993 : CNF.NClause := [(61,false),(62,false),(82,false),(72,false),(77,true),(87,true)]
theorem der_24993 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24993 :=
  CNF.rup_sound cl_24993 [cl_15595,cl_15593] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15595 v h) (hints_cons _ _ _ (der_15593 v h) (by intro d hd; cases hd)))
def cl_24994 : CNF.NClause := [(61,false),(67,true),(62,false),(72,true),(77,true),(82,false)]
theorem der_24994 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24994 :=
  CNF.rup_sound cl_24994 [cl_15599,cl_24986] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15599 v h) (hints_cons _ _ _ (der_24986 v h) (by intro d hd; cases hd)))
def cl_24995 : CNF.NClause := [(61,false),(82,true),(67,true),(72,false),(77,false),(62,false)]
theorem der_24995 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24995 :=
  CNF.rup_sound cl_24995 [cl_15603,cl_24987] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15603 v h) (hints_cons _ _ _ (der_24987 v h) (by intro d hd; cases hd)))
def cl_24996 : CNF.NClause := [(61,false),(67,true),(62,false),(77,false),(82,true),(87,true)]
theorem der_24996 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24996 :=
  CNF.rup_sound cl_24996 [cl_15607,cl_24995] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15607 v h) (hints_cons _ _ _ (der_24995 v h) (by intro d hd; cases hd)))
def cl_24997 : CNF.NClause := [(61,false),(82,true),(62,false),(72,false),(77,true),(87,true)]
theorem der_24997 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24997 :=
  CNF.rup_sound cl_24997 [cl_15611,cl_23683] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15611 v h) (hints_cons _ _ _ (der_23683 v h) (by intro d hd; cases hd)))
def cl_24998 : CNF.NClause := [(61,false),(67,true),(62,false),(72,true),(82,true),(87,true)]
theorem der_24998 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24998 :=
  CNF.rup_sound cl_24998 [cl_15615,cl_24996] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15615 v h) (hints_cons _ _ _ (der_24996 v h) (by intro d hd; cases hd)))
def cl_24999 : CNF.NClause := [(61,false),(72,false),(82,false),(67,true),(87,false),(77,false)]
theorem der_24999 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24999 :=
  CNF.rup_sound cl_24999 [cl_15556,cl_24984] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15556 v h) (hints_cons _ _ _ (der_24984 v h) (by intro d hd; cases hd)))
def cl_25000 : CNF.NClause := [(61,false),(67,true),(72,true),(77,false),(82,false),(87,false)]
theorem der_25000 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25000 :=
  CNF.rup_sound cl_25000 [cl_15560,cl_24984] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15560 v h) (hints_cons _ _ _ (der_24984 v h) (by intro d hd; cases hd)))
def cl_25001 : CNF.NClause := [(61,false),(77,true),(87,false),(62,true),(72,false),(82,false)]
theorem der_25001 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25001 :=
  CNF.rup_sound cl_25001 [cl_15564,cl_15562] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15564 v h) (hints_cons _ _ _ (der_15562 v h) (by intro d hd; cases hd)))
def cl_25002 : CNF.NClause := [(61,false),(62,true),(72,true),(77,true),(82,false),(87,false)]
theorem der_25002 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25002 :=
  CNF.rup_sound cl_25002 [cl_15568,cl_24977] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15568 v h) (hints_cons _ _ _ (der_24977 v h) (by intro d hd; cases hd)))
def cl_25003 : CNF.NClause := [(61,false),(82,true),(72,false),(77,false),(67,true),(87,false)]
theorem der_25003 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25003 :=
  CNF.rup_sound cl_25003 [cl_15572,cl_24995] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15572 v h) (hints_cons _ _ _ (der_24995 v h) (by intro d hd; cases hd)))
def cl_25004 : CNF.NClause := [(61,false),(67,true),(72,true),(77,false),(82,true),(87,false)]
theorem der_25004 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25004 :=
  CNF.rup_sound cl_25004 [cl_15576,cl_24988] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15576 v h) (hints_cons _ _ _ (der_24988 v h) (by intro d hd; cases hd)))
def cl_25005 : CNF.NClause := [(61,false),(82,true),(72,false),(67,true),(77,true),(87,false)]
theorem der_25005 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25005 :=
  CNF.rup_sound cl_25005 [cl_15580,cl_24989] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15580 v h) (hints_cons _ _ _ (der_24989 v h) (by intro d hd; cases hd)))
def cl_25006 : CNF.NClause := [(61,false),(67,true),(62,true),(72,true),(82,true),(87,false)]
theorem der_25006 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25006 :=
  CNF.rup_sound cl_25006 [cl_15584,cl_25004] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15584 v h) (hints_cons _ _ _ (der_25004 v h) (by intro d hd; cases hd)))
def cl_25007 : CNF.NClause := [(61,false),(62,true),(77,false),(72,false),(82,false),(87,true)]
theorem der_25007 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25007 :=
  CNF.rup_sound cl_25007 [cl_15588,cl_15586] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15588 v h) (hints_cons _ _ _ (der_15586 v h) (by intro d hd; cases hd)))
def cl_25008 : CNF.NClause := [(61,false),(62,true),(72,true),(77,false),(82,false),(87,true)]
theorem der_25008 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25008 :=
  CNF.rup_sound cl_25008 [cl_15592,cl_24976] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15592 v h) (hints_cons _ _ _ (der_24976 v h) (by intro d hd; cases hd)))
def cl_25009 : CNF.NClause := [(61,false),(67,true),(62,true),(82,false),(72,false),(77,true)]
theorem der_25009 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25009 :=
  CNF.rup_sound cl_25009 [cl_15596,cl_25001] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15596 v h) (hints_cons _ _ _ (der_25001 v h) (by intro d hd; cases hd)))
def cl_25010 : CNF.NClause := [(61,false),(62,true),(72,true),(77,true),(82,false),(87,true)]
theorem der_25010 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25010 :=
  CNF.rup_sound cl_25010 [cl_15600,cl_24977] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15600 v h) (hints_cons _ _ _ (der_24977 v h) (by intro d hd; cases hd)))
def cl_25011 : CNF.NClause := [(61,false),(82,true),(72,false),(77,false),(67,true),(87,true)]
theorem der_25011 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25011 :=
  CNF.rup_sound cl_25011 [cl_15604,cl_24995] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15604 v h) (hints_cons _ _ _ (der_24995 v h) (by intro d hd; cases hd)))
def cl_25012 : CNF.NClause := [(61,false),(67,true),(62,true),(72,true),(77,false),(82,true)]
theorem der_25012 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25012 :=
  CNF.rup_sound cl_25012 [cl_15608,cl_25004] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15608 v h) (hints_cons _ _ _ (der_25004 v h) (by intro d hd; cases hd)))
def cl_25013 : CNF.NClause := [(61,false),(82,true),(62,true),(72,false),(77,true),(87,true)]
theorem der_25013 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25013 :=
  CNF.rup_sound cl_25013 [cl_15612,cl_23686] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15612 v h) (hints_cons _ _ _ (der_23686 v h) (by intro d hd; cases hd)))
def cl_25014 : CNF.NClause := [(61,false),(67,true),(62,true),(72,true),(77,true),(82,true)]
theorem der_25014 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25014 :=
  CNF.rup_sound cl_25014 [cl_15616,cl_25006] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15616 v h) (hints_cons _ _ _ (der_25006 v h) (by intro d hd; cases hd)))
def cl_25015 : CNF.NClause := [(56,false),(62,false),(65,false),(66,false),(64,false),(92,false)]
theorem der_25015 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25015 :=
  CNF.rup_sound cl_25015 [cl_15491,cl_15489] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15491 v h) (hints_cons _ _ _ (der_15489 v h) (by intro d hd; cases hd)))
def cl_25016 : CNF.NClause := [(56,false),(63,true),(66,false),(62,false),(65,false),(92,false)]
theorem der_25016 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25016 :=
  CNF.rup_sound cl_25016 [cl_15495,cl_25015] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15495 v h) (hints_cons _ _ _ (der_25015 v h) (by intro d hd; cases hd)))
def cl_25017 : CNF.NClause := [(56,false),(62,false),(64,false),(63,true),(66,false),(92,false)]
theorem der_25017 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25017 :=
  CNF.rup_sound cl_25017 [cl_15499,cl_25015] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15499 v h) (hints_cons _ _ _ (der_25015 v h) (by intro d hd; cases hd)))
def cl_25018 : CNF.NClause := [(56,false),(65,true),(63,true),(64,true),(66,false),(92,false)]
theorem der_25018 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25018 :=
  CNF.rup_sound cl_25018 [cl_15503,cl_24700] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15503 v h) (hints_cons _ _ _ (der_24700 v h) (by intro d hd; cases hd)))
def cl_25019 : CNF.NClause := [(56,false),(62,false),(64,false),(63,true),(65,false),(92,false)]
theorem der_25019 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25019 :=
  CNF.rup_sound cl_25019 [cl_15507,cl_25016] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15507 v h) (hints_cons _ _ _ (der_25016 v h) (by intro d hd; cases hd)))
def cl_25020 : CNF.NClause := [(56,false),(62,false),(63,true),(65,false),(64,true),(92,false)]
theorem der_25020 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25020 :=
  CNF.rup_sound cl_25020 [cl_15511,cl_25016] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15511 v h) (hints_cons _ _ _ (der_25016 v h) (by intro d hd; cases hd)))
def cl_25021 : CNF.NClause := [(56,false),(62,false),(64,false),(63,true),(66,true),(92,false)]
theorem der_25021 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25021 :=
  CNF.rup_sound cl_25021 [cl_15515,cl_25019] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15515 v h) (hints_cons _ _ _ (der_25019 v h) (by intro d hd; cases hd)))
def cl_25022 : CNF.NClause := [(56,false),(65,true),(63,true),(64,true),(66,true),(92,false)]
theorem der_25022 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25022 :=
  CNF.rup_sound cl_25022 [cl_15519,cl_24700] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15519 v h) (hints_cons _ _ _ (der_24700 v h) (by intro d hd; cases hd)))
def cl_25023 : CNF.NClause := [(56,false),(62,false),(92,true),(64,false),(66,false),(65,false)]
theorem der_25023 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25023 :=
  CNF.rup_sound cl_25023 [cl_15523,cl_24699] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15523 v h) (hints_cons _ _ _ (der_24699 v h) (by intro d hd; cases hd)))
def cl_25024 : CNF.NClause := [(56,false),(92,true),(62,false),(63,true),(65,false),(66,false)]
theorem der_25024 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25024 :=
  CNF.rup_sound cl_25024 [cl_15527,cl_25023] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15527 v h) (hints_cons _ _ _ (der_25023 v h) (by intro d hd; cases hd)))
def cl_25025 : CNF.NClause := [(56,false),(62,false),(64,false),(63,true),(66,false),(92,true)]
theorem der_25025 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25025 :=
  CNF.rup_sound cl_25025 [cl_15531,cl_25023] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15531 v h) (hints_cons _ _ _ (der_25023 v h) (by intro d hd; cases hd)))
def cl_25026 : CNF.NClause := [(56,false),(62,false),(63,true),(64,true),(66,false),(92,true)]
theorem der_25026 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25026 :=
  CNF.rup_sound cl_25026 [cl_15535,cl_25024] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15535 v h) (hints_cons _ _ _ (der_25024 v h) (by intro d hd; cases hd)))
def cl_25027 : CNF.NClause := [(56,false),(62,false),(64,false),(63,true),(65,false),(92,true)]
theorem der_25027 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25027 :=
  CNF.rup_sound cl_25027 [cl_15539,cl_25023] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15539 v h) (hints_cons _ _ _ (der_25023 v h) (by intro d hd; cases hd)))
def cl_25028 : CNF.NClause := [(56,false),(62,false),(63,true),(65,false),(64,true),(92,true)]
theorem der_25028 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25028 :=
  CNF.rup_sound cl_25028 [cl_15543,cl_25024] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15543 v h) (hints_cons _ _ _ (der_25024 v h) (by intro d hd; cases hd)))
def cl_25029 : CNF.NClause := [(56,false),(62,false),(64,false),(63,true),(66,true),(92,true)]
theorem der_25029 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25029 :=
  CNF.rup_sound cl_25029 [cl_15547,cl_25027] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15547 v h) (hints_cons _ _ _ (der_25027 v h) (by intro d hd; cases hd)))
def cl_25030 : CNF.NClause := [(56,false),(62,false),(63,true),(64,true),(66,true),(92,true)]
theorem der_25030 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25030 :=
  CNF.rup_sound cl_25030 [cl_15551,cl_25028] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15551 v h) (hints_cons _ _ _ (der_25028 v h) (by intro d hd; cases hd)))
def cl_25031 : CNF.NClause := [(56,false),(62,true),(65,false),(92,false),(64,false),(66,false)]
theorem der_25031 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25031 :=
  CNF.rup_sound cl_25031 [cl_15492,cl_23668] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15492 v h) (hints_cons _ _ _ (der_23668 v h) (by intro d hd; cases hd)))
def cl_25032 : CNF.NClause := [(56,false),(65,true),(62,true),(63,true),(66,false),(92,false)]
theorem der_25032 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25032 :=
  CNF.rup_sound cl_25032 [cl_15500,cl_24700] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15500 v h) (hints_cons _ _ _ (der_24700 v h) (by intro d hd; cases hd)))
def cl_25033 : CNF.NClause := [(56,false),(62,true),(64,false),(63,true),(65,false),(92,false)]
theorem der_25033 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25033 :=
  CNF.rup_sound cl_25033 [cl_15508,cl_25031] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15508 v h) (hints_cons _ _ _ (der_25031 v h) (by intro d hd; cases hd)))
def cl_25034 : CNF.NClause := [(56,false),(65,true),(62,true),(63,true),(66,true),(92,false)]
theorem der_25034 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25034 :=
  CNF.rup_sound cl_25034 [cl_15516,cl_24700] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15516 v h) (hints_cons _ _ _ (der_24700 v h) (by intro d hd; cases hd)))
def cl_25035 : CNF.NClause := [(56,false),(92,true),(66,false),(64,false),(65,false),(62,true)]
theorem der_25035 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25035 :=
  CNF.rup_sound cl_25035 [cl_15524,cl_23669] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15524 v h) (hints_cons _ _ _ (der_23669 v h) (by intro d hd; cases hd)))
def cl_25036 : CNF.NClause := [(56,false),(65,true),(62,true),(64,false),(63,true),(66,false)]
theorem der_25036 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25036 :=
  CNF.rup_sound cl_25036 [cl_15532,cl_25032] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15532 v h) (hints_cons _ _ _ (der_25032 v h) (by intro d hd; cases hd)))
def cl_25037 : CNF.NClause := [(56,false),(66,true),(62,true),(64,false),(65,false),(92,true)]
theorem der_25037 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25037 :=
  CNF.rup_sound cl_25037 [cl_15540,cl_24707] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15540 v h) (hints_cons _ _ _ (der_24707 v h) (by intro d hd; cases hd)))
def cl_25038 : CNF.NClause := [(56,false),(65,true),(62,true),(64,false),(66,true),(92,true)]
theorem der_25038 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25038 :=
  CNF.rup_sound cl_25038 [cl_15548,cl_24707] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15548 v h) (hints_cons _ _ _ (der_24707 v h) (by intro d hd; cases hd)))
def cl_25039 : CNF.NClause := [(93,true),(58,true),(57,false),(56,true),(60,false),(61,false)]
theorem der_25039 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25039 :=
  CNF.rup_sound cl_25039 [cl_1998,cl_1990] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1998 v h) (hints_cons _ _ _ (inp_1990 v h) (by intro d hd; cases hd)))
def cl_25040 : CNF.NClause := [(93,true),(57,false),(56,true),(59,false),(60,true),(61,false)]
theorem der_25040 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25040 :=
  CNF.rup_sound cl_25040 [cl_2006,cl_2002] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2006 v h) (hints_cons _ _ _ (inp_2002 v h) (by intro d hd; cases hd)))
def cl_25041 : CNF.NClause := [(93,true),(58,true),(57,false),(56,true),(59,true),(61,false)]
theorem der_25041 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25041 :=
  CNF.rup_sound cl_25041 [cl_2014,cl_25039] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2014 v h) (hints_cons _ _ _ (der_25039 v h) (by intro d hd; cases hd)))
def cl_25042 : CNF.NClause := [(100,true),(58,true),(40,false),(33,false),(42,false),(51,false)]
theorem der_25042 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25042 :=
  CNF.rup_sound cl_25042 [cl_2465,cl_23808] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2465 v h) (hints_cons _ _ _ (der_23808 v h) (by intro d hd; cases hd)))
def cl_25043 : CNF.NClause := [(100,true),(58,true),(42,false),(49,false),(33,false),(51,false)]
theorem der_25043 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25043 :=
  CNF.rup_sound cl_25043 [cl_2467,cl_25042] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2467 v h) (hints_cons _ _ _ (der_25042 v h) (by intro d hd; cases hd)))
def cl_25044 : CNF.NClause := [(93,true),(56,true),(57,false),(59,false),(60,false),(61,true)]
theorem der_25044 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25044 :=
  CNF.rup_sound cl_25044 [cl_2022,cl_23838] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2022 v h) (hints_cons _ _ _ (der_23838 v h) (by intro d hd; cases hd)))
def cl_25045 : CNF.NClause := [(93,true),(58,true),(56,true),(57,false),(59,true),(60,false)]
theorem der_25045 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25045 :=
  CNF.rup_sound cl_25045 [cl_2030,cl_25039] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2030 v h) (hints_cons _ _ _ (der_25039 v h) (by intro d hd; cases hd)))
def cl_25046 : CNF.NClause := [(93,true),(56,true),(57,false),(59,false),(60,true),(61,true)]
theorem der_25046 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25046 :=
  CNF.rup_sound cl_25046 [cl_2038,cl_23791] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2038 v h) (hints_cons _ _ _ (der_23791 v h) (by intro d hd; cases hd)))
def cl_25047 : CNF.NClause := [(109,true),(58,true),(37,false),(35,false),(46,false),(53,false)]
theorem der_25047 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25047 :=
  CNF.rup_sound cl_25047 [cl_3041,cl_23874] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3041 v h) (hints_cons _ _ _ (der_23874 v h) (by intro d hd; cases hd)))
def cl_25048 : CNF.NClause := [(116,true),(58,true),(43,true),(34,false),(52,false),(50,false)]
theorem der_25048 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25048 :=
  CNF.rup_sound cl_25048 [cl_3493,cl_24919] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3493 v h) (hints_cons _ _ _ (der_24919 v h) (by intro d hd; cases hd)))
def cl_25049 : CNF.NClause := [(116,true),(58,true),(36,false),(34,false),(43,false),(50,false)]
theorem der_25049 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25049 :=
  CNF.rup_sound cl_25049 [cl_3489,cl_23800] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3489 v h) (hints_cons _ _ _ (der_23800 v h) (by intro d hd; cases hd)))
def cl_25050 : CNF.NClause := [(107,true),(32,false),(41,false),(48,false),(39,false),(55,false)]
theorem der_25050 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25050 :=
  CNF.rup_sound cl_25050 [cl_2913,cl_23903] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2913 v h) (hints_cons _ _ _ (der_23903 v h) (by intro d hd; cases hd)))
def cl_25051 : CNF.NClause := [(120,true),(58,true),(31,true),(47,true),(54,false),(38,false)]
theorem der_25051 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25051 :=
  CNF.rup_sound cl_25051 [cl_3754,cl_23704] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3754 v h) (hints_cons _ _ _ (der_23704 v h) (by intro d hd; cases hd)))
def cl_25052 : CNF.NClause := [(120,true),(58,true),(31,true),(45,false),(54,false),(38,false)]
theorem der_25052 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25052 :=
  CNF.rup_sound cl_25052 [cl_3746,cl_25051] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3746 v h) (hints_cons _ _ _ (der_25051 v h) (by intro d hd; cases hd)))
def cl_25053 : CNF.NClause := [(98,true),(54,true),(51,false),(53,false),(55,false),(61,true)]
theorem der_25053 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25053 :=
  CNF.rup_sound cl_25053 [cl_2345,cl_23845] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2345 v h) (hints_cons _ _ _ (der_23845 v h) (by intro d hd; cases hd)))
def cl_25054 : CNF.NClause := [(98,true),(54,true),(51,false),(53,false),(55,true),(61,true)]
theorem der_25054 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25054 :=
  CNF.rup_sound cl_25054 [cl_2361,cl_23845] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2361 v h) (hints_cons _ _ _ (der_23845 v h) (by intro d hd; cases hd)))
def cl_25055 : CNF.NClause := [(112,true),(40,false),(32,false),(46,false),(43,false),(59,false)]
theorem der_25055 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25055 :=
  CNF.rup_sound cl_25055 [cl_3217,cl_23905] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3217 v h) (hints_cons _ _ _ (der_23905 v h) (by intro d hd; cases hd)))
def cl_25056 : CNF.NClause := [(112,true),(54,true),(40,false),(32,false),(46,false),(43,false)]
theorem der_25056 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25056 :=
  CNF.rup_sound cl_25056 [cl_3249,cl_25055] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3249 v h) (hints_cons _ _ _ (der_25055 v h) (by intro d hd; cases hd)))
def cl_25057 : CNF.NClause := [(98,true),(54,true),(52,false),(51,false),(55,false),(61,false)]
theorem der_25057 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25057 :=
  CNF.rup_sound cl_25057 [cl_2313,cl_23757] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2313 v h) (hints_cons _ _ _ (der_23757 v h) (by intro d hd; cases hd)))
def cl_25058 : CNF.NClause := [(98,true),(54,true),(52,false),(53,false),(51,false),(55,true)]
theorem der_25058 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25058 :=
  CNF.rup_sound cl_25058 [cl_2329,cl_25054] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2329 v h) (hints_cons _ _ _ (der_25054 v h) (by intro d hd; cases hd)))
def cl_25059 : CNF.NClause := [(105,true),(33,false),(41,false),(37,false),(50,false),(60,false)]
theorem der_25059 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25059 :=
  CNF.rup_sound cl_25059 [cl_2769,cl_23850] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2769 v h) (hints_cons _ _ _ (der_23850 v h) (by intro d hd; cases hd)))
def cl_25060 : CNF.NClause := [(105,true),(33,false),(41,false),(37,false),(50,false),(60,true)]
theorem der_25060 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25060 :=
  CNF.rup_sound cl_25060 [cl_2801,cl_2785] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2801 v h) (hints_cons _ _ _ (inp_2785 v h) (by intro d hd; cases hd)))
def cl_25061 : CNF.NClause := [(112,true),(40,true),(43,false),(46,false),(32,false),(59,false)]
theorem der_25061 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25061 :=
  CNF.rup_sound cl_25061 [cl_3219,cl_23790] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3219 v h) (hints_cons _ _ _ (der_23790 v h) (by intro d hd; cases hd)))
def cl_25062 : CNF.NClause := [(112,true),(54,true),(40,true),(43,false),(32,false),(59,true)]
theorem der_25062 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25062 :=
  CNF.rup_sound cl_25062 [cl_3251,cl_23900] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3251 v h) (hints_cons _ _ _ (der_23900 v h) (by intro d hd; cases hd)))
def cl_25063 : CNF.NClause := [(96,true),(54,true),(34,false),(44,false),(39,false),(56,true)]
theorem der_25063 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25063 :=
  CNF.rup_sound cl_25063 [cl_2225,cl_23809] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2225 v h) (hints_cons _ _ _ (der_23809 v h) (by intro d hd; cases hd)))
def cl_25064 : CNF.NClause := [(114,true),(35,false),(36,false),(48,false),(42,false),(57,false)]
theorem der_25064 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25064 :=
  CNF.rup_sound cl_25064 [cl_3345,cl_23840] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3345 v h) (hints_cons _ _ _ (der_23840 v h) (by intro d hd; cases hd)))
def cl_25065 : CNF.NClause := [(114,true),(54,true),(35,false),(48,false),(42,false),(57,true)]
theorem der_25065 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25065 :=
  CNF.rup_sound cl_25065 [cl_3377,cl_24907] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3377 v h) (hints_cons _ _ _ (der_24907 v h) (by intro d hd; cases hd)))
def cl_25066 : CNF.NClause := [(120,true),(54,true),(31,true),(47,true),(38,false),(58,false)]
theorem der_25066 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25066 :=
  CNF.rup_sound cl_25066 [cl_3738,cl_23703] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3738 v h) (hints_cons _ _ _ (der_23703 v h) (by intro d hd; cases hd)))
def cl_25067 : CNF.NClause := [(120,true),(31,true),(45,false),(47,true),(38,false),(58,true)]
theorem der_25067 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25067 :=
  CNF.rup_sound cl_25067 [cl_3770,cl_25051] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3770 v h) (hints_cons _ _ _ (der_25051 v h) (by intro d hd; cases hd)))
def cl_25068 : CNF.NClause := [(120,true),(54,true),(31,true),(45,false),(38,false),(58,false)]
theorem der_25068 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25068 :=
  CNF.rup_sound cl_25068 [cl_3730,cl_25066] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3730 v h) (hints_cons _ _ _ (der_25066 v h) (by intro d hd; cases hd)))
def cl_25069 : CNF.NClause := [(120,true),(31,true),(45,false),(47,false),(38,false),(58,true)]
theorem der_25069 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25069 :=
  CNF.rup_sound cl_25069 [cl_3762,cl_25052] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3762 v h) (hints_cons _ _ _ (der_25052 v h) (by intro d hd; cases hd)))
def cl_25070 : CNF.NClause := [(120,true),(47,false),(45,false),(38,true),(54,false),(31,true)]
theorem der_25070 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25070 :=
  CNF.rup_sound cl_25070 [cl_3716,cl_3748] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3716 v h) (hints_cons _ _ _ (inp_3748 v h) (by intro d hd; cases hd)))
def cl_25071 : CNF.NClause := [(120,true),(58,false),(31,true),(38,true),(54,false),(45,true)]
theorem der_25071 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25071 :=
  CNF.rup_sound cl_25071 [cl_3720,cl_23706] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3720 v h) (hints_cons _ _ _ (der_23706 v h) (by intro d hd; cases hd)))
def cl_25072 : CNF.NClause := [(120,true),(31,true),(38,false),(47,true),(54,false),(58,false)]
theorem der_25072 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25072 :=
  CNF.rup_sound cl_25072 [cl_3722,cl_3726] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3722 v h) (hints_cons _ _ _ (inp_3726 v h) (by intro d hd; cases hd)))
def cl_25073 : CNF.NClause := [(120,true),(45,false),(31,true),(38,false),(47,false),(54,false)]
theorem der_25073 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25073 :=
  CNF.rup_sound cl_25073 [cl_3714,cl_25052] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3714 v h) (hints_cons _ _ _ (der_25052 v h) (by intro d hd; cases hd)))
def cl_25074 : CNF.NClause := [(118,true),(31,false),(33,false),(34,false),(35,false),(61,false)]
theorem der_25074 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25074 :=
  CNF.rup_sound cl_25074 [cl_3587,cl_3585] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3587 v h) (hints_cons _ _ _ (inp_3585 v h) (by intro d hd; cases hd)))
def cl_25075 : CNF.NClause := [(118,true),(31,false),(32,false),(34,false),(35,false),(61,false)]
theorem der_25075 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25075 :=
  CNF.rup_sound cl_25075 [cl_3589,cl_3585] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3589 v h) (hints_cons _ _ _ (inp_3585 v h) (by intro d hd; cases hd)))
def cl_25076 : CNF.NClause := [(118,true),(31,false),(32,true),(34,false),(35,false),(61,false)]
theorem der_25076 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25076 :=
  CNF.rup_sound cl_25076 [cl_3591,cl_25074] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3591 v h) (hints_cons _ _ _ (der_25074 v h) (by intro d hd; cases hd)))
def cl_25077 : CNF.NClause := [(118,true),(31,false),(32,false),(33,false),(35,false),(61,false)]
theorem der_25077 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25077 :=
  CNF.rup_sound cl_25077 [cl_3593,cl_3585] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3593 v h) (hints_cons _ _ _ (inp_3585 v h) (by intro d hd; cases hd)))
def cl_25078 : CNF.NClause := [(118,true),(31,false),(32,true),(33,false),(35,false),(61,false)]
theorem der_25078 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25078 :=
  CNF.rup_sound cl_25078 [cl_3595,cl_25074] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3595 v h) (hints_cons _ _ _ (der_25074 v h) (by intro d hd; cases hd)))
def cl_25079 : CNF.NClause := [(118,true),(31,false),(32,false),(33,true),(35,false),(61,false)]
theorem der_25079 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25079 :=
  CNF.rup_sound cl_25079 [cl_3597,cl_25075] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3597 v h) (hints_cons _ _ _ (der_25075 v h) (by intro d hd; cases hd)))
def cl_25080 : CNF.NClause := [(118,true),(31,false),(32,true),(33,true),(35,false),(61,false)]
theorem der_25080 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25080 :=
  CNF.rup_sound cl_25080 [cl_3599,cl_25076] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3599 v h) (hints_cons _ _ _ (der_25076 v h) (by intro d hd; cases hd)))
def cl_25081 : CNF.NClause := [(118,true),(31,false),(32,false),(33,false),(34,false),(61,false)]
theorem der_25081 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25081 :=
  CNF.rup_sound cl_25081 [cl_3601,cl_3585] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3601 v h) (hints_cons _ _ _ (inp_3585 v h) (by intro d hd; cases hd)))
def cl_25082 : CNF.NClause := [(118,true),(31,false),(32,true),(33,false),(34,false),(61,false)]
theorem der_25082 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25082 :=
  CNF.rup_sound cl_25082 [cl_3603,cl_25074] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3603 v h) (hints_cons _ _ _ (der_25074 v h) (by intro d hd; cases hd)))
def cl_25083 : CNF.NClause := [(118,true),(31,false),(32,false),(33,true),(34,false),(61,false)]
theorem der_25083 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25083 :=
  CNF.rup_sound cl_25083 [cl_3605,cl_25075] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3605 v h) (hints_cons _ _ _ (der_25075 v h) (by intro d hd; cases hd)))
def cl_25084 : CNF.NClause := [(118,true),(31,false),(32,true),(33,true),(34,false),(61,false)]
theorem der_25084 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25084 :=
  CNF.rup_sound cl_25084 [cl_3607,cl_25076] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3607 v h) (hints_cons _ _ _ (der_25076 v h) (by intro d hd; cases hd)))
def cl_25085 : CNF.NClause := [(118,true),(31,false),(32,false),(33,false),(34,true),(61,false)]
theorem der_25085 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25085 :=
  CNF.rup_sound cl_25085 [cl_3609,cl_25077] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3609 v h) (hints_cons _ _ _ (der_25077 v h) (by intro d hd; cases hd)))
def cl_25087 : CNF.NClause := [(118,true),(31,false),(32,false),(33,true),(34,true),(61,false)]
theorem der_25087 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25087 :=
  CNF.rup_sound cl_25087 [cl_3613,cl_25079] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3613 v h) (hints_cons _ _ _ (der_25079 v h) (by intro d hd; cases hd)))
def cl_25088 : CNF.NClause := [(118,true),(31,false),(32,true),(33,true),(34,true),(61,false)]
theorem der_25088 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25088 :=
  CNF.rup_sound cl_25088 [cl_3615,cl_25080] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3615 v h) (hints_cons _ _ _ (der_25080 v h) (by intro d hd; cases hd)))
def cl_25091 : CNF.NClause := [(118,true),(31,false),(32,false),(33,true),(34,false),(35,false)]
theorem der_25091 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25091 :=
  CNF.rup_sound cl_25091 [cl_3621,cl_25075] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3621 v h) (hints_cons _ _ _ (der_25075 v h) (by intro d hd; cases hd)))
def cl_25092 : CNF.NClause := [(118,true),(31,false),(32,true),(33,true),(34,false),(35,false)]
theorem der_25092 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25092 :=
  CNF.rup_sound cl_25092 [cl_3623,cl_25076] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3623 v h) (hints_cons _ _ _ (der_25076 v h) (by intro d hd; cases hd)))
def cl_25093 : CNF.NClause := [(118,true),(31,false),(32,false),(33,false),(34,true),(35,false)]
theorem der_25093 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25093 :=
  CNF.rup_sound cl_25093 [cl_3625,cl_25077] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3625 v h) (hints_cons _ _ _ (der_25077 v h) (by intro d hd; cases hd)))
def cl_25094 : CNF.NClause := [(118,true),(31,false),(32,true),(33,false),(34,true),(35,false)]
theorem der_25094 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25094 :=
  CNF.rup_sound cl_25094 [cl_3627,cl_25078] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3627 v h) (hints_cons _ _ _ (der_25078 v h) (by intro d hd; cases hd)))
def cl_25095 : CNF.NClause := [(118,true),(31,false),(32,false),(34,true),(35,false),(61,true)]
theorem der_25095 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25095 :=
  CNF.rup_sound cl_25095 [cl_3629,cl_25093] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3629 v h) (hints_cons _ _ _ (der_25093 v h) (by intro d hd; cases hd)))
def cl_25099 : CNF.NClause := [(118,true),(31,false),(32,false),(33,true),(34,false),(35,true)]
theorem der_25099 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25099 :=
  CNF.rup_sound cl_25099 [cl_3637,cl_25083] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3637 v h) (hints_cons _ _ _ (der_25083 v h) (by intro d hd; cases hd)))
def cl_25101 : CNF.NClause := [(118,true),(31,false),(32,false),(33,false),(34,true),(61,true)]
theorem der_25101 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25101 :=
  CNF.rup_sound cl_25101 [cl_3641,cl_25093] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3641 v h) (hints_cons _ _ _ (der_25093 v h) (by intro d hd; cases hd)))
def cl_25103 : CNF.NClause := [(118,true),(31,false),(32,false),(33,true),(34,true),(35,true)]
theorem der_25103 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25103 :=
  CNF.rup_sound cl_25103 [cl_3645,cl_25087] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3645 v h) (hints_cons _ _ _ (der_25087 v h) (by intro d hd; cases hd)))
def cl_25104 : CNF.NClause := [(119,true),(31,false),(44,false),(48,false),(52,false),(60,false)]
theorem der_25104 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25104 :=
  CNF.rup_sound cl_25104 [cl_3651,cl_3649] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3651 v h) (hints_cons _ _ _ (inp_3649 v h) (by intro d hd; cases hd)))
def cl_25105 : CNF.NClause := [(119,true),(31,false),(40,false),(48,false),(52,false),(60,false)]
theorem der_25105 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25105 :=
  CNF.rup_sound cl_25105 [cl_3653,cl_3649] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3653 v h) (hints_cons _ _ _ (inp_3649 v h) (by intro d hd; cases hd)))
def cl_25106 : CNF.NClause := [(119,true),(31,false),(40,true),(48,false),(52,false),(60,false)]
theorem der_25106 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25106 :=
  CNF.rup_sound cl_25106 [cl_3655,cl_25104] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3655 v h) (hints_cons _ _ _ (der_25104 v h) (by intro d hd; cases hd)))
def cl_25107 : CNF.NClause := [(119,true),(31,false),(40,false),(44,false),(52,false),(60,false)]
theorem der_25107 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25107 :=
  CNF.rup_sound cl_25107 [cl_3657,cl_3649] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3657 v h) (hints_cons _ _ _ (inp_3649 v h) (by intro d hd; cases hd)))
def cl_25108 : CNF.NClause := [(119,true),(31,false),(40,true),(44,false),(52,false),(60,false)]
theorem der_25108 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25108 :=
  CNF.rup_sound cl_25108 [cl_3659,cl_25104] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3659 v h) (hints_cons _ _ _ (der_25104 v h) (by intro d hd; cases hd)))
def cl_25109 : CNF.NClause := [(119,true),(31,false),(40,false),(44,true),(52,false),(60,false)]
theorem der_25109 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25109 :=
  CNF.rup_sound cl_25109 [cl_3661,cl_25105] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3661 v h) (hints_cons _ _ _ (der_25105 v h) (by intro d hd; cases hd)))
def cl_25110 : CNF.NClause := [(119,true),(31,false),(40,true),(44,true),(52,false),(60,false)]
theorem der_25110 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25110 :=
  CNF.rup_sound cl_25110 [cl_3663,cl_25106] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3663 v h) (hints_cons _ _ _ (der_25106 v h) (by intro d hd; cases hd)))
def cl_25111 : CNF.NClause := [(119,true),(31,false),(40,false),(44,false),(48,false),(60,false)]
theorem der_25111 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25111 :=
  CNF.rup_sound cl_25111 [cl_3665,cl_3649] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3665 v h) (hints_cons _ _ _ (inp_3649 v h) (by intro d hd; cases hd)))
def cl_25112 : CNF.NClause := [(119,true),(31,false),(40,true),(44,false),(48,false),(60,false)]
theorem der_25112 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25112 :=
  CNF.rup_sound cl_25112 [cl_3667,cl_25104] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3667 v h) (hints_cons _ _ _ (der_25104 v h) (by intro d hd; cases hd)))
def cl_25113 : CNF.NClause := [(119,true),(40,false),(44,true),(48,false),(52,true),(60,false)]
theorem der_25113 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25113 :=
  CNF.rup_sound cl_25113 [cl_3669,cl_3670] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3669 v h) (hints_cons _ _ _ (inp_3670 v h) (by intro d hd; cases hd)))
def cl_25115 : CNF.NClause := [(119,true),(31,false),(40,false),(44,false),(52,true),(60,false)]
theorem der_25115 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25115 :=
  CNF.rup_sound cl_25115 [cl_3673,cl_25111] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3673 v h) (hints_cons _ _ _ (der_25111 v h) (by intro d hd; cases hd)))
def cl_25116 : CNF.NClause := [(119,true),(31,false),(40,true),(44,false),(52,true),(60,false)]
theorem der_25116 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25116 :=
  CNF.rup_sound cl_25116 [cl_3675,cl_25112] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3675 v h) (hints_cons _ _ _ (der_25112 v h) (by intro d hd; cases hd)))
def cl_25117 : CNF.NClause := [(119,true),(40,false),(44,true),(48,true),(52,true),(60,false)]
theorem der_25117 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25117 :=
  CNF.rup_sound cl_25117 [cl_3677,cl_23889] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3677 v h) (hints_cons _ _ _ (der_23889 v h) (by intro d hd; cases hd)))
def cl_25118 : CNF.NClause := [(119,true),(31,false),(40,true),(44,true),(48,true),(60,false)]
theorem der_25118 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25118 :=
  CNF.rup_sound cl_25118 [cl_3679,cl_25110] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3679 v h) (hints_cons _ _ _ (der_25110 v h) (by intro d hd; cases hd)))
def cl_25119 : CNF.NClause := [(119,true),(31,false),(40,false),(44,false),(48,false),(52,false)]
theorem der_25119 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25119 :=
  CNF.rup_sound cl_25119 [cl_3681,cl_3649] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3681 v h) (hints_cons _ _ _ (inp_3649 v h) (by intro d hd; cases hd)))
def cl_25120 : CNF.NClause := [(119,true),(40,true),(44,false),(48,false),(52,false),(60,true)]
theorem der_25120 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25120 :=
  CNF.rup_sound cl_25120 [cl_3683,cl_3684] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3683 v h) (hints_cons _ _ _ (inp_3684 v h) (by intro d hd; cases hd)))
def cl_25121 : CNF.NClause := [(119,true),(31,false),(40,false),(44,true),(48,false),(52,false)]
theorem der_25121 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25121 :=
  CNF.rup_sound cl_25121 [cl_3685,cl_25105] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3685 v h) (hints_cons _ _ _ (der_25105 v h) (by intro d hd; cases hd)))
def cl_25122 : CNF.NClause := [(119,true),(31,false),(40,true),(44,true),(48,false),(52,false)]
theorem der_25122 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25122 :=
  CNF.rup_sound cl_25122 [cl_3687,cl_25106] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3687 v h) (hints_cons _ _ _ (der_25106 v h) (by intro d hd; cases hd)))
def cl_25123 : CNF.NClause := [(119,true),(31,false),(40,false),(44,false),(48,true),(52,false)]
theorem der_25123 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25123 :=
  CNF.rup_sound cl_25123 [cl_3689,cl_25107] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3689 v h) (hints_cons _ _ _ (der_25107 v h) (by intro d hd; cases hd)))
def cl_25124 : CNF.NClause := [(119,true),(31,false),(44,false),(48,true),(52,false),(60,true)]
theorem der_25124 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25124 :=
  CNF.rup_sound cl_25124 [cl_3691,cl_25123] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3691 v h) (hints_cons _ _ _ (der_25123 v h) (by intro d hd; cases hd)))
def cl_25125 : CNF.NClause := [(119,true),(31,false),(40,false),(44,true),(48,true),(52,false)]
theorem der_25125 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25125 :=
  CNF.rup_sound cl_25125 [cl_3693,cl_25109] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3693 v h) (hints_cons _ _ _ (der_25109 v h) (by intro d hd; cases hd)))
def cl_25126 : CNF.NClause := [(119,true),(31,false),(40,true),(44,true),(48,true),(52,false)]
theorem der_25126 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25126 :=
  CNF.rup_sound cl_25126 [cl_3695,cl_25118] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3695 v h) (hints_cons _ _ _ (der_25118 v h) (by intro d hd; cases hd)))
def cl_25127 : CNF.NClause := [(119,true),(31,false),(40,false),(44,false),(48,false),(52,true)]
theorem der_25127 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25127 :=
  CNF.rup_sound cl_25127 [cl_3697,cl_25111] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3697 v h) (hints_cons _ _ _ (der_25111 v h) (by intro d hd; cases hd)))
def cl_25128 : CNF.NClause := [(119,true),(31,false),(40,true),(44,false),(48,false),(52,true)]
theorem der_25128 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25128 :=
  CNF.rup_sound cl_25128 [cl_3699,cl_25112] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3699 v h) (hints_cons _ _ _ (der_25112 v h) (by intro d hd; cases hd)))
def cl_25129 : CNF.NClause := [(119,true),(40,false),(44,true),(48,false),(52,true),(60,true)]
theorem der_25129 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25129 :=
  CNF.rup_sound cl_25129 [cl_3701,cl_23892] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3701 v h) (hints_cons _ _ _ (der_23892 v h) (by intro d hd; cases hd)))
def cl_25131 : CNF.NClause := [(119,true),(31,false),(40,false),(44,false),(48,true),(60,true)]
theorem der_25131 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25131 :=
  CNF.rup_sound cl_25131 [cl_3705,cl_25123] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3705 v h) (hints_cons _ _ _ (der_25123 v h) (by intro d hd; cases hd)))
def cl_25132 : CNF.NClause := [(119,true),(31,false),(44,false),(48,true),(52,true),(60,true)]
theorem der_25132 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25132 :=
  CNF.rup_sound cl_25132 [cl_3707,cl_25131] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3707 v h) (hints_cons _ _ _ (der_25131 v h) (by intro d hd; cases hd)))
def cl_25134 : CNF.NClause := [(120,true),(38,false),(45,false),(47,false),(54,false),(58,false)]
theorem der_25134 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25134 :=
  CNF.rup_sound cl_25134 [cl_3713,cl_25073] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3713 v h) (hints_cons _ _ _ (der_25073 v h) (by intro d hd; cases hd)))
def cl_25135 : CNF.NClause := [(120,true),(38,true),(45,false),(47,false),(54,false),(58,false)]
theorem der_25135 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25135 :=
  CNF.rup_sound cl_25135 [cl_3715,cl_25070] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3715 v h) (hints_cons _ _ _ (der_25070 v h) (by intro d hd; cases hd)))
def cl_25136 : CNF.NClause := [(120,true),(38,false),(45,true),(47,false),(54,false),(58,false)]
theorem der_25136 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25136 :=
  CNF.rup_sound cl_25136 [cl_3717,cl_23714] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3717 v h) (hints_cons _ _ _ (der_23714 v h) (by intro d hd; cases hd)))
def cl_25137 : CNF.NClause := [(120,true),(31,false),(38,true),(47,false),(54,false),(58,false)]
theorem der_25137 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25137 :=
  CNF.rup_sound cl_25137 [cl_3719,cl_25135] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3719 v h) (hints_cons _ _ _ (der_25135 v h) (by intro d hd; cases hd)))
def cl_25138 : CNF.NClause := [(120,true),(31,false),(38,false),(45,false),(54,false),(58,false)]
theorem der_25138 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25138 :=
  CNF.rup_sound cl_25138 [cl_3721,cl_25134] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3721 v h) (hints_cons _ _ _ (der_25134 v h) (by intro d hd; cases hd)))
def cl_25139 : CNF.NClause := [(120,true),(31,false),(38,true),(45,false),(54,false),(58,false)]
theorem der_25139 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25139 :=
  CNF.rup_sound cl_25139 [cl_3723,cl_25135] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3723 v h) (hints_cons _ _ _ (der_25135 v h) (by intro d hd; cases hd)))
def cl_25140 : CNF.NClause := [(120,true),(38,false),(45,true),(47,true),(54,false),(58,false)]
theorem der_25140 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25140 :=
  CNF.rup_sound cl_25140 [cl_3725,cl_3726] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3725 v h) (hints_cons _ _ _ (inp_3726 v h) (by intro d hd; cases hd)))
def cl_25141 : CNF.NClause := [(120,true),(31,false),(38,true),(45,true),(54,false),(58,false)]
theorem der_25141 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25141 :=
  CNF.rup_sound cl_25141 [cl_3727,cl_25137] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3727 v h) (hints_cons _ _ _ (der_25137 v h) (by intro d hd; cases hd)))
def cl_25142 : CNF.NClause := [(120,true),(38,false),(45,false),(47,false),(54,true),(58,false)]
theorem der_25142 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25142 :=
  CNF.rup_sound cl_25142 [cl_3729,cl_25068] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3729 v h) (hints_cons _ _ _ (der_25068 v h) (by intro d hd; cases hd)))
def cl_25143 : CNF.NClause := [(120,true),(38,true),(45,false),(47,false),(54,true),(58,false)]
theorem der_25143 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25143 :=
  CNF.rup_sound cl_25143 [cl_3731,cl_23708] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3731 v h) (hints_cons _ _ _ (der_23708 v h) (by intro d hd; cases hd)))
def cl_25144 : CNF.NClause := [(120,true),(31,false),(38,false),(45,true),(47,false),(58,false)]
theorem der_25144 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25144 :=
  CNF.rup_sound cl_25144 [cl_3733,cl_25136] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3733 v h) (hints_cons _ _ _ (der_25136 v h) (by intro d hd; cases hd)))
def cl_25146 : CNF.NClause := [(120,true),(38,false),(45,false),(47,true),(54,true),(58,false)]
theorem der_25146 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25146 :=
  CNF.rup_sound cl_25146 [cl_3737,cl_25066] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3737 v h) (hints_cons _ _ _ (der_25066 v h) (by intro d hd; cases hd)))
def cl_25147 : CNF.NClause := [(120,true),(38,true),(45,false),(47,true),(54,true),(58,false)]
theorem der_25147 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25147 :=
  CNF.rup_sound cl_25147 [cl_3739,cl_23708] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3739 v h) (hints_cons _ _ _ (der_23708 v h) (by intro d hd; cases hd)))
def cl_25148 : CNF.NClause := [(120,true),(38,false),(45,true),(47,true),(54,true),(58,false)]
theorem der_25148 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25148 :=
  CNF.rup_sound cl_25148 [cl_3741,cl_25066] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3741 v h) (hints_cons _ _ _ (der_25066 v h) (by intro d hd; cases hd)))
def cl_25150 : CNF.NClause := [(120,true),(38,false),(45,false),(47,false),(54,false),(58,true)]
theorem der_25150 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25150 :=
  CNF.rup_sound cl_25150 [cl_3745,cl_25052] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3745 v h) (hints_cons _ _ _ (der_25052 v h) (by intro d hd; cases hd)))
def cl_25151 : CNF.NClause := [(120,true),(38,true),(45,false),(47,false),(54,false),(58,true)]
theorem der_25151 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25151 :=
  CNF.rup_sound cl_25151 [cl_3747,cl_25070] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3747 v h) (hints_cons _ _ _ (der_25070 v h) (by intro d hd; cases hd)))
def cl_25154 : CNF.NClause := [(120,true),(38,false),(45,false),(47,true),(54,false),(58,true)]
theorem der_25154 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25154 :=
  CNF.rup_sound cl_25154 [cl_3753,cl_25051] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3753 v h) (hints_cons _ _ _ (der_25051 v h) (by intro d hd; cases hd)))
def cl_25155 : CNF.NClause := [(120,true),(38,true),(45,false),(47,true),(54,false),(58,true)]
theorem der_25155 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25155 :=
  CNF.rup_sound cl_25155 [cl_3755,cl_23710] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3755 v h) (hints_cons _ _ _ (der_23710 v h) (by intro d hd; cases hd)))
def cl_25156 : CNF.NClause := [(120,true),(38,false),(45,true),(47,true),(54,false),(58,true)]
theorem der_25156 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25156 :=
  CNF.rup_sound cl_25156 [cl_3757,cl_23704] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3757 v h) (hints_cons _ _ _ (der_23704 v h) (by intro d hd; cases hd)))
def cl_25158 : CNF.NClause := [(120,true),(38,false),(45,false),(47,false),(54,true),(58,true)]
theorem der_25158 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25158 :=
  CNF.rup_sound cl_25158 [cl_3761,cl_25069] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3761 v h) (hints_cons _ _ _ (der_25069 v h) (by intro d hd; cases hd)))
def cl_25159 : CNF.NClause := [(120,true),(31,false),(38,true),(45,false),(47,false),(54,true)]
theorem der_25159 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25159 :=
  CNF.rup_sound cl_25159 [cl_3763,cl_25143] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3763 v h) (hints_cons _ _ _ (der_25143 v h) (by intro d hd; cases hd)))
def cl_25160 : CNF.NClause := [(120,true),(31,false),(38,false),(45,true),(47,false),(54,true)]
theorem der_25160 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25160 :=
  CNF.rup_sound cl_25160 [cl_3765,cl_25144] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3765 v h) (hints_cons _ _ _ (der_25144 v h) (by intro d hd; cases hd)))
def cl_25162 : CNF.NClause := [(120,true),(38,false),(45,false),(47,true),(54,true),(58,true)]
theorem der_25162 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25162 :=
  CNF.rup_sound cl_25162 [cl_3769,cl_25067] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3769 v h) (hints_cons _ _ _ (der_25067 v h) (by intro d hd; cases hd)))
def cl_25165 : CNF.NClause := [(121,true),(39,false),(42,false),(50,false),(53,false),(59,false)]
theorem der_25165 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25165 :=
  CNF.rup_sound cl_25165 [cl_3777,cl_23792] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3777 v h) (hints_cons _ _ _ (der_23792 v h) (by intro d hd; cases hd)))
def cl_25166 : CNF.NClause := [(121,true),(31,false),(42,false),(50,false),(53,false),(59,false)]
theorem der_25166 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25166 :=
  CNF.rup_sound cl_25166 [cl_3779,cl_25165] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3779 v h) (hints_cons _ _ _ (der_25165 v h) (by intro d hd; cases hd)))
def cl_25167 : CNF.NClause := [(121,true),(31,false),(39,false),(50,false),(53,false),(59,false)]
theorem der_25167 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25167 :=
  CNF.rup_sound cl_25167 [cl_3781,cl_25165] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3781 v h) (hints_cons _ _ _ (der_25165 v h) (by intro d hd; cases hd)))
def cl_25168 : CNF.NClause := [(121,true),(39,true),(42,true),(50,false),(53,false),(59,false)]
theorem der_25168 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25168 :=
  CNF.rup_sound cl_25168 [cl_3783,cl_24759] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3783 v h) (hints_cons _ _ _ (der_24759 v h) (by intro d hd; cases hd)))
def cl_25169 : CNF.NClause := [(121,true),(31,false),(39,false),(42,false),(53,false),(59,false)]
theorem der_25169 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25169 :=
  CNF.rup_sound cl_25169 [cl_3785,cl_25165] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3785 v h) (hints_cons _ _ _ (der_25165 v h) (by intro d hd; cases hd)))
def cl_25170 : CNF.NClause := [(121,true),(31,false),(39,true),(42,false),(53,false),(59,false)]
theorem der_25170 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25170 :=
  CNF.rup_sound cl_25170 [cl_3787,cl_25166] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3787 v h) (hints_cons _ _ _ (der_25166 v h) (by intro d hd; cases hd)))
def cl_25171 : CNF.NClause := [(121,true),(31,false),(39,false),(42,true),(53,false),(59,false)]
theorem der_25171 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25171 :=
  CNF.rup_sound cl_25171 [cl_3789,cl_25167] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3789 v h) (hints_cons _ _ _ (der_25167 v h) (by intro d hd; cases hd)))
def cl_25172 : CNF.NClause := [(121,true),(39,true),(42,true),(50,true),(53,false),(59,false)]
theorem der_25172 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25172 :=
  CNF.rup_sound cl_25172 [cl_3791,cl_3792] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3791 v h) (hints_cons _ _ _ (inp_3792 v h) (by intro d hd; cases hd)))
def cl_25173 : CNF.NClause := [(121,true),(39,false),(42,false),(50,false),(53,true),(59,false)]
theorem der_25173 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25173 :=
  CNF.rup_sound cl_25173 [cl_3793,cl_3794] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3793 v h) (hints_cons _ _ _ (inp_3794 v h) (by intro d hd; cases hd)))
def cl_25174 : CNF.NClause := [(121,true),(31,false),(39,true),(42,false),(50,false),(59,false)]
theorem der_25174 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25174 :=
  CNF.rup_sound cl_25174 [cl_3795,cl_25166] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3795 v h) (hints_cons _ _ _ (der_25166 v h) (by intro d hd; cases hd)))
def cl_25175 : CNF.NClause := [(121,true),(31,false),(39,false),(42,true),(50,false),(59,false)]
theorem der_25175 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25175 :=
  CNF.rup_sound cl_25175 [cl_3797,cl_25167] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3797 v h) (hints_cons _ _ _ (der_25167 v h) (by intro d hd; cases hd)))
def cl_25176 : CNF.NClause := [(121,true),(31,false),(39,true),(50,false),(53,true),(59,false)]
theorem der_25176 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25176 :=
  CNF.rup_sound cl_25176 [cl_3799,cl_25174] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3799 v h) (hints_cons _ _ _ (der_25174 v h) (by intro d hd; cases hd)))
def cl_25177 : CNF.NClause := [(121,true),(31,false),(39,false),(42,false),(50,true),(59,false)]
theorem der_25177 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25177 :=
  CNF.rup_sound cl_25177 [cl_3801,cl_25169] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3801 v h) (hints_cons _ _ _ (der_25169 v h) (by intro d hd; cases hd)))
def cl_25178 : CNF.NClause := [(121,true),(31,false),(42,false),(50,true),(53,true),(59,false)]
theorem der_25178 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25178 :=
  CNF.rup_sound cl_25178 [cl_3803,cl_25177] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3803 v h) (hints_cons _ _ _ (der_25177 v h) (by intro d hd; cases hd)))
def cl_25179 : CNF.NClause := [(121,true),(31,false),(39,false),(50,true),(53,true),(59,false)]
theorem der_25179 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25179 :=
  CNF.rup_sound cl_25179 [cl_3805,cl_25177] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3805 v h) (hints_cons _ _ _ (der_25177 v h) (by intro d hd; cases hd)))
def cl_25181 : CNF.NClause := [(121,true),(31,false),(39,false),(42,false),(50,false),(53,false)]
theorem der_25181 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25181 :=
  CNF.rup_sound cl_25181 [cl_3809,cl_25165] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3809 v h) (hints_cons _ _ _ (der_25165 v h) (by intro d hd; cases hd)))
def cl_25182 : CNF.NClause := [(121,true),(31,false),(39,true),(42,false),(50,false),(53,false)]
theorem der_25182 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25182 :=
  CNF.rup_sound cl_25182 [cl_3811,cl_25166] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3811 v h) (hints_cons _ _ _ (der_25166 v h) (by intro d hd; cases hd)))
def cl_25183 : CNF.NClause := [(121,true),(31,false),(39,false),(42,true),(50,false),(53,false)]
theorem der_25183 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25183 :=
  CNF.rup_sound cl_25183 [cl_3813,cl_25167] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3813 v h) (hints_cons _ _ _ (der_25167 v h) (by intro d hd; cases hd)))
def cl_25184 : CNF.NClause := [(121,true),(31,false),(39,true),(50,false),(53,false),(59,true)]
theorem der_25184 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25184 :=
  CNF.rup_sound cl_25184 [cl_3815,cl_25182] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3815 v h) (hints_cons _ _ _ (der_25182 v h) (by intro d hd; cases hd)))
def cl_25185 : CNF.NClause := [(121,true),(31,false),(39,false),(42,false),(50,true),(53,false)]
theorem der_25185 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25185 :=
  CNF.rup_sound cl_25185 [cl_3817,cl_25169] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3817 v h) (hints_cons _ _ _ (der_25169 v h) (by intro d hd; cases hd)))
def cl_25186 : CNF.NClause := [(121,true),(31,false),(39,true),(42,false),(53,false),(59,true)]
theorem der_25186 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25186 :=
  CNF.rup_sound cl_25186 [cl_3819,cl_25182] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3819 v h) (hints_cons _ _ _ (der_25182 v h) (by intro d hd; cases hd)))
def cl_25187 : CNF.NClause := [(121,true),(31,false),(39,false),(42,true),(50,true),(53,false)]
theorem der_25187 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25187 :=
  CNF.rup_sound cl_25187 [cl_3821,cl_25171] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3821 v h) (hints_cons _ _ _ (der_25171 v h) (by intro d hd; cases hd)))
def cl_25188 : CNF.NClause := [(121,true),(31,false),(42,true),(50,true),(53,false),(59,true)]
theorem der_25188 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25188 :=
  CNF.rup_sound cl_25188 [cl_3823,cl_25187] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3823 v h) (hints_cons _ _ _ (der_25187 v h) (by intro d hd; cases hd)))
def cl_25189 : CNF.NClause := [(121,true),(39,false),(42,false),(50,false),(53,true),(59,true)]
theorem der_25189 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25189 :=
  CNF.rup_sound cl_25189 [cl_3825,cl_23744] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3825 v h) (hints_cons _ _ _ (der_23744 v h) (by intro d hd; cases hd)))
def cl_25190 : CNF.NClause := [(121,true),(31,false),(39,true),(42,false),(50,false),(59,true)]
theorem der_25190 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25190 :=
  CNF.rup_sound cl_25190 [cl_3827,cl_25182] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3827 v h) (hints_cons _ _ _ (der_25182 v h) (by intro d hd; cases hd)))
def cl_25191 : CNF.NClause := [(121,true),(31,false),(39,false),(42,true),(50,false),(59,true)]
theorem der_25191 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25191 :=
  CNF.rup_sound cl_25191 [cl_3829,cl_25183] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3829 v h) (hints_cons _ _ _ (der_25183 v h) (by intro d hd; cases hd)))
def cl_25192 : CNF.NClause := [(121,true),(31,false),(42,true),(50,false),(53,true),(59,true)]
theorem der_25192 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25192 :=
  CNF.rup_sound cl_25192 [cl_3831,cl_25191] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3831 v h) (hints_cons _ _ _ (der_25191 v h) (by intro d hd; cases hd)))
def cl_25193 : CNF.NClause := [(121,true),(31,false),(39,false),(42,false),(50,true),(53,true)]
theorem der_25193 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25193 :=
  CNF.rup_sound cl_25193 [cl_3833,cl_25177] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3833 v h) (hints_cons _ _ _ (der_25177 v h) (by intro d hd; cases hd)))
def cl_25194 : CNF.NClause := [(121,true),(31,false),(39,true),(42,false),(53,true),(59,true)]
theorem der_25194 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25194 :=
  CNF.rup_sound cl_25194 [cl_3835,cl_25190] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3835 v h) (hints_cons _ _ _ (der_25190 v h) (by intro d hd; cases hd)))
def cl_25195 : CNF.NClause := [(121,true),(31,false),(39,false),(42,true),(50,true),(59,true)]
theorem der_25195 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25195 :=
  CNF.rup_sound cl_25195 [cl_3837,cl_25187] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3837 v h) (hints_cons _ _ _ (der_25187 v h) (by intro d hd; cases hd)))
def cl_25196 : CNF.NClause := [(122,true),(31,false),(43,false),(49,false),(55,false),(57,false)]
theorem der_25196 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25196 :=
  CNF.rup_sound cl_25196 [cl_3843,cl_3841] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3843 v h) (hints_cons _ _ _ (inp_3841 v h) (by intro d hd; cases hd)))
def cl_25197 : CNF.NClause := [(122,true),(31,false),(37,false),(49,false),(55,false),(57,false)]
theorem der_25197 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25197 :=
  CNF.rup_sound cl_25197 [cl_3845,cl_3841] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3845 v h) (hints_cons _ _ _ (inp_3841 v h) (by intro d hd; cases hd)))
def cl_25198 : CNF.NClause := [(122,true),(37,true),(43,true),(49,false),(55,false),(57,false)]
theorem der_25198 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25198 :=
  CNF.rup_sound cl_25198 [cl_3847,cl_3848] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3847 v h) (hints_cons _ _ _ (inp_3848 v h) (by intro d hd; cases hd)))
def cl_25199 : CNF.NClause := [(122,true),(37,false),(43,false),(49,true),(55,false),(57,false)]
theorem der_25199 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25199 :=
  CNF.rup_sound cl_25199 [cl_3849,cl_24833] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3849 v h) (hints_cons _ _ _ (der_24833 v h) (by intro d hd; cases hd)))
def cl_25200 : CNF.NClause := [(122,true),(37,true),(43,false),(49,true),(55,false),(57,false)]
theorem der_25200 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25200 :=
  CNF.rup_sound cl_25200 [cl_3851,cl_24833] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3851 v h) (hints_cons _ _ _ (der_24833 v h) (by intro d hd; cases hd)))
def cl_25201 : CNF.NClause := [(122,true),(31,false),(37,false),(43,true),(55,false),(57,false)]
theorem der_25201 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25201 :=
  CNF.rup_sound cl_25201 [cl_3853,cl_25197] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3853 v h) (hints_cons _ _ _ (der_25197 v h) (by intro d hd; cases hd)))
def cl_25202 : CNF.NClause := [(122,true),(37,true),(43,true),(49,true),(55,false),(57,false)]
theorem der_25202 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25202 :=
  CNF.rup_sound cl_25202 [cl_3855,cl_24834] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3855 v h) (hints_cons _ _ _ (der_24834 v h) (by intro d hd; cases hd)))
def cl_25203 : CNF.NClause := [(122,true),(31,false),(37,false),(43,false),(49,false),(57,false)]
theorem der_25203 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25203 :=
  CNF.rup_sound cl_25203 [cl_3857,cl_3841] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3857 v h) (hints_cons _ _ _ (inp_3841 v h) (by intro d hd; cases hd)))
def chunk005 : List CNF.NClause := [cl_24678,cl_24679,cl_24680,cl_24681,cl_24682,cl_24683,cl_24684,cl_24685,cl_24686,cl_24687,cl_24688,cl_24689,cl_24690,cl_24691,cl_24692,cl_24693,cl_24694,cl_24695,cl_24696,cl_24697,cl_24698,cl_24699,cl_24700,cl_24701,cl_24702,cl_24703,cl_24704,cl_24705,cl_24706,cl_24707,cl_24708,cl_24709,cl_24710,cl_24711,cl_24712,cl_24713,cl_24714,cl_24715,cl_24716,cl_24717,cl_24718,cl_24719,cl_24720,cl_24721,cl_24722,cl_24723,cl_24724,cl_24725,cl_24726,cl_24727,cl_24728,cl_24729,cl_24730,cl_24731,cl_24732,cl_24733,cl_24734,cl_24735,cl_24736,cl_24737,cl_24738,cl_24739,cl_24740,cl_24741,cl_24742,cl_24743,cl_24744,cl_24745,cl_24746,cl_24747,cl_24748,cl_24749,cl_24750,cl_24751,cl_24752,cl_24753,cl_24754,cl_24755,cl_24756,cl_24757,cl_24758,cl_24759,cl_24760,cl_24761,cl_24762,cl_24763,cl_24764,cl_24765,cl_24766,cl_24767,cl_24768,cl_24769,cl_24770,cl_24771,cl_24772,cl_24773,cl_24774,cl_24775,cl_24776,cl_24777,cl_24778,cl_24779,cl_24780,cl_24782,cl_24783,cl_24784,cl_24785,cl_24786,cl_24787,cl_24788,cl_24789,cl_24790,cl_24791,cl_24792,cl_24793,cl_24794,cl_24795,cl_24796,cl_24797,cl_24798,cl_24799,cl_24800,cl_24801,cl_24802,cl_24803,cl_24804,cl_24805,cl_24806,cl_24807,cl_24808,cl_24809,cl_24810,cl_24811,cl_24812,cl_24813,cl_24814,cl_24815,cl_24816,cl_24817,cl_24818,cl_24819,cl_24820,cl_24821,cl_24822,cl_24823,cl_24824,cl_24826,cl_24827,cl_24828,cl_24829,cl_24830,cl_24831,cl_24832,cl_24833,cl_24834,cl_24835,cl_24836,cl_24837,cl_24838,cl_24839,cl_24840,cl_24841,cl_24842,cl_24843,cl_24844,cl_24845,cl_24846,cl_24847,cl_24849,cl_24850,cl_24851,cl_24852,cl_24856,cl_24857,cl_24858,cl_24859,cl_24860,cl_24861,cl_24862,cl_24863,cl_24864,cl_24865,cl_24866,cl_24867,cl_24868,cl_24869,cl_24870,cl_24871,cl_24872,cl_24873,cl_24874,cl_24875,cl_24876,cl_24877,cl_24878,cl_24879,cl_24880,cl_24881,cl_24882,cl_24883,cl_24884,cl_24885,cl_24886,cl_24887,cl_24888,cl_24889,cl_24890,cl_24891,cl_24892,cl_24893,cl_24894,cl_24895,cl_24896,cl_24897,cl_24898,cl_24899,cl_24900,cl_24901,cl_24902,cl_24903,cl_24904,cl_24905,cl_24906,cl_24907,cl_24908,cl_24909,cl_24910,cl_24911,cl_24912,cl_24913,cl_24914,cl_24915,cl_24916,cl_24917,cl_24918,cl_24919,cl_24920,cl_24921,cl_24922,cl_24923,cl_24924,cl_24925,cl_24926,cl_24927,cl_24928,cl_24929,cl_24930,cl_24931,cl_24932,cl_24933,cl_24934,cl_24935,cl_24936,cl_24937,cl_24938,cl_24939,cl_24940,cl_24941,cl_24942,cl_24943,cl_24944,cl_24945,cl_24946,cl_24947,cl_24948,cl_24949,cl_24950,cl_24951,cl_24952,cl_24953,cl_24954,cl_24955,cl_24956,cl_24957,cl_24958,cl_24959,cl_24960,cl_24961,cl_24962,cl_24963,cl_24964,cl_24965,cl_24966,cl_24967,cl_24968,cl_24969,cl_24970,cl_24971,cl_24972,cl_24973,cl_24974,cl_24975,cl_24976,cl_24977,cl_24978,cl_24979,cl_24980,cl_24981,cl_24982,cl_24983,cl_24984,cl_24985,cl_24986,cl_24987,cl_24988,cl_24989,cl_24990,cl_24991,cl_24992,cl_24993,cl_24994,cl_24995,cl_24996,cl_24997,cl_24998,cl_24999,cl_25000,cl_25001,cl_25002,cl_25003,cl_25004,cl_25005,cl_25006,cl_25007,cl_25008,cl_25009,cl_25010,cl_25011,cl_25012,cl_25013,cl_25014,cl_25015,cl_25016,cl_25017,cl_25018,cl_25019,cl_25020,cl_25021,cl_25022,cl_25023,cl_25024,cl_25025,cl_25026,cl_25027,cl_25028,cl_25029,cl_25030,cl_25031,cl_25032,cl_25033,cl_25034,cl_25035,cl_25036,cl_25037,cl_25038,cl_25039,cl_25040,cl_25041,cl_25042,cl_25043,cl_25044,cl_25045,cl_25046,cl_25047,cl_25048,cl_25049,cl_25050,cl_25051,cl_25052,cl_25053,cl_25054,cl_25055,cl_25056,cl_25057,cl_25058,cl_25059,cl_25060,cl_25061,cl_25062,cl_25063,cl_25064,cl_25065,cl_25066,cl_25067,cl_25068,cl_25069,cl_25070,cl_25071,cl_25072,cl_25073,cl_25074,cl_25075,cl_25076,cl_25077,cl_25078,cl_25079,cl_25080,cl_25081,cl_25082,cl_25083,cl_25084,cl_25085,cl_25087,cl_25088,cl_25091,cl_25092,cl_25093,cl_25094,cl_25095,cl_25099,cl_25101,cl_25103,cl_25104,cl_25105,cl_25106,cl_25107,cl_25108,cl_25109,cl_25110,cl_25111,cl_25112,cl_25113,cl_25115,cl_25116,cl_25117,cl_25118,cl_25119,cl_25120,cl_25121,cl_25122,cl_25123,cl_25124,cl_25125,cl_25126,cl_25127,cl_25128,cl_25129,cl_25131,cl_25132,cl_25134,cl_25135,cl_25136,cl_25137,cl_25138,cl_25139,cl_25140,cl_25141,cl_25142,cl_25143,cl_25144,cl_25146,cl_25147,cl_25148,cl_25150,cl_25151,cl_25154,cl_25155,cl_25156,cl_25158,cl_25159,cl_25160,cl_25162,cl_25165,cl_25166,cl_25167,cl_25168,cl_25169,cl_25170,cl_25171,cl_25172,cl_25173,cl_25174,cl_25175,cl_25176,cl_25177,cl_25178,cl_25179,cl_25181,cl_25182,cl_25183,cl_25184,cl_25185,cl_25186,cl_25187,cl_25188,cl_25189,cl_25190,cl_25191,cl_25192,cl_25193,cl_25194,cl_25195,cl_25196,cl_25197,cl_25198,cl_25199,cl_25200,cl_25201,cl_25202,cl_25203]
theorem chunk_sound005 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : ∀ c ∈ chunk005, CNF.Holds (v ∘ decodeVar) c :=
  (hints_cons _ _ _ (der_24678 v h) (hints_cons _ _ _ (der_24679 v h) (hints_cons _ _ _ (der_24680 v h) (hints_cons _ _ _ (der_24681 v h) (hints_cons _ _ _ (der_24682 v h) (hints_cons _ _ _ (der_24683 v h) (hints_cons _ _ _ (der_24684 v h) (hints_cons _ _ _ (der_24685 v h) (hints_cons _ _ _ (der_24686 v h) (hints_cons _ _ _ (der_24687 v h) (hints_cons _ _ _ (der_24688 v h) (hints_cons _ _ _ (der_24689 v h) (hints_cons _ _ _ (der_24690 v h) (hints_cons _ _ _ (der_24691 v h) (hints_cons _ _ _ (der_24692 v h) (hints_cons _ _ _ (der_24693 v h) (hints_cons _ _ _ (der_24694 v h) (hints_cons _ _ _ (der_24695 v h) (hints_cons _ _ _ (der_24696 v h) (hints_cons _ _ _ (der_24697 v h) (hints_cons _ _ _ (der_24698 v h) (hints_cons _ _ _ (der_24699 v h) (hints_cons _ _ _ (der_24700 v h) (hints_cons _ _ _ (der_24701 v h) (hints_cons _ _ _ (der_24702 v h) (hints_cons _ _ _ (der_24703 v h) (hints_cons _ _ _ (der_24704 v h) (hints_cons _ _ _ (der_24705 v h) (hints_cons _ _ _ (der_24706 v h) (hints_cons _ _ _ (der_24707 v h) (hints_cons _ _ _ (der_24708 v h) (hints_cons _ _ _ (der_24709 v h) (hints_cons _ _ _ (der_24710 v h) (hints_cons _ _ _ (der_24711 v h) (hints_cons _ _ _ (der_24712 v h) (hints_cons _ _ _ (der_24713 v h) (hints_cons _ _ _ (der_24714 v h) (hints_cons _ _ _ (der_24715 v h) (hints_cons _ _ _ (der_24716 v h) (hints_cons _ _ _ (der_24717 v h) (hints_cons _ _ _ (der_24718 v h) (hints_cons _ _ _ (der_24719 v h) (hints_cons _ _ _ (der_24720 v h) (hints_cons _ _ _ (der_24721 v h) (hints_cons _ _ _ (der_24722 v h) (hints_cons _ _ _ (der_24723 v h) (hints_cons _ _ _ (der_24724 v h) (hints_cons _ _ _ (der_24725 v h) (hints_cons _ _ _ (der_24726 v h) (hints_cons _ _ _ (der_24727 v h) (hints_cons _ _ _ (der_24728 v h) (hints_cons _ _ _ (der_24729 v h) (hints_cons _ _ _ (der_24730 v h) (hints_cons _ _ _ (der_24731 v h) (hints_cons _ _ _ (der_24732 v h) (hints_cons _ _ _ (der_24733 v h) (hints_cons _ _ _ (der_24734 v h) (hints_cons _ _ _ (der_24735 v h) (hints_cons _ _ _ (der_24736 v h) (hints_cons _ _ _ (der_24737 v h) (hints_cons _ _ _ (der_24738 v h) (hints_cons _ _ _ (der_24739 v h) (hints_cons _ _ _ (der_24740 v h) (hints_cons _ _ _ (der_24741 v h) (hints_cons _ _ _ (der_24742 v h) (hints_cons _ _ _ (der_24743 v h) (hints_cons _ _ _ (der_24744 v h) (hints_cons _ _ _ (der_24745 v h) (hints_cons _ _ _ (der_24746 v h) (hints_cons _ _ _ (der_24747 v h) (hints_cons _ _ _ (der_24748 v h) (hints_cons _ _ _ (der_24749 v h) (hints_cons _ _ _ (der_24750 v h) (hints_cons _ _ _ (der_24751 v h) (hints_cons _ _ _ (der_24752 v h) (hints_cons _ _ _ (der_24753 v h) (hints_cons _ _ _ (der_24754 v h) (hints_cons _ _ _ (der_24755 v h) (hints_cons _ _ _ (der_24756 v h) (hints_cons _ _ _ (der_24757 v h) (hints_cons _ _ _ (der_24758 v h) (hints_cons _ _ _ (der_24759 v h) (hints_cons _ _ _ (der_24760 v h) (hints_cons _ _ _ (der_24761 v h) (hints_cons _ _ _ (der_24762 v h) (hints_cons _ _ _ (der_24763 v h) (hints_cons _ _ _ (der_24764 v h) (hints_cons _ _ _ (der_24765 v h) (hints_cons _ _ _ (der_24766 v h) (hints_cons _ _ _ (der_24767 v h) (hints_cons _ _ _ (der_24768 v h) (hints_cons _ _ _ (der_24769 v h) (hints_cons _ _ _ (der_24770 v h) (hints_cons _ _ _ (der_24771 v h) (hints_cons _ _ _ (der_24772 v h) (hints_cons _ _ _ (der_24773 v h) (hints_cons _ _ _ (der_24774 v h) (hints_cons _ _ _ (der_24775 v h) (hints_cons _ _ _ (der_24776 v h) (hints_cons _ _ _ (der_24777 v h) (hints_cons _ _ _ (der_24778 v h) (hints_cons _ _ _ (der_24779 v h) (hints_cons _ _ _ (der_24780 v h) (hints_cons _ _ _ (der_24782 v h) (hints_cons _ _ _ (der_24783 v h) (hints_cons _ _ _ (der_24784 v h) (hints_cons _ _ _ (der_24785 v h) (hints_cons _ _ _ (der_24786 v h) (hints_cons _ _ _ (der_24787 v h) (hints_cons _ _ _ (der_24788 v h) (hints_cons _ _ _ (der_24789 v h) (hints_cons _ _ _ (der_24790 v h) (hints_cons _ _ _ (der_24791 v h) (hints_cons _ _ _ (der_24792 v h) (hints_cons _ _ _ (der_24793 v h) (hints_cons _ _ _ (der_24794 v h) (hints_cons _ _ _ (der_24795 v h) (hints_cons _ _ _ (der_24796 v h) (hints_cons _ _ _ (der_24797 v h) (hints_cons _ _ _ (der_24798 v h) (hints_cons _ _ _ (der_24799 v h) (hints_cons _ _ _ (der_24800 v h) (hints_cons _ _ _ (der_24801 v h) (hints_cons _ _ _ (der_24802 v h) (hints_cons _ _ _ (der_24803 v h) (hints_cons _ _ _ (der_24804 v h) (hints_cons _ _ _ (der_24805 v h) (hints_cons _ _ _ (der_24806 v h) (hints_cons _ _ _ (der_24807 v h) (hints_cons _ _ _ (der_24808 v h) (hints_cons _ _ _ (der_24809 v h) (hints_cons _ _ _ (der_24810 v h) (hints_cons _ _ _ (der_24811 v h) (hints_cons _ _ _ (der_24812 v h) (hints_cons _ _ _ (der_24813 v h) (hints_cons _ _ _ (der_24814 v h) (hints_cons _ _ _ (der_24815 v h) (hints_cons _ _ _ (der_24816 v h) (hints_cons _ _ _ (der_24817 v h) (hints_cons _ _ _ (der_24818 v h) (hints_cons _ _ _ (der_24819 v h) (hints_cons _ _ _ (der_24820 v h) (hints_cons _ _ _ (der_24821 v h) (hints_cons _ _ _ (der_24822 v h) (hints_cons _ _ _ (der_24823 v h) (hints_cons _ _ _ (der_24824 v h) (hints_cons _ _ _ (der_24826 v h) (hints_cons _ _ _ (der_24827 v h) (hints_cons _ _ _ (der_24828 v h) (hints_cons _ _ _ (der_24829 v h) (hints_cons _ _ _ (der_24830 v h) (hints_cons _ _ _ (der_24831 v h) (hints_cons _ _ _ (der_24832 v h) (hints_cons _ _ _ (der_24833 v h) (hints_cons _ _ _ (der_24834 v h) (hints_cons _ _ _ (der_24835 v h) (hints_cons _ _ _ (der_24836 v h) (hints_cons _ _ _ (der_24837 v h) (hints_cons _ _ _ (der_24838 v h) (hints_cons _ _ _ (der_24839 v h) (hints_cons _ _ _ (der_24840 v h) (hints_cons _ _ _ (der_24841 v h) (hints_cons _ _ _ (der_24842 v h) (hints_cons _ _ _ (der_24843 v h) (hints_cons _ _ _ (der_24844 v h) (hints_cons _ _ _ (der_24845 v h) (hints_cons _ _ _ (der_24846 v h) (hints_cons _ _ _ (der_24847 v h) (hints_cons _ _ _ (der_24849 v h) (hints_cons _ _ _ (der_24850 v h) (hints_cons _ _ _ (der_24851 v h) (hints_cons _ _ _ (der_24852 v h) (hints_cons _ _ _ (der_24856 v h) (hints_cons _ _ _ (der_24857 v h) (hints_cons _ _ _ (der_24858 v h) (hints_cons _ _ _ (der_24859 v h) (hints_cons _ _ _ (der_24860 v h) (hints_cons _ _ _ (der_24861 v h) (hints_cons _ _ _ (der_24862 v h) (hints_cons _ _ _ (der_24863 v h) (hints_cons _ _ _ (der_24864 v h) (hints_cons _ _ _ (der_24865 v h) (hints_cons _ _ _ (der_24866 v h) (hints_cons _ _ _ (der_24867 v h) (hints_cons _ _ _ (der_24868 v h) (hints_cons _ _ _ (der_24869 v h) (hints_cons _ _ _ (der_24870 v h) (hints_cons _ _ _ (der_24871 v h) (hints_cons _ _ _ (der_24872 v h) (hints_cons _ _ _ (der_24873 v h) (hints_cons _ _ _ (der_24874 v h) (hints_cons _ _ _ (der_24875 v h) (hints_cons _ _ _ (der_24876 v h) (hints_cons _ _ _ (der_24877 v h) (hints_cons _ _ _ (der_24878 v h) (hints_cons _ _ _ (der_24879 v h) (hints_cons _ _ _ (der_24880 v h) (hints_cons _ _ _ (der_24881 v h) (hints_cons _ _ _ (der_24882 v h) (hints_cons _ _ _ (der_24883 v h) (hints_cons _ _ _ (der_24884 v h) (hints_cons _ _ _ (der_24885 v h) (hints_cons _ _ _ (der_24886 v h) (hints_cons _ _ _ (der_24887 v h) (hints_cons _ _ _ (der_24888 v h) (hints_cons _ _ _ (der_24889 v h) (hints_cons _ _ _ (der_24890 v h) (hints_cons _ _ _ (der_24891 v h) (hints_cons _ _ _ (der_24892 v h) (hints_cons _ _ _ (der_24893 v h) (hints_cons _ _ _ (der_24894 v h) (hints_cons _ _ _ (der_24895 v h) (hints_cons _ _ _ (der_24896 v h) (hints_cons _ _ _ (der_24897 v h) (hints_cons _ _ _ (der_24898 v h) (hints_cons _ _ _ (der_24899 v h) (hints_cons _ _ _ (der_24900 v h) (hints_cons _ _ _ (der_24901 v h) (hints_cons _ _ _ (der_24902 v h) (hints_cons _ _ _ (der_24903 v h) (hints_cons _ _ _ (der_24904 v h) (hints_cons _ _ _ (der_24905 v h) (hints_cons _ _ _ (der_24906 v h) (hints_cons _ _ _ (der_24907 v h) (hints_cons _ _ _ (der_24908 v h) (hints_cons _ _ _ (der_24909 v h) (hints_cons _ _ _ (der_24910 v h) (hints_cons _ _ _ (der_24911 v h) (hints_cons _ _ _ (der_24912 v h) (hints_cons _ _ _ (der_24913 v h) (hints_cons _ _ _ (der_24914 v h) (hints_cons _ _ _ (der_24915 v h) (hints_cons _ _ _ (der_24916 v h) (hints_cons _ _ _ (der_24917 v h) (hints_cons _ _ _ (der_24918 v h) (hints_cons _ _ _ (der_24919 v h) (hints_cons _ _ _ (der_24920 v h) (hints_cons _ _ _ (der_24921 v h) (hints_cons _ _ _ (der_24922 v h) (hints_cons _ _ _ (der_24923 v h) (hints_cons _ _ _ (der_24924 v h) (hints_cons _ _ _ (der_24925 v h) (hints_cons _ _ _ (der_24926 v h) (hints_cons _ _ _ (der_24927 v h) (hints_cons _ _ _ (der_24928 v h) (hints_cons _ _ _ (der_24929 v h) (hints_cons _ _ _ (der_24930 v h) (hints_cons _ _ _ (der_24931 v h) (hints_cons _ _ _ (der_24932 v h) (hints_cons _ _ _ (der_24933 v h) (hints_cons _ _ _ (der_24934 v h) (hints_cons _ _ _ (der_24935 v h) (hints_cons _ _ _ (der_24936 v h) (hints_cons _ _ _ (der_24937 v h) (hints_cons _ _ _ (der_24938 v h) (hints_cons _ _ _ (der_24939 v h) (hints_cons _ _ _ (der_24940 v h) (hints_cons _ _ _ (der_24941 v h) (hints_cons _ _ _ (der_24942 v h) (hints_cons _ _ _ (der_24943 v h) (hints_cons _ _ _ (der_24944 v h) (hints_cons _ _ _ (der_24945 v h) (hints_cons _ _ _ (der_24946 v h) (hints_cons _ _ _ (der_24947 v h) (hints_cons _ _ _ (der_24948 v h) (hints_cons _ _ _ (der_24949 v h) (hints_cons _ _ _ (der_24950 v h) (hints_cons _ _ _ (der_24951 v h) (hints_cons _ _ _ (der_24952 v h) (hints_cons _ _ _ (der_24953 v h) (hints_cons _ _ _ (der_24954 v h) (hints_cons _ _ _ (der_24955 v h) (hints_cons _ _ _ (der_24956 v h) (hints_cons _ _ _ (der_24957 v h) (hints_cons _ _ _ (der_24958 v h) (hints_cons _ _ _ (der_24959 v h) (hints_cons _ _ _ (der_24960 v h) (hints_cons _ _ _ (der_24961 v h) (hints_cons _ _ _ (der_24962 v h) (hints_cons _ _ _ (der_24963 v h) (hints_cons _ _ _ (der_24964 v h) (hints_cons _ _ _ (der_24965 v h) (hints_cons _ _ _ (der_24966 v h) (hints_cons _ _ _ (der_24967 v h) (hints_cons _ _ _ (der_24968 v h) (hints_cons _ _ _ (der_24969 v h) (hints_cons _ _ _ (der_24970 v h) (hints_cons _ _ _ (der_24971 v h) (hints_cons _ _ _ (der_24972 v h) (hints_cons _ _ _ (der_24973 v h) (hints_cons _ _ _ (der_24974 v h) (hints_cons _ _ _ (der_24975 v h) (hints_cons _ _ _ (der_24976 v h) (hints_cons _ _ _ (der_24977 v h) (hints_cons _ _ _ (der_24978 v h) (hints_cons _ _ _ (der_24979 v h) (hints_cons _ _ _ (der_24980 v h) (hints_cons _ _ _ (der_24981 v h) (hints_cons _ _ _ (der_24982 v h) (hints_cons _ _ _ (der_24983 v h) (hints_cons _ _ _ (der_24984 v h) (hints_cons _ _ _ (der_24985 v h) (hints_cons _ _ _ (der_24986 v h) (hints_cons _ _ _ (der_24987 v h) (hints_cons _ _ _ (der_24988 v h) (hints_cons _ _ _ (der_24989 v h) (hints_cons _ _ _ (der_24990 v h) (hints_cons _ _ _ (der_24991 v h) (hints_cons _ _ _ (der_24992 v h) (hints_cons _ _ _ (der_24993 v h) (hints_cons _ _ _ (der_24994 v h) (hints_cons _ _ _ (der_24995 v h) (hints_cons _ _ _ (der_24996 v h) (hints_cons _ _ _ (der_24997 v h) (hints_cons _ _ _ (der_24998 v h) (hints_cons _ _ _ (der_24999 v h) (hints_cons _ _ _ (der_25000 v h) (hints_cons _ _ _ (der_25001 v h) (hints_cons _ _ _ (der_25002 v h) (hints_cons _ _ _ (der_25003 v h) (hints_cons _ _ _ (der_25004 v h) (hints_cons _ _ _ (der_25005 v h) (hints_cons _ _ _ (der_25006 v h) (hints_cons _ _ _ (der_25007 v h) (hints_cons _ _ _ (der_25008 v h) (hints_cons _ _ _ (der_25009 v h) (hints_cons _ _ _ (der_25010 v h) (hints_cons _ _ _ (der_25011 v h) (hints_cons _ _ _ (der_25012 v h) (hints_cons _ _ _ (der_25013 v h) (hints_cons _ _ _ (der_25014 v h) (hints_cons _ _ _ (der_25015 v h) (hints_cons _ _ _ (der_25016 v h) (hints_cons _ _ _ (der_25017 v h) (hints_cons _ _ _ (der_25018 v h) (hints_cons _ _ _ (der_25019 v h) (hints_cons _ _ _ (der_25020 v h) (hints_cons _ _ _ (der_25021 v h) (hints_cons _ _ _ (der_25022 v h) (hints_cons _ _ _ (der_25023 v h) (hints_cons _ _ _ (der_25024 v h) (hints_cons _ _ _ (der_25025 v h) (hints_cons _ _ _ (der_25026 v h) (hints_cons _ _ _ (der_25027 v h) (hints_cons _ _ _ (der_25028 v h) (hints_cons _ _ _ (der_25029 v h) (hints_cons _ _ _ (der_25030 v h) (hints_cons _ _ _ (der_25031 v h) (hints_cons _ _ _ (der_25032 v h) (hints_cons _ _ _ (der_25033 v h) (hints_cons _ _ _ (der_25034 v h) (hints_cons _ _ _ (der_25035 v h) (hints_cons _ _ _ (der_25036 v h) (hints_cons _ _ _ (der_25037 v h) (hints_cons _ _ _ (der_25038 v h) (hints_cons _ _ _ (der_25039 v h) (hints_cons _ _ _ (der_25040 v h) (hints_cons _ _ _ (der_25041 v h) (hints_cons _ _ _ (der_25042 v h) (hints_cons _ _ _ (der_25043 v h) (hints_cons _ _ _ (der_25044 v h) (hints_cons _ _ _ (der_25045 v h) (hints_cons _ _ _ (der_25046 v h) (hints_cons _ _ _ (der_25047 v h) (hints_cons _ _ _ (der_25048 v h) (hints_cons _ _ _ (der_25049 v h) (hints_cons _ _ _ (der_25050 v h) (hints_cons _ _ _ (der_25051 v h) (hints_cons _ _ _ (der_25052 v h) (hints_cons _ _ _ (der_25053 v h) (hints_cons _ _ _ (der_25054 v h) (hints_cons _ _ _ (der_25055 v h) (hints_cons _ _ _ (der_25056 v h) (hints_cons _ _ _ (der_25057 v h) (hints_cons _ _ _ (der_25058 v h) (hints_cons _ _ _ (der_25059 v h) (hints_cons _ _ _ (der_25060 v h) (hints_cons _ _ _ (der_25061 v h) (hints_cons _ _ _ (der_25062 v h) (hints_cons _ _ _ (der_25063 v h) (hints_cons _ _ _ (der_25064 v h) (hints_cons _ _ _ (der_25065 v h) (hints_cons _ _ _ (der_25066 v h) (hints_cons _ _ _ (der_25067 v h) (hints_cons _ _ _ (der_25068 v h) (hints_cons _ _ _ (der_25069 v h) (hints_cons _ _ _ (der_25070 v h) (hints_cons _ _ _ (der_25071 v h) (hints_cons _ _ _ (der_25072 v h) (hints_cons _ _ _ (der_25073 v h) (hints_cons _ _ _ (der_25074 v h) (hints_cons _ _ _ (der_25075 v h) (hints_cons _ _ _ (der_25076 v h) (hints_cons _ _ _ (der_25077 v h) (hints_cons _ _ _ (der_25078 v h) (hints_cons _ _ _ (der_25079 v h) (hints_cons _ _ _ (der_25080 v h) (hints_cons _ _ _ (der_25081 v h) (hints_cons _ _ _ (der_25082 v h) (hints_cons _ _ _ (der_25083 v h) (hints_cons _ _ _ (der_25084 v h) (hints_cons _ _ _ (der_25085 v h) (hints_cons _ _ _ (der_25087 v h) (hints_cons _ _ _ (der_25088 v h) (hints_cons _ _ _ (der_25091 v h) (hints_cons _ _ _ (der_25092 v h) (hints_cons _ _ _ (der_25093 v h) (hints_cons _ _ _ (der_25094 v h) (hints_cons _ _ _ (der_25095 v h) (hints_cons _ _ _ (der_25099 v h) (hints_cons _ _ _ (der_25101 v h) (hints_cons _ _ _ (der_25103 v h) (hints_cons _ _ _ (der_25104 v h) (hints_cons _ _ _ (der_25105 v h) (hints_cons _ _ _ (der_25106 v h) (hints_cons _ _ _ (der_25107 v h) (hints_cons _ _ _ (der_25108 v h) (hints_cons _ _ _ (der_25109 v h) (hints_cons _ _ _ (der_25110 v h) (hints_cons _ _ _ (der_25111 v h) (hints_cons _ _ _ (der_25112 v h) (hints_cons _ _ _ (der_25113 v h) (hints_cons _ _ _ (der_25115 v h) (hints_cons _ _ _ (der_25116 v h) (hints_cons _ _ _ (der_25117 v h) (hints_cons _ _ _ (der_25118 v h) (hints_cons _ _ _ (der_25119 v h) (hints_cons _ _ _ (der_25120 v h) (hints_cons _ _ _ (der_25121 v h) (hints_cons _ _ _ (der_25122 v h) (hints_cons _ _ _ (der_25123 v h) (hints_cons _ _ _ (der_25124 v h) (hints_cons _ _ _ (der_25125 v h) (hints_cons _ _ _ (der_25126 v h) (hints_cons _ _ _ (der_25127 v h) (hints_cons _ _ _ (der_25128 v h) (hints_cons _ _ _ (der_25129 v h) (hints_cons _ _ _ (der_25131 v h) (hints_cons _ _ _ (der_25132 v h) (hints_cons _ _ _ (der_25134 v h) (hints_cons _ _ _ (der_25135 v h) (hints_cons _ _ _ (der_25136 v h) (hints_cons _ _ _ (der_25137 v h) (hints_cons _ _ _ (der_25138 v h) (hints_cons _ _ _ (der_25139 v h) (hints_cons _ _ _ (der_25140 v h) (hints_cons _ _ _ (der_25141 v h) (hints_cons _ _ _ (der_25142 v h) (hints_cons _ _ _ (der_25143 v h) (hints_cons _ _ _ (der_25144 v h) (hints_cons _ _ _ (der_25146 v h) (hints_cons _ _ _ (der_25147 v h) (hints_cons _ _ _ (der_25148 v h) (hints_cons _ _ _ (der_25150 v h) (hints_cons _ _ _ (der_25151 v h) (hints_cons _ _ _ (der_25154 v h) (hints_cons _ _ _ (der_25155 v h) (hints_cons _ _ _ (der_25156 v h) (hints_cons _ _ _ (der_25158 v h) (hints_cons _ _ _ (der_25159 v h) (hints_cons _ _ _ (der_25160 v h) (hints_cons _ _ _ (der_25162 v h) (hints_cons _ _ _ (der_25165 v h) (hints_cons _ _ _ (der_25166 v h) (hints_cons _ _ _ (der_25167 v h) (hints_cons _ _ _ (der_25168 v h) (hints_cons _ _ _ (der_25169 v h) (hints_cons _ _ _ (der_25170 v h) (hints_cons _ _ _ (der_25171 v h) (hints_cons _ _ _ (der_25172 v h) (hints_cons _ _ _ (der_25173 v h) (hints_cons _ _ _ (der_25174 v h) (hints_cons _ _ _ (der_25175 v h) (hints_cons _ _ _ (der_25176 v h) (hints_cons _ _ _ (der_25177 v h) (hints_cons _ _ _ (der_25178 v h) (hints_cons _ _ _ (der_25179 v h) (hints_cons _ _ _ (der_25181 v h) (hints_cons _ _ _ (der_25182 v h) (hints_cons _ _ _ (der_25183 v h) (hints_cons _ _ _ (der_25184 v h) (hints_cons _ _ _ (der_25185 v h) (hints_cons _ _ _ (der_25186 v h) (hints_cons _ _ _ (der_25187 v h) (hints_cons _ _ _ (der_25188 v h) (hints_cons _ _ _ (der_25189 v h) (hints_cons _ _ _ (der_25190 v h) (hints_cons _ _ _ (der_25191 v h) (hints_cons _ _ _ (der_25192 v h) (hints_cons _ _ _ (der_25193 v h) (hints_cons _ _ _ (der_25194 v h) (hints_cons _ _ _ (der_25195 v h) (hints_cons _ _ _ (der_25196 v h) (hints_cons _ _ _ (der_25197 v h) (hints_cons _ _ _ (der_25198 v h) (hints_cons _ _ _ (der_25199 v h) (hints_cons _ _ _ (der_25200 v h) (hints_cons _ _ _ (der_25201 v h) (hints_cons _ _ _ (der_25202 v h) (hints_cons _ _ _ (der_25203 v h) (by intro d hd; cases hd)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def prefix005 := prefix004 ++ chunk005
theorem prefix_sound005 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : ∀ c ∈ prefix005, CNF.Holds (v ∘ decodeVar) c := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact prefix_sound004 v h c hc
  · exact chunk_sound005 v h c hc
end Percolation.NReplay
