import NReplay002
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_23670 : CNF.NClause := [(113,true),(39,false),(37,false),(38,true),(36,false),(61,false)]
theorem der_23670 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23670 :=
  CNF.rup_sound cl_23670 [cl_3285,cl_3269] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3285 v h) (hints_cons _ _ _ (inp_3269 v h) (by intro d hd; cases hd)))
def cl_23671 : CNF.NClause := [(113,true),(36,false),(38,true),(39,true),(37,false),(61,true)]
theorem der_23671 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23671 :=
  CNF.rup_sound cl_23671 [cl_3325,cl_3309] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3325 v h) (hints_cons _ _ _ (inp_3309 v h) (by intro d hd; cases hd)))
def cl_23672 : CNF.NClause := [(113,true),(61,false),(37,false),(39,false),(40,false),(36,false)]
theorem der_23672 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23672 :=
  CNF.rup_sound cl_23672 [cl_3265,cl_3269] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3265 v h) (hints_cons _ _ _ (inp_3269 v h) (by intro d hd; cases hd)))
def cl_23673 : CNF.NClause := [(113,true),(61,false),(37,false),(38,false),(40,false),(36,false)]
theorem der_23673 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23673 :=
  CNF.rup_sound cl_23673 [cl_3273,cl_23672] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3273 v h) (hints_cons _ _ _ (der_23672 v h) (by intro d hd; cases hd)))
def cl_23674 : CNF.NClause := [(113,true),(61,false),(37,false),(38,true),(40,false),(36,false)]
theorem der_23674 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23674 :=
  CNF.rup_sound cl_23674 [cl_3277,cl_3269] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3277 v h) (hints_cons _ _ _ (inp_3269 v h) (by intro d hd; cases hd)))
def cl_23675 : CNF.NClause := [(113,true),(61,false),(37,false),(38,false),(39,false),(36,false)]
theorem der_23675 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23675 :=
  CNF.rup_sound cl_23675 [cl_3281,cl_23673] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3281 v h) (hints_cons _ _ _ (der_23673 v h) (by intro d hd; cases hd)))
def cl_23676 : CNF.NClause := [(113,true),(61,false),(37,false),(38,false),(40,true),(36,false)]
theorem der_23676 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23676 :=
  CNF.rup_sound cl_23676 [cl_3289,cl_23675] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3289 v h) (hints_cons _ _ _ (der_23675 v h) (by intro d hd; cases hd)))
def cl_23677 : CNF.NClause := [(113,true),(61,false),(37,false),(38,true),(39,true),(36,false)]
theorem der_23677 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23677 :=
  CNF.rup_sound cl_23677 [cl_3293,cl_23674] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3293 v h) (hints_cons _ _ _ (der_23674 v h) (by intro d hd; cases hd)))
def cl_23678 : CNF.NClause := [(73,false),(18,true),(28,true),(10,true),(4,true),(21,true)]
theorem der_23678 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23678 :=
  CNF.rup_sound cl_23678 [cl_768,cl_766] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_768 v h) (hints_cons _ _ _ (inp_766 v h) (by intro d hd; cases hd)))
def cl_23679 : CNF.NClause := [(71,false),(13,true),(1,true),(20,true),(7,true),(19,true)]
theorem der_23679 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23679 :=
  CNF.rup_sound cl_23679 [cl_640,cl_608] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_640 v h) (hints_cons _ _ _ (inp_608 v h) (by intro d hd; cases hd)))
def cl_23680 : CNF.NClause := [(31,false),(90,false),(91,false),(89,false),(88,false),(87,false)]
theorem der_23680 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23680 :=
  CNF.rup_sound cl_23680 [cl_15457,cl_15425] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15457 v h) (hints_cons _ _ _ (der_15425 v h) (by intro d hd; cases hd)))
def cl_23681 : CNF.NClause := [(81,false),(15,true),(1,true),(12,true),(9,true),(23,true)]
theorem der_23681 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23681 :=
  CNF.rup_sound cl_23681 [cl_1280,cl_1248] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1280 v h) (hints_cons _ _ _ (inp_1248 v h) (by intro d hd; cases hd)))
def cl_23682 : CNF.NClause := [(75,false),(16,true),(3,true),(10,true),(26,true),(22,true)]
theorem der_23682 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23682 :=
  CNF.rup_sound cl_23682 [cl_896,cl_894] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_896 v h) (hints_cons _ _ _ (inp_894 v h) (by intro d hd; cases hd)))
def cl_23683 : CNF.NClause := [(61,false),(82,true),(67,false),(62,false),(72,false),(77,true)]
theorem der_23683 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23683 :=
  CNF.rup_sound cl_23683 [cl_15609,cl_15577] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15609 v h) (hints_cons _ _ _ (der_15577 v h) (by intro d hd; cases hd)))
def cl_23684 : CNF.NClause := [(61,false),(82,true),(67,false),(72,false),(77,true),(87,false)]
theorem der_23684 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23684 :=
  CNF.rup_sound cl_23684 [cl_15578,cl_15577] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15578 v h) (hints_cons _ _ _ (der_15577 v h) (by intro d hd; cases hd)))
def cl_23685 : CNF.NClause := [(61,false),(72,false),(62,true),(87,true),(82,false),(67,false)]
theorem der_23685 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23685 :=
  CNF.rup_sound cl_23685 [cl_15594,cl_15586] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15594 v h) (hints_cons _ _ _ (der_15586 v h) (by intro d hd; cases hd)))
def cl_23686 : CNF.NClause := [(61,false),(82,true),(67,false),(72,false),(77,true),(87,true)]
theorem der_23686 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23686 :=
  CNF.rup_sound cl_23686 [cl_15610,cl_23683] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15610 v h) (hints_cons _ _ _ (der_23683 v h) (by intro d hd; cases hd)))
def cl_23687 : CNF.NClause := [(61,false),(67,false),(82,false),(62,true),(72,false),(77,false)]
theorem der_23687 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23687 :=
  CNF.rup_sound cl_23687 [cl_15554,cl_15586] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15554 v h) (hints_cons _ _ _ (der_15586 v h) (by intro d hd; cases hd)))
def cl_23688 : CNF.NClause := [(69,false),(11,true),(27,true),(2,true),(18,true),(20,true)]
theorem der_23688 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23688 :=
  CNF.rup_sound cl_23688 [cl_512,cl_510] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_512 v h) (hints_cons _ _ _ (inp_510 v h) (by intro d hd; cases hd)))
def cl_23689 : CNF.NClause := [(61,false),(67,false),(82,false),(77,false),(72,false),(87,false)]
theorem der_23689 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23689 :=
  CNF.rup_sound cl_23689 [cl_15553,cl_23687] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15553 v h) (hints_cons _ _ _ (der_23687 v h) (by intro d hd; cases hd)))
def cl_23690 : CNF.NClause := [(61,false),(77,true),(87,false),(62,false),(72,false),(67,false)]
theorem der_23690 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23690 :=
  CNF.rup_sound cl_23690 [cl_15561,cl_15577] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15561 v h) (hints_cons _ _ _ (der_15577 v h) (by intro d hd; cases hd)))
def cl_23691 : CNF.NClause := [(108,true),(61,false),(46,false),(49,false),(50,false),(47,true)]
theorem der_23691 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23691 :=
  CNF.rup_sound cl_23691 [cl_2951,cl_2947] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2951 v h) (hints_cons _ _ _ (inp_2947 v h) (by intro d hd; cases hd)))
def cl_23692 : CNF.NClause := [(108,true),(61,false),(46,false),(48,false),(50,false),(47,true)]
theorem der_23692 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23692 :=
  CNF.rup_sound cl_23692 [cl_2955,cl_2947] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2955 v h) (hints_cons _ _ _ (inp_2947 v h) (by intro d hd; cases hd)))
def cl_23693 : CNF.NClause := [(108,true),(61,false),(46,false),(48,true),(50,false),(47,true)]
theorem der_23693 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23693 :=
  CNF.rup_sound cl_23693 [cl_2959,cl_23691] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2959 v h) (hints_cons _ _ _ (der_23691 v h) (by intro d hd; cases hd)))
def cl_23694 : CNF.NClause := [(108,true),(61,false),(46,false),(48,false),(49,false),(47,true)]
theorem der_23694 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23694 :=
  CNF.rup_sound cl_23694 [cl_2963,cl_2947] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2963 v h) (hints_cons _ _ _ (inp_2947 v h) (by intro d hd; cases hd)))
def cl_23695 : CNF.NClause := [(108,true),(61,false),(46,false),(48,true),(49,false),(47,true)]
theorem der_23695 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23695 :=
  CNF.rup_sound cl_23695 [cl_2967,cl_23691] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2967 v h) (hints_cons _ _ _ (der_23691 v h) (by intro d hd; cases hd)))
def cl_23696 : CNF.NClause := [(108,true),(61,false),(46,false),(48,false),(49,true),(47,true)]
theorem der_23696 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23696 :=
  CNF.rup_sound cl_23696 [cl_2971,cl_23692] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2971 v h) (hints_cons _ _ _ (der_23692 v h) (by intro d hd; cases hd)))
def cl_23697 : CNF.NClause := [(108,true),(61,false),(46,false),(48,true),(49,true),(47,true)]
theorem der_23697 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23697 :=
  CNF.rup_sound cl_23697 [cl_2975,cl_23693] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2975 v h) (hints_cons _ _ _ (der_23693 v h) (by intro d hd; cases hd)))
def cl_23698 : CNF.NClause := [(115,true),(33,false),(47,true),(44,false),(36,false),(55,true)]
theorem der_23698 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23698 :=
  CNF.rup_sound cl_23698 [cl_3449,cl_3417] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3449 v h) (hints_cons _ _ _ (inp_3417 v h) (by intro d hd; cases hd)))
def cl_23699 : CNF.NClause := [(103,true),(41,false),(42,true),(45,true),(44,false),(43,false)]
theorem der_23699 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23699 :=
  CNF.rup_sound cl_23699 [cl_2675,cl_2643] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2675 v h) (hints_cons _ _ _ (inp_2643 v h) (by intro d hd; cases hd)))
def cl_23700 : CNF.NClause := [(94,true),(56,false),(35,false),(50,false),(55,true),(45,true)]
theorem der_23700 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23700 :=
  CNF.rup_sound cl_23700 [cl_2071,cl_2069] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2071 v h) (hints_cons _ _ _ (inp_2069 v h) (by intro d hd; cases hd)))
def cl_23701 : CNF.NClause := [(94,true),(56,false),(40,false),(35,false),(55,true),(45,true)]
theorem der_23701 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23701 :=
  CNF.rup_sound cl_23701 [cl_2077,cl_2069] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2077 v h) (hints_cons _ _ _ (inp_2069 v h) (by intro d hd; cases hd)))
def cl_23702 : CNF.NClause := [(94,true),(56,false),(40,true),(35,false),(55,true),(45,true)]
theorem der_23702 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23702 :=
  CNF.rup_sound cl_23702 [cl_2079,cl_23700] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2079 v h) (hints_cons _ _ _ (der_23700 v h) (by intro d hd; cases hd)))
def cl_23703 : CNF.NClause := [(120,true),(31,true),(45,true),(47,true),(38,false),(58,false)]
theorem der_23703 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23703 :=
  CNF.rup_sound cl_23703 [cl_3742,cl_3726] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3742 v h) (hints_cons _ _ _ (inp_3726 v h) (by intro d hd; cases hd)))
def cl_23704 : CNF.NClause := [(120,true),(38,false),(31,true),(45,true),(47,true),(54,false)]
theorem der_23704 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23704 :=
  CNF.rup_sound cl_23704 [cl_3758,cl_3726] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3758 v h) (hints_cons _ _ _ (inp_3726 v h) (by intro d hd; cases hd)))
def cl_23705 : CNF.NClause := [(120,true),(38,false),(31,true),(45,true),(47,false),(54,true)]
theorem der_23705 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23705 :=
  CNF.rup_sound cl_23705 [cl_3766,cl_3734] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3766 v h) (hints_cons _ _ _ (inp_3734 v h) (by intro d hd; cases hd)))
def cl_23706 : CNF.NClause := [(120,true),(58,false),(31,true),(45,true),(54,false),(47,true)]
theorem der_23706 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23706 :=
  CNF.rup_sound cl_23706 [cl_3728,cl_3726] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3728 v h) (hints_cons _ _ _ (inp_3726 v h) (by intro d hd; cases hd)))
def cl_23707 : CNF.NClause := [(120,true),(54,true),(45,true),(47,false),(31,true),(58,false)]
theorem der_23707 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23707 :=
  CNF.rup_sound cl_23707 [cl_3736,cl_23705] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3736 v h) (hints_cons _ _ _ (der_23705 v h) (by intro d hd; cases hd)))
def cl_23708 : CNF.NClause := [(120,true),(54,true),(38,true),(45,false),(58,false),(31,true)]
theorem der_23708 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23708 :=
  CNF.rup_sound cl_23708 [cl_3740,cl_3732] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3740 v h) (hints_cons _ _ _ (inp_3732 v h) (by intro d hd; cases hd)))
def cl_23709 : CNF.NClause := [(120,true),(54,false),(47,false),(31,true),(45,true),(58,true)]
theorem der_23709 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23709 :=
  CNF.rup_sound cl_23709 [cl_3752,cl_3750] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3752 v h) (hints_cons _ _ _ (inp_3750 v h) (by intro d hd; cases hd)))
def cl_23710 : CNF.NClause := [(120,true),(54,false),(38,true),(45,false),(31,true),(58,true)]
theorem der_23710 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23710 :=
  CNF.rup_sound cl_23710 [cl_3756,cl_3748] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3756 v h) (hints_cons _ _ _ (inp_3748 v h) (by intro d hd; cases hd)))
def cl_23711 : CNF.NClause := [(120,true),(47,false),(38,true),(45,false),(31,true),(54,true)]
theorem der_23711 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23711 :=
  CNF.rup_sound cl_23711 [cl_3764,cl_23708] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3764 v h) (hints_cons _ _ _ (der_23708 v h) (by intro d hd; cases hd)))
def cl_23712 : CNF.NClause := [(120,false),(54,true),(38,true),(45,true),(31,true),(47,true)]
theorem der_23712 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23712 :=
  CNF.rup_sound cl_23712 [cl_3776,cl_3744] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3776 v h) (hints_cons _ _ _ (inp_3744 v h) (by intro d hd; cases hd)))
def cl_23713 : CNF.NClause := [(120,true),(38,true),(45,false),(47,true),(31,true),(58,false)]
theorem der_23713 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23713 :=
  CNF.rup_sound cl_23713 [cl_3724,cl_23708] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3724 v h) (hints_cons _ _ _ (der_23708 v h) (by intro d hd; cases hd)))
def cl_23714 : CNF.NClause := [(120,true),(31,true),(45,true),(38,false),(54,false),(58,false)]
theorem der_23714 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23714 :=
  CNF.rup_sound cl_23714 [cl_3718,cl_3726] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3718 v h) (hints_cons _ _ _ (inp_3726 v h) (by intro d hd; cases hd)))
def cl_23715 : CNF.NClause := [(113,true),(38,false),(39,false),(37,false),(36,false),(40,false)]
theorem der_23715 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23715 :=
  CNF.rup_sound cl_23715 [cl_3297,cl_23675] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3297 v h) (hints_cons _ _ _ (der_23675 v h) (by intro d hd; cases hd)))
def cl_23716 : CNF.NClause := [(113,true),(40,false),(39,false),(37,false),(36,false),(38,true)]
theorem der_23716 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23716 :=
  CNF.rup_sound cl_23716 [cl_3301,cl_3269] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3301 v h) (hints_cons _ _ _ (inp_3269 v h) (by intro d hd; cases hd)))
def cl_23717 : CNF.NClause := [(111,true),(55,false),(34,false),(46,false),(60,false),(42,false)]
theorem der_23717 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23717 :=
  CNF.rup_sound cl_23717 [cl_3137,cl_3139] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3137 v h) (hints_cons _ _ _ (inp_3139 v h) (by intro d hd; cases hd)))
def cl_23718 : CNF.NClause := [(111,true),(34,false),(38,true),(46,false),(55,false),(60,false)]
theorem der_23718 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23718 :=
  CNF.rup_sound cl_23718 [cl_3143,cl_3139] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3143 v h) (hints_cons _ _ _ (inp_3139 v h) (by intro d hd; cases hd)))
def cl_23719 : CNF.NClause := [(111,true),(55,false),(46,false),(34,false),(38,true),(42,false)]
theorem der_23719 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23719 :=
  CNF.rup_sound cl_23719 [cl_3171,cl_3139] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3171 v h) (hints_cons _ _ _ (inp_3139 v h) (by intro d hd; cases hd)))
def cl_23720 : CNF.NClause := [(111,true),(34,false),(42,false),(46,true),(55,true),(60,false)]
theorem der_23720 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23720 :=
  CNF.rup_sound cl_23720 [cl_3163,cl_3161] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3163 v h) (hints_cons _ _ _ (inp_3161 v h) (by intro d hd; cases hd)))
def cl_23721 : CNF.NClause := [(111,true),(38,false),(42,false),(34,false),(46,true),(55,true)]
theorem der_23721 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23721 :=
  CNF.rup_sound cl_23721 [cl_3193,cl_3161] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3193 v h) (hints_cons _ _ _ (inp_3161 v h) (by intro d hd; cases hd)))
def cl_23722 : CNF.NClause := [(111,true),(42,false),(38,true),(34,false),(55,false),(60,true)]
theorem der_23722 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23722 :=
  CNF.rup_sound cl_23722 [cl_3179,cl_23719] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3179 v h) (hints_cons _ _ _ (der_23719 v h) (by intro d hd; cases hd)))
def cl_23723 : CNF.NClause := [(111,true),(42,false),(38,true),(34,false),(55,false),(60,false)]
theorem der_23723 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23723 :=
  CNF.rup_sound cl_23723 [cl_3147,cl_3139] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3147 v h) (hints_cons _ _ _ (inp_3139 v h) (by intro d hd; cases hd)))
def cl_23724 : CNF.NClause := [(111,true),(34,false),(38,true),(42,true),(55,false),(60,false)]
theorem der_23724 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23724 :=
  CNF.rup_sound cl_23724 [cl_3151,cl_23718] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3151 v h) (hints_cons _ _ _ (der_23718 v h) (by intro d hd; cases hd)))
def cl_23725 : CNF.NClause := [(111,true),(34,false),(38,true),(42,true),(46,false),(60,false)]
theorem der_23725 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23725 :=
  CNF.rup_sound cl_23725 [cl_3159,cl_23718] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3159 v h) (hints_cons _ _ _ (der_23718 v h) (by intro d hd; cases hd)))
def cl_23726 : CNF.NClause := [(111,true),(34,false),(38,true),(42,true),(55,true),(60,false)]
theorem der_23726 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23726 :=
  CNF.rup_sound cl_23726 [cl_3167,cl_23725] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3167 v h) (hints_cons _ _ _ (der_23725 v h) (by intro d hd; cases hd)))
def cl_23727 : CNF.NClause := [(111,true),(34,false),(38,true),(42,true),(46,false),(55,true)]
theorem der_23727 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23727 :=
  CNF.rup_sound cl_23727 [cl_3191,cl_23725] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3191 v h) (hints_cons _ _ _ (der_23725 v h) (by intro d hd; cases hd)))
def cl_23728 : CNF.NClause := [(111,true),(34,false),(42,false),(46,true),(55,true),(60,true)]
theorem der_23728 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23728 :=
  CNF.rup_sound cl_23728 [cl_3195,cl_23721] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3195 v h) (hints_cons _ _ _ (der_23721 v h) (by intro d hd; cases hd)))
def cl_23729 : CNF.NClause := [(98,true),(53,true),(52,false),(51,false),(55,false),(61,false)]
theorem der_23729 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23729 :=
  CNF.rup_sound cl_23729 [cl_2317,cl_2309] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2317 v h) (hints_cons _ _ _ (inp_2309 v h) (by intro d hd; cases hd)))
def cl_23730 : CNF.NClause := [(98,true),(53,true),(52,false),(51,false),(54,false),(61,false)]
theorem der_23730 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23730 :=
  CNF.rup_sound cl_23730 [cl_2325,cl_2309] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2325 v h) (hints_cons _ _ _ (inp_2309 v h) (by intro d hd; cases hd)))
def cl_23731 : CNF.NClause := [(98,true),(53,true),(52,false),(51,false),(54,true),(61,false)]
theorem der_23731 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23731 :=
  CNF.rup_sound cl_23731 [cl_2333,cl_23729] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2333 v h) (hints_cons _ _ _ (der_23729 v h) (by intro d hd; cases hd)))
def cl_23732 : CNF.NClause := [(98,true),(51,false),(55,false),(52,false),(54,false),(53,true)]
theorem der_23732 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23732 :=
  CNF.rup_sound cl_23732 [cl_2341,cl_2309] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2341 v h) (hints_cons _ _ _ (inp_2309 v h) (by intro d hd; cases hd)))
def cl_23733 : CNF.NClause := [(98,true),(53,true),(51,false),(52,false),(55,false),(61,true)]
theorem der_23733 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23733 :=
  CNF.rup_sound cl_23733 [cl_2349,cl_23732] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2349 v h) (hints_cons _ _ _ (der_23732 v h) (by intro d hd; cases hd)))
def cl_23734 : CNF.NClause := [(98,true),(51,false),(52,false),(54,false),(53,true),(61,true)]
theorem der_23734 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23734 :=
  CNF.rup_sound cl_23734 [cl_2357,cl_23732] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2357 v h) (hints_cons _ _ _ (der_23732 v h) (by intro d hd; cases hd)))
def cl_23735 : CNF.NClause := [(98,true),(53,true),(51,false),(52,false),(54,true),(55,true)]
theorem der_23735 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23735 :=
  CNF.rup_sound cl_23735 [cl_2365,cl_23731] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2365 v h) (hints_cons _ _ _ (der_23731 v h) (by intro d hd; cases hd)))
def cl_23736 : CNF.NClause := [(106,true),(34,false),(40,false),(41,false),(47,false),(57,false)]
theorem der_23736 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23736 :=
  CNF.rup_sound cl_23736 [cl_2833,cl_2817] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2833 v h) (hints_cons _ _ _ (inp_2817 v h) (by intro d hd; cases hd)))
def cl_23737 : CNF.NClause := [(106,true),(34,false),(41,false),(47,false),(53,true),(57,false)]
theorem der_23737 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23737 :=
  CNF.rup_sound cl_23737 [cl_2835,cl_23736] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2835 v h) (hints_cons _ _ _ (der_23736 v h) (by intro d hd; cases hd)))
def cl_23738 : CNF.NClause := [(106,true),(41,false),(53,true),(40,false),(47,false),(34,false)]
theorem der_23738 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23738 :=
  CNF.rup_sound cl_23738 [cl_2865,cl_23737] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2865 v h) (hints_cons _ _ _ (der_23737 v h) (by intro d hd; cases hd)))
def cl_23739 : CNF.NClause := [(106,true),(41,false),(40,true),(53,true),(47,false),(34,false)]
theorem der_23739 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23739 :=
  CNF.rup_sound cl_23739 [cl_2867,cl_23737] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2867 v h) (hints_cons _ _ _ (der_23737 v h) (by intro d hd; cases hd)))
def cl_23740 : CNF.NClause := [(117,true),(53,true),(32,false),(45,false),(36,false),(49,false)]
theorem der_23740 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23740 :=
  CNF.rup_sound cl_23740 [cl_3569,cl_3537] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3569 v h) (hints_cons _ _ _ (inp_3537 v h) (by intro d hd; cases hd)))
def cl_23741 : CNF.NClause := [(109,true),(53,true),(37,false),(35,false),(46,false),(44,false)]
theorem der_23741 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23741 :=
  CNF.rup_sound cl_23741 [cl_3057,cl_3025] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3057 v h) (hints_cons _ _ _ (inp_3025 v h) (by intro d hd; cases hd)))
def cl_23742 : CNF.NClause := [(121,true),(50,false),(53,true),(31,true),(42,false),(59,false)]
theorem der_23742 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23742 :=
  CNF.rup_sound cl_23742 [cl_3796,cl_3794] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3796 v h) (hints_cons _ _ _ (inp_3794 v h) (by intro d hd; cases hd)))
def cl_23743 : CNF.NClause := [(121,true),(50,false),(39,true),(31,true),(53,true),(59,false)]
theorem der_23743 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23743 :=
  CNF.rup_sound cl_23743 [cl_3800,cl_23742] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3800 v h) (hints_cons _ _ _ (der_23742 v h) (by intro d hd; cases hd)))
def cl_23744 : CNF.NClause := [(121,true),(53,true),(39,false),(42,false),(31,true),(50,false)]
theorem der_23744 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23744 :=
  CNF.rup_sound cl_23744 [cl_3826,cl_3794] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3826 v h) (hints_cons _ _ _ (inp_3794 v h) (by intro d hd; cases hd)))
def cl_23745 : CNF.NClause := [(121,true),(50,false),(53,true),(31,true),(42,false),(59,true)]
theorem der_23745 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23745 :=
  CNF.rup_sound cl_23745 [cl_3828,cl_23744] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3828 v h) (hints_cons _ _ _ (der_23744 v h) (by intro d hd; cases hd)))
def cl_23746 : CNF.NClause := [(109,true),(53,true),(37,false),(35,false),(44,false),(58,false)]
theorem der_23746 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23746 :=
  CNF.rup_sound cl_23746 [cl_3033,cl_3025] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3033 v h) (hints_cons _ _ _ (inp_3025 v h) (by intro d hd; cases hd)))
def cl_23747 : CNF.NClause := [(109,true),(53,true),(37,false),(35,false),(44,false),(46,true)]
theorem der_23747 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23747 :=
  CNF.rup_sound cl_23747 [cl_3065,cl_23746] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3065 v h) (hints_cons _ _ _ (der_23746 v h) (by intro d hd; cases hd)))
def cl_23748 : CNF.NClause := [(106,true),(41,false),(40,true),(53,true),(57,false),(34,false)]
theorem der_23748 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23748 :=
  CNF.rup_sound cl_23748 [cl_2843,cl_23737] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2843 v h) (hints_cons _ _ _ (der_23737 v h) (by intro d hd; cases hd)))
def cl_23749 : CNF.NClause := [(106,true),(34,false),(40,true),(53,true),(41,false),(57,true)]
theorem der_23749 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23749 :=
  CNF.rup_sound cl_23749 [cl_2875,cl_23739] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2875 v h) (hints_cons _ _ _ (der_23739 v h) (by intro d hd; cases hd)))
def cl_23750 : CNF.NClause := [(106,true),(41,false),(53,true),(40,false),(34,false),(57,false)]
theorem der_23750 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23750 :=
  CNF.rup_sound cl_23750 [cl_2841,cl_23737] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2841 v h) (hints_cons _ _ _ (der_23737 v h) (by intro d hd; cases hd)))
def cl_23751 : CNF.NClause := [(106,true),(41,false),(53,true),(40,false),(34,false),(47,true)]
theorem der_23751 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23751 :=
  CNF.rup_sound cl_23751 [cl_2873,cl_23750] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2873 v h) (hints_cons _ _ _ (der_23750 v h) (by intro d hd; cases hd)))
def cl_23752 : CNF.NClause := [(117,true),(53,true),(32,false),(45,false),(36,false),(60,false)]
theorem der_23752 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23752 :=
  CNF.rup_sound cl_23752 [cl_3545,cl_3537] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3545 v h) (hints_cons _ _ _ (inp_3537 v h) (by intro d hd; cases hd)))
def cl_23753 : CNF.NClause := [(117,true),(53,true),(32,false),(45,false),(36,false),(49,true)]
theorem der_23753 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23753 :=
  CNF.rup_sound cl_23753 [cl_3577,cl_23752] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3577 v h) (hints_cons _ _ _ (der_23752 v h) (by intro d hd; cases hd)))
def cl_23754 : CNF.NClause := [(117,true),(32,false),(53,true),(36,false),(49,true),(60,false)]
theorem der_23754 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23754 :=
  CNF.rup_sound cl_23754 [cl_3549,cl_23752] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3549 v h) (hints_cons _ _ _ (der_23752 v h) (by intro d hd; cases hd)))
def cl_23755 : CNF.NClause := [(117,true),(32,false),(53,true),(36,false),(49,true),(60,true)]
theorem der_23755 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23755 :=
  CNF.rup_sound cl_23755 [cl_3581,cl_23753] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3581 v h) (hints_cons _ _ _ (der_23753 v h) (by intro d hd; cases hd)))
def cl_23756 : CNF.NClause := [(98,true),(53,true),(51,false),(54,false),(55,false),(61,false)]
theorem der_23756 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23756 :=
  CNF.rup_sound cl_23756 [cl_2311,cl_2309] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2311 v h) (hints_cons _ _ _ (inp_2309 v h) (by intro d hd; cases hd)))
def cl_23757 : CNF.NClause := [(98,true),(53,true),(51,false),(54,true),(55,false),(61,false)]
theorem der_23757 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23757 :=
  CNF.rup_sound cl_23757 [cl_2319,cl_23729] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2319 v h) (hints_cons _ _ _ (der_23729 v h) (by intro d hd; cases hd)))
def cl_23758 : CNF.NClause := [(98,true),(53,true),(51,false),(54,false),(55,true),(61,false)]
theorem der_23758 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23758 :=
  CNF.rup_sound cl_23758 [cl_2327,cl_23730] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2327 v h) (hints_cons _ _ _ (der_23730 v h) (by intro d hd; cases hd)))
def cl_23759 : CNF.NClause := [(98,true),(53,true),(51,false),(52,true),(54,true),(61,false)]
theorem der_23759 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23759 :=
  CNF.rup_sound cl_23759 [cl_2335,cl_23757] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2335 v h) (hints_cons _ _ _ (der_23757 v h) (by intro d hd; cases hd)))
def cl_23760 : CNF.NClause := [(121,true),(53,true),(39,false),(42,false),(31,true),(59,false)]
theorem der_23760 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23760 :=
  CNF.rup_sound cl_23760 [cl_3802,cl_3794] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3802 v h) (hints_cons _ _ _ (inp_3794 v h) (by intro d hd; cases hd)))
def cl_23761 : CNF.NClause := [(121,true),(59,false),(39,true),(53,true),(31,true),(42,false)]
theorem der_23761 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23761 :=
  CNF.rup_sound cl_23761 [cl_3804,cl_23743] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3804 v h) (hints_cons _ _ _ (der_23743 v h) (by intro d hd; cases hd)))
def cl_23762 : CNF.NClause := [(121,true),(53,true),(39,false),(42,false),(31,true),(59,true)]
theorem der_23762 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23762 :=
  CNF.rup_sound cl_23762 [cl_3834,cl_23744] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3834 v h) (hints_cons _ _ _ (der_23744 v h) (by intro d hd; cases hd)))
def cl_23763 : CNF.NClause := [(121,false),(42,true),(53,true),(31,true),(39,true),(59,true)]
theorem der_23763 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23763 :=
  CNF.rup_sound cl_23763 [cl_3840,cl_3832] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3840 v h) (hints_cons _ _ _ (inp_3832 v h) (by intro d hd; cases hd)))
def cl_23764 : CNF.NClause := [(98,true),(55,false),(51,false),(54,false),(53,true),(61,true)]
theorem der_23764 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23764 :=
  CNF.rup_sound cl_23764 [cl_2343,cl_23732] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2343 v h) (hints_cons _ _ _ (der_23732 v h) (by intro d hd; cases hd)))
def cl_23765 : CNF.NClause := [(98,true),(53,true),(52,true),(51,false),(54,true),(55,false)]
theorem der_23765 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23765 :=
  CNF.rup_sound cl_23765 [cl_2351,cl_23757] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2351 v h) (hints_cons _ _ _ (der_23757 v h) (by intro d hd; cases hd)))
def cl_23766 : CNF.NClause := [(98,true),(51,false),(55,true),(54,false),(53,true),(61,true)]
theorem der_23766 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23766 :=
  CNF.rup_sound cl_23766 [cl_2359,cl_23734] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2359 v h) (hints_cons _ _ _ (der_23734 v h) (by intro d hd; cases hd)))
def cl_23767 : CNF.NClause := [(109,true),(53,true),(37,false),(35,false),(46,true),(58,false)]
theorem der_23767 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23767 :=
  CNF.rup_sound cl_23767 [cl_3037,cl_23746] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3037 v h) (hints_cons _ _ _ (der_23746 v h) (by intro d hd; cases hd)))
def cl_23768 : CNF.NClause := [(109,true),(53,true),(37,false),(35,false),(46,true),(58,true)]
theorem der_23768 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23768 :=
  CNF.rup_sound cl_23768 [cl_3069,cl_23747] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3069 v h) (hints_cons _ _ _ (der_23747 v h) (by intro d hd; cases hd)))
def cl_23769 : CNF.NClause := [(95,true),(33,false),(43,false),(48,false),(38,true),(56,true)]
theorem der_23769 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23769 :=
  CNF.rup_sound cl_23769 [cl_2163,cl_14710] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2163 v h) (hints_cons _ _ _ (der_14710 v h) (by intro d hd; cases hd)))
def cl_23770 : CNF.NClause := [(95,true),(33,false),(53,true),(43,false),(38,true),(56,true)]
theorem der_23770 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23770 :=
  CNF.rup_sound cl_23770 [cl_2171,cl_23769] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2171 v h) (hints_cons _ _ _ (der_23769 v h) (by intro d hd; cases hd)))
def cl_23771 : CNF.NClause := [(80,false),(15,true),(3,true),(7,true),(11,true),(24,true)]
theorem der_23771 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23771 :=
  CNF.rup_sound cl_23771 [cl_1216,cl_1184] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1216 v h) (hints_cons _ _ _ (inp_1184 v h) (by intro d hd; cases hd)))
def cl_23772 : CNF.NClause := [(108,true),(47,true),(46,true),(48,false),(50,false),(61,true)]
theorem der_23772 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23772 :=
  CNF.rup_sound cl_23772 [cl_2988,cl_2980] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2988 v h) (hints_cons _ _ _ (inp_2980 v h) (by intro d hd; cases hd)))
def cl_23773 : CNF.NClause := [(108,true),(47,true),(49,false),(46,true),(48,false),(61,true)]
theorem der_23773 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23773 :=
  CNF.rup_sound cl_23773 [cl_2996,cl_23772] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2996 v h) (hints_cons _ _ _ (der_23772 v h) (by intro d hd; cases hd)))
def cl_23774 : CNF.NClause := [(119,true),(40,true),(31,true),(48,false),(52,false),(60,true)]
theorem der_23774 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23774 :=
  CNF.rup_sound cl_23774 [cl_3688,cl_3684] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3688 v h) (hints_cons _ _ _ (inp_3684 v h) (by intro d hd; cases hd)))
def cl_23775 : CNF.NClause := [(95,true),(38,false),(33,false),(48,false),(53,false),(43,false)]
theorem der_23775 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23775 :=
  CNF.rup_sound cl_23775 [cl_2113,cl_14710] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2113 v h) (hints_cons _ _ _ (der_14710 v h) (by intro d hd; cases hd)))
def cl_23776 : CNF.NClause := [(95,true),(56,false),(38,false),(33,false),(53,false),(43,false)]
theorem der_23776 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23776 :=
  CNF.rup_sound cl_23776 [cl_2121,cl_23775] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2121 v h) (hints_cons _ _ _ (der_23775 v h) (by intro d hd; cases hd)))
def cl_23777 : CNF.NClause := [(95,true),(56,false),(38,false),(33,false),(48,false),(43,false)]
theorem der_23777 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23777 :=
  CNF.rup_sound cl_23777 [cl_2129,cl_23775] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2129 v h) (hints_cons _ _ _ (der_23775 v h) (by intro d hd; cases hd)))
def cl_23778 : CNF.NClause := [(95,true),(56,false),(38,false),(33,false),(48,true),(43,false)]
theorem der_23778 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23778 :=
  CNF.rup_sound cl_23778 [cl_2137,cl_23776] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2137 v h) (hints_cons _ _ _ (der_23776 v h) (by intro d hd; cases hd)))
def cl_23779 : CNF.NClause := [(95,true),(38,false),(43,false),(33,false),(48,false),(56,true)]
theorem der_23779 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23779 :=
  CNF.rup_sound cl_23779 [cl_2161,cl_14710] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2161 v h) (hints_cons _ _ _ (der_14710 v h) (by intro d hd; cases hd)))
def cl_23780 : CNF.NClause := [(95,true),(38,false),(43,false),(33,false),(48,true),(56,true)]
theorem der_23780 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23780 :=
  CNF.rup_sound cl_23780 [cl_2169,cl_23274] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2169 v h) (hints_cons _ _ _ (der_23274 v h) (by intro d hd; cases hd)))
def cl_23781 : CNF.NClause := [(122,true),(49,true),(37,false),(31,true),(43,false),(55,true)]
theorem der_23781 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23781 :=
  CNF.rup_sound cl_23781 [cl_3898,cl_3866] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3898 v h) (hints_cons _ _ _ (inp_3866 v h) (by intro d hd; cases hd)))
def cl_23782 : CNF.NClause := [(95,true),(33,false),(38,true),(43,false),(48,false),(53,false)]
theorem der_23782 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23782 :=
  CNF.rup_sound cl_23782 [cl_2115,cl_14710] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2115 v h) (hints_cons _ _ _ (der_14710 v h) (by intro d hd; cases hd)))
def cl_23783 : CNF.NClause := [(95,true),(33,false),(38,true),(48,false),(53,false),(56,false)]
theorem der_23783 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23783 :=
  CNF.rup_sound cl_23783 [cl_2119,cl_23782] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2119 v h) (hints_cons _ _ _ (der_23782 v h) (by intro d hd; cases hd)))
def cl_23784 : CNF.NClause := [(95,true),(33,false),(38,true),(43,false),(53,false),(56,false)]
theorem der_23784 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23784 :=
  CNF.rup_sound cl_23784 [cl_2123,cl_23782] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2123 v h) (hints_cons _ _ _ (der_23782 v h) (by intro d hd; cases hd)))
def cl_23785 : CNF.NClause := [(95,true),(33,false),(38,true),(43,true),(53,false),(56,false)]
theorem der_23785 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23785 :=
  CNF.rup_sound cl_23785 [cl_2127,cl_23783] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2127 v h) (hints_cons _ _ _ (der_23783 v h) (by intro d hd; cases hd)))
def cl_23786 : CNF.NClause := [(95,true),(33,false),(38,true),(43,false),(48,false),(53,true)]
theorem der_23786 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23786 :=
  CNF.rup_sound cl_23786 [cl_2131,cl_23769] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2131 v h) (hints_cons _ _ _ (der_23769 v h) (by intro d hd; cases hd)))
def cl_23788 : CNF.NClause := [(95,true),(33,false),(38,true),(43,false),(48,true),(53,true)]
theorem der_23788 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23788 :=
  CNF.rup_sound cl_23788 [cl_2139,cl_23770] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2139 v h) (hints_cons _ _ _ (der_23770 v h) (by intro d hd; cases hd)))
def cl_23790 : CNF.NClause := [(112,true),(32,false),(59,false),(43,false),(54,false),(40,true)]
theorem der_23790 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23790 :=
  CNF.rup_sound cl_23790 [cl_3203,cl_3211] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3203 v h) (hints_cons _ _ _ (inp_3211 v h) (by intro d hd; cases hd)))
def cl_23791 : CNF.NClause := [(93,true),(59,false),(57,false),(58,false),(56,true),(60,true)]
theorem der_23791 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23791 :=
  CNF.rup_sound cl_23791 [cl_2034,cl_2002] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2034 v h) (hints_cons _ _ _ (inp_2002 v h) (by intro d hd; cases hd)))
def cl_23792 : CNF.NClause := [(121,true),(59,false),(42,false),(50,false),(31,true),(39,false)]
theorem der_23792 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23792 :=
  CNF.rup_sound cl_23792 [cl_3778,cl_3794] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3778 v h) (hints_cons _ _ _ (inp_3794 v h) (by intro d hd; cases hd)))
def cl_23793 : CNF.NClause := [(98,true),(52,true),(51,false),(54,false),(55,false),(61,false)]
theorem der_23793 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23793 :=
  CNF.rup_sound cl_23793 [cl_2307,cl_23756] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2307 v h) (hints_cons _ _ _ (der_23756 v h) (by intro d hd; cases hd)))
def cl_23794 : CNF.NClause := [(98,true),(52,true),(51,false),(54,true),(55,false),(61,false)]
theorem der_23794 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23794 :=
  CNF.rup_sound cl_23794 [cl_2315,cl_23757] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2315 v h) (hints_cons _ _ _ (der_23757 v h) (by intro d hd; cases hd)))
def cl_23795 : CNF.NClause := [(98,true),(52,true),(51,false),(53,false),(54,false),(61,false)]
theorem der_23795 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23795 :=
  CNF.rup_sound cl_23795 [cl_2323,cl_23793] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2323 v h) (hints_cons _ _ _ (der_23793 v h) (by intro d hd; cases hd)))
def cl_23796 : CNF.NClause := [(98,true),(52,true),(51,false),(54,true),(55,true),(61,false)]
theorem der_23796 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23796 :=
  CNF.rup_sound cl_23796 [cl_2331,cl_23759] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2331 v h) (hints_cons _ _ _ (der_23759 v h) (by intro d hd; cases hd)))
def cl_23797 : CNF.NClause := [(98,true),(52,true),(51,false),(53,false),(54,false),(55,false)]
theorem der_23797 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23797 :=
  CNF.rup_sound cl_23797 [cl_2339,cl_23793] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2339 v h) (hints_cons _ _ _ (der_23793 v h) (by intro d hd; cases hd)))
def cl_23798 : CNF.NClause := [(97,true),(32,false),(37,false),(42,false),(52,true),(56,true)]
theorem der_23798 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23798 :=
  CNF.rup_sound cl_23798 [cl_2297,cl_2289] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2297 v h) (hints_cons _ _ _ (inp_2289 v h) (by intro d hd; cases hd)))
def cl_23799 : CNF.NClause := [(110,true),(33,false),(52,true),(39,false),(46,false),(57,false)]
theorem der_23799 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23799 :=
  CNF.rup_sound cl_23799 [cl_3093,cl_3089] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3093 v h) (hints_cons _ _ _ (inp_3089 v h) (by intro d hd; cases hd)))
def cl_23800 : CNF.NClause := [(116,true),(43,false),(52,true),(34,false),(36,false),(50,false)]
theorem der_23800 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23800 :=
  CNF.rup_sound cl_23800 [cl_3505,cl_3473] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3505 v h) (hints_cons _ _ _ (inp_3473 v h) (by intro d hd; cases hd)))
def cl_23801 : CNF.NClause := [(119,false),(52,true),(40,true),(44,true),(31,true),(60,true)]
theorem der_23801 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23801 :=
  CNF.rup_sound cl_23801 [cl_3712,cl_3704] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3712 v h) (hints_cons _ _ _ (inp_3704 v h) (by intro d hd; cases hd)))
def cl_23802 : CNF.NClause := [(119,false),(48,true),(40,true),(44,true),(52,true),(31,true)]
theorem der_23802 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23802 :=
  CNF.rup_sound cl_23802 [cl_3680,cl_23801] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3680 v h) (hints_cons _ _ _ (der_23801 v h) (by intro d hd; cases hd)))
def cl_23803 : CNF.NClause := [(108,true),(49,true),(48,false),(46,false),(50,false),(61,false)]
theorem der_23803 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23803 :=
  CNF.rup_sound cl_23803 [cl_2953,cl_23696] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2953 v h) (hints_cons _ _ _ (der_23696 v h) (by intro d hd; cases hd)))
def cl_23804 : CNF.NClause := [(108,true),(49,true),(47,false),(48,false),(46,false),(61,false)]
theorem der_23804 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23804 :=
  CNF.rup_sound cl_23804 [cl_2969,cl_23803] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2969 v h) (hints_cons _ _ _ (der_23803 v h) (by intro d hd; cases hd)))
def cl_23805 : CNF.NClause := [(104,true),(49,true),(38,false),(41,false),(35,false),(52,false)]
theorem der_23805 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23805 :=
  CNF.rup_sound cl_23805 [cl_2729,cl_2697] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2729 v h) (hints_cons _ _ _ (inp_2697 v h) (by intro d hd; cases hd)))
def cl_23806 : CNF.NClause := [(104,true),(49,true),(38,false),(41,false),(35,false),(59,true)]
theorem der_23806 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23806 :=
  CNF.rup_sound cl_23806 [cl_2745,cl_23805] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2745 v h) (hints_cons _ _ _ (der_23805 v h) (by intro d hd; cases hd)))
def cl_23807 : CNF.NClause := [(96,true),(49,true),(44,false),(34,false),(54,true),(56,false)]
theorem der_23807 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23807 :=
  CNF.rup_sound cl_23807 [cl_2203,cl_2201] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2203 v h) (hints_cons _ _ _ (inp_2201 v h) (by intro d hd; cases hd)))
def cl_23808 : CNF.NClause := [(100,true),(49,true),(40,false),(33,false),(42,false),(51,false)]
theorem der_23808 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23808 :=
  CNF.rup_sound cl_23808 [cl_2473,cl_2441] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2473 v h) (hints_cons _ _ _ (inp_2441 v h) (by intro d hd; cases hd)))
def cl_23809 : CNF.NClause := [(96,true),(49,true),(34,false),(44,false),(39,false),(54,true)]
theorem der_23809 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23809 :=
  CNF.rup_sound cl_23809 [cl_2233,cl_2201] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2233 v h) (hints_cons _ _ _ (inp_2201 v h) (by intro d hd; cases hd)))
def cl_23810 : CNF.NClause := [(122,true),(49,true),(37,false),(31,true),(55,true),(57,false)]
theorem der_23810 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23810 :=
  CNF.rup_sound cl_23810 [cl_3870,cl_3866] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3870 v h) (hints_cons _ _ _ (inp_3866 v h) (by intro d hd; cases hd)))
def cl_23811 : CNF.NClause := [(122,false),(49,true),(37,true),(43,true),(31,true),(55,true)]
theorem der_23811 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23811 :=
  CNF.rup_sound cl_23811 [cl_3904,cl_3872] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3904 v h) (hints_cons _ _ _ (inp_3872 v h) (by intro d hd; cases hd)))
def cl_23812 : CNF.NClause := [(108,false),(49,true),(47,true),(46,true),(50,true),(61,true)]
theorem der_23812 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23812 :=
  CNF.rup_sound cl_23812 [cl_3008,cl_3004] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3008 v h) (hints_cons _ _ _ (inp_3004 v h) (by intro d hd; cases hd)))
def cl_23813 : CNF.NClause := [(104,true),(49,true),(38,false),(41,false),(35,false),(59,false)]
theorem der_23813 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23813 :=
  CNF.rup_sound cl_23813 [cl_2713,cl_2697] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2713 v h) (hints_cons _ _ _ (inp_2697 v h) (by intro d hd; cases hd)))
def cl_23814 : CNF.NClause := [(100,true),(49,true),(42,false),(51,false),(33,false),(58,false)]
theorem der_23814 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23814 :=
  CNF.rup_sound cl_23814 [cl_2443,cl_2441] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2443 v h) (hints_cons _ _ _ (inp_2441 v h) (by intro d hd; cases hd)))
def cl_23815 : CNF.NClause := [(117,true),(32,false),(36,false),(45,true),(49,true),(60,true)]
theorem der_23815 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23815 :=
  CNF.rup_sound cl_23815 [cl_3565,cl_23755] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3565 v h) (hints_cons _ _ _ (der_23755 v h) (by intro d hd; cases hd)))
def cl_23816 : CNF.NClause := [(122,true),(49,true),(37,false),(31,true),(57,false),(43,false)]
theorem der_23816 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23816 :=
  CNF.rup_sound cl_23816 [cl_3850,cl_3866] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3850 v h) (hints_cons _ _ _ (inp_3866 v h) (by intro d hd; cases hd)))
def cl_23817 : CNF.NClause := [(108,true),(49,true),(46,false),(48,true),(50,false),(47,true)]
theorem der_23817 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23817 :=
  CNF.rup_sound cl_23817 [cl_2991,cl_23697] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2991 v h) (hints_cons _ _ _ (der_23697 v h) (by intro d hd; cases hd)))
def cl_23818 : CNF.NClause := [(123,true),(41,false),(31,true),(51,false),(36,false),(56,true)]
theorem der_23818 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23818 :=
  CNF.rup_sound cl_23818 [cl_3938,cl_3946] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3938 v h) (hints_cons _ _ _ (inp_3946 v h) (by intro d hd; cases hd)))
def cl_23819 : CNF.NClause := [(106,true),(41,false),(40,true),(47,true),(57,false),(34,false)]
theorem der_23819 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23819 :=
  CNF.rup_sound cl_23819 [cl_2827,cl_23748] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2827 v h) (hints_cons _ _ _ (der_23748 v h) (by intro d hd; cases hd)))
def cl_23820 : CNF.NClause := [(106,true),(41,false),(40,false),(53,false),(34,false),(57,false)]
theorem der_23820 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23820 :=
  CNF.rup_sound cl_23820 [cl_2825,cl_2817] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2825 v h) (hints_cons _ _ _ (inp_2817 v h) (by intro d hd; cases hd)))
def cl_23821 : CNF.NClause := [(104,true),(38,false),(35,false),(49,true),(52,false),(59,false)]
theorem der_23821 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23821 :=
  CNF.rup_sound cl_23821 [cl_2701,cl_2697] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2701 v h) (hints_cons _ _ _ (inp_2697 v h) (by intro d hd; cases hd)))
def cl_23822 : CNF.NClause := [(104,true),(38,false),(35,false),(41,true),(49,false),(59,false)]
theorem der_23822 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23822 :=
  CNF.rup_sound cl_23822 [cl_2709,cl_2693] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2709 v h) (hints_cons _ _ _ (inp_2693 v h) (by intro d hd; cases hd)))
def cl_23823 : CNF.NClause := [(104,true),(38,false),(35,false),(49,true),(52,true),(59,false)]
theorem der_23823 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23823 :=
  CNF.rup_sound cl_23823 [cl_2717,cl_23813] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2717 v h) (hints_cons _ _ _ (der_23813 v h) (by intro d hd; cases hd)))
def cl_23824 : CNF.NClause := [(104,true),(38,false),(35,false),(41,true),(49,false),(52,false)]
theorem der_23824 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23824 :=
  CNF.rup_sound cl_23824 [cl_2725,cl_2693] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2725 v h) (hints_cons _ _ _ (inp_2693 v h) (by intro d hd; cases hd)))
def cl_23825 : CNF.NClause := [(104,true),(38,false),(35,false),(49,true),(52,false),(59,true)]
theorem der_23825 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23825 :=
  CNF.rup_sound cl_23825 [cl_2733,cl_23805] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2733 v h) (hints_cons _ _ _ (der_23805 v h) (by intro d hd; cases hd)))
def cl_23826 : CNF.NClause := [(104,true),(38,false),(35,false),(41,true),(49,false),(52,true)]
theorem der_23826 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23826 :=
  CNF.rup_sound cl_23826 [cl_2741,cl_23822] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2741 v h) (hints_cons _ _ _ (der_23822 v h) (by intro d hd; cases hd)))
def cl_23827 : CNF.NClause := [(104,true),(38,false),(35,false),(49,true),(52,true),(59,true)]
theorem der_23827 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23827 :=
  CNF.rup_sound cl_23827 [cl_2749,cl_23806] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2749 v h) (hints_cons _ _ _ (der_23806 v h) (by intro d hd; cases hd)))
def cl_23828 : CNF.NClause := [(109,true),(58,false),(37,false),(35,false),(46,true),(44,true)]
theorem der_23828 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23828 :=
  CNF.rup_sound cl_23828 [cl_3021,cl_23767] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3021 v h) (hints_cons _ _ _ (der_23767 v h) (by intro d hd; cases hd)))
def cl_23829 : CNF.NClause := [(109,true),(58,false),(37,false),(35,false),(53,false),(44,true)]
theorem der_23829 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23829 :=
  CNF.rup_sound cl_23829 [cl_3013,cl_23828] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3013 v h) (hints_cons _ _ _ (der_23828 v h) (by intro d hd; cases hd)))
def cl_23830 : CNF.NClause := [(104,true),(41,false),(35,false),(49,true),(52,true),(59,false)]
theorem der_23830 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23830 :=
  CNF.rup_sound cl_23830 [cl_2715,cl_23813] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2715 v h) (hints_cons _ _ _ (der_23813 v h) (by intro d hd; cases hd)))
def cl_23831 : CNF.NClause := [(104,true),(52,true),(38,true),(49,true),(35,false),(59,false)]
theorem der_23831 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23831 :=
  CNF.rup_sound cl_23831 [cl_2719,cl_23830] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2719 v h) (hints_cons _ _ _ (der_23830 v h) (by intro d hd; cases hd)))
def cl_23832 : CNF.NClause := [(104,true),(35,false),(38,true),(49,false),(52,false),(59,true)]
theorem der_23832 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23832 :=
  CNF.rup_sound cl_23832 [cl_2727,cl_2723] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2727 v h) (hints_cons _ _ _ (inp_2723 v h) (by intro d hd; cases hd)))
def cl_23833 : CNF.NClause := [(104,true),(41,false),(35,false),(49,true),(52,false),(59,true)]
theorem der_23833 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23833 :=
  CNF.rup_sound cl_23833 [cl_2731,cl_23805] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2731 v h) (hints_cons _ _ _ (der_23805 v h) (by intro d hd; cases hd)))
def cl_23834 : CNF.NClause := [(104,true),(35,false),(38,true),(41,true),(52,false),(59,true)]
theorem der_23834 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23834 :=
  CNF.rup_sound cl_23834 [cl_2735,cl_23832] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2735 v h) (hints_cons _ _ _ (der_23832 v h) (by intro d hd; cases hd)))
def cl_23835 : CNF.NClause := [(104,true),(41,false),(38,true),(35,false),(49,false),(59,true)]
theorem der_23835 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23835 :=
  CNF.rup_sound cl_23835 [cl_2739,cl_2723] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2739 v h) (hints_cons _ _ _ (inp_2723 v h) (by intro d hd; cases hd)))
def cl_23836 : CNF.NClause := [(104,true),(35,false),(38,true),(41,true),(49,false),(59,true)]
theorem der_23836 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23836 :=
  CNF.rup_sound cl_23836 [cl_2743,cl_23832] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2743 v h) (hints_cons _ _ _ (der_23832 v h) (by intro d hd; cases hd)))
def cl_23837 : CNF.NClause := [(104,true),(52,true),(41,false),(49,true),(35,false),(59,true)]
theorem der_23837 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23837 :=
  CNF.rup_sound cl_23837 [cl_2747,cl_23806] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2747 v h) (hints_cons _ _ _ (der_23806 v h) (by intro d hd; cases hd)))
def cl_23838 : CNF.NClause := [(93,true),(59,false),(58,false),(61,true),(56,true),(57,false)]
theorem der_23838 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23838 :=
  CNF.rup_sound cl_23838 [cl_2018,cl_23791] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2018 v h) (hints_cons _ _ _ (der_23791 v h) (by intro d hd; cases hd)))
def cl_23839 : CNF.NClause := [(106,true),(41,false),(34,false),(47,false),(57,false),(53,false)]
theorem der_23839 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23839 :=
  CNF.rup_sound cl_23839 [cl_2819,cl_2817] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2819 v h) (hints_cons _ _ _ (inp_2817 v h) (by intro d hd; cases hd)))
def cl_23840 : CNF.NClause := [(114,true),(57,false),(36,false),(42,false),(54,false),(35,false)]
theorem der_23840 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23840 :=
  CNF.rup_sound cl_23840 [cl_3329,cl_3337] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3329 v h) (hints_cons _ _ _ (inp_3337 v h) (by intro d hd; cases hd)))
def cl_23841 : CNF.NClause := [(99,true),(51,false),(35,false),(39,false),(43,false),(47,true)]
theorem der_23841 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23841 :=
  CNF.rup_sound cl_23841 [cl_2377,cl_2409] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2377 v h) (hints_cons _ _ _ (inp_2409 v h) (by intro d hd; cases hd)))
def cl_23842 : CNF.NClause := [(99,true),(51,false),(35,false),(39,false),(43,false),(60,true)]
theorem der_23842 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23842 :=
  CNF.rup_sound cl_23842 [cl_2401,cl_2409] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2401 v h) (hints_cons _ _ _ (inp_2409 v h) (by intro d hd; cases hd)))
def cl_23843 : CNF.NClause := [(98,true),(52,true),(53,false),(51,false),(55,false),(61,true)]
theorem der_23843 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23843 :=
  CNF.rup_sound cl_23843 [cl_2347,cl_23797] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2347 v h) (hints_cons _ _ _ (der_23797 v h) (by intro d hd; cases hd)))
def cl_23844 : CNF.NClause := [(98,true),(51,false),(52,true),(54,false),(55,true),(61,true)]
theorem der_23844 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23844 :=
  CNF.rup_sound cl_23844 [cl_2355,cl_23766] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2355 v h) (hints_cons _ _ _ (der_23766 v h) (by intro d hd; cases hd)))
def cl_23845 : CNF.NClause := [(98,true),(52,true),(51,false),(53,false),(54,true),(61,true)]
theorem der_23845 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23845 :=
  CNF.rup_sound cl_23845 [cl_2363,cl_23843] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2363 v h) (hints_cons _ _ _ (der_23843 v h) (by intro d hd; cases hd)))
def cl_23846 : CNF.NClause := [(100,true),(51,false),(42,false),(49,true),(33,false),(58,true)]
theorem der_23846 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23846 :=
  CNF.rup_sound cl_23846 [cl_2475,cl_23808] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2475 v h) (hints_cons _ _ _ (der_23808 v h) (by intro d hd; cases hd)))
def cl_23847 : CNF.NClause := [(101,true),(34,false),(37,false),(59,false),(45,true),(51,false)]
theorem der_23847 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23847 :=
  CNF.rup_sound cl_23847 [cl_2501,cl_2509] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2501 v h) (hints_cons _ _ _ (inp_2509 v h) (by intro d hd; cases hd)))
def cl_23848 : CNF.NClause := [(101,true),(34,false),(51,false),(37,false),(48,false),(59,false)]
theorem der_23848 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23848 :=
  CNF.rup_sound cl_23848 [cl_2497,cl_23847] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2497 v h) (hints_cons _ _ _ (der_23847 v h) (by intro d hd; cases hd)))
def cl_23849 : CNF.NClause := [(102,true),(50,false),(38,false),(44,false),(32,false),(51,true)]
theorem der_23849 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23849 :=
  CNF.rup_sound cl_23849 [cl_2609,cl_2577] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2609 v h) (hints_cons _ _ _ (inp_2577 v h) (by intro d hd; cases hd)))
def cl_23850 : CNF.NClause := [(105,true),(41,false),(33,false),(37,false),(54,false),(50,false)]
theorem der_23850 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23850 :=
  CNF.rup_sound cl_23850 [cl_2753,cl_2785] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2753 v h) (hints_cons _ _ _ (inp_2785 v h) (by intro d hd; cases hd)))
def cl_23851 : CNF.NClause := [(94,true),(55,false),(35,false),(40,true),(50,false),(56,true)]
theorem der_23851 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23851 :=
  CNF.rup_sound cl_23851 [cl_2083,cl_2087] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2083 v h) (hints_cons _ _ _ (inp_2087 v h) (by intro d hd; cases hd)))
def cl_23853 : CNF.NClause := [(108,true),(61,false),(47,true),(48,true),(49,true),(50,false)]
theorem der_23853 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23853 :=
  CNF.rup_sound cl_23853 [cl_2960,cl_23697] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2960 v h) (hints_cons _ _ _ (der_23697 v h) (by intro d hd; cases hd)))
def cl_23854 : CNF.NClause := [(108,false),(46,true),(48,true),(49,true),(47,true),(61,true)]
theorem der_23854 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23854 :=
  CNF.rup_sound cl_23854 [cl_2992,cl_23812] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2992 v h) (hints_cons _ _ _ (der_23812 v h) (by intro d hd; cases hd)))
def cl_23855 : CNF.NClause := [(108,true),(49,true),(46,false),(48,false),(50,false),(47,true)]
theorem der_23855 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23855 :=
  CNF.rup_sound cl_23855 [cl_2987,cl_23803] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2987 v h) (hints_cons _ _ _ (der_23803 v h) (by intro d hd; cases hd)))
def cl_23856 : CNF.NClause := [(94,true),(50,false),(35,false),(45,true),(55,false),(56,true)]
theorem der_23856 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23856 :=
  CNF.rup_sound cl_23856 [cl_2085,cl_2087] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2085 v h) (hints_cons _ _ _ (inp_2087 v h) (by intro d hd; cases hd)))
def cl_23857 : CNF.NClause := [(94,true),(40,false),(50,false),(45,true),(35,false),(55,true)]
theorem der_23857 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23857 :=
  CNF.rup_sound cl_23857 [cl_2101,cl_2069] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2101 v h) (hints_cons _ _ _ (inp_2069 v h) (by intro d hd; cases hd)))
def cl_23858 : CNF.NClause := [(94,true),(50,false),(40,true),(45,true),(35,false),(56,true)]
theorem der_23858 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23858 :=
  CNF.rup_sound cl_23858 [cl_2103,cl_2087] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2103 v h) (hints_cons _ _ _ (inp_2087 v h) (by intro d hd; cases hd)))
def cl_23859 : CNF.NClause := [(108,true),(50,false),(47,false),(46,false),(49,false),(61,true)]
theorem der_23859 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23859 :=
  CNF.rup_sound cl_23859 [cl_2981,cl_2977] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2981 v h) (hints_cons _ _ _ (inp_2977 v h) (by intro d hd; cases hd)))
def cl_23860 : CNF.NClause := [(108,true),(49,true),(46,false),(50,false),(48,true),(61,true)]
theorem der_23860 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23860 :=
  CNF.rup_sound cl_23860 [cl_2989,cl_23817] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2989 v h) (hints_cons _ _ _ (der_23817 v h) (by intro d hd; cases hd)))
def cl_23861 : CNF.NClause := [(108,true),(49,true),(47,false),(50,false),(46,false),(48,false)]
theorem der_23861 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23861 :=
  CNF.rup_sound cl_23861 [cl_2985,cl_23803] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2985 v h) (hints_cons _ _ _ (der_23803 v h) (by intro d hd; cases hd)))
def cl_23862 : CNF.NClause := [(102,true),(32,false),(38,false),(44,false),(50,false),(57,false)]
theorem der_23862 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23862 :=
  CNF.rup_sound cl_23862 [cl_2561,cl_2577] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2561 v h) (hints_cons _ _ _ (inp_2577 v h) (by intro d hd; cases hd)))
def cl_23863 : CNF.NClause := [(119,false),(52,true),(31,true),(48,true),(44,true),(60,true)]
theorem der_23863 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23863 :=
  CNF.rup_sound cl_23863 [cl_3710,cl_23801] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3710 v h) (hints_cons _ _ _ (der_23801 v h) (by intro d hd; cases hd)))
def cl_23864 : CNF.NClause := [(96,true),(34,false),(39,false),(49,true),(54,true),(56,true)]
theorem der_23864 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23864 :=
  CNF.rup_sound cl_23864 [cl_2237,cl_23809] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2237 v h) (hints_cons _ _ _ (der_23809 v h) (by intro d hd; cases hd)))
def cl_23865 : CNF.NClause := [(115,true),(44,true),(33,false),(36,false),(55,false),(59,false)]
theorem der_23865 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23865 :=
  CNF.rup_sound cl_23865 [cl_3397,cl_3405] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3397 v h) (hints_cons _ _ _ (inp_3405 v h) (by intro d hd; cases hd)))
def cl_23866 : CNF.NClause := [(115,true),(59,false),(33,false),(36,false),(47,false),(44,true)]
theorem der_23866 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23866 :=
  CNF.rup_sound cl_23866 [cl_3413,cl_23865] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3413 v h) (hints_cons _ _ _ (der_23865 v h) (by intro d hd; cases hd)))
def cl_23867 : CNF.NClause := [(115,true),(33,false),(36,false),(47,true),(55,true),(59,false)]
theorem der_23867 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23867 :=
  CNF.rup_sound cl_23867 [cl_3421,cl_3417] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3421 v h) (hints_cons _ _ _ (inp_3417 v h) (by intro d hd; cases hd)))
def cl_23868 : CNF.NClause := [(115,true),(44,true),(33,false),(36,false),(47,false),(55,false)]
theorem der_23868 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23868 :=
  CNF.rup_sound cl_23868 [cl_3429,cl_23865] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3429 v h) (hints_cons _ _ _ (der_23865 v h) (by intro d hd; cases hd)))
def cl_23869 : CNF.NClause := [(115,true),(33,false),(44,true),(36,false),(47,false),(55,true)]
theorem der_23869 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23869 :=
  CNF.rup_sound cl_23869 [cl_3445,cl_23866] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3445 v h) (hints_cons _ _ _ (der_23866 v h) (by intro d hd; cases hd)))
def cl_23870 : CNF.NClause := [(115,true),(33,false),(36,false),(47,true),(55,true),(59,true)]
theorem der_23870 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23870 :=
  CNF.rup_sound cl_23870 [cl_3453,cl_23698] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3453 v h) (hints_cons _ _ _ (der_23698 v h) (by intro d hd; cases hd)))
def cl_23871 : CNF.NClause := [(96,true),(56,false),(39,false),(34,false),(49,true),(54,true)]
theorem der_23871 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23871 :=
  CNF.rup_sound cl_23871 [cl_2205,cl_2201] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2205 v h) (hints_cons _ _ _ (inp_2201 v h) (by intro d hd; cases hd)))
def cl_23873 : CNF.NClause := [(109,true),(53,true),(35,false),(46,false),(37,false),(58,false)]
theorem der_23873 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23873 :=
  CNF.rup_sound cl_23873 [cl_3029,cl_3025] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3029 v h) (hints_cons _ _ _ (inp_3025 v h) (by intro d hd; cases hd)))
def cl_23874 : CNF.NClause := [(109,true),(35,false),(37,false),(44,true),(46,false),(53,false)]
theorem der_23874 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23874 :=
  CNF.rup_sound cl_23874 [cl_3045,cl_23829] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3045 v h) (hints_cons _ _ _ (der_23829 v h) (by intro d hd; cases hd)))
def cl_23875 : CNF.NClause := [(109,true),(53,true),(44,true),(35,false),(37,false),(58,true)]
theorem der_23875 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23875 :=
  CNF.rup_sound cl_23875 [cl_3061,cl_23768] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3061 v h) (hints_cons _ _ _ (der_23768 v h) (by intro d hd; cases hd)))
def cl_23876 : CNF.NClause := [(103,true),(61,false),(42,false),(41,false),(45,false),(44,true)]
theorem der_23876 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23876 :=
  CNF.rup_sound cl_23876 [cl_2637,cl_2633] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2637 v h) (hints_cons _ _ _ (inp_2633 v h) (by intro d hd; cases hd)))
def cl_23877 : CNF.NClause := [(103,true),(61,false),(43,true),(41,false),(45,false),(44,true)]
theorem der_23877 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23877 :=
  CNF.rup_sound cl_23877 [cl_2639,cl_23876] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2639 v h) (hints_cons _ _ _ (der_23876 v h) (by intro d hd; cases hd)))
def cl_23878 : CNF.NClause := [(103,true),(42,false),(43,false),(41,false),(45,true),(44,true)]
theorem der_23878 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23878 :=
  CNF.rup_sound cl_23878 [cl_2649,cl_2681] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2649 v h) (hints_cons _ _ _ (inp_2681 v h) (by intro d hd; cases hd)))
def cl_23879 : CNF.NClause := [(103,true),(61,false),(42,false),(43,true),(41,false),(44,true)]
theorem der_23879 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23879 :=
  CNF.rup_sound cl_23879 [cl_2653,cl_23877] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2653 v h) (hints_cons _ _ _ (der_23877 v h) (by intro d hd; cases hd)))
def cl_23880 : CNF.NClause := [(103,true),(61,false),(42,true),(43,true),(41,false),(44,true)]
theorem der_23880 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23880 :=
  CNF.rup_sound cl_23880 [cl_2655,cl_23877] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2655 v h) (hints_cons _ _ _ (der_23877 v h) (by intro d hd; cases hd)))
def cl_23881 : CNF.NClause := [(103,true),(41,false),(42,true),(43,true),(44,true),(45,false)]
theorem der_23881 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23881 :=
  CNF.rup_sound cl_23881 [cl_2671,cl_23877] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2671 v h) (hints_cons _ _ _ (der_23877 v h) (by intro d hd; cases hd)))
def cl_23882 : CNF.NClause := [(103,true),(61,false),(41,false),(43,false),(45,false),(44,true)]
theorem der_23882 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23882 :=
  CNF.rup_sound cl_23882 [cl_2635,cl_2633] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2635 v h) (hints_cons _ _ _ (inp_2633 v h) (by intro d hd; cases hd)))
def cl_23883 : CNF.NClause := [(103,true),(61,false),(42,true),(41,false),(43,false),(45,true)]
theorem der_23883 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23883 :=
  CNF.rup_sound cl_23883 [cl_2651,cl_2643] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2651 v h) (hints_cons _ _ _ (inp_2643 v h) (by intro d hd; cases hd)))
def cl_23884 : CNF.NClause := [(103,true),(41,false),(42,true),(44,true),(45,false),(61,true)]
theorem der_23884 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23884 :=
  CNF.rup_sound cl_23884 [cl_2667,cl_23881] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2667 v h) (hints_cons _ _ _ (der_23881 v h) (by intro d hd; cases hd)))
def cl_23885 : CNF.NClause := [(103,true),(41,false),(44,true),(42,false),(43,false),(61,true)]
theorem der_23885 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23885 :=
  CNF.rup_sound cl_23885 [cl_2665,cl_2681] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2665 v h) (hints_cons _ _ _ (inp_2681 v h) (by intro d hd; cases hd)))
def cl_23886 : CNF.NClause := [(109,true),(46,true),(44,true),(35,false),(37,false),(58,true)]
theorem der_23886 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23886 :=
  CNF.rup_sound cl_23886 [cl_3053,cl_23768] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3053 v h) (hints_cons _ _ _ (der_23768 v h) (by intro d hd; cases hd)))
def cl_23887 : CNF.NClause := [(96,true),(34,false),(44,true),(49,true),(54,false),(56,true)]
theorem der_23887 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23887 :=
  CNF.rup_sound cl_23887 [cl_2223,cl_2221] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2223 v h) (hints_cons _ _ _ (inp_2221 v h) (by intro d hd; cases hd)))
def cl_23888 : CNF.NClause := [(119,true),(52,true),(44,true),(48,false),(31,true),(60,false)]
theorem der_23888 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23888 :=
  CNF.rup_sound cl_23888 [cl_3672,cl_3670] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3672 v h) (hints_cons _ _ _ (inp_3670 v h) (by intro d hd; cases hd)))
def cl_23889 : CNF.NClause := [(119,true),(44,true),(31,true),(60,false),(52,true),(40,false)]
theorem der_23889 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23889 :=
  CNF.rup_sound cl_23889 [cl_3678,cl_3670] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3678 v h) (hints_cons _ _ _ (inp_3670 v h) (by intro d hd; cases hd)))
def cl_23890 : CNF.NClause := [(119,true),(52,false),(31,true),(44,true),(48,false),(60,true)]
theorem der_23890 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23890 :=
  CNF.rup_sound cl_23890 [cl_3686,cl_23774] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3686 v h) (hints_cons _ _ _ (der_23774 v h) (by intro d hd; cases hd)))
def cl_23891 : CNF.NClause := [(119,true),(52,false),(31,true),(44,true),(40,false),(60,true)]
theorem der_23891 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23891 :=
  CNF.rup_sound cl_23891 [cl_3694,cl_23890] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3694 v h) (hints_cons _ _ _ (der_23890 v h) (by intro d hd; cases hd)))
def cl_23892 : CNF.NClause := [(119,true),(48,false),(31,true),(44,true),(40,false),(52,true)]
theorem der_23892 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23892 :=
  CNF.rup_sound cl_23892 [cl_3702,cl_3670] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3702 v h) (hints_cons _ _ _ (inp_3670 v h) (by intro d hd; cases hd)))
def cl_23893 : CNF.NClause := [(102,true),(32,false),(38,false),(50,false),(51,true),(57,false)]
theorem der_23893 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23893 :=
  CNF.rup_sound cl_23893 [cl_2581,cl_2577] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2581 v h) (hints_cons _ _ _ (inp_2577 v h) (by intro d hd; cases hd)))
def cl_23894 : CNF.NClause := [(102,true),(32,false),(38,false),(44,true),(50,true),(57,false)]
theorem der_23894 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23894 :=
  CNF.rup_sound cl_23894 [cl_2589,cl_2573] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2589 v h) (hints_cons _ _ _ (inp_2573 v h) (by intro d hd; cases hd)))
def cl_23895 : CNF.NClause := [(102,true),(32,false),(38,false),(50,false),(51,false),(57,true)]
theorem der_23895 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23895 :=
  CNF.rup_sound cl_23895 [cl_2597,cl_2593] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2597 v h) (hints_cons _ _ _ (inp_2593 v h) (by intro d hd; cases hd)))
def cl_23896 : CNF.NClause := [(102,true),(32,false),(38,false),(44,true),(50,true),(51,false)]
theorem der_23896 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23896 :=
  CNF.rup_sound cl_23896 [cl_2605,cl_2573] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2605 v h) (hints_cons _ _ _ (inp_2573 v h) (by intro d hd; cases hd)))
def cl_23897 : CNF.NClause := [(102,true),(32,false),(38,false),(50,false),(51,true),(57,true)]
theorem der_23897 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23897 :=
  CNF.rup_sound cl_23897 [cl_2613,cl_23849] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2613 v h) (hints_cons _ _ _ (der_23849 v h) (by intro d hd; cases hd)))
def cl_23898 : CNF.NClause := [(102,true),(32,false),(38,false),(44,true),(50,true),(57,true)]
theorem der_23898 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23898 :=
  CNF.rup_sound cl_23898 [cl_2621,cl_23896] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2621 v h) (hints_cons _ _ _ (der_23896 v h) (by intro d hd; cases hd)))
def cl_23899 : CNF.NClause := [(112,true),(32,false),(40,true),(43,false),(46,true),(59,false)]
theorem der_23899 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23899 :=
  CNF.rup_sound cl_23899 [cl_3227,cl_3211] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3227 v h) (hints_cons _ _ _ (inp_3211 v h) (by intro d hd; cases hd)))
def cl_23900 : CNF.NClause := [(112,true),(32,false),(40,true),(43,false),(46,true),(54,true)]
theorem der_23900 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23900 :=
  CNF.rup_sound cl_23900 [cl_3259,cl_23899] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3259 v h) (hints_cons _ _ _ (der_23899 v h) (by intro d hd; cases hd)))
def cl_23901 : CNF.NClause := [(117,true),(32,false),(49,true),(45,false),(36,false),(60,true)]
theorem der_23901 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23901 :=
  CNF.rup_sound cl_23901 [cl_3561,cl_23753] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3561 v h) (hints_cons _ _ _ (der_23753 v h) (by intro d hd; cases hd)))
def cl_23902 : CNF.NClause := [(117,true),(32,false),(36,false),(45,true),(49,true),(60,false)]
theorem der_23902 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23902 :=
  CNF.rup_sound cl_23902 [cl_3533,cl_23754] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3533 v h) (hints_cons _ _ _ (der_23754 v h) (by intro d hd; cases hd)))
def cl_23903 : CNF.NClause := [(107,true),(32,false),(41,false),(39,false),(55,false),(58,false)]
theorem der_23903 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23903 :=
  CNF.rup_sound cl_23903 [cl_2881,cl_2889] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2881 v h) (hints_cons _ _ _ (inp_2889 v h) (by intro d hd; cases hd)))
def cl_23904 : CNF.NClause := [(117,true),(32,false),(49,true),(45,false),(36,false),(60,false)]
theorem der_23904 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23904 :=
  CNF.rup_sound cl_23904 [cl_3529,cl_23752] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3529 v h) (hints_cons _ _ _ (der_23752 v h) (by intro d hd; cases hd)))
def cl_23905 : CNF.NClause := [(112,true),(32,false),(43,false),(46,false),(54,false),(59,false)]
theorem der_23905 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23905 :=
  CNF.rup_sound cl_23905 [cl_3201,cl_23790] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3201 v h) (hints_cons _ _ _ (der_23790 v h) (by intro d hd; cases hd)))
def cl_23906 : CNF.NClause := [(102,true),(32,false),(44,false),(50,false),(51,true),(57,false)]
theorem der_23906 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23906 :=
  CNF.rup_sound cl_23906 [cl_2579,cl_2577] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2579 v h) (hints_cons _ _ _ (inp_2577 v h) (by intro d hd; cases hd)))
def cl_23907 : CNF.NClause := [(102,true),(32,false),(38,true),(44,true),(50,false),(57,false)]
theorem der_23907 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23907 :=
  CNF.rup_sound cl_23907 [cl_2583,cl_2567] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2583 v h) (hints_cons _ _ _ (inp_2567 v h) (by intro d hd; cases hd)))
def cl_23908 : CNF.NClause := [(102,true),(32,false),(38,true),(44,false),(51,true),(57,false)]
theorem der_23908 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23908 :=
  CNF.rup_sound cl_23908 [cl_2587,cl_23906] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2587 v h) (hints_cons _ _ _ (der_23906 v h) (by intro d hd; cases hd)))
def cl_23909 : CNF.NClause := [(102,true),(32,false),(38,true),(50,true),(51,true),(57,false)]
theorem der_23909 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23909 :=
  CNF.rup_sound cl_23909 [cl_2591,cl_23908] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2591 v h) (hints_cons _ _ _ (der_23908 v h) (by intro d hd; cases hd)))
def cl_23910 : CNF.NClause := [(102,true),(32,false),(44,false),(50,false),(51,false),(57,true)]
theorem der_23910 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23910 :=
  CNF.rup_sound cl_23910 [cl_2595,cl_2593] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2595 v h) (hints_cons _ _ _ (inp_2593 v h) (by intro d hd; cases hd)))
def cl_23911 : CNF.NClause := [(102,true),(32,false),(38,true),(44,true),(50,false),(51,false)]
theorem der_23911 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23911 :=
  CNF.rup_sound cl_23911 [cl_2599,cl_2567] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2599 v h) (hints_cons _ _ _ (inp_2567 v h) (by intro d hd; cases hd)))
def cl_23912 : CNF.NClause := [(102,true),(32,false),(38,true),(44,false),(51,false),(57,true)]
theorem der_23912 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23912 :=
  CNF.rup_sound cl_23912 [cl_2603,cl_23910] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2603 v h) (hints_cons _ _ _ (der_23910 v h) (by intro d hd; cases hd)))
def cl_23913 : CNF.NClause := [(102,true),(32,false),(44,true),(50,true),(51,false),(57,true)]
theorem der_23913 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23913 :=
  CNF.rup_sound cl_23913 [cl_2607,cl_23896] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2607 v h) (hints_cons _ _ _ (der_23896 v h) (by intro d hd; cases hd)))
def cl_23914 : CNF.NClause := [(102,true),(32,false),(38,true),(44,false),(50,false),(51,true)]
theorem der_23914 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23914 :=
  CNF.rup_sound cl_23914 [cl_2611,cl_23906] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2611 v h) (hints_cons _ _ _ (der_23906 v h) (by intro d hd; cases hd)))
def cl_23915 : CNF.NClause := [(102,true),(32,false),(38,true),(44,true),(50,false),(57,true)]
theorem der_23915 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23915 :=
  CNF.rup_sound cl_23915 [cl_2615,cl_23911] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2615 v h) (hints_cons _ _ _ (der_23911 v h) (by intro d hd; cases hd)))
def cl_23916 : CNF.NClause := [(102,true),(32,false),(38,true),(44,false),(50,true),(51,true)]
theorem der_23916 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23916 :=
  CNF.rup_sound cl_23916 [cl_2619,cl_23908] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2619 v h) (hints_cons _ _ _ (der_23908 v h) (by intro d hd; cases hd)))
def cl_23917 : CNF.NClause := [(102,true),(32,false),(38,true),(44,true),(51,false),(57,false)]
theorem der_23917 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23917 :=
  CNF.rup_sound cl_23917 [cl_2575,cl_2567] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2575 v h) (hints_cons _ _ _ (inp_2567 v h) (by intro d hd; cases hd)))
def cl_23918 : CNF.NClause := [(102,true),(32,false),(44,true),(50,false),(51,false),(57,false)]
theorem der_23918 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23918 :=
  CNF.rup_sound cl_23918 [cl_2565,cl_2567] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2565 v h) (hints_cons _ _ _ (inp_2567 v h) (by intro d hd; cases hd)))
def cl_23919 : CNF.NClause := [(116,false),(36,true),(43,true),(50,true),(52,true),(34,true)]
theorem der_23919 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23919 :=
  CNF.rup_sound cl_23919 [cl_3520,cl_3488] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3520 v h) (hints_cons _ _ _ (inp_3488 v h) (by intro d hd; cases hd)))
def cl_23920 : CNF.NClause := [(123,false),(51,true),(31,true),(36,true),(46,true),(41,true)]
theorem der_23920 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23920 :=
  CNF.rup_sound cl_23920 [cl_3968,cl_3936] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3968 v h) (hints_cons _ _ _ (inp_3936 v h) (by intro d hd; cases hd)))
def cl_23921 : CNF.NClause := [(115,false),(47,true),(36,true),(55,true),(44,true),(33,true)]
theorem der_23921 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23921 :=
  CNF.rup_sound cl_23921 [cl_3456,cl_3424] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3456 v h) (hints_cons _ _ _ (inp_3424 v h) (by intro d hd; cases hd)))
def cl_23922 : CNF.NClause := [(114,false),(35,true),(36,true),(42,true),(48,true),(54,true)]
theorem der_23922 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23922 :=
  CNF.rup_sound cl_23922 [cl_3392,cl_3360] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3392 v h) (hints_cons _ _ _ (inp_3360 v h) (by intro d hd; cases hd)))
def cl_23923 : CNF.NClause := [(117,false),(49,true),(36,true),(32,true),(45,true),(60,true)]
theorem der_23923 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23923 :=
  CNF.rup_sound cl_23923 [cl_3584,cl_3568] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3584 v h) (hints_cons _ _ _ (inp_3568 v h) (by intro d hd; cases hd)))
def cl_23924 : CNF.NClause := [(113,false),(40,true),(37,true),(36,true),(39,true),(38,true)]
theorem der_23924 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23924 :=
  CNF.rup_sound cl_23924 [cl_3328,cl_3296] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3328 v h) (hints_cons _ _ _ (inp_3296 v h) (by intro d hd; cases hd)))
def cl_23925 : CNF.NClause := [(112,false),(54,true),(40,true),(43,true),(46,true),(32,true)]
theorem der_23925 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23925 :=
  CNF.rup_sound cl_23925 [cl_3264,cl_3232] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3264 v h) (hints_cons _ _ _ (inp_3232 v h) (by intro d hd; cases hd)))
def cl_23926 : CNF.NClause := [(95,false),(48,true),(43,true),(38,true),(53,true),(56,true)]
theorem der_23926 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23926 :=
  CNF.rup_sound cl_23926 [cl_2176,cl_2175] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2176 v h) (hints_cons _ _ _ (inp_2175 v h) (by intro d hd; cases hd)))
def cl_23927 : CNF.NClause := [(99,false),(47,true),(39,true),(43,true),(51,true),(35,true)]
theorem der_23927 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23927 :=
  CNF.rup_sound cl_23927 [cl_2432,cl_2400] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2432 v h) (hints_cons _ _ _ (inp_2400 v h) (by intro d hd; cases hd)))
def cl_23928 : CNF.NClause := [(122,false),(57,true),(37,true),(43,true),(31,true),(49,true)]
theorem der_23928 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23928 :=
  CNF.rup_sound cl_23928 [cl_3888,cl_23811] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3888 v h) (hints_cons _ _ _ (der_23811 v h) (by intro d hd; cases hd)))
def cl_23929 : CNF.NClause := [(122,false),(57,true),(31,true),(43,true),(37,true),(55,true)]
theorem der_23929 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23929 :=
  CNF.rup_sound cl_23929 [cl_3896,cl_23928] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3896 v h) (hints_cons _ _ _ (der_23928 v h) (by intro d hd; cases hd)))
def cl_23931 : CNF.NClause := [(103,false),(45,true),(42,true),(43,true),(44,true),(61,true)]
theorem der_23931 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23931 :=
  CNF.rup_sound cl_23931 [cl_2688,cl_2687] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2688 v h) (hints_cons _ _ _ (inp_2687 v h) (by intro d hd; cases hd)))
def cl_23933 : CNF.NClause := [(108,false),(48,true),(47,true),(46,true),(50,true),(61,true)]
theorem der_23933 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23933 :=
  CNF.rup_sound cl_23933 [cl_3000,cl_23812] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3000 v h) (hints_cons _ _ _ (der_23812 v h) (by intro d hd; cases hd)))
def cl_23934 : CNF.NClause := [(108,false),(49,true),(48,true),(46,true),(50,true),(61,true)]
theorem der_23934 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23934 :=
  CNF.rup_sound cl_23934 [cl_3006,cl_23812] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3006 v h) (hints_cons _ _ _ (der_23812 v h) (by intro d hd; cases hd)))
def cl_23935 : CNF.NClause := [(108,false),(49,true),(48,true),(50,true),(47,true),(61,true)]
theorem der_23935 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23935 :=
  CNF.rup_sound cl_23935 [cl_3007,cl_23812] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3007 v h) (hints_cons _ _ _ (der_23812 v h) (by intro d hd; cases hd)))
def cl_23936 : CNF.NClause := [(109,false),(46,true),(37,true),(35,true),(44,true),(53,true)]
theorem der_23936 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23936 :=
  CNF.rup_sound cl_23936 [cl_3072,cl_3040] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3072 v h) (hints_cons _ _ _ (inp_3040 v h) (by intro d hd; cases hd)))
def cl_23937 : CNF.NClause := [(110,false),(52,true),(45,true),(46,true),(39,true),(57,true)]
theorem der_23937 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23937 :=
  CNF.rup_sound cl_23937 [cl_3136,cl_3135] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3136 v h) (hints_cons _ _ _ (inp_3135 v h) (by intro d hd; cases hd)))
def cl_23938 : CNF.NClause := [(110,false),(52,true),(33,true),(45,true),(39,true),(57,true)]
theorem der_23938 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23938 :=
  CNF.rup_sound cl_23938 [cl_3128,cl_23937] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3128 v h) (hints_cons _ _ _ (der_23937 v h) (by intro d hd; cases hd)))
def cl_23939 : CNF.NClause := [(111,false),(42,true),(38,true),(55,true),(46,true),(60,true)]
theorem der_23939 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23939 :=
  CNF.rup_sound cl_23939 [cl_3200,cl_3199] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3200 v h) (hints_cons _ _ _ (inp_3199 v h) (by intro d hd; cases hd)))
def cl_23940 : CNF.NClause := [(106,false),(34,true),(41,true),(47,true),(53,true),(40,true)]
theorem der_23940 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23940 :=
  CNF.rup_sound cl_23940 [cl_2880,cl_2848] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2880 v h) (hints_cons _ _ _ (inp_2848 v h) (by intro d hd; cases hd)))
def cl_23941 : CNF.NClause := [(97,false),(52,true),(37,true),(42,true),(47,true),(32,true)]
theorem der_23941 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23941 :=
  CNF.rup_sound cl_23941 [cl_2304,cl_2272] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2304 v h) (hints_cons _ _ _ (inp_2272 v h) (by intro d hd; cases hd)))
def cl_23943 : CNF.NClause := [(104,false),(49,true),(38,true),(41,true),(59,true),(52,true)]
theorem der_23943 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23943 :=
  CNF.rup_sound cl_23943 [cl_2752,cl_2751] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2752 v h) (hints_cons _ _ _ (inp_2751 v h) (by intro d hd; cases hd)))
def cl_23944 : CNF.NClause := [(118,false),(35,true),(33,true),(34,true),(32,true),(31,true)]
theorem der_23944 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23944 :=
  CNF.rup_sound cl_23944 [cl_3648,cl_3616] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3648 v h) (hints_cons _ _ _ (inp_3616 v h) (by intro d hd; cases hd)))
def cl_23945 : CNF.NClause := [(94,false),(40,true),(50,true),(45,true),(55,true),(56,true)]
theorem der_23945 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23945 :=
  CNF.rup_sound cl_23945 [cl_2112,cl_2111] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2112 v h) (hints_cons _ _ _ (inp_2111 v h) (by intro d hd; cases hd)))
def cl_23946 : CNF.NClause := [(121,false),(42,true),(31,true),(50,true),(53,true),(39,true)]
theorem der_23946 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23946 :=
  CNF.rup_sound cl_23946 [cl_3808,cl_23763] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3808 v h) (hints_cons _ _ _ (der_23763 v h) (by intro d hd; cases hd)))
def cl_23947 : CNF.NClause := [(121,false),(42,true),(39,true),(59,true),(50,true),(31,true)]
theorem der_23947 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23947 :=
  CNF.rup_sound cl_23947 [cl_3824,cl_23763] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3824 v h) (hints_cons _ _ _ (der_23763 v h) (by intro d hd; cases hd)))
def cl_23948 : CNF.NClause := [(121,false),(53,true),(31,true),(50,true),(42,true),(59,true)]
theorem der_23948 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23948 :=
  CNF.rup_sound cl_23948 [cl_3838,cl_23763] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3838 v h) (hints_cons _ _ _ (der_23763 v h) (by intro d hd; cases hd)))
def cl_23949 : CNF.NClause := [(121,false),(39,true),(42,true),(50,true),(53,true),(59,true)]
theorem der_23949 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23949 :=
  CNF.rup_sound cl_23949 [cl_3839,cl_23763] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3839 v h) (hints_cons _ _ _ (der_23763 v h) (by intro d hd; cases hd)))
def cl_23950 : CNF.NClause := [(98,false),(54,true),(52,true),(53,true),(55,true),(61,true)]
theorem der_23950 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23950 :=
  CNF.rup_sound cl_23950 [cl_2368,cl_2367] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2368 v h) (hints_cons _ _ _ (inp_2367 v h) (by intro d hd; cases hd)))
def cl_23951 : CNF.NClause := [(101,false),(48,true),(37,true),(45,true),(51,true),(34,true)]
theorem der_23951 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23951 :=
  CNF.rup_sound cl_23951 [cl_2560,cl_2528] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2560 v h) (hints_cons _ _ _ (inp_2528 v h) (by intro d hd; cases hd)))
def cl_23952 : CNF.NClause := [(93,false),(57,true),(56,true),(58,true),(59,true),(60,true)]
theorem der_23952 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23952 :=
  CNF.rup_sound cl_23952 [cl_2048,cl_2016] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2048 v h) (hints_cons _ _ _ (inp_2016 v h) (by intro d hd; cases hd)))
def cl_23953 : CNF.NClause := [(105,false),(37,true),(41,true),(50,true),(54,true),(33,true)]
theorem der_23953 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23953 :=
  CNF.rup_sound cl_23953 [cl_2816,cl_2784] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2816 v h) (hints_cons _ _ _ (inp_2784 v h) (by intro d hd; cases hd)))
def cl_23954 : CNF.NClause := [(100,false),(49,true),(40,true),(42,true),(33,true),(51,true)]
theorem der_23954 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23954 :=
  CNF.rup_sound cl_23954 [cl_2496,cl_2464] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2496 v h) (hints_cons _ _ _ (inp_2464 v h) (by intro d hd; cases hd)))
def cl_23955 : CNF.NClause := [(107,false),(32,true),(39,true),(41,true),(48,true),(55,true)]
theorem der_23955 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23955 :=
  CNF.rup_sound cl_23955 [cl_2944,cl_2912] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2944 v h) (hints_cons _ _ _ (inp_2912 v h) (by intro d hd; cases hd)))
def cl_23956 : CNF.NClause := [(96,false),(49,true),(39,true),(44,true),(54,true),(56,true)]
theorem der_23956 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23956 :=
  CNF.rup_sound cl_23956 [cl_2240,cl_2239] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2240 v h) (hints_cons _ _ _ (inp_2239 v h) (by intro d hd; cases hd)))
def cl_23957 : CNF.NClause := [(102,false),(38,true),(51,true),(50,true),(44,true),(57,true)]
theorem der_23957 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23957 :=
  CNF.rup_sound cl_23957 [cl_2624,cl_2623] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2624 v h) (hints_cons _ _ _ (inp_2623 v h) (by intro d hd; cases hd)))
def cl_23958 : CNF.NClause := [(119,false),(48,true),(40,true),(44,true),(31,true),(60,true)]
theorem der_23958 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23958 :=
  CNF.rup_sound cl_23958 [cl_3696,cl_23801] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3696 v h) (hints_cons _ _ _ (der_23801 v h) (by intro d hd; cases hd)))
def cl_23959 : CNF.NClause := [(119,false),(52,true),(40,true),(48,true),(31,true),(60,true)]
theorem der_23959 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23959 :=
  CNF.rup_sound cl_23959 [cl_3708,cl_23801] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3708 v h) (hints_cons _ _ _ (der_23801 v h) (by intro d hd; cases hd)))
def cl_23961 : CNF.NClause := [(79,true),(2,false),(15,false),(8,true),(21,false),(26,false)]
theorem der_23961 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23961 :=
  CNF.rup_sound cl_23961 [cl_1095,cl_1091] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1095 v h) (hints_cons _ _ _ (inp_1091 v h) (by intro d hd; cases hd)))
def cl_23962 : CNF.NClause := [(79,true),(14,false),(2,false),(8,true),(21,false),(26,false)]
theorem der_23962 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23962 :=
  CNF.rup_sound cl_23962 [cl_1099,cl_1091] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1099 v h) (hints_cons _ _ _ (inp_1091 v h) (by intro d hd; cases hd)))
def cl_23963 : CNF.NClause := [(79,true),(14,true),(2,false),(15,true),(21,false),(26,false)]
theorem der_23963 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23963 :=
  CNF.rup_sound cl_23963 [cl_1103,cl_23604] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1103 v h) (hints_cons _ _ _ (der_23604 v h) (by intro d hd; cases hd)))
def cl_23964 : CNF.NClause := [(79,true),(8,true),(2,false),(14,false),(15,false),(26,false)]
theorem der_23964 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23964 :=
  CNF.rup_sound cl_23964 [cl_1107,cl_23961] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1107 v h) (hints_cons _ _ _ (der_23961 v h) (by intro d hd; cases hd)))
def cl_23965 : CNF.NClause := [(79,true),(2,false),(14,true),(15,false),(21,true),(26,false)]
theorem der_23965 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23965 :=
  CNF.rup_sound cl_23965 [cl_1111,cl_23651] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1111 v h) (hints_cons _ _ _ (der_23651 v h) (by intro d hd; cases hd)))
def cl_23966 : CNF.NClause := [(79,true),(15,true),(14,false),(8,true),(21,true),(26,false)]
theorem der_23966 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23966 :=
  CNF.rup_sound cl_23966 [cl_1115,cl_23638] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1115 v h) (hints_cons _ _ _ (der_23638 v h) (by intro d hd; cases hd)))
def cl_23967 : CNF.NClause := [(79,true),(2,false),(14,true),(15,true),(21,true),(26,false)]
theorem der_23967 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23967 :=
  CNF.rup_sound cl_23967 [cl_1119,cl_23604] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1119 v h) (hints_cons _ _ _ (der_23604 v h) (by intro d hd; cases hd)))
def cl_23968 : CNF.NClause := [(79,true),(8,true),(14,false),(15,false),(21,false),(26,true)]
theorem der_23968 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23968 :=
  CNF.rup_sound cl_23968 [cl_1123,cl_23640] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1123 v h) (hints_cons _ _ _ (der_23640 v h) (by intro d hd; cases hd)))
def cl_23969 : CNF.NClause := [(79,true),(2,false),(8,true),(15,false),(21,false),(26,true)]
theorem der_23969 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23969 :=
  CNF.rup_sound cl_23969 [cl_1127,cl_23968] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1127 v h) (hints_cons _ _ _ (der_23968 v h) (by intro d hd; cases hd)))
def cl_23970 : CNF.NClause := [(79,true),(14,false),(2,false),(8,true),(21,false),(26,true)]
theorem der_23970 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23970 :=
  CNF.rup_sound cl_23970 [cl_1131,cl_23968] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1131 v h) (hints_cons _ _ _ (der_23968 v h) (by intro d hd; cases hd)))
def cl_23971 : CNF.NClause := [(79,true),(8,true),(2,false),(14,true),(15,true),(21,false)]
theorem der_23971 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23971 :=
  CNF.rup_sound cl_23971 [cl_1135,cl_23963] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1135 v h) (hints_cons _ _ _ (der_23963 v h) (by intro d hd; cases hd)))
def cl_23972 : CNF.NClause := [(79,true),(8,true),(14,false),(15,false),(21,true),(26,true)]
theorem der_23972 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23972 :=
  CNF.rup_sound cl_23972 [cl_1139,cl_23640] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1139 v h) (hints_cons _ _ _ (der_23640 v h) (by intro d hd; cases hd)))
def cl_23973 : CNF.NClause := [(79,true),(26,true),(2,false),(8,true),(15,false),(21,true)]
theorem der_23973 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23973 :=
  CNF.rup_sound cl_23973 [cl_1143,cl_23972] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1143 v h) (hints_cons _ _ _ (der_23972 v h) (by intro d hd; cases hd)))
def cl_23974 : CNF.NClause := [(79,true),(15,true),(2,false),(14,false),(8,true),(21,true)]
theorem der_23974 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23974 :=
  CNF.rup_sound cl_23974 [cl_1147,cl_23966] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1147 v h) (hints_cons _ _ _ (der_23966 v h) (by intro d hd; cases hd)))
def cl_23975 : CNF.NClause := [(68,true),(29,false),(4,false),(8,true),(16,true),(20,false)]
theorem der_23975 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23975 :=
  CNF.rup_sound cl_23975 [cl_395,cl_23564] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_395 v h) (hints_cons _ _ _ (der_23564 v h) (by intro d hd; cases hd)))
def cl_23976 : CNF.NClause := [(68,true),(8,true),(4,false),(12,false),(16,false),(29,false)]
theorem der_23976 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23976 :=
  CNF.rup_sound cl_23976 [cl_403,cl_387] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_403 v h) (hints_cons _ _ _ (inp_387 v h) (by intro d hd; cases hd)))
def cl_23977 : CNF.NClause := [(68,true),(16,true),(20,true),(4,false),(8,true),(29,false)]
theorem der_23977 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23977 :=
  CNF.rup_sound cl_23977 [cl_411,cl_23554] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_411 v h) (hints_cons _ _ _ (der_23554 v h) (by intro d hd; cases hd)))
def cl_23978 : CNF.NClause := [(68,true),(20,false),(4,false),(8,true),(12,false),(16,false)]
theorem der_23978 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23978 :=
  CNF.rup_sound cl_23978 [cl_419,cl_387] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_419 v h) (hints_cons _ _ _ (inp_387 v h) (by intro d hd; cases hd)))
def cl_23979 : CNF.NClause := [(68,true),(4,false),(8,true),(12,false),(16,true),(20,false)]
theorem der_23979 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23979 :=
  CNF.rup_sound cl_23979 [cl_427,cl_23975] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_427 v h) (hints_cons _ _ _ (der_23975 v h) (by intro d hd; cases hd)))
def cl_23980 : CNF.NClause := [(68,true),(8,true),(4,false),(12,false),(16,false),(20,true)]
theorem der_23980 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23980 :=
  CNF.rup_sound cl_23980 [cl_435,cl_23976] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_435 v h) (hints_cons _ _ _ (der_23976 v h) (by intro d hd; cases hd)))
def cl_23981 : CNF.NClause := [(68,true),(16,true),(29,true),(4,false),(12,false),(8,true)]
theorem der_23981 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23981 :=
  CNF.rup_sound cl_23981 [cl_443,cl_23979] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_443 v h) (hints_cons _ _ _ (der_23979 v h) (by intro d hd; cases hd)))
def cl_23982 : CNF.NClause := [(68,true),(29,false),(8,true),(12,false),(16,false),(20,false)]
theorem der_23982 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23982 :=
  CNF.rup_sound cl_23982 [cl_388,cl_387] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_388 v h) (hints_cons _ _ _ (inp_387 v h) (by intro d hd; cases hd)))
def cl_23983 : CNF.NClause := [(68,true),(29,false),(8,true),(12,false),(16,true),(20,false)]
theorem der_23983 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23983 :=
  CNF.rup_sound cl_23983 [cl_396,cl_23975] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_396 v h) (hints_cons _ _ _ (der_23975 v h) (by intro d hd; cases hd)))
def cl_23984 : CNF.NClause := [(68,true),(8,true),(29,false),(12,true),(20,false),(16,true)]
theorem der_23984 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23984 :=
  CNF.rup_sound cl_23984 [cl_400,cl_23975] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_400 v h) (hints_cons _ _ _ (der_23975 v h) (by intro d hd; cases hd)))
def cl_23985 : CNF.NClause := [(68,true),(29,false),(12,false),(4,true),(8,true),(16,false)]
theorem der_23985 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23985 :=
  CNF.rup_sound cl_23985 [cl_404,cl_23982] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_404 v h) (hints_cons _ _ _ (der_23982 v h) (by intro d hd; cases hd)))
def cl_23986 : CNF.NClause := [(68,true),(29,false),(4,true),(12,false),(8,true),(16,true)]
theorem der_23986 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23986 :=
  CNF.rup_sound cl_23986 [cl_412,cl_23983] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_412 v h) (hints_cons _ _ _ (der_23983 v h) (by intro d hd; cases hd)))
def cl_23987 : CNF.NClause := [(68,true),(20,false),(29,true),(12,false),(8,true),(16,false)]
theorem der_23987 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23987 :=
  CNF.rup_sound cl_23987 [cl_420,cl_23978] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_420 v h) (hints_cons _ _ _ (der_23978 v h) (by intro d hd; cases hd)))
def cl_23988 : CNF.NClause := [(68,true),(29,true),(8,true),(12,false),(16,true),(20,false)]
theorem der_23988 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23988 :=
  CNF.rup_sound cl_23988 [cl_428,cl_23979] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_428 v h) (hints_cons _ _ _ (der_23979 v h) (by intro d hd; cases hd)))
def cl_23989 : CNF.NClause := [(68,true),(29,true),(12,false),(4,true),(16,false),(8,true)]
theorem der_23989 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23989 :=
  CNF.rup_sound cl_23989 [cl_436,cl_23987] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_436 v h) (hints_cons _ _ _ (der_23987 v h) (by intro d hd; cases hd)))
def cl_23990 : CNF.NClause := [(76,true),(8,true),(10,false),(17,false),(24,false),(27,false)]
theorem der_23990 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23990 :=
  CNF.rup_sound cl_23990 [cl_899,cl_900] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_899 v h) (hints_cons _ _ _ (inp_900 v h) (by intro d hd; cases hd)))
def cl_23991 : CNF.NClause := [(76,true),(8,true),(10,false),(17,false),(24,false),(27,true)]
theorem der_23991 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23991 :=
  CNF.rup_sound cl_23991 [cl_931,cl_23594] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_931 v h) (hints_cons _ _ _ (der_23594 v h) (by intro d hd; cases hd)))
def cl_23992 : CNF.NClause := [(76,true),(8,true),(1,false),(17,false),(24,false),(27,true)]
theorem der_23992 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23992 :=
  CNF.rup_sound cl_23992 [cl_935,cl_23991] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_935 v h) (hints_cons _ _ _ (der_23991 v h) (by intro d hd; cases hd)))
def cl_23993 : CNF.NClause := [(76,true),(8,true),(1,false),(10,false),(24,false),(27,true)]
theorem der_23993 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23993 :=
  CNF.rup_sound cl_23993 [cl_939,cl_23991] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_939 v h) (hints_cons _ _ _ (der_23991 v h) (by intro d hd; cases hd)))
def cl_23994 : CNF.NClause := [(76,true),(8,true),(1,false),(10,true),(24,false),(27,true)]
theorem der_23994 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23994 :=
  CNF.rup_sound cl_23994 [cl_943,cl_23992] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_943 v h) (hints_cons _ _ _ (der_23992 v h) (by intro d hd; cases hd)))
def cl_23995 : CNF.NClause := [(76,true),(8,true),(1,false),(10,false),(17,false),(27,true)]
theorem der_23995 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23995 :=
  CNF.rup_sound cl_23995 [cl_947,cl_23991] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_947 v h) (hints_cons _ _ _ (der_23991 v h) (by intro d hd; cases hd)))
def cl_23996 : CNF.NClause := [(76,true),(8,true),(1,false),(10,true),(17,false),(27,true)]
theorem der_23996 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23996 :=
  CNF.rup_sound cl_23996 [cl_951,cl_23992] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_951 v h) (hints_cons _ _ _ (der_23992 v h) (by intro d hd; cases hd)))
def cl_23997 : CNF.NClause := [(76,true),(8,true),(1,false),(10,false),(17,true),(27,true)]
theorem der_23997 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23997 :=
  CNF.rup_sound cl_23997 [cl_955,cl_23993] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_955 v h) (hints_cons _ _ _ (der_23993 v h) (by intro d hd; cases hd)))
def cl_23998 : CNF.NClause := [(68,true),(20,false),(4,false),(29,false),(16,false),(12,true)]
theorem der_23998 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23998 :=
  CNF.rup_sound cl_23998 [cl_391,cl_389] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_391 v h) (hints_cons _ _ _ (inp_389 v h) (by intro d hd; cases hd)))
def cl_23999 : CNF.NClause := [(68,true),(20,false),(29,false),(12,true),(8,true),(16,false)]
theorem der_23999 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_23999 :=
  CNF.rup_sound cl_23999 [cl_392,cl_23998] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_392 v h) (hints_cons _ _ _ (der_23998 v h) (by intro d hd; cases hd)))
def cl_24000 : CNF.NClause := [(68,true),(8,true),(29,true),(16,false),(4,true),(20,false)]
theorem der_24000 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24000 :=
  CNF.rup_sound cl_24000 [cl_424,cl_23987] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_424 v h) (hints_cons _ _ _ (der_23987 v h) (by intro d hd; cases hd)))
def cl_24001 : CNF.NClause := [(79,true),(15,false),(21,false),(2,true),(8,true),(26,true)]
theorem der_24001 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24001 :=
  CNF.rup_sound cl_24001 [cl_1128,cl_23571] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1128 v h) (hints_cons _ _ _ (der_23571 v h) (by intro d hd; cases hd)))
def cl_24002 : CNF.NClause := [(74,true),(2,false),(10,false),(19,false),(23,false),(29,false)]
theorem der_24002 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24002 :=
  CNF.rup_sound cl_24002 [cl_771,cl_769] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_771 v h) (hints_cons _ _ _ (inp_769 v h) (by intro d hd; cases hd)))
def cl_24003 : CNF.NClause := [(74,true),(6,true),(2,false),(19,false),(23,false),(29,false)]
theorem der_24003 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24003 :=
  CNF.rup_sound cl_24003 [cl_775,cl_24002] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_775 v h) (hints_cons _ _ _ (der_24002 v h) (by intro d hd; cases hd)))
def cl_24004 : CNF.NClause := [(74,true),(6,true),(2,false),(10,false),(23,false),(29,false)]
theorem der_24004 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24004 :=
  CNF.rup_sound cl_24004 [cl_779,cl_24003] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_779 v h) (hints_cons _ _ _ (der_24003 v h) (by intro d hd; cases hd)))
def cl_24005 : CNF.NClause := [(74,true),(23,false),(2,false),(19,true),(6,true),(29,false)]
theorem der_24005 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24005 :=
  CNF.rup_sound cl_24005 [cl_783,cl_24004] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_783 v h) (hints_cons _ _ _ (der_24004 v h) (by intro d hd; cases hd)))
def cl_24006 : CNF.NClause := [(74,true),(6,true),(2,false),(10,false),(19,false),(29,false)]
theorem der_24006 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24006 :=
  CNF.rup_sound cl_24006 [cl_787,cl_24004] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_787 v h) (hints_cons _ _ _ (der_24004 v h) (by intro d hd; cases hd)))
def cl_24007 : CNF.NClause := [(74,true),(6,true),(2,false),(10,true),(19,false),(29,false)]
theorem der_24007 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24007 :=
  CNF.rup_sound cl_24007 [cl_791,cl_24003] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_791 v h) (hints_cons _ _ _ (der_24003 v h) (by intro d hd; cases hd)))
def cl_24008 : CNF.NClause := [(74,true),(6,true),(2,false),(10,false),(19,true),(29,false)]
theorem der_24008 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24008 :=
  CNF.rup_sound cl_24008 [cl_795,cl_24004] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_795 v h) (hints_cons _ _ _ (der_24004 v h) (by intro d hd; cases hd)))
def cl_24009 : CNF.NClause := [(74,true),(2,false),(10,true),(19,true),(6,true),(29,false)]
theorem der_24009 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24009 :=
  CNF.rup_sound cl_24009 [cl_799,cl_24005] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_799 v h) (hints_cons _ _ _ (der_24005 v h) (by intro d hd; cases hd)))
def cl_24010 : CNF.NClause := [(74,true),(6,true),(2,false),(10,false),(19,false),(23,false)]
theorem der_24010 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24010 :=
  CNF.rup_sound cl_24010 [cl_803,cl_24004] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_803 v h) (hints_cons _ _ _ (der_24004 v h) (by intro d hd; cases hd)))
def cl_24011 : CNF.NClause := [(74,true),(6,true),(2,false),(10,true),(19,false),(23,false)]
theorem der_24011 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24011 :=
  CNF.rup_sound cl_24011 [cl_807,cl_24003] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_807 v h) (hints_cons _ _ _ (der_24003 v h) (by intro d hd; cases hd)))
def cl_24012 : CNF.NClause := [(74,true),(6,true),(2,false),(10,false),(19,true),(23,false)]
theorem der_24012 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24012 :=
  CNF.rup_sound cl_24012 [cl_811,cl_24004] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_811 v h) (hints_cons _ _ _ (der_24004 v h) (by intro d hd; cases hd)))
def cl_24013 : CNF.NClause := [(74,true),(23,false),(2,false),(10,true),(19,true),(6,true)]
theorem der_24013 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24013 :=
  CNF.rup_sound cl_24013 [cl_815,cl_24009] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_815 v h) (hints_cons _ _ _ (der_24009 v h) (by intro d hd; cases hd)))
def cl_24014 : CNF.NClause := [(74,true),(6,true),(2,false),(10,false),(19,false),(23,true)]
theorem der_24014 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24014 :=
  CNF.rup_sound cl_24014 [cl_819,cl_24006] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_819 v h) (hints_cons _ _ _ (der_24006 v h) (by intro d hd; cases hd)))
def cl_24015 : CNF.NClause := [(74,true),(6,true),(2,false),(10,true),(19,false),(29,true)]
theorem der_24015 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24015 :=
  CNF.rup_sound cl_24015 [cl_823,cl_24011] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_823 v h) (hints_cons _ _ _ (der_24011 v h) (by intro d hd; cases hd)))
def cl_24016 : CNF.NClause := [(74,true),(6,true),(2,false),(10,false),(19,true),(29,true)]
theorem der_24016 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24016 :=
  CNF.rup_sound cl_24016 [cl_827,cl_24012] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_827 v h) (hints_cons _ _ _ (der_24012 v h) (by intro d hd; cases hd)))
def cl_24017 : CNF.NClause := [(70,true),(3,false),(14,false),(17,false),(20,false),(28,false)]
theorem der_24017 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24017 :=
  CNF.rup_sound cl_24017 [cl_515,cl_513] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_515 v h) (hints_cons _ _ _ (inp_513 v h) (by intro d hd; cases hd)))
def cl_24018 : CNF.NClause := [(70,true),(3,false),(14,true),(17,false),(20,false),(28,false)]
theorem der_24018 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24018 :=
  CNF.rup_sound cl_24018 [cl_519,cl_23612] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_519 v h) (hints_cons _ _ _ (der_23612 v h) (by intro d hd; cases hd)))
def cl_24019 : CNF.NClause := [(70,true),(6,true),(3,false),(14,false),(20,false),(28,false)]
theorem der_24019 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24019 :=
  CNF.rup_sound cl_24019 [cl_523,cl_24017] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_523 v h) (hints_cons _ _ _ (der_24017 v h) (by intro d hd; cases hd)))
def cl_24020 : CNF.NClause := [(70,true),(6,true),(3,false),(14,true),(20,false),(28,false)]
theorem der_24020 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24020 :=
  CNF.rup_sound cl_24020 [cl_527,cl_24018] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_527 v h) (hints_cons _ _ _ (der_24018 v h) (by intro d hd; cases hd)))
def cl_24021 : CNF.NClause := [(70,true),(6,true),(3,false),(14,false),(17,false),(28,false)]
theorem der_24021 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24021 :=
  CNF.rup_sound cl_24021 [cl_531,cl_24017] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_531 v h) (hints_cons _ _ _ (der_24017 v h) (by intro d hd; cases hd)))
def cl_24022 : CNF.NClause := [(70,true),(6,true),(3,false),(14,true),(17,false),(28,false)]
theorem der_24022 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24022 :=
  CNF.rup_sound cl_24022 [cl_535,cl_24018] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_535 v h) (hints_cons _ _ _ (der_24018 v h) (by intro d hd; cases hd)))
def cl_24023 : CNF.NClause := [(70,true),(6,true),(3,false),(14,false),(17,true),(28,false)]
theorem der_24023 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24023 :=
  CNF.rup_sound cl_24023 [cl_539,cl_24019] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_539 v h) (hints_cons _ _ _ (der_24019 v h) (by intro d hd; cases hd)))
def cl_24024 : CNF.NClause := [(70,true),(6,true),(3,false),(14,true),(17,true),(28,false)]
theorem der_24024 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24024 :=
  CNF.rup_sound cl_24024 [cl_543,cl_24020] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_543 v h) (hints_cons _ _ _ (der_24020 v h) (by intro d hd; cases hd)))
def cl_24025 : CNF.NClause := [(70,true),(6,true),(3,false),(14,false),(17,false),(20,false)]
theorem der_24025 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24025 :=
  CNF.rup_sound cl_24025 [cl_547,cl_24017] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_547 v h) (hints_cons _ _ _ (der_24017 v h) (by intro d hd; cases hd)))
def cl_24026 : CNF.NClause := [(70,true),(3,false),(14,true),(17,false),(20,false),(28,true)]
theorem der_24026 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24026 :=
  CNF.rup_sound cl_24026 [cl_551,cl_23613] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_551 v h) (hints_cons _ _ _ (der_23613 v h) (by intro d hd; cases hd)))
def cl_24027 : CNF.NClause := [(70,true),(6,true),(3,false),(14,false),(17,true),(20,false)]
theorem der_24027 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24027 :=
  CNF.rup_sound cl_24027 [cl_555,cl_24019] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_555 v h) (hints_cons _ _ _ (der_24019 v h) (by intro d hd; cases hd)))
def cl_24028 : CNF.NClause := [(70,true),(3,false),(14,true),(17,true),(20,false),(28,true)]
theorem der_24028 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24028 :=
  CNF.rup_sound cl_24028 [cl_559,cl_557] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_559 v h) (hints_cons _ _ _ (inp_557 v h) (by intro d hd; cases hd)))
def cl_24029 : CNF.NClause := [(70,true),(6,true),(3,false),(14,false),(17,false),(20,true)]
theorem der_24029 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24029 :=
  CNF.rup_sound cl_24029 [cl_563,cl_24021] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_563 v h) (hints_cons _ _ _ (der_24021 v h) (by intro d hd; cases hd)))
def cl_24030 : CNF.NClause := [(70,true),(3,false),(14,true),(17,false),(20,true),(28,true)]
theorem der_24030 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24030 :=
  CNF.rup_sound cl_24030 [cl_567,cl_23614] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_567 v h) (hints_cons _ _ _ (der_23614 v h) (by intro d hd; cases hd)))
def cl_24031 : CNF.NClause := [(70,true),(6,true),(3,false),(14,false),(17,true),(28,true)]
theorem der_24031 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24031 :=
  CNF.rup_sound cl_24031 [cl_571,cl_24027] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_571 v h) (hints_cons _ _ _ (der_24027 v h) (by intro d hd; cases hd)))
def cl_24032 : CNF.NClause := [(78,true),(4,false),(27,false),(15,false),(13,false),(22,false)]
theorem der_24032 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24032 :=
  CNF.rup_sound cl_24032 [cl_1027,cl_1025] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1027 v h) (hints_cons _ _ _ (inp_1025 v h) (by intro d hd; cases hd)))
def cl_24033 : CNF.NClause := [(78,true),(4,false),(6,true),(27,false),(22,false),(13,false)]
theorem der_24033 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24033 :=
  CNF.rup_sound cl_24033 [cl_1035,cl_24032] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1035 v h) (hints_cons _ _ _ (der_24032 v h) (by intro d hd; cases hd)))
def cl_24034 : CNF.NClause := [(78,true),(27,false),(4,false),(15,false),(13,false),(22,true)]
theorem der_24034 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24034 :=
  CNF.rup_sound cl_24034 [cl_1043,cl_23632] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1043 v h) (hints_cons _ _ _ (der_23632 v h) (by intro d hd; cases hd)))
def cl_24035 : CNF.NClause := [(78,true),(6,true),(4,false),(13,false),(27,false),(15,true)]
theorem der_24035 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24035 :=
  CNF.rup_sound cl_24035 [cl_1051,cl_24033] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1051 v h) (hints_cons _ _ _ (der_24033 v h) (by intro d hd; cases hd)))
def cl_24036 : CNF.NClause := [(78,true),(6,true),(4,false),(13,false),(22,false),(15,false)]
theorem der_24036 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24036 :=
  CNF.rup_sound cl_24036 [cl_1059,cl_24032] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1059 v h) (hints_cons _ _ _ (der_24032 v h) (by intro d hd; cases hd)))
def cl_24037 : CNF.NClause := [(78,true),(6,true),(22,false),(4,false),(13,false),(15,true)]
theorem der_24037 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24037 :=
  CNF.rup_sound cl_24037 [cl_1067,cl_24033] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1067 v h) (hints_cons _ _ _ (der_24033 v h) (by intro d hd; cases hd)))
def cl_24038 : CNF.NClause := [(78,true),(27,true),(4,false),(13,false),(22,true),(15,false)]
theorem der_24038 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24038 :=
  CNF.rup_sound cl_24038 [cl_1075,cl_1073] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1075 v h) (hints_cons _ _ _ (inp_1073 v h) (by intro d hd; cases hd)))
def cl_24039 : CNF.NClause := [(78,true),(6,true),(4,false),(15,true),(13,false),(22,true)]
theorem der_24039 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24039 :=
  CNF.rup_sound cl_24039 [cl_1083,cl_24035] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1083 v h) (hints_cons _ _ _ (der_24035 v h) (by intro d hd; cases hd)))
def cl_24040 : CNF.NClause := [(74,true),(6,true),(10,false),(19,false),(23,false),(29,false)]
theorem der_24040 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24040 :=
  CNF.rup_sound cl_24040 [cl_772,cl_24004] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_772 v h) (hints_cons _ _ _ (der_24004 v h) (by intro d hd; cases hd)))
def cl_24041 : CNF.NClause := [(74,true),(23,false),(2,true),(10,false),(19,true),(29,false)]
theorem der_24041 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24041 :=
  CNF.rup_sound cl_24041 [cl_780,cl_23552] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_780 v h) (hints_cons _ _ _ (der_23552 v h) (by intro d hd; cases hd)))
def cl_24042 : CNF.NClause := [(74,true),(6,true),(2,true),(10,false),(19,false),(29,false)]
theorem der_24042 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24042 :=
  CNF.rup_sound cl_24042 [cl_788,cl_24040] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_788 v h) (hints_cons _ _ _ (der_24040 v h) (by intro d hd; cases hd)))
def cl_24043 : CNF.NClause := [(74,true),(23,true),(2,true),(10,false),(19,true),(29,false)]
theorem der_24043 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24043 :=
  CNF.rup_sound cl_24043 [cl_796,cl_794] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_796 v h) (hints_cons _ _ _ (inp_794 v h) (by intro d hd; cases hd)))
def cl_24044 : CNF.NClause := [(74,true),(2,true),(10,false),(19,false),(23,false),(29,true)]
theorem der_24044 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24044 :=
  CNF.rup_sound cl_24044 [cl_804,cl_802] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_804 v h) (hints_cons _ _ _ (inp_802 v h) (by intro d hd; cases hd)))
def cl_24045 : CNF.NClause := [(74,true),(23,false),(2,true),(10,false),(19,true),(29,true)]
theorem der_24045 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24045 :=
  CNF.rup_sound cl_24045 [cl_812,cl_23525] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_812 v h) (hints_cons _ _ _ (der_23525 v h) (by intro d hd; cases hd)))
def cl_24046 : CNF.NClause := [(74,true),(2,true),(10,false),(19,false),(23,true),(29,true)]
theorem der_24046 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24046 :=
  CNF.rup_sound cl_24046 [cl_820,cl_23527] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_820 v h) (hints_cons _ _ _ (der_23527 v h) (by intro d hd; cases hd)))
def cl_24047 : CNF.NClause := [(78,true),(27,false),(13,false),(22,false),(6,true),(15,false)]
theorem der_24047 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24047 :=
  CNF.rup_sound cl_24047 [cl_1028,cl_24032] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1028 v h) (hints_cons _ _ _ (der_24032 v h) (by intro d hd; cases hd)))
def cl_24048 : CNF.NClause := [(78,true),(6,true),(15,false),(4,true),(22,false),(27,false)]
theorem der_24048 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24048 :=
  CNF.rup_sound cl_24048 [cl_1032,cl_24047] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1032 v h) (hints_cons _ _ _ (der_24047 v h) (by intro d hd; cases hd)))
def cl_24049 : CNF.NClause := [(78,true),(15,true),(13,false),(6,true),(22,false),(27,false)]
theorem der_24049 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24049 :=
  CNF.rup_sound cl_24049 [cl_1036,cl_24033] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1036 v h) (hints_cons _ _ _ (der_24033 v h) (by intro d hd; cases hd)))
def cl_24050 : CNF.NClause := [(78,true),(27,false),(4,true),(6,true),(15,true),(22,false)]
theorem der_24050 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24050 :=
  CNF.rup_sound cl_24050 [cl_1040,cl_24049] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1040 v h) (hints_cons _ _ _ (der_24049 v h) (by intro d hd; cases hd)))
def cl_24051 : CNF.NClause := [(78,true),(6,true),(22,true),(13,false),(15,false),(27,false)]
theorem der_24051 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24051 :=
  CNF.rup_sound cl_24051 [cl_1044,cl_24034] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1044 v h) (hints_cons _ _ _ (der_24034 v h) (by intro d hd; cases hd)))
def cl_24052 : CNF.NClause := [(78,true),(6,true),(15,false),(4,true),(22,true),(27,false)]
theorem der_24052 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24052 :=
  CNF.rup_sound cl_24052 [cl_1048,cl_24051] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1048 v h) (hints_cons _ _ _ (der_24051 v h) (by intro d hd; cases hd)))
def cl_24053 : CNF.NClause := [(78,true),(15,true),(13,false),(6,true),(22,true),(27,false)]
theorem der_24053 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24053 :=
  CNF.rup_sound cl_24053 [cl_1052,cl_24035] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1052 v h) (hints_cons _ _ _ (der_24035 v h) (by intro d hd; cases hd)))
def cl_24054 : CNF.NClause := [(78,true),(15,false),(27,true),(6,true),(13,false),(22,false)]
theorem der_24054 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24054 :=
  CNF.rup_sound cl_24054 [cl_1060,cl_24036] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1060 v h) (hints_cons _ _ _ (der_24036 v h) (by intro d hd; cases hd)))
def cl_24055 : CNF.NClause := [(78,true),(13,true),(6,true),(4,true),(22,false),(15,false)]
theorem der_24055 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24055 :=
  CNF.rup_sound cl_24055 [cl_1064,cl_24048] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1064 v h) (hints_cons _ _ _ (der_24048 v h) (by intro d hd; cases hd)))
def cl_24056 : CNF.NClause := [(78,true),(15,true),(4,true),(13,false),(22,false),(6,true)]
theorem der_24056 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24056 :=
  CNF.rup_sound cl_24056 [cl_1068,cl_24049] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1068 v h) (hints_cons _ _ _ (der_24049 v h) (by intro d hd; cases hd)))
def cl_24057 : CNF.NClause := [(78,true),(27,true),(15,false),(22,true),(6,true),(13,false)]
theorem der_24057 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24057 :=
  CNF.rup_sound cl_24057 [cl_1076,cl_24038] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1076 v h) (hints_cons _ _ _ (der_24038 v h) (by intro d hd; cases hd)))
def cl_24058 : CNF.NClause := [(70,true),(20,false),(6,true),(28,false),(14,true),(17,false)]
theorem der_24058 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24058 :=
  CNF.rup_sound cl_24058 [cl_520,cl_24018] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_520 v h) (hints_cons _ _ _ (der_24018 v h) (by intro d hd; cases hd)))
def cl_24059 : CNF.NClause := [(70,true),(20,false),(6,true),(28,false),(14,true),(17,true)]
theorem der_24059 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24059 :=
  CNF.rup_sound cl_24059 [cl_528,cl_24020] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_528 v h) (hints_cons _ _ _ (der_24020 v h) (by intro d hd; cases hd)))
def cl_24060 : CNF.NClause := [(70,true),(6,true),(14,true),(20,true),(28,false),(17,false)]
theorem der_24060 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24060 :=
  CNF.rup_sound cl_24060 [cl_536,cl_24022] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_536 v h) (hints_cons _ _ _ (der_24022 v h) (by intro d hd; cases hd)))
def cl_24061 : CNF.NClause := [(70,true),(3,true),(6,true),(14,true),(20,false),(17,false)]
theorem der_24061 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24061 :=
  CNF.rup_sound cl_24061 [cl_552,cl_24058] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_552 v h) (hints_cons _ _ _ (der_24058 v h) (by intro d hd; cases hd)))
def cl_24062 : CNF.NClause := [(86,true),(14,true),(1,false),(18,false),(22,false),(29,false)]
theorem der_24062 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24062 :=
  CNF.rup_sound cl_24062 [cl_1543,cl_1541] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1543 v h) (hints_cons _ _ _ (inp_1541 v h) (by intro d hd; cases hd)))
def cl_24063 : CNF.NClause := [(86,true),(5,true),(14,false),(1,false),(22,false),(29,false)]
theorem der_24063 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24063 :=
  CNF.rup_sound cl_24063 [cl_1547,cl_1539] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1547 v h) (hints_cons _ _ _ (inp_1539 v h) (by intro d hd; cases hd)))
def cl_24064 : CNF.NClause := [(86,true),(14,true),(1,false),(18,true),(22,false),(29,false)]
theorem der_24064 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24064 :=
  CNF.rup_sound cl_24064 [cl_1551,cl_23608] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1551 v h) (hints_cons _ _ _ (der_23608 v h) (by intro d hd; cases hd)))
def cl_24065 : CNF.NClause := [(86,true),(5,true),(14,false),(1,false),(18,false),(29,false)]
theorem der_24065 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24065 :=
  CNF.rup_sound cl_24065 [cl_1555,cl_1539] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1555 v h) (hints_cons _ _ _ (inp_1539 v h) (by intro d hd; cases hd)))
def cl_24066 : CNF.NClause := [(86,true),(14,true),(1,false),(18,false),(22,true),(29,false)]
theorem der_24066 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24066 :=
  CNF.rup_sound cl_24066 [cl_1559,cl_23607] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1559 v h) (hints_cons _ _ _ (der_23607 v h) (by intro d hd; cases hd)))
def cl_24067 : CNF.NClause := [(86,true),(5,true),(14,false),(1,false),(18,true),(29,false)]
theorem der_24067 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24067 :=
  CNF.rup_sound cl_24067 [cl_1563,cl_24063] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1563 v h) (hints_cons _ _ _ (der_24063 v h) (by intro d hd; cases hd)))
def cl_24068 : CNF.NClause := [(86,true),(14,true),(1,false),(18,true),(22,true),(29,false)]
theorem der_24068 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24068 :=
  CNF.rup_sound cl_24068 [cl_1567,cl_23609] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1567 v h) (hints_cons _ _ _ (der_23609 v h) (by intro d hd; cases hd)))
def cl_24069 : CNF.NClause := [(86,true),(5,true),(14,false),(1,false),(18,false),(22,false)]
theorem der_24069 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24069 :=
  CNF.rup_sound cl_24069 [cl_1571,cl_1539] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1571 v h) (hints_cons _ _ _ (inp_1539 v h) (by intro d hd; cases hd)))
def cl_24070 : CNF.NClause := [(86,true),(5,true),(1,false),(18,false),(14,true),(22,false)]
theorem der_24070 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24070 :=
  CNF.rup_sound cl_24070 [cl_1575,cl_24062] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1575 v h) (hints_cons _ _ _ (der_24062 v h) (by intro d hd; cases hd)))
def cl_24071 : CNF.NClause := [(86,true),(5,true),(14,false),(1,false),(18,true),(22,false)]
theorem der_24071 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24071 :=
  CNF.rup_sound cl_24071 [cl_1579,cl_24063] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1579 v h) (hints_cons _ _ _ (der_24063 v h) (by intro d hd; cases hd)))
def cl_24072 : CNF.NClause := [(86,true),(29,true),(1,false),(14,true),(18,true),(22,false)]
theorem der_24072 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24072 :=
  CNF.rup_sound cl_24072 [cl_1583,cl_1581] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1583 v h) (hints_cons _ _ _ (inp_1581 v h) (by intro d hd; cases hd)))
def cl_24073 : CNF.NClause := [(86,true),(5,true),(14,false),(1,false),(18,false),(22,true)]
theorem der_24073 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24073 :=
  CNF.rup_sound cl_24073 [cl_1587,cl_24065] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1587 v h) (hints_cons _ _ _ (der_24065 v h) (by intro d hd; cases hd)))
def cl_24074 : CNF.NClause := [(86,true),(5,true),(14,true),(1,false),(18,false),(29,true)]
theorem der_24074 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24074 :=
  CNF.rup_sound cl_24074 [cl_1591,cl_24070] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1591 v h) (hints_cons _ _ _ (der_24070 v h) (by intro d hd; cases hd)))
def cl_24075 : CNF.NClause := [(86,true),(5,true),(14,false),(1,false),(18,true),(22,true)]
theorem der_24075 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24075 :=
  CNF.rup_sound cl_24075 [cl_1595,cl_24067] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1595 v h) (hints_cons _ _ _ (der_24067 v h) (by intro d hd; cases hd)))
def cl_24076 : CNF.NClause := [(84,true),(2,false),(13,false),(16,false),(24,false),(28,false)]
theorem der_24076 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24076 :=
  CNF.rup_sound cl_24076 [cl_1411,cl_23616] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1411 v h) (hints_cons _ _ _ (der_23616 v h) (by intro d hd; cases hd)))
def cl_24077 : CNF.NClause := [(84,true),(28,false),(2,false),(5,true),(16,false),(24,false)]
theorem der_24077 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24077 :=
  CNF.rup_sound cl_24077 [cl_1415,cl_24076] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1415 v h) (hints_cons _ _ _ (der_24076 v h) (by intro d hd; cases hd)))
def cl_24078 : CNF.NClause := [(84,true),(16,true),(2,false),(13,false),(24,false),(28,false)]
theorem der_24078 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24078 :=
  CNF.rup_sound cl_24078 [cl_1419,cl_23626] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1419 v h) (hints_cons _ _ _ (der_23626 v h) (by intro d hd; cases hd)))
def cl_24079 : CNF.NClause := [(84,true),(16,true),(2,false),(5,true),(24,false),(28,false)]
theorem der_24079 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24079 :=
  CNF.rup_sound cl_24079 [cl_1423,cl_24078] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1423 v h) (hints_cons _ _ _ (der_24078 v h) (by intro d hd; cases hd)))
def cl_24080 : CNF.NClause := [(84,true),(5,true),(2,false),(13,false),(16,false),(28,false)]
theorem der_24080 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24080 :=
  CNF.rup_sound cl_24080 [cl_1427,cl_24076] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1427 v h) (hints_cons _ _ _ (der_24076 v h) (by intro d hd; cases hd)))
def cl_24081 : CNF.NClause := [(84,true),(28,false),(2,false),(5,true),(24,true),(16,false)]
theorem der_24081 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24081 :=
  CNF.rup_sound cl_24081 [cl_1431,cl_24080] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1431 v h) (hints_cons _ _ _ (der_24080 v h) (by intro d hd; cases hd)))
def cl_24082 : CNF.NClause := [(84,true),(16,true),(2,false),(13,false),(24,true),(28,false)]
theorem der_24082 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24082 :=
  CNF.rup_sound cl_24082 [cl_1435,cl_23626] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1435 v h) (hints_cons _ _ _ (der_23626 v h) (by intro d hd; cases hd)))
def cl_24083 : CNF.NClause := [(84,true),(16,true),(2,false),(5,true),(13,true),(28,false)]
theorem der_24083 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24083 :=
  CNF.rup_sound cl_24083 [cl_1439,cl_24079] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1439 v h) (hints_cons _ _ _ (der_24079 v h) (by intro d hd; cases hd)))
def cl_24084 : CNF.NClause := [(84,true),(5,true),(2,false),(13,false),(16,false),(24,false)]
theorem der_24084 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24084 :=
  CNF.rup_sound cl_24084 [cl_1443,cl_24076] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1443 v h) (hints_cons _ _ _ (der_24076 v h) (by intro d hd; cases hd)))
def cl_24085 : CNF.NClause := [(84,true),(28,true),(2,false),(5,true),(16,false),(24,false)]
theorem der_24085 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24085 :=
  CNF.rup_sound cl_24085 [cl_1447,cl_24084] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1447 v h) (hints_cons _ _ _ (der_24084 v h) (by intro d hd; cases hd)))
def cl_24086 : CNF.NClause := [(84,true),(16,true),(2,false),(13,false),(5,true),(24,false)]
theorem der_24086 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24086 :=
  CNF.rup_sound cl_24086 [cl_1451,cl_24079] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1451 v h) (hints_cons _ _ _ (der_24079 v h) (by intro d hd; cases hd)))
def cl_24087 : CNF.NClause := [(84,true),(16,true),(2,false),(5,true),(13,true),(24,false)]
theorem der_24087 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24087 :=
  CNF.rup_sound cl_24087 [cl_1455,cl_24079] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1455 v h) (hints_cons _ _ _ (der_24079 v h) (by intro d hd; cases hd)))
def cl_24088 : CNF.NClause := [(84,true),(16,false),(2,false),(13,false),(5,true),(24,true)]
theorem der_24088 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24088 :=
  CNF.rup_sound cl_24088 [cl_1459,cl_24080] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1459 v h) (hints_cons _ _ _ (der_24080 v h) (by intro d hd; cases hd)))
def cl_24089 : CNF.NClause := [(84,true),(2,false),(5,true),(16,false),(24,true),(28,true)]
theorem der_24089 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24089 :=
  CNF.rup_sound cl_24089 [cl_1463,cl_24088] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1463 v h) (hints_cons _ _ _ (der_24088 v h) (by intro d hd; cases hd)))
def cl_24090 : CNF.NClause := [(84,true),(2,false),(5,true),(13,false),(24,true),(28,true)]
theorem der_24090 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24090 :=
  CNF.rup_sound cl_24090 [cl_1467,cl_24088] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1467 v h) (hints_cons _ _ _ (der_24088 v h) (by intro d hd; cases hd)))
def cl_24091 : CNF.NClause := [(85,true),(27,false),(3,false),(5,true),(19,false),(21,false)]
theorem der_24091 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24091 :=
  CNF.rup_sound cl_24091 [cl_1479,cl_1475] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1479 v h) (hints_cons _ _ _ (inp_1475 v h) (by intro d hd; cases hd)))
def cl_24092 : CNF.NClause := [(85,true),(3,false),(12,false),(27,false),(5,true),(21,false)]
theorem der_24092 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24092 :=
  CNF.rup_sound cl_24092 [cl_1483,cl_1475] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1483 v h) (hints_cons _ _ _ (inp_1475 v h) (by intro d hd; cases hd)))
def cl_24093 : CNF.NClause := [(85,true),(27,false),(3,false),(21,false),(5,true),(12,true)]
theorem der_24093 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24093 :=
  CNF.rup_sound cl_24093 [cl_1487,cl_24091] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1487 v h) (hints_cons _ _ _ (der_24091 v h) (by intro d hd; cases hd)))
def cl_24094 : CNF.NClause := [(85,true),(12,false),(3,false),(19,false),(21,true),(27,false)]
theorem der_24094 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24094 :=
  CNF.rup_sound cl_24094 [cl_1491,cl_23648] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1491 v h) (hints_cons _ _ _ (der_23648 v h) (by intro d hd; cases hd)))
def cl_24095 : CNF.NClause := [(85,true),(27,false),(3,false),(19,false),(12,true),(21,true)]
theorem der_24095 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24095 :=
  CNF.rup_sound cl_24095 [cl_1495,cl_1493] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1495 v h) (hints_cons _ _ _ (inp_1493 v h) (by intro d hd; cases hd)))
def cl_24096 : CNF.NClause := [(85,true),(3,false),(12,false),(27,false),(19,true),(5,true)]
theorem der_24096 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24096 :=
  CNF.rup_sound cl_24096 [cl_1499,cl_24092] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1499 v h) (hints_cons _ _ _ (der_24092 v h) (by intro d hd; cases hd)))
def cl_24097 : CNF.NClause := [(85,true),(27,false),(3,false),(21,true),(19,true),(12,true)]
theorem der_24097 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24097 :=
  CNF.rup_sound cl_24097 [cl_1503,cl_23644] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1503 v h) (hints_cons _ _ _ (der_23644 v h) (by intro d hd; cases hd)))
def cl_24098 : CNF.NClause := [(85,true),(12,false),(3,false),(19,false),(21,false),(27,true)]
theorem der_24098 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24098 :=
  CNF.rup_sound cl_24098 [cl_1507,cl_1505] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1507 v h) (hints_cons _ _ _ (inp_1505 v h) (by intro d hd; cases hd)))
def cl_24099 : CNF.NClause := [(85,true),(12,true),(3,false),(5,true),(19,false),(21,false)]
theorem der_24099 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24099 :=
  CNF.rup_sound cl_24099 [cl_1511,cl_24091] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1511 v h) (hints_cons _ _ _ (der_24091 v h) (by intro d hd; cases hd)))
def cl_24100 : CNF.NClause := [(85,true),(3,false),(12,false),(19,true),(5,true),(21,false)]
theorem der_24100 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24100 :=
  CNF.rup_sound cl_24100 [cl_1515,cl_24096] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1515 v h) (hints_cons _ _ _ (der_24096 v h) (by intro d hd; cases hd)))
def cl_24101 : CNF.NClause := [(85,true),(12,true),(21,false),(3,false),(5,true),(27,true)]
theorem der_24101 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24101 :=
  CNF.rup_sound cl_24101 [cl_1519,cl_24099] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1519 v h) (hints_cons _ _ _ (der_24099 v h) (by intro d hd; cases hd)))
def cl_24102 : CNF.NClause := [(85,true),(12,false),(3,false),(19,false),(21,true),(27,true)]
theorem der_24102 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24102 :=
  CNF.rup_sound cl_24102 [cl_1523,cl_23649] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1523 v h) (hints_cons _ _ _ (der_23649 v h) (by intro d hd; cases hd)))
def cl_24103 : CNF.NClause := [(85,true),(27,true),(3,false),(19,false),(12,true),(21,true)]
theorem der_24103 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24103 :=
  CNF.rup_sound cl_24103 [cl_1527,cl_23601] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1527 v h) (hints_cons _ _ _ (der_23601 v h) (by intro d hd; cases hd)))
def cl_24104 : CNF.NClause := [(85,true),(21,true),(3,false),(12,false),(19,true),(27,true)]
theorem der_24104 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24104 :=
  CNF.rup_sound cl_24104 [cl_1531,cl_23654] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1531 v h) (hints_cons _ _ _ (der_23654 v h) (by intro d hd; cases hd)))
def cl_24105 : CNF.NClause := [(83,true),(11,true),(4,false),(5,true),(23,false),(17,false)]
theorem der_24105 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24105 :=
  CNF.rup_sound cl_24105 [cl_1351,cl_1383] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1351 v h) (hints_cons _ _ _ (inp_1383 v h) (by intro d hd; cases hd)))
def cl_24106 : CNF.NClause := [(84,true),(28,false),(2,true),(13,false),(16,false),(24,false)]
theorem der_24106 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24106 :=
  CNF.rup_sound cl_24106 [cl_1412,cl_1410] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1412 v h) (hints_cons _ _ _ (inp_1410 v h) (by intro d hd; cases hd)))
def cl_24107 : CNF.NClause := [(84,true),(28,false),(5,true),(24,false),(16,true),(13,false)]
theorem der_24107 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24107 :=
  CNF.rup_sound cl_24107 [cl_1420,cl_24079] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1420 v h) (hints_cons _ _ _ (der_24079 v h) (by intro d hd; cases hd)))
def cl_24108 : CNF.NClause := [(84,true),(24,true),(2,true),(13,false),(16,false),(28,false)]
theorem der_24108 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24108 :=
  CNF.rup_sound cl_24108 [cl_1428,cl_23615] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1428 v h) (hints_cons _ _ _ (der_23615 v h) (by intro d hd; cases hd)))
def cl_24109 : CNF.NClause := [(84,true),(28,false),(24,true),(2,true),(13,false),(16,true)]
theorem der_24109 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24109 :=
  CNF.rup_sound cl_24109 [cl_1436,cl_23630] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1436 v h) (hints_cons _ _ _ (der_23630 v h) (by intro d hd; cases hd)))
def cl_24110 : CNF.NClause := [(84,true),(28,true),(2,true),(13,false),(16,false),(24,false)]
theorem der_24110 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24110 :=
  CNF.rup_sound cl_24110 [cl_1444,cl_23617] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1444 v h) (hints_cons _ _ _ (der_23617 v h) (by intro d hd; cases hd)))
def cl_24111 : CNF.NClause := [(84,true),(28,true),(2,true),(24,false),(16,true),(13,false)]
theorem der_24111 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24111 :=
  CNF.rup_sound cl_24111 [cl_1452,cl_23618] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1452 v h) (hints_cons _ _ _ (der_23618 v h) (by intro d hd; cases hd)))
def cl_24112 : CNF.NClause := [(84,true),(13,false),(2,true),(16,false),(28,true),(24,true)]
theorem der_24112 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24112 :=
  CNF.rup_sound cl_24112 [cl_1460,cl_23619] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1460 v h) (hints_cons _ _ _ (der_23619 v h) (by intro d hd; cases hd)))
def cl_24113 : CNF.NClause := [(85,true),(12,false),(19,false),(5,true),(27,false),(21,false)]
theorem der_24113 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24113 :=
  CNF.rup_sound cl_24113 [cl_1476,cl_1475] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1476 v h) (hints_cons _ _ _ (inp_1475 v h) (by intro d hd; cases hd)))
def cl_24114 : CNF.NClause := [(85,true),(5,true),(27,false),(12,false),(19,true),(21,false)]
theorem der_24114 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24114 :=
  CNF.rup_sound cl_24114 [cl_1484,cl_24096] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1484 v h) (hints_cons _ _ _ (der_24096 v h) (by intro d hd; cases hd)))
def cl_24115 : CNF.NClause := [(85,true),(21,true),(5,true),(12,false),(27,false),(19,false)]
theorem der_24115 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24115 :=
  CNF.rup_sound cl_24115 [cl_1492,cl_24094] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1492 v h) (hints_cons _ _ _ (der_24094 v h) (by intro d hd; cases hd)))
def cl_24116 : CNF.NClause := [(85,true),(5,true),(27,false),(12,false),(19,true),(21,true)]
theorem der_24116 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24116 :=
  CNF.rup_sound cl_24116 [cl_1500,cl_24096] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1500 v h) (hints_cons _ _ _ (der_24096 v h) (by intro d hd; cases hd)))
def cl_24117 : CNF.NClause := [(85,true),(12,false),(21,false),(5,true),(27,true),(19,false)]
theorem der_24117 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24117 :=
  CNF.rup_sound cl_24117 [cl_1508,cl_24098] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1508 v h) (hints_cons _ _ _ (der_24098 v h) (by intro d hd; cases hd)))
def cl_24118 : CNF.NClause := [(85,true),(12,false),(5,true),(21,false),(19,true),(3,true)]
theorem der_24118 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24118 :=
  CNF.rup_sound cl_24118 [cl_1516,cl_24114] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1516 v h) (hints_cons _ _ _ (der_24114 v h) (by intro d hd; cases hd)))
def cl_24119 : CNF.NClause := [(85,true),(3,true),(5,true),(12,false),(27,true),(19,false)]
theorem der_24119 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24119 :=
  CNF.rup_sound cl_24119 [cl_1524,cl_24117] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1524 v h) (hints_cons _ _ _ (der_24117 v h) (by intro d hd; cases hd)))
def cl_24120 : CNF.NClause := [(83,true),(26,false),(4,false),(11,false),(23,false),(17,false)]
theorem der_24120 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24120 :=
  CNF.rup_sound cl_24120 [cl_1347,cl_23611] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1347 v h) (hints_cons _ _ _ (der_23611 v h) (by intro d hd; cases hd)))
def cl_24121 : CNF.NClause := [(83,true),(5,true),(11,false),(4,false),(26,false),(23,false)]
theorem der_24121 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24121 :=
  CNF.rup_sound cl_24121 [cl_1355,cl_24120] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1355 v h) (hints_cons _ _ _ (der_24120 v h) (by intro d hd; cases hd)))
def cl_24122 : CNF.NClause := [(83,true),(5,true),(4,false),(11,false),(26,false),(17,false)]
theorem der_24122 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24122 :=
  CNF.rup_sound cl_24122 [cl_1363,cl_24120] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1363 v h) (hints_cons _ _ _ (der_24120 v h) (by intro d hd; cases hd)))
def cl_24123 : CNF.NClause := [(83,true),(23,true),(4,false),(11,false),(5,true),(26,false)]
theorem der_24123 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24123 :=
  CNF.rup_sound cl_24123 [cl_1371,cl_24122] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1371 v h) (hints_cons _ _ _ (der_24122 v h) (by intro d hd; cases hd)))
def cl_24124 : CNF.NClause := [(83,true),(4,false),(11,false),(17,false),(23,false),(26,true)]
theorem der_24124 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24124 :=
  CNF.rup_sound cl_24124 [cl_1379,cl_23611] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1379 v h) (hints_cons _ _ _ (der_23611 v h) (by intro d hd; cases hd)))
def cl_24125 : CNF.NClause := [(83,true),(5,true),(4,false),(11,false),(17,true),(23,false)]
theorem der_24125 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24125 :=
  CNF.rup_sound cl_24125 [cl_1387,cl_24121] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1387 v h) (hints_cons _ _ _ (der_24121 v h) (by intro d hd; cases hd)))
def cl_24126 : CNF.NClause := [(83,true),(5,true),(4,false),(11,false),(23,true),(17,false)]
theorem der_24126 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24126 :=
  CNF.rup_sound cl_24126 [cl_1395,cl_24122] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1395 v h) (hints_cons _ _ _ (der_24122 v h) (by intro d hd; cases hd)))
def cl_24127 : CNF.NClause := [(83,true),(5,true),(4,false),(11,false),(17,true),(26,true)]
theorem der_24127 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24127 :=
  CNF.rup_sound cl_24127 [cl_1403,cl_24125] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1403 v h) (hints_cons _ _ _ (der_24125 v h) (by intro d hd; cases hd)))
def cl_24128 : CNF.NClause := [(83,true),(5,true),(26,false),(11,false),(17,false),(23,false)]
theorem der_24128 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24128 :=
  CNF.rup_sound cl_24128 [cl_1348,cl_24120] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1348 v h) (hints_cons _ _ _ (der_24120 v h) (by intro d hd; cases hd)))
def cl_24129 : CNF.NClause := [(83,true),(17,false),(11,true),(23,false),(4,true),(26,false)]
theorem der_24129 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24129 :=
  CNF.rup_sound cl_24129 [cl_1352,cl_1350] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1352 v h) (hints_cons _ _ _ (inp_1350 v h) (by intro d hd; cases hd)))
def cl_24130 : CNF.NClause := [(83,true),(5,true),(11,false),(17,true),(23,false),(26,false)]
theorem der_24130 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24130 :=
  CNF.rup_sound cl_24130 [cl_1356,cl_24125] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1356 v h) (hints_cons _ _ _ (der_24125 v h) (by intro d hd; cases hd)))
def cl_24131 : CNF.NClause := [(83,true),(17,true),(4,true),(11,true),(23,false),(26,false)]
theorem der_24131 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24131 :=
  CNF.rup_sound cl_24131 [cl_1360,cl_23530] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1360 v h) (hints_cons _ _ _ (der_23530 v h) (by intro d hd; cases hd)))
def cl_24132 : CNF.NClause := [(83,true),(17,false),(26,false),(11,false),(23,true),(5,true)]
theorem der_24132 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24132 :=
  CNF.rup_sound cl_24132 [cl_1364,cl_24122] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1364 v h) (hints_cons _ _ _ (der_24122 v h) (by intro d hd; cases hd)))
def cl_24133 : CNF.NClause := [(83,true),(23,true),(26,false),(4,true),(17,false),(11,true)]
theorem der_24133 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24133 :=
  CNF.rup_sound cl_24133 [cl_1368,cl_23531] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1368 v h) (hints_cons _ _ _ (der_23531 v h) (by intro d hd; cases hd)))
def cl_24134 : CNF.NClause := [(83,true),(5,true),(26,false),(11,false),(4,true),(23,true)]
theorem der_24134 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24134 :=
  CNF.rup_sound cl_24134 [cl_1372,cl_24132] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1372 v h) (hints_cons _ _ _ (der_24132 v h) (by intro d hd; cases hd)))
def cl_24135 : CNF.NClause := [(83,true),(26,true),(23,false),(17,false),(11,false),(4,true)]
theorem der_24135 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24135 :=
  CNF.rup_sound cl_24135 [cl_1380,cl_1378] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1380 v h) (hints_cons _ _ _ (inp_1378 v h) (by intro d hd; cases hd)))
def cl_24136 : CNF.NClause := [(83,true),(17,false),(26,true),(4,true),(5,true),(23,false)]
theorem der_24136 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24136 :=
  CNF.rup_sound cl_24136 [cl_1384,cl_24135] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1384 v h) (hints_cons _ _ _ (der_24135 v h) (by intro d hd; cases hd)))
def cl_24137 : CNF.NClause := [(83,true),(5,true),(26,true),(23,false),(17,true),(11,false)]
theorem der_24137 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24137 :=
  CNF.rup_sound cl_24137 [cl_1388,cl_24125] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1388 v h) (hints_cons _ _ _ (der_24125 v h) (by intro d hd; cases hd)))
def cl_24138 : CNF.NClause := [(83,true),(17,false),(26,true),(5,true),(4,true),(11,false)]
theorem der_24138 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24138 :=
  CNF.rup_sound cl_24138 [cl_1396,cl_24136] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1396 v h) (hints_cons _ _ _ (der_24136 v h) (by intro d hd; cases hd)))
def cl_24139 : CNF.NClause := [(86,true),(29,false),(5,true),(14,true),(18,false),(22,false)]
theorem der_24139 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24139 :=
  CNF.rup_sound cl_24139 [cl_1544,cl_24062] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1544 v h) (hints_cons _ _ _ (der_24062 v h) (by intro d hd; cases hd)))
def cl_24140 : CNF.NClause := [(86,true),(22,false),(29,false),(5,true),(14,true),(18,true)]
theorem der_24140 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24140 :=
  CNF.rup_sound cl_24140 [cl_1552,cl_24064] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1552 v h) (hints_cons _ _ _ (der_24064 v h) (by intro d hd; cases hd)))
def cl_24141 : CNF.NClause := [(86,true),(22,true),(29,false),(5,true),(18,false),(14,true)]
theorem der_24141 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24141 :=
  CNF.rup_sound cl_24141 [cl_1560,cl_24066] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1560 v h) (hints_cons _ _ _ (der_24066 v h) (by intro d hd; cases hd)))
def cl_24142 : CNF.NClause := [(86,true),(29,true),(22,false),(14,true),(5,true),(18,false)]
theorem der_24142 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24142 :=
  CNF.rup_sound cl_24142 [cl_1576,cl_24070] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1576 v h) (hints_cons _ _ _ (der_24070 v h) (by intro d hd; cases hd)))
def cl_24143 : CNF.NClause := [(61,false),(67,false),(62,false),(87,false),(82,true),(72,false)]
theorem der_24143 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24143 :=
  CNF.rup_sound cl_24143 [cl_15569,cl_15577] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15569 v h) (hints_cons _ _ _ (der_15577 v h) (by intro d hd; cases hd)))
def cl_24144 : CNF.NClause := [(61,false),(82,true),(87,true),(72,false),(62,false),(67,false)]
theorem der_24144 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24144 :=
  CNF.rup_sound cl_24144 [cl_15601,cl_23683] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15601 v h) (hints_cons _ _ _ (der_23683 v h) (by intro d hd; cases hd)))
def cl_24145 : CNF.NClause := [(61,false),(62,true),(67,false),(72,false),(77,false),(87,false)]
theorem der_24145 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24145 :=
  CNF.rup_sound cl_24145 [cl_15570,cl_23689] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15570 v h) (hints_cons _ _ _ (der_23689 v h) (by intro d hd; cases hd)))
def cl_24146 : CNF.NClause := [(61,false),(87,true),(62,true),(72,false),(77,false),(67,false)]
theorem der_24146 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24146 :=
  CNF.rup_sound cl_24146 [cl_15602,cl_15586] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15602 v h) (hints_cons _ _ _ (der_15586 v h) (by intro d hd; cases hd)))
def cl_24147 : CNF.NClause := [(80,true),(3,false),(7,true),(15,false),(24,false),(29,false)]
theorem der_24147 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24147 :=
  CNF.rup_sound cl_24147 [cl_1159,cl_14718] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1159 v h) (hints_cons _ _ _ (der_14718 v h) (by intro d hd; cases hd)))
def cl_24148 : CNF.NClause := [(80,true),(3,false),(7,true),(11,false),(24,false),(29,false)]
theorem der_24148 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24148 :=
  CNF.rup_sound cl_24148 [cl_1163,cl_14718] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1163 v h) (hints_cons _ _ _ (der_14718 v h) (by intro d hd; cases hd)))
def cl_24149 : CNF.NClause := [(80,true),(3,false),(7,true),(11,true),(24,false),(29,false)]
theorem der_24149 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24149 :=
  CNF.rup_sound cl_24149 [cl_1167,cl_24147] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1167 v h) (hints_cons _ _ _ (der_24147 v h) (by intro d hd; cases hd)))
def cl_24150 : CNF.NClause := [(80,true),(3,false),(7,true),(11,false),(15,false),(29,false)]
theorem der_24150 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24150 :=
  CNF.rup_sound cl_24150 [cl_1171,cl_14718] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1171 v h) (hints_cons _ _ _ (der_14718 v h) (by intro d hd; cases hd)))
def cl_24151 : CNF.NClause := [(80,true),(3,false),(7,true),(11,true),(15,false),(29,false)]
theorem der_24151 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24151 :=
  CNF.rup_sound cl_24151 [cl_1175,cl_24147] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1175 v h) (hints_cons _ _ _ (der_24147 v h) (by intro d hd; cases hd)))
def cl_24152 : CNF.NClause := [(80,true),(3,false),(7,true),(11,false),(15,true),(29,false)]
theorem der_24152 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24152 :=
  CNF.rup_sound cl_24152 [cl_1179,cl_24148] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1179 v h) (hints_cons _ _ _ (der_24148 v h) (by intro d hd; cases hd)))
def cl_24153 : CNF.NClause := [(80,true),(3,false),(7,true),(11,true),(15,true),(29,false)]
theorem der_24153 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24153 :=
  CNF.rup_sound cl_24153 [cl_1183,cl_24149] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1183 v h) (hints_cons _ _ _ (der_24149 v h) (by intro d hd; cases hd)))
def cl_24154 : CNF.NClause := [(80,true),(3,false),(7,true),(11,false),(15,false),(24,false)]
theorem der_24154 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24154 :=
  CNF.rup_sound cl_24154 [cl_1187,cl_14718] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1187 v h) (hints_cons _ _ _ (der_14718 v h) (by intro d hd; cases hd)))
def cl_24155 : CNF.NClause := [(80,true),(3,false),(7,true),(11,true),(15,false),(24,false)]
theorem der_24155 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24155 :=
  CNF.rup_sound cl_24155 [cl_1191,cl_24147] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1191 v h) (hints_cons _ _ _ (der_24147 v h) (by intro d hd; cases hd)))
def cl_24156 : CNF.NClause := [(80,true),(3,false),(7,true),(11,false),(15,true),(24,false)]
theorem der_24156 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24156 :=
  CNF.rup_sound cl_24156 [cl_1195,cl_24148] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1195 v h) (hints_cons _ _ _ (der_24148 v h) (by intro d hd; cases hd)))
def cl_24157 : CNF.NClause := [(80,true),(3,false),(7,true),(11,true),(15,true),(24,false)]
theorem der_24157 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24157 :=
  CNF.rup_sound cl_24157 [cl_1199,cl_24149] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1199 v h) (hints_cons _ _ _ (der_24149 v h) (by intro d hd; cases hd)))
def cl_24158 : CNF.NClause := [(80,true),(3,false),(7,true),(11,false),(15,false),(24,true)]
theorem der_24158 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24158 :=
  CNF.rup_sound cl_24158 [cl_1203,cl_24150] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1203 v h) (hints_cons _ _ _ (der_24150 v h) (by intro d hd; cases hd)))
def cl_24159 : CNF.NClause := [(80,true),(3,false),(7,true),(11,true),(15,false),(24,true)]
theorem der_24159 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24159 :=
  CNF.rup_sound cl_24159 [cl_1207,cl_24151] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1207 v h) (hints_cons _ _ _ (der_24151 v h) (by intro d hd; cases hd)))
def cl_24160 : CNF.NClause := [(80,true),(3,false),(7,true),(11,false),(15,true),(24,true)]
theorem der_24160 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24160 :=
  CNF.rup_sound cl_24160 [cl_1211,cl_24152] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1211 v h) (hints_cons _ _ _ (der_24152 v h) (by intro d hd; cases hd)))
def cl_24161 : CNF.NClause := [(71,true),(20,false),(1,false),(19,true),(13,false),(7,true)]
theorem der_24161 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24161 :=
  CNF.rup_sound cl_24161 [cl_619,cl_23241] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_619 v h) (hints_cons _ _ _ (der_23241 v h) (by intro d hd; cases hd)))
def cl_24162 : CNF.NClause := [(71,true),(13,true),(1,false),(19,true),(20,false),(7,true)]
theorem der_24162 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24162 :=
  CNF.rup_sound cl_24162 [cl_623,cl_23465] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_623 v h) (hints_cons _ _ _ (der_23465 v h) (by intro d hd; cases hd)))
def cl_24163 : CNF.NClause := [(71,true),(13,false),(1,false),(19,false),(7,true),(20,true)]
theorem der_24163 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24163 :=
  CNF.rup_sound cl_24163 [cl_627,cl_23598] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_627 v h) (hints_cons _ _ _ (der_23598 v h) (by intro d hd; cases hd)))
def cl_24164 : CNF.NClause := [(71,true),(26,true),(1,false),(19,false),(7,true),(20,true)]
theorem der_24164 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24164 :=
  CNF.rup_sound cl_24164 [cl_631,cl_24163] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_631 v h) (hints_cons _ _ _ (der_24163 v h) (by intro d hd; cases hd)))
def cl_24165 : CNF.NClause := [(71,true),(26,true),(1,false),(7,true),(19,true),(13,false)]
theorem der_24165 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24165 :=
  CNF.rup_sound cl_24165 [cl_635,cl_24161] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_635 v h) (hints_cons _ _ _ (der_24161 v h) (by intro d hd; cases hd)))
def cl_24166 : CNF.NClause := [(73,true),(28,true),(10,false),(18,true),(21,false),(7,true)]
theorem der_24166 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24166 :=
  CNF.rup_sound cl_24166 [cl_748,cl_23589] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_748 v h) (hints_cons _ _ _ (der_23589 v h) (by intro d hd; cases hd)))
def cl_24167 : CNF.NClause := [(68,true),(29,false),(4,false),(8,false),(16,false),(20,true)]
theorem der_24167 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24167 :=
  CNF.rup_sound cl_24167 [cl_401,cl_23516] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_401 v h) (hints_cons _ _ _ (der_23516 v h) (by intro d hd; cases hd)))
def cl_24168 : CNF.NClause := [(68,true),(16,false),(4,false),(12,false),(29,true),(20,true)]
theorem der_24168 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24168 :=
  CNF.rup_sound cl_24168 [cl_433,cl_23980] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_433 v h) (hints_cons _ _ _ (der_23980 v h) (by intro d hd; cases hd)))
def cl_24169 : CNF.NClause := [(70,true),(6,true),(17,false),(28,false),(20,true),(14,false)]
theorem der_24169 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24169 :=
  CNF.rup_sound cl_24169 [cl_532,cl_24021] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_532 v h) (hints_cons _ _ _ (der_24021 v h) (by intro d hd; cases hd)))
def cl_24170 : CNF.NClause := [(70,true),(14,false),(3,true),(17,false),(20,true),(6,true)]
theorem der_24170 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24170 :=
  CNF.rup_sound cl_24170 [cl_564,cl_24169] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_564 v h) (hints_cons _ _ _ (der_24169 v h) (by intro d hd; cases hd)))
def cl_24171 : CNF.NClause := [(70,true),(17,false),(28,false),(6,false),(3,false),(14,false)]
theorem der_24171 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24171 :=
  CNF.rup_sound cl_24171 [cl_529,cl_513] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_529 v h) (hints_cons _ _ _ (inp_513 v h) (by intro d hd; cases hd)))
def cl_24172 : CNF.NClause := [(70,true),(17,false),(28,true),(6,false),(3,false),(20,true)]
theorem der_24172 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24172 :=
  CNF.rup_sound cl_24172 [cl_561,cl_23614] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_561 v h) (hints_cons _ _ _ (der_23614 v h) (by intro d hd; cases hd)))
def cl_24173 : CNF.NClause := [(69,true),(11,false),(2,true),(27,false),(9,false),(20,true)]
theorem der_24173 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24173 :=
  CNF.rup_sound cl_24173 [cl_466,cl_23580] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_466 v h) (hints_cons _ _ _ (der_23580 v h) (by intro d hd; cases hd)))
def cl_24174 : CNF.NClause := [(69,true),(2,true),(9,false),(11,false),(18,false),(20,true)]
theorem der_24174 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24174 :=
  CNF.rup_sound cl_24174 [cl_498,cl_24173] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_498 v h) (hints_cons _ _ _ (der_24173 v h) (by intro d hd; cases hd)))
def cl_24175 : CNF.NClause := [(69,true),(27,false),(11,false),(9,false),(18,false),(20,true)]
theorem der_24175 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24175 :=
  CNF.rup_sound cl_24175 [cl_465,cl_24173] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_465 v h) (hints_cons _ _ _ (der_24173 v h) (by intro d hd; cases hd)))
def cl_24176 : CNF.NClause := [(69,true),(18,false),(9,false),(2,false),(11,false),(20,true)]
theorem der_24176 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24176 :=
  CNF.rup_sound cl_24176 [cl_497,cl_24175] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_497 v h) (hints_cons _ _ _ (der_24175 v h) (by intro d hd; cases hd)))
def cl_24177 : CNF.NClause := [(71,true),(13,false),(1,false),(7,false),(26,false),(19,false)]
theorem der_24177 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_24177 :=
  CNF.rup_sound cl_24177 [cl_593,cl_14714] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_593 v h) (hints_cons _ _ _ (der_14714 v h) (by intro d hd; cases hd)))
def chunk003 : List CNF.NClause := [cl_23670,cl_23671,cl_23672,cl_23673,cl_23674,cl_23675,cl_23676,cl_23677,cl_23678,cl_23679,cl_23680,cl_23681,cl_23682,cl_23683,cl_23684,cl_23685,cl_23686,cl_23687,cl_23688,cl_23689,cl_23690,cl_23691,cl_23692,cl_23693,cl_23694,cl_23695,cl_23696,cl_23697,cl_23698,cl_23699,cl_23700,cl_23701,cl_23702,cl_23703,cl_23704,cl_23705,cl_23706,cl_23707,cl_23708,cl_23709,cl_23710,cl_23711,cl_23712,cl_23713,cl_23714,cl_23715,cl_23716,cl_23717,cl_23718,cl_23719,cl_23720,cl_23721,cl_23722,cl_23723,cl_23724,cl_23725,cl_23726,cl_23727,cl_23728,cl_23729,cl_23730,cl_23731,cl_23732,cl_23733,cl_23734,cl_23735,cl_23736,cl_23737,cl_23738,cl_23739,cl_23740,cl_23741,cl_23742,cl_23743,cl_23744,cl_23745,cl_23746,cl_23747,cl_23748,cl_23749,cl_23750,cl_23751,cl_23752,cl_23753,cl_23754,cl_23755,cl_23756,cl_23757,cl_23758,cl_23759,cl_23760,cl_23761,cl_23762,cl_23763,cl_23764,cl_23765,cl_23766,cl_23767,cl_23768,cl_23769,cl_23770,cl_23771,cl_23772,cl_23773,cl_23774,cl_23775,cl_23776,cl_23777,cl_23778,cl_23779,cl_23780,cl_23781,cl_23782,cl_23783,cl_23784,cl_23785,cl_23786,cl_23788,cl_23790,cl_23791,cl_23792,cl_23793,cl_23794,cl_23795,cl_23796,cl_23797,cl_23798,cl_23799,cl_23800,cl_23801,cl_23802,cl_23803,cl_23804,cl_23805,cl_23806,cl_23807,cl_23808,cl_23809,cl_23810,cl_23811,cl_23812,cl_23813,cl_23814,cl_23815,cl_23816,cl_23817,cl_23818,cl_23819,cl_23820,cl_23821,cl_23822,cl_23823,cl_23824,cl_23825,cl_23826,cl_23827,cl_23828,cl_23829,cl_23830,cl_23831,cl_23832,cl_23833,cl_23834,cl_23835,cl_23836,cl_23837,cl_23838,cl_23839,cl_23840,cl_23841,cl_23842,cl_23843,cl_23844,cl_23845,cl_23846,cl_23847,cl_23848,cl_23849,cl_23850,cl_23851,cl_23853,cl_23854,cl_23855,cl_23856,cl_23857,cl_23858,cl_23859,cl_23860,cl_23861,cl_23862,cl_23863,cl_23864,cl_23865,cl_23866,cl_23867,cl_23868,cl_23869,cl_23870,cl_23871,cl_23873,cl_23874,cl_23875,cl_23876,cl_23877,cl_23878,cl_23879,cl_23880,cl_23881,cl_23882,cl_23883,cl_23884,cl_23885,cl_23886,cl_23887,cl_23888,cl_23889,cl_23890,cl_23891,cl_23892,cl_23893,cl_23894,cl_23895,cl_23896,cl_23897,cl_23898,cl_23899,cl_23900,cl_23901,cl_23902,cl_23903,cl_23904,cl_23905,cl_23906,cl_23907,cl_23908,cl_23909,cl_23910,cl_23911,cl_23912,cl_23913,cl_23914,cl_23915,cl_23916,cl_23917,cl_23918,cl_23919,cl_23920,cl_23921,cl_23922,cl_23923,cl_23924,cl_23925,cl_23926,cl_23927,cl_23928,cl_23929,cl_23931,cl_23933,cl_23934,cl_23935,cl_23936,cl_23937,cl_23938,cl_23939,cl_23940,cl_23941,cl_23943,cl_23944,cl_23945,cl_23946,cl_23947,cl_23948,cl_23949,cl_23950,cl_23951,cl_23952,cl_23953,cl_23954,cl_23955,cl_23956,cl_23957,cl_23958,cl_23959,cl_23961,cl_23962,cl_23963,cl_23964,cl_23965,cl_23966,cl_23967,cl_23968,cl_23969,cl_23970,cl_23971,cl_23972,cl_23973,cl_23974,cl_23975,cl_23976,cl_23977,cl_23978,cl_23979,cl_23980,cl_23981,cl_23982,cl_23983,cl_23984,cl_23985,cl_23986,cl_23987,cl_23988,cl_23989,cl_23990,cl_23991,cl_23992,cl_23993,cl_23994,cl_23995,cl_23996,cl_23997,cl_23998,cl_23999,cl_24000,cl_24001,cl_24002,cl_24003,cl_24004,cl_24005,cl_24006,cl_24007,cl_24008,cl_24009,cl_24010,cl_24011,cl_24012,cl_24013,cl_24014,cl_24015,cl_24016,cl_24017,cl_24018,cl_24019,cl_24020,cl_24021,cl_24022,cl_24023,cl_24024,cl_24025,cl_24026,cl_24027,cl_24028,cl_24029,cl_24030,cl_24031,cl_24032,cl_24033,cl_24034,cl_24035,cl_24036,cl_24037,cl_24038,cl_24039,cl_24040,cl_24041,cl_24042,cl_24043,cl_24044,cl_24045,cl_24046,cl_24047,cl_24048,cl_24049,cl_24050,cl_24051,cl_24052,cl_24053,cl_24054,cl_24055,cl_24056,cl_24057,cl_24058,cl_24059,cl_24060,cl_24061,cl_24062,cl_24063,cl_24064,cl_24065,cl_24066,cl_24067,cl_24068,cl_24069,cl_24070,cl_24071,cl_24072,cl_24073,cl_24074,cl_24075,cl_24076,cl_24077,cl_24078,cl_24079,cl_24080,cl_24081,cl_24082,cl_24083,cl_24084,cl_24085,cl_24086,cl_24087,cl_24088,cl_24089,cl_24090,cl_24091,cl_24092,cl_24093,cl_24094,cl_24095,cl_24096,cl_24097,cl_24098,cl_24099,cl_24100,cl_24101,cl_24102,cl_24103,cl_24104,cl_24105,cl_24106,cl_24107,cl_24108,cl_24109,cl_24110,cl_24111,cl_24112,cl_24113,cl_24114,cl_24115,cl_24116,cl_24117,cl_24118,cl_24119,cl_24120,cl_24121,cl_24122,cl_24123,cl_24124,cl_24125,cl_24126,cl_24127,cl_24128,cl_24129,cl_24130,cl_24131,cl_24132,cl_24133,cl_24134,cl_24135,cl_24136,cl_24137,cl_24138,cl_24139,cl_24140,cl_24141,cl_24142,cl_24143,cl_24144,cl_24145,cl_24146,cl_24147,cl_24148,cl_24149,cl_24150,cl_24151,cl_24152,cl_24153,cl_24154,cl_24155,cl_24156,cl_24157,cl_24158,cl_24159,cl_24160,cl_24161,cl_24162,cl_24163,cl_24164,cl_24165,cl_24166,cl_24167,cl_24168,cl_24169,cl_24170,cl_24171,cl_24172,cl_24173,cl_24174,cl_24175,cl_24176,cl_24177]
theorem chunk_sound003 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : ∀ c ∈ chunk003, CNF.Holds (v ∘ decodeVar) c :=
  (hints_cons _ _ _ (der_23670 v h) (hints_cons _ _ _ (der_23671 v h) (hints_cons _ _ _ (der_23672 v h) (hints_cons _ _ _ (der_23673 v h) (hints_cons _ _ _ (der_23674 v h) (hints_cons _ _ _ (der_23675 v h) (hints_cons _ _ _ (der_23676 v h) (hints_cons _ _ _ (der_23677 v h) (hints_cons _ _ _ (der_23678 v h) (hints_cons _ _ _ (der_23679 v h) (hints_cons _ _ _ (der_23680 v h) (hints_cons _ _ _ (der_23681 v h) (hints_cons _ _ _ (der_23682 v h) (hints_cons _ _ _ (der_23683 v h) (hints_cons _ _ _ (der_23684 v h) (hints_cons _ _ _ (der_23685 v h) (hints_cons _ _ _ (der_23686 v h) (hints_cons _ _ _ (der_23687 v h) (hints_cons _ _ _ (der_23688 v h) (hints_cons _ _ _ (der_23689 v h) (hints_cons _ _ _ (der_23690 v h) (hints_cons _ _ _ (der_23691 v h) (hints_cons _ _ _ (der_23692 v h) (hints_cons _ _ _ (der_23693 v h) (hints_cons _ _ _ (der_23694 v h) (hints_cons _ _ _ (der_23695 v h) (hints_cons _ _ _ (der_23696 v h) (hints_cons _ _ _ (der_23697 v h) (hints_cons _ _ _ (der_23698 v h) (hints_cons _ _ _ (der_23699 v h) (hints_cons _ _ _ (der_23700 v h) (hints_cons _ _ _ (der_23701 v h) (hints_cons _ _ _ (der_23702 v h) (hints_cons _ _ _ (der_23703 v h) (hints_cons _ _ _ (der_23704 v h) (hints_cons _ _ _ (der_23705 v h) (hints_cons _ _ _ (der_23706 v h) (hints_cons _ _ _ (der_23707 v h) (hints_cons _ _ _ (der_23708 v h) (hints_cons _ _ _ (der_23709 v h) (hints_cons _ _ _ (der_23710 v h) (hints_cons _ _ _ (der_23711 v h) (hints_cons _ _ _ (der_23712 v h) (hints_cons _ _ _ (der_23713 v h) (hints_cons _ _ _ (der_23714 v h) (hints_cons _ _ _ (der_23715 v h) (hints_cons _ _ _ (der_23716 v h) (hints_cons _ _ _ (der_23717 v h) (hints_cons _ _ _ (der_23718 v h) (hints_cons _ _ _ (der_23719 v h) (hints_cons _ _ _ (der_23720 v h) (hints_cons _ _ _ (der_23721 v h) (hints_cons _ _ _ (der_23722 v h) (hints_cons _ _ _ (der_23723 v h) (hints_cons _ _ _ (der_23724 v h) (hints_cons _ _ _ (der_23725 v h) (hints_cons _ _ _ (der_23726 v h) (hints_cons _ _ _ (der_23727 v h) (hints_cons _ _ _ (der_23728 v h) (hints_cons _ _ _ (der_23729 v h) (hints_cons _ _ _ (der_23730 v h) (hints_cons _ _ _ (der_23731 v h) (hints_cons _ _ _ (der_23732 v h) (hints_cons _ _ _ (der_23733 v h) (hints_cons _ _ _ (der_23734 v h) (hints_cons _ _ _ (der_23735 v h) (hints_cons _ _ _ (der_23736 v h) (hints_cons _ _ _ (der_23737 v h) (hints_cons _ _ _ (der_23738 v h) (hints_cons _ _ _ (der_23739 v h) (hints_cons _ _ _ (der_23740 v h) (hints_cons _ _ _ (der_23741 v h) (hints_cons _ _ _ (der_23742 v h) (hints_cons _ _ _ (der_23743 v h) (hints_cons _ _ _ (der_23744 v h) (hints_cons _ _ _ (der_23745 v h) (hints_cons _ _ _ (der_23746 v h) (hints_cons _ _ _ (der_23747 v h) (hints_cons _ _ _ (der_23748 v h) (hints_cons _ _ _ (der_23749 v h) (hints_cons _ _ _ (der_23750 v h) (hints_cons _ _ _ (der_23751 v h) (hints_cons _ _ _ (der_23752 v h) (hints_cons _ _ _ (der_23753 v h) (hints_cons _ _ _ (der_23754 v h) (hints_cons _ _ _ (der_23755 v h) (hints_cons _ _ _ (der_23756 v h) (hints_cons _ _ _ (der_23757 v h) (hints_cons _ _ _ (der_23758 v h) (hints_cons _ _ _ (der_23759 v h) (hints_cons _ _ _ (der_23760 v h) (hints_cons _ _ _ (der_23761 v h) (hints_cons _ _ _ (der_23762 v h) (hints_cons _ _ _ (der_23763 v h) (hints_cons _ _ _ (der_23764 v h) (hints_cons _ _ _ (der_23765 v h) (hints_cons _ _ _ (der_23766 v h) (hints_cons _ _ _ (der_23767 v h) (hints_cons _ _ _ (der_23768 v h) (hints_cons _ _ _ (der_23769 v h) (hints_cons _ _ _ (der_23770 v h) (hints_cons _ _ _ (der_23771 v h) (hints_cons _ _ _ (der_23772 v h) (hints_cons _ _ _ (der_23773 v h) (hints_cons _ _ _ (der_23774 v h) (hints_cons _ _ _ (der_23775 v h) (hints_cons _ _ _ (der_23776 v h) (hints_cons _ _ _ (der_23777 v h) (hints_cons _ _ _ (der_23778 v h) (hints_cons _ _ _ (der_23779 v h) (hints_cons _ _ _ (der_23780 v h) (hints_cons _ _ _ (der_23781 v h) (hints_cons _ _ _ (der_23782 v h) (hints_cons _ _ _ (der_23783 v h) (hints_cons _ _ _ (der_23784 v h) (hints_cons _ _ _ (der_23785 v h) (hints_cons _ _ _ (der_23786 v h) (hints_cons _ _ _ (der_23788 v h) (hints_cons _ _ _ (der_23790 v h) (hints_cons _ _ _ (der_23791 v h) (hints_cons _ _ _ (der_23792 v h) (hints_cons _ _ _ (der_23793 v h) (hints_cons _ _ _ (der_23794 v h) (hints_cons _ _ _ (der_23795 v h) (hints_cons _ _ _ (der_23796 v h) (hints_cons _ _ _ (der_23797 v h) (hints_cons _ _ _ (der_23798 v h) (hints_cons _ _ _ (der_23799 v h) (hints_cons _ _ _ (der_23800 v h) (hints_cons _ _ _ (der_23801 v h) (hints_cons _ _ _ (der_23802 v h) (hints_cons _ _ _ (der_23803 v h) (hints_cons _ _ _ (der_23804 v h) (hints_cons _ _ _ (der_23805 v h) (hints_cons _ _ _ (der_23806 v h) (hints_cons _ _ _ (der_23807 v h) (hints_cons _ _ _ (der_23808 v h) (hints_cons _ _ _ (der_23809 v h) (hints_cons _ _ _ (der_23810 v h) (hints_cons _ _ _ (der_23811 v h) (hints_cons _ _ _ (der_23812 v h) (hints_cons _ _ _ (der_23813 v h) (hints_cons _ _ _ (der_23814 v h) (hints_cons _ _ _ (der_23815 v h) (hints_cons _ _ _ (der_23816 v h) (hints_cons _ _ _ (der_23817 v h) (hints_cons _ _ _ (der_23818 v h) (hints_cons _ _ _ (der_23819 v h) (hints_cons _ _ _ (der_23820 v h) (hints_cons _ _ _ (der_23821 v h) (hints_cons _ _ _ (der_23822 v h) (hints_cons _ _ _ (der_23823 v h) (hints_cons _ _ _ (der_23824 v h) (hints_cons _ _ _ (der_23825 v h) (hints_cons _ _ _ (der_23826 v h) (hints_cons _ _ _ (der_23827 v h) (hints_cons _ _ _ (der_23828 v h) (hints_cons _ _ _ (der_23829 v h) (hints_cons _ _ _ (der_23830 v h) (hints_cons _ _ _ (der_23831 v h) (hints_cons _ _ _ (der_23832 v h) (hints_cons _ _ _ (der_23833 v h) (hints_cons _ _ _ (der_23834 v h) (hints_cons _ _ _ (der_23835 v h) (hints_cons _ _ _ (der_23836 v h) (hints_cons _ _ _ (der_23837 v h) (hints_cons _ _ _ (der_23838 v h) (hints_cons _ _ _ (der_23839 v h) (hints_cons _ _ _ (der_23840 v h) (hints_cons _ _ _ (der_23841 v h) (hints_cons _ _ _ (der_23842 v h) (hints_cons _ _ _ (der_23843 v h) (hints_cons _ _ _ (der_23844 v h) (hints_cons _ _ _ (der_23845 v h) (hints_cons _ _ _ (der_23846 v h) (hints_cons _ _ _ (der_23847 v h) (hints_cons _ _ _ (der_23848 v h) (hints_cons _ _ _ (der_23849 v h) (hints_cons _ _ _ (der_23850 v h) (hints_cons _ _ _ (der_23851 v h) (hints_cons _ _ _ (der_23853 v h) (hints_cons _ _ _ (der_23854 v h) (hints_cons _ _ _ (der_23855 v h) (hints_cons _ _ _ (der_23856 v h) (hints_cons _ _ _ (der_23857 v h) (hints_cons _ _ _ (der_23858 v h) (hints_cons _ _ _ (der_23859 v h) (hints_cons _ _ _ (der_23860 v h) (hints_cons _ _ _ (der_23861 v h) (hints_cons _ _ _ (der_23862 v h) (hints_cons _ _ _ (der_23863 v h) (hints_cons _ _ _ (der_23864 v h) (hints_cons _ _ _ (der_23865 v h) (hints_cons _ _ _ (der_23866 v h) (hints_cons _ _ _ (der_23867 v h) (hints_cons _ _ _ (der_23868 v h) (hints_cons _ _ _ (der_23869 v h) (hints_cons _ _ _ (der_23870 v h) (hints_cons _ _ _ (der_23871 v h) (hints_cons _ _ _ (der_23873 v h) (hints_cons _ _ _ (der_23874 v h) (hints_cons _ _ _ (der_23875 v h) (hints_cons _ _ _ (der_23876 v h) (hints_cons _ _ _ (der_23877 v h) (hints_cons _ _ _ (der_23878 v h) (hints_cons _ _ _ (der_23879 v h) (hints_cons _ _ _ (der_23880 v h) (hints_cons _ _ _ (der_23881 v h) (hints_cons _ _ _ (der_23882 v h) (hints_cons _ _ _ (der_23883 v h) (hints_cons _ _ _ (der_23884 v h) (hints_cons _ _ _ (der_23885 v h) (hints_cons _ _ _ (der_23886 v h) (hints_cons _ _ _ (der_23887 v h) (hints_cons _ _ _ (der_23888 v h) (hints_cons _ _ _ (der_23889 v h) (hints_cons _ _ _ (der_23890 v h) (hints_cons _ _ _ (der_23891 v h) (hints_cons _ _ _ (der_23892 v h) (hints_cons _ _ _ (der_23893 v h) (hints_cons _ _ _ (der_23894 v h) (hints_cons _ _ _ (der_23895 v h) (hints_cons _ _ _ (der_23896 v h) (hints_cons _ _ _ (der_23897 v h) (hints_cons _ _ _ (der_23898 v h) (hints_cons _ _ _ (der_23899 v h) (hints_cons _ _ _ (der_23900 v h) (hints_cons _ _ _ (der_23901 v h) (hints_cons _ _ _ (der_23902 v h) (hints_cons _ _ _ (der_23903 v h) (hints_cons _ _ _ (der_23904 v h) (hints_cons _ _ _ (der_23905 v h) (hints_cons _ _ _ (der_23906 v h) (hints_cons _ _ _ (der_23907 v h) (hints_cons _ _ _ (der_23908 v h) (hints_cons _ _ _ (der_23909 v h) (hints_cons _ _ _ (der_23910 v h) (hints_cons _ _ _ (der_23911 v h) (hints_cons _ _ _ (der_23912 v h) (hints_cons _ _ _ (der_23913 v h) (hints_cons _ _ _ (der_23914 v h) (hints_cons _ _ _ (der_23915 v h) (hints_cons _ _ _ (der_23916 v h) (hints_cons _ _ _ (der_23917 v h) (hints_cons _ _ _ (der_23918 v h) (hints_cons _ _ _ (der_23919 v h) (hints_cons _ _ _ (der_23920 v h) (hints_cons _ _ _ (der_23921 v h) (hints_cons _ _ _ (der_23922 v h) (hints_cons _ _ _ (der_23923 v h) (hints_cons _ _ _ (der_23924 v h) (hints_cons _ _ _ (der_23925 v h) (hints_cons _ _ _ (der_23926 v h) (hints_cons _ _ _ (der_23927 v h) (hints_cons _ _ _ (der_23928 v h) (hints_cons _ _ _ (der_23929 v h) (hints_cons _ _ _ (der_23931 v h) (hints_cons _ _ _ (der_23933 v h) (hints_cons _ _ _ (der_23934 v h) (hints_cons _ _ _ (der_23935 v h) (hints_cons _ _ _ (der_23936 v h) (hints_cons _ _ _ (der_23937 v h) (hints_cons _ _ _ (der_23938 v h) (hints_cons _ _ _ (der_23939 v h) (hints_cons _ _ _ (der_23940 v h) (hints_cons _ _ _ (der_23941 v h) (hints_cons _ _ _ (der_23943 v h) (hints_cons _ _ _ (der_23944 v h) (hints_cons _ _ _ (der_23945 v h) (hints_cons _ _ _ (der_23946 v h) (hints_cons _ _ _ (der_23947 v h) (hints_cons _ _ _ (der_23948 v h) (hints_cons _ _ _ (der_23949 v h) (hints_cons _ _ _ (der_23950 v h) (hints_cons _ _ _ (der_23951 v h) (hints_cons _ _ _ (der_23952 v h) (hints_cons _ _ _ (der_23953 v h) (hints_cons _ _ _ (der_23954 v h) (hints_cons _ _ _ (der_23955 v h) (hints_cons _ _ _ (der_23956 v h) (hints_cons _ _ _ (der_23957 v h) (hints_cons _ _ _ (der_23958 v h) (hints_cons _ _ _ (der_23959 v h) (hints_cons _ _ _ (der_23961 v h) (hints_cons _ _ _ (der_23962 v h) (hints_cons _ _ _ (der_23963 v h) (hints_cons _ _ _ (der_23964 v h) (hints_cons _ _ _ (der_23965 v h) (hints_cons _ _ _ (der_23966 v h) (hints_cons _ _ _ (der_23967 v h) (hints_cons _ _ _ (der_23968 v h) (hints_cons _ _ _ (der_23969 v h) (hints_cons _ _ _ (der_23970 v h) (hints_cons _ _ _ (der_23971 v h) (hints_cons _ _ _ (der_23972 v h) (hints_cons _ _ _ (der_23973 v h) (hints_cons _ _ _ (der_23974 v h) (hints_cons _ _ _ (der_23975 v h) (hints_cons _ _ _ (der_23976 v h) (hints_cons _ _ _ (der_23977 v h) (hints_cons _ _ _ (der_23978 v h) (hints_cons _ _ _ (der_23979 v h) (hints_cons _ _ _ (der_23980 v h) (hints_cons _ _ _ (der_23981 v h) (hints_cons _ _ _ (der_23982 v h) (hints_cons _ _ _ (der_23983 v h) (hints_cons _ _ _ (der_23984 v h) (hints_cons _ _ _ (der_23985 v h) (hints_cons _ _ _ (der_23986 v h) (hints_cons _ _ _ (der_23987 v h) (hints_cons _ _ _ (der_23988 v h) (hints_cons _ _ _ (der_23989 v h) (hints_cons _ _ _ (der_23990 v h) (hints_cons _ _ _ (der_23991 v h) (hints_cons _ _ _ (der_23992 v h) (hints_cons _ _ _ (der_23993 v h) (hints_cons _ _ _ (der_23994 v h) (hints_cons _ _ _ (der_23995 v h) (hints_cons _ _ _ (der_23996 v h) (hints_cons _ _ _ (der_23997 v h) (hints_cons _ _ _ (der_23998 v h) (hints_cons _ _ _ (der_23999 v h) (hints_cons _ _ _ (der_24000 v h) (hints_cons _ _ _ (der_24001 v h) (hints_cons _ _ _ (der_24002 v h) (hints_cons _ _ _ (der_24003 v h) (hints_cons _ _ _ (der_24004 v h) (hints_cons _ _ _ (der_24005 v h) (hints_cons _ _ _ (der_24006 v h) (hints_cons _ _ _ (der_24007 v h) (hints_cons _ _ _ (der_24008 v h) (hints_cons _ _ _ (der_24009 v h) (hints_cons _ _ _ (der_24010 v h) (hints_cons _ _ _ (der_24011 v h) (hints_cons _ _ _ (der_24012 v h) (hints_cons _ _ _ (der_24013 v h) (hints_cons _ _ _ (der_24014 v h) (hints_cons _ _ _ (der_24015 v h) (hints_cons _ _ _ (der_24016 v h) (hints_cons _ _ _ (der_24017 v h) (hints_cons _ _ _ (der_24018 v h) (hints_cons _ _ _ (der_24019 v h) (hints_cons _ _ _ (der_24020 v h) (hints_cons _ _ _ (der_24021 v h) (hints_cons _ _ _ (der_24022 v h) (hints_cons _ _ _ (der_24023 v h) (hints_cons _ _ _ (der_24024 v h) (hints_cons _ _ _ (der_24025 v h) (hints_cons _ _ _ (der_24026 v h) (hints_cons _ _ _ (der_24027 v h) (hints_cons _ _ _ (der_24028 v h) (hints_cons _ _ _ (der_24029 v h) (hints_cons _ _ _ (der_24030 v h) (hints_cons _ _ _ (der_24031 v h) (hints_cons _ _ _ (der_24032 v h) (hints_cons _ _ _ (der_24033 v h) (hints_cons _ _ _ (der_24034 v h) (hints_cons _ _ _ (der_24035 v h) (hints_cons _ _ _ (der_24036 v h) (hints_cons _ _ _ (der_24037 v h) (hints_cons _ _ _ (der_24038 v h) (hints_cons _ _ _ (der_24039 v h) (hints_cons _ _ _ (der_24040 v h) (hints_cons _ _ _ (der_24041 v h) (hints_cons _ _ _ (der_24042 v h) (hints_cons _ _ _ (der_24043 v h) (hints_cons _ _ _ (der_24044 v h) (hints_cons _ _ _ (der_24045 v h) (hints_cons _ _ _ (der_24046 v h) (hints_cons _ _ _ (der_24047 v h) (hints_cons _ _ _ (der_24048 v h) (hints_cons _ _ _ (der_24049 v h) (hints_cons _ _ _ (der_24050 v h) (hints_cons _ _ _ (der_24051 v h) (hints_cons _ _ _ (der_24052 v h) (hints_cons _ _ _ (der_24053 v h) (hints_cons _ _ _ (der_24054 v h) (hints_cons _ _ _ (der_24055 v h) (hints_cons _ _ _ (der_24056 v h) (hints_cons _ _ _ (der_24057 v h) (hints_cons _ _ _ (der_24058 v h) (hints_cons _ _ _ (der_24059 v h) (hints_cons _ _ _ (der_24060 v h) (hints_cons _ _ _ (der_24061 v h) (hints_cons _ _ _ (der_24062 v h) (hints_cons _ _ _ (der_24063 v h) (hints_cons _ _ _ (der_24064 v h) (hints_cons _ _ _ (der_24065 v h) (hints_cons _ _ _ (der_24066 v h) (hints_cons _ _ _ (der_24067 v h) (hints_cons _ _ _ (der_24068 v h) (hints_cons _ _ _ (der_24069 v h) (hints_cons _ _ _ (der_24070 v h) (hints_cons _ _ _ (der_24071 v h) (hints_cons _ _ _ (der_24072 v h) (hints_cons _ _ _ (der_24073 v h) (hints_cons _ _ _ (der_24074 v h) (hints_cons _ _ _ (der_24075 v h) (hints_cons _ _ _ (der_24076 v h) (hints_cons _ _ _ (der_24077 v h) (hints_cons _ _ _ (der_24078 v h) (hints_cons _ _ _ (der_24079 v h) (hints_cons _ _ _ (der_24080 v h) (hints_cons _ _ _ (der_24081 v h) (hints_cons _ _ _ (der_24082 v h) (hints_cons _ _ _ (der_24083 v h) (hints_cons _ _ _ (der_24084 v h) (hints_cons _ _ _ (der_24085 v h) (hints_cons _ _ _ (der_24086 v h) (hints_cons _ _ _ (der_24087 v h) (hints_cons _ _ _ (der_24088 v h) (hints_cons _ _ _ (der_24089 v h) (hints_cons _ _ _ (der_24090 v h) (hints_cons _ _ _ (der_24091 v h) (hints_cons _ _ _ (der_24092 v h) (hints_cons _ _ _ (der_24093 v h) (hints_cons _ _ _ (der_24094 v h) (hints_cons _ _ _ (der_24095 v h) (hints_cons _ _ _ (der_24096 v h) (hints_cons _ _ _ (der_24097 v h) (hints_cons _ _ _ (der_24098 v h) (hints_cons _ _ _ (der_24099 v h) (hints_cons _ _ _ (der_24100 v h) (hints_cons _ _ _ (der_24101 v h) (hints_cons _ _ _ (der_24102 v h) (hints_cons _ _ _ (der_24103 v h) (hints_cons _ _ _ (der_24104 v h) (hints_cons _ _ _ (der_24105 v h) (hints_cons _ _ _ (der_24106 v h) (hints_cons _ _ _ (der_24107 v h) (hints_cons _ _ _ (der_24108 v h) (hints_cons _ _ _ (der_24109 v h) (hints_cons _ _ _ (der_24110 v h) (hints_cons _ _ _ (der_24111 v h) (hints_cons _ _ _ (der_24112 v h) (hints_cons _ _ _ (der_24113 v h) (hints_cons _ _ _ (der_24114 v h) (hints_cons _ _ _ (der_24115 v h) (hints_cons _ _ _ (der_24116 v h) (hints_cons _ _ _ (der_24117 v h) (hints_cons _ _ _ (der_24118 v h) (hints_cons _ _ _ (der_24119 v h) (hints_cons _ _ _ (der_24120 v h) (hints_cons _ _ _ (der_24121 v h) (hints_cons _ _ _ (der_24122 v h) (hints_cons _ _ _ (der_24123 v h) (hints_cons _ _ _ (der_24124 v h) (hints_cons _ _ _ (der_24125 v h) (hints_cons _ _ _ (der_24126 v h) (hints_cons _ _ _ (der_24127 v h) (hints_cons _ _ _ (der_24128 v h) (hints_cons _ _ _ (der_24129 v h) (hints_cons _ _ _ (der_24130 v h) (hints_cons _ _ _ (der_24131 v h) (hints_cons _ _ _ (der_24132 v h) (hints_cons _ _ _ (der_24133 v h) (hints_cons _ _ _ (der_24134 v h) (hints_cons _ _ _ (der_24135 v h) (hints_cons _ _ _ (der_24136 v h) (hints_cons _ _ _ (der_24137 v h) (hints_cons _ _ _ (der_24138 v h) (hints_cons _ _ _ (der_24139 v h) (hints_cons _ _ _ (der_24140 v h) (hints_cons _ _ _ (der_24141 v h) (hints_cons _ _ _ (der_24142 v h) (hints_cons _ _ _ (der_24143 v h) (hints_cons _ _ _ (der_24144 v h) (hints_cons _ _ _ (der_24145 v h) (hints_cons _ _ _ (der_24146 v h) (hints_cons _ _ _ (der_24147 v h) (hints_cons _ _ _ (der_24148 v h) (hints_cons _ _ _ (der_24149 v h) (hints_cons _ _ _ (der_24150 v h) (hints_cons _ _ _ (der_24151 v h) (hints_cons _ _ _ (der_24152 v h) (hints_cons _ _ _ (der_24153 v h) (hints_cons _ _ _ (der_24154 v h) (hints_cons _ _ _ (der_24155 v h) (hints_cons _ _ _ (der_24156 v h) (hints_cons _ _ _ (der_24157 v h) (hints_cons _ _ _ (der_24158 v h) (hints_cons _ _ _ (der_24159 v h) (hints_cons _ _ _ (der_24160 v h) (hints_cons _ _ _ (der_24161 v h) (hints_cons _ _ _ (der_24162 v h) (hints_cons _ _ _ (der_24163 v h) (hints_cons _ _ _ (der_24164 v h) (hints_cons _ _ _ (der_24165 v h) (hints_cons _ _ _ (der_24166 v h) (hints_cons _ _ _ (der_24167 v h) (hints_cons _ _ _ (der_24168 v h) (hints_cons _ _ _ (der_24169 v h) (hints_cons _ _ _ (der_24170 v h) (hints_cons _ _ _ (der_24171 v h) (hints_cons _ _ _ (der_24172 v h) (hints_cons _ _ _ (der_24173 v h) (hints_cons _ _ _ (der_24174 v h) (hints_cons _ _ _ (der_24175 v h) (hints_cons _ _ _ (der_24176 v h) (hints_cons _ _ _ (der_24177 v h) (by intro d hd; cases hd)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def prefix003 := prefix002 ++ chunk003
theorem prefix_sound003 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : ∀ c ∈ prefix003, CNF.Holds (v ∘ decodeVar) c := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact prefix_sound002 v h c hc
  · exact chunk_sound003 v h c hc
end Percolation.NReplay
