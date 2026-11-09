import NReplay006
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_25750 : CNF.NClause := [(115,true),(59,false),(36,true),(44,false),(55,false),(47,false)]
theorem der_25750 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25750 :=
  CNF.rup_sound cl_25750 [cl_3396,cl_3395] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3396 v h) (hints_cons _ _ _ (inp_3395 v h) (by intro d hd; cases hd)))
def cl_25751 : CNF.NClause := [(115,true),(55,false),(36,false),(44,true),(47,false),(59,false)]
theorem der_25751 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25751 :=
  CNF.rup_sound cl_25751 [cl_3398,cl_23865] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3398 v h) (hints_cons _ _ _ (der_23865 v h) (by intro d hd; cases hd)))
def cl_25752 : CNF.NClause := [(115,true),(59,false),(36,true),(55,false),(47,false),(44,true)]
theorem der_25752 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25752 :=
  CNF.rup_sound cl_25752 [cl_3400,cl_24867] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3400 v h) (hints_cons _ _ _ (der_24867 v h) (by intro d hd; cases hd)))
def cl_25753 : CNF.NClause := [(115,true),(55,false),(36,false),(44,false),(33,true),(59,false)]
theorem der_25753 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25753 :=
  CNF.rup_sound cl_25753 [cl_3402,cl_3394] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3402 v h) (hints_cons _ _ _ (inp_3394 v h) (by intro d hd; cases hd)))
def cl_25754 : CNF.NClause := [(115,true),(59,false),(36,true),(44,false),(47,true),(55,false)]
theorem der_25754 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25754 :=
  CNF.rup_sound cl_25754 [cl_3404,cl_24868] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3404 v h) (hints_cons _ _ _ (der_24868 v h) (by intro d hd; cases hd)))
def cl_25755 : CNF.NClause := [(115,true),(55,false),(36,false),(44,true),(47,true),(59,false)]
theorem der_25755 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25755 :=
  CNF.rup_sound cl_25755 [cl_3406,cl_23865] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3406 v h) (hints_cons _ _ _ (der_23865 v h) (by intro d hd; cases hd)))
def cl_25756 : CNF.NClause := [(115,true),(44,true),(36,true),(55,false),(47,true),(59,false)]
theorem der_25756 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25756 :=
  CNF.rup_sound cl_25756 [cl_3408,cl_24869] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3408 v h) (hints_cons _ _ _ (der_24869 v h) (by intro d hd; cases hd)))
def cl_25757 : CNF.NClause := [(115,true),(36,false),(44,false),(47,false),(55,true),(59,false)]
theorem der_25757 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25757 :=
  CNF.rup_sound cl_25757 [cl_3410,cl_25280] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3410 v h) (hints_cons _ _ _ (der_25280 v h) (by intro d hd; cases hd)))
def cl_25758 : CNF.NClause := [(115,true),(59,false),(36,true),(44,false),(47,false),(33,true)]
theorem der_25758 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25758 :=
  CNF.rup_sound cl_25758 [cl_3412,cl_25750] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3412 v h) (hints_cons _ _ _ (der_25750 v h) (by intro d hd; cases hd)))
def cl_25759 : CNF.NClause := [(115,true),(36,false),(44,true),(47,false),(55,true),(59,false)]
theorem der_25759 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25759 :=
  CNF.rup_sound cl_25759 [cl_3414,cl_23866] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3414 v h) (hints_cons _ _ _ (der_23866 v h) (by intro d hd; cases hd)))
def cl_25760 : CNF.NClause := [(115,true),(47,false),(36,true),(44,true),(33,true),(59,false)]
theorem der_25760 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25760 :=
  CNF.rup_sound cl_25760 [cl_3416,cl_25752] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3416 v h) (hints_cons _ _ _ (der_25752 v h) (by intro d hd; cases hd)))
def cl_25761 : CNF.NClause := [(115,true),(36,false),(44,false),(47,true),(55,true),(59,false)]
theorem der_25761 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25761 :=
  CNF.rup_sound cl_25761 [cl_3418,cl_3417] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3418 v h) (hints_cons _ _ _ (inp_3417 v h) (by intro d hd; cases hd)))
def cl_25762 : CNF.NClause := [(115,true),(59,false),(36,true),(44,false),(47,true),(55,true)]
theorem der_25762 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25762 :=
  CNF.rup_sound cl_25762 [cl_3420,cl_24872] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3420 v h) (hints_cons _ _ _ (der_24872 v h) (by intro d hd; cases hd)))
def cl_25763 : CNF.NClause := [(115,true),(36,false),(44,true),(47,true),(55,true),(59,false)]
theorem der_25763 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25763 :=
  CNF.rup_sound cl_25763 [cl_3422,cl_23867] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3422 v h) (hints_cons _ _ _ (der_23867 v h) (by intro d hd; cases hd)))
def cl_25764 : CNF.NClause := [(115,true),(55,false),(36,false),(44,false),(47,false),(33,true)]
theorem der_25764 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25764 :=
  CNF.rup_sound cl_25764 [cl_3426,cl_3394] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3426 v h) (hints_cons _ _ _ (inp_3394 v h) (by intro d hd; cases hd)))
def cl_25765 : CNF.NClause := [(115,true),(36,true),(44,false),(47,false),(55,false),(33,true)]
theorem der_25765 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25765 :=
  CNF.rup_sound cl_25765 [cl_3428,cl_25750] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3428 v h) (hints_cons _ _ _ (der_25750 v h) (by intro d hd; cases hd)))
def cl_25766 : CNF.NClause := [(115,true),(55,false),(36,false),(44,true),(47,false),(59,true)]
theorem der_25766 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25766 :=
  CNF.rup_sound cl_25766 [cl_3430,cl_23868] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3430 v h) (hints_cons _ _ _ (der_23868 v h) (by intro d hd; cases hd)))
def cl_25767 : CNF.NClause := [(115,true),(36,true),(44,true),(47,false),(55,false),(33,true)]
theorem der_25767 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25767 :=
  CNF.rup_sound cl_25767 [cl_3432,cl_25752] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3432 v h) (hints_cons _ _ _ (der_25752 v h) (by intro d hd; cases hd)))
def cl_25768 : CNF.NClause := [(115,true),(55,false),(36,false),(44,false),(47,true),(33,true)]
theorem der_25768 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25768 :=
  CNF.rup_sound cl_25768 [cl_3434,cl_25753] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3434 v h) (hints_cons _ _ _ (der_25753 v h) (by intro d hd; cases hd)))
def cl_25769 : CNF.NClause := [(115,true),(55,false),(36,true),(44,false),(47,true),(59,true)]
theorem der_25769 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25769 :=
  CNF.rup_sound cl_25769 [cl_3436,cl_24876] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3436 v h) (hints_cons _ _ _ (der_24876 v h) (by intro d hd; cases hd)))
def cl_25770 : CNF.NClause := [(115,true),(55,false),(36,false),(44,true),(47,true),(33,true)]
theorem der_25770 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25770 :=
  CNF.rup_sound cl_25770 [cl_3438,cl_25755] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3438 v h) (hints_cons _ _ _ (der_25755 v h) (by intro d hd; cases hd)))
def cl_25771 : CNF.NClause := [(115,true),(36,false),(44,false),(47,false),(55,true),(59,true)]
theorem der_25771 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25771 :=
  CNF.rup_sound cl_25771 [cl_3442,cl_25281] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3442 v h) (hints_cons _ _ _ (der_25281 v h) (by intro d hd; cases hd)))
def cl_25772 : CNF.NClause := [(115,true),(47,false),(44,false),(59,true),(55,true),(33,true)]
theorem der_25772 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25772 :=
  CNF.rup_sound cl_25772 [cl_3444,cl_25771] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3444 v h) (hints_cons _ _ _ (der_25771 v h) (by intro d hd; cases hd)))
def cl_25773 : CNF.NClause := [(115,true),(36,false),(33,true),(44,true),(47,false),(59,true)]
theorem der_25773 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25773 :=
  CNF.rup_sound cl_25773 [cl_3446,cl_25766] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3446 v h) (hints_cons _ _ _ (der_25766 v h) (by intro d hd; cases hd)))
def cl_25774 : CNF.NClause := [(115,true),(36,false),(44,false),(47,true),(55,true),(59,true)]
theorem der_25774 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25774 :=
  CNF.rup_sound cl_25774 [cl_3450,cl_23870] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3450 v h) (hints_cons _ _ _ (der_23870 v h) (by intro d hd; cases hd)))
def cl_25775 : CNF.NClause := [(118,true),(32,false),(31,true),(33,true),(34,false),(35,true)]
theorem der_25775 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25775 :=
  CNF.rup_sound cl_25775 [cl_3638,cl_25263] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3638 v h) (hints_cons _ _ _ (der_25263 v h) (by intro d hd; cases hd)))
def cl_25776 : CNF.NClause := [(118,true),(32,false),(35,false),(34,false),(31,true),(61,true)]
theorem der_25776 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25776 :=
  CNF.rup_sound cl_25776 [cl_3622,cl_3618] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3622 v h) (hints_cons _ _ _ (inp_3618 v h) (by intro d hd; cases hd)))
def cl_25777 : CNF.NClause := [(93,true),(61,false),(57,false),(56,true),(60,false),(59,true)]
theorem der_25777 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25777 :=
  CNF.rup_sound cl_25777 [cl_1994,cl_25039] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1994 v h) (hints_cons _ _ _ (der_25039 v h) (by intro d hd; cases hd)))
def cl_25778 : CNF.NClause := [(93,true),(61,false),(57,false),(58,false),(56,true),(60,true)]
theorem der_25778 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25778 :=
  CNF.rup_sound cl_25778 [cl_2010,cl_2002] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2010 v h) (hints_cons _ _ _ (inp_2002 v h) (by intro d hd; cases hd)))
def cl_25779 : CNF.NClause := [(101,true),(51,false),(37,false),(45,false),(48,false),(34,false)]
theorem der_25779 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25779 :=
  CNF.rup_sound cl_25779 [cl_2529,cl_23848] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2529 v h) (hints_cons _ _ _ (der_23848 v h) (by intro d hd; cases hd)))
def cl_25780 : CNF.NClause := [(101,true),(51,false),(37,false),(45,true),(48,false),(34,false)]
theorem der_25780 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25780 :=
  CNF.rup_sound cl_25780 [cl_2533,cl_23847] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2533 v h) (hints_cons _ _ _ (der_23847 v h) (by intro d hd; cases hd)))
def cl_25781 : CNF.NClause := [(115,true),(59,true),(33,false),(47,false),(36,false),(55,false)]
theorem der_25781 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25781 :=
  CNF.rup_sound cl_25781 [cl_3425,cl_23868] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3425 v h) (hints_cons _ _ _ (der_23868 v h) (by intro d hd; cases hd)))
def cl_25782 : CNF.NClause := [(112,true),(32,false),(40,false),(46,false),(54,false),(43,false)]
theorem der_25782 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25782 :=
  CNF.rup_sound cl_25782 [cl_3233,cl_25055] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3233 v h) (hints_cons _ _ _ (der_25055 v h) (by intro d hd; cases hd)))
def cl_25783 : CNF.NClause := [(93,true),(58,false),(56,true),(57,false),(60,false),(61,true)]
theorem der_25783 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25783 :=
  CNF.rup_sound cl_25783 [cl_2026,cl_23838] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2026 v h) (hints_cons _ _ _ (der_23838 v h) (by intro d hd; cases hd)))
def cl_25784 : CNF.NClause := [(93,true),(58,false),(56,true),(57,false),(60,true),(61,true)]
theorem der_25784 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25784 :=
  CNF.rup_sound cl_25784 [cl_2042,cl_23791] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2042 v h) (hints_cons _ _ _ (der_23791 v h) (by intro d hd; cases hd)))
def cl_25785 : CNF.NClause := [(121,true),(39,false),(59,true),(42,false),(31,true),(50,false)]
theorem der_25785 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25785 :=
  CNF.rup_sound cl_25785 [cl_3810,cl_23744] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3810 v h) (hints_cons _ _ _ (der_23744 v h) (by intro d hd; cases hd)))
def cl_25786 : CNF.NClause := [(121,true),(50,false),(42,false),(31,true),(53,false),(59,true)]
theorem der_25786 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25786 :=
  CNF.rup_sound cl_25786 [cl_3812,cl_25785] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3812 v h) (hints_cons _ _ _ (der_25785 v h) (by intro d hd; cases hd)))
def cl_25787 : CNF.NClause := [(121,true),(42,true),(39,true),(31,true),(53,false),(50,false)]
theorem der_25787 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25787 :=
  CNF.rup_sound cl_25787 [cl_3816,cl_24759] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3816 v h) (hints_cons _ _ _ (der_24759 v h) (by intro d hd; cases hd)))
def cl_25788 : CNF.NClause := [(112,true),(32,false),(40,true),(43,false),(46,false),(54,false)]
theorem der_25788 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25788 :=
  CNF.rup_sound cl_25788 [cl_3235,cl_23790] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3235 v h) (hints_cons _ _ _ (der_23790 v h) (by intro d hd; cases hd)))
def cl_25789 : CNF.NClause := [(112,true),(32,false),(40,false),(43,false),(54,false),(46,true)]
theorem der_25789 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25789 :=
  CNF.rup_sound cl_25789 [cl_3241,cl_25313] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3241 v h) (hints_cons _ _ _ (der_25313 v h) (by intro d hd; cases hd)))
def cl_25790 : CNF.NClause := [(115,true),(59,true),(33,false),(44,false),(36,false),(47,true)]
theorem der_25790 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25790 :=
  CNF.rup_sound cl_25790 [cl_3433,cl_23698] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3433 v h) (hints_cons _ _ _ (der_23698 v h) (by intro d hd; cases hd)))
def cl_25791 : CNF.NClause := [(101,true),(51,false),(37,false),(45,false),(34,false),(59,true)]
theorem der_25791 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25791 :=
  CNF.rup_sound cl_25791 [cl_2537,cl_25779] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2537 v h) (hints_cons _ _ _ (der_25779 v h) (by intro d hd; cases hd)))
def cl_25792 : CNF.NClause := [(101,true),(51,false),(34,false),(37,false),(45,true),(48,true)]
theorem der_25792 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25792 :=
  CNF.rup_sound cl_25792 [cl_2541,cl_2509] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2541 v h) (hints_cons _ _ _ (inp_2509 v h) (by intro d hd; cases hd)))
def cl_25793 : CNF.NClause := [(121,true),(39,false),(59,true),(42,false),(31,true),(53,false)]
theorem der_25793 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25793 :=
  CNF.rup_sound cl_25793 [cl_3818,cl_25785] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3818 v h) (hints_cons _ _ _ (der_25785 v h) (by intro d hd; cases hd)))
def cl_25794 : CNF.NClause := [(121,true),(39,true),(42,false),(31,true),(53,false),(59,true)]
theorem der_25794 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25794 :=
  CNF.rup_sound cl_25794 [cl_3820,cl_25786] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3820 v h) (hints_cons _ _ _ (der_25786 v h) (by intro d hd; cases hd)))
def cl_25795 : CNF.NClause := [(112,true),(32,false),(40,true),(43,false),(46,true),(54,false)]
theorem der_25795 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25795 :=
  CNF.rup_sound cl_25795 [cl_3243,cl_3211] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3243 v h) (hints_cons _ _ _ (inp_3211 v h) (by intro d hd; cases hd)))
def cl_25796 : CNF.NClause := [(115,true),(33,false),(36,false),(47,true),(55,false),(44,true)]
theorem der_25796 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25796 :=
  CNF.rup_sound cl_25796 [cl_3437,cl_23865] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3437 v h) (hints_cons _ _ _ (der_23865 v h) (by intro d hd; cases hd)))
def cl_25797 : CNF.NClause := [(110,true),(33,false),(52,false),(45,false),(46,true),(57,false)]
theorem der_25797 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25797 :=
  CNF.rup_sound cl_25797 [cl_3081,cl_24713] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3081 v h) (hints_cons _ _ _ (der_24713 v h) (by intro d hd; cases hd)))
def cl_25798 : CNF.NClause := [(97,true),(37,false),(42,false),(32,false),(47,true),(56,true)]
theorem der_25798 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25798 :=
  CNF.rup_sound cl_25798 [cl_2281,cl_23798] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2281 v h) (hints_cons _ _ _ (der_23798 v h) (by intro d hd; cases hd)))
def cl_25799 : CNF.NClause := [(110,true),(33,false),(39,false),(46,false),(45,true),(57,false)]
theorem der_25799 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25799 :=
  CNF.rup_sound cl_25799 [cl_3077,cl_23799] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3077 v h) (hints_cons _ _ _ (der_23799 v h) (by intro d hd; cases hd)))
def cl_25800 : CNF.NClause := [(110,true),(33,false),(39,false),(46,true),(45,true),(57,false)]
theorem der_25800 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25800 :=
  CNF.rup_sound cl_25800 [cl_3085,cl_3101] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3085 v h) (hints_cons _ _ _ (inp_3101 v h) (by intro d hd; cases hd)))
def cl_25801 : CNF.NClause := [(110,true),(33,false),(52,false),(39,false),(46,true),(45,true)]
theorem der_25801 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25801 :=
  CNF.rup_sound cl_25801 [cl_3117,cl_25800] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3117 v h) (hints_cons _ _ _ (der_25800 v h) (by intro d hd; cases hd)))
def cl_25802 : CNF.NClause := [(119,true),(52,false),(40,true),(60,false),(44,false),(48,true)]
theorem der_25802 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25802 :=
  CNF.rup_sound cl_25802 [cl_3660,cl_25108] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3660 v h) (hints_cons _ _ _ (der_25108 v h) (by intro d hd; cases hd)))
def cl_25803 : CNF.NClause := [(110,true),(57,false),(33,false),(45,false),(46,false),(39,false)]
theorem der_25803 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25803 :=
  CNF.rup_sound cl_25803 [cl_3073,cl_3089] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3073 v h) (hints_cons _ _ _ (inp_3089 v h) (by intro d hd; cases hd)))
def cl_25804 : CNF.NClause := [(116,true),(34,false),(52,false),(43,false),(50,true),(58,false)]
theorem der_25804 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25804 :=
  CNF.rup_sound cl_25804 [cl_3465,cl_24912] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3465 v h) (hints_cons _ _ _ (der_24912 v h) (by intro d hd; cases hd)))
def cl_25805 : CNF.NClause := [(116,true),(52,false),(43,false),(36,false),(50,true),(58,true)]
theorem der_25805 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25805 :=
  CNF.rup_sound cl_25805 [cl_3497,cl_25498] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3497 v h) (hints_cons _ _ _ (der_25498 v h) (by intro d hd; cases hd)))
def cl_25806 : CNF.NClause := [(98,true),(51,false),(61,true),(54,false),(52,false),(55,false)]
theorem der_25806 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25806 :=
  CNF.rup_sound cl_25806 [cl_2337,cl_23732] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2337 v h) (hints_cons _ _ _ (der_23732 v h) (by intro d hd; cases hd)))
def cl_25807 : CNF.NClause := [(97,true),(32,false),(42,false),(47,false),(37,false),(56,true)]
theorem der_25807 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25807 :=
  CNF.rup_sound cl_25807 [cl_2273,cl_2289] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2273 v h) (hints_cons _ _ _ (inp_2289 v h) (by intro d hd; cases hd)))
def cl_25808 : CNF.NClause := [(119,true),(44,true),(40,true),(60,false),(52,false),(48,false)]
theorem der_25808 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25808 :=
  CNF.rup_sound cl_25808 [cl_3656,cl_25106] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3656 v h) (hints_cons _ _ _ (der_25106 v h) (by intro d hd; cases hd)))
def cl_25809 : CNF.NClause := [(119,true),(52,false),(44,false),(48,false),(40,false),(60,false)]
theorem der_25809 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25809 :=
  CNF.rup_sound cl_25809 [cl_3650,cl_3649] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3650 v h) (hints_cons _ _ _ (inp_3649 v h) (by intro d hd; cases hd)))
def cl_25810 : CNF.NClause := [(119,true),(31,true),(44,true),(48,false),(40,false),(60,false)]
theorem der_25810 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25810 :=
  CNF.rup_sound cl_25810 [cl_3654,cl_3670] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3654 v h) (hints_cons _ _ _ (inp_3670 v h) (by intro d hd; cases hd)))
def cl_25811 : CNF.NClause := [(119,true),(52,false),(31,true),(44,false),(48,true),(60,false)]
theorem der_25811 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25811 :=
  CNF.rup_sound cl_25811 [cl_3658,cl_25802] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3658 v h) (hints_cons _ _ _ (der_25802 v h) (by intro d hd; cases hd)))
def cl_25812 : CNF.NClause := [(119,true),(31,true),(44,true),(48,true),(40,false),(60,false)]
theorem der_25812 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25812 :=
  CNF.rup_sound cl_25812 [cl_3662,cl_23889] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3662 v h) (hints_cons _ _ _ (der_23889 v h) (by intro d hd; cases hd)))
def cl_25813 : CNF.NClause := [(110,true),(33,false),(52,false),(46,false),(45,true),(57,true)]
theorem der_25813 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25813 :=
  CNF.rup_sound cl_25813 [cl_3109,cl_24720] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3109 v h) (hints_cons _ _ _ (der_24720 v h) (by intro d hd; cases hd)))
def cl_25814 : CNF.NClause := [(116,true),(50,false),(34,false),(58,false),(43,false),(36,false)]
theorem der_25814 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25814 :=
  CNF.rup_sound cl_25814 [cl_3457,cl_3473] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3457 v h) (hints_cons _ _ _ (inp_3473 v h) (by intro d hd; cases hd)))
def cl_25815 : CNF.NClause := [(119,true),(44,true),(40,true),(52,false),(48,true),(60,false)]
theorem der_25815 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25815 :=
  CNF.rup_sound cl_25815 [cl_3664,cl_25118] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3664 v h) (hints_cons _ _ _ (der_25118 v h) (by intro d hd; cases hd)))
def cl_25816 : CNF.NClause := [(104,true),(38,true),(52,false),(41,false),(49,false),(35,false)]
theorem der_25816 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25816 :=
  CNF.rup_sound cl_25816 [cl_2691,cl_2723] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2691 v h) (hints_cons _ _ _ (inp_2723 v h) (by intro d hd; cases hd)))
def cl_25817 : CNF.NClause := [(104,true),(52,false),(41,false),(49,true),(35,false),(59,false)]
theorem der_25817 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25817 :=
  CNF.rup_sound cl_25817 [cl_2699,cl_2697] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2699 v h) (hints_cons _ _ _ (inp_2697 v h) (by intro d hd; cases hd)))
def cl_25818 : CNF.NClause := [(104,true),(41,false),(35,false),(38,false),(52,false),(59,true)]
theorem der_25818 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25818 :=
  CNF.rup_sound cl_25818 [cl_2721,cl_23805] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2721 v h) (hints_cons _ _ _ (der_23805 v h) (by intro d hd; cases hd)))
def cl_25819 : CNF.NClause := [(104,true),(41,false),(35,false),(38,false),(52,true),(59,true)]
theorem der_25819 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25819 :=
  CNF.rup_sound cl_25819 [cl_2737,cl_23806] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2737 v h) (hints_cons _ _ _ (der_23806 v h) (by intro d hd; cases hd)))
def cl_25820 : CNF.NClause := [(108,true),(61,false),(47,true),(48,true),(46,true),(50,false)]
theorem der_25820 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25820 :=
  CNF.rup_sound cl_25820 [cl_2952,cl_23853] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2952 v h) (hints_cons _ _ _ (der_23853 v h) (by intro d hd; cases hd)))
def cl_25822 : CNF.NClause := [(108,true),(50,false),(47,true),(48,true),(46,true),(49,false)]
theorem der_25822 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25822 :=
  CNF.rup_sound cl_25822 [cl_2984,cl_25820] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2984 v h) (hints_cons _ _ _ (der_25820 v h) (by intro d hd; cases hd)))
def cl_25823 : CNF.NClause := [(108,true),(47,true),(46,false),(49,false),(48,false),(50,false)]
theorem der_25823 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25823 :=
  CNF.rup_sound cl_25823 [cl_2979,cl_2947] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2979 v h) (hints_cons _ _ _ (inp_2947 v h) (by intro d hd; cases hd)))
def cl_25824 : CNF.NClause := [(117,true),(32,false),(49,false),(45,true),(53,false),(60,false)]
theorem der_25824 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25824 :=
  CNF.rup_sound cl_25824 [cl_3525,cl_24881] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3525 v h) (hints_cons _ _ _ (der_24881 v h) (by intro d hd; cases hd)))
def cl_25825 : CNF.NClause := [(117,true),(32,false),(49,false),(36,false),(53,true),(60,false)]
theorem der_25825 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25825 :=
  CNF.rup_sound cl_25825 [cl_3541,cl_3537] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3541 v h) (hints_cons _ _ _ (inp_3537 v h) (by intro d hd; cases hd)))
def cl_25826 : CNF.NClause := [(117,true),(32,false),(49,false),(36,false),(45,true),(53,true)]
theorem der_25826 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25826 :=
  CNF.rup_sound cl_25826 [cl_3573,cl_25825] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3573 v h) (hints_cons _ _ _ (der_25825 v h) (by intro d hd; cases hd)))
def cl_25827 : CNF.NClause := [(100,true),(51,false),(33,false),(42,false),(40,false),(58,false)]
theorem der_25827 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25827 :=
  CNF.rup_sound cl_25827 [cl_2433,cl_2441] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2433 v h) (hints_cons _ _ _ (inp_2441 v h) (by intro d hd; cases hd)))
def cl_25828 : CNF.NClause := [(100,true),(51,false),(42,false),(40,true),(33,false),(58,false)]
theorem der_25828 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25828 :=
  CNF.rup_sound cl_25828 [cl_2435,cl_23814] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2435 v h) (hints_cons _ _ _ (der_23814 v h) (by intro d hd; cases hd)))
def cl_25829 : CNF.NClause := [(117,true),(32,false),(49,false),(36,false),(45,true),(53,false)]
theorem der_25829 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25829 :=
  CNF.rup_sound cl_25829 [cl_3557,cl_25824] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3557 v h) (hints_cons _ _ _ (der_25824 v h) (by intro d hd; cases hd)))
def cl_25830 : CNF.NClause := [(117,true),(32,false),(45,false),(60,false),(36,false),(49,false)]
theorem der_25830 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25830 :=
  CNF.rup_sound cl_25830 [cl_3521,cl_3537] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3521 v h) (hints_cons _ _ _ (inp_3537 v h) (by intro d hd; cases hd)))
def cl_25831 : CNF.NClause := [(117,true),(32,false),(45,false),(36,false),(53,false),(60,true)]
theorem der_25831 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25831 :=
  CNF.rup_sound cl_25831 [cl_3553,cl_23901] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3553 v h) (hints_cons _ _ _ (der_23901 v h) (by intro d hd; cases hd)))
def cl_25832 : CNF.NClause := [(122,true),(57,false),(55,false),(31,true),(37,false),(43,false)]
theorem der_25832 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25832 :=
  CNF.rup_sound cl_25832 [cl_3842,cl_24833] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3842 v h) (hints_cons _ _ _ (der_24833 v h) (by intro d hd; cases hd)))
def cl_25833 : CNF.NClause := [(108,true),(50,false),(47,true),(48,true),(49,false),(61,true)]
theorem der_25833 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25833 :=
  CNF.rup_sound cl_25833 [cl_2983,cl_25822] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2983 v h) (hints_cons _ _ _ (der_25822 v h) (by intro d hd; cases hd)))
def cl_25834 : CNF.NClause := [(96,true),(34,false),(39,false),(44,true),(54,false),(56,true)]
theorem der_25834 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25834 :=
  CNF.rup_sound cl_25834 [cl_2213,cl_2221] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2213 v h) (hints_cons _ _ _ (inp_2221 v h) (by intro d hd; cases hd)))
def cl_25835 : CNF.NClause := [(96,true),(34,false),(39,false),(44,true),(54,true),(56,true)]
theorem der_25835 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25835 :=
  CNF.rup_sound cl_25835 [cl_2229,cl_23864] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2229 v h) (hints_cons _ _ _ (der_23864 v h) (by intro d hd; cases hd)))
def cl_25838 : CNF.NClause := [(96,true),(39,false),(34,false),(44,true),(54,true),(49,false)]
theorem der_25838 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25838 :=
  CNF.rup_sound cl_25838 [cl_2197,cl_25835] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2197 v h) (hints_cons _ _ _ (der_25835 v h) (by intro d hd; cases hd)))
def cl_25840 : CNF.NClause := [(96,true),(34,false),(39,true),(49,false),(54,false),(56,true)]
theorem der_25840 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25840 :=
  CNF.rup_sound cl_25840 [cl_2215,cl_24752] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2215 v h) (hints_cons _ _ _ (der_24752 v h) (by intro d hd; cases hd)))
def cl_25841 : CNF.NClause := [(104,true),(52,true),(41,false),(38,true),(35,false),(59,false)]
theorem der_25841 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25841 :=
  CNF.rup_sound cl_25841 [cl_2707,cl_23830] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2707 v h) (hints_cons _ _ _ (der_23830 v h) (by intro d hd; cases hd)))
def cl_25842 : CNF.NClause := [(104,true),(59,false),(41,false),(38,false),(52,true),(35,false)]
theorem der_25842 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25842 :=
  CNF.rup_sound cl_25842 [cl_2705,cl_23830] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2705 v h) (hints_cons _ _ _ (der_23830 v h) (by intro d hd; cases hd)))
def cl_25843 : CNF.NClause := [(104,true),(59,false),(41,false),(38,false),(52,false),(35,false)]
theorem der_25843 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25843 :=
  CNF.rup_sound cl_25843 [cl_2689,cl_2697] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2689 v h) (hints_cons _ _ _ (inp_2697 v h) (by intro d hd; cases hd)))
def cl_25844 : CNF.NClause := [(103,true),(42,false),(43,false),(44,false),(45,false),(61,false)]
theorem der_25844 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25844 :=
  CNF.rup_sound cl_25844 [cl_2626,cl_25268] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2626 v h) (hints_cons _ _ _ (der_25268 v h) (by intro d hd; cases hd)))
def cl_25845 : CNF.NClause := [(103,true),(61,false),(42,true),(44,false),(45,false),(43,false)]
theorem der_25845 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25845 :=
  CNF.rup_sound cl_25845 [cl_2628,cl_25265] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2628 v h) (hints_cons _ _ _ (der_25265 v h) (by intro d hd; cases hd)))
def cl_25846 : CNF.NClause := [(103,true),(42,false),(43,true),(44,false),(45,false),(61,false)]
theorem der_25846 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25846 :=
  CNF.rup_sound cl_25846 [cl_2630,cl_25269] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2630 v h) (hints_cons _ _ _ (der_25269 v h) (by intro d hd; cases hd)))
def cl_25847 : CNF.NClause := [(103,true),(61,false),(42,true),(43,true),(44,false),(45,false)]
theorem der_25847 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25847 :=
  CNF.rup_sound cl_25847 [cl_2632,cl_25270] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2632 v h) (hints_cons _ _ _ (der_25270 v h) (by intro d hd; cases hd)))
def cl_25848 : CNF.NClause := [(103,true),(42,false),(43,false),(44,true),(45,false),(61,false)]
theorem der_25848 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25848 :=
  CNF.rup_sound cl_25848 [cl_2634,cl_2633] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2634 v h) (hints_cons _ _ _ (inp_2633 v h) (by intro d hd; cases hd)))
def cl_25849 : CNF.NClause := [(103,true),(61,false),(42,true),(41,true),(45,false),(43,false)]
theorem der_25849 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25849 :=
  CNF.rup_sound cl_25849 [cl_2636,cl_25845] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2636 v h) (hints_cons _ _ _ (der_25845 v h) (by intro d hd; cases hd)))
def cl_25850 : CNF.NClause := [(103,true),(42,false),(43,true),(44,true),(45,false),(61,false)]
theorem der_25850 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25850 :=
  CNF.rup_sound cl_25850 [cl_2638,cl_23877] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2638 v h) (hints_cons _ _ _ (der_23877 v h) (by intro d hd; cases hd)))
def cl_25851 : CNF.NClause := [(103,true),(61,false),(42,true),(43,true),(44,true),(45,false)]
theorem der_25851 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25851 :=
  CNF.rup_sound cl_25851 [cl_2640,cl_23877] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2640 v h) (hints_cons _ _ _ (der_23877 v h) (by intro d hd; cases hd)))
def cl_25852 : CNF.NClause := [(103,true),(42,false),(43,false),(44,false),(45,true),(61,false)]
theorem der_25852 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25852 :=
  CNF.rup_sound cl_25852 [cl_2642,cl_25271] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2642 v h) (hints_cons _ _ _ (der_25271 v h) (by intro d hd; cases hd)))
def cl_25854 : CNF.NClause := [(103,true),(42,false),(43,true),(44,false),(45,true),(61,false)]
theorem der_25854 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25854 :=
  CNF.rup_sound cl_25854 [cl_2646,cl_25272] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2646 v h) (hints_cons _ _ _ (der_25272 v h) (by intro d hd; cases hd)))
def cl_25856 : CNF.NClause := [(103,true),(42,false),(43,false),(44,true),(45,true),(61,false)]
theorem der_25856 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25856 :=
  CNF.rup_sound cl_25856 [cl_2650,cl_23878] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2650 v h) (hints_cons _ _ _ (der_23878 v h) (by intro d hd; cases hd)))
def cl_25859 : CNF.NClause := [(103,true),(45,false),(41,true),(42,false),(44,false),(43,false)]
theorem der_25859 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25859 :=
  CNF.rup_sound cl_25859 [cl_2658,cl_25844] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2658 v h) (hints_cons _ _ _ (der_25844 v h) (by intro d hd; cases hd)))
def cl_25860 : CNF.NClause := [(103,true),(42,true),(44,false),(41,true),(45,false),(43,false)]
theorem der_25860 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25860 :=
  CNF.rup_sound cl_25860 [cl_2660,cl_25845] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2660 v h) (hints_cons _ _ _ (der_25845 v h) (by intro d hd; cases hd)))
def cl_25861 : CNF.NClause := [(103,true),(42,false),(43,true),(44,false),(45,false),(61,true)]
theorem der_25861 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25861 :=
  CNF.rup_sound cl_25861 [cl_2662,cl_25618] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2662 v h) (hints_cons _ _ _ (der_25618 v h) (by intro d hd; cases hd)))
def cl_25862 : CNF.NClause := [(103,true),(42,true),(45,false),(44,false),(41,true),(61,true)]
theorem der_25862 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25862 :=
  CNF.rup_sound cl_25862 [cl_2664,cl_25860] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2664 v h) (hints_cons _ _ _ (der_25860 v h) (by intro d hd; cases hd)))
def cl_25863 : CNF.NClause := [(103,true),(45,false),(41,true),(42,false),(43,false),(61,true)]
theorem der_25863 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25863 :=
  CNF.rup_sound cl_25863 [cl_2666,cl_25859] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2666 v h) (hints_cons _ _ _ (der_25859 v h) (by intro d hd; cases hd)))
def cl_25864 : CNF.NClause := [(103,true),(45,false),(42,true),(41,true),(43,false),(61,true)]
theorem der_25864 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25864 :=
  CNF.rup_sound cl_25864 [cl_2668,cl_25862] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2668 v h) (hints_cons _ _ _ (der_25862 v h) (by intro d hd; cases hd)))
def cl_25865 : CNF.NClause := [(103,true),(42,false),(43,true),(44,true),(45,false),(61,true)]
theorem der_25865 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25865 :=
  CNF.rup_sound cl_25865 [cl_2670,cl_25619] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2670 v h) (hints_cons _ _ _ (der_25619 v h) (by intro d hd; cases hd)))
def cl_25866 : CNF.NClause := [(103,true),(41,true),(42,false),(43,false),(44,false),(61,true)]
theorem der_25866 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25866 :=
  CNF.rup_sound cl_25866 [cl_2674,cl_25859] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2674 v h) (hints_cons _ _ _ (der_25859 v h) (by intro d hd; cases hd)))
def cl_25867 : CNF.NClause := [(103,true),(42,true),(41,true),(44,false),(43,false),(61,true)]
theorem der_25867 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25867 :=
  CNF.rup_sound cl_25867 [cl_2676,cl_25862] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2676 v h) (hints_cons _ _ _ (der_25862 v h) (by intro d hd; cases hd)))
def cl_25868 : CNF.NClause := [(103,true),(42,false),(41,true),(43,true),(44,false),(45,true)]
theorem der_25868 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25868 :=
  CNF.rup_sound cl_25868 [cl_2678,cl_25854] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2678 v h) (hints_cons _ _ _ (der_25854 v h) (by intro d hd; cases hd)))
def cl_25869 : CNF.NClause := [(103,true),(42,false),(43,false),(44,true),(45,true),(61,true)]
theorem der_25869 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25869 :=
  CNF.rup_sound cl_25869 [cl_2682,cl_2681] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2682 v h) (hints_cons _ _ _ (inp_2681 v h) (by intro d hd; cases hd)))
def cl_25870 : CNF.NClause := [(123,true),(56,false),(36,false),(46,false),(51,false),(41,true)]
theorem der_25870 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25870 :=
  CNF.rup_sound cl_25870 [cl_3910,cl_25227] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3910 v h) (hints_cons _ _ _ (der_25227 v h) (by intro d hd; cases hd)))
def cl_25871 : CNF.NClause := [(123,true),(56,false),(31,true),(46,true),(51,false),(41,true)]
theorem der_25871 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25871 :=
  CNF.rup_sound cl_25871 [cl_3918,cl_25564] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3918 v h) (hints_cons _ _ _ (der_25564 v h) (by intro d hd; cases hd)))
def cl_25872 : CNF.NClause := [(123,true),(56,false),(36,false),(31,true),(46,false),(41,true)]
theorem der_25872 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25872 :=
  CNF.rup_sound cl_25872 [cl_3926,cl_25870] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3926 v h) (hints_cons _ _ _ (der_25870 v h) (by intro d hd; cases hd)))
def cl_25873 : CNF.NClause := [(123,true),(56,false),(36,false),(31,true),(46,true),(41,true)]
theorem der_25873 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25873 :=
  CNF.rup_sound cl_25873 [cl_3934,cl_25871] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3934 v h) (hints_cons _ _ _ (der_25871 v h) (by intro d hd; cases hd)))
def cl_25874 : CNF.NClause := [(107,true),(55,false),(32,false),(48,false),(39,false),(58,false)]
theorem der_25874 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25874 :=
  CNF.rup_sound cl_25874 [cl_2885,cl_23903] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2885 v h) (hints_cons _ _ _ (der_23903 v h) (by intro d hd; cases hd)))
def cl_25875 : CNF.NClause := [(107,true),(55,false),(32,false),(48,true),(39,false),(58,false)]
theorem der_25875 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25875 :=
  CNF.rup_sound cl_25875 [cl_2893,cl_2889] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2893 v h) (hints_cons _ _ _ (inp_2889 v h) (by intro d hd; cases hd)))
def cl_25876 : CNF.NClause := [(107,true),(48,false),(32,false),(58,false),(55,true),(39,false)]
theorem der_25876 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25876 :=
  CNF.rup_sound cl_25876 [cl_2901,cl_25286] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2901 v h) (hints_cons _ _ _ (der_25286 v h) (by intro d hd; cases hd)))
def cl_25877 : CNF.NClause := [(107,true),(32,false),(58,false),(48,true),(55,true),(39,false)]
theorem der_25877 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25877 :=
  CNF.rup_sound cl_25877 [cl_2909,cl_25587] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2909 v h) (hints_cons _ _ _ (der_25587 v h) (by intro d hd; cases hd)))
def cl_25878 : CNF.NClause := [(107,true),(55,false),(32,false),(48,false),(39,false),(58,true)]
theorem der_25878 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25878 :=
  CNF.rup_sound cl_25878 [cl_2917,cl_25050] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2917 v h) (hints_cons _ _ _ (der_25050 v h) (by intro d hd; cases hd)))
def cl_25879 : CNF.NClause := [(107,true),(55,false),(32,false),(48,true),(39,false),(58,true)]
theorem der_25879 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25879 :=
  CNF.rup_sound cl_25879 [cl_2925,cl_25588] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2925 v h) (hints_cons _ _ _ (der_25588 v h) (by intro d hd; cases hd)))
def cl_25880 : CNF.NClause := [(107,true),(48,false),(32,false),(39,false),(55,true),(58,true)]
theorem der_25880 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25880 :=
  CNF.rup_sound cl_25880 [cl_2933,cl_25287] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2933 v h) (hints_cons _ _ _ (der_25287 v h) (by intro d hd; cases hd)))
def cl_25881 : CNF.NClause := [(107,true),(32,false),(39,false),(48,true),(55,true),(58,true)]
theorem der_25881 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25881 :=
  CNF.rup_sound cl_25881 [cl_2941,cl_25589] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2941 v h) (hints_cons _ _ _ (der_25589 v h) (by intro d hd; cases hd)))
def cl_25882 : CNF.NClause := [(105,true),(50,false),(33,false),(60,false),(54,false),(37,false)]
theorem der_25882 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25882 :=
  CNF.rup_sound cl_25882 [cl_2757,cl_23850] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2757 v h) (hints_cons _ _ _ (der_23850 v h) (by intro d hd; cases hd)))
def cl_25883 : CNF.NClause := [(105,true),(33,false),(60,false),(41,true),(50,true),(54,false)]
theorem der_25883 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25883 :=
  CNF.rup_sound cl_25883 [cl_2765,cl_24763] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2765 v h) (hints_cons _ _ _ (der_24763 v h) (by intro d hd; cases hd)))
def cl_25884 : CNF.NClause := [(105,true),(54,true),(33,false),(41,true),(50,false),(60,false)]
theorem der_25884 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25884 :=
  CNF.rup_sound cl_25884 [cl_2773,cl_24767] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2773 v h) (hints_cons _ _ _ (der_24767 v h) (by intro d hd; cases hd)))
def cl_25885 : CNF.NClause := [(105,true),(54,true),(33,false),(41,true),(50,true),(60,false)]
theorem der_25885 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25885 :=
  CNF.rup_sound cl_25885 [cl_2781,cl_24767] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2781 v h) (hints_cons _ _ _ (der_24767 v h) (by intro d hd; cases hd)))
def cl_25886 : CNF.NClause := [(105,true),(50,false),(33,false),(37,false),(54,false),(60,true)]
theorem der_25886 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25886 :=
  CNF.rup_sound cl_25886 [cl_2789,cl_2785] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2789 v h) (hints_cons _ _ _ (inp_2785 v h) (by intro d hd; cases hd)))
def cl_25887 : CNF.NClause := [(105,true),(41,true),(37,false),(50,true),(54,false),(60,true)]
theorem der_25887 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25887 :=
  CNF.rup_sound cl_25887 [cl_2797,cl_25719] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2797 v h) (hints_cons _ _ _ (der_25719 v h) (by intro d hd; cases hd)))
def cl_25888 : CNF.NClause := [(105,true),(50,false),(33,false),(37,false),(54,true),(60,true)]
theorem der_25888 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25888 :=
  CNF.rup_sound cl_25888 [cl_2805,cl_25060] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2805 v h) (hints_cons _ _ _ (der_25060 v h) (by intro d hd; cases hd)))
def cl_25889 : CNF.NClause := [(105,true),(33,false),(41,true),(37,false),(50,true),(54,true)]
theorem der_25889 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25889 :=
  CNF.rup_sound cl_25889 [cl_2813,cl_25885] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2813 v h) (hints_cons _ _ _ (der_25885 v h) (by intro d hd; cases hd)))
def cl_25890 : CNF.NClause := [(123,true),(51,false),(31,true),(46,false),(36,false),(56,true)]
theorem der_25890 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25890 :=
  CNF.rup_sound cl_25890 [cl_3942,cl_23818] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3942 v h) (hints_cons _ _ _ (der_23818 v h) (by intro d hd; cases hd)))
def cl_25891 : CNF.NClause := [(123,true),(51,false),(31,true),(46,true),(36,false),(56,true)]
theorem der_25891 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25891 :=
  CNF.rup_sound cl_25891 [cl_3950,cl_3946] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3950 v h) (hints_cons _ _ _ (inp_3946 v h) (by intro d hd; cases hd)))
def cl_25892 : CNF.NClause := [(123,true),(46,false),(31,true),(41,true),(36,false),(51,true)]
theorem der_25892 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25892 :=
  CNF.rup_sound cl_25892 [cl_3958,cl_25872] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3958 v h) (hints_cons _ _ _ (der_25872 v h) (by intro d hd; cases hd)))
def cl_25893 : CNF.NClause := [(106,true),(34,false),(40,false),(47,false),(53,false),(57,false)]
theorem der_25893 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25893 :=
  CNF.rup_sound cl_25893 [cl_2821,cl_2817] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2821 v h) (hints_cons _ _ _ (inp_2817 v h) (by intro d hd; cases hd)))
def cl_25894 : CNF.NClause := [(106,true),(40,true),(41,true),(47,false),(53,false),(57,false)]
theorem der_25894 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25894 :=
  CNF.rup_sound cl_25894 [cl_2823,cl_25425] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2823 v h) (hints_cons _ _ _ (der_25425 v h) (by intro d hd; cases hd)))
def cl_25895 : CNF.NClause := [(106,true),(40,false),(41,true),(47,true),(53,false),(57,false)]
theorem der_25895 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25895 :=
  CNF.rup_sound cl_25895 [cl_2829,cl_25428] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2829 v h) (hints_cons _ _ _ (der_25428 v h) (by intro d hd; cases hd)))
def cl_25896 : CNF.NClause := [(106,true),(40,true),(41,true),(47,true),(53,false),(57,false)]
theorem der_25896 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25896 :=
  CNF.rup_sound cl_25896 [cl_2831,cl_25429] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2831 v h) (hints_cons _ _ _ (der_25429 v h) (by intro d hd; cases hd)))
def cl_25897 : CNF.NClause := [(106,true),(34,false),(40,false),(47,false),(53,true),(57,false)]
theorem der_25897 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25897 :=
  CNF.rup_sound cl_25897 [cl_2837,cl_23737] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2837 v h) (hints_cons _ _ _ (der_23737 v h) (by intro d hd; cases hd)))
def cl_25898 : CNF.NClause := [(106,true),(34,false),(40,true),(47,false),(53,true),(57,false)]
theorem der_25898 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25898 :=
  CNF.rup_sound cl_25898 [cl_2839,cl_23737] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2839 v h) (hints_cons _ _ _ (der_23737 v h) (by intro d hd; cases hd)))
def cl_25899 : CNF.NClause := [(106,true),(34,false),(40,false),(47,true),(53,true),(57,false)]
theorem der_25899 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25899 :=
  CNF.rup_sound cl_25899 [cl_2845,cl_23750] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2845 v h) (hints_cons _ _ _ (der_23750 v h) (by intro d hd; cases hd)))
def cl_25900 : CNF.NClause := [(106,true),(34,false),(40,true),(41,true),(53,true),(57,false)]
theorem der_25900 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25900 :=
  CNF.rup_sound cl_25900 [cl_2847,cl_25898] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2847 v h) (hints_cons _ _ _ (der_25898 v h) (by intro d hd; cases hd)))
def cl_25901 : CNF.NClause := [(106,true),(34,false),(40,false),(41,true),(47,false),(53,false)]
theorem der_25901 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25901 :=
  CNF.rup_sound cl_25901 [cl_2853,cl_25893] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2853 v h) (hints_cons _ _ _ (der_25893 v h) (by intro d hd; cases hd)))
def cl_25902 : CNF.NClause := [(106,true),(34,false),(40,true),(41,true),(47,false),(53,false)]
theorem der_25902 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25902 :=
  CNF.rup_sound cl_25902 [cl_2855,cl_25894] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2855 v h) (hints_cons _ _ _ (der_25894 v h) (by intro d hd; cases hd)))
def cl_25903 : CNF.NClause := [(106,true),(34,false),(40,false),(41,true),(47,true),(53,false)]
theorem der_25903 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25903 :=
  CNF.rup_sound cl_25903 [cl_2861,cl_25895] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2861 v h) (hints_cons _ _ _ (der_25895 v h) (by intro d hd; cases hd)))
def cl_25904 : CNF.NClause := [(106,true),(34,false),(40,true),(41,true),(53,false),(57,true)]
theorem der_25904 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25904 :=
  CNF.rup_sound cl_25904 [cl_2863,cl_25902] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2863 v h) (hints_cons _ _ _ (der_25902 v h) (by intro d hd; cases hd)))
def cl_25905 : CNF.NClause := [(106,true),(40,false),(41,true),(47,false),(53,true),(57,true)]
theorem der_25905 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25905 :=
  CNF.rup_sound cl_25905 [cl_2869,cl_25446] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2869 v h) (hints_cons _ _ _ (der_25446 v h) (by intro d hd; cases hd)))
def cl_25906 : CNF.NClause := [(106,true),(34,false),(40,true),(41,true),(47,false),(53,true)]
theorem der_25906 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25906 :=
  CNF.rup_sound cl_25906 [cl_2871,cl_25898] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2871 v h) (hints_cons _ _ _ (der_25898 v h) (by intro d hd; cases hd)))
def cl_25907 : CNF.NClause := [(106,true),(34,false),(40,false),(41,true),(53,true),(57,true)]
theorem der_25907 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25907 :=
  CNF.rup_sound cl_25907 [cl_2877,cl_25905] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2877 v h) (hints_cons _ _ _ (der_25905 v h) (by intro d hd; cases hd)))
def cl_25908 : CNF.NClause := [(104,true),(59,false),(38,true),(35,false),(52,false),(49,false)]
theorem der_25908 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25908 :=
  CNF.rup_sound cl_25908 [cl_2695,cl_25816] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2695 v h) (hints_cons _ _ _ (der_25816 v h) (by intro d hd; cases hd)))
def cl_25909 : CNF.NClause := [(104,true),(49,true),(38,true),(35,false),(52,false),(59,false)]
theorem der_25909 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25909 :=
  CNF.rup_sound cl_25909 [cl_2703,cl_25817] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2703 v h) (hints_cons _ _ _ (der_25817 v h) (by intro d hd; cases hd)))
def cl_25910 : CNF.NClause := [(104,true),(59,false),(35,false),(38,true),(49,false),(52,true)]
theorem der_25910 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25910 :=
  CNF.rup_sound cl_25910 [cl_2711,cl_25841] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2711 v h) (hints_cons _ _ _ (der_25841 v h) (by intro d hd; cases hd)))
def cl_25911 : CNF.NClause := [(94,true),(40,false),(45,false),(50,false),(55,false),(56,false)]
theorem der_25911 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25911 :=
  CNF.rup_sound cl_25911 [cl_2050,cl_25569] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2050 v h) (hints_cons _ _ _ (der_25569 v h) (by intro d hd; cases hd)))
def cl_25912 : CNF.NClause := [(94,true),(56,false),(40,true),(45,false),(50,false),(55,false)]
theorem der_25912 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25912 :=
  CNF.rup_sound cl_25912 [cl_2052,cl_25570] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2052 v h) (hints_cons _ _ _ (der_25570 v h) (by intro d hd; cases hd)))
def cl_25913 : CNF.NClause := [(94,true),(40,false),(45,true),(50,false),(55,false),(56,false)]
theorem der_25913 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25913 :=
  CNF.rup_sound cl_25913 [cl_2054,cl_25576] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2054 v h) (hints_cons _ _ _ (der_25576 v h) (by intro d hd; cases hd)))
def cl_25914 : CNF.NClause := [(94,true),(56,false),(40,true),(45,true),(50,false),(55,false)]
theorem der_25914 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25914 :=
  CNF.rup_sound cl_25914 [cl_2056,cl_25577] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2056 v h) (hints_cons _ _ _ (der_25577 v h) (by intro d hd; cases hd)))
def cl_25915 : CNF.NClause := [(94,true),(40,false),(35,true),(45,false),(55,false),(56,false)]
theorem der_25915 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25915 :=
  CNF.rup_sound cl_25915 [cl_2058,cl_25911] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2058 v h) (hints_cons _ _ _ (der_25911 v h) (by intro d hd; cases hd)))
def cl_25916 : CNF.NClause := [(94,true),(56,false),(40,true),(45,false),(50,true),(55,false)]
theorem der_25916 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25916 :=
  CNF.rup_sound cl_25916 [cl_2060,cl_25584] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2060 v h) (hints_cons _ _ _ (der_25584 v h) (by intro d hd; cases hd)))
def cl_25917 : CNF.NClause := [(94,true),(40,false),(35,true),(45,true),(55,false),(56,false)]
theorem der_25917 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25917 :=
  CNF.rup_sound cl_25917 [cl_2062,cl_25913] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2062 v h) (hints_cons _ _ _ (der_25913 v h) (by intro d hd; cases hd)))
def cl_25919 : CNF.NClause := [(94,true),(40,false),(45,false),(50,false),(55,true),(56,false)]
theorem der_25919 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25919 :=
  CNF.rup_sound cl_25919 [cl_2066,cl_25279] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2066 v h) (hints_cons _ _ _ (der_25279 v h) (by intro d hd; cases hd)))
def cl_25921 : CNF.NClause := [(94,true),(40,false),(45,true),(50,false),(55,true),(56,false)]
theorem der_25921 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25921 :=
  CNF.rup_sound cl_25921 [cl_2070,cl_2069] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2070 v h) (hints_cons _ _ _ (inp_2069 v h) (by intro d hd; cases hd)))
def cl_25923 : CNF.NClause := [(94,true),(40,false),(35,true),(45,false),(50,true),(56,false)]
theorem der_25923 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25923 :=
  CNF.rup_sound cl_25923 [cl_2074,cl_25915] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2074 v h) (hints_cons _ _ _ (der_25915 v h) (by intro d hd; cases hd)))
def cl_25926 : CNF.NClause := [(94,true),(40,false),(35,true),(45,false),(50,false),(55,false)]
theorem der_25926 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25926 :=
  CNF.rup_sound cl_25926 [cl_2082,cl_25911] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2082 v h) (hints_cons _ _ _ (der_25911 v h) (by intro d hd; cases hd)))
def cl_25927 : CNF.NClause := [(94,true),(40,true),(45,false),(50,false),(55,false),(56,true)]
theorem der_25927 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25927 :=
  CNF.rup_sound cl_25927 [cl_2084,cl_23851] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2084 v h) (hints_cons _ _ _ (der_23851 v h) (by intro d hd; cases hd)))
def cl_25928 : CNF.NClause := [(94,true),(40,false),(35,true),(45,true),(50,false),(55,false)]
theorem der_25928 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25928 :=
  CNF.rup_sound cl_25928 [cl_2086,cl_25913] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2086 v h) (hints_cons _ _ _ (der_25913 v h) (by intro d hd; cases hd)))
def cl_25929 : CNF.NClause := [(94,true),(50,false),(40,true),(45,true),(55,false),(56,true)]
theorem der_25929 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25929 :=
  CNF.rup_sound cl_25929 [cl_2088,cl_2087] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2088 v h) (hints_cons _ _ _ (inp_2087 v h) (by intro d hd; cases hd)))
def cl_25930 : CNF.NClause := [(94,true),(40,false),(35,true),(45,false),(50,true),(55,false)]
theorem der_25930 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25930 :=
  CNF.rup_sound cl_25930 [cl_2090,cl_25915] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2090 v h) (hints_cons _ _ _ (der_25915 v h) (by intro d hd; cases hd)))
def cl_25931 : CNF.NClause := [(94,true),(55,false),(40,true),(45,false),(50,true),(35,true)]
theorem der_25931 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25931 :=
  CNF.rup_sound cl_25931 [cl_2092,cl_25916] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2092 v h) (hints_cons _ _ _ (der_25916 v h) (by intro d hd; cases hd)))
def cl_25932 : CNF.NClause := [(94,true),(40,false),(35,true),(45,true),(55,false),(56,true)]
theorem der_25932 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25932 :=
  CNF.rup_sound cl_25932 [cl_2094,cl_25928] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2094 v h) (hints_cons _ _ _ (der_25928 v h) (by intro d hd; cases hd)))
def cl_25933 : CNF.NClause := [(94,true),(40,false),(45,false),(50,false),(55,true),(56,true)]
theorem der_25933 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25933 :=
  CNF.rup_sound cl_25933 [cl_2098,cl_25291] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2098 v h) (hints_cons _ _ _ (der_25291 v h) (by intro d hd; cases hd)))
def cl_25934 : CNF.NClause := [(94,true),(50,false),(40,true),(45,false),(55,true),(56,true)]
theorem der_25934 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25934 :=
  CNF.rup_sound cl_25934 [cl_2100,cl_25293] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2100 v h) (hints_cons _ _ _ (der_25293 v h) (by intro d hd; cases hd)))
def cl_25935 : CNF.NClause := [(94,true),(40,false),(45,true),(50,false),(55,true),(56,true)]
theorem der_25935 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25935 :=
  CNF.rup_sound cl_25935 [cl_2102,cl_23857] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2102 v h) (hints_cons _ _ _ (der_23857 v h) (by intro d hd; cases hd)))
def cl_25936 : CNF.NClause := [(94,true),(40,false),(35,true),(45,false),(50,true),(55,true)]
theorem der_25936 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25936 :=
  CNF.rup_sound cl_25936 [cl_2106,cl_25923] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2106 v h) (hints_cons _ _ _ (der_25923 v h) (by intro d hd; cases hd)))
def cl_25937 : CNF.NClause := [(99,true),(43,false),(39,false),(47,false),(51,false),(60,false)]
theorem der_25937 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25937 :=
  CNF.rup_sound cl_25937 [cl_2370,cl_2369] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2370 v h) (hints_cons _ _ _ (inp_2369 v h) (by intro d hd; cases hd)))
def cl_25938 : CNF.NClause := [(99,true),(51,false),(39,true),(47,false),(43,false),(60,false)]
theorem der_25938 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25938 :=
  CNF.rup_sound cl_25938 [cl_2372,cl_24737] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2372 v h) (hints_cons _ _ _ (der_24737 v h) (by intro d hd; cases hd)))
def cl_25939 : CNF.NClause := [(99,true),(47,false),(43,true),(39,false),(51,false),(60,false)]
theorem der_25939 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25939 :=
  CNF.rup_sound cl_25939 [cl_2374,cl_25622] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2374 v h) (hints_cons _ _ _ (der_25622 v h) (by intro d hd; cases hd)))
def cl_25940 : CNF.NClause := [(99,true),(51,false),(35,true),(47,false),(60,false),(39,true)]
theorem der_25940 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25940 :=
  CNF.rup_sound cl_25940 [cl_2376,cl_25938] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2376 v h) (hints_cons _ _ _ (der_25938 v h) (by intro d hd; cases hd)))
def cl_25941 : CNF.NClause := [(99,true),(43,false),(39,false),(47,true),(51,false),(60,false)]
theorem der_25941 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25941 :=
  CNF.rup_sound cl_25941 [cl_2378,cl_23841] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2378 v h) (hints_cons _ _ _ (der_23841 v h) (by intro d hd; cases hd)))
def cl_25942 : CNF.NClause := [(99,true),(43,false),(39,true),(47,true),(51,false),(60,false)]
theorem der_25942 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25942 :=
  CNF.rup_sound cl_25942 [cl_2380,cl_24739] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2380 v h) (hints_cons _ _ _ (der_24739 v h) (by intro d hd; cases hd)))
def cl_25943 : CNF.NClause := [(99,true),(51,false),(43,true),(47,true),(39,false),(60,false)]
theorem der_25943 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25943 :=
  CNF.rup_sound cl_25943 [cl_2382,cl_25623] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2382 v h) (hints_cons _ _ _ (der_25623 v h) (by intro d hd; cases hd)))
def cl_25944 : CNF.NClause := [(99,true),(51,false),(39,true),(43,true),(47,true),(60,false)]
theorem der_25944 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25944 :=
  CNF.rup_sound cl_25944 [cl_2384,cl_24740] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2384 v h) (hints_cons _ _ _ (der_24740 v h) (by intro d hd; cases hd)))
def cl_25945 : CNF.NClause := [(99,true),(43,false),(35,true),(39,false),(47,false),(60,false)]
theorem der_25945 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25945 :=
  CNF.rup_sound cl_25945 [cl_2386,cl_25937] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2386 v h) (hints_cons _ _ _ (der_25937 v h) (by intro d hd; cases hd)))
def cl_25946 : CNF.NClause := [(99,true),(43,false),(60,false),(35,true),(47,false),(39,true)]
theorem der_25946 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25946 :=
  CNF.rup_sound cl_25946 [cl_2388,cl_25938] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2388 v h) (hints_cons _ _ _ (der_25938 v h) (by intro d hd; cases hd)))
def cl_25947 : CNF.NClause := [(99,true),(47,false),(43,true),(39,false),(51,true),(60,false)]
theorem der_25947 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25947 :=
  CNF.rup_sound cl_25947 [cl_2390,cl_25624] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2390 v h) (hints_cons _ _ _ (der_25624 v h) (by intro d hd; cases hd)))
def cl_25948 : CNF.NClause := [(99,true),(43,true),(60,false),(39,true),(47,false),(51,true)]
theorem der_25948 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25948 :=
  CNF.rup_sound cl_25948 [cl_2392,cl_24744] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2392 v h) (hints_cons _ _ _ (der_24744 v h) (by intro d hd; cases hd)))
def cl_25949 : CNF.NClause := [(99,true),(47,true),(35,true),(39,false),(60,false),(43,false)]
theorem der_25949 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25949 :=
  CNF.rup_sound cl_25949 [cl_2394,cl_25941] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2394 v h) (hints_cons _ _ _ (der_25941 v h) (by intro d hd; cases hd)))
def cl_25950 : CNF.NClause := [(99,true),(47,true),(35,true),(60,false),(51,true),(43,false)]
theorem der_25950 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25950 :=
  CNF.rup_sound cl_25950 [cl_2396,cl_25949] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2396 v h) (hints_cons _ _ _ (der_25949 v h) (by intro d hd; cases hd)))
def cl_25951 : CNF.NClause := [(99,true),(60,false),(43,true),(47,true),(51,true),(39,false)]
theorem der_25951 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25951 :=
  CNF.rup_sound cl_25951 [cl_2398,cl_25625] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2398 v h) (hints_cons _ _ _ (der_25625 v h) (by intro d hd; cases hd)))
def cl_25952 : CNF.NClause := [(99,true),(43,false),(35,true),(39,false),(47,false),(51,false)]
theorem der_25952 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25952 :=
  CNF.rup_sound cl_25952 [cl_2402,cl_25937] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2402 v h) (hints_cons _ _ _ (der_25937 v h) (by intro d hd; cases hd)))
def cl_25953 : CNF.NClause := [(99,true),(51,false),(39,true),(47,false),(43,false),(60,true)]
theorem der_25953 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25953 :=
  CNF.rup_sound cl_25953 [cl_2404,cl_24745] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2404 v h) (hints_cons _ _ _ (der_24745 v h) (by intro d hd; cases hd)))
def cl_25954 : CNF.NClause := [(99,true),(47,false),(43,true),(39,false),(51,false),(60,true)]
theorem der_25954 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25954 :=
  CNF.rup_sound cl_25954 [cl_2406,cl_25626] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2406 v h) (hints_cons _ _ _ (der_25626 v h) (by intro d hd; cases hd)))
def cl_25955 : CNF.NClause := [(99,true),(51,false),(39,true),(43,true),(47,false),(35,true)]
theorem der_25955 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25955 :=
  CNF.rup_sound cl_25955 [cl_2408,cl_25940] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2408 v h) (hints_cons _ _ _ (der_25940 v h) (by intro d hd; cases hd)))
def cl_25956 : CNF.NClause := [(99,true),(43,false),(39,false),(47,true),(51,false),(60,true)]
theorem der_25956 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25956 :=
  CNF.rup_sound cl_25956 [cl_2410,cl_2409] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2410 v h) (hints_cons _ _ _ (inp_2409 v h) (by intro d hd; cases hd)))
def cl_25957 : CNF.NClause := [(99,true),(51,false),(39,true),(47,true),(43,false),(60,true)]
theorem der_25957 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25957 :=
  CNF.rup_sound cl_25957 [cl_2412,cl_24747] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2412 v h) (hints_cons _ _ _ (der_24747 v h) (by intro d hd; cases hd)))
def cl_25958 : CNF.NClause := [(99,true),(51,false),(43,true),(47,true),(39,false),(60,true)]
theorem der_25958 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25958 :=
  CNF.rup_sound cl_25958 [cl_2414,cl_25627] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2414 v h) (hints_cons _ _ _ (der_25627 v h) (by intro d hd; cases hd)))
def cl_25959 : CNF.NClause := [(99,true),(43,false),(35,true),(39,false),(47,false),(60,true)]
theorem der_25959 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25959 :=
  CNF.rup_sound cl_25959 [cl_2418,cl_25952] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2418 v h) (hints_cons _ _ _ (der_25952 v h) (by intro d hd; cases hd)))
def cl_25960 : CNF.NClause := [(99,true),(43,false),(51,true),(47,false),(39,true),(60,true)]
theorem der_25960 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25960 :=
  CNF.rup_sound cl_25960 [cl_2420,cl_24749] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2420 v h) (hints_cons _ _ _ (der_24749 v h) (by intro d hd; cases hd)))
def cl_25961 : CNF.NClause := [(99,true),(47,false),(43,true),(39,false),(51,true),(60,true)]
theorem der_25961 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25961 :=
  CNF.rup_sound cl_25961 [cl_2422,cl_25628] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2422 v h) (hints_cons _ _ _ (der_25628 v h) (by intro d hd; cases hd)))
def cl_25962 : CNF.NClause := [(99,true),(35,true),(39,false),(47,true),(51,true),(43,false)]
theorem der_25962 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25962 :=
  CNF.rup_sound cl_25962 [cl_2426,cl_25949] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2426 v h) (hints_cons _ _ _ (der_25949 v h) (by intro d hd; cases hd)))
def cl_25963 : CNF.NClause := [(104,true),(59,false),(41,false),(49,false),(52,false),(38,false)]
theorem der_25963 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25963 :=
  CNF.rup_sound cl_25963 [cl_2690,cl_25843] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2690 v h) (hints_cons _ _ _ (der_25843 v h) (by intro d hd; cases hd)))
def cl_25964 : CNF.NClause := [(104,true),(41,false),(38,true),(49,false),(52,false),(59,false)]
theorem der_25964 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25964 :=
  CNF.rup_sound cl_25964 [cl_2692,cl_25816] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2692 v h) (hints_cons _ _ _ (der_25816 v h) (by intro d hd; cases hd)))
def cl_25965 : CNF.NClause := [(104,true),(59,false),(35,true),(49,false),(52,false),(38,false)]
theorem der_25965 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25965 :=
  CNF.rup_sound cl_25965 [cl_2694,cl_25963] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2694 v h) (hints_cons _ _ _ (der_25963 v h) (by intro d hd; cases hd)))
def cl_25966 : CNF.NClause := [(104,true),(52,false),(38,true),(41,true),(49,false),(59,false)]
theorem der_25966 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25966 :=
  CNF.rup_sound cl_25966 [cl_2696,cl_25908] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2696 v h) (hints_cons _ _ _ (der_25908 v h) (by intro d hd; cases hd)))
def cl_25967 : CNF.NClause := [(104,true),(59,false),(41,false),(49,true),(52,false),(38,false)]
theorem der_25967 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25967 :=
  CNF.rup_sound cl_25967 [cl_2698,cl_2697] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2698 v h) (hints_cons _ _ _ (inp_2697 v h) (by intro d hd; cases hd)))
def cl_25968 : CNF.NClause := [(104,true),(41,false),(38,true),(49,true),(52,false),(59,false)]
theorem der_25968 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25968 :=
  CNF.rup_sound cl_25968 [cl_2700,cl_25817] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2700 v h) (hints_cons _ _ _ (der_25817 v h) (by intro d hd; cases hd)))
def cl_25969 : CNF.NClause := [(104,true),(59,false),(35,true),(49,true),(52,false),(38,false)]
theorem der_25969 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25969 :=
  CNF.rup_sound cl_25969 [cl_2702,cl_25967] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2702 v h) (hints_cons _ _ _ (der_25967 v h) (by intro d hd; cases hd)))
def cl_25970 : CNF.NClause := [(104,true),(49,true),(38,true),(41,true),(52,false),(59,false)]
theorem der_25970 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25970 :=
  CNF.rup_sound cl_25970 [cl_2704,cl_25909] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2704 v h) (hints_cons _ _ _ (der_25909 v h) (by intro d hd; cases hd)))
def cl_25971 : CNF.NClause := [(104,true),(59,false),(41,false),(49,false),(52,true),(38,false)]
theorem der_25971 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25971 :=
  CNF.rup_sound cl_25971 [cl_2706,cl_25842] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2706 v h) (hints_cons _ _ _ (der_25842 v h) (by intro d hd; cases hd)))
def cl_25972 : CNF.NClause := [(104,true),(41,false),(38,true),(49,false),(52,true),(59,false)]
theorem der_25972 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25972 :=
  CNF.rup_sound cl_25972 [cl_2708,cl_25841] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2708 v h) (hints_cons _ _ _ (der_25841 v h) (by intro d hd; cases hd)))
def cl_25973 : CNF.NClause := [(104,true),(59,false),(35,true),(41,true),(49,false),(38,false)]
theorem der_25973 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25973 :=
  CNF.rup_sound cl_25973 [cl_2710,cl_25965] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2710 v h) (hints_cons _ _ _ (der_25965 v h) (by intro d hd; cases hd)))
def cl_25974 : CNF.NClause := [(104,true),(59,false),(38,true),(41,true),(52,true),(49,false)]
theorem der_25974 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25974 :=
  CNF.rup_sound cl_25974 [cl_2712,cl_25910] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2712 v h) (hints_cons _ _ _ (der_25910 v h) (by intro d hd; cases hd)))
def cl_25975 : CNF.NClause := [(104,true),(59,false),(41,false),(49,true),(52,true),(38,false)]
theorem der_25975 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25975 :=
  CNF.rup_sound cl_25975 [cl_2714,cl_23830] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2714 v h) (hints_cons _ _ _ (der_23830 v h) (by intro d hd; cases hd)))
def cl_25976 : CNF.NClause := [(104,true),(41,false),(38,true),(49,true),(52,true),(59,false)]
theorem der_25976 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25976 :=
  CNF.rup_sound cl_25976 [cl_2716,cl_23830] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2716 v h) (hints_cons _ _ _ (der_23830 v h) (by intro d hd; cases hd)))
def cl_25977 : CNF.NClause := [(104,true),(59,false),(35,true),(49,true),(52,true),(38,false)]
theorem der_25977 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25977 :=
  CNF.rup_sound cl_25977 [cl_2718,cl_25975] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2718 v h) (hints_cons _ _ _ (der_25975 v h) (by intro d hd; cases hd)))
def cl_25978 : CNF.NClause := [(104,true),(41,false),(38,false),(49,false),(52,false),(59,true)]
theorem der_25978 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25978 :=
  CNF.rup_sound cl_25978 [cl_2722,cl_25818] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2722 v h) (hints_cons _ _ _ (der_25818 v h) (by intro d hd; cases hd)))
def cl_25979 : CNF.NClause := [(104,true),(41,false),(38,true),(49,false),(52,false),(59,true)]
theorem der_25979 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25979 :=
  CNF.rup_sound cl_25979 [cl_2724,cl_25816] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2724 v h) (hints_cons _ _ _ (der_25816 v h) (by intro d hd; cases hd)))
def cl_25980 : CNF.NClause := [(104,true),(38,false),(35,true),(41,true),(49,false),(52,false)]
theorem der_25980 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25980 :=
  CNF.rup_sound cl_25980 [cl_2726,cl_25973] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2726 v h) (hints_cons _ _ _ (der_25973 v h) (by intro d hd; cases hd)))
def cl_25981 : CNF.NClause := [(104,true),(52,false),(41,true),(49,false),(35,true),(59,true)]
theorem der_25981 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25981 :=
  CNF.rup_sound cl_25981 [cl_2728,cl_25980] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2728 v h) (hints_cons _ _ _ (der_25980 v h) (by intro d hd; cases hd)))
def cl_25982 : CNF.NClause := [(104,true),(41,false),(38,false),(49,true),(52,false),(59,true)]
theorem der_25982 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25982 :=
  CNF.rup_sound cl_25982 [cl_2730,cl_23805] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2730 v h) (hints_cons _ _ _ (der_23805 v h) (by intro d hd; cases hd)))
def cl_25983 : CNF.NClause := [(104,true),(41,false),(38,true),(35,true),(49,true),(52,false)]
theorem der_25983 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25983 :=
  CNF.rup_sound cl_25983 [cl_2732,cl_25968] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2732 v h) (hints_cons _ _ _ (der_25968 v h) (by intro d hd; cases hd)))
def cl_25984 : CNF.NClause := [(104,true),(52,false),(41,true),(49,true),(38,false),(59,true)]
theorem der_25984 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25984 :=
  CNF.rup_sound cl_25984 [cl_2734,cl_23825] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2734 v h) (hints_cons _ _ _ (der_23825 v h) (by intro d hd; cases hd)))
def cl_25985 : CNF.NClause := [(104,true),(41,false),(38,false),(49,false),(52,true),(59,true)]
theorem der_25985 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25985 :=
  CNF.rup_sound cl_25985 [cl_2738,cl_25819] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2738 v h) (hints_cons _ _ _ (der_25819 v h) (by intro d hd; cases hd)))
def cl_25986 : CNF.NClause := [(104,true),(41,false),(38,true),(35,true),(49,false),(52,true)]
theorem der_25986 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25986 :=
  CNF.rup_sound cl_25986 [cl_2740,cl_25972] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2740 v h) (hints_cons _ _ _ (der_25972 v h) (by intro d hd; cases hd)))
def cl_25987 : CNF.NClause := [(104,true),(38,false),(35,true),(41,true),(49,false),(52,true)]
theorem der_25987 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25987 :=
  CNF.rup_sound cl_25987 [cl_2742,cl_25973] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2742 v h) (hints_cons _ _ _ (der_25973 v h) (by intro d hd; cases hd)))
def cl_25988 : CNF.NClause := [(104,true),(41,false),(38,false),(49,true),(52,true),(59,true)]
theorem der_25988 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25988 :=
  CNF.rup_sound cl_25988 [cl_2746,cl_23806] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2746 v h) (hints_cons _ _ _ (der_23806 v h) (by intro d hd; cases hd)))
def cl_25989 : CNF.NClause := [(109,true),(46,false),(37,true),(44,false),(53,false),(58,false)]
theorem der_25989 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25989 :=
  CNF.rup_sound cl_25989 [cl_3012,cl_3011] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3012 v h) (hints_cons _ _ _ (inp_3011 v h) (by intro d hd; cases hd)))
def cl_25990 : CNF.NClause := [(109,true),(58,false),(44,true),(46,false),(53,false),(37,false)]
theorem der_25990 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25990 :=
  CNF.rup_sound cl_25990 [cl_3014,cl_23874] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3014 v h) (hints_cons _ _ _ (der_23874 v h) (by intro d hd; cases hd)))
def cl_25991 : CNF.NClause := [(109,true),(46,false),(37,true),(35,true),(53,false),(58,false)]
theorem der_25991 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25991 :=
  CNF.rup_sound cl_25991 [cl_3016,cl_25989] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3016 v h) (hints_cons _ _ _ (der_25989 v h) (by intro d hd; cases hd)))
def cl_25992 : CNF.NClause := [(109,true),(35,true),(44,false),(37,false),(53,false),(58,false)]
theorem der_25992 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25992 :=
  CNF.rup_sound cl_25992 [cl_3018,cl_3010] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3018 v h) (hints_cons _ _ _ (inp_3010 v h) (by intro d hd; cases hd)))
def cl_25993 : CNF.NClause := [(109,true),(46,true),(37,true),(44,false),(53,false),(58,false)]
theorem der_25993 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25993 :=
  CNF.rup_sound cl_25993 [cl_3020,cl_24790] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3020 v h) (hints_cons _ _ _ (der_24790 v h) (by intro d hd; cases hd)))
def cl_25994 : CNF.NClause := [(109,true),(35,true),(44,true),(37,false),(53,false),(58,false)]
theorem der_25994 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25994 :=
  CNF.rup_sound cl_25994 [cl_3022,cl_25990] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3022 v h) (hints_cons _ _ _ (der_25990 v h) (by intro d hd; cases hd)))
def cl_25995 : CNF.NClause := [(109,true),(35,true),(44,true),(37,true),(53,false),(58,false)]
theorem der_25995 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25995 :=
  CNF.rup_sound cl_25995 [cl_3024,cl_25991] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3024 v h) (hints_cons _ _ _ (der_25991 v h) (by intro d hd; cases hd)))
def cl_25996 : CNF.NClause := [(109,true),(53,true),(44,false),(46,false),(37,false),(58,false)]
theorem der_25996 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25996 :=
  CNF.rup_sound cl_25996 [cl_3026,cl_3025] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3026 v h) (hints_cons _ _ _ (inp_3025 v h) (by intro d hd; cases hd)))
def cl_25997 : CNF.NClause := [(109,true),(58,false),(37,true),(46,false),(44,false),(35,true)]
theorem der_25997 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25997 :=
  CNF.rup_sound cl_25997 [cl_3028,cl_25989] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3028 v h) (hints_cons _ _ _ (der_25989 v h) (by intro d hd; cases hd)))
def cl_25998 : CNF.NClause := [(109,true),(35,true),(44,true),(46,false),(37,false),(58,false)]
theorem der_25998 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25998 :=
  CNF.rup_sound cl_25998 [cl_3030,cl_25990] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3030 v h) (hints_cons _ _ _ (der_25990 v h) (by intro d hd; cases hd)))
def cl_25999 : CNF.NClause := [(109,true),(58,false),(37,true),(46,false),(35,true),(44,true)]
theorem der_25999 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25999 :=
  CNF.rup_sound cl_25999 [cl_3032,cl_25991] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3032 v h) (hints_cons _ _ _ (der_25991 v h) (by intro d hd; cases hd)))
def cl_26000 : CNF.NClause := [(109,true),(46,true),(44,false),(37,false),(53,true),(58,false)]
theorem der_26000 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26000 :=
  CNF.rup_sound cl_26000 [cl_3034,cl_23746] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3034 v h) (hints_cons _ _ _ (der_23746 v h) (by intro d hd; cases hd)))
def cl_26001 : CNF.NClause := [(109,true),(46,true),(37,true),(44,false),(53,true),(58,false)]
theorem der_26001 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26001 :=
  CNF.rup_sound cl_26001 [cl_3036,cl_24794] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3036 v h) (hints_cons _ _ _ (der_24794 v h) (by intro d hd; cases hd)))
def cl_26002 : CNF.NClause := [(109,true),(46,true),(35,true),(44,true),(37,false),(58,false)]
theorem der_26002 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26002 :=
  CNF.rup_sound cl_26002 [cl_3038,cl_25994] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3038 v h) (hints_cons _ _ _ (der_25994 v h) (by intro d hd; cases hd)))
def cl_26003 : CNF.NClause := [(109,true),(37,false),(44,false),(46,false),(53,false),(58,true)]
theorem der_26003 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26003 :=
  CNF.rup_sound cl_26003 [cl_3042,cl_25047] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3042 v h) (hints_cons _ _ _ (der_25047 v h) (by intro d hd; cases hd)))
def cl_26004 : CNF.NClause := [(109,true),(46,false),(35,true),(44,false),(37,true),(53,false)]
theorem der_26004 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26004 :=
  CNF.rup_sound cl_26004 [cl_3044,cl_25989] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3044 v h) (hints_cons _ _ _ (der_25989 v h) (by intro d hd; cases hd)))
def cl_26005 : CNF.NClause := [(109,true),(37,false),(44,true),(46,false),(53,false),(58,true)]
theorem der_26005 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26005 :=
  CNF.rup_sound cl_26005 [cl_3046,cl_23874] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3046 v h) (hints_cons _ _ _ (der_23874 v h) (by intro d hd; cases hd)))
def cl_26006 : CNF.NClause := [(109,true),(46,false),(37,true),(44,true),(35,true),(53,false)]
theorem der_26006 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26006 :=
  CNF.rup_sound cl_26006 [cl_3048,cl_25991] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3048 v h) (hints_cons _ _ _ (der_25991 v h) (by intro d hd; cases hd)))
def cl_26007 : CNF.NClause := [(109,true),(37,false),(44,false),(46,true),(53,false),(58,true)]
theorem der_26007 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26007 :=
  CNF.rup_sound cl_26007 [cl_3050,cl_25509] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3050 v h) (hints_cons _ _ _ (der_25509 v h) (by intro d hd; cases hd)))
def cl_26008 : CNF.NClause := [(109,true),(46,true),(35,true),(44,false),(37,true),(53,false)]
theorem der_26008 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26008 :=
  CNF.rup_sound cl_26008 [cl_3052,cl_25993] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3052 v h) (hints_cons _ _ _ (der_25993 v h) (by intro d hd; cases hd)))
def cl_26009 : CNF.NClause := [(109,true),(46,true),(37,false),(35,true),(44,true),(53,false)]
theorem der_26009 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26009 :=
  CNF.rup_sound cl_26009 [cl_3054,cl_25994] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3054 v h) (hints_cons _ _ _ (der_25994 v h) (by intro d hd; cases hd)))
def cl_26010 : CNF.NClause := [(109,true),(46,false),(37,false),(44,false),(53,true),(58,true)]
theorem der_26010 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26010 :=
  CNF.rup_sound cl_26010 [cl_3058,cl_23741] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3058 v h) (hints_cons _ _ _ (der_23741 v h) (by intro d hd; cases hd)))
def cl_26011 : CNF.NClause := [(109,true),(37,true),(44,false),(46,false),(53,true),(35,true)]
theorem der_26011 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26011 :=
  CNF.rup_sound cl_26011 [cl_3060,cl_25997] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3060 v h) (hints_cons _ _ _ (der_25997 v h) (by intro d hd; cases hd)))
def cl_26012 : CNF.NClause := [(109,true),(53,true),(37,false),(35,true),(46,false),(44,true)]
theorem der_26012 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26012 :=
  CNF.rup_sound cl_26012 [cl_3062,cl_25998] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3062 v h) (hints_cons _ _ _ (der_25998 v h) (by intro d hd; cases hd)))
def cl_26013 : CNF.NClause := [(109,true),(53,true),(37,false),(46,true),(44,false),(58,true)]
theorem der_26013 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26013 :=
  CNF.rup_sound cl_26013 [cl_3066,cl_23768] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3066 v h) (hints_cons _ _ _ (der_23768 v h) (by intro d hd; cases hd)))
def cl_26014 : CNF.NClause := [(114,true),(57,false),(36,false),(48,false),(54,false),(42,false)]
theorem der_26014 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26014 :=
  CNF.rup_sound cl_26014 [cl_3330,cl_23840] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3330 v h) (hints_cons _ _ _ (der_23840 v h) (by intro d hd; cases hd)))
def cl_26015 : CNF.NClause := [(114,true),(57,false),(36,true),(48,false),(54,false),(42,false)]
theorem der_26015 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26015 :=
  CNF.rup_sound cl_26015 [cl_3332,cl_24895] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3332 v h) (hints_cons _ _ _ (der_24895 v h) (by intro d hd; cases hd)))
def cl_26016 : CNF.NClause := [(114,true),(57,false),(42,true),(48,false),(54,false),(36,false)]
theorem der_26016 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26016 :=
  CNF.rup_sound cl_26016 [cl_3334,cl_25342] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3334 v h) (hints_cons _ _ _ (der_25342 v h) (by intro d hd; cases hd)))
def cl_26017 : CNF.NClause := [(114,true),(54,false),(36,true),(48,false),(42,true),(57,false)]
theorem der_26017 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26017 :=
  CNF.rup_sound cl_26017 [cl_3336,cl_24896] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3336 v h) (hints_cons _ _ _ (der_24896 v h) (by intro d hd; cases hd)))
def cl_26018 : CNF.NClause := [(114,true),(57,false),(36,false),(48,true),(54,false),(42,false)]
theorem der_26018 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26018 :=
  CNF.rup_sound cl_26018 [cl_3338,cl_3337] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3338 v h) (hints_cons _ _ _ (inp_3337 v h) (by intro d hd; cases hd)))
def cl_26019 : CNF.NClause := [(114,true),(57,false),(36,true),(48,true),(54,false),(42,false)]
theorem der_26019 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26019 :=
  CNF.rup_sound cl_26019 [cl_3340,cl_24897] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3340 v h) (hints_cons _ _ _ (der_24897 v h) (by intro d hd; cases hd)))
def cl_26020 : CNF.NClause := [(114,true),(57,false),(42,true),(48,true),(54,false),(36,false)]
theorem der_26020 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26020 :=
  CNF.rup_sound cl_26020 [cl_3342,cl_25343] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3342 v h) (hints_cons _ _ _ (der_25343 v h) (by intro d hd; cases hd)))
def cl_26021 : CNF.NClause := [(114,true),(57,false),(42,true),(48,true),(54,false),(36,true)]
theorem der_26021 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26021 :=
  CNF.rup_sound cl_26021 [cl_3344,cl_24898] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3344 v h) (hints_cons _ _ _ (der_24898 v h) (by intro d hd; cases hd)))
def cl_26022 : CNF.NClause := [(114,true),(57,false),(36,false),(35,true),(48,false),(42,false)]
theorem der_26022 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26022 :=
  CNF.rup_sound cl_26022 [cl_3346,cl_26014] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3346 v h) (hints_cons _ _ _ (der_26014 v h) (by intro d hd; cases hd)))
def cl_26023 : CNF.NClause := [(114,true),(57,false),(36,true),(48,false),(54,true),(42,false)]
theorem der_26023 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26023 :=
  CNF.rup_sound cl_26023 [cl_3348,cl_24899] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3348 v h) (hints_cons _ _ _ (der_24899 v h) (by intro d hd; cases hd)))
def cl_26024 : CNF.NClause := [(114,true),(35,true),(42,true),(48,false),(36,false),(57,false)]
theorem der_26024 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26024 :=
  CNF.rup_sound cl_26024 [cl_3350,cl_26016] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3350 v h) (hints_cons _ _ _ (der_26016 v h) (by intro d hd; cases hd)))
def cl_26025 : CNF.NClause := [(114,true),(57,false),(36,true),(35,true),(54,true),(48,false)]
theorem der_26025 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26025 :=
  CNF.rup_sound cl_26025 [cl_3352,cl_26023] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3352 v h) (hints_cons _ _ _ (der_26023 v h) (by intro d hd; cases hd)))
def cl_26026 : CNF.NClause := [(114,true),(57,false),(36,false),(48,true),(54,true),(42,false)]
theorem der_26026 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26026 :=
  CNF.rup_sound cl_26026 [cl_3354,cl_25590] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3354 v h) (hints_cons _ _ _ (der_25590 v h) (by intro d hd; cases hd)))
def cl_26027 : CNF.NClause := [(114,true),(57,false),(36,true),(48,true),(54,true),(42,false)]
theorem der_26027 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26027 :=
  CNF.rup_sound cl_26027 [cl_3356,cl_24901] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3356 v h) (hints_cons _ _ _ (der_24901 v h) (by intro d hd; cases hd)))
def cl_26028 : CNF.NClause := [(114,true),(54,true),(42,true),(48,true),(36,false),(57,false)]
theorem der_26028 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26028 :=
  CNF.rup_sound cl_26028 [cl_3358,cl_25345] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3358 v h) (hints_cons _ _ _ (der_25345 v h) (by intro d hd; cases hd)))
def cl_26029 : CNF.NClause := [(114,true),(48,false),(36,false),(35,true),(42,false),(54,false)]
theorem der_26029 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26029 :=
  CNF.rup_sound cl_26029 [cl_3362,cl_26014] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3362 v h) (hints_cons _ _ _ (der_26014 v h) (by intro d hd; cases hd)))
def cl_26030 : CNF.NClause := [(114,true),(54,false),(42,false),(35,true),(48,false),(36,true)]
theorem der_26030 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26030 :=
  CNF.rup_sound cl_26030 [cl_3364,cl_26015] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3364 v h) (hints_cons _ _ _ (der_26015 v h) (by intro d hd; cases hd)))
def cl_26031 : CNF.NClause := [(114,true),(35,true),(36,false),(42,true),(48,false),(54,false)]
theorem der_26031 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26031 :=
  CNF.rup_sound cl_26031 [cl_3366,cl_26016] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3366 v h) (hints_cons _ _ _ (der_26016 v h) (by intro d hd; cases hd)))
def cl_26032 : CNF.NClause := [(114,true),(54,false),(36,true),(42,true),(35,true),(48,false)]
theorem der_26032 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26032 :=
  CNF.rup_sound cl_26032 [cl_3368,cl_26017] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3368 v h) (hints_cons _ _ _ (der_26017 v h) (by intro d hd; cases hd)))
def cl_26033 : CNF.NClause := [(114,true),(48,true),(36,false),(35,true),(42,false),(54,false)]
theorem der_26033 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26033 :=
  CNF.rup_sound cl_26033 [cl_3370,cl_26018] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3370 v h) (hints_cons _ _ _ (der_26018 v h) (by intro d hd; cases hd)))
def cl_26034 : CNF.NClause := [(114,true),(54,false),(36,true),(35,true),(42,false),(57,true)]
theorem der_26034 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26034 :=
  CNF.rup_sound cl_26034 [cl_3372,cl_26030] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3372 v h) (hints_cons _ _ _ (der_26030 v h) (by intro d hd; cases hd)))
def cl_26035 : CNF.NClause := [(114,true),(35,true),(36,false),(42,true),(54,false),(57,true)]
theorem der_26035 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26035 :=
  CNF.rup_sound cl_26035 [cl_3374,cl_26031] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3374 v h) (hints_cons _ _ _ (der_26031 v h) (by intro d hd; cases hd)))
def cl_26036 : CNF.NClause := [(114,true),(48,false),(36,false),(35,true),(42,false),(54,true)]
theorem der_26036 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26036 :=
  CNF.rup_sound cl_26036 [cl_3378,cl_26022] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3378 v h) (hints_cons _ _ _ (der_26022 v h) (by intro d hd; cases hd)))
def cl_26037 : CNF.NClause := [(114,true),(48,false),(35,true),(42,false),(54,true),(57,true)]
theorem der_26037 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26037 :=
  CNF.rup_sound cl_26037 [cl_3380,cl_26036] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3380 v h) (hints_cons _ _ _ (der_26036 v h) (by intro d hd; cases hd)))
def cl_26038 : CNF.NClause := [(114,true),(35,true),(36,false),(42,true),(48,false),(57,true)]
theorem der_26038 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26038 :=
  CNF.rup_sound cl_26038 [cl_3382,cl_26031] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3382 v h) (hints_cons _ _ _ (der_26031 v h) (by intro d hd; cases hd)))
def cl_26039 : CNF.NClause := [(114,true),(36,false),(42,false),(48,true),(54,true),(57,true)]
theorem der_26039 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26039 :=
  CNF.rup_sound cl_26039 [cl_3386,cl_25591] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3386 v h) (hints_cons _ _ _ (der_25591 v h) (by intro d hd; cases hd)))
def cl_26040 : CNF.NClause := [(118,true),(33,false),(32,false),(31,true),(34,false),(61,true)]
theorem der_26040 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26040 :=
  CNF.rup_sound cl_26040 [cl_3634,cl_3618] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3634 v h) (hints_cons _ _ _ (inp_3618 v h) (by intro d hd; cases hd)))
def cl_26041 : CNF.NClause := [(118,true),(33,false),(31,true),(34,false),(35,true),(61,true)]
theorem der_26041 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26041 :=
  CNF.rup_sound cl_26041 [cl_3636,cl_26040] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3636 v h) (hints_cons _ _ _ (der_26040 v h) (by intro d hd; cases hd)))
def cl_26042 : CNF.NClause := [(93,true),(56,true),(58,false),(59,false),(60,false),(61,false)]
theorem der_26042 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26042 :=
  CNF.rup_sound cl_26042 [cl_1988,cl_25266] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1988 v h) (hints_cons _ _ _ (der_25266 v h) (by intro d hd; cases hd)))
def cl_26043 : CNF.NClause := [(93,true),(56,true),(58,true),(59,false),(60,false),(61,false)]
theorem der_26043 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26043 :=
  CNF.rup_sound cl_26043 [cl_1992,cl_1990] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1992 v h) (hints_cons _ _ _ (inp_1990 v h) (by intro d hd; cases hd)))
def cl_26044 : CNF.NClause := [(93,true),(57,true),(56,true),(58,false),(60,false),(61,false)]
theorem der_26044 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26044 :=
  CNF.rup_sound cl_26044 [cl_1996,cl_26042] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1996 v h) (hints_cons _ _ _ (der_26042 v h) (by intro d hd; cases hd)))
def cl_26045 : CNF.NClause := [(93,true),(56,true),(58,true),(59,true),(60,false),(61,false)]
theorem der_26045 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26045 :=
  CNF.rup_sound cl_26045 [cl_2000,cl_25039] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2000 v h) (hints_cons _ _ _ (der_25039 v h) (by intro d hd; cases hd)))
def cl_26046 : CNF.NClause := [(93,true),(56,true),(58,false),(59,false),(60,true),(61,false)]
theorem der_26046 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26046 :=
  CNF.rup_sound cl_26046 [cl_2004,cl_2002] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2004 v h) (hints_cons _ _ _ (inp_2002 v h) (by intro d hd; cases hd)))
def cl_26049 : CNF.NClause := [(93,true),(56,true),(58,false),(59,false),(60,false),(61,true)]
theorem der_26049 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26049 :=
  CNF.rup_sound cl_26049 [cl_2020,cl_23838] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2020 v h) (hints_cons _ _ _ (der_23838 v h) (by intro d hd; cases hd)))
def cl_26050 : CNF.NClause := [(93,true),(57,true),(58,true),(59,false),(60,false),(61,true)]
theorem der_26050 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26050 :=
  CNF.rup_sound cl_26050 [cl_2024,cl_25549] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2024 v h) (hints_cons _ _ _ (der_25549 v h) (by intro d hd; cases hd)))
def cl_26051 : CNF.NClause := [(93,true),(57,true),(56,true),(58,false),(59,true),(60,false)]
theorem der_26051 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26051 :=
  CNF.rup_sound cl_26051 [cl_2028,cl_26044] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2028 v h) (hints_cons _ _ _ (der_26044 v h) (by intro d hd; cases hd)))
def cl_26052 : CNF.NClause := [(93,true),(56,true),(58,false),(59,false),(60,true),(61,true)]
theorem der_26052 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26052 :=
  CNF.rup_sound cl_26052 [cl_2036,cl_23791] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2036 v h) (hints_cons _ _ _ (der_23791 v h) (by intro d hd; cases hd)))
def cl_26053 : CNF.NClause := [(114,true),(35,false),(36,false),(48,false),(54,false),(42,false)]
theorem der_26053 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26053 :=
  CNF.rup_sound cl_26053 [cl_3361,cl_23840] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3361 v h) (hints_cons _ _ _ (der_23840 v h) (by intro d hd; cases hd)))
def cl_26054 : CNF.NClause := [(110,true),(33,false),(45,false),(46,false),(52,false),(39,false)]
theorem der_26054 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26054 :=
  CNF.rup_sound cl_26054 [cl_3105,cl_25803] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3105 v h) (hints_cons _ _ _ (der_25803 v h) (by intro d hd; cases hd)))
def cl_26055 : CNF.NClause := [(106,true),(40,false),(41,false),(47,false),(34,false),(53,false)]
theorem der_26055 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26055 :=
  CNF.rup_sound cl_26055 [cl_2849,cl_2817] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2849 v h) (hints_cons _ _ _ (inp_2817 v h) (by intro d hd; cases hd)))
def cl_26056 : CNF.NClause := [(106,true),(57,true),(40,true),(41,false),(47,false),(53,false)]
theorem der_26056 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26056 :=
  CNF.rup_sound cl_26056 [cl_2851,cl_25438] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2851 v h) (hints_cons _ _ _ (der_25438 v h) (by intro d hd; cases hd)))
def cl_26057 : CNF.NClause := [(106,true),(57,true),(40,true),(41,false),(47,true),(34,false)]
theorem der_26057 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26057 :=
  CNF.rup_sound cl_26057 [cl_2859,cl_23749] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2859 v h) (hints_cons _ _ _ (der_23749 v h) (by intro d hd; cases hd)))
def cl_26058 : CNF.NClause := [(122,true),(37,false),(43,true),(49,false),(55,false),(31,true)]
theorem der_26058 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26058 :=
  CNF.rup_sound cl_26058 [cl_3878,cl_25630] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3878 v h) (hints_cons _ _ _ (der_25630 v h) (by intro d hd; cases hd)))
def cl_26059 : CNF.NClause := [(122,true),(37,false),(31,true),(49,false),(55,false),(43,false)]
theorem der_26059 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26059 :=
  CNF.rup_sound cl_26059 [cl_3874,cl_25832] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3874 v h) (hints_cons _ _ _ (der_25832 v h) (by intro d hd; cases hd)))
def cl_26060 : CNF.NClause := [(110,true),(57,true),(33,false),(45,false),(39,false),(52,false)]
theorem der_26060 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26060 :=
  CNF.rup_sound cl_26060 [cl_3113,cl_26054] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3113 v h) (hints_cons _ _ _ (der_26054 v h) (by intro d hd; cases hd)))
def cl_26061 : CNF.NClause := [(110,true),(33,false),(45,false),(39,false),(52,true),(46,true)]
theorem der_26061 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26061 :=
  CNF.rup_sound cl_26061 [cl_3129,cl_25317] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3129 v h) (hints_cons _ _ _ (der_25317 v h) (by intro d hd; cases hd)))
def cl_26062 : CNF.NClause := [(122,true),(57,true),(37,false),(43,true),(31,true),(55,false)]
theorem der_26062 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26062 :=
  CNF.rup_sound cl_26062 [cl_3886,cl_26058] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3886 v h) (hints_cons _ _ _ (der_26058 v h) (by intro d hd; cases hd)))
def cl_26063 : CNF.NClause := [(110,true),(33,false),(45,false),(46,false),(39,false),(52,true)]
theorem der_26063 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26063 :=
  CNF.rup_sound cl_26063 [cl_3121,cl_3089] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3121 v h) (hints_cons _ _ _ (inp_3089 v h) (by intro d hd; cases hd)))
def cl_26064 : CNF.NClause := [(110,true),(33,false),(39,false),(46,true),(45,true),(52,true)]
theorem der_26064 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26064 :=
  CNF.rup_sound cl_26064 [cl_3133,cl_3101] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3133 v h) (hints_cons _ _ _ (inp_3101 v h) (by intro d hd; cases hd)))
def cl_26065 : CNF.NClause := [(106,true),(57,true),(40,false),(41,false),(34,false),(53,false)]
theorem der_26065 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26065 :=
  CNF.rup_sound cl_26065 [cl_2857,cl_26055] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2857 v h) (hints_cons _ _ _ (der_26055 v h) (by intro d hd; cases hd)))
def cl_26066 : CNF.NClause := [(122,true),(57,true),(37,false),(31,true),(49,true),(43,false)]
theorem der_26066 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26066 :=
  CNF.rup_sound cl_26066 [cl_3882,cl_23781] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3882 v h) (hints_cons _ _ _ (der_23781 v h) (by intro d hd; cases hd)))
def cl_26067 : CNF.NClause := [(114,true),(35,false),(36,false),(42,false),(54,false),(48,true)]
theorem der_26067 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26067 :=
  CNF.rup_sound cl_26067 [cl_3369,cl_3337] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3369 v h) (hints_cons _ _ _ (inp_3337 v h) (by intro d hd; cases hd)))
def cl_26068 : CNF.NClause := [(110,true),(33,false),(39,false),(46,false),(52,true),(45,true)]
theorem der_26068 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26068 :=
  CNF.rup_sound cl_26068 [cl_3125,cl_23799] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3125 v h) (hints_cons _ _ _ (der_23799 v h) (by intro d hd; cases hd)))
def cl_26069 : CNF.NClause := [(98,true),(52,false),(53,false),(54,false),(55,false),(61,false)]
theorem der_26069 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26069 :=
  CNF.rup_sound cl_26069 [cl_2306,cl_25267] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2306 v h) (hints_cons _ _ _ (der_25267 v h) (by intro d hd; cases hd)))
def cl_26070 : CNF.NClause := [(98,true),(51,true),(53,false),(54,false),(55,false),(61,false)]
theorem der_26070 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26070 :=
  CNF.rup_sound cl_26070 [cl_2308,cl_26069] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2308 v h) (hints_cons _ _ _ (der_26069 v h) (by intro d hd; cases hd)))
def cl_26071 : CNF.NClause := [(98,true),(52,false),(53,true),(54,false),(55,false),(61,false)]
theorem der_26071 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26071 :=
  CNF.rup_sound cl_26071 [cl_2310,cl_2309] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2310 v h) (hints_cons _ _ _ (inp_2309 v h) (by intro d hd; cases hd)))
def cl_26072 : CNF.NClause := [(98,true),(51,true),(52,true),(54,false),(55,false),(61,false)]
theorem der_26072 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26072 :=
  CNF.rup_sound cl_26072 [cl_2312,cl_26070] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2312 v h) (hints_cons _ _ _ (der_26070 v h) (by intro d hd; cases hd)))
def cl_26073 : CNF.NClause := [(98,true),(52,false),(53,false),(54,true),(55,false),(61,false)]
theorem der_26073 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26073 :=
  CNF.rup_sound cl_26073 [cl_2314,cl_25057] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2314 v h) (hints_cons _ _ _ (der_25057 v h) (by intro d hd; cases hd)))
def cl_26074 : CNF.NClause := [(98,true),(51,true),(52,true),(53,false),(55,false),(61,false)]
theorem der_26074 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26074 :=
  CNF.rup_sound cl_26074 [cl_2316,cl_26070] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2316 v h) (hints_cons _ _ _ (der_26070 v h) (by intro d hd; cases hd)))
def cl_26075 : CNF.NClause := [(98,true),(52,false),(53,true),(54,true),(55,false),(61,false)]
theorem der_26075 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26075 :=
  CNF.rup_sound cl_26075 [cl_2318,cl_23757] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2318 v h) (hints_cons _ _ _ (der_23757 v h) (by intro d hd; cases hd)))
def cl_26077 : CNF.NClause := [(98,true),(52,false),(53,false),(54,false),(55,true),(61,false)]
theorem der_26077 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26077 :=
  CNF.rup_sound cl_26077 [cl_2322,cl_25278] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2322 v h) (hints_cons _ _ _ (der_25278 v h) (by intro d hd; cases hd)))
def cl_26078 : CNF.NClause := [(98,true),(51,true),(52,true),(53,false),(54,false),(61,false)]
theorem der_26078 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26078 :=
  CNF.rup_sound cl_26078 [cl_2324,cl_26070] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2324 v h) (hints_cons _ _ _ (der_26070 v h) (by intro d hd; cases hd)))
def cl_26079 : CNF.NClause := [(98,true),(51,true),(52,false),(53,true),(54,false),(61,false)]
theorem der_26079 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26079 :=
  CNF.rup_sound cl_26079 [cl_2326,cl_26071] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2326 v h) (hints_cons _ _ _ (der_26071 v h) (by intro d hd; cases hd)))
def cl_26080 : CNF.NClause := [(98,true),(51,true),(52,true),(53,true),(54,false),(61,false)]
theorem der_26080 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26080 :=
  CNF.rup_sound cl_26080 [cl_2328,cl_26072] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2328 v h) (hints_cons _ _ _ (der_26072 v h) (by intro d hd; cases hd)))
def cl_26081 : CNF.NClause := [(98,true),(52,false),(53,false),(54,true),(55,true),(61,false)]
theorem der_26081 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26081 :=
  CNF.rup_sound cl_26081 [cl_2330,cl_25058] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2330 v h) (hints_cons _ _ _ (der_25058 v h) (by intro d hd; cases hd)))
def cl_26082 : CNF.NClause := [(98,true),(51,true),(52,true),(53,false),(54,true),(61,false)]
theorem der_26082 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26082 :=
  CNF.rup_sound cl_26082 [cl_2332,cl_26074] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2332 v h) (hints_cons _ _ _ (der_26074 v h) (by intro d hd; cases hd)))
def cl_26084 : CNF.NClause := [(98,true),(55,false),(52,false),(53,false),(54,false),(61,true)]
theorem der_26084 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26084 :=
  CNF.rup_sound cl_26084 [cl_2338,cl_25806] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2338 v h) (hints_cons _ _ _ (der_25806 v h) (by intro d hd; cases hd)))
def cl_26085 : CNF.NClause := [(98,true),(55,false),(52,true),(53,false),(54,false),(51,true)]
theorem der_26085 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26085 :=
  CNF.rup_sound cl_26085 [cl_2340,cl_26070] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2340 v h) (hints_cons _ _ _ (der_26070 v h) (by intro d hd; cases hd)))
def cl_26086 : CNF.NClause := [(98,true),(55,false),(52,false),(53,true),(54,false),(61,true)]
theorem der_26086 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26086 :=
  CNF.rup_sound cl_26086 [cl_2342,cl_23732] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2342 v h) (hints_cons _ _ _ (der_23732 v h) (by intro d hd; cases hd)))
def cl_26087 : CNF.NClause := [(98,true),(54,false),(52,true),(53,true),(51,true),(55,false)]
theorem der_26087 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26087 :=
  CNF.rup_sound cl_26087 [cl_2344,cl_26072] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2344 v h) (hints_cons _ _ _ (der_26072 v h) (by intro d hd; cases hd)))
def cl_26088 : CNF.NClause := [(98,true),(55,false),(52,false),(53,false),(54,true),(61,true)]
theorem der_26088 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26088 :=
  CNF.rup_sound cl_26088 [cl_2346,cl_25053] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2346 v h) (hints_cons _ _ _ (der_25053 v h) (by intro d hd; cases hd)))
def cl_26089 : CNF.NClause := [(98,true),(55,false),(52,true),(53,false),(54,true),(61,true)]
theorem der_26089 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26089 :=
  CNF.rup_sound cl_26089 [cl_2348,cl_23845] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2348 v h) (hints_cons _ _ _ (der_23845 v h) (by intro d hd; cases hd)))
def cl_26090 : CNF.NClause := [(98,true),(55,false),(52,false),(53,true),(54,true),(51,true)]
theorem der_26090 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26090 :=
  CNF.rup_sound cl_26090 [cl_2350,cl_26075] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2350 v h) (hints_cons _ _ _ (der_26075 v h) (by intro d hd; cases hd)))
def cl_26091 : CNF.NClause := [(98,true),(52,false),(53,false),(51,true),(54,false),(55,true)]
theorem der_26091 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26091 :=
  CNF.rup_sound cl_26091 [cl_2354,cl_26077] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2354 v h) (hints_cons _ _ _ (der_26077 v h) (by intro d hd; cases hd)))
def cl_26092 : CNF.NClause := [(98,true),(53,false),(52,true),(51,true),(54,false),(61,true)]
theorem der_26092 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26092 :=
  CNF.rup_sound cl_26092 [cl_2356,cl_26085] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2356 v h) (hints_cons _ _ _ (der_26085 v h) (by intro d hd; cases hd)))
def cl_26093 : CNF.NClause := [(98,true),(54,false),(52,false),(53,true),(51,true),(55,true)]
theorem der_26093 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26093 :=
  CNF.rup_sound cl_26093 [cl_2358,cl_26079] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2358 v h) (hints_cons _ _ _ (der_26079 v h) (by intro d hd; cases hd)))
def cl_26094 : CNF.NClause := [(98,true),(52,false),(53,false),(54,true),(55,true),(61,true)]
theorem der_26094 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26094 :=
  CNF.rup_sound cl_26094 [cl_2362,cl_25054] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2362 v h) (hints_cons _ _ _ (der_25054 v h) (by intro d hd; cases hd)))
def cl_26095 : CNF.NClause := [(123,true),(56,false),(36,false),(41,false),(46,false),(31,true)]
theorem der_26095 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26095 :=
  CNF.rup_sound cl_26095 [cl_3922,cl_25561] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3922 v h) (hints_cons _ _ _ (der_25561 v h) (by intro d hd; cases hd)))
def cl_26097 : CNF.NClause := [(123,true),(56,false),(41,true),(46,false),(31,true),(51,true)]
theorem der_26097 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26097 :=
  CNF.rup_sound cl_26097 [cl_3928,cl_25872] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3928 v h) (hints_cons _ _ _ (der_25872 v h) (by intro d hd; cases hd)))
def cl_26098 : CNF.NClause := [(101,true),(48,false),(34,false),(45,false),(37,false),(59,true)]
theorem der_26098 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26098 :=
  CNF.rup_sound cl_26098 [cl_2545,cl_25779] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2545 v h) (hints_cons _ _ _ (der_25779 v h) (by intro d hd; cases hd)))
def cl_26099 : CNF.NClause := [(101,true),(34,false),(37,false),(45,false),(48,false),(59,false)]
theorem der_26099 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26099 :=
  CNF.rup_sound cl_26099 [cl_2513,cl_23848] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2513 v h) (hints_cons _ _ _ (der_23848 v h) (by intro d hd; cases hd)))
def cl_26100 : CNF.NClause := [(101,true),(34,false),(37,false),(45,true),(48,false),(59,false)]
theorem der_26100 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26100 :=
  CNF.rup_sound cl_26100 [cl_2517,cl_23847] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2517 v h) (hints_cons _ _ _ (der_23847 v h) (by intro d hd; cases hd)))
def cl_26101 : CNF.NClause := [(101,true),(34,false),(37,false),(45,true),(48,true),(59,false)]
theorem der_26101 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26101 :=
  CNF.rup_sound cl_26101 [cl_2525,cl_2509] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2525 v h) (hints_cons _ _ _ (inp_2509 v h) (by intro d hd; cases hd)))
def cl_26102 : CNF.NClause := [(100,true),(33,false),(51,true),(58,false),(49,false),(40,false)]
theorem der_26102 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26102 :=
  CNF.rup_sound cl_26102 [cl_2449,cl_25321] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2449 v h) (hints_cons _ _ _ (der_25321 v h) (by intro d hd; cases hd)))
def cl_26103 : CNF.NClause := [(100,true),(33,false),(49,false),(42,false),(40,false),(58,true)]
theorem der_26103 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26103 :=
  CNF.rup_sound cl_26103 [cl_2481,cl_25042] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2481 v h) (hints_cons _ _ _ (der_25042 v h) (by intro d hd; cases hd)))
def cl_26104 : CNF.NClause := [(123,true),(41,false),(36,true),(31,true),(46,false),(56,true)]
theorem der_26104 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26104 :=
  CNF.rup_sound cl_26104 [cl_3956,cl_24910] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3956 v h) (hints_cons _ _ _ (der_24910 v h) (by intro d hd; cases hd)))
def cl_26105 : CNF.NClause := [(123,true),(41,false),(31,true),(36,false),(46,false),(56,true)]
theorem der_26105 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26105 :=
  CNF.rup_sound cl_26105 [cl_3954,cl_23818] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3954 v h) (hints_cons _ _ _ (der_23818 v h) (by intro d hd; cases hd)))
def cl_26106 : CNF.NClause := [(99,true),(47,false),(39,false),(35,false),(43,false),(60,false)]
theorem der_26106 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26106 :=
  CNF.rup_sound cl_26106 [cl_2385,cl_2369] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2385 v h) (hints_cons _ _ _ (inp_2369 v h) (by intro d hd; cases hd)))
def cl_26107 : CNF.NClause := [(99,true),(47,false),(51,true),(39,false),(35,false),(60,true)]
theorem der_26107 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26107 :=
  CNF.rup_sound cl_26107 [cl_2417,cl_25628] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2417 v h) (hints_cons _ _ _ (der_25628 v h) (by intro d hd; cases hd)))
def cl_26108 : CNF.NClause := [(100,true),(40,true),(42,false),(49,false),(51,true),(58,false)]
theorem der_26108 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26108 :=
  CNF.rup_sound cl_26108 [cl_2451,cl_25685] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2451 v h) (hints_cons _ _ _ (der_25685 v h) (by intro d hd; cases hd)))
def cl_26109 : CNF.NClause := [(100,true),(33,false),(40,true),(42,false),(49,false),(58,true)]
theorem der_26109 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26109 :=
  CNF.rup_sound cl_26109 [cl_2483,cl_25043] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2483 v h) (hints_cons _ _ _ (der_25043 v h) (by intro d hd; cases hd)))
def cl_26110 : CNF.NClause := [(123,true),(56,false),(36,false),(41,false),(31,true),(51,true)]
theorem der_26110 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26110 :=
  CNF.rup_sound cl_26110 [cl_3930,cl_26095] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3930 v h) (hints_cons _ _ _ (der_26095 v h) (by intro d hd; cases hd)))
def cl_26112 : CNF.NClause := [(123,true),(41,false),(31,true),(36,false),(46,true),(56,true)]
theorem der_26112 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26112 :=
  CNF.rup_sound cl_26112 [cl_3962,cl_3946] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3962 v h) (hints_cons _ _ _ (inp_3946 v h) (by intro d hd; cases hd)))
def cl_26113 : CNF.NClause := [(99,true),(35,false),(39,false),(43,false),(47,true),(60,false)]
theorem der_26113 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26113 :=
  CNF.rup_sound cl_26113 [cl_2393,cl_23841] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2393 v h) (hints_cons _ _ _ (der_23841 v h) (by intro d hd; cases hd)))
def cl_26114 : CNF.NClause := [(99,true),(35,false),(39,false),(43,false),(47,true),(60,true)]
theorem der_26114 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26114 :=
  CNF.rup_sound cl_26114 [cl_2425,cl_2409] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2425 v h) (hints_cons _ _ _ (inp_2409 v h) (by intro d hd; cases hd)))
def cl_26115 : CNF.NClause := [(100,true),(33,false),(58,false),(42,false),(49,true),(40,false)]
theorem der_26115 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26115 :=
  CNF.rup_sound cl_26115 [cl_2457,cl_2441] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2457 v h) (hints_cons _ _ _ (inp_2441 v h) (by intro d hd; cases hd)))
def cl_26116 : CNF.NClause := [(100,true),(49,true),(33,false),(40,false),(42,false),(58,true)]
theorem der_26116 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26116 :=
  CNF.rup_sound cl_26116 [cl_2489,cl_23808] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2489 v h) (hints_cons _ _ _ (der_23808 v h) (by intro d hd; cases hd)))
def cl_26117 : CNF.NClause := [(100,true),(33,false),(40,true),(42,false),(49,true),(58,false)]
theorem der_26117 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26117 :=
  CNF.rup_sound cl_26117 [cl_2459,cl_23814] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2459 v h) (hints_cons _ _ _ (der_23814 v h) (by intro d hd; cases hd)))
def cl_26118 : CNF.NClause := [(100,true),(33,false),(40,true),(42,false),(51,true),(58,true)]
theorem der_26118 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26118 :=
  CNF.rup_sound cl_26118 [cl_2491,cl_26109] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2491 v h) (hints_cons _ _ _ (der_26109 v h) (by intro d hd; cases hd)))
def cl_26119 : CNF.NClause := [(101,true),(34,false),(51,true),(45,false),(37,false),(59,true)]
theorem der_26119 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26119 :=
  CNF.rup_sound cl_26119 [cl_2553,cl_26098] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2553 v h) (hints_cons _ _ _ (der_26098 v h) (by intro d hd; cases hd)))
def cl_26120 : CNF.NClause := [(101,true),(59,false),(51,true),(45,false),(34,false),(48,true)]
theorem der_26120 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26120 :=
  CNF.rup_sound cl_26120 [cl_2521,cl_25409] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2521 v h) (hints_cons _ _ _ (der_25409 v h) (by intro d hd; cases hd)))
def cl_26121 : CNF.NClause := [(101,true),(34,false),(37,false),(45,true),(48,true),(59,true)]
theorem der_26121 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26121 :=
  CNF.rup_sound cl_26121 [cl_2557,cl_25792] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2557 v h) (hints_cons _ _ _ (der_25792 v h) (by intro d hd; cases hd)))
def cl_26122 : CNF.NClause := [(101,true),(51,true),(37,false),(45,true),(48,false),(59,true)]
theorem der_26122 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26122 :=
  CNF.rup_sound cl_26122 [cl_2549,cl_25420] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2549 v h) (hints_cons _ _ _ (der_25420 v h) (by intro d hd; cases hd)))
def cl_26123 : CNF.NClause := [(102,true),(57,false),(44,false),(32,false),(51,true),(38,false)]
theorem der_26123 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26123 :=
  CNF.rup_sound cl_26123 [cl_2585,cl_2577] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2585 v h) (hints_cons _ _ _ (inp_2577 v h) (by intro d hd; cases hd)))
def cl_26124 : CNF.NClause := [(102,true),(51,false),(44,false),(32,false),(38,false),(57,true)]
theorem der_26124 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26124 :=
  CNF.rup_sound cl_26124 [cl_2601,cl_2593] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2601 v h) (hints_cons _ _ _ (inp_2593 v h) (by intro d hd; cases hd)))
def cl_26125 : CNF.NClause := [(102,true),(38,false),(50,true),(44,false),(32,false),(51,true)]
theorem der_26125 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26125 :=
  CNF.rup_sound cl_26125 [cl_2617,cl_26123] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2617 v h) (hints_cons _ _ _ (der_26123 v h) (by intro d hd; cases hd)))
def cl_26126 : CNF.NClause := [(108,true),(61,false),(47,false),(48,false),(49,false),(46,false)]
theorem der_26126 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26126 :=
  CNF.rup_sound cl_26126 [cl_2961,cl_25274] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2961 v h) (hints_cons _ _ _ (der_25274 v h) (by intro d hd; cases hd)))
def cl_26128 : CNF.NClause := [(94,true),(40,false),(50,true),(35,false),(55,false),(56,true)]
theorem der_26128 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26128 :=
  CNF.rup_sound cl_26128 [cl_2089,cl_2093] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2089 v h) (hints_cons _ _ _ (inp_2093 v h) (by intro d hd; cases hd)))
def cl_26129 : CNF.NClause := [(94,true),(45,false),(40,false),(55,true),(35,false),(56,true)]
theorem der_26129 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26129 :=
  CNF.rup_sound cl_26129 [cl_2105,cl_25291] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2105 v h) (hints_cons _ _ _ (der_25291 v h) (by intro d hd; cases hd)))
def cl_26130 : CNF.NClause := [(105,true),(33,false),(41,false),(37,false),(54,false),(60,false)]
theorem der_26130 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26130 :=
  CNF.rup_sound cl_26130 [cl_2761,cl_23850] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2761 v h) (hints_cons _ _ _ (der_23850 v h) (by intro d hd; cases hd)))
def cl_26131 : CNF.NClause := [(105,true),(54,true),(41,false),(37,false),(50,true),(60,false)]
theorem der_26131 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26131 :=
  CNF.rup_sound cl_26131 [cl_2777,cl_25723] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2777 v h) (hints_cons _ _ _ (der_25723 v h) (by intro d hd; cases hd)))
def cl_26132 : CNF.NClause := [(105,true),(54,true),(33,false),(41,false),(37,false),(60,true)]
theorem der_26132 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26132 :=
  CNF.rup_sound cl_26132 [cl_2809,cl_25060] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2809 v h) (hints_cons _ _ _ (der_25060 v h) (by intro d hd; cases hd)))
def cl_26133 : CNF.NClause := [(94,true),(56,false),(40,true),(45,false),(35,false),(55,true)]
theorem der_26133 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26133 :=
  CNF.rup_sound cl_26133 [cl_2075,cl_25292] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2075 v h) (hints_cons _ _ _ (der_25292 v h) (by intro d hd; cases hd)))
def cl_26134 : CNF.NClause := [(94,true),(55,false),(40,true),(45,false),(35,false),(56,true)]
theorem der_26134 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26134 :=
  CNF.rup_sound cl_26134 [cl_2091,cl_23851] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2091 v h) (hints_cons _ _ _ (der_23851 v h) (by intro d hd; cases hd)))
def cl_26135 : CNF.NClause := [(94,true),(45,false),(40,true),(55,true),(35,false),(56,true)]
theorem der_26135 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26135 :=
  CNF.rup_sound cl_26135 [cl_2107,cl_25293] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2107 v h) (hints_cons _ _ _ (der_25293 v h) (by intro d hd; cases hd)))
def cl_26136 : CNF.NClause := [(94,true),(35,false),(40,false),(55,true),(45,true),(56,true)]
theorem der_26136 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26136 :=
  CNF.rup_sound cl_26136 [cl_2109,cl_23857] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2109 v h) (hints_cons _ _ _ (der_23857 v h) (by intro d hd; cases hd)))
def cl_26137 : CNF.NClause := [(94,true),(55,false),(40,true),(45,true),(35,false),(56,true)]
theorem der_26137 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26137 :=
  CNF.rup_sound cl_26137 [cl_2095,cl_2087] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2095 v h) (hints_cons _ _ _ (inp_2087 v h) (by intro d hd; cases hd)))
def cl_26138 : CNF.NClause := [(108,true),(49,true),(47,false),(50,true),(46,false),(61,true)]
theorem der_26138 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26138 :=
  CNF.rup_sound cl_26138 [cl_3001,cl_25597] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3001 v h) (hints_cons _ _ _ (der_25597 v h) (by intro d hd; cases hd)))
def cl_26139 : CNF.NClause := [(108,true),(48,false),(47,false),(49,false),(50,true),(46,false)]
theorem der_26139 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26139 :=
  CNF.rup_sound cl_26139 [cl_2993,cl_26126] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2993 v h) (hints_cons _ _ _ (der_26126 v h) (by intro d hd; cases hd)))
def cl_26140 : CNF.NClause := [(116,true),(36,false),(34,false),(43,false),(52,true),(58,false)]
theorem der_26140 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26140 :=
  CNF.rup_sound cl_26140 [cl_3481,cl_3473] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3481 v h) (hints_cons _ _ _ (inp_3473 v h) (by intro d hd; cases hd)))
def cl_26141 : CNF.NClause := [(116,true),(36,false),(34,false),(43,false),(52,true),(58,true)]
theorem der_26141 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26141 :=
  CNF.rup_sound cl_26141 [cl_3513,cl_23800] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3513 v h) (hints_cons _ _ _ (der_23800 v h) (by intro d hd; cases hd)))
def cl_26142 : CNF.NClause := [(108,true),(49,true),(46,false),(48,false),(50,true),(61,true)]
theorem der_26142 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26142 :=
  CNF.rup_sound cl_26142 [cl_3003,cl_26138] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3003 v h) (hints_cons _ _ _ (der_26138 v h) (by intro d hd; cases hd)))
def cl_26143 : CNF.NClause := [(121,true),(59,false),(42,false),(31,true),(53,false),(39,false)]
theorem der_26143 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26143 :=
  CNF.rup_sound cl_26143 [cl_3786,cl_23792] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3786 v h) (hints_cons _ _ _ (der_23792 v h) (by intro d hd; cases hd)))
def cl_26144 : CNF.NClause := [(121,true),(59,false),(50,true),(31,true),(53,false),(39,true)]
theorem der_26144 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26144 :=
  CNF.rup_sound cl_26144 [cl_3788,cl_3792] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3788 v h) (hints_cons _ _ _ (inp_3792 v h) (by intro d hd; cases hd)))
def cl_26145 : CNF.NClause := [(108,true),(48,false),(50,true),(49,false),(46,false),(61,true)]
theorem der_26145 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26145 :=
  CNF.rup_sound cl_26145 [cl_2995,cl_26139] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2995 v h) (hints_cons _ _ _ (der_26139 v h) (by intro d hd; cases hd)))
def cl_26146 : CNF.NClause := [(108,true),(47,true),(46,false),(48,true),(49,false),(50,true)]
theorem der_26146 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26146 :=
  CNF.rup_sound cl_26146 [cl_2999,cl_23695] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2999 v h) (hints_cons _ _ _ (der_23695 v h) (by intro d hd; cases hd)))
def cl_26147 : CNF.NClause := [(108,true),(47,false),(46,false),(48,true),(50,true),(61,true)]
theorem der_26147 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26147 :=
  CNF.rup_sound cl_26147 [cl_2997,cl_25597] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2997 v h) (hints_cons _ _ _ (der_25597 v h) (by intro d hd; cases hd)))
def cl_26148 : CNF.NClause := [(105,true),(41,false),(33,false),(37,false),(54,false),(60,true)]
theorem der_26148 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26148 :=
  CNF.rup_sound cl_26148 [cl_2793,cl_2785] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2793 v h) (hints_cons _ _ _ (inp_2785 v h) (by intro d hd; cases hd)))
def cl_26149 : CNF.NClause := [(103,true),(41,false),(44,false),(43,false),(45,false),(42,false)]
theorem der_26149 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26149 :=
  CNF.rup_sound cl_26149 [cl_2657,cl_25268] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2657 v h) (hints_cons _ _ _ (der_25268 v h) (by intro d hd; cases hd)))
def cl_26150 : CNF.NClause := [(96,true),(34,false),(49,false),(56,true),(44,false),(54,false)]
theorem der_26150 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26150 :=
  CNF.rup_sound cl_26150 [cl_2209,cl_24752] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2209 v h) (hints_cons _ _ _ (der_24752 v h) (by intro d hd; cases hd)))
def cl_26151 : CNF.NClause := [(109,true),(58,false),(46,false),(44,false),(35,false),(37,false)]
theorem der_26151 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26151 :=
  CNF.rup_sound cl_26151 [cl_3009,cl_3025] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3009 v h) (hints_cons _ _ _ (inp_3025 v h) (by intro d hd; cases hd)))
def cl_26152 : CNF.NClause := [(115,true),(55,false),(36,false),(33,false),(47,false),(59,false)]
theorem der_26152 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26152 :=
  CNF.rup_sound cl_26152 [cl_3393,cl_23865] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3393 v h) (hints_cons _ _ _ (der_23865 v h) (by intro d hd; cases hd)))
def cl_26153 : CNF.NClause := [(119,true),(52,false),(48,false),(31,true),(40,true),(44,false)]
theorem der_26153 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26153 :=
  CNF.rup_sound cl_26153 [cl_3652,cl_3684] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3652 v h) (hints_cons _ _ _ (inp_3684 v h) (by intro d hd; cases hd)))
def cl_26154 : CNF.NClause := [(103,true),(41,false),(42,false),(43,false),(45,true),(61,true)]
theorem der_26154 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26154 :=
  CNF.rup_sound cl_26154 [cl_2673,cl_2681] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2673 v h) (hints_cons _ _ _ (inp_2681 v h) (by intro d hd; cases hd)))
def cl_26155 : CNF.NClause := [(96,true),(34,false),(44,false),(49,true),(39,false),(56,true)]
theorem der_26155 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26155 :=
  CNF.rup_sound cl_26155 [cl_2217,cl_23809] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2217 v h) (hints_cons _ _ _ (der_23809 v h) (by intro d hd; cases hd)))
def cl_26156 : CNF.NClause := [(119,true),(48,false),(31,true),(40,true),(44,false),(60,true)]
theorem der_26156 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26156 :=
  CNF.rup_sound cl_26156 [cl_3700,cl_3684] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3700 v h) (hints_cons _ _ _ (inp_3684 v h) (by intro d hd; cases hd)))
def cl_26157 : CNF.NClause := [(109,true),(46,true),(44,false),(35,false),(37,false),(58,false)]
theorem der_26157 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26157 :=
  CNF.rup_sound cl_26157 [cl_3017,cl_23746] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3017 v h) (hints_cons _ _ _ (der_23746 v h) (by intro d hd; cases hd)))
def cl_26158 : CNF.NClause := [(115,true),(59,false),(33,false),(36,false),(44,false),(47,true)]
theorem der_26158 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26158 :=
  CNF.rup_sound cl_26158 [cl_3401,cl_3417] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3401 v h) (hints_cons _ _ _ (inp_3417 v h) (by intro d hd; cases hd)))
def cl_26159 : CNF.NClause := [(119,true),(60,true),(31,true),(40,true),(52,false),(44,false)]
theorem der_26159 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26159 :=
  CNF.rup_sound cl_26159 [cl_3692,cl_3684] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3692 v h) (hints_cons _ _ _ (inp_3684 v h) (by intro d hd; cases hd)))
def cl_26160 : CNF.NClause := [(119,true),(40,true),(44,false),(48,false),(31,true),(60,false)]
theorem der_26160 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26160 :=
  CNF.rup_sound cl_26160 [cl_3668,cl_26153] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3668 v h) (hints_cons _ _ _ (der_26153 v h) (by intro d hd; cases hd)))
def cl_26161 : CNF.NClause := [(119,true),(40,false),(31,true),(48,false),(52,true),(60,false)]
theorem der_26161 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26161 :=
  CNF.rup_sound cl_26161 [cl_3666,cl_3670] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3666 v h) (hints_cons _ _ _ (inp_3670 v h) (by intro d hd; cases hd)))
def cl_26162 : CNF.NClause := [(119,true),(40,false),(31,true),(48,true),(52,true),(60,false)]
theorem der_26162 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26162 :=
  CNF.rup_sound cl_26162 [cl_3674,cl_23889] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3674 v h) (hints_cons _ _ _ (der_23889 v h) (by intro d hd; cases hd)))
def cl_26163 : CNF.NClause := [(119,true),(48,false),(31,true),(44,false),(52,false),(60,true)]
theorem der_26163 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26163 :=
  CNF.rup_sound cl_26163 [cl_3682,cl_3684] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3682 v h) (hints_cons _ _ _ (inp_3684 v h) (by intro d hd; cases hd)))
def cl_26164 : CNF.NClause := [(119,true),(52,false),(31,true),(44,false),(48,true),(40,false)]
theorem der_26164 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26164 :=
  CNF.rup_sound cl_26164 [cl_3690,cl_25811] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3690 v h) (hints_cons _ _ _ (der_25811 v h) (by intro d hd; cases hd)))
def cl_26165 : CNF.NClause := [(119,true),(48,false),(31,true),(40,false),(52,true),(60,true)]
theorem der_26165 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26165 :=
  CNF.rup_sound cl_26165 [cl_3698,cl_23892] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3698 v h) (hints_cons _ _ _ (der_23892 v h) (by intro d hd; cases hd)))
def cl_26166 : CNF.NClause := [(119,true),(60,true),(31,true),(40,false),(48,true),(44,false)]
theorem der_26166 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26166 :=
  CNF.rup_sound cl_26166 [cl_3706,cl_26164] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3706 v h) (hints_cons _ _ _ (der_26164 v h) (by intro d hd; cases hd)))
def cl_26167 : CNF.NClause := [(119,true),(48,true),(44,false),(40,true),(31,true),(60,false)]
theorem der_26167 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26167 :=
  CNF.rup_sound cl_26167 [cl_3676,cl_25802] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3676 v h) (hints_cons _ _ _ (der_25802 v h) (by intro d hd; cases hd)))
def cl_26168 : CNF.NClause := [(102,true),(51,false),(50,true),(38,false),(32,false),(57,false)]
theorem der_26168 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26168 :=
  CNF.rup_sound cl_26168 [cl_2569,cl_23896] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2569 v h) (hints_cons _ _ _ (der_23896 v h) (by intro d hd; cases hd)))
def cl_26169 : CNF.NClause := [(102,true),(32,false),(38,true),(50,false),(51,false),(57,false)]
theorem der_26169 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26169 :=
  CNF.rup_sound cl_26169 [cl_2563,cl_2567] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2563 v h) (hints_cons _ _ _ (inp_2567 v h) (by intro d hd; cases hd)))
def cl_26170 : CNF.NClause := [(102,true),(32,false),(44,false),(50,true),(51,false),(57,false)]
theorem der_26170 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26170 :=
  CNF.rup_sound cl_26170 [cl_2571,cl_26168] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2571 v h) (hints_cons _ _ _ (der_26168 v h) (by intro d hd; cases hd)))
def cl_26171 : CNF.NClause := [(97,true),(56,false),(37,false),(42,false),(47,false),(52,false)]
theorem der_26171 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26171 :=
  CNF.rup_sound cl_26171 [cl_2242,cl_25571] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2242 v h) (hints_cons _ _ _ (der_25571 v h) (by intro d hd; cases hd)))
def cl_26172 : CNF.NClause := [(97,true),(56,false),(37,true),(47,false),(52,false),(42,false)]
theorem der_26172 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26172 :=
  CNF.rup_sound cl_26172 [cl_2244,cl_2243] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2244 v h) (hints_cons _ _ _ (inp_2243 v h) (by intro d hd; cases hd)))
def cl_26173 : CNF.NClause := [(97,true),(56,false),(37,false),(42,true),(47,false),(52,false)]
theorem der_26173 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26173 :=
  CNF.rup_sound cl_26173 [cl_2246,cl_25327] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2246 v h) (hints_cons _ _ _ (der_25327 v h) (by intro d hd; cases hd)))
def cl_26174 : CNF.NClause := [(97,true),(56,false),(37,true),(42,true),(47,false),(52,false)]
theorem der_26174 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26174 :=
  CNF.rup_sound cl_26174 [cl_2248,cl_24775] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2248 v h) (hints_cons _ _ _ (der_24775 v h) (by intro d hd; cases hd)))
def cl_26175 : CNF.NClause := [(97,true),(56,false),(37,false),(42,false),(47,true),(52,false)]
theorem der_26175 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26175 :=
  CNF.rup_sound cl_26175 [cl_2250,cl_25574] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2250 v h) (hints_cons _ _ _ (der_25574 v h) (by intro d hd; cases hd)))
def cl_26176 : CNF.NClause := [(97,true),(56,false),(37,true),(47,true),(52,false),(42,false)]
theorem der_26176 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26176 :=
  CNF.rup_sound cl_26176 [cl_2252,cl_24776] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2252 v h) (hints_cons _ _ _ (der_24776 v h) (by intro d hd; cases hd)))
def cl_26177 : CNF.NClause := [(97,true),(56,false),(37,false),(42,true),(47,true),(52,false)]
theorem der_26177 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26177 :=
  CNF.rup_sound cl_26177 [cl_2254,cl_25328] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2254 v h) (hints_cons _ _ _ (der_25328 v h) (by intro d hd; cases hd)))
def cl_26179 : CNF.NClause := [(97,true),(56,false),(37,false),(42,false),(47,false),(52,true)]
theorem der_26179 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26179 :=
  CNF.rup_sound cl_26179 [cl_2258,cl_25582] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2258 v h) (hints_cons _ _ _ (der_25582 v h) (by intro d hd; cases hd)))
def cl_26181 : CNF.NClause := [(97,true),(56,false),(37,false),(42,true),(47,false),(52,true)]
theorem der_26181 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26181 :=
  CNF.rup_sound cl_26181 [cl_2262,cl_25329] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2262 v h) (hints_cons _ _ _ (der_25329 v h) (by intro d hd; cases hd)))
def cl_26183 : CNF.NClause := [(97,true),(56,false),(37,false),(42,false),(47,true),(32,true)]
theorem der_26183 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26183 :=
  CNF.rup_sound cl_26183 [cl_2266,cl_26175] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2266 v h) (hints_cons _ _ _ (der_26175 v h) (by intro d hd; cases hd)))
def cl_26186 : CNF.NClause := [(97,true),(42,false),(37,false),(47,false),(52,false),(56,true)]
theorem der_26186 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26186 :=
  CNF.rup_sound cl_26186 [cl_2274,cl_25807] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2274 v h) (hints_cons _ _ _ (der_25807 v h) (by intro d hd; cases hd)))
def cl_26187 : CNF.NClause := [(97,true),(37,true),(42,false),(32,true),(47,false),(52,false)]
theorem der_26187 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26187 :=
  CNF.rup_sound cl_26187 [cl_2276,cl_26172] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2276 v h) (hints_cons _ _ _ (der_26172 v h) (by intro d hd; cases hd)))
def cl_26188 : CNF.NClause := [(97,true),(42,true),(37,false),(32,true),(47,false),(52,false)]
theorem der_26188 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26188 :=
  CNF.rup_sound cl_26188 [cl_2278,cl_26173] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2278 v h) (hints_cons _ _ _ (der_26173 v h) (by intro d hd; cases hd)))
def cl_26189 : CNF.NClause := [(97,true),(47,false),(37,true),(42,true),(52,false),(32,true)]
theorem der_26189 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26189 :=
  CNF.rup_sound cl_26189 [cl_2280,cl_26174] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2280 v h) (hints_cons _ _ _ (der_26174 v h) (by intro d hd; cases hd)))
def cl_26190 : CNF.NClause := [(97,true),(52,false),(37,false),(42,false),(47,true),(56,true)]
theorem der_26190 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26190 :=
  CNF.rup_sound cl_26190 [cl_2282,cl_25798] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2282 v h) (hints_cons _ _ _ (der_25798 v h) (by intro d hd; cases hd)))
def cl_26191 : CNF.NClause := [(97,true),(37,true),(42,false),(32,true),(47,true),(52,false)]
theorem der_26191 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26191 :=
  CNF.rup_sound cl_26191 [cl_2284,cl_26176] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2284 v h) (hints_cons _ _ _ (der_26176 v h) (by intro d hd; cases hd)))
def cl_26192 : CNF.NClause := [(97,true),(42,true),(37,false),(32,true),(47,true),(52,false)]
theorem der_26192 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26192 :=
  CNF.rup_sound cl_26192 [cl_2286,cl_26177] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2286 v h) (hints_cons _ _ _ (der_26177 v h) (by intro d hd; cases hd)))
def cl_26193 : CNF.NClause := [(97,true),(47,false),(37,false),(42,false),(52,true),(56,true)]
theorem der_26193 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26193 :=
  CNF.rup_sound cl_26193 [cl_2290,cl_2289] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2290 v h) (hints_cons _ _ _ (inp_2289 v h) (by intro d hd; cases hd)))
def cl_26194 : CNF.NClause := [(97,true),(47,false),(42,false),(32,true),(52,true),(56,true)]
theorem der_26194 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26194 :=
  CNF.rup_sound cl_26194 [cl_2292,cl_26193] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2292 v h) (hints_cons _ _ _ (der_26193 v h) (by intro d hd; cases hd)))
def cl_26195 : CNF.NClause := [(97,true),(42,true),(37,false),(32,true),(47,false),(52,true)]
theorem der_26195 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26195 :=
  CNF.rup_sound cl_26195 [cl_2294,cl_26181] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2294 v h) (hints_cons _ _ _ (der_26181 v h) (by intro d hd; cases hd)))
def cl_26196 : CNF.NClause := [(97,true),(37,false),(42,false),(47,true),(52,true),(56,true)]
theorem der_26196 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26196 :=
  CNF.rup_sound cl_26196 [cl_2298,cl_23798] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2298 v h) (hints_cons _ _ _ (der_23798 v h) (by intro d hd; cases hd)))
def cl_26197 : CNF.NClause := [(102,true),(38,false),(44,false),(50,false),(51,false),(57,false)]
theorem der_26197 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26197 :=
  CNF.rup_sound cl_26197 [cl_2562,cl_23862] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2562 v h) (hints_cons _ _ _ (der_23862 v h) (by intro d hd; cases hd)))
def cl_26198 : CNF.NClause := [(102,true),(50,false),(38,true),(44,false),(51,false),(57,false)]
theorem der_26198 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26198 :=
  CNF.rup_sound cl_26198 [cl_2564,cl_26169] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2564 v h) (hints_cons _ _ _ (der_26169 v h) (by intro d hd; cases hd)))
def cl_26199 : CNF.NClause := [(102,true),(32,true),(38,false),(50,false),(51,false),(57,false)]
theorem der_26199 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26199 :=
  CNF.rup_sound cl_26199 [cl_2566,cl_26197] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2566 v h) (hints_cons _ _ _ (der_26197 v h) (by intro d hd; cases hd)))
def cl_26200 : CNF.NClause := [(102,true),(50,false),(38,true),(44,true),(51,false),(57,false)]
theorem der_26200 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26200 :=
  CNF.rup_sound cl_26200 [cl_2568,cl_2567] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2568 v h) (hints_cons _ _ _ (inp_2567 v h) (by intro d hd; cases hd)))
def cl_26201 : CNF.NClause := [(102,true),(38,false),(44,false),(50,true),(51,false),(57,false)]
theorem der_26201 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26201 :=
  CNF.rup_sound cl_26201 [cl_2570,cl_26168] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2570 v h) (hints_cons _ _ _ (der_26168 v h) (by intro d hd; cases hd)))
def cl_26202 : CNF.NClause := [(102,true),(57,false),(38,true),(44,false),(50,true),(51,false)]
theorem der_26202 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26202 :=
  CNF.rup_sound cl_26202 [cl_2572,cl_26170] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2572 v h) (hints_cons _ _ _ (der_26170 v h) (by intro d hd; cases hd)))
def cl_26203 : CNF.NClause := [(102,true),(38,false),(44,true),(50,true),(51,false),(57,false)]
theorem der_26203 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26203 :=
  CNF.rup_sound cl_26203 [cl_2574,cl_23896] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2574 v h) (hints_cons _ _ _ (der_23896 v h) (by intro d hd; cases hd)))
def cl_26204 : CNF.NClause := [(102,true),(51,false),(38,true),(44,true),(57,false),(32,true)]
theorem der_26204 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26204 :=
  CNF.rup_sound cl_26204 [cl_2576,cl_26200] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2576 v h) (hints_cons _ _ _ (der_26200 v h) (by intro d hd; cases hd)))
def cl_26205 : CNF.NClause := [(102,true),(38,false),(44,false),(50,false),(51,true),(57,false)]
theorem der_26205 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26205 :=
  CNF.rup_sound cl_26205 [cl_2578,cl_2577] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2578 v h) (hints_cons _ _ _ (inp_2577 v h) (by intro d hd; cases hd)))
def cl_26206 : CNF.NClause := [(102,true),(50,false),(38,true),(44,false),(32,true),(57,false)]
theorem der_26206 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26206 :=
  CNF.rup_sound cl_26206 [cl_2580,cl_26198] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2580 v h) (hints_cons _ _ _ (der_26198 v h) (by intro d hd; cases hd)))
def cl_26207 : CNF.NClause := [(102,true),(32,true),(38,false),(44,true),(50,false),(57,false)]
theorem der_26207 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26207 :=
  CNF.rup_sound cl_26207 [cl_2582,cl_26199] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2582 v h) (hints_cons _ _ _ (der_26199 v h) (by intro d hd; cases hd)))
def cl_26208 : CNF.NClause := [(102,true),(50,false),(38,true),(44,true),(57,false),(32,true)]
theorem der_26208 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26208 :=
  CNF.rup_sound cl_26208 [cl_2584,cl_26200] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2584 v h) (hints_cons _ _ _ (der_26200 v h) (by intro d hd; cases hd)))
def cl_26209 : CNF.NClause := [(102,true),(38,false),(44,false),(50,true),(51,true),(57,false)]
theorem der_26209 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26209 :=
  CNF.rup_sound cl_26209 [cl_2586,cl_26123] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2586 v h) (hints_cons _ _ _ (der_26123 v h) (by intro d hd; cases hd)))
def cl_26210 : CNF.NClause := [(102,true),(57,false),(38,true),(44,false),(50,true),(32,true)]
theorem der_26210 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26210 :=
  CNF.rup_sound cl_26210 [cl_2588,cl_26202] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2588 v h) (hints_cons _ _ _ (der_26202 v h) (by intro d hd; cases hd)))
def cl_26211 : CNF.NClause := [(102,true),(32,true),(38,false),(44,true),(50,true),(57,false)]
theorem der_26211 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26211 :=
  CNF.rup_sound cl_26211 [cl_2590,cl_26203] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2590 v h) (hints_cons _ _ _ (der_26203 v h) (by intro d hd; cases hd)))
def cl_26212 : CNF.NClause := [(102,true),(38,false),(44,false),(50,false),(51,false),(57,true)]
theorem der_26212 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26212 :=
  CNF.rup_sound cl_26212 [cl_2594,cl_2593] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2594 v h) (hints_cons _ _ _ (inp_2593 v h) (by intro d hd; cases hd)))
def cl_26213 : CNF.NClause := [(102,true),(38,true),(44,false),(50,false),(32,true),(51,false)]
theorem der_26213 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26213 :=
  CNF.rup_sound cl_26213 [cl_2596,cl_26198] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2596 v h) (hints_cons _ _ _ (der_26198 v h) (by intro d hd; cases hd)))
def cl_26214 : CNF.NClause := [(102,true),(32,true),(38,false),(44,true),(50,false),(51,false)]
theorem der_26214 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26214 :=
  CNF.rup_sound cl_26214 [cl_2598,cl_26199] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2598 v h) (hints_cons _ _ _ (der_26199 v h) (by intro d hd; cases hd)))
def cl_26215 : CNF.NClause := [(102,true),(50,false),(38,true),(44,true),(51,false),(57,true)]
theorem der_26215 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26215 :=
  CNF.rup_sound cl_26215 [cl_2600,cl_23911] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2600 v h) (hints_cons _ _ _ (der_23911 v h) (by intro d hd; cases hd)))
def cl_26216 : CNF.NClause := [(102,true),(38,false),(44,false),(50,true),(51,false),(57,true)]
theorem der_26216 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26216 :=
  CNF.rup_sound cl_26216 [cl_2602,cl_26124] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2602 v h) (hints_cons _ _ _ (der_26124 v h) (by intro d hd; cases hd)))
def cl_26217 : CNF.NClause := [(102,true),(38,true),(44,false),(32,true),(50,true),(51,false)]
theorem der_26217 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26217 :=
  CNF.rup_sound cl_26217 [cl_2604,cl_26202] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2604 v h) (hints_cons _ _ _ (der_26202 v h) (by intro d hd; cases hd)))
def cl_26218 : CNF.NClause := [(102,true),(38,false),(44,true),(50,true),(51,false),(57,true)]
theorem der_26218 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26218 :=
  CNF.rup_sound cl_26218 [cl_2606,cl_23896] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2606 v h) (hints_cons _ _ _ (der_23896 v h) (by intro d hd; cases hd)))
def cl_26219 : CNF.NClause := [(102,true),(32,true),(38,false),(44,false),(50,false),(51,true)]
theorem der_26219 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26219 :=
  CNF.rup_sound cl_26219 [cl_2610,cl_26205] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2610 v h) (hints_cons _ _ _ (der_26205 v h) (by intro d hd; cases hd)))
def cl_26220 : CNF.NClause := [(102,true),(50,false),(38,true),(44,false),(32,true),(51,true)]
theorem der_26220 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26220 :=
  CNF.rup_sound cl_26220 [cl_2612,cl_26206] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2612 v h) (hints_cons _ _ _ (der_26206 v h) (by intro d hd; cases hd)))
def cl_26221 : CNF.NClause := [(102,true),(32,true),(38,false),(44,true),(50,false),(57,true)]
theorem der_26221 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26221 :=
  CNF.rup_sound cl_26221 [cl_2614,cl_26214] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2614 v h) (hints_cons _ _ _ (der_26214 v h) (by intro d hd; cases hd)))
def cl_26222 : CNF.NClause := [(102,true),(38,false),(44,false),(50,true),(51,true),(57,true)]
theorem der_26222 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26222 :=
  CNF.rup_sound cl_26222 [cl_2618,cl_26125] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2618 v h) (hints_cons _ _ _ (der_26125 v h) (by intro d hd; cases hd)))
def cl_26223 : CNF.NClause := [(107,true),(55,false),(39,false),(41,false),(48,false),(58,false)]
theorem der_26223 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26223 :=
  CNF.rup_sound cl_26223 [cl_2882,cl_23903] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2882 v h) (hints_cons _ _ _ (der_23903 v h) (by intro d hd; cases hd)))
def cl_26224 : CNF.NClause := [(107,true),(55,false),(39,true),(41,false),(48,false),(58,false)]
theorem der_26224 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26224 :=
  CNF.rup_sound cl_26224 [cl_2884,cl_24722] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2884 v h) (hints_cons _ _ _ (der_24722 v h) (by intro d hd; cases hd)))
def cl_26225 : CNF.NClause := [(107,true),(55,false),(39,false),(41,true),(48,false),(58,false)]
theorem der_26225 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26225 :=
  CNF.rup_sound cl_26225 [cl_2886,cl_25874] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2886 v h) (hints_cons _ _ _ (der_25874 v h) (by intro d hd; cases hd)))
def cl_26226 : CNF.NClause := [(107,true),(55,false),(39,true),(41,true),(48,false),(58,false)]
theorem der_26226 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26226 :=
  CNF.rup_sound cl_26226 [cl_2888,cl_24723] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2888 v h) (hints_cons _ _ _ (der_24723 v h) (by intro d hd; cases hd)))
def cl_26227 : CNF.NClause := [(107,true),(55,false),(39,false),(41,false),(48,true),(58,false)]
theorem der_26227 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26227 :=
  CNF.rup_sound cl_26227 [cl_2890,cl_2889] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2890 v h) (hints_cons _ _ _ (inp_2889 v h) (by intro d hd; cases hd)))
def cl_26228 : CNF.NClause := [(107,true),(55,false),(39,true),(41,false),(32,true),(58,false)]
theorem der_26228 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26228 :=
  CNF.rup_sound cl_26228 [cl_2892,cl_26224] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2892 v h) (hints_cons _ _ _ (der_26224 v h) (by intro d hd; cases hd)))
def cl_26229 : CNF.NClause := [(107,true),(55,false),(39,false),(41,true),(48,true),(58,false)]
theorem der_26229 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26229 :=
  CNF.rup_sound cl_26229 [cl_2894,cl_25875] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2894 v h) (hints_cons _ _ _ (der_25875 v h) (by intro d hd; cases hd)))
def cl_26230 : CNF.NClause := [(107,true),(55,false),(39,true),(41,true),(48,true),(58,false)]
theorem der_26230 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26230 :=
  CNF.rup_sound cl_26230 [cl_2896,cl_24725] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2896 v h) (hints_cons _ _ _ (der_24725 v h) (by intro d hd; cases hd)))
def cl_26231 : CNF.NClause := [(107,true),(39,false),(41,false),(48,false),(55,true),(58,false)]
theorem der_26231 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26231 :=
  CNF.rup_sound cl_26231 [cl_2898,cl_25286] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2898 v h) (hints_cons _ _ _ (der_25286 v h) (by intro d hd; cases hd)))
def cl_26232 : CNF.NClause := [(107,true),(39,true),(41,false),(48,false),(55,true),(58,false)]
theorem der_26232 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26232 :=
  CNF.rup_sound cl_26232 [cl_2900,cl_24728] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2900 v h) (hints_cons _ _ _ (der_24728 v h) (by intro d hd; cases hd)))
def cl_26233 : CNF.NClause := [(107,true),(58,false),(39,false),(41,true),(48,false),(55,true)]
theorem der_26233 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26233 :=
  CNF.rup_sound cl_26233 [cl_2902,cl_25876] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2902 v h) (hints_cons _ _ _ (der_25876 v h) (by intro d hd; cases hd)))
def cl_26234 : CNF.NClause := [(107,true),(58,false),(41,true),(48,false),(32,true),(39,true)]
theorem der_26234 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26234 :=
  CNF.rup_sound cl_26234 [cl_2904,cl_26226] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2904 v h) (hints_cons _ _ _ (der_26226 v h) (by intro d hd; cases hd)))
def cl_26235 : CNF.NClause := [(107,true),(39,false),(41,false),(48,true),(55,true),(58,false)]
theorem der_26235 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26235 :=
  CNF.rup_sound cl_26235 [cl_2906,cl_25587] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2906 v h) (hints_cons _ _ _ (der_25587 v h) (by intro d hd; cases hd)))
def cl_26236 : CNF.NClause := [(107,true),(39,true),(41,false),(48,true),(55,true),(58,false)]
theorem der_26236 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26236 :=
  CNF.rup_sound cl_26236 [cl_2908,cl_24728] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2908 v h) (hints_cons _ _ _ (der_24728 v h) (by intro d hd; cases hd)))
def cl_26237 : CNF.NClause := [(107,true),(58,false),(39,false),(41,true),(48,true),(55,true)]
theorem der_26237 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26237 :=
  CNF.rup_sound cl_26237 [cl_2910,cl_25877] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2910 v h) (hints_cons _ _ _ (der_25877 v h) (by intro d hd; cases hd)))
def cl_26238 : CNF.NClause := [(107,true),(55,false),(39,false),(41,false),(48,false),(58,true)]
theorem der_26238 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26238 :=
  CNF.rup_sound cl_26238 [cl_2914,cl_25050] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2914 v h) (hints_cons _ _ _ (der_25050 v h) (by intro d hd; cases hd)))
def cl_26239 : CNF.NClause := [(107,true),(55,false),(39,true),(41,false),(48,false),(32,true)]
theorem der_26239 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26239 :=
  CNF.rup_sound cl_26239 [cl_2916,cl_26224] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2916 v h) (hints_cons _ _ _ (der_26224 v h) (by intro d hd; cases hd)))
def cl_26240 : CNF.NClause := [(107,true),(55,false),(39,false),(41,true),(48,false),(58,true)]
theorem der_26240 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26240 :=
  CNF.rup_sound cl_26240 [cl_2918,cl_25878] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2918 v h) (hints_cons _ _ _ (der_25878 v h) (by intro d hd; cases hd)))
def cl_26241 : CNF.NClause := [(107,true),(48,false),(39,true),(41,true),(55,false),(32,true)]
theorem der_26241 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26241 :=
  CNF.rup_sound cl_26241 [cl_2920,cl_26226] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2920 v h) (hints_cons _ _ _ (der_26226 v h) (by intro d hd; cases hd)))
def cl_26242 : CNF.NClause := [(107,true),(55,false),(39,false),(41,false),(48,true),(58,true)]
theorem der_26242 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26242 :=
  CNF.rup_sound cl_26242 [cl_2922,cl_25588] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2922 v h) (hints_cons _ _ _ (der_25588 v h) (by intro d hd; cases hd)))
def cl_26243 : CNF.NClause := [(107,true),(55,false),(39,true),(41,false),(32,true),(58,true)]
theorem der_26243 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26243 :=
  CNF.rup_sound cl_26243 [cl_2924,cl_26239] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2924 v h) (hints_cons _ _ _ (der_26239 v h) (by intro d hd; cases hd)))
def cl_26244 : CNF.NClause := [(107,true),(55,false),(39,false),(41,true),(48,true),(58,true)]
theorem der_26244 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26244 :=
  CNF.rup_sound cl_26244 [cl_2926,cl_25879] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2926 v h) (hints_cons _ _ _ (der_25879 v h) (by intro d hd; cases hd)))
def cl_26245 : CNF.NClause := [(107,true),(39,false),(41,false),(48,false),(55,true),(58,true)]
theorem der_26245 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26245 :=
  CNF.rup_sound cl_26245 [cl_2930,cl_25287] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2930 v h) (hints_cons _ _ _ (der_25287 v h) (by intro d hd; cases hd)))
def cl_26246 : CNF.NClause := [(107,true),(32,true),(39,true),(41,false),(48,false),(58,true)]
theorem der_26246 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26246 :=
  CNF.rup_sound cl_26246 [cl_2932,cl_26239] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2932 v h) (hints_cons _ _ _ (der_26239 v h) (by intro d hd; cases hd)))
def cl_26247 : CNF.NClause := [(107,true),(39,false),(41,true),(48,false),(55,true),(58,true)]
theorem der_26247 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26247 :=
  CNF.rup_sound cl_26247 [cl_2934,cl_25880] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2934 v h) (hints_cons _ _ _ (der_25880 v h) (by intro d hd; cases hd)))
def cl_26248 : CNF.NClause := [(107,true),(39,false),(41,false),(48,true),(55,true),(58,true)]
theorem der_26248 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26248 :=
  CNF.rup_sound cl_26248 [cl_2938,cl_25589] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2938 v h) (hints_cons _ _ _ (der_25589 v h) (by intro d hd; cases hd)))
def cl_26249 : CNF.NClause := [(112,true),(59,false),(43,false),(40,false),(54,false),(46,false)]
theorem der_26249 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26249 :=
  CNF.rup_sound cl_26249 [cl_3202,cl_25055] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3202 v h) (hints_cons _ _ _ (der_25055 v h) (by intro d hd; cases hd)))
def cl_26250 : CNF.NClause := [(112,true),(59,false),(40,true),(46,false),(54,false),(43,false)]
theorem der_26250 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26250 :=
  CNF.rup_sound cl_26250 [cl_3204,cl_23790] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3204 v h) (hints_cons _ _ _ (der_23790 v h) (by intro d hd; cases hd)))
def cl_26251 : CNF.NClause := [(112,true),(59,false),(40,false),(43,true),(46,false),(54,false)]
theorem der_26251 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26251 :=
  CNF.rup_sound cl_26251 [cl_3206,cl_25606] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3206 v h) (hints_cons _ _ _ (der_25606 v h) (by intro d hd; cases hd)))
def cl_26252 : CNF.NClause := [(112,true),(59,false),(40,true),(46,false),(54,false),(32,true)]
theorem der_26252 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26252 :=
  CNF.rup_sound cl_26252 [cl_3208,cl_26250] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3208 v h) (hints_cons _ _ _ (der_26250 v h) (by intro d hd; cases hd)))
def cl_26253 : CNF.NClause := [(112,true),(59,false),(40,false),(43,false),(46,true),(54,false)]
theorem der_26253 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26253 :=
  CNF.rup_sound cl_26253 [cl_3210,cl_25313] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3210 v h) (hints_cons _ _ _ (der_25313 v h) (by intro d hd; cases hd)))
def cl_26254 : CNF.NClause := [(112,true),(46,true),(40,true),(43,false),(54,false),(59,false)]
theorem der_26254 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26254 :=
  CNF.rup_sound cl_26254 [cl_3212,cl_3211] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3212 v h) (hints_cons _ _ _ (inp_3211 v h) (by intro d hd; cases hd)))
def cl_26255 : CNF.NClause := [(112,true),(59,false),(40,false),(43,true),(46,true),(54,false)]
theorem der_26255 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26255 :=
  CNF.rup_sound cl_26255 [cl_3214,cl_25607] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3214 v h) (hints_cons _ _ _ (der_25607 v h) (by intro d hd; cases hd)))
def cl_26256 : CNF.NClause := [(112,true),(54,false),(40,true),(43,true),(32,true),(59,false)]
theorem der_26256 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26256 :=
  CNF.rup_sound cl_26256 [cl_3216,cl_26252] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3216 v h) (hints_cons _ _ _ (der_26252 v h) (by intro d hd; cases hd)))
def cl_26257 : CNF.NClause := [(112,true),(59,false),(43,false),(40,false),(54,true),(46,false)]
theorem der_26257 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26257 :=
  CNF.rup_sound cl_26257 [cl_3218,cl_25055] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3218 v h) (hints_cons _ _ _ (der_25055 v h) (by intro d hd; cases hd)))
def cl_26258 : CNF.NClause := [(112,true),(59,false),(40,true),(46,false),(54,true),(43,false)]
theorem der_26258 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26258 :=
  CNF.rup_sound cl_26258 [cl_3220,cl_25061] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3220 v h) (hints_cons _ _ _ (der_25061 v h) (by intro d hd; cases hd)))
def cl_26259 : CNF.NClause := [(112,true),(59,false),(40,false),(43,true),(46,false),(54,true)]
theorem der_26259 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26259 :=
  CNF.rup_sound cl_26259 [cl_3222,cl_25608] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3222 v h) (hints_cons _ _ _ (der_25608 v h) (by intro d hd; cases hd)))
def cl_26260 : CNF.NClause := [(112,true),(59,false),(40,true),(43,true),(46,false),(32,true)]
theorem der_26260 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26260 :=
  CNF.rup_sound cl_26260 [cl_3224,cl_26252] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3224 v h) (hints_cons _ _ _ (der_26252 v h) (by intro d hd; cases hd)))
def cl_26261 : CNF.NClause := [(112,true),(59,false),(40,false),(43,false),(46,true),(54,true)]
theorem der_26261 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26261 :=
  CNF.rup_sound cl_26261 [cl_3226,cl_25314] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3226 v h) (hints_cons _ _ _ (der_25314 v h) (by intro d hd; cases hd)))
def cl_26262 : CNF.NClause := [(112,true),(59,false),(40,true),(46,true),(54,true),(43,false)]
theorem der_26262 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26262 :=
  CNF.rup_sound cl_26262 [cl_3228,cl_23899] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3228 v h) (hints_cons _ _ _ (der_23899 v h) (by intro d hd; cases hd)))
def cl_26263 : CNF.NClause := [(112,true),(59,false),(40,false),(43,true),(46,true),(54,true)]
theorem der_26263 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26263 :=
  CNF.rup_sound cl_26263 [cl_3230,cl_25609] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3230 v h) (hints_cons _ _ _ (der_25609 v h) (by intro d hd; cases hd)))
def cl_26264 : CNF.NClause := [(112,true),(40,false),(46,false),(43,false),(54,false),(59,true)]
theorem der_26264 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26264 :=
  CNF.rup_sound cl_26264 [cl_3234,cl_25782] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3234 v h) (hints_cons _ _ _ (der_25782 v h) (by intro d hd; cases hd)))
def cl_26265 : CNF.NClause := [(112,true),(40,true),(32,true),(46,false),(54,false),(43,false)]
theorem der_26265 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26265 :=
  CNF.rup_sound cl_26265 [cl_3236,cl_26250] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3236 v h) (hints_cons _ _ _ (der_26250 v h) (by intro d hd; cases hd)))
def cl_26266 : CNF.NClause := [(112,true),(40,false),(32,true),(43,true),(46,false),(54,false)]
theorem der_26266 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26266 :=
  CNF.rup_sound cl_26266 [cl_3238,cl_26251] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3238 v h) (hints_cons _ _ _ (der_26251 v h) (by intro d hd; cases hd)))
def cl_26267 : CNF.NClause := [(112,true),(43,true),(40,true),(32,true),(54,false),(46,false)]
theorem der_26267 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26267 :=
  CNF.rup_sound cl_26267 [cl_3240,cl_26252] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3240 v h) (hints_cons _ _ _ (der_26252 v h) (by intro d hd; cases hd)))
def cl_26268 : CNF.NClause := [(112,true),(40,false),(43,false),(46,true),(54,false),(59,true)]
theorem der_26268 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26268 :=
  CNF.rup_sound cl_26268 [cl_3242,cl_25789] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3242 v h) (hints_cons _ _ _ (der_25789 v h) (by intro d hd; cases hd)))
def cl_26269 : CNF.NClause := [(112,true),(40,true),(59,true),(32,true),(54,false),(43,false)]
theorem der_26269 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26269 :=
  CNF.rup_sound cl_26269 [cl_3244,cl_26265] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3244 v h) (hints_cons _ _ _ (der_26265 v h) (by intro d hd; cases hd)))
def cl_26270 : CNF.NClause := [(112,true),(40,false),(32,true),(43,true),(54,false),(59,true)]
theorem der_26270 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26270 :=
  CNF.rup_sound cl_26270 [cl_3246,cl_26266] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3246 v h) (hints_cons _ _ _ (der_26266 v h) (by intro d hd; cases hd)))
def cl_26271 : CNF.NClause := [(112,true),(40,false),(46,false),(43,false),(54,true),(59,true)]
theorem der_26271 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26271 :=
  CNF.rup_sound cl_26271 [cl_3250,cl_25056] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3250 v h) (hints_cons _ _ _ (der_25056 v h) (by intro d hd; cases hd)))
def cl_26272 : CNF.NClause := [(112,true),(43,false),(40,true),(46,false),(54,true),(59,true)]
theorem der_26272 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26272 :=
  CNF.rup_sound cl_26272 [cl_3252,cl_25062] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3252 v h) (hints_cons _ _ _ (der_25062 v h) (by intro d hd; cases hd)))
def cl_26273 : CNF.NClause := [(112,true),(40,false),(32,true),(43,true),(46,false),(54,true)]
theorem der_26273 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26273 :=
  CNF.rup_sound cl_26273 [cl_3254,cl_26259] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3254 v h) (hints_cons _ _ _ (der_26259 v h) (by intro d hd; cases hd)))
def cl_26274 : CNF.NClause := [(112,true),(40,false),(43,false),(46,true),(54,true),(59,true)]
theorem der_26274 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26274 :=
  CNF.rup_sound cl_26274 [cl_3258,cl_25315] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3258 v h) (hints_cons _ _ _ (der_25315 v h) (by intro d hd; cases hd)))
def chunk007 : List CNF.NClause := [cl_25750,cl_25751,cl_25752,cl_25753,cl_25754,cl_25755,cl_25756,cl_25757,cl_25758,cl_25759,cl_25760,cl_25761,cl_25762,cl_25763,cl_25764,cl_25765,cl_25766,cl_25767,cl_25768,cl_25769,cl_25770,cl_25771,cl_25772,cl_25773,cl_25774,cl_25775,cl_25776,cl_25777,cl_25778,cl_25779,cl_25780,cl_25781,cl_25782,cl_25783,cl_25784,cl_25785,cl_25786,cl_25787,cl_25788,cl_25789,cl_25790,cl_25791,cl_25792,cl_25793,cl_25794,cl_25795,cl_25796,cl_25797,cl_25798,cl_25799,cl_25800,cl_25801,cl_25802,cl_25803,cl_25804,cl_25805,cl_25806,cl_25807,cl_25808,cl_25809,cl_25810,cl_25811,cl_25812,cl_25813,cl_25814,cl_25815,cl_25816,cl_25817,cl_25818,cl_25819,cl_25820,cl_25822,cl_25823,cl_25824,cl_25825,cl_25826,cl_25827,cl_25828,cl_25829,cl_25830,cl_25831,cl_25832,cl_25833,cl_25834,cl_25835,cl_25838,cl_25840,cl_25841,cl_25842,cl_25843,cl_25844,cl_25845,cl_25846,cl_25847,cl_25848,cl_25849,cl_25850,cl_25851,cl_25852,cl_25854,cl_25856,cl_25859,cl_25860,cl_25861,cl_25862,cl_25863,cl_25864,cl_25865,cl_25866,cl_25867,cl_25868,cl_25869,cl_25870,cl_25871,cl_25872,cl_25873,cl_25874,cl_25875,cl_25876,cl_25877,cl_25878,cl_25879,cl_25880,cl_25881,cl_25882,cl_25883,cl_25884,cl_25885,cl_25886,cl_25887,cl_25888,cl_25889,cl_25890,cl_25891,cl_25892,cl_25893,cl_25894,cl_25895,cl_25896,cl_25897,cl_25898,cl_25899,cl_25900,cl_25901,cl_25902,cl_25903,cl_25904,cl_25905,cl_25906,cl_25907,cl_25908,cl_25909,cl_25910,cl_25911,cl_25912,cl_25913,cl_25914,cl_25915,cl_25916,cl_25917,cl_25919,cl_25921,cl_25923,cl_25926,cl_25927,cl_25928,cl_25929,cl_25930,cl_25931,cl_25932,cl_25933,cl_25934,cl_25935,cl_25936,cl_25937,cl_25938,cl_25939,cl_25940,cl_25941,cl_25942,cl_25943,cl_25944,cl_25945,cl_25946,cl_25947,cl_25948,cl_25949,cl_25950,cl_25951,cl_25952,cl_25953,cl_25954,cl_25955,cl_25956,cl_25957,cl_25958,cl_25959,cl_25960,cl_25961,cl_25962,cl_25963,cl_25964,cl_25965,cl_25966,cl_25967,cl_25968,cl_25969,cl_25970,cl_25971,cl_25972,cl_25973,cl_25974,cl_25975,cl_25976,cl_25977,cl_25978,cl_25979,cl_25980,cl_25981,cl_25982,cl_25983,cl_25984,cl_25985,cl_25986,cl_25987,cl_25988,cl_25989,cl_25990,cl_25991,cl_25992,cl_25993,cl_25994,cl_25995,cl_25996,cl_25997,cl_25998,cl_25999,cl_26000,cl_26001,cl_26002,cl_26003,cl_26004,cl_26005,cl_26006,cl_26007,cl_26008,cl_26009,cl_26010,cl_26011,cl_26012,cl_26013,cl_26014,cl_26015,cl_26016,cl_26017,cl_26018,cl_26019,cl_26020,cl_26021,cl_26022,cl_26023,cl_26024,cl_26025,cl_26026,cl_26027,cl_26028,cl_26029,cl_26030,cl_26031,cl_26032,cl_26033,cl_26034,cl_26035,cl_26036,cl_26037,cl_26038,cl_26039,cl_26040,cl_26041,cl_26042,cl_26043,cl_26044,cl_26045,cl_26046,cl_26049,cl_26050,cl_26051,cl_26052,cl_26053,cl_26054,cl_26055,cl_26056,cl_26057,cl_26058,cl_26059,cl_26060,cl_26061,cl_26062,cl_26063,cl_26064,cl_26065,cl_26066,cl_26067,cl_26068,cl_26069,cl_26070,cl_26071,cl_26072,cl_26073,cl_26074,cl_26075,cl_26077,cl_26078,cl_26079,cl_26080,cl_26081,cl_26082,cl_26084,cl_26085,cl_26086,cl_26087,cl_26088,cl_26089,cl_26090,cl_26091,cl_26092,cl_26093,cl_26094,cl_26095,cl_26097,cl_26098,cl_26099,cl_26100,cl_26101,cl_26102,cl_26103,cl_26104,cl_26105,cl_26106,cl_26107,cl_26108,cl_26109,cl_26110,cl_26112,cl_26113,cl_26114,cl_26115,cl_26116,cl_26117,cl_26118,cl_26119,cl_26120,cl_26121,cl_26122,cl_26123,cl_26124,cl_26125,cl_26126,cl_26128,cl_26129,cl_26130,cl_26131,cl_26132,cl_26133,cl_26134,cl_26135,cl_26136,cl_26137,cl_26138,cl_26139,cl_26140,cl_26141,cl_26142,cl_26143,cl_26144,cl_26145,cl_26146,cl_26147,cl_26148,cl_26149,cl_26150,cl_26151,cl_26152,cl_26153,cl_26154,cl_26155,cl_26156,cl_26157,cl_26158,cl_26159,cl_26160,cl_26161,cl_26162,cl_26163,cl_26164,cl_26165,cl_26166,cl_26167,cl_26168,cl_26169,cl_26170,cl_26171,cl_26172,cl_26173,cl_26174,cl_26175,cl_26176,cl_26177,cl_26179,cl_26181,cl_26183,cl_26186,cl_26187,cl_26188,cl_26189,cl_26190,cl_26191,cl_26192,cl_26193,cl_26194,cl_26195,cl_26196,cl_26197,cl_26198,cl_26199,cl_26200,cl_26201,cl_26202,cl_26203,cl_26204,cl_26205,cl_26206,cl_26207,cl_26208,cl_26209,cl_26210,cl_26211,cl_26212,cl_26213,cl_26214,cl_26215,cl_26216,cl_26217,cl_26218,cl_26219,cl_26220,cl_26221,cl_26222,cl_26223,cl_26224,cl_26225,cl_26226,cl_26227,cl_26228,cl_26229,cl_26230,cl_26231,cl_26232,cl_26233,cl_26234,cl_26235,cl_26236,cl_26237,cl_26238,cl_26239,cl_26240,cl_26241,cl_26242,cl_26243,cl_26244,cl_26245,cl_26246,cl_26247,cl_26248,cl_26249,cl_26250,cl_26251,cl_26252,cl_26253,cl_26254,cl_26255,cl_26256,cl_26257,cl_26258,cl_26259,cl_26260,cl_26261,cl_26262,cl_26263,cl_26264,cl_26265,cl_26266,cl_26267,cl_26268,cl_26269,cl_26270,cl_26271,cl_26272,cl_26273,cl_26274]
theorem chunk_sound007 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : ∀ c ∈ chunk007, CNF.Holds (v ∘ decodeVar) c :=
  (hints_cons _ _ _ (der_25750 v h) (hints_cons _ _ _ (der_25751 v h) (hints_cons _ _ _ (der_25752 v h) (hints_cons _ _ _ (der_25753 v h) (hints_cons _ _ _ (der_25754 v h) (hints_cons _ _ _ (der_25755 v h) (hints_cons _ _ _ (der_25756 v h) (hints_cons _ _ _ (der_25757 v h) (hints_cons _ _ _ (der_25758 v h) (hints_cons _ _ _ (der_25759 v h) (hints_cons _ _ _ (der_25760 v h) (hints_cons _ _ _ (der_25761 v h) (hints_cons _ _ _ (der_25762 v h) (hints_cons _ _ _ (der_25763 v h) (hints_cons _ _ _ (der_25764 v h) (hints_cons _ _ _ (der_25765 v h) (hints_cons _ _ _ (der_25766 v h) (hints_cons _ _ _ (der_25767 v h) (hints_cons _ _ _ (der_25768 v h) (hints_cons _ _ _ (der_25769 v h) (hints_cons _ _ _ (der_25770 v h) (hints_cons _ _ _ (der_25771 v h) (hints_cons _ _ _ (der_25772 v h) (hints_cons _ _ _ (der_25773 v h) (hints_cons _ _ _ (der_25774 v h) (hints_cons _ _ _ (der_25775 v h) (hints_cons _ _ _ (der_25776 v h) (hints_cons _ _ _ (der_25777 v h) (hints_cons _ _ _ (der_25778 v h) (hints_cons _ _ _ (der_25779 v h) (hints_cons _ _ _ (der_25780 v h) (hints_cons _ _ _ (der_25781 v h) (hints_cons _ _ _ (der_25782 v h) (hints_cons _ _ _ (der_25783 v h) (hints_cons _ _ _ (der_25784 v h) (hints_cons _ _ _ (der_25785 v h) (hints_cons _ _ _ (der_25786 v h) (hints_cons _ _ _ (der_25787 v h) (hints_cons _ _ _ (der_25788 v h) (hints_cons _ _ _ (der_25789 v h) (hints_cons _ _ _ (der_25790 v h) (hints_cons _ _ _ (der_25791 v h) (hints_cons _ _ _ (der_25792 v h) (hints_cons _ _ _ (der_25793 v h) (hints_cons _ _ _ (der_25794 v h) (hints_cons _ _ _ (der_25795 v h) (hints_cons _ _ _ (der_25796 v h) (hints_cons _ _ _ (der_25797 v h) (hints_cons _ _ _ (der_25798 v h) (hints_cons _ _ _ (der_25799 v h) (hints_cons _ _ _ (der_25800 v h) (hints_cons _ _ _ (der_25801 v h) (hints_cons _ _ _ (der_25802 v h) (hints_cons _ _ _ (der_25803 v h) (hints_cons _ _ _ (der_25804 v h) (hints_cons _ _ _ (der_25805 v h) (hints_cons _ _ _ (der_25806 v h) (hints_cons _ _ _ (der_25807 v h) (hints_cons _ _ _ (der_25808 v h) (hints_cons _ _ _ (der_25809 v h) (hints_cons _ _ _ (der_25810 v h) (hints_cons _ _ _ (der_25811 v h) (hints_cons _ _ _ (der_25812 v h) (hints_cons _ _ _ (der_25813 v h) (hints_cons _ _ _ (der_25814 v h) (hints_cons _ _ _ (der_25815 v h) (hints_cons _ _ _ (der_25816 v h) (hints_cons _ _ _ (der_25817 v h) (hints_cons _ _ _ (der_25818 v h) (hints_cons _ _ _ (der_25819 v h) (hints_cons _ _ _ (der_25820 v h) (hints_cons _ _ _ (der_25822 v h) (hints_cons _ _ _ (der_25823 v h) (hints_cons _ _ _ (der_25824 v h) (hints_cons _ _ _ (der_25825 v h) (hints_cons _ _ _ (der_25826 v h) (hints_cons _ _ _ (der_25827 v h) (hints_cons _ _ _ (der_25828 v h) (hints_cons _ _ _ (der_25829 v h) (hints_cons _ _ _ (der_25830 v h) (hints_cons _ _ _ (der_25831 v h) (hints_cons _ _ _ (der_25832 v h) (hints_cons _ _ _ (der_25833 v h) (hints_cons _ _ _ (der_25834 v h) (hints_cons _ _ _ (der_25835 v h) (hints_cons _ _ _ (der_25838 v h) (hints_cons _ _ _ (der_25840 v h) (hints_cons _ _ _ (der_25841 v h) (hints_cons _ _ _ (der_25842 v h) (hints_cons _ _ _ (der_25843 v h) (hints_cons _ _ _ (der_25844 v h) (hints_cons _ _ _ (der_25845 v h) (hints_cons _ _ _ (der_25846 v h) (hints_cons _ _ _ (der_25847 v h) (hints_cons _ _ _ (der_25848 v h) (hints_cons _ _ _ (der_25849 v h) (hints_cons _ _ _ (der_25850 v h) (hints_cons _ _ _ (der_25851 v h) (hints_cons _ _ _ (der_25852 v h) (hints_cons _ _ _ (der_25854 v h) (hints_cons _ _ _ (der_25856 v h) (hints_cons _ _ _ (der_25859 v h) (hints_cons _ _ _ (der_25860 v h) (hints_cons _ _ _ (der_25861 v h) (hints_cons _ _ _ (der_25862 v h) (hints_cons _ _ _ (der_25863 v h) (hints_cons _ _ _ (der_25864 v h) (hints_cons _ _ _ (der_25865 v h) (hints_cons _ _ _ (der_25866 v h) (hints_cons _ _ _ (der_25867 v h) (hints_cons _ _ _ (der_25868 v h) (hints_cons _ _ _ (der_25869 v h) (hints_cons _ _ _ (der_25870 v h) (hints_cons _ _ _ (der_25871 v h) (hints_cons _ _ _ (der_25872 v h) (hints_cons _ _ _ (der_25873 v h) (hints_cons _ _ _ (der_25874 v h) (hints_cons _ _ _ (der_25875 v h) (hints_cons _ _ _ (der_25876 v h) (hints_cons _ _ _ (der_25877 v h) (hints_cons _ _ _ (der_25878 v h) (hints_cons _ _ _ (der_25879 v h) (hints_cons _ _ _ (der_25880 v h) (hints_cons _ _ _ (der_25881 v h) (hints_cons _ _ _ (der_25882 v h) (hints_cons _ _ _ (der_25883 v h) (hints_cons _ _ _ (der_25884 v h) (hints_cons _ _ _ (der_25885 v h) (hints_cons _ _ _ (der_25886 v h) (hints_cons _ _ _ (der_25887 v h) (hints_cons _ _ _ (der_25888 v h) (hints_cons _ _ _ (der_25889 v h) (hints_cons _ _ _ (der_25890 v h) (hints_cons _ _ _ (der_25891 v h) (hints_cons _ _ _ (der_25892 v h) (hints_cons _ _ _ (der_25893 v h) (hints_cons _ _ _ (der_25894 v h) (hints_cons _ _ _ (der_25895 v h) (hints_cons _ _ _ (der_25896 v h) (hints_cons _ _ _ (der_25897 v h) (hints_cons _ _ _ (der_25898 v h) (hints_cons _ _ _ (der_25899 v h) (hints_cons _ _ _ (der_25900 v h) (hints_cons _ _ _ (der_25901 v h) (hints_cons _ _ _ (der_25902 v h) (hints_cons _ _ _ (der_25903 v h) (hints_cons _ _ _ (der_25904 v h) (hints_cons _ _ _ (der_25905 v h) (hints_cons _ _ _ (der_25906 v h) (hints_cons _ _ _ (der_25907 v h) (hints_cons _ _ _ (der_25908 v h) (hints_cons _ _ _ (der_25909 v h) (hints_cons _ _ _ (der_25910 v h) (hints_cons _ _ _ (der_25911 v h) (hints_cons _ _ _ (der_25912 v h) (hints_cons _ _ _ (der_25913 v h) (hints_cons _ _ _ (der_25914 v h) (hints_cons _ _ _ (der_25915 v h) (hints_cons _ _ _ (der_25916 v h) (hints_cons _ _ _ (der_25917 v h) (hints_cons _ _ _ (der_25919 v h) (hints_cons _ _ _ (der_25921 v h) (hints_cons _ _ _ (der_25923 v h) (hints_cons _ _ _ (der_25926 v h) (hints_cons _ _ _ (der_25927 v h) (hints_cons _ _ _ (der_25928 v h) (hints_cons _ _ _ (der_25929 v h) (hints_cons _ _ _ (der_25930 v h) (hints_cons _ _ _ (der_25931 v h) (hints_cons _ _ _ (der_25932 v h) (hints_cons _ _ _ (der_25933 v h) (hints_cons _ _ _ (der_25934 v h) (hints_cons _ _ _ (der_25935 v h) (hints_cons _ _ _ (der_25936 v h) (hints_cons _ _ _ (der_25937 v h) (hints_cons _ _ _ (der_25938 v h) (hints_cons _ _ _ (der_25939 v h) (hints_cons _ _ _ (der_25940 v h) (hints_cons _ _ _ (der_25941 v h) (hints_cons _ _ _ (der_25942 v h) (hints_cons _ _ _ (der_25943 v h) (hints_cons _ _ _ (der_25944 v h) (hints_cons _ _ _ (der_25945 v h) (hints_cons _ _ _ (der_25946 v h) (hints_cons _ _ _ (der_25947 v h) (hints_cons _ _ _ (der_25948 v h) (hints_cons _ _ _ (der_25949 v h) (hints_cons _ _ _ (der_25950 v h) (hints_cons _ _ _ (der_25951 v h) (hints_cons _ _ _ (der_25952 v h) (hints_cons _ _ _ (der_25953 v h) (hints_cons _ _ _ (der_25954 v h) (hints_cons _ _ _ (der_25955 v h) (hints_cons _ _ _ (der_25956 v h) (hints_cons _ _ _ (der_25957 v h) (hints_cons _ _ _ (der_25958 v h) (hints_cons _ _ _ (der_25959 v h) (hints_cons _ _ _ (der_25960 v h) (hints_cons _ _ _ (der_25961 v h) (hints_cons _ _ _ (der_25962 v h) (hints_cons _ _ _ (der_25963 v h) (hints_cons _ _ _ (der_25964 v h) (hints_cons _ _ _ (der_25965 v h) (hints_cons _ _ _ (der_25966 v h) (hints_cons _ _ _ (der_25967 v h) (hints_cons _ _ _ (der_25968 v h) (hints_cons _ _ _ (der_25969 v h) (hints_cons _ _ _ (der_25970 v h) (hints_cons _ _ _ (der_25971 v h) (hints_cons _ _ _ (der_25972 v h) (hints_cons _ _ _ (der_25973 v h) (hints_cons _ _ _ (der_25974 v h) (hints_cons _ _ _ (der_25975 v h) (hints_cons _ _ _ (der_25976 v h) (hints_cons _ _ _ (der_25977 v h) (hints_cons _ _ _ (der_25978 v h) (hints_cons _ _ _ (der_25979 v h) (hints_cons _ _ _ (der_25980 v h) (hints_cons _ _ _ (der_25981 v h) (hints_cons _ _ _ (der_25982 v h) (hints_cons _ _ _ (der_25983 v h) (hints_cons _ _ _ (der_25984 v h) (hints_cons _ _ _ (der_25985 v h) (hints_cons _ _ _ (der_25986 v h) (hints_cons _ _ _ (der_25987 v h) (hints_cons _ _ _ (der_25988 v h) (hints_cons _ _ _ (der_25989 v h) (hints_cons _ _ _ (der_25990 v h) (hints_cons _ _ _ (der_25991 v h) (hints_cons _ _ _ (der_25992 v h) (hints_cons _ _ _ (der_25993 v h) (hints_cons _ _ _ (der_25994 v h) (hints_cons _ _ _ (der_25995 v h) (hints_cons _ _ _ (der_25996 v h) (hints_cons _ _ _ (der_25997 v h) (hints_cons _ _ _ (der_25998 v h) (hints_cons _ _ _ (der_25999 v h) (hints_cons _ _ _ (der_26000 v h) (hints_cons _ _ _ (der_26001 v h) (hints_cons _ _ _ (der_26002 v h) (hints_cons _ _ _ (der_26003 v h) (hints_cons _ _ _ (der_26004 v h) (hints_cons _ _ _ (der_26005 v h) (hints_cons _ _ _ (der_26006 v h) (hints_cons _ _ _ (der_26007 v h) (hints_cons _ _ _ (der_26008 v h) (hints_cons _ _ _ (der_26009 v h) (hints_cons _ _ _ (der_26010 v h) (hints_cons _ _ _ (der_26011 v h) (hints_cons _ _ _ (der_26012 v h) (hints_cons _ _ _ (der_26013 v h) (hints_cons _ _ _ (der_26014 v h) (hints_cons _ _ _ (der_26015 v h) (hints_cons _ _ _ (der_26016 v h) (hints_cons _ _ _ (der_26017 v h) (hints_cons _ _ _ (der_26018 v h) (hints_cons _ _ _ (der_26019 v h) (hints_cons _ _ _ (der_26020 v h) (hints_cons _ _ _ (der_26021 v h) (hints_cons _ _ _ (der_26022 v h) (hints_cons _ _ _ (der_26023 v h) (hints_cons _ _ _ (der_26024 v h) (hints_cons _ _ _ (der_26025 v h) (hints_cons _ _ _ (der_26026 v h) (hints_cons _ _ _ (der_26027 v h) (hints_cons _ _ _ (der_26028 v h) (hints_cons _ _ _ (der_26029 v h) (hints_cons _ _ _ (der_26030 v h) (hints_cons _ _ _ (der_26031 v h) (hints_cons _ _ _ (der_26032 v h) (hints_cons _ _ _ (der_26033 v h) (hints_cons _ _ _ (der_26034 v h) (hints_cons _ _ _ (der_26035 v h) (hints_cons _ _ _ (der_26036 v h) (hints_cons _ _ _ (der_26037 v h) (hints_cons _ _ _ (der_26038 v h) (hints_cons _ _ _ (der_26039 v h) (hints_cons _ _ _ (der_26040 v h) (hints_cons _ _ _ (der_26041 v h) (hints_cons _ _ _ (der_26042 v h) (hints_cons _ _ _ (der_26043 v h) (hints_cons _ _ _ (der_26044 v h) (hints_cons _ _ _ (der_26045 v h) (hints_cons _ _ _ (der_26046 v h) (hints_cons _ _ _ (der_26049 v h) (hints_cons _ _ _ (der_26050 v h) (hints_cons _ _ _ (der_26051 v h) (hints_cons _ _ _ (der_26052 v h) (hints_cons _ _ _ (der_26053 v h) (hints_cons _ _ _ (der_26054 v h) (hints_cons _ _ _ (der_26055 v h) (hints_cons _ _ _ (der_26056 v h) (hints_cons _ _ _ (der_26057 v h) (hints_cons _ _ _ (der_26058 v h) (hints_cons _ _ _ (der_26059 v h) (hints_cons _ _ _ (der_26060 v h) (hints_cons _ _ _ (der_26061 v h) (hints_cons _ _ _ (der_26062 v h) (hints_cons _ _ _ (der_26063 v h) (hints_cons _ _ _ (der_26064 v h) (hints_cons _ _ _ (der_26065 v h) (hints_cons _ _ _ (der_26066 v h) (hints_cons _ _ _ (der_26067 v h) (hints_cons _ _ _ (der_26068 v h) (hints_cons _ _ _ (der_26069 v h) (hints_cons _ _ _ (der_26070 v h) (hints_cons _ _ _ (der_26071 v h) (hints_cons _ _ _ (der_26072 v h) (hints_cons _ _ _ (der_26073 v h) (hints_cons _ _ _ (der_26074 v h) (hints_cons _ _ _ (der_26075 v h) (hints_cons _ _ _ (der_26077 v h) (hints_cons _ _ _ (der_26078 v h) (hints_cons _ _ _ (der_26079 v h) (hints_cons _ _ _ (der_26080 v h) (hints_cons _ _ _ (der_26081 v h) (hints_cons _ _ _ (der_26082 v h) (hints_cons _ _ _ (der_26084 v h) (hints_cons _ _ _ (der_26085 v h) (hints_cons _ _ _ (der_26086 v h) (hints_cons _ _ _ (der_26087 v h) (hints_cons _ _ _ (der_26088 v h) (hints_cons _ _ _ (der_26089 v h) (hints_cons _ _ _ (der_26090 v h) (hints_cons _ _ _ (der_26091 v h) (hints_cons _ _ _ (der_26092 v h) (hints_cons _ _ _ (der_26093 v h) (hints_cons _ _ _ (der_26094 v h) (hints_cons _ _ _ (der_26095 v h) (hints_cons _ _ _ (der_26097 v h) (hints_cons _ _ _ (der_26098 v h) (hints_cons _ _ _ (der_26099 v h) (hints_cons _ _ _ (der_26100 v h) (hints_cons _ _ _ (der_26101 v h) (hints_cons _ _ _ (der_26102 v h) (hints_cons _ _ _ (der_26103 v h) (hints_cons _ _ _ (der_26104 v h) (hints_cons _ _ _ (der_26105 v h) (hints_cons _ _ _ (der_26106 v h) (hints_cons _ _ _ (der_26107 v h) (hints_cons _ _ _ (der_26108 v h) (hints_cons _ _ _ (der_26109 v h) (hints_cons _ _ _ (der_26110 v h) (hints_cons _ _ _ (der_26112 v h) (hints_cons _ _ _ (der_26113 v h) (hints_cons _ _ _ (der_26114 v h) (hints_cons _ _ _ (der_26115 v h) (hints_cons _ _ _ (der_26116 v h) (hints_cons _ _ _ (der_26117 v h) (hints_cons _ _ _ (der_26118 v h) (hints_cons _ _ _ (der_26119 v h) (hints_cons _ _ _ (der_26120 v h) (hints_cons _ _ _ (der_26121 v h) (hints_cons _ _ _ (der_26122 v h) (hints_cons _ _ _ (der_26123 v h) (hints_cons _ _ _ (der_26124 v h) (hints_cons _ _ _ (der_26125 v h) (hints_cons _ _ _ (der_26126 v h) (hints_cons _ _ _ (der_26128 v h) (hints_cons _ _ _ (der_26129 v h) (hints_cons _ _ _ (der_26130 v h) (hints_cons _ _ _ (der_26131 v h) (hints_cons _ _ _ (der_26132 v h) (hints_cons _ _ _ (der_26133 v h) (hints_cons _ _ _ (der_26134 v h) (hints_cons _ _ _ (der_26135 v h) (hints_cons _ _ _ (der_26136 v h) (hints_cons _ _ _ (der_26137 v h) (hints_cons _ _ _ (der_26138 v h) (hints_cons _ _ _ (der_26139 v h) (hints_cons _ _ _ (der_26140 v h) (hints_cons _ _ _ (der_26141 v h) (hints_cons _ _ _ (der_26142 v h) (hints_cons _ _ _ (der_26143 v h) (hints_cons _ _ _ (der_26144 v h) (hints_cons _ _ _ (der_26145 v h) (hints_cons _ _ _ (der_26146 v h) (hints_cons _ _ _ (der_26147 v h) (hints_cons _ _ _ (der_26148 v h) (hints_cons _ _ _ (der_26149 v h) (hints_cons _ _ _ (der_26150 v h) (hints_cons _ _ _ (der_26151 v h) (hints_cons _ _ _ (der_26152 v h) (hints_cons _ _ _ (der_26153 v h) (hints_cons _ _ _ (der_26154 v h) (hints_cons _ _ _ (der_26155 v h) (hints_cons _ _ _ (der_26156 v h) (hints_cons _ _ _ (der_26157 v h) (hints_cons _ _ _ (der_26158 v h) (hints_cons _ _ _ (der_26159 v h) (hints_cons _ _ _ (der_26160 v h) (hints_cons _ _ _ (der_26161 v h) (hints_cons _ _ _ (der_26162 v h) (hints_cons _ _ _ (der_26163 v h) (hints_cons _ _ _ (der_26164 v h) (hints_cons _ _ _ (der_26165 v h) (hints_cons _ _ _ (der_26166 v h) (hints_cons _ _ _ (der_26167 v h) (hints_cons _ _ _ (der_26168 v h) (hints_cons _ _ _ (der_26169 v h) (hints_cons _ _ _ (der_26170 v h) (hints_cons _ _ _ (der_26171 v h) (hints_cons _ _ _ (der_26172 v h) (hints_cons _ _ _ (der_26173 v h) (hints_cons _ _ _ (der_26174 v h) (hints_cons _ _ _ (der_26175 v h) (hints_cons _ _ _ (der_26176 v h) (hints_cons _ _ _ (der_26177 v h) (hints_cons _ _ _ (der_26179 v h) (hints_cons _ _ _ (der_26181 v h) (hints_cons _ _ _ (der_26183 v h) (hints_cons _ _ _ (der_26186 v h) (hints_cons _ _ _ (der_26187 v h) (hints_cons _ _ _ (der_26188 v h) (hints_cons _ _ _ (der_26189 v h) (hints_cons _ _ _ (der_26190 v h) (hints_cons _ _ _ (der_26191 v h) (hints_cons _ _ _ (der_26192 v h) (hints_cons _ _ _ (der_26193 v h) (hints_cons _ _ _ (der_26194 v h) (hints_cons _ _ _ (der_26195 v h) (hints_cons _ _ _ (der_26196 v h) (hints_cons _ _ _ (der_26197 v h) (hints_cons _ _ _ (der_26198 v h) (hints_cons _ _ _ (der_26199 v h) (hints_cons _ _ _ (der_26200 v h) (hints_cons _ _ _ (der_26201 v h) (hints_cons _ _ _ (der_26202 v h) (hints_cons _ _ _ (der_26203 v h) (hints_cons _ _ _ (der_26204 v h) (hints_cons _ _ _ (der_26205 v h) (hints_cons _ _ _ (der_26206 v h) (hints_cons _ _ _ (der_26207 v h) (hints_cons _ _ _ (der_26208 v h) (hints_cons _ _ _ (der_26209 v h) (hints_cons _ _ _ (der_26210 v h) (hints_cons _ _ _ (der_26211 v h) (hints_cons _ _ _ (der_26212 v h) (hints_cons _ _ _ (der_26213 v h) (hints_cons _ _ _ (der_26214 v h) (hints_cons _ _ _ (der_26215 v h) (hints_cons _ _ _ (der_26216 v h) (hints_cons _ _ _ (der_26217 v h) (hints_cons _ _ _ (der_26218 v h) (hints_cons _ _ _ (der_26219 v h) (hints_cons _ _ _ (der_26220 v h) (hints_cons _ _ _ (der_26221 v h) (hints_cons _ _ _ (der_26222 v h) (hints_cons _ _ _ (der_26223 v h) (hints_cons _ _ _ (der_26224 v h) (hints_cons _ _ _ (der_26225 v h) (hints_cons _ _ _ (der_26226 v h) (hints_cons _ _ _ (der_26227 v h) (hints_cons _ _ _ (der_26228 v h) (hints_cons _ _ _ (der_26229 v h) (hints_cons _ _ _ (der_26230 v h) (hints_cons _ _ _ (der_26231 v h) (hints_cons _ _ _ (der_26232 v h) (hints_cons _ _ _ (der_26233 v h) (hints_cons _ _ _ (der_26234 v h) (hints_cons _ _ _ (der_26235 v h) (hints_cons _ _ _ (der_26236 v h) (hints_cons _ _ _ (der_26237 v h) (hints_cons _ _ _ (der_26238 v h) (hints_cons _ _ _ (der_26239 v h) (hints_cons _ _ _ (der_26240 v h) (hints_cons _ _ _ (der_26241 v h) (hints_cons _ _ _ (der_26242 v h) (hints_cons _ _ _ (der_26243 v h) (hints_cons _ _ _ (der_26244 v h) (hints_cons _ _ _ (der_26245 v h) (hints_cons _ _ _ (der_26246 v h) (hints_cons _ _ _ (der_26247 v h) (hints_cons _ _ _ (der_26248 v h) (hints_cons _ _ _ (der_26249 v h) (hints_cons _ _ _ (der_26250 v h) (hints_cons _ _ _ (der_26251 v h) (hints_cons _ _ _ (der_26252 v h) (hints_cons _ _ _ (der_26253 v h) (hints_cons _ _ _ (der_26254 v h) (hints_cons _ _ _ (der_26255 v h) (hints_cons _ _ _ (der_26256 v h) (hints_cons _ _ _ (der_26257 v h) (hints_cons _ _ _ (der_26258 v h) (hints_cons _ _ _ (der_26259 v h) (hints_cons _ _ _ (der_26260 v h) (hints_cons _ _ _ (der_26261 v h) (hints_cons _ _ _ (der_26262 v h) (hints_cons _ _ _ (der_26263 v h) (hints_cons _ _ _ (der_26264 v h) (hints_cons _ _ _ (der_26265 v h) (hints_cons _ _ _ (der_26266 v h) (hints_cons _ _ _ (der_26267 v h) (hints_cons _ _ _ (der_26268 v h) (hints_cons _ _ _ (der_26269 v h) (hints_cons _ _ _ (der_26270 v h) (hints_cons _ _ _ (der_26271 v h) (hints_cons _ _ _ (der_26272 v h) (hints_cons _ _ _ (der_26273 v h) (hints_cons _ _ _ (der_26274 v h) (by intro d hd; cases hd)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def prefix007 := prefix006 ++ chunk007
theorem prefix_sound007 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : ∀ c ∈ prefix007, CNF.Holds (v ∘ decodeVar) c := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact prefix_sound006 v h c hc
  · exact chunk_sound007 v h c hc
end Percolation.NReplay
