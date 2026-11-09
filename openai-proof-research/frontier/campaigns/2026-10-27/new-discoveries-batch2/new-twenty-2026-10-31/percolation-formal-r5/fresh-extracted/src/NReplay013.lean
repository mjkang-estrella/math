import NReplay012
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_28855 : CNF.NClause := [(50,false),(19,true),(63,true),(71,false),(74,true),(77,true),(90,false)]
theorem der_28855 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28855 :=
  CNF.rup_sound cl_28855 [cl_6460,cl_28826] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6460 v h) (hints_cons _ _ _ (der_28826 v h) (by intro d hd; cases hd)))
def cl_28856 : CNF.NClause := [(50,false),(19,false),(63,false),(71,true),(74,true),(77,true),(90,false)]
theorem der_28856 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28856 :=
  CNF.rup_sound cl_28856 [cl_6461,cl_28828] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6461 v h) (hints_cons _ _ _ (der_28828 v h) (by intro d hd; cases hd)))
def cl_28857 : CNF.NClause := [(50,false),(74,true),(19,true),(63,false),(71,true),(77,true),(90,false)]
theorem der_28857 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28857 :=
  CNF.rup_sound cl_28857 [cl_6462,cl_28828] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6462 v h) (hints_cons _ _ _ (der_28828 v h) (by intro d hd; cases hd)))
def cl_28858 : CNF.NClause := [(50,false),(74,true),(19,false),(63,true),(71,true),(77,true),(90,false)]
theorem der_28858 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28858 :=
  CNF.rup_sound cl_28858 [cl_6463,cl_28829] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6463 v h) (hints_cons _ _ _ (der_28829 v h) (by intro d hd; cases hd)))
def cl_28859 : CNF.NClause := [(50,false),(74,true),(19,true),(63,true),(71,true),(77,true),(90,false)]
theorem der_28859 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28859 :=
  CNF.rup_sound cl_28859 [cl_6464,cl_28830] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6464 v h) (hints_cons _ _ _ (der_28830 v h) (by intro d hd; cases hd)))
def cl_28860 : CNF.NClause := [(50,false),(90,true),(63,false),(71,false),(77,false),(85,false),(74,false)]
theorem der_28860 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28860 :=
  CNF.rup_sound cl_28860 [cl_6465,cl_26755] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6465 v h) (hints_cons _ _ _ (der_26755 v h) (by intro d hd; cases hd)))
def cl_28861 : CNF.NClause := [(50,false),(63,true),(19,false),(71,false),(74,false),(77,false),(85,false)]
theorem der_28861 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28861 :=
  CNF.rup_sound cl_28861 [cl_6467,cl_6403] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6467 v h) (hints_cons _ _ _ (inp_6403 v h) (by intro d hd; cases hd)))
def cl_28862 : CNF.NClause := [(50,false),(19,true),(85,false),(71,false),(63,true),(74,false),(77,false)]
theorem der_28862 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28862 :=
  CNF.rup_sound cl_28862 [cl_6468,cl_28807] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6468 v h) (hints_cons _ _ _ (der_28807 v h) (by intro d hd; cases hd)))
def cl_28863 : CNF.NClause := [(50,false),(19,false),(63,false),(74,false),(77,false),(85,false),(71,true)]
theorem der_28863 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28863 :=
  CNF.rup_sound cl_28863 [cl_6469,cl_28808] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6469 v h) (hints_cons _ _ _ (der_28808 v h) (by intro d hd; cases hd)))
def cl_28864 : CNF.NClause := [(50,false),(19,true),(63,false),(74,false),(77,false),(85,false),(71,true)]
theorem der_28864 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28864 :=
  CNF.rup_sound cl_28864 [cl_6470,cl_28808] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6470 v h) (hints_cons _ _ _ (der_28808 v h) (by intro d hd; cases hd)))
def cl_28865 : CNF.NClause := [(50,false),(19,false),(63,true),(74,false),(77,false),(85,false),(71,true)]
theorem der_28865 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28865 :=
  CNF.rup_sound cl_28865 [cl_6471,cl_28809] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6471 v h) (hints_cons _ _ _ (der_28809 v h) (by intro d hd; cases hd)))
def cl_28866 : CNF.NClause := [(50,false),(19,true),(63,true),(74,false),(77,false),(85,false),(71,true)]
theorem der_28866 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28866 :=
  CNF.rup_sound cl_28866 [cl_6472,cl_28810] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6472 v h) (hints_cons _ _ _ (der_28810 v h) (by intro d hd; cases hd)))
def cl_28867 : CNF.NClause := [(50,false),(74,true),(19,false),(63,false),(77,false),(85,false),(71,false)]
theorem der_28867 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28867 :=
  CNF.rup_sound cl_28867 [cl_6473,cl_28811] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6473 v h) (hints_cons _ _ _ (der_28811 v h) (by intro d hd; cases hd)))
def cl_28868 : CNF.NClause := [(50,false),(19,false),(71,false),(74,true),(63,true),(77,false),(85,false)]
theorem der_28868 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28868 :=
  CNF.rup_sound cl_28868 [cl_6475,cl_28825] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6475 v h) (hints_cons _ _ _ (der_28825 v h) (by intro d hd; cases hd)))
def cl_28869 : CNF.NClause := [(50,false),(74,true),(90,true),(71,false),(63,true),(85,false),(77,false)]
theorem der_28869 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28869 :=
  CNF.rup_sound cl_28869 [cl_6476,cl_28868] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6476 v h) (hints_cons _ _ _ (der_28868 v h) (by intro d hd; cases hd)))
def cl_28870 : CNF.NClause := [(50,false),(74,true),(19,false),(63,false),(77,false),(85,false),(90,true)]
theorem der_28870 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28870 :=
  CNF.rup_sound cl_28870 [cl_6477,cl_28867] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6477 v h) (hints_cons _ _ _ (der_28867 v h) (by intro d hd; cases hd)))
def cl_28871 : CNF.NClause := [(50,false),(74,true),(19,true),(63,false),(71,true),(77,false),(85,false)]
theorem der_28871 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28871 :=
  CNF.rup_sound cl_28871 [cl_6478,cl_28815] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6478 v h) (hints_cons _ _ _ (der_28815 v h) (by intro d hd; cases hd)))
def cl_28872 : CNF.NClause := [(50,false),(74,true),(19,false),(63,true),(71,true),(77,false),(85,false)]
theorem der_28872 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28872 :=
  CNF.rup_sound cl_28872 [cl_6479,cl_28817] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6479 v h) (hints_cons _ _ _ (der_28817 v h) (by intro d hd; cases hd)))
def cl_28873 : CNF.NClause := [(50,false),(74,true),(19,true),(63,true),(71,true),(77,false),(85,false)]
theorem der_28873 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28873 :=
  CNF.rup_sound cl_28873 [cl_6480,cl_28817] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6480 v h) (hints_cons _ _ _ (der_28817 v h) (by intro d hd; cases hd)))
def cl_28874 : CNF.NClause := [(50,false),(63,true),(19,false),(71,false),(74,false),(77,true),(85,false)]
theorem der_28874 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28874 :=
  CNF.rup_sound cl_28874 [cl_6483,cl_28818] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6483 v h) (hints_cons _ _ _ (der_28818 v h) (by intro d hd; cases hd)))
def cl_28875 : CNF.NClause := [(50,false),(77,true),(90,true),(74,false),(63,true),(71,false),(85,false)]
theorem der_28875 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28875 :=
  CNF.rup_sound cl_28875 [cl_6484,cl_28874] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6484 v h) (hints_cons _ _ _ (der_28874 v h) (by intro d hd; cases hd)))
def cl_28876 : CNF.NClause := [(50,false),(19,false),(63,false),(71,true),(74,false),(77,true),(85,false)]
theorem der_28876 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28876 :=
  CNF.rup_sound cl_28876 [cl_6485,cl_28820] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6485 v h) (hints_cons _ _ _ (der_28820 v h) (by intro d hd; cases hd)))
def cl_28877 : CNF.NClause := [(50,false),(77,true),(63,false),(74,false),(71,true),(85,false),(90,true)]
theorem der_28877 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28877 :=
  CNF.rup_sound cl_28877 [cl_6486,cl_28876] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6486 v h) (hints_cons _ _ _ (der_28876 v h) (by intro d hd; cases hd)))
def cl_28878 : CNF.NClause := [(50,false),(77,true),(19,false),(63,true),(74,false),(71,true),(85,false)]
theorem der_28878 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28878 :=
  CNF.rup_sound cl_28878 [cl_6487,cl_28823] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6487 v h) (hints_cons _ _ _ (der_28823 v h) (by intro d hd; cases hd)))
def cl_28879 : CNF.NClause := [(50,false),(77,true),(19,true),(63,true),(74,false),(71,true),(85,false)]
theorem der_28879 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28879 :=
  CNF.rup_sound cl_28879 [cl_6488,cl_28823] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6488 v h) (hints_cons _ _ _ (der_28823 v h) (by intro d hd; cases hd)))
def cl_28880 : CNF.NClause := [(50,false),(19,false),(71,false),(63,false),(74,true),(77,true),(85,false)]
theorem der_28880 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28880 :=
  CNF.rup_sound cl_28880 [cl_6489,cl_28853] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6489 v h) (hints_cons _ _ _ (der_28853 v h) (by intro d hd; cases hd)))
def cl_28881 : CNF.NClause := [(50,false),(77,true),(19,false),(71,false),(74,true),(63,true),(85,false)]
theorem der_28881 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28881 :=
  CNF.rup_sound cl_28881 [cl_6491,cl_28825] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6491 v h) (hints_cons _ _ _ (der_28825 v h) (by intro d hd; cases hd)))
def cl_28882 : CNF.NClause := [(50,false),(74,true),(19,true),(71,false),(63,true),(77,true),(85,false)]
theorem der_28882 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28882 :=
  CNF.rup_sound cl_28882 [cl_6492,cl_28826] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6492 v h) (hints_cons _ _ _ (der_28826 v h) (by intro d hd; cases hd)))
def cl_28883 : CNF.NClause := [(50,false),(19,false),(63,false),(71,true),(74,true),(77,true),(85,false)]
theorem der_28883 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28883 :=
  CNF.rup_sound cl_28883 [cl_6493,cl_28828] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6493 v h) (hints_cons _ _ _ (der_28828 v h) (by intro d hd; cases hd)))
def cl_28884 : CNF.NClause := [(50,false),(74,true),(19,true),(63,false),(71,true),(77,true),(85,false)]
theorem der_28884 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28884 :=
  CNF.rup_sound cl_28884 [cl_6494,cl_28828] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6494 v h) (hints_cons _ _ _ (der_28828 v h) (by intro d hd; cases hd)))
def cl_28885 : CNF.NClause := [(50,false),(74,true),(19,false),(63,true),(71,true),(85,false),(90,true)]
theorem der_28885 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28885 :=
  CNF.rup_sound cl_28885 [cl_6495,cl_28872] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6495 v h) (hints_cons _ _ _ (der_28872 v h) (by intro d hd; cases hd)))
def cl_28886 : CNF.NClause := [(50,false),(74,true),(19,true),(71,true),(77,true),(85,false),(90,true)]
theorem der_28886 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28886 :=
  CNF.rup_sound cl_28886 [cl_6496,cl_28884] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6496 v h) (hints_cons _ _ _ (der_28884 v h) (by intro d hd; cases hd)))
def cl_28887 : CNF.NClause := [(50,false),(85,true),(19,false),(71,false),(74,false),(77,false),(63,false)]
theorem der_28887 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28887 :=
  CNF.rup_sound cl_28887 [cl_6497,cl_28831] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6497 v h) (hints_cons _ _ _ (der_28831 v h) (by intro d hd; cases hd)))
def cl_28888 : CNF.NClause := [(50,false),(19,true),(63,false),(85,true),(77,false),(71,false),(74,false)]
theorem der_28888 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28888 :=
  CNF.rup_sound cl_28888 [cl_6498,cl_28831] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6498 v h) (hints_cons _ _ _ (der_28831 v h) (by intro d hd; cases hd)))
def cl_28889 : CNF.NClause := [(50,false),(63,true),(19,false),(71,false),(74,false),(77,false),(85,true)]
theorem der_28889 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28889 :=
  CNF.rup_sound cl_28889 [cl_6499,cl_28832] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6499 v h) (hints_cons _ _ _ (der_28832 v h) (by intro d hd; cases hd)))
def cl_28890 : CNF.NClause := [(50,false),(19,true),(63,true),(74,false),(77,false),(71,false),(85,true)]
theorem der_28890 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28890 :=
  CNF.rup_sound cl_28890 [cl_6500,cl_28833] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6500 v h) (hints_cons _ _ _ (der_28833 v h) (by intro d hd; cases hd)))
def cl_28891 : CNF.NClause := [(50,false),(19,false),(63,false),(74,false),(77,false),(85,true),(71,true)]
theorem der_28891 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28891 :=
  CNF.rup_sound cl_28891 [cl_6501,cl_28834] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6501 v h) (hints_cons _ _ _ (der_28834 v h) (by intro d hd; cases hd)))
def cl_28892 : CNF.NClause := [(50,false),(90,true),(63,false),(74,false),(77,false),(85,true),(71,true)]
theorem der_28892 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28892 :=
  CNF.rup_sound cl_28892 [cl_6502,cl_28891] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6502 v h) (hints_cons _ _ _ (der_28891 v h) (by intro d hd; cases hd)))
def cl_28893 : CNF.NClause := [(50,false),(19,false),(63,true),(74,false),(77,false),(71,true),(85,true)]
theorem der_28893 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28893 :=
  CNF.rup_sound cl_28893 [cl_6503,cl_28837] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6503 v h) (hints_cons _ _ _ (der_28837 v h) (by intro d hd; cases hd)))
def cl_28894 : CNF.NClause := [(50,false),(19,true),(63,true),(74,false),(77,false),(71,true),(85,true)]
theorem der_28894 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28894 :=
  CNF.rup_sound cl_28894 [cl_6504,cl_28837] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6504 v h) (hints_cons _ _ _ (der_28837 v h) (by intro d hd; cases hd)))
def cl_28895 : CNF.NClause := [(50,false),(74,true),(19,false),(71,false),(63,false),(77,false),(90,true)]
theorem der_28895 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28895 :=
  CNF.rup_sound cl_28895 [cl_6505,cl_28867] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6505 v h) (hints_cons _ _ _ (der_28867 v h) (by intro d hd; cases hd)))
def cl_28896 : CNF.NClause := [(50,false),(19,false),(71,false),(74,true),(63,true),(77,false),(85,true)]
theorem der_28896 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28896 :=
  CNF.rup_sound cl_28896 [cl_6507,cl_28839] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6507 v h) (hints_cons _ _ _ (der_28839 v h) (by intro d hd; cases hd)))
def cl_28897 : CNF.NClause := [(50,false),(19,true),(63,true),(71,false),(74,true),(77,false),(85,true)]
theorem der_28897 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28897 :=
  CNF.rup_sound cl_28897 [cl_6508,cl_28840] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6508 v h) (hints_cons _ _ _ (der_28840 v h) (by intro d hd; cases hd)))
def cl_28898 : CNF.NClause := [(50,false),(74,true),(19,false),(63,false),(71,true),(77,false),(85,true)]
theorem der_28898 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28898 :=
  CNF.rup_sound cl_28898 [cl_6509,cl_28842] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6509 v h) (hints_cons _ _ _ (der_28842 v h) (by intro d hd; cases hd)))
def cl_28899 : CNF.NClause := [(50,false),(74,true),(19,true),(63,false),(71,true),(77,false),(85,true)]
theorem der_28899 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28899 :=
  CNF.rup_sound cl_28899 [cl_6510,cl_28842] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6510 v h) (hints_cons _ _ _ (der_28842 v h) (by intro d hd; cases hd)))
def cl_28900 : CNF.NClause := [(50,false),(74,true),(19,false),(63,true),(71,true),(77,false),(90,true)]
theorem der_28900 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28900 :=
  CNF.rup_sound cl_28900 [cl_6511,cl_28872] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6511 v h) (hints_cons _ _ _ (der_28872 v h) (by intro d hd; cases hd)))
def cl_28901 : CNF.NClause := [(50,false),(74,true),(63,true),(71,true),(77,false),(85,true),(90,true)]
theorem der_28901 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28901 :=
  CNF.rup_sound cl_28901 [cl_6512,cl_28900] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6512 v h) (hints_cons _ _ _ (der_28900 v h) (by intro d hd; cases hd)))
def cl_28903 : CNF.NClause := [(50,false),(19,true),(63,false),(74,false),(90,true),(71,false),(85,true)]
theorem der_28903 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28903 :=
  CNF.rup_sound cl_28903 [cl_6514,cl_28888] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6514 v h) (hints_cons _ _ _ (der_28888 v h) (by intro d hd; cases hd)))
def cl_28904 : CNF.NClause := [(50,false),(63,true),(19,false),(71,false),(74,false),(85,true),(90,true)]
theorem der_28904 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28904 :=
  CNF.rup_sound cl_28904 [cl_6515,cl_28889] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6515 v h) (hints_cons _ _ _ (der_28889 v h) (by intro d hd; cases hd)))
def cl_28905 : CNF.NClause := [(50,false),(77,true),(19,true),(90,true),(74,false),(63,true),(71,false)]
theorem der_28905 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28905 :=
  CNF.rup_sound cl_28905 [cl_6516,cl_28875] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6516 v h) (hints_cons _ _ _ (der_28875 v h) (by intro d hd; cases hd)))
def cl_28906 : CNF.NClause := [(50,false),(19,false),(63,false),(71,true),(77,true),(74,false),(85,true)]
theorem der_28906 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28906 :=
  CNF.rup_sound cl_28906 [cl_6517,cl_28849] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6517 v h) (hints_cons _ _ _ (der_28849 v h) (by intro d hd; cases hd)))
def cl_28907 : CNF.NClause := [(50,false),(77,true),(63,false),(74,false),(71,true),(85,true),(90,true)]
theorem der_28907 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28907 :=
  CNF.rup_sound cl_28907 [cl_6518,cl_28906] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6518 v h) (hints_cons _ _ _ (der_28906 v h) (by intro d hd; cases hd)))
def cl_28908 : CNF.NClause := [(50,false),(77,true),(19,false),(63,true),(74,false),(71,true),(90,true)]
theorem der_28908 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28908 :=
  CNF.rup_sound cl_28908 [cl_6519,cl_28878] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6519 v h) (hints_cons _ _ _ (der_28878 v h) (by intro d hd; cases hd)))
def cl_28909 : CNF.NClause := [(50,false),(19,true),(63,true),(74,false),(71,true),(85,true),(90,true)]
theorem der_28909 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28909 :=
  CNF.rup_sound cl_28909 [cl_6520,cl_28894] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6520 v h) (hints_cons _ _ _ (der_28894 v h) (by intro d hd; cases hd)))
def cl_28910 : CNF.NClause := [(50,false),(85,true),(19,false),(71,false),(63,false),(74,true),(77,true)]
theorem der_28910 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28910 :=
  CNF.rup_sound cl_28910 [cl_6521,cl_28853] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6521 v h) (hints_cons _ _ _ (der_28853 v h) (by intro d hd; cases hd)))
def cl_28911 : CNF.NClause := [(50,false),(85,true),(19,false),(71,false),(74,true),(63,true),(90,true)]
theorem der_28911 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28911 :=
  CNF.rup_sound cl_28911 [cl_6523,cl_28896] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6523 v h) (hints_cons _ _ _ (der_28896 v h) (by intro d hd; cases hd)))
def cl_28912 : CNF.NClause := [(50,false),(85,true),(63,true),(71,false),(74,true),(77,true),(90,true)]
theorem der_28912 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28912 :=
  CNF.rup_sound cl_28912 [cl_6524,cl_28911] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6524 v h) (hints_cons _ _ _ (der_28911 v h) (by intro d hd; cases hd)))
def cl_28914 : CNF.NClause := [(50,false),(74,true),(19,true),(63,false),(71,true),(77,true),(90,true)]
theorem der_28914 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28914 :=
  CNF.rup_sound cl_28914 [cl_6526,cl_28884] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6526 v h) (hints_cons _ _ _ (der_28884 v h) (by intro d hd; cases hd)))
def cl_28916 : CNF.NClause := [(50,false),(74,true),(19,true),(71,true),(77,true),(85,true),(90,true)]
theorem der_28916 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28916 :=
  CNF.rup_sound cl_28916 [cl_6528,cl_28914] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6528 v h) (hints_cons _ _ _ (der_28914 v h) (by intro d hd; cases hd)))
def cl_28917 : CNF.NClause := [(32,false),(71,false),(1,true),(81,false),(87,false),(86,false),(76,false)]
theorem der_28917 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28917 :=
  CNF.rup_sound cl_28917 [cl_4098,cl_4100] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4098 v h) (hints_cons _ _ _ (inp_4100 v h) (by intro d hd; cases hd)))
def cl_28918 : CNF.NClause := [(32,false),(66,true),(71,false),(76,false),(81,false),(86,false),(87,false)]
theorem der_28918 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28918 :=
  CNF.rup_sound cl_28918 [cl_4099,cl_28917] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4099 v h) (hints_cons _ _ _ (der_28917 v h) (by intro d hd; cases hd)))
def cl_28919 : CNF.NClause := [(32,false),(1,true),(66,false),(81,false),(86,false),(76,false),(87,false)]
theorem der_28919 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28919 :=
  CNF.rup_sound cl_28919 [cl_4102,cl_28917] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4102 v h) (hints_cons _ _ _ (der_28917 v h) (by intro d hd; cases hd)))
def cl_28920 : CNF.NClause := [(32,false),(66,true),(1,false),(76,false),(81,false),(86,false),(87,false)]
theorem der_28920 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28920 :=
  CNF.rup_sound cl_28920 [cl_4103,cl_28918] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4103 v h) (hints_cons _ _ _ (der_28918 v h) (by intro d hd; cases hd)))
def cl_28921 : CNF.NClause := [(32,false),(66,true),(1,true),(76,false),(81,false),(86,false),(87,false)]
theorem der_28921 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28921 :=
  CNF.rup_sound cl_28921 [cl_4104,cl_28917] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4104 v h) (hints_cons _ _ _ (der_28917 v h) (by intro d hd; cases hd)))
def cl_28922 : CNF.NClause := [(32,false),(71,false),(1,true),(86,false),(66,false),(81,false),(87,false)]
theorem der_28922 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28922 :=
  CNF.rup_sound cl_28922 [cl_4106,cl_28917] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4106 v h) (hints_cons _ _ _ (der_28917 v h) (by intro d hd; cases hd)))
def cl_28923 : CNF.NClause := [(32,false),(66,true),(1,false),(71,false),(81,false),(86,false),(87,false)]
theorem der_28923 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28923 :=
  CNF.rup_sound cl_28923 [cl_4107,cl_28918] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4107 v h) (hints_cons _ _ _ (der_28918 v h) (by intro d hd; cases hd)))
def cl_28924 : CNF.NClause := [(32,false),(66,true),(1,true),(81,false),(71,false),(86,false),(87,false)]
theorem der_28924 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28924 :=
  CNF.rup_sound cl_28924 [cl_4108,cl_28917] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4108 v h) (hints_cons _ _ _ (der_28917 v h) (by intro d hd; cases hd)))
def cl_28925 : CNF.NClause := [(32,false),(81,false),(1,false),(66,false),(76,true),(86,false),(87,false)]
theorem der_28925 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28925 :=
  CNF.rup_sound cl_28925 [cl_4109,cl_4105] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4109 v h) (hints_cons _ _ _ (inp_4105 v h) (by intro d hd; cases hd)))
def cl_28926 : CNF.NClause := [(32,false),(71,true),(66,false),(86,false),(76,true),(81,false),(87,false)]
theorem der_28926 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28926 :=
  CNF.rup_sound cl_28926 [cl_4110,cl_28925] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4110 v h) (hints_cons _ _ _ (der_28925 v h) (by intro d hd; cases hd)))
def cl_28927 : CNF.NClause := [(32,false),(1,false),(71,true),(76,true),(81,false),(86,false),(87,false)]
theorem der_28927 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28927 :=
  CNF.rup_sound cl_28927 [cl_4111,cl_28926] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4111 v h) (hints_cons _ _ _ (der_28926 v h) (by intro d hd; cases hd)))
def cl_28928 : CNF.NClause := [(32,false),(81,false),(1,true),(66,true),(76,true),(86,false),(87,false)]
theorem der_28928 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28928 :=
  CNF.rup_sound cl_28928 [cl_4112,cl_28924] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4112 v h) (hints_cons _ _ _ (der_28924 v h) (by intro d hd; cases hd)))
def cl_28929 : CNF.NClause := [(32,false),(1,true),(66,false),(71,false),(76,false),(86,false),(87,false)]
theorem der_28929 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28929 :=
  CNF.rup_sound cl_28929 [cl_4114,cl_28917] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4114 v h) (hints_cons _ _ _ (der_28917 v h) (by intro d hd; cases hd)))
def cl_28930 : CNF.NClause := [(32,false),(1,false),(71,false),(76,false),(66,true),(86,false),(87,false)]
theorem der_28930 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28930 :=
  CNF.rup_sound cl_28930 [cl_4115,cl_28918] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4115 v h) (hints_cons _ _ _ (der_28918 v h) (by intro d hd; cases hd)))
def cl_28931 : CNF.NClause := [(32,false),(1,true),(66,true),(76,false),(71,false),(86,false),(87,false)]
theorem der_28931 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28931 :=
  CNF.rup_sound cl_28931 [cl_4116,cl_28917] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4116 v h) (hints_cons _ _ _ (der_28917 v h) (by intro d hd; cases hd)))
def cl_28932 : CNF.NClause := [(32,false),(86,false),(1,false),(66,false),(76,false),(81,true),(87,false)]
theorem der_28932 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28932 :=
  CNF.rup_sound cl_28932 [cl_4117,cl_4113] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4117 v h) (hints_cons _ _ _ (inp_4113 v h) (by intro d hd; cases hd)))
def cl_28933 : CNF.NClause := [(32,false),(81,true),(66,false),(71,true),(76,false),(86,false),(87,false)]
theorem der_28933 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28933 :=
  CNF.rup_sound cl_28933 [cl_4118,cl_28932] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4118 v h) (hints_cons _ _ _ (der_28932 v h) (by intro d hd; cases hd)))
def cl_28934 : CNF.NClause := [(32,false),(1,false),(71,true),(76,false),(81,true),(86,false),(87,false)]
theorem der_28934 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28934 :=
  CNF.rup_sound cl_28934 [cl_4119,cl_28932] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4119 v h) (hints_cons _ _ _ (der_28932 v h) (by intro d hd; cases hd)))
def cl_28935 : CNF.NClause := [(32,false),(86,false),(1,true),(71,true),(76,false),(81,true),(87,false)]
theorem der_28935 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28935 :=
  CNF.rup_sound cl_28935 [cl_4120,cl_28933] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4120 v h) (hints_cons _ _ _ (der_28933 v h) (by intro d hd; cases hd)))
def cl_28936 : CNF.NClause := [(32,false),(1,false),(66,false),(71,false),(76,true),(86,false),(87,false)]
theorem der_28936 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28936 :=
  CNF.rup_sound cl_28936 [cl_4121,cl_4105] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4121 v h) (hints_cons _ _ _ (inp_4105 v h) (by intro d hd; cases hd)))
def cl_28937 : CNF.NClause := [(32,false),(81,true),(66,false),(71,false),(76,true),(86,false),(87,false)]
theorem der_28937 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28937 :=
  CNF.rup_sound cl_28937 [cl_4122,cl_28936] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4122 v h) (hints_cons _ _ _ (der_28936 v h) (by intro d hd; cases hd)))
def cl_28939 : CNF.NClause := [(32,false),(1,true),(66,true),(71,false),(76,true),(86,false),(87,false)]
theorem der_28939 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28939 :=
  CNF.rup_sound cl_28939 [cl_4124,cl_28924] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4124 v h) (hints_cons _ _ _ (der_28924 v h) (by intro d hd; cases hd)))
def cl_28940 : CNF.NClause := [(32,false),(1,false),(66,false),(76,true),(71,true),(86,false),(87,false)]
theorem der_28940 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28940 :=
  CNF.rup_sound cl_28940 [cl_4125,cl_28926] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4125 v h) (hints_cons _ _ _ (der_28926 v h) (by intro d hd; cases hd)))
def cl_28941 : CNF.NClause := [(32,false),(1,true),(66,false),(76,true),(71,true),(86,false),(87,false)]
theorem der_28941 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28941 :=
  CNF.rup_sound cl_28941 [cl_4126,cl_28926] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4126 v h) (hints_cons _ _ _ (der_28926 v h) (by intro d hd; cases hd)))
def cl_28942 : CNF.NClause := [(32,false),(1,false),(71,true),(76,true),(81,true),(86,false),(87,false)]
theorem der_28942 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28942 :=
  CNF.rup_sound cl_28942 [cl_4127,cl_28940] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4127 v h) (hints_cons _ _ _ (der_28940 v h) (by intro d hd; cases hd)))
def cl_28943 : CNF.NClause := [(32,false),(81,true),(66,true),(76,true),(71,true),(86,false),(87,false)]
theorem der_28943 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28943 :=
  CNF.rup_sound cl_28943 [cl_4128,cl_28942] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4128 v h) (hints_cons _ _ _ (der_28942 v h) (by intro d hd; cases hd)))
def cl_28944 : CNF.NClause := [(32,false),(71,false),(1,true),(66,false),(81,false),(76,false),(87,false)]
theorem der_28944 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28944 :=
  CNF.rup_sound cl_28944 [cl_4130,cl_28917] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4130 v h) (hints_cons _ _ _ (der_28917 v h) (by intro d hd; cases hd)))
def cl_28945 : CNF.NClause := [(32,false),(66,true),(1,false),(71,false),(76,false),(81,false),(87,false)]
theorem der_28945 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28945 :=
  CNF.rup_sound cl_28945 [cl_4131,cl_28918] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4131 v h) (hints_cons _ _ _ (der_28918 v h) (by intro d hd; cases hd)))
def cl_28946 : CNF.NClause := [(32,false),(1,true),(66,true),(76,false),(81,false),(71,false),(87,false)]
theorem der_28946 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28946 :=
  CNF.rup_sound cl_28946 [cl_4132,cl_28917] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4132 v h) (hints_cons _ _ _ (der_28917 v h) (by intro d hd; cases hd)))
def cl_28947 : CNF.NClause := [(32,false),(1,false),(66,false),(71,true),(76,false),(81,false),(87,false)]
theorem der_28947 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28947 :=
  CNF.rup_sound cl_28947 [cl_4133,cl_4101] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4133 v h) (hints_cons _ _ _ (inp_4101 v h) (by intro d hd; cases hd)))
def cl_28948 : CNF.NClause := [(32,false),(71,true),(66,false),(86,true),(76,false),(81,false),(87,false)]
theorem der_28948 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28948 :=
  CNF.rup_sound cl_28948 [cl_4134,cl_28947] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4134 v h) (hints_cons _ _ _ (der_28947 v h) (by intro d hd; cases hd)))
def cl_28949 : CNF.NClause := [(32,false),(66,true),(1,false),(76,false),(81,false),(86,true),(87,false)]
theorem der_28949 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28949 :=
  CNF.rup_sound cl_28949 [cl_4135,cl_28945] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4135 v h) (hints_cons _ _ _ (der_28945 v h) (by intro d hd; cases hd)))
def cl_28950 : CNF.NClause := [(32,false),(76,false),(1,true),(71,true),(81,false),(86,true),(87,false)]
theorem der_28950 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28950 :=
  CNF.rup_sound cl_28950 [cl_4136,cl_28948] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4136 v h) (hints_cons _ _ _ (der_28948 v h) (by intro d hd; cases hd)))
def cl_28951 : CNF.NClause := [(32,false),(1,false),(66,false),(71,false),(76,true),(81,false),(87,false)]
theorem der_28951 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28951 :=
  CNF.rup_sound cl_28951 [cl_4137,cl_4105] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4137 v h) (hints_cons _ _ _ (inp_4105 v h) (by intro d hd; cases hd)))
def cl_28952 : CNF.NClause := [(32,false),(71,false),(66,false),(81,false),(86,true),(76,true),(87,false)]
theorem der_28952 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28952 :=
  CNF.rup_sound cl_28952 [cl_4138,cl_28951] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4138 v h) (hints_cons _ _ _ (der_28951 v h) (by intro d hd; cases hd)))
def cl_28953 : CNF.NClause := [(32,false),(66,true),(1,false),(71,false),(81,false),(86,true),(87,false)]
theorem der_28953 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28953 :=
  CNF.rup_sound cl_28953 [cl_4139,cl_28945] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4139 v h) (hints_cons _ _ _ (der_28945 v h) (by intro d hd; cases hd)))
def cl_28954 : CNF.NClause := [(32,false),(1,true),(66,true),(71,false),(76,true),(81,false),(87,false)]
theorem der_28954 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28954 :=
  CNF.rup_sound cl_28954 [cl_4140,cl_28924] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4140 v h) (hints_cons _ _ _ (der_28924 v h) (by intro d hd; cases hd)))
def cl_28955 : CNF.NClause := [(32,false),(81,false),(1,false),(66,false),(76,true),(71,true),(87,false)]
theorem der_28955 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28955 :=
  CNF.rup_sound cl_28955 [cl_4141,cl_28926] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4141 v h) (hints_cons _ _ _ (der_28926 v h) (by intro d hd; cases hd)))
def cl_28956 : CNF.NClause := [(32,false),(71,true),(1,true),(66,false),(76,true),(81,false),(87,false)]
theorem der_28956 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28956 :=
  CNF.rup_sound cl_28956 [cl_4142,cl_28926] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4142 v h) (hints_cons _ _ _ (der_28926 v h) (by intro d hd; cases hd)))
def cl_28957 : CNF.NClause := [(32,false),(66,true),(1,false),(71,true),(76,true),(81,false),(87,false)]
theorem der_28957 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28957 :=
  CNF.rup_sound cl_28957 [cl_4143,cl_28927] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4143 v h) (hints_cons _ _ _ (der_28927 v h) (by intro d hd; cases hd)))
def cl_28958 : CNF.NClause := [(32,false),(81,false),(66,true),(76,true),(71,true),(86,true),(87,false)]
theorem der_28958 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28958 :=
  CNF.rup_sound cl_28958 [cl_4144,cl_28957] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4144 v h) (hints_cons _ _ _ (der_28957 v h) (by intro d hd; cases hd)))
def cl_28959 : CNF.NClause := [(32,false),(81,true),(1,false),(66,false),(71,false),(76,false),(87,false)]
theorem der_28959 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28959 :=
  CNF.rup_sound cl_28959 [cl_4145,cl_4113] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4145 v h) (hints_cons _ _ _ (inp_4113 v h) (by intro d hd; cases hd)))
def cl_28960 : CNF.NClause := [(32,false),(81,true),(66,false),(71,false),(76,false),(86,true),(87,false)]
theorem der_28960 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28960 :=
  CNF.rup_sound cl_28960 [cl_4146,cl_28959] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4146 v h) (hints_cons _ _ _ (der_28959 v h) (by intro d hd; cases hd)))
def cl_28961 : CNF.NClause := [(32,false),(1,false),(71,false),(76,false),(66,true),(86,true),(87,false)]
theorem der_28961 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28961 :=
  CNF.rup_sound cl_28961 [cl_4147,cl_28945] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4147 v h) (hints_cons _ _ _ (der_28945 v h) (by intro d hd; cases hd)))
def cl_28962 : CNF.NClause := [(32,false),(81,true),(66,true),(76,false),(71,false),(86,true),(87,false)]
theorem der_28962 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28962 :=
  CNF.rup_sound cl_28962 [cl_4148,cl_28961] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4148 v h) (hints_cons _ _ _ (der_28961 v h) (by intro d hd; cases hd)))
def cl_28963 : CNF.NClause := [(32,false),(81,true),(1,false),(66,false),(71,true),(76,false),(87,false)]
theorem der_28963 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28963 :=
  CNF.rup_sound cl_28963 [cl_4149,cl_28932] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4149 v h) (hints_cons _ _ _ (der_28932 v h) (by intro d hd; cases hd)))
def cl_28964 : CNF.NClause := [(32,false),(81,true),(1,true),(66,false),(71,true),(76,false),(87,false)]
theorem der_28964 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28964 :=
  CNF.rup_sound cl_28964 [cl_4150,cl_28933] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4150 v h) (hints_cons _ _ _ (der_28933 v h) (by intro d hd; cases hd)))
def cl_28966 : CNF.NClause := [(32,false),(81,true),(1,true),(66,true),(71,true),(76,false),(87,false)]
theorem der_28966 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28966 :=
  CNF.rup_sound cl_28966 [cl_4152,cl_28935] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4152 v h) (hints_cons _ _ _ (der_28935 v h) (by intro d hd; cases hd)))
def cl_28967 : CNF.NClause := [(32,false),(81,true),(1,false),(66,false),(71,false),(76,true),(87,false)]
theorem der_28967 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28967 :=
  CNF.rup_sound cl_28967 [cl_4153,cl_28937] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4153 v h) (hints_cons _ _ _ (der_28937 v h) (by intro d hd; cases hd)))
def cl_28968 : CNF.NClause := [(32,false),(81,true),(1,true),(66,false),(71,false),(76,true),(87,false)]
theorem der_28968 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28968 :=
  CNF.rup_sound cl_28968 [cl_4154,cl_28937] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4154 v h) (hints_cons _ _ _ (der_28937 v h) (by intro d hd; cases hd)))
def cl_28971 : CNF.NClause := [(32,false),(81,true),(1,false),(66,false),(76,true),(71,true),(87,false)]
theorem der_28971 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28971 :=
  CNF.rup_sound cl_28971 [cl_4157,cl_28940] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4157 v h) (hints_cons _ _ _ (der_28940 v h) (by intro d hd; cases hd)))
def cl_28972 : CNF.NClause := [(32,false),(81,true),(66,false),(76,true),(71,true),(86,true),(87,false)]
theorem der_28972 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28972 :=
  CNF.rup_sound cl_28972 [cl_4158,cl_28971] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4158 v h) (hints_cons _ _ _ (der_28971 v h) (by intro d hd; cases hd)))
def cl_28973 : CNF.NClause := [(32,false),(66,true),(1,false),(71,true),(76,true),(81,true),(87,false)]
theorem der_28973 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28973 :=
  CNF.rup_sound cl_28973 [cl_4159,cl_28943] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4159 v h) (hints_cons _ _ _ (der_28943 v h) (by intro d hd; cases hd)))
def cl_28974 : CNF.NClause := [(32,false),(81,true),(1,true),(66,true),(76,true),(71,true),(87,false)]
theorem der_28974 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28974 :=
  CNF.rup_sound cl_28974 [cl_4160,cl_28943] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4160 v h) (hints_cons _ _ _ (der_28943 v h) (by intro d hd; cases hd)))
def cl_28975 : CNF.NClause := [(32,false),(86,false),(1,true),(76,false),(81,false),(71,false),(66,false)]
theorem der_28975 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28975 :=
  CNF.rup_sound cl_28975 [cl_4162,cl_28917] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4162 v h) (hints_cons _ _ _ (der_28917 v h) (by intro d hd; cases hd)))
def cl_28976 : CNF.NClause := [(32,false),(66,true),(1,false),(71,false),(76,false),(81,false),(86,false)]
theorem der_28976 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28976 :=
  CNF.rup_sound cl_28976 [cl_4163,cl_28918] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4163 v h) (hints_cons _ _ _ (der_28918 v h) (by intro d hd; cases hd)))
def cl_28977 : CNF.NClause := [(32,false),(66,true),(1,true),(81,false),(76,false),(86,false),(71,false)]
theorem der_28977 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28977 :=
  CNF.rup_sound cl_28977 [cl_4164,cl_28917] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4164 v h) (hints_cons _ _ _ (der_28917 v h) (by intro d hd; cases hd)))
def cl_28978 : CNF.NClause := [(32,false),(86,false),(1,false),(81,false),(66,false),(76,false),(87,true)]
theorem der_28978 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28978 :=
  CNF.rup_sound cl_28978 [cl_4165,cl_4161] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4165 v h) (hints_cons _ _ _ (inp_4161 v h) (by intro d hd; cases hd)))
def cl_28979 : CNF.NClause := [(32,false),(81,false),(1,true),(86,false),(66,false),(76,false),(71,true)]
theorem der_28979 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28979 :=
  CNF.rup_sound cl_28979 [cl_4166,cl_28919] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4166 v h) (hints_cons _ _ _ (der_28919 v h) (by intro d hd; cases hd)))
def cl_28980 : CNF.NClause := [(32,false),(66,true),(1,false),(71,true),(76,false),(81,false),(86,false)]
theorem der_28980 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28980 :=
  CNF.rup_sound cl_28980 [cl_4167,cl_28920] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4167 v h) (hints_cons _ _ _ (der_28920 v h) (by intro d hd; cases hd)))
def cl_28981 : CNF.NClause := [(32,false),(66,true),(1,true),(86,false),(71,true),(81,false),(76,false)]
theorem der_28981 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28981 :=
  CNF.rup_sound cl_28981 [cl_4168,cl_28921] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4168 v h) (hints_cons _ _ _ (der_28921 v h) (by intro d hd; cases hd)))
def cl_28982 : CNF.NClause := [(32,false),(66,false),(1,false),(81,false),(71,false),(76,true),(86,false)]
theorem der_28982 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28982 :=
  CNF.rup_sound cl_28982 [cl_4169,cl_4105] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4169 v h) (hints_cons _ _ _ (inp_4105 v h) (by intro d hd; cases hd)))
def cl_28983 : CNF.NClause := [(32,false),(86,false),(1,true),(66,false),(71,false),(87,true),(81,false)]
theorem der_28983 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28983 :=
  CNF.rup_sound cl_28983 [cl_4170,cl_28975] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4170 v h) (hints_cons _ _ _ (der_28975 v h) (by intro d hd; cases hd)))
def cl_28984 : CNF.NClause := [(32,false),(1,false),(71,false),(76,true),(81,false),(86,false),(87,true)]
theorem der_28984 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28984 :=
  CNF.rup_sound cl_28984 [cl_4171,cl_28982] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4171 v h) (hints_cons _ _ _ (der_28982 v h) (by intro d hd; cases hd)))
def cl_28985 : CNF.NClause := [(32,false),(66,true),(1,true),(76,true),(86,false),(71,false),(81,false)]
theorem der_28985 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28985 :=
  CNF.rup_sound cl_28985 [cl_4172,cl_28924] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4172 v h) (hints_cons _ _ _ (der_28924 v h) (by intro d hd; cases hd)))
def cl_28986 : CNF.NClause := [(32,false),(81,false),(1,false),(66,false),(76,true),(71,true),(86,false)]
theorem der_28986 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28986 :=
  CNF.rup_sound cl_28986 [cl_4173,cl_28926] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4173 v h) (hints_cons _ _ _ (der_28926 v h) (by intro d hd; cases hd)))
def cl_28987 : CNF.NClause := [(32,false),(81,false),(1,true),(86,false),(71,true),(66,false),(76,true)]
theorem der_28987 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28987 :=
  CNF.rup_sound cl_28987 [cl_4174,cl_28926] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4174 v h) (hints_cons _ _ _ (der_28926 v h) (by intro d hd; cases hd)))
def cl_28988 : CNF.NClause := [(32,false),(66,true),(1,false),(71,true),(76,true),(81,false),(86,false)]
theorem der_28988 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28988 :=
  CNF.rup_sound cl_28988 [cl_4175,cl_28957] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4175 v h) (hints_cons _ _ _ (der_28957 v h) (by intro d hd; cases hd)))
def cl_28989 : CNF.NClause := [(32,false),(66,true),(1,true),(81,false),(71,true),(86,false),(87,true)]
theorem der_28989 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28989 :=
  CNF.rup_sound cl_28989 [cl_4176,cl_28981] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4176 v h) (hints_cons _ _ _ (der_28981 v h) (by intro d hd; cases hd)))
def cl_28990 : CNF.NClause := [(32,false),(86,false),(1,false),(66,false),(71,false),(76,false),(81,true)]
theorem der_28990 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28990 :=
  CNF.rup_sound cl_28990 [cl_4177,cl_4113] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4177 v h) (hints_cons _ _ _ (inp_4113 v h) (by intro d hd; cases hd)))
def cl_28991 : CNF.NClause := [(32,false),(81,true),(66,false),(71,false),(76,false),(86,false),(87,true)]
theorem der_28991 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28991 :=
  CNF.rup_sound cl_28991 [cl_4178,cl_28990] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4178 v h) (hints_cons _ _ _ (der_28990 v h) (by intro d hd; cases hd)))
def cl_28992 : CNF.NClause := [(32,false),(81,true),(1,false),(71,false),(76,false),(66,true),(86,false)]
theorem der_28992 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28992 :=
  CNF.rup_sound cl_28992 [cl_4179,cl_28930] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4179 v h) (hints_cons _ _ _ (der_28930 v h) (by intro d hd; cases hd)))
def cl_28993 : CNF.NClause := [(32,false),(81,true),(66,true),(71,false),(76,false),(86,false),(87,true)]
theorem der_28993 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28993 :=
  CNF.rup_sound cl_28993 [cl_4180,cl_28992] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4180 v h) (hints_cons _ _ _ (der_28992 v h) (by intro d hd; cases hd)))
def cl_28994 : CNF.NClause := [(32,false),(81,true),(1,false),(66,false),(71,true),(76,false),(86,false)]
theorem der_28994 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28994 :=
  CNF.rup_sound cl_28994 [cl_4181,cl_28932] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4181 v h) (hints_cons _ _ _ (der_28932 v h) (by intro d hd; cases hd)))
def cl_28995 : CNF.NClause := [(32,false),(81,true),(1,true),(66,false),(71,true),(76,false),(86,false)]
theorem der_28995 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28995 :=
  CNF.rup_sound cl_28995 [cl_4182,cl_28933] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4182 v h) (hints_cons _ _ _ (der_28933 v h) (by intro d hd; cases hd)))
def cl_28996 : CNF.NClause := [(32,false),(66,true),(1,false),(76,false),(81,true),(86,false),(87,true)]
theorem der_28996 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28996 :=
  CNF.rup_sound cl_28996 [cl_4183,cl_28992] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4183 v h) (hints_cons _ _ _ (der_28992 v h) (by intro d hd; cases hd)))
def cl_28997 : CNF.NClause := [(32,false),(81,true),(1,true),(66,true),(76,false),(71,true),(86,false)]
theorem der_28997 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28997 :=
  CNF.rup_sound cl_28997 [cl_4184,cl_28935] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4184 v h) (hints_cons _ _ _ (der_28935 v h) (by intro d hd; cases hd)))
def cl_28998 : CNF.NClause := [(32,false),(81,true),(1,false),(66,false),(71,false),(76,true),(86,false)]
theorem der_28998 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28998 :=
  CNF.rup_sound cl_28998 [cl_4185,cl_28937] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4185 v h) (hints_cons _ _ _ (der_28937 v h) (by intro d hd; cases hd)))
def cl_28999 : CNF.NClause := [(32,false),(81,true),(1,true),(66,false),(71,false),(76,true),(86,false)]
theorem der_28999 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28999 :=
  CNF.rup_sound cl_28999 [cl_4186,cl_28937] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4186 v h) (hints_cons _ _ _ (der_28937 v h) (by intro d hd; cases hd)))
def cl_29000 : CNF.NClause := [(32,false),(66,true),(1,false),(71,false),(81,true),(86,false),(87,true)]
theorem der_29000 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29000 :=
  CNF.rup_sound cl_29000 [cl_4187,cl_28992] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4187 v h) (hints_cons _ _ _ (der_28992 v h) (by intro d hd; cases hd)))
def cl_29001 : CNF.NClause := [(32,false),(81,true),(1,true),(66,true),(71,false),(76,true),(86,false)]
theorem der_29001 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29001 :=
  CNF.rup_sound cl_29001 [cl_4188,cl_28939] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4188 v h) (hints_cons _ _ _ (der_28939 v h) (by intro d hd; cases hd)))
def cl_29002 : CNF.NClause := [(32,false),(81,true),(1,false),(66,false),(76,true),(71,true),(86,false)]
theorem der_29002 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29002 :=
  CNF.rup_sound cl_29002 [cl_4189,cl_28940] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4189 v h) (hints_cons _ _ _ (der_28940 v h) (by intro d hd; cases hd)))
def cl_29003 : CNF.NClause := [(32,false),(81,true),(66,false),(76,true),(71,true),(86,false),(87,true)]
theorem der_29003 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29003 :=
  CNF.rup_sound cl_29003 [cl_4190,cl_29002] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4190 v h) (hints_cons _ _ _ (der_29002 v h) (by intro d hd; cases hd)))
def cl_29004 : CNF.NClause := [(32,false),(66,true),(1,false),(71,true),(76,true),(81,true),(86,false)]
theorem der_29004 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29004 :=
  CNF.rup_sound cl_29004 [cl_4191,cl_28943] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4191 v h) (hints_cons _ _ _ (der_28943 v h) (by intro d hd; cases hd)))
def cl_29005 : CNF.NClause := [(32,false),(81,true),(1,true),(66,true),(76,true),(71,true),(86,false)]
theorem der_29005 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29005 :=
  CNF.rup_sound cl_29005 [cl_4192,cl_28943] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4192 v h) (hints_cons _ _ _ (der_28943 v h) (by intro d hd; cases hd)))
def cl_29006 : CNF.NClause := [(32,false),(1,false),(66,false),(71,false),(76,false),(81,false),(87,true)]
theorem der_29006 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29006 :=
  CNF.rup_sound cl_29006 [cl_4193,cl_4161] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4193 v h) (hints_cons _ _ _ (inp_4161 v h) (by intro d hd; cases hd)))
def cl_29007 : CNF.NClause := [(32,false),(81,false),(1,true),(66,false),(71,false),(86,true),(76,false)]
theorem der_29007 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29007 :=
  CNF.rup_sound cl_29007 [cl_4194,cl_28944] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4194 v h) (hints_cons _ _ _ (der_28944 v h) (by intro d hd; cases hd)))
def cl_29008 : CNF.NClause := [(32,false),(66,true),(1,false),(71,false),(76,false),(81,false),(86,true)]
theorem der_29008 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29008 :=
  CNF.rup_sound cl_29008 [cl_4195,cl_28945] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4195 v h) (hints_cons _ _ _ (der_28945 v h) (by intro d hd; cases hd)))
def cl_29009 : CNF.NClause := [(32,false),(66,true),(1,true),(86,true),(71,false),(81,false),(76,false)]
theorem der_29009 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29009 :=
  CNF.rup_sound cl_29009 [cl_4196,cl_28946] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4196 v h) (hints_cons _ _ _ (der_28946 v h) (by intro d hd; cases hd)))
def cl_29010 : CNF.NClause := [(32,false),(86,true),(1,false),(66,false),(71,true),(76,false),(81,false)]
theorem der_29010 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29010 :=
  CNF.rup_sound cl_29010 [cl_4197,cl_28948] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4197 v h) (hints_cons _ _ _ (der_28948 v h) (by intro d hd; cases hd)))
def cl_29011 : CNF.NClause := [(32,false),(71,true),(1,true),(66,false),(86,true),(76,false),(81,false)]
theorem der_29011 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29011 :=
  CNF.rup_sound cl_29011 [cl_4198,cl_28948] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4198 v h) (hints_cons _ _ _ (der_28948 v h) (by intro d hd; cases hd)))
def cl_29012 : CNF.NClause := [(32,false),(66,true),(1,false),(71,true),(76,false),(81,false),(86,true)]
theorem der_29012 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29012 :=
  CNF.rup_sound cl_29012 [cl_4199,cl_28949] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4199 v h) (hints_cons _ _ _ (der_28949 v h) (by intro d hd; cases hd)))
def cl_29013 : CNF.NClause := [(32,false),(71,true),(1,true),(66,true),(76,false),(81,false),(86,true)]
theorem der_29013 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29013 :=
  CNF.rup_sound cl_29013 [cl_4200,cl_28950] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4200 v h) (hints_cons _ _ _ (der_28950 v h) (by intro d hd; cases hd)))
def cl_29014 : CNF.NClause := [(32,false),(86,true),(1,false),(66,false),(71,false),(76,true),(81,false)]
theorem der_29014 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29014 :=
  CNF.rup_sound cl_29014 [cl_4201,cl_28951] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4201 v h) (hints_cons _ _ _ (der_28951 v h) (by intro d hd; cases hd)))
def cl_29015 : CNF.NClause := [(32,false),(81,false),(1,true),(66,false),(71,false),(86,true),(76,true)]
theorem der_29015 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29015 :=
  CNF.rup_sound cl_29015 [cl_4202,cl_28952] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4202 v h) (hints_cons _ _ _ (der_28952 v h) (by intro d hd; cases hd)))
def cl_29016 : CNF.NClause := [(32,false),(66,true),(1,false),(71,false),(76,true),(81,false),(86,true)]
theorem der_29016 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29016 :=
  CNF.rup_sound cl_29016 [cl_4203,cl_28953] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4203 v h) (hints_cons _ _ _ (der_28953 v h) (by intro d hd; cases hd)))
def cl_29017 : CNF.NClause := [(32,false),(66,true),(86,true),(71,false),(76,true),(81,false),(87,true)]
theorem der_29017 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29017 :=
  CNF.rup_sound cl_29017 [cl_4204,cl_29016] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4204 v h) (hints_cons _ _ _ (der_29016 v h) (by intro d hd; cases hd)))
def cl_29018 : CNF.NClause := [(32,false),(81,false),(1,false),(66,false),(76,true),(71,true),(87,true)]
theorem der_29018 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29018 :=
  CNF.rup_sound cl_29018 [cl_4205,cl_28986] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4205 v h) (hints_cons _ _ _ (der_28986 v h) (by intro d hd; cases hd)))
def cl_29019 : CNF.NClause := [(32,false),(86,true),(1,true),(66,false),(71,true),(81,false),(87,true)]
theorem der_29019 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29019 :=
  CNF.rup_sound cl_29019 [cl_4206,cl_29011] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4206 v h) (hints_cons _ _ _ (der_29011 v h) (by intro d hd; cases hd)))
def cl_29020 : CNF.NClause := [(32,false),(66,true),(1,false),(71,true),(76,true),(81,false),(86,true)]
theorem der_29020 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29020 :=
  CNF.rup_sound cl_29020 [cl_4207,cl_28957] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4207 v h) (hints_cons _ _ _ (der_28957 v h) (by intro d hd; cases hd)))
def cl_29021 : CNF.NClause := [(32,false),(66,true),(1,true),(81,false),(76,true),(86,true),(87,true)]
theorem der_29021 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29021 :=
  CNF.rup_sound cl_29021 [cl_4208,cl_29017] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4208 v h) (hints_cons _ _ _ (der_29017 v h) (by intro d hd; cases hd)))
def cl_29022 : CNF.NClause := [(32,false),(81,true),(1,false),(66,false),(71,false),(76,false),(86,true)]
theorem der_29022 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29022 :=
  CNF.rup_sound cl_29022 [cl_4209,cl_28959] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4209 v h) (hints_cons _ _ _ (der_28959 v h) (by intro d hd; cases hd)))
def cl_29023 : CNF.NClause := [(32,false),(81,true),(1,true),(66,false),(71,false),(76,false),(87,true)]
theorem der_29023 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29023 :=
  CNF.rup_sound cl_29023 [cl_4210,cl_28991] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4210 v h) (hints_cons _ _ _ (der_28991 v h) (by intro d hd; cases hd)))
def cl_29024 : CNF.NClause := [(32,false),(81,true),(1,false),(71,false),(76,false),(66,true),(86,true)]
theorem der_29024 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29024 :=
  CNF.rup_sound cl_29024 [cl_4211,cl_28961] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4211 v h) (hints_cons _ _ _ (der_28961 v h) (by intro d hd; cases hd)))
def cl_29025 : CNF.NClause := [(32,false),(81,true),(1,true),(71,false),(76,false),(86,true),(87,true)]
theorem der_29025 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29025 :=
  CNF.rup_sound cl_29025 [cl_4212,cl_29023] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4212 v h) (hints_cons _ _ _ (der_29023 v h) (by intro d hd; cases hd)))
def cl_29026 : CNF.NClause := [(32,false),(81,true),(1,false),(66,false),(71,true),(76,false),(86,true)]
theorem der_29026 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29026 :=
  CNF.rup_sound cl_29026 [cl_4213,cl_28963] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4213 v h) (hints_cons _ _ _ (der_28963 v h) (by intro d hd; cases hd)))
def cl_29027 : CNF.NClause := [(32,false),(81,true),(1,true),(66,false),(76,false),(86,true),(87,true)]
theorem der_29027 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29027 :=
  CNF.rup_sound cl_29027 [cl_4214,cl_29023] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4214 v h) (hints_cons _ _ _ (der_29023 v h) (by intro d hd; cases hd)))
def cl_29028 : CNF.NClause := [(32,false),(1,false),(71,true),(76,false),(81,true),(86,true),(87,true)]
theorem der_29028 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29028 :=
  CNF.rup_sound cl_29028 [cl_4215,cl_29026] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4215 v h) (hints_cons _ _ _ (der_29026 v h) (by intro d hd; cases hd)))
def cl_29029 : CNF.NClause := [(32,false),(81,true),(1,true),(66,true),(76,false),(71,true),(87,true)]
theorem der_29029 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29029 :=
  CNF.rup_sound cl_29029 [cl_4216,cl_28997] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4216 v h) (hints_cons _ _ _ (der_28997 v h) (by intro d hd; cases hd)))
def cl_29030 : CNF.NClause := [(32,false),(81,true),(1,false),(66,false),(71,false),(76,true),(86,true)]
theorem der_29030 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29030 :=
  CNF.rup_sound cl_29030 [cl_4217,cl_28967] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4217 v h) (hints_cons _ _ _ (der_28967 v h) (by intro d hd; cases hd)))
def cl_29031 : CNF.NClause := [(32,false),(81,true),(1,true),(66,false),(71,false),(86,true),(87,true)]
theorem der_29031 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29031 :=
  CNF.rup_sound cl_29031 [cl_4218,cl_29027] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4218 v h) (hints_cons _ _ _ (der_29027 v h) (by intro d hd; cases hd)))
def cl_29034 : CNF.NClause := [(32,false),(81,true),(1,false),(66,false),(76,true),(71,true),(86,true)]
theorem der_29034 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29034 :=
  CNF.rup_sound cl_29034 [cl_4221,cl_28971] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4221 v h) (hints_cons _ _ _ (der_28971 v h) (by intro d hd; cases hd)))
def cl_29035 : CNF.NClause := [(32,false),(81,true),(1,true),(66,false),(71,true),(86,true),(87,true)]
theorem der_29035 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29035 :=
  CNF.rup_sound cl_29035 [cl_4222,cl_29027] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4222 v h) (hints_cons _ _ _ (der_29027 v h) (by intro d hd; cases hd)))
def cl_29036 : CNF.NClause := [(32,false),(66,true),(1,false),(71,true),(76,true),(81,true),(86,true)]
theorem der_29036 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29036 :=
  CNF.rup_sound cl_29036 [cl_4223,cl_28973] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4223 v h) (hints_cons _ _ _ (der_28973 v h) (by intro d hd; cases hd)))
def cl_29037 : CNF.NClause := [(32,false),(81,true),(66,true),(76,true),(71,true),(86,true),(87,true)]
theorem der_29037 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29037 :=
  CNF.rup_sound cl_29037 [cl_4224,cl_29036] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4224 v h) (hints_cons _ _ _ (der_29036 v h) (by intro d hd; cases hd)))
def cl_29038 : CNF.NClause := [(49,false),(86,false),(77,false),(91,true),(69,false),(73,false),(65,false)]
theorem der_29038 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29038 :=
  CNF.rup_sound cl_29038 [cl_6337,cl_26318] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6337 v h) (hints_cons _ _ _ (der_26318 v h) (by intro d hd; cases hd)))
def cl_29039 : CNF.NClause := [(53,false),(90,true),(78,false),(75,false),(64,false),(86,false),(67,false)]
theorem der_29039 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29039 :=
  CNF.rup_sound cl_29039 [cl_6849,cl_26773] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6849 v h) (hints_cons _ _ _ (der_26773 v h) (by intro d hd; cases hd)))
def cl_29040 : CNF.NClause := [(53,false),(90,true),(22,true),(75,false),(86,false),(67,false),(78,false)]
theorem der_29040 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29040 :=
  CNF.rup_sound cl_29040 [cl_6852,cl_29039] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6852 v h) (hints_cons _ _ _ (der_29039 v h) (by intro d hd; cases hd)))
def cl_29041 : CNF.NClause := [(49,false),(18,false),(69,false),(73,false),(77,false),(65,false),(91,true)]
theorem der_29041 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29041 :=
  CNF.rup_sound cl_29041 [cl_6369,cl_29038] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6369 v h) (hints_cons _ _ _ (der_29038 v h) (by intro d hd; cases hd)))
def cl_29042 : CNF.NClause := [(53,false),(86,true),(64,false),(75,false),(78,false),(67,false),(90,false)]
theorem der_29042 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29042 :=
  CNF.rup_sound cl_29042 [cl_6817,cl_26777] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6817 v h) (hints_cons _ _ _ (der_26777 v h) (by intro d hd; cases hd)))
def cl_29043 : CNF.NClause := [(53,false),(90,true),(64,false),(22,false),(75,false),(78,false),(67,false)]
theorem der_29043 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29043 :=
  CNF.rup_sound cl_29043 [cl_6881,cl_29039] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6881 v h) (hints_cons _ _ _ (der_29039 v h) (by intro d hd; cases hd)))
def cl_29044 : CNF.NClause := [(45,false),(86,true),(63,false),(72,false),(79,false),(70,false),(89,false)]
theorem der_29044 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29044 :=
  CNF.rup_sound cl_29044 [cl_5793,cl_26813] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5793 v h) (hints_cons _ _ _ (der_26813 v h) (by intro d hd; cases hd)))
def cl_29045 : CNF.NClause := [(45,false),(14,false),(63,false),(72,false),(79,false),(70,false),(86,true)]
theorem der_29045 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29045 :=
  CNF.rup_sound cl_29045 [cl_5857,cl_29044] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5857 v h) (hints_cons _ _ _ (der_29044 v h) (by intro d hd; cases hd)))
def cl_29046 : CNF.NClause := [(45,false),(86,true),(14,true),(72,false),(79,false),(70,false),(89,false)]
theorem der_29046 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29046 :=
  CNF.rup_sound cl_29046 [cl_5796,cl_29044] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5796 v h) (hints_cons _ _ _ (der_29044 v h) (by intro d hd; cases hd)))
def cl_29047 : CNF.NClause := [(53,false),(67,false),(22,true),(90,false),(86,true),(75,false),(78,false)]
theorem der_29047 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29047 :=
  CNF.rup_sound cl_29047 [cl_6820,cl_29042] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6820 v h) (hints_cons _ _ _ (der_29042 v h) (by intro d hd; cases hd)))
def cl_29048 : CNF.NClause := [(53,false),(90,true),(22,true),(64,true),(67,false),(75,false),(78,false)]
theorem der_29048 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29048 :=
  CNF.rup_sound cl_29048 [cl_6884,cl_29040] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6884 v h) (hints_cons _ _ _ (der_29040 v h) (by intro d hd; cases hd)))
def cl_29049 : CNF.NClause := [(49,false),(77,true),(18,true),(69,false),(73,false),(65,false),(91,false)]
theorem der_29049 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29049 :=
  CNF.rup_sound cl_29049 [cl_6322,cl_26729] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6322 v h) (hints_cons _ _ _ (der_26729 v h) (by intro d hd; cases hd)))
def cl_29050 : CNF.NClause := [(49,false),(18,true),(69,false),(73,false),(77,true),(65,false),(91,true)]
theorem der_29050 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29050 :=
  CNF.rup_sound cl_29050 [cl_6386,cl_26318] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6386 v h) (hints_cons _ _ _ (der_26318 v h) (by intro d hd; cases hd)))
def cl_29051 : CNF.NClause := [(49,false),(86,true),(69,false),(73,false),(77,true),(65,false),(91,false)]
theorem der_29051 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29051 :=
  CNF.rup_sound cl_29051 [cl_6321,cl_29049] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6321 v h) (hints_cons _ _ _ (der_29049 v h) (by intro d hd; cases hd)))
def cl_29052 : CNF.NClause := [(49,false),(86,true),(18,false),(69,false),(73,false),(77,true),(65,false)]
theorem der_29052 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29052 :=
  CNF.rup_sound cl_29052 [cl_6385,cl_29051] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6385 v h) (hints_cons _ _ _ (der_29051 v h) (by intro d hd; cases hd)))
def cl_29053 : CNF.NClause := [(49,false),(69,false),(18,true),(86,true),(73,false),(65,false),(91,false)]
theorem der_29053 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29053 :=
  CNF.rup_sound cl_29053 [cl_6306,cl_29051] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6306 v h) (hints_cons _ _ _ (der_29051 v h) (by intro d hd; cases hd)))
def cl_29054 : CNF.NClause := [(49,false),(69,false),(18,true),(73,false),(77,false),(65,false),(91,true)]
theorem der_29054 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29054 :=
  CNF.rup_sound cl_29054 [cl_6370,cl_29038] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6370 v h) (hints_cons _ _ _ (der_29038 v h) (by intro d hd; cases hd)))
def cl_29055 : CNF.NClause := [(52,false),(21,false),(66,false),(85,true),(79,false),(67,false),(73,false)]
theorem der_29055 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29055 :=
  CNF.rup_sound cl_29055 [cl_6753,cl_6689] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6753 v h) (hints_cons _ _ _ (inp_6689 v h) (by intro d hd; cases hd)))
def cl_29056 : CNF.NClause := [(52,false),(85,true),(88,false),(67,false),(66,false),(79,false),(73,false)]
theorem der_29056 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29056 :=
  CNF.rup_sound cl_29056 [cl_6690,cl_6689] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6690 v h) (hints_cons _ _ _ (inp_6689 v h) (by intro d hd; cases hd)))
def cl_29057 : CNF.NClause := [(52,false),(21,true),(67,false),(66,false),(73,false),(79,false),(85,true)]
theorem der_29057 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29057 :=
  CNF.rup_sound cl_29057 [cl_6754,cl_29056] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6754 v h) (hints_cons _ _ _ (der_29056 v h) (by intro d hd; cases hd)))
def cl_29058 : CNF.NClause := [(44,false),(84,true),(65,false),(88,false),(72,false),(71,false),(78,false)]
theorem der_29058 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29058 :=
  CNF.rup_sound cl_29058 [cl_5665,cl_5666] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5665 v h) (hints_cons _ _ _ (inp_5666 v h) (by intro d hd; cases hd)))
def cl_29059 : CNF.NClause := [(44,false),(13,false),(65,false),(84,true),(71,false),(78,false),(72,false)]
theorem der_29059 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29059 :=
  CNF.rup_sound cl_29059 [cl_5729,cl_29058] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5729 v h) (hints_cons _ _ _ (der_29058 v h) (by intro d hd; cases hd)))
def cl_29060 : CNF.NClause := [(47,false),(84,true),(16,false),(66,false),(75,false),(77,false),(68,false)]
theorem der_29060 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29060 :=
  CNF.rup_sound cl_29060 [cl_6113,cl_6049] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6113 v h) (hints_cons _ _ _ (inp_6049 v h) (by intro d hd; cases hd)))
def cl_29061 : CNF.NClause := [(47,false),(84,true),(66,false),(68,false),(77,false),(75,false),(89,false)]
theorem der_29061 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29061 :=
  CNF.rup_sound cl_29061 [cl_6050,cl_6049] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6050 v h) (hints_cons _ _ _ (inp_6049 v h) (by intro d hd; cases hd)))
def cl_29062 : CNF.NClause := [(47,false),(84,true),(66,false),(68,false),(16,true),(77,false),(75,false)]
theorem der_29062 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29062 :=
  CNF.rup_sound cl_29062 [cl_6114,cl_29061] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6114 v h) (hints_cons _ _ _ (der_29061 v h) (by intro d hd; cases hd)))
def cl_29063 : CNF.NClause := [(47,false),(84,true),(16,false),(66,false),(75,false),(68,false),(89,false)]
theorem der_29063 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29063 :=
  CNF.rup_sound cl_29063 [cl_6065,cl_29061] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6065 v h) (hints_cons _ _ _ (der_29061 v h) (by intro d hd; cases hd)))
def cl_29064 : CNF.NClause := [(47,false),(84,true),(16,false),(66,false),(75,false),(68,false),(89,true)]
theorem der_29064 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29064 :=
  CNF.rup_sound cl_29064 [cl_6129,cl_29060] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6129 v h) (hints_cons _ _ _ (der_29060 v h) (by intro d hd; cases hd)))
def cl_29065 : CNF.NClause := [(47,false),(84,true),(66,false),(68,false),(16,true),(75,false),(89,false)]
theorem der_29065 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29065 :=
  CNF.rup_sound cl_29065 [cl_6066,cl_29061] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6066 v h) (hints_cons _ _ _ (der_29061 v h) (by intro d hd; cases hd)))
def cl_29066 : CNF.NClause := [(47,false),(84,true),(66,false),(68,false),(77,true),(75,false),(89,true)]
theorem der_29066 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29066 :=
  CNF.rup_sound cl_29066 [cl_6130,cl_29064] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6130 v h) (hints_cons _ _ _ (der_29064 v h) (by intro d hd; cases hd)))
def cl_29067 : CNF.NClause := [(52,false),(21,false),(85,true),(66,false),(73,false),(67,false),(88,false)]
theorem der_29067 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29067 :=
  CNF.rup_sound cl_29067 [cl_6705,cl_29056] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6705 v h) (hints_cons _ _ _ (der_29056 v h) (by intro d hd; cases hd)))
def cl_29068 : CNF.NClause := [(52,false),(79,true),(21,false),(66,false),(67,false),(85,false),(73,false)]
theorem der_29068 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29068 :=
  CNF.rup_sound cl_29068 [cl_6737,cl_6673] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6737 v h) (hints_cons _ _ _ (inp_6673 v h) (by intro d hd; cases hd)))
def cl_29069 : CNF.NClause := [(52,false),(21,false),(66,false),(67,false),(88,true),(85,true),(73,false)]
theorem der_29069 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29069 :=
  CNF.rup_sound cl_29069 [cl_6769,cl_29055] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6769 v h) (hints_cons _ _ _ (der_29055 v h) (by intro d hd; cases hd)))
def cl_29070 : CNF.NClause := [(45,false),(89,false),(14,false),(63,false),(72,false),(70,false),(86,true)]
theorem der_29070 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29070 :=
  CNF.rup_sound cl_29070 [cl_5809,cl_29044] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5809 v h) (hints_cons _ _ _ (der_29044 v h) (by intro d hd; cases hd)))
def cl_29071 : CNF.NClause := [(45,false),(79,true),(14,false),(63,false),(70,false),(72,false),(86,false)]
theorem der_29071 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29071 :=
  CNF.rup_sound cl_29071 [cl_5841,cl_5777] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5841 v h) (hints_cons _ _ _ (inp_5777 v h) (by intro d hd; cases hd)))
def cl_29072 : CNF.NClause := [(45,false),(86,true),(14,false),(63,false),(72,false),(70,false),(89,true)]
theorem der_29072 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29072 :=
  CNF.rup_sound cl_29072 [cl_5873,cl_29045] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5873 v h) (hints_cons _ _ _ (der_29045 v h) (by intro d hd; cases hd)))
def cl_29073 : CNF.NClause := [(45,false),(89,false),(14,true),(63,true),(72,false),(70,false),(86,true)]
theorem der_29073 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29073 :=
  CNF.rup_sound cl_29073 [cl_5812,cl_29046] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5812 v h) (hints_cons _ _ _ (der_29046 v h) (by intro d hd; cases hd)))
def cl_29074 : CNF.NClause := [(52,false),(79,true),(73,false),(66,false),(67,false),(85,false),(88,false)]
theorem der_29074 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29074 :=
  CNF.rup_sound cl_29074 [cl_6674,cl_6673] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6674 v h) (hints_cons _ _ _ (inp_6673 v h) (by intro d hd; cases hd)))
def cl_29075 : CNF.NClause := [(52,false),(21,true),(73,false),(66,false),(85,true),(67,false),(88,false)]
theorem der_29075 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29075 :=
  CNF.rup_sound cl_29075 [cl_6706,cl_29056] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6706 v h) (hints_cons _ _ _ (der_29056 v h) (by intro d hd; cases hd)))
def cl_29076 : CNF.NClause := [(52,false),(79,true),(21,true),(67,false),(66,false),(85,false),(73,false)]
theorem der_29076 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29076 :=
  CNF.rup_sound cl_29076 [cl_6738,cl_29074] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6738 v h) (hints_cons _ _ _ (der_29074 v h) (by intro d hd; cases hd)))
def cl_29077 : CNF.NClause := [(52,false),(79,true),(67,false),(66,false),(88,true),(85,true),(73,false)]
theorem der_29077 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29077 :=
  CNF.rup_sound cl_29077 [cl_6770,cl_29069] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6770 v h) (hints_cons _ _ _ (der_29069 v h) (by intro d hd; cases hd)))
def cl_29078 : CNF.NClause := [(45,false),(79,true),(89,false),(86,false),(63,false),(70,false),(72,false)]
theorem der_29078 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29078 :=
  CNF.rup_sound cl_29078 [cl_5778,cl_5777] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5778 v h) (hints_cons _ _ _ (inp_5777 v h) (by intro d hd; cases hd)))
def cl_29079 : CNF.NClause := [(45,false),(14,true),(70,false),(63,false),(72,false),(86,true),(89,false)]
theorem der_29079 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29079 :=
  CNF.rup_sound cl_29079 [cl_5810,cl_29044] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5810 v h) (hints_cons _ _ _ (der_29044 v h) (by intro d hd; cases hd)))
def cl_29080 : CNF.NClause := [(45,false),(79,true),(14,true),(86,false),(63,false),(70,false),(72,false)]
theorem der_29080 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29080 :=
  CNF.rup_sound cl_29080 [cl_5842,cl_29078] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5842 v h) (hints_cons _ _ _ (der_29078 v h) (by intro d hd; cases hd)))
def cl_29081 : CNF.NClause := [(45,false),(79,true),(70,false),(63,false),(72,false),(86,true),(89,true)]
theorem der_29081 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29081 :=
  CNF.rup_sound cl_29081 [cl_5874,cl_29072] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5874 v h) (hints_cons _ _ _ (der_29072 v h) (by intro d hd; cases hd)))
def cl_29082 : CNF.NClause := [(53,false),(78,true),(64,false),(75,false),(67,false),(86,false),(90,false)]
theorem der_29082 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29082 :=
  CNF.rup_sound cl_29082 [cl_6801,cl_26775] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6801 v h) (hints_cons _ _ _ (der_26775 v h) (by intro d hd; cases hd)))
def cl_29083 : CNF.NClause := [(53,false),(64,false),(22,false),(75,false),(67,false),(86,true),(90,false)]
theorem der_29083 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29083 :=
  CNF.rup_sound cl_29083 [cl_6833,cl_29042] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6833 v h) (hints_cons _ _ _ (der_29042 v h) (by intro d hd; cases hd)))
def cl_29084 : CNF.NClause := [(53,false),(64,false),(22,false),(75,false),(67,false),(86,false),(90,true)]
theorem der_29084 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29084 :=
  CNF.rup_sound cl_29084 [cl_6865,cl_29039] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6865 v h) (hints_cons _ _ _ (der_29039 v h) (by intro d hd; cases hd)))
def cl_29085 : CNF.NClause := [(53,false),(78,true),(64,false),(75,false),(67,false),(86,true),(90,true)]
theorem der_29085 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29085 :=
  CNF.rup_sound cl_29085 [cl_6897,cl_26780] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6897 v h) (hints_cons _ _ _ (der_26780 v h) (by intro d hd; cases hd)))
def cl_29086 : CNF.NClause := [(44,false),(78,true),(65,false),(72,false),(71,false),(84,false),(88,false)]
theorem der_29086 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29086 :=
  CNF.rup_sound cl_29086 [cl_5649,cl_5650] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5649 v h) (hints_cons _ _ _ (inp_5650 v h) (by intro d hd; cases hd)))
def cl_29087 : CNF.NClause := [(44,false),(13,false),(65,false),(72,false),(71,false),(84,true),(88,false)]
theorem der_29087 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29087 :=
  CNF.rup_sound cl_29087 [cl_5681,cl_29058] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5681 v h) (hints_cons _ _ _ (der_29058 v h) (by intro d hd; cases hd)))
def cl_29088 : CNF.NClause := [(44,false),(78,true),(13,false),(65,false),(72,false),(71,false),(84,false)]
theorem der_29088 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29088 :=
  CNF.rup_sound cl_29088 [cl_5713,cl_29086] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5713 v h) (hints_cons _ _ _ (der_29086 v h) (by intro d hd; cases hd)))
def cl_29089 : CNF.NClause := [(44,false),(13,false),(65,false),(72,false),(71,false),(84,true),(88,true)]
theorem der_29089 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29089 :=
  CNF.rup_sound cl_29089 [cl_5745,cl_29059] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5745 v h) (hints_cons _ _ _ (der_29059 v h) (by intro d hd; cases hd)))
def cl_29090 : CNF.NClause := [(53,false),(78,true),(22,true),(67,false),(75,false),(86,false),(90,false)]
theorem der_29090 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29090 :=
  CNF.rup_sound cl_29090 [cl_6804,cl_29082] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6804 v h) (hints_cons _ _ _ (der_29082 v h) (by intro d hd; cases hd)))
def cl_29091 : CNF.NClause := [(53,false),(22,true),(64,true),(67,false),(75,false),(86,true),(90,false)]
theorem der_29091 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29091 :=
  CNF.rup_sound cl_29091 [cl_6836,cl_29047] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6836 v h) (hints_cons _ _ _ (der_29047 v h) (by intro d hd; cases hd)))
def cl_29092 : CNF.NClause := [(53,false),(78,true),(22,true),(67,false),(75,false),(86,false),(90,true)]
theorem der_29092 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29092 :=
  CNF.rup_sound cl_29092 [cl_6868,cl_26779] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6868 v h) (hints_cons _ _ _ (der_26779 v h) (by intro d hd; cases hd)))
def cl_29093 : CNF.NClause := [(53,false),(78,true),(22,true),(67,false),(75,false),(86,true),(90,true)]
theorem der_29093 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29093 :=
  CNF.rup_sound cl_29093 [cl_6900,cl_29085] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6900 v h) (hints_cons _ _ _ (der_29085 v h) (by intro d hd; cases hd)))
def cl_29094 : CNF.NClause := [(45,false),(70,true),(63,false),(86,false),(72,false),(79,false),(89,false)]
theorem der_29094 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29094 :=
  CNF.rup_sound cl_29094 [cl_5765,cl_26817] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5765 v h) (hints_cons _ _ _ (der_26817 v h) (by intro d hd; cases hd)))
def cl_29095 : CNF.NClause := [(45,false),(14,false),(63,false),(86,false),(79,false),(70,true),(89,false)]
theorem der_29095 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29095 :=
  CNF.rup_sound cl_29095 [cl_5773,cl_29094] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5773 v h) (hints_cons _ _ _ (der_29094 v h) (by intro d hd; cases hd)))
def cl_29096 : CNF.NClause := [(45,false),(79,true),(14,false),(63,false),(72,false),(86,false),(89,false)]
theorem der_29096 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29096 :=
  CNF.rup_sound cl_29096 [cl_5781,cl_29078] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5781 v h) (hints_cons _ _ _ (der_29078 v h) (by intro d hd; cases hd)))
def cl_29097 : CNF.NClause := [(45,false),(14,false),(63,false),(72,true),(70,true),(86,false),(89,false)]
theorem der_29097 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29097 :=
  CNF.rup_sound cl_29097 [cl_5789,cl_29095] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5789 v h) (hints_cons _ _ _ (der_29095 v h) (by intro d hd; cases hd)))
def cl_29098 : CNF.NClause := [(45,false),(14,false),(63,false),(72,false),(79,false),(86,true),(89,false)]
theorem der_29098 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29098 :=
  CNF.rup_sound cl_29098 [cl_5797,cl_29044] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5797 v h) (hints_cons _ _ _ (der_29044 v h) (by intro d hd; cases hd)))
def cl_29099 : CNF.NClause := [(45,false),(70,true),(14,false),(63,false),(72,true),(79,false),(89,false)]
theorem der_29099 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29099 :=
  CNF.rup_sound cl_29099 [cl_5805,cl_29095] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5805 v h) (hints_cons _ _ _ (der_29095 v h) (by intro d hd; cases hd)))
def cl_29100 : CNF.NClause := [(45,false),(79,true),(63,false),(72,false),(70,true),(86,true),(89,false)]
theorem der_29100 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29100 :=
  CNF.rup_sound cl_29100 [cl_5813,cl_26816] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5813 v h) (hints_cons _ _ _ (der_26816 v h) (by intro d hd; cases hd)))
def cl_29101 : CNF.NClause := [(45,false),(79,true),(14,false),(63,false),(70,true),(86,true),(89,false)]
theorem der_29101 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29101 :=
  CNF.rup_sound cl_29101 [cl_5821,cl_29100] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5821 v h) (hints_cons _ _ _ (der_29100 v h) (by intro d hd; cases hd)))
def cl_29102 : CNF.NClause := [(45,false),(70,true),(14,false),(63,false),(72,false),(79,false),(86,false)]
theorem der_29102 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29102 :=
  CNF.rup_sound cl_29102 [cl_5829,cl_29094] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5829 v h) (hints_cons _ _ _ (der_29094 v h) (by intro d hd; cases hd)))
def cl_29103 : CNF.NClause := [(45,false),(72,true),(14,false),(63,false),(86,false),(79,false),(70,true)]
theorem der_29103 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29103 :=
  CNF.rup_sound cl_29103 [cl_5837,cl_29095] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5837 v h) (hints_cons _ _ _ (der_29095 v h) (by intro d hd; cases hd)))
def cl_29104 : CNF.NClause := [(45,false),(79,true),(14,false),(63,false),(72,false),(86,false),(89,true)]
theorem der_29104 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29104 :=
  CNF.rup_sound cl_29104 [cl_5845,cl_29071] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5845 v h) (hints_cons _ _ _ (der_29071 v h) (by intro d hd; cases hd)))
def cl_29105 : CNF.NClause := [(45,false),(14,false),(63,false),(72,true),(70,true),(86,false),(89,true)]
theorem der_29105 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29105 :=
  CNF.rup_sound cl_29105 [cl_5853,cl_29103] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5853 v h) (hints_cons _ _ _ (der_29103 v h) (by intro d hd; cases hd)))
def cl_29106 : CNF.NClause := [(45,false),(70,true),(63,false),(72,false),(79,false),(86,true),(89,true)]
theorem der_29106 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29106 :=
  CNF.rup_sound cl_29106 [cl_5861,cl_26821] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5861 v h) (hints_cons _ _ _ (der_26821 v h) (by intro d hd; cases hd)))
def cl_29107 : CNF.NClause := [(45,false),(70,true),(14,false),(63,false),(72,true),(79,false),(89,true)]
theorem der_29107 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29107 :=
  CNF.rup_sound cl_29107 [cl_5869,cl_29103] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5869 v h) (hints_cons _ _ _ (der_29103 v h) (by intro d hd; cases hd)))
def cl_29108 : CNF.NClause := [(45,false),(79,true),(14,false),(63,false),(72,false),(86,true),(89,true)]
theorem der_29108 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29108 :=
  CNF.rup_sound cl_29108 [cl_5877,cl_29081] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5877 v h) (hints_cons _ _ _ (der_29081 v h) (by intro d hd; cases hd)))
def cl_29110 : CNF.NClause := [(45,false),(70,true),(14,true),(79,false),(72,false),(89,false),(86,false)]
theorem der_29110 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29110 :=
  CNF.rup_sound cl_29110 [cl_5768,cl_29094] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5768 v h) (hints_cons _ _ _ (der_29094 v h) (by intro d hd; cases hd)))
def cl_29111 : CNF.NClause := [(45,false),(72,true),(14,true),(70,true),(79,false),(86,false),(89,false)]
theorem der_29111 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29111 :=
  CNF.rup_sound cl_29111 [cl_5776,cl_26812] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5776 v h) (hints_cons _ _ _ (der_26812 v h) (by intro d hd; cases hd)))
def cl_29112 : CNF.NClause := [(45,false),(79,true),(14,true),(63,true),(72,false),(86,false),(89,false)]
theorem der_29112 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29112 :=
  CNF.rup_sound cl_29112 [cl_5784,cl_5780] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5784 v h) (hints_cons _ _ _ (inp_5780 v h) (by intro d hd; cases hd)))
def cl_29113 : CNF.NClause := [(45,false),(72,true),(14,true),(70,true),(79,true),(86,false),(89,false)]
theorem der_29113 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29113 :=
  CNF.rup_sound cl_29113 [cl_5792,cl_26812] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5792 v h) (hints_cons _ _ _ (der_26812 v h) (by intro d hd; cases hd)))
def cl_29114 : CNF.NClause := [(45,false),(14,true),(72,false),(70,true),(79,false),(86,true),(89,false)]
theorem der_29114 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29114 :=
  CNF.rup_sound cl_29114 [cl_5800,cl_26813] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5800 v h) (hints_cons _ _ _ (der_26813 v h) (by intro d hd; cases hd)))
def cl_29115 : CNF.NClause := [(45,false),(72,true),(14,true),(63,true),(70,true),(79,false),(89,false)]
theorem der_29115 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29115 :=
  CNF.rup_sound cl_29115 [cl_5808,cl_29111] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5808 v h) (hints_cons _ _ _ (der_29111 v h) (by intro d hd; cases hd)))
def cl_29116 : CNF.NClause := [(45,false),(79,true),(14,true),(70,true),(72,false),(86,true),(89,false)]
theorem der_29116 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29116 :=
  CNF.rup_sound cl_29116 [cl_5816,cl_29100] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5816 v h) (hints_cons _ _ _ (der_29100 v h) (by intro d hd; cases hd)))
def cl_29117 : CNF.NClause := [(45,false),(72,true),(14,true),(70,true),(79,true),(86,true),(89,false)]
theorem der_29117 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29117 :=
  CNF.rup_sound cl_29117 [cl_5824,cl_26824] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5824 v h) (hints_cons _ _ _ (der_26824 v h) (by intro d hd; cases hd)))
def cl_29118 : CNF.NClause := [(45,false),(63,true),(14,true),(72,false),(70,true),(79,false),(86,false)]
theorem der_29118 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29118 :=
  CNF.rup_sound cl_29118 [cl_5832,cl_29110] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5832 v h) (hints_cons _ _ _ (der_29110 v h) (by intro d hd; cases hd)))
def cl_29119 : CNF.NClause := [(45,false),(72,true),(14,true),(63,true),(70,true),(79,false),(86,false)]
theorem der_29119 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29119 :=
  CNF.rup_sound cl_29119 [cl_5840,cl_29111] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5840 v h) (hints_cons _ _ _ (der_29111 v h) (by intro d hd; cases hd)))
def cl_29120 : CNF.NClause := [(45,false),(79,true),(14,true),(63,true),(70,true),(72,false),(86,false)]
theorem der_29120 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29120 :=
  CNF.rup_sound cl_29120 [cl_5848,cl_29112] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5848 v h) (hints_cons _ _ _ (der_29112 v h) (by intro d hd; cases hd)))
def cl_29121 : CNF.NClause := [(45,false),(14,true),(63,true),(70,true),(79,true),(86,false),(89,true)]
theorem der_29121 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29121 :=
  CNF.rup_sound cl_29121 [cl_5856,cl_29120] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5856 v h) (hints_cons _ _ _ (der_29120 v h) (by intro d hd; cases hd)))
def cl_29122 : CNF.NClause := [(45,false),(14,true),(72,false),(70,true),(79,false),(86,true),(89,true)]
theorem der_29122 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29122 :=
  CNF.rup_sound cl_29122 [cl_5864,cl_29106] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5864 v h) (hints_cons _ _ _ (der_29106 v h) (by intro d hd; cases hd)))
def cl_29123 : CNF.NClause := [(45,false),(14,true),(63,true),(70,true),(79,false),(86,true),(89,true)]
theorem der_29123 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29123 :=
  CNF.rup_sound cl_29123 [cl_5872,cl_29122] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5872 v h) (hints_cons _ _ _ (der_29122 v h) (by intro d hd; cases hd)))
def cl_29124 : CNF.NClause := [(45,false),(79,true),(14,true),(63,true),(70,true),(72,false),(89,true)]
theorem der_29124 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29124 :=
  CNF.rup_sound cl_29124 [cl_5880,cl_29120] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5880 v h) (hints_cons _ _ _ (der_29120 v h) (by intro d hd; cases hd)))
def cl_29125 : CNF.NClause := [(45,false),(14,true),(63,true),(70,true),(79,true),(86,true),(89,true)]
theorem der_29125 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29125 :=
  CNF.rup_sound cl_29125 [cl_5888,cl_29124] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5888 v h) (hints_cons _ _ _ (der_29124 v h) (by intro d hd; cases hd)))
def cl_29126 : CNF.NClause := [(47,false),(68,true),(84,false),(75,false),(77,false),(66,false),(89,false)]
theorem der_29126 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29126 :=
  CNF.rup_sound cl_29126 [cl_6021,cl_26303] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6021 v h) (hints_cons _ _ _ (der_26303 v h) (by intro d hd; cases hd)))
def cl_29127 : CNF.NClause := [(47,false),(16,false),(68,true),(66,false),(77,false),(84,false),(89,false)]
theorem der_29127 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29127 :=
  CNF.rup_sound cl_29127 [cl_6029,cl_29126] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6029 v h) (hints_cons _ _ _ (der_29126 v h) (by intro d hd; cases hd)))
def cl_29128 : CNF.NClause := [(47,false),(16,false),(68,true),(75,false),(66,false),(89,false),(84,false)]
theorem der_29128 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29128 :=
  CNF.rup_sound cl_29128 [cl_6037,cl_29126] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6037 v h) (hints_cons _ _ _ (der_29126 v h) (by intro d hd; cases hd)))
def cl_29129 : CNF.NClause := [(47,false),(75,true),(16,false),(68,true),(66,false),(84,false),(89,false)]
theorem der_29129 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29129 :=
  CNF.rup_sound cl_29129 [cl_6045,cl_29127] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6045 v h) (hints_cons _ _ _ (der_29127 v h) (by intro d hd; cases hd)))
def cl_29130 : CNF.NClause := [(47,false),(84,true),(16,false),(89,false),(77,false),(75,false),(66,false)]
theorem der_29130 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29130 :=
  CNF.rup_sound cl_29130 [cl_6053,cl_29061] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6053 v h) (hints_cons _ _ _ (der_29061 v h) (by intro d hd; cases hd)))
def cl_29131 : CNF.NClause := [(47,false),(84,true),(16,false),(68,true),(66,false),(77,false),(89,false)]
theorem der_29131 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29131 :=
  CNF.rup_sound cl_29131 [cl_6061,cl_29130] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6061 v h) (hints_cons _ _ _ (der_29130 v h) (by intro d hd; cases hd)))
def cl_29132 : CNF.NClause := [(47,false),(84,true),(16,false),(89,false),(68,true),(75,false),(66,false)]
theorem der_29132 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29132 :=
  CNF.rup_sound cl_29132 [cl_6069,cl_29130] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6069 v h) (hints_cons _ _ _ (der_29130 v h) (by intro d hd; cases hd)))
def cl_29133 : CNF.NClause := [(47,false),(16,false),(68,true),(66,false),(77,true),(84,true),(89,false)]
theorem der_29133 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29133 :=
  CNF.rup_sound cl_29133 [cl_6077,cl_29132] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6077 v h) (hints_cons _ _ _ (der_29132 v h) (by intro d hd; cases hd)))
def cl_29134 : CNF.NClause := [(47,false),(68,true),(16,false),(75,false),(77,false),(84,false),(66,false)]
theorem der_29134 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29134 :=
  CNF.rup_sound cl_29134 [cl_6085,cl_29126] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6085 v h) (hints_cons _ _ _ (der_29126 v h) (by intro d hd; cases hd)))
def cl_29135 : CNF.NClause := [(47,false),(16,false),(68,true),(66,false),(77,false),(84,false),(89,true)]
theorem der_29135 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29135 :=
  CNF.rup_sound cl_29135 [cl_6093,cl_29134] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6093 v h) (hints_cons _ _ _ (der_29134 v h) (by intro d hd; cases hd)))
def cl_29136 : CNF.NClause := [(47,false),(68,true),(16,false),(89,true),(75,false),(84,false),(66,false)]
theorem der_29136 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29136 :=
  CNF.rup_sound cl_29136 [cl_6101,cl_29134] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6101 v h) (hints_cons _ _ _ (der_29134 v h) (by intro d hd; cases hd)))
def cl_29137 : CNF.NClause := [(47,false),(16,false),(68,true),(66,false),(77,true),(84,false),(89,true)]
theorem der_29137 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29137 :=
  CNF.rup_sound cl_29137 [cl_6109,cl_29136] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6109 v h) (hints_cons _ _ _ (der_29136 v h) (by intro d hd; cases hd)))
def cl_29138 : CNF.NClause := [(47,false),(68,true),(16,false),(75,false),(77,false),(84,true),(66,false)]
theorem der_29138 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29138 :=
  CNF.rup_sound cl_29138 [cl_6117,cl_29130] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6117 v h) (hints_cons _ _ _ (der_29130 v h) (by intro d hd; cases hd)))
def cl_29139 : CNF.NClause := [(47,false),(84,true),(16,false),(68,true),(66,false),(77,false),(89,true)]
theorem der_29139 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29139 :=
  CNF.rup_sound cl_29139 [cl_6125,cl_29138] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6125 v h) (hints_cons _ _ _ (der_29138 v h) (by intro d hd; cases hd)))
def cl_29140 : CNF.NClause := [(47,false),(16,false),(89,true),(75,false),(77,true),(84,true),(66,false)]
theorem der_29140 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29140 :=
  CNF.rup_sound cl_29140 [cl_6133,cl_29066] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6133 v h) (hints_cons _ _ _ (der_29066 v h) (by intro d hd; cases hd)))
def cl_29141 : CNF.NClause := [(47,false),(16,false),(68,true),(66,false),(77,true),(84,true),(89,true)]
theorem der_29141 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29141 :=
  CNF.rup_sound cl_29141 [cl_6141,cl_29140] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6141 v h) (hints_cons _ _ _ (der_29140 v h) (by intro d hd; cases hd)))
def cl_29142 : CNF.NClause := [(47,false),(16,true),(68,true),(75,false),(77,false),(84,false),(89,false)]
theorem der_29142 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29142 :=
  CNF.rup_sound cl_29142 [cl_6024,cl_29126] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6024 v h) (hints_cons _ _ _ (der_29126 v h) (by intro d hd; cases hd)))
def cl_29143 : CNF.NClause := [(47,false),(66,true),(16,true),(68,true),(77,false),(84,false),(89,false)]
theorem der_29143 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29143 :=
  CNF.rup_sound cl_29143 [cl_6032,cl_29142] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6032 v h) (hints_cons _ _ _ (der_29142 v h) (by intro d hd; cases hd)))
def cl_29144 : CNF.NClause := [(47,false),(66,true),(16,true),(68,true),(75,false),(84,false),(89,false)]
theorem der_29144 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29144 :=
  CNF.rup_sound cl_29144 [cl_6040,cl_29142] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6040 v h) (hints_cons _ _ _ (der_29142 v h) (by intro d hd; cases hd)))
def cl_29145 : CNF.NClause := [(47,false),(66,true),(16,true),(68,true),(75,true),(84,false),(89,false)]
theorem der_29145 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29145 :=
  CNF.rup_sound cl_29145 [cl_6048,cl_29143] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6048 v h) (hints_cons _ _ _ (der_29143 v h) (by intro d hd; cases hd)))
def cl_29146 : CNF.NClause := [(47,false),(66,true),(16,true),(68,true),(75,false),(77,false),(89,false)]
theorem der_29146 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29146 :=
  CNF.rup_sound cl_29146 [cl_6056,cl_29142] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6056 v h) (hints_cons _ _ _ (der_29142 v h) (by intro d hd; cases hd)))
def cl_29147 : CNF.NClause := [(47,false),(66,true),(16,true),(68,true),(75,true),(77,false),(89,false)]
theorem der_29147 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29147 :=
  CNF.rup_sound cl_29147 [cl_6064,cl_29143] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6064 v h) (hints_cons _ _ _ (der_29143 v h) (by intro d hd; cases hd)))
def cl_29148 : CNF.NClause := [(47,false),(16,true),(68,true),(75,false),(77,true),(84,true),(89,false)]
theorem der_29148 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29148 :=
  CNF.rup_sound cl_29148 [cl_6072,cl_26309] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6072 v h) (hints_cons _ _ _ (der_26309 v h) (by intro d hd; cases hd)))
def cl_29149 : CNF.NClause := [(47,false),(16,true),(68,true),(75,true),(77,true),(84,true),(89,false)]
theorem der_29149 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29149 :=
  CNF.rup_sound cl_29149 [cl_6080,cl_26309] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6080 v h) (hints_cons _ _ _ (der_26309 v h) (by intro d hd; cases hd)))
def cl_29150 : CNF.NClause := [(47,false),(66,true),(16,true),(68,true),(75,false),(77,false),(84,false)]
theorem der_29150 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29150 :=
  CNF.rup_sound cl_29150 [cl_6088,cl_29142] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6088 v h) (hints_cons _ _ _ (der_29142 v h) (by intro d hd; cases hd)))
def cl_29151 : CNF.NClause := [(47,false),(66,true),(16,true),(68,true),(75,true),(77,false),(84,false)]
theorem der_29151 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29151 :=
  CNF.rup_sound cl_29151 [cl_6096,cl_29143] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6096 v h) (hints_cons _ _ _ (der_29143 v h) (by intro d hd; cases hd)))
def cl_29152 : CNF.NClause := [(47,false),(66,true),(16,true),(68,true),(75,false),(77,true),(84,false)]
theorem der_29152 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29152 :=
  CNF.rup_sound cl_29152 [cl_6104,cl_29144] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6104 v h) (hints_cons _ _ _ (der_29144 v h) (by intro d hd; cases hd)))
def cl_29153 : CNF.NClause := [(47,false),(66,true),(16,true),(68,true),(77,true),(84,false),(89,true)]
theorem der_29153 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29153 :=
  CNF.rup_sound cl_29153 [cl_6112,cl_29152] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6112 v h) (hints_cons _ _ _ (der_29152 v h) (by intro d hd; cases hd)))
def cl_29154 : CNF.NClause := [(47,false),(16,true),(68,true),(75,false),(77,false),(84,true),(89,true)]
theorem der_29154 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29154 :=
  CNF.rup_sound cl_29154 [cl_6120,cl_26315] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6120 v h) (hints_cons _ _ _ (der_26315 v h) (by intro d hd; cases hd)))
def cl_29155 : CNF.NClause := [(47,false),(66,true),(16,true),(68,true),(77,false),(84,true),(89,true)]
theorem der_29155 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29155 :=
  CNF.rup_sound cl_29155 [cl_6128,cl_29154] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6128 v h) (hints_cons _ _ _ (der_29154 v h) (by intro d hd; cases hd)))
def cl_29156 : CNF.NClause := [(47,false),(66,true),(16,true),(68,true),(75,false),(77,true),(89,true)]
theorem der_29156 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29156 :=
  CNF.rup_sound cl_29156 [cl_6136,cl_29152] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6136 v h) (hints_cons _ _ _ (der_29152 v h) (by intro d hd; cases hd)))
def cl_29157 : CNF.NClause := [(47,false),(66,true),(16,true),(68,true),(77,true),(84,true),(89,true)]
theorem der_29157 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29157 :=
  CNF.rup_sound cl_29157 [cl_6144,cl_29156] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6144 v h) (hints_cons _ _ _ (der_29156 v h) (by intro d hd; cases hd)))
def cl_29158 : CNF.NClause := [(47,false),(16,false),(68,true),(75,false),(77,false),(84,false),(89,false)]
theorem der_29158 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29158 :=
  CNF.rup_sound cl_29158 [cl_6023,cl_29126] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6023 v h) (hints_cons _ _ _ (der_29126 v h) (by intro d hd; cases hd)))
def cl_29159 : CNF.NClause := [(47,false),(66,true),(16,false),(68,false),(77,false),(84,false),(89,false)]
theorem der_29159 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29159 :=
  CNF.rup_sound cl_29159 [cl_6027,cl_6019] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6027 v h) (hints_cons _ _ _ (inp_6019 v h) (by intro d hd; cases hd)))
def cl_29160 : CNF.NClause := [(47,false),(66,true),(68,true),(75,true),(77,false),(84,false),(89,false)]
theorem der_29160 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29160 :=
  CNF.rup_sound cl_29160 [cl_6031,cl_29143] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6031 v h) (hints_cons _ _ _ (der_29143 v h) (by intro d hd; cases hd)))
def cl_29161 : CNF.NClause := [(47,false),(16,false),(84,false),(75,false),(68,false),(77,true),(89,false)]
theorem der_29161 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29161 :=
  CNF.rup_sound cl_29161 [cl_6035,cl_26763] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6035 v h) (hints_cons _ _ _ (der_26763 v h) (by intro d hd; cases hd)))
def cl_29162 : CNF.NClause := [(47,false),(66,true),(68,true),(75,false),(77,true),(84,false),(89,false)]
theorem der_29162 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29162 :=
  CNF.rup_sound cl_29162 [cl_6039,cl_29152] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6039 v h) (hints_cons _ _ _ (der_29152 v h) (by intro d hd; cases hd)))
def cl_29163 : CNF.NClause := [(47,false),(16,false),(66,true),(68,false),(77,true),(84,false),(89,false)]
theorem der_29163 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29163 :=
  CNF.rup_sound cl_29163 [cl_6043,cl_29161] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6043 v h) (hints_cons _ _ _ (der_29161 v h) (by intro d hd; cases hd)))
def cl_29164 : CNF.NClause := [(47,false),(66,true),(68,true),(75,true),(77,true),(84,false),(89,false)]
theorem der_29164 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29164 :=
  CNF.rup_sound cl_29164 [cl_6047,cl_29145] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6047 v h) (hints_cons _ _ _ (der_29145 v h) (by intro d hd; cases hd)))
def cl_29165 : CNF.NClause := [(47,false),(84,true),(16,false),(75,false),(77,false),(68,false),(89,false)]
theorem der_29165 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29165 :=
  CNF.rup_sound cl_29165 [cl_6051,cl_29061] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6051 v h) (hints_cons _ _ _ (der_29061 v h) (by intro d hd; cases hd)))
def cl_29166 : CNF.NClause := [(47,false),(16,false),(68,true),(75,false),(77,false),(84,true),(89,false)]
theorem der_29166 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29166 :=
  CNF.rup_sound cl_29166 [cl_6055,cl_29130] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6055 v h) (hints_cons _ _ _ (der_29130 v h) (by intro d hd; cases hd)))
def cl_29167 : CNF.NClause := [(47,false),(84,true),(16,false),(66,true),(68,false),(77,false),(89,false)]
theorem der_29167 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29167 :=
  CNF.rup_sound cl_29167 [cl_6059,cl_29165] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6059 v h) (hints_cons _ _ _ (der_29165 v h) (by intro d hd; cases hd)))
def cl_29168 : CNF.NClause := [(47,false),(66,true),(16,false),(75,true),(77,false),(84,true),(89,false)]
theorem der_29168 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29168 :=
  CNF.rup_sound cl_29168 [cl_6063,cl_29167] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6063 v h) (hints_cons _ _ _ (der_29167 v h) (by intro d hd; cases hd)))
def cl_29169 : CNF.NClause := [(47,false),(84,true),(16,false),(66,true),(75,false),(89,false),(68,false)]
theorem der_29169 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29169 :=
  CNF.rup_sound cl_29169 [cl_6067,cl_29167] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6067 v h) (hints_cons _ _ _ (der_29167 v h) (by intro d hd; cases hd)))
def cl_29170 : CNF.NClause := [(47,false),(16,false),(68,true),(75,false),(77,true),(84,true),(89,false)]
theorem der_29170 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29170 :=
  CNF.rup_sound cl_29170 [cl_6071,cl_29132] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6071 v h) (hints_cons _ _ _ (der_29132 v h) (by intro d hd; cases hd)))
def cl_29171 : CNF.NClause := [(47,false),(75,true),(16,false),(66,true),(68,false),(84,true),(89,false)]
theorem der_29171 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29171 :=
  CNF.rup_sound cl_29171 [cl_6075,cl_29167] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6075 v h) (hints_cons _ _ _ (der_29167 v h) (by intro d hd; cases hd)))
def cl_29172 : CNF.NClause := [(47,false),(66,true),(16,false),(68,true),(75,true),(77,true),(89,false)]
theorem der_29172 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29172 :=
  CNF.rup_sound cl_29172 [cl_6079,cl_29164] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6079 v h) (hints_cons _ _ _ (der_29164 v h) (by intro d hd; cases hd)))
def cl_29173 : CNF.NClause := [(47,false),(66,true),(16,false),(75,false),(77,false),(68,false),(84,false)]
theorem der_29173 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29173 :=
  CNF.rup_sound cl_29173 [cl_6083,cl_6019] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6083 v h) (hints_cons _ _ _ (inp_6019 v h) (by intro d hd; cases hd)))
def cl_29174 : CNF.NClause := [(47,false),(16,false),(68,true),(75,false),(77,false),(84,false),(89,true)]
theorem der_29174 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29174 :=
  CNF.rup_sound cl_29174 [cl_6087,cl_29134] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6087 v h) (hints_cons _ _ _ (der_29134 v h) (by intro d hd; cases hd)))
def cl_29175 : CNF.NClause := [(47,false),(16,false),(66,true),(68,false),(77,false),(84,false),(89,true)]
theorem der_29175 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29175 :=
  CNF.rup_sound cl_29175 [cl_6091,cl_29173] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6091 v h) (hints_cons _ _ _ (der_29173 v h) (by intro d hd; cases hd)))
def cl_29176 : CNF.NClause := [(47,false),(66,true),(68,true),(75,true),(77,false),(84,false),(89,true)]
theorem der_29176 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29176 :=
  CNF.rup_sound cl_29176 [cl_6095,cl_29151] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6095 v h) (hints_cons _ _ _ (der_29151 v h) (by intro d hd; cases hd)))
def cl_29177 : CNF.NClause := [(47,false),(66,true),(16,false),(89,true),(75,false),(84,false),(68,false)]
theorem der_29177 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29177 :=
  CNF.rup_sound cl_29177 [cl_6099,cl_29173] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6099 v h) (hints_cons _ _ _ (der_29173 v h) (by intro d hd; cases hd)))
def cl_29179 : CNF.NClause := [(47,false),(75,true),(16,false),(66,true),(68,false),(77,true),(84,false)]
theorem der_29179 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29179 :=
  CNF.rup_sound cl_29179 [cl_6107,cl_29163] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6107 v h) (hints_cons _ _ _ (der_29163 v h) (by intro d hd; cases hd)))
def cl_29180 : CNF.NClause := [(47,false),(66,true),(16,false),(68,true),(75,true),(77,true),(84,false)]
theorem der_29180 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29180 :=
  CNF.rup_sound cl_29180 [cl_6111,cl_29164] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6111 v h) (hints_cons _ _ _ (der_29164 v h) (by intro d hd; cases hd)))
def cl_29181 : CNF.NClause := [(47,false),(84,true),(16,false),(66,true),(75,false),(77,false),(68,false)]
theorem der_29181 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29181 :=
  CNF.rup_sound cl_29181 [cl_6115,cl_29167] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6115 v h) (hints_cons _ _ _ (der_29167 v h) (by intro d hd; cases hd)))
def cl_29182 : CNF.NClause := [(47,false),(16,false),(68,true),(75,false),(77,false),(84,true),(89,true)]
theorem der_29182 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29182 :=
  CNF.rup_sound cl_29182 [cl_6119,cl_29138] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6119 v h) (hints_cons _ _ _ (der_29138 v h) (by intro d hd; cases hd)))
def cl_29183 : CNF.NClause := [(47,false),(84,true),(16,false),(66,true),(68,false),(77,false),(75,true)]
theorem der_29183 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29183 :=
  CNF.rup_sound cl_29183 [cl_6123,cl_29167] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6123 v h) (hints_cons _ _ _ (der_29167 v h) (by intro d hd; cases hd)))
def cl_29184 : CNF.NClause := [(47,false),(66,true),(68,true),(75,true),(77,false),(84,true),(89,true)]
theorem der_29184 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29184 :=
  CNF.rup_sound cl_29184 [cl_6127,cl_29155] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6127 v h) (hints_cons _ _ _ (der_29155 v h) (by intro d hd; cases hd)))
def cl_29185 : CNF.NClause := [(47,false),(16,false),(89,true),(75,false),(77,true),(84,true),(68,false)]
theorem der_29185 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29185 :=
  CNF.rup_sound cl_29185 [cl_6131,cl_29066] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6131 v h) (hints_cons _ _ _ (der_29066 v h) (by intro d hd; cases hd)))
def cl_29187 : CNF.NClause := [(47,false),(75,true),(16,false),(66,true),(68,false),(77,true),(89,true)]
theorem der_29187 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29187 :=
  CNF.rup_sound cl_29187 [cl_6139,cl_29179] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6139 v h) (hints_cons _ _ _ (der_29179 v h) (by intro d hd; cases hd)))
def cl_29188 : CNF.NClause := [(47,false),(66,true),(68,true),(75,true),(77,true),(84,true),(89,true)]
theorem der_29188 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29188 :=
  CNF.rup_sound cl_29188 [cl_6143,cl_29157] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6143 v h) (hints_cons _ _ _ (der_29157 v h) (by intro d hd; cases hd)))
def cl_29189 : CNF.NClause := [(52,false),(66,true),(21,false),(79,false),(67,false),(85,false),(88,false)]
theorem der_29189 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29189 :=
  CNF.rup_sound cl_29189 [cl_6667,cl_6659] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6667 v h) (hints_cons _ _ _ (inp_6659 v h) (by intro d hd; cases hd)))
def cl_29190 : CNF.NClause := [(52,false),(79,true),(21,false),(85,false),(67,false),(73,false),(88,false)]
theorem der_29190 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29190 :=
  CNF.rup_sound cl_29190 [cl_6675,cl_29074] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6675 v h) (hints_cons _ _ _ (der_29074 v h) (by intro d hd; cases hd)))
def cl_29191 : CNF.NClause := [(52,false),(21,false),(66,true),(73,true),(67,false),(85,false),(88,false)]
theorem der_29191 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29191 :=
  CNF.rup_sound cl_29191 [cl_6683,cl_29189] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6683 v h) (hints_cons _ _ _ (der_29189 v h) (by intro d hd; cases hd)))
def cl_29192 : CNF.NClause := [(52,false),(21,false),(85,true),(67,false),(79,false),(73,false),(88,false)]
theorem der_29192 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29192 :=
  CNF.rup_sound cl_29192 [cl_6691,cl_29056] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6691 v h) (hints_cons _ _ _ (der_29056 v h) (by intro d hd; cases hd)))
def cl_29193 : CNF.NClause := [(52,false),(88,false),(21,false),(66,true),(73,true),(67,false),(79,false)]
theorem der_29193 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29193 :=
  CNF.rup_sound cl_29193 [cl_6699,cl_29191] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6699 v h) (hints_cons _ _ _ (der_29191 v h) (by intro d hd; cases hd)))
def cl_29194 : CNF.NClause := [(52,false),(21,false),(85,true),(73,false),(79,true),(67,false),(88,false)]
theorem der_29194 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29194 :=
  CNF.rup_sound cl_29194 [cl_6707,cl_29067] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6707 v h) (hints_cons _ _ _ (der_29067 v h) (by intro d hd; cases hd)))
def cl_29195 : CNF.NClause := [(52,false),(79,true),(21,false),(66,true),(73,true),(67,false),(88,false)]
theorem der_29195 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29195 :=
  CNF.rup_sound cl_29195 [cl_6715,cl_29191] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6715 v h) (hints_cons _ _ _ (der_29191 v h) (by intro d hd; cases hd)))
def cl_29196 : CNF.NClause := [(52,false),(66,true),(21,false),(73,false),(79,false),(85,false),(67,false)]
theorem der_29196 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29196 :=
  CNF.rup_sound cl_29196 [cl_6723,cl_6659] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6723 v h) (hints_cons _ _ _ (inp_6659 v h) (by intro d hd; cases hd)))
def cl_29197 : CNF.NClause := [(52,false),(21,false),(66,true),(73,true),(67,false),(85,false),(79,false)]
theorem der_29197 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29197 :=
  CNF.rup_sound cl_29197 [cl_6731,cl_29191] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6731 v h) (hints_cons _ _ _ (der_29191 v h) (by intro d hd; cases hd)))
def cl_29198 : CNF.NClause := [(52,false),(21,false),(88,true),(73,false),(79,true),(85,false),(67,false)]
theorem der_29198 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29198 :=
  CNF.rup_sound cl_29198 [cl_6739,cl_29068] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6739 v h) (hints_cons _ _ _ (der_29068 v h) (by intro d hd; cases hd)))
def cl_29199 : CNF.NClause := [(52,false),(79,true),(21,false),(66,true),(73,true),(67,false),(85,false)]
theorem der_29199 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29199 :=
  CNF.rup_sound cl_29199 [cl_6747,cl_29191] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6747 v h) (hints_cons _ _ _ (der_29191 v h) (by intro d hd; cases hd)))
def cl_29200 : CNF.NClause := [(52,false),(21,false),(85,true),(73,false),(79,false),(67,false),(88,true)]
theorem der_29200 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29200 :=
  CNF.rup_sound cl_29200 [cl_6755,cl_29069] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6755 v h) (hints_cons _ _ _ (der_29069 v h) (by intro d hd; cases hd)))
def cl_29201 : CNF.NClause := [(52,false),(21,false),(66,true),(73,true),(67,false),(79,false),(85,true)]
theorem der_29201 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29201 :=
  CNF.rup_sound cl_29201 [cl_6763,cl_29193] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6763 v h) (hints_cons _ _ _ (der_29193 v h) (by intro d hd; cases hd)))
def cl_29202 : CNF.NClause := [(52,false),(21,false),(88,true),(73,false),(79,true),(85,true),(67,false)]
theorem der_29202 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29202 :=
  CNF.rup_sound cl_29202 [cl_6771,cl_29069] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6771 v h) (hints_cons _ _ _ (der_29069 v h) (by intro d hd; cases hd)))
def cl_29203 : CNF.NClause := [(52,false),(79,true),(21,false),(66,true),(73,true),(67,false),(85,true)]
theorem der_29203 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29203 :=
  CNF.rup_sound cl_29203 [cl_6779,cl_29195] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6779 v h) (hints_cons _ _ _ (der_29195 v h) (by intro d hd; cases hd)))
def cl_29204 : CNF.NClause := [(47,false),(66,true),(89,false),(75,false),(77,false),(84,false),(68,false)]
theorem der_29204 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29204 :=
  CNF.rup_sound cl_29204 [cl_6020,cl_29173] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6020 v h) (hints_cons _ _ _ (der_29173 v h) (by intro d hd; cases hd)))
def cl_29205 : CNF.NClause := [(47,false),(66,true),(16,true),(75,false),(89,false),(77,true),(84,false)]
theorem der_29205 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29205 :=
  CNF.rup_sound cl_29205 [cl_6036,cl_29152] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6036 v h) (hints_cons _ _ _ (der_29152 v h) (by intro d hd; cases hd)))
def cl_29206 : CNF.NClause := [(47,false),(16,true),(89,false),(84,true),(77,false),(75,false),(68,false)]
theorem der_29206 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29206 :=
  CNF.rup_sound cl_29206 [cl_6052,cl_29061] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6052 v h) (hints_cons _ _ _ (der_29061 v h) (by intro d hd; cases hd)))
def cl_29207 : CNF.NClause := [(47,false),(16,true),(68,false),(75,false),(89,false),(77,true),(84,true)]
theorem der_29207 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29207 :=
  CNF.rup_sound cl_29207 [cl_6068,cl_29065] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6068 v h) (hints_cons _ _ _ (der_29065 v h) (by intro d hd; cases hd)))
def cl_29208 : CNF.NClause := [(47,false),(66,true),(84,false),(89,true),(77,false),(75,false),(68,false)]
theorem der_29208 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29208 :=
  CNF.rup_sound cl_29208 [cl_6084,cl_29173] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6084 v h) (hints_cons _ _ _ (der_29173 v h) (by intro d hd; cases hd)))
def cl_29209 : CNF.NClause := [(47,false),(66,true),(16,true),(89,true),(77,true),(75,false),(84,false)]
theorem der_29209 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29209 :=
  CNF.rup_sound cl_29209 [cl_6100,cl_29152] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6100 v h) (hints_cons _ _ _ (der_29152 v h) (by intro d hd; cases hd)))
def cl_29210 : CNF.NClause := [(47,false),(84,true),(16,true),(66,true),(77,false),(75,false),(89,true)]
theorem der_29210 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29210 :=
  CNF.rup_sound cl_29210 [cl_6116,cl_29154] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6116 v h) (hints_cons _ _ _ (der_29154 v h) (by intro d hd; cases hd)))
def cl_29211 : CNF.NClause := [(47,false),(84,true),(16,true),(68,false),(77,true),(75,false),(89,true)]
theorem der_29211 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29211 :=
  CNF.rup_sound cl_29211 [cl_6132,cl_29066] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6132 v h) (hints_cons _ _ _ (der_29066 v h) (by intro d hd; cases hd)))
def cl_29212 : CNF.NClause := [(52,false),(66,true),(67,false),(88,false),(79,false),(73,false),(85,false)]
theorem der_29212 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29212 :=
  CNF.rup_sound cl_29212 [cl_6660,cl_6659] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6660 v h) (hints_cons _ _ _ (inp_6659 v h) (by intro d hd; cases hd)))
def cl_29213 : CNF.NClause := [(52,false),(21,true),(67,true),(73,false),(79,false),(85,false),(88,false)]
theorem der_29213 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29213 :=
  CNF.rup_sound cl_29213 [cl_6664,cl_26350] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6664 v h) (hints_cons _ _ _ (der_26350 v h) (by intro d hd; cases hd)))
def cl_29214 : CNF.NClause := [(52,false),(79,false),(66,true),(73,true),(67,false),(85,false),(88,false)]
theorem der_29214 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29214 :=
  CNF.rup_sound cl_29214 [cl_6668,cl_29191] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6668 v h) (hints_cons _ _ _ (der_29191 v h) (by intro d hd; cases hd)))
def cl_29215 : CNF.NClause := [(52,false),(79,false),(21,true),(67,true),(73,true),(85,false),(88,false)]
theorem der_29215 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29215 :=
  CNF.rup_sound cl_29215 [cl_6672,cl_26357] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6672 v h) (hints_cons _ _ _ (der_26357 v h) (by intro d hd; cases hd)))
def cl_29216 : CNF.NClause := [(52,false),(79,true),(21,true),(73,false),(88,false),(85,false),(67,false)]
theorem der_29216 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29216 :=
  CNF.rup_sound cl_29216 [cl_6676,cl_29074] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6676 v h) (hints_cons _ _ _ (der_29074 v h) (by intro d hd; cases hd)))
def cl_29217 : CNF.NClause := [(52,false),(21,true),(66,true),(73,false),(67,true),(85,false),(88,false)]
theorem der_29217 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29217 :=
  CNF.rup_sound cl_29217 [cl_6680,cl_29213] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6680 v h) (hints_cons _ _ _ (der_29213 v h) (by intro d hd; cases hd)))
def cl_29218 : CNF.NClause := [(52,false),(79,true),(66,true),(73,true),(67,false),(85,false),(88,false)]
theorem der_29218 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29218 :=
  CNF.rup_sound cl_29218 [cl_6684,cl_29191] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6684 v h) (hints_cons _ _ _ (der_29191 v h) (by intro d hd; cases hd)))
def cl_29219 : CNF.NClause := [(52,false),(21,true),(66,true),(67,true),(73,true),(85,false),(88,false)]
theorem der_29219 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29219 :=
  CNF.rup_sound cl_29219 [cl_6688,cl_29215] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6688 v h) (hints_cons _ _ _ (der_29215 v h) (by intro d hd; cases hd)))
def cl_29220 : CNF.NClause := [(52,false),(21,true),(85,true),(88,false),(79,false),(67,false),(73,false)]
theorem der_29220 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29220 :=
  CNF.rup_sound cl_29220 [cl_6692,cl_29056] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6692 v h) (hints_cons _ _ _ (der_29056 v h) (by intro d hd; cases hd)))
def cl_29221 : CNF.NClause := [(52,false),(66,true),(21,true),(67,true),(73,false),(79,false),(88,false)]
theorem der_29221 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29221 :=
  CNF.rup_sound cl_29221 [cl_6696,cl_29213] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6696 v h) (hints_cons _ _ _ (der_29213 v h) (by intro d hd; cases hd)))
def cl_29222 : CNF.NClause := [(52,false),(88,false),(66,true),(73,true),(67,false),(79,false),(85,true)]
theorem der_29222 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29222 :=
  CNF.rup_sound cl_29222 [cl_6700,cl_29193] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6700 v h) (hints_cons _ _ _ (der_29193 v h) (by intro d hd; cases hd)))
def cl_29223 : CNF.NClause := [(52,false),(88,false),(21,true),(67,true),(73,true),(79,false),(85,true)]
theorem der_29223 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29223 :=
  CNF.rup_sound cl_29223 [cl_6704,cl_26355] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6704 v h) (hints_cons _ _ _ (der_26355 v h) (by intro d hd; cases hd)))
def cl_29224 : CNF.NClause := [(52,false),(66,true),(85,true),(73,false),(79,true),(67,false),(88,false)]
theorem der_29224 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29224 :=
  CNF.rup_sound cl_29224 [cl_6708,cl_29194] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6708 v h) (hints_cons _ _ _ (der_29194 v h) (by intro d hd; cases hd)))
def cl_29225 : CNF.NClause := [(52,false),(79,true),(21,true),(66,true),(73,false),(67,true),(88,false)]
theorem der_29225 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29225 :=
  CNF.rup_sound cl_29225 [cl_6712,cl_29217] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6712 v h) (hints_cons _ _ _ (der_29217 v h) (by intro d hd; cases hd)))
def cl_29226 : CNF.NClause := [(52,false),(79,true),(66,true),(73,true),(67,false),(85,true),(88,false)]
theorem der_29226 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29226 :=
  CNF.rup_sound cl_29226 [cl_6716,cl_29195] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6716 v h) (hints_cons _ _ _ (der_29195 v h) (by intro d hd; cases hd)))
def cl_29227 : CNF.NClause := [(52,false),(79,true),(21,true),(66,true),(73,true),(85,true),(88,false)]
theorem der_29227 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29227 :=
  CNF.rup_sound cl_29227 [cl_6720,cl_29226] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6720 v h) (hints_cons _ _ _ (der_29226 v h) (by intro d hd; cases hd)))
def cl_29228 : CNF.NClause := [(52,false),(66,true),(88,true),(67,false),(79,false),(85,false),(73,false)]
theorem der_29228 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29228 :=
  CNF.rup_sound cl_29228 [cl_6724,cl_29196] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6724 v h) (hints_cons _ _ _ (der_29196 v h) (by intro d hd; cases hd)))
def cl_29229 : CNF.NClause := [(52,false),(66,true),(21,true),(88,true),(73,false),(79,false),(85,false)]
theorem der_29229 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29229 :=
  CNF.rup_sound cl_29229 [cl_6728,cl_29228] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6728 v h) (hints_cons _ _ _ (der_29228 v h) (by intro d hd; cases hd)))
def cl_29230 : CNF.NClause := [(52,false),(88,true),(66,true),(73,true),(67,false),(85,false),(79,false)]
theorem der_29230 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29230 :=
  CNF.rup_sound cl_29230 [cl_6732,cl_29197] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6732 v h) (hints_cons _ _ _ (der_29197 v h) (by intro d hd; cases hd)))
def cl_29231 : CNF.NClause := [(52,false),(88,true),(21,true),(66,true),(73,true),(85,false),(79,false)]
theorem der_29231 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29231 :=
  CNF.rup_sound cl_29231 [cl_6736,cl_29230] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6736 v h) (hints_cons _ _ _ (der_29230 v h) (by intro d hd; cases hd)))
def cl_29232 : CNF.NClause := [(52,false),(66,true),(21,true),(88,true),(67,false),(85,false),(73,false)]
theorem der_29232 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29232 :=
  CNF.rup_sound cl_29232 [cl_6740,cl_29228] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6740 v h) (hints_cons _ _ _ (der_29228 v h) (by intro d hd; cases hd)))
def cl_29233 : CNF.NClause := [(52,false),(79,true),(21,true),(66,true),(73,false),(67,true),(85,false)]
theorem der_29233 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29233 :=
  CNF.rup_sound cl_29233 [cl_6744,cl_29217] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6744 v h) (hints_cons _ _ _ (der_29217 v h) (by intro d hd; cases hd)))
def cl_29234 : CNF.NClause := [(52,false),(79,true),(66,true),(73,true),(67,false),(85,false),(88,true)]
theorem der_29234 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29234 :=
  CNF.rup_sound cl_29234 [cl_6748,cl_29199] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6748 v h) (hints_cons _ _ _ (der_29199 v h) (by intro d hd; cases hd)))
def cl_29235 : CNF.NClause := [(52,false),(79,true),(21,true),(66,true),(73,true),(85,false),(88,true)]
theorem der_29235 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29235 :=
  CNF.rup_sound cl_29235 [cl_6752,cl_29234] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6752 v h) (hints_cons _ _ _ (der_29234 v h) (by intro d hd; cases hd)))
def cl_29236 : CNF.NClause := [(52,false),(66,true),(21,true),(88,true),(67,false),(79,false),(73,false)]
theorem der_29236 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29236 :=
  CNF.rup_sound cl_29236 [cl_6756,cl_29228] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6756 v h) (hints_cons _ _ _ (der_29228 v h) (by intro d hd; cases hd)))
def cl_29237 : CNF.NClause := [(52,false),(66,true),(21,true),(73,false),(79,false),(85,true),(67,true)]
theorem der_29237 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29237 :=
  CNF.rup_sound cl_29237 [cl_6760,cl_29221] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6760 v h) (hints_cons _ _ _ (der_29221 v h) (by intro d hd; cases hd)))
def cl_29238 : CNF.NClause := [(52,false),(88,true),(66,true),(73,true),(67,false),(79,false),(85,true)]
theorem der_29238 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29238 :=
  CNF.rup_sound cl_29238 [cl_6764,cl_29201] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6764 v h) (hints_cons _ _ _ (der_29201 v h) (by intro d hd; cases hd)))
def cl_29239 : CNF.NClause := [(52,false),(88,true),(21,true),(66,true),(73,true),(79,false),(85,true)]
theorem der_29239 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29239 :=
  CNF.rup_sound cl_29239 [cl_6768,cl_29238] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6768 v h) (hints_cons _ _ _ (der_29238 v h) (by intro d hd; cases hd)))
def cl_29240 : CNF.NClause := [(52,false),(21,true),(88,true),(67,false),(79,true),(85,true),(73,false)]
theorem der_29240 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29240 :=
  CNF.rup_sound cl_29240 [cl_6772,cl_29077] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6772 v h) (hints_cons _ _ _ (der_29077 v h) (by intro d hd; cases hd)))
def cl_29241 : CNF.NClause := [(52,false),(79,true),(21,true),(66,true),(73,false),(85,true),(88,true)]
theorem der_29241 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29241 :=
  CNF.rup_sound cl_29241 [cl_6776,cl_29240] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6776 v h) (hints_cons _ _ _ (der_29240 v h) (by intro d hd; cases hd)))
def cl_29242 : CNF.NClause := [(52,false),(79,true),(66,true),(73,true),(67,false),(85,true),(88,true)]
theorem der_29242 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29242 :=
  CNF.rup_sound cl_29242 [cl_6780,cl_29203] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6780 v h) (hints_cons _ _ _ (der_29203 v h) (by intro d hd; cases hd)))
def cl_29243 : CNF.NClause := [(52,false),(79,true),(21,true),(66,true),(67,true),(73,true),(85,true)]
theorem der_29243 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29243 :=
  CNF.rup_sound cl_29243 [cl_6784,cl_29227] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6784 v h) (hints_cons _ _ _ (der_29227 v h) (by intro d hd; cases hd)))
def cl_29244 : CNF.NClause := [(44,false),(13,true),(72,false),(78,false),(88,false),(84,false),(71,false)]
theorem der_29244 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29244 :=
  CNF.rup_sound cl_29244 [cl_5636,cl_26761] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5636 v h) (hints_cons _ _ _ (der_26761 v h) (by intro d hd; cases hd)))
def cl_29245 : CNF.NClause := [(44,false),(84,false),(13,true),(65,true),(78,false),(72,false),(88,false)]
theorem der_29245 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29245 :=
  CNF.rup_sound cl_29245 [cl_5640,cl_29244] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5640 v h) (hints_cons _ _ _ (der_29244 v h) (by intro d hd; cases hd)))
def cl_29246 : CNF.NClause := [(44,false),(13,true),(84,false),(65,true),(71,false),(88,false),(78,false)]
theorem der_29246 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29246 :=
  CNF.rup_sound cl_29246 [cl_5644,cl_29244] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5644 v h) (hints_cons _ _ _ (der_29244 v h) (by intro d hd; cases hd)))
def cl_29247 : CNF.NClause := [(44,false),(13,true),(65,true),(71,true),(78,false),(84,false),(88,false)]
theorem der_29247 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29247 :=
  CNF.rup_sound cl_29247 [cl_5648,cl_29245] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5648 v h) (hints_cons _ _ _ (der_29245 v h) (by intro d hd; cases hd)))
def cl_29248 : CNF.NClause := [(44,false),(78,true),(13,true),(72,false),(71,false),(84,false),(88,false)]
theorem der_29248 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29248 :=
  CNF.rup_sound cl_29248 [cl_5652,cl_29086] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5652 v h) (hints_cons _ _ _ (der_29086 v h) (by intro d hd; cases hd)))
def cl_29249 : CNF.NClause := [(44,false),(13,true),(65,true),(72,false),(71,true),(84,false),(88,false)]
theorem der_29249 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29249 :=
  CNF.rup_sound cl_29249 [cl_5656,cl_29245] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5656 v h) (hints_cons _ _ _ (der_29245 v h) (by intro d hd; cases hd)))
def cl_29250 : CNF.NClause := [(44,false),(13,true),(65,true),(72,true),(71,false),(84,false),(88,false)]
theorem der_29250 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29250 :=
  CNF.rup_sound cl_29250 [cl_5660,cl_29246] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5660 v h) (hints_cons _ _ _ (der_29246 v h) (by intro d hd; cases hd)))
def cl_29251 : CNF.NClause := [(44,false),(78,true),(13,true),(65,true),(71,true),(84,false),(88,false)]
theorem der_29251 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29251 :=
  CNF.rup_sound cl_29251 [cl_5664,cl_29249] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5664 v h) (hints_cons _ _ _ (der_29249 v h) (by intro d hd; cases hd)))
def cl_29252 : CNF.NClause := [(44,false),(13,true),(78,false),(72,false),(71,false),(84,true),(88,false)]
theorem der_29252 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29252 :=
  CNF.rup_sound cl_29252 [cl_5668,cl_29058] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5668 v h) (hints_cons _ _ _ (der_29058 v h) (by intro d hd; cases hd)))
def cl_29253 : CNF.NClause := [(44,false),(13,true),(71,true),(65,true),(78,false),(72,false),(88,false)]
theorem der_29253 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29253 :=
  CNF.rup_sound cl_29253 [cl_5672,cl_29249] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5672 v h) (hints_cons _ _ _ (der_29249 v h) (by intro d hd; cases hd)))
def cl_29254 : CNF.NClause := [(44,false),(65,true),(13,true),(72,true),(71,false),(78,false),(88,false)]
theorem der_29254 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29254 :=
  CNF.rup_sound cl_29254 [cl_5676,cl_29246] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5676 v h) (hints_cons _ _ _ (der_29246 v h) (by intro d hd; cases hd)))
def cl_29255 : CNF.NClause := [(44,false),(84,true),(13,true),(65,true),(71,true),(78,false),(88,false)]
theorem der_29255 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29255 :=
  CNF.rup_sound cl_29255 [cl_5680,cl_29253] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5680 v h) (hints_cons _ _ _ (der_29253 v h) (by intro d hd; cases hd)))
def cl_29256 : CNF.NClause := [(44,false),(78,true),(13,true),(65,true),(72,false),(71,false),(88,false)]
theorem der_29256 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29256 :=
  CNF.rup_sound cl_29256 [cl_5684,cl_29248] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5684 v h) (hints_cons _ _ _ (der_29248 v h) (by intro d hd; cases hd)))
def cl_29257 : CNF.NClause := [(44,false),(78,true),(13,true),(65,true),(72,false),(71,true),(88,false)]
theorem der_29257 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29257 :=
  CNF.rup_sound cl_29257 [cl_5688,cl_29249] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5688 v h) (hints_cons _ _ _ (der_29249 v h) (by intro d hd; cases hd)))
def cl_29258 : CNF.NClause := [(44,false),(78,true),(13,true),(65,true),(72,true),(71,false),(88,false)]
theorem der_29258 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29258 :=
  CNF.rup_sound cl_29258 [cl_5692,cl_29250] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5692 v h) (hints_cons _ _ _ (der_29250 v h) (by intro d hd; cases hd)))
def cl_29259 : CNF.NClause := [(44,false),(78,true),(13,true),(65,true),(71,true),(72,true),(88,false)]
theorem der_29259 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29259 :=
  CNF.rup_sound cl_29259 [cl_5696,cl_29251] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5696 v h) (hints_cons _ _ _ (der_29251 v h) (by intro d hd; cases hd)))
def cl_29260 : CNF.NClause := [(44,false),(13,true),(65,true),(72,false),(71,false),(78,false),(84,false)]
theorem der_29260 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29260 :=
  CNF.rup_sound cl_29260 [cl_5700,cl_29244] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5700 v h) (hints_cons _ _ _ (der_29244 v h) (by intro d hd; cases hd)))
def cl_29261 : CNF.NClause := [(44,false),(13,true),(65,true),(72,false),(78,false),(71,true),(84,false)]
theorem der_29261 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29261 :=
  CNF.rup_sound cl_29261 [cl_5704,cl_29249] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5704 v h) (hints_cons _ _ _ (der_29249 v h) (by intro d hd; cases hd)))
def cl_29262 : CNF.NClause := [(44,false),(13,true),(65,true),(72,true),(71,false),(78,false),(84,false)]
theorem der_29262 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29262 :=
  CNF.rup_sound cl_29262 [cl_5708,cl_29246] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5708 v h) (hints_cons _ _ _ (der_29246 v h) (by intro d hd; cases hd)))
def cl_29263 : CNF.NClause := [(44,false),(88,true),(13,true),(65,true),(71,true),(78,false),(84,false)]
theorem der_29263 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29263 :=
  CNF.rup_sound cl_29263 [cl_5712,cl_29261] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5712 v h) (hints_cons _ _ _ (der_29261 v h) (by intro d hd; cases hd)))
def cl_29264 : CNF.NClause := [(44,false),(78,true),(13,true),(65,true),(72,false),(71,false),(84,false)]
theorem der_29264 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29264 :=
  CNF.rup_sound cl_29264 [cl_5716,cl_29248] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5716 v h) (hints_cons _ _ _ (der_29248 v h) (by intro d hd; cases hd)))
def cl_29265 : CNF.NClause := [(44,false),(78,true),(13,true),(65,true),(72,false),(71,true),(84,false)]
theorem der_29265 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29265 :=
  CNF.rup_sound cl_29265 [cl_5720,cl_29249] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5720 v h) (hints_cons _ _ _ (der_29249 v h) (by intro d hd; cases hd)))
def cl_29266 : CNF.NClause := [(44,false),(78,true),(13,true),(65,true),(72,true),(71,false),(84,false)]
theorem der_29266 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29266 :=
  CNF.rup_sound cl_29266 [cl_5724,cl_29250] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5724 v h) (hints_cons _ _ _ (der_29250 v h) (by intro d hd; cases hd)))
def cl_29267 : CNF.NClause := [(44,false),(78,true),(13,true),(65,true),(71,true),(72,true),(84,false)]
theorem der_29267 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29267 :=
  CNF.rup_sound cl_29267 [cl_5728,cl_29251] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5728 v h) (hints_cons _ _ _ (der_29251 v h) (by intro d hd; cases hd)))
def cl_29268 : CNF.NClause := [(44,false),(13,true),(65,true),(72,false),(71,false),(84,true),(78,false)]
theorem der_29268 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29268 :=
  CNF.rup_sound cl_29268 [cl_5732,cl_29252] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5732 v h) (hints_cons _ _ _ (der_29252 v h) (by intro d hd; cases hd)))
def cl_29269 : CNF.NClause := [(44,false),(13,true),(65,true),(72,false),(78,false),(84,true),(71,true)]
theorem der_29269 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29269 :=
  CNF.rup_sound cl_29269 [cl_5736,cl_29253] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5736 v h) (hints_cons _ _ _ (der_29253 v h) (by intro d hd; cases hd)))
def cl_29270 : CNF.NClause := [(44,false),(13,true),(65,true),(72,true),(71,false),(78,false),(84,true)]
theorem der_29270 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29270 :=
  CNF.rup_sound cl_29270 [cl_5740,cl_29254] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5740 v h) (hints_cons _ _ _ (der_29254 v h) (by intro d hd; cases hd)))
def cl_29271 : CNF.NClause := [(44,false),(84,true),(13,true),(65,true),(71,true),(78,false),(72,true)]
theorem der_29271 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29271 :=
  CNF.rup_sound cl_29271 [cl_5744,cl_29255] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5744 v h) (hints_cons _ _ _ (der_29255 v h) (by intro d hd; cases hd)))
def cl_29272 : CNF.NClause := [(44,false),(78,true),(13,true),(65,true),(72,false),(71,false),(84,true)]
theorem der_29272 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29272 :=
  CNF.rup_sound cl_29272 [cl_5748,cl_29256] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5748 v h) (hints_cons _ _ _ (der_29256 v h) (by intro d hd; cases hd)))
def cl_29273 : CNF.NClause := [(44,false),(78,true),(13,true),(65,true),(72,false),(71,true),(84,true)]
theorem der_29273 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29273 :=
  CNF.rup_sound cl_29273 [cl_5752,cl_29257] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5752 v h) (hints_cons _ _ _ (der_29257 v h) (by intro d hd; cases hd)))
def cl_29274 : CNF.NClause := [(44,false),(78,true),(13,true),(65,true),(71,false),(84,true),(88,true)]
theorem der_29274 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29274 :=
  CNF.rup_sound cl_29274 [cl_5756,cl_29272] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5756 v h) (hints_cons _ _ _ (der_29272 v h) (by intro d hd; cases hd)))
def cl_29275 : CNF.NClause := [(44,false),(78,true),(13,true),(65,true),(71,true),(72,true),(84,true)]
theorem der_29275 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29275 :=
  CNF.rup_sound cl_29275 [cl_5760,cl_29259] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5760 v h) (hints_cons _ _ _ (der_29259 v h) (by intro d hd; cases hd)))
def cl_29276 : CNF.NClause := [(49,false),(18,false),(65,true),(73,false),(77,false),(86,false),(91,false)]
theorem der_29276 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29276 :=
  CNF.rup_sound cl_29276 [cl_6279,cl_6275] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6279 v h) (hints_cons _ _ _ (inp_6275 v h) (by intro d hd; cases hd)))
def cl_29277 : CNF.NClause := [(49,false),(65,true),(18,false),(69,false),(77,false),(86,false),(91,false)]
theorem der_29277 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29277 :=
  CNF.rup_sound cl_29277 [cl_6283,cl_6275] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6283 v h) (hints_cons _ _ _ (inp_6275 v h) (by intro d hd; cases hd)))
def cl_29278 : CNF.NClause := [(49,false),(69,true),(18,false),(65,true),(77,false),(86,false),(91,false)]
theorem der_29278 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29278 :=
  CNF.rup_sound cl_29278 [cl_6287,cl_29276] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6287 v h) (hints_cons _ _ _ (der_29276 v h) (by intro d hd; cases hd)))
def cl_29279 : CNF.NClause := [(49,false),(18,false),(65,true),(73,false),(69,false),(86,false),(91,false)]
theorem der_29279 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29279 :=
  CNF.rup_sound cl_29279 [cl_6291,cl_6275] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6291 v h) (hints_cons _ _ _ (inp_6275 v h) (by intro d hd; cases hd)))
def cl_29280 : CNF.NClause := [(49,false),(69,true),(18,false),(65,true),(73,false),(86,false),(91,false)]
theorem der_29280 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29280 :=
  CNF.rup_sound cl_29280 [cl_6295,cl_29278] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6295 v h) (hints_cons _ _ _ (der_29278 v h) (by intro d hd; cases hd)))
def cl_29281 : CNF.NClause := [(49,false),(18,false),(65,true),(69,false),(73,true),(86,false),(91,false)]
theorem der_29281 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29281 :=
  CNF.rup_sound cl_29281 [cl_6299,cl_29277] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6299 v h) (hints_cons _ _ _ (der_29277 v h) (by intro d hd; cases hd)))
def cl_29282 : CNF.NClause := [(49,false),(69,true),(18,false),(65,true),(73,true),(86,false),(91,false)]
theorem der_29282 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29282 :=
  CNF.rup_sound cl_29282 [cl_6303,cl_29278] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6303 v h) (hints_cons _ _ _ (der_29278 v h) (by intro d hd; cases hd)))
def cl_29283 : CNF.NClause := [(49,false),(86,true),(18,false),(73,false),(77,false),(69,false),(91,false)]
theorem der_29283 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29283 :=
  CNF.rup_sound cl_29283 [cl_6307,cl_6305] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6307 v h) (hints_cons _ _ _ (inp_6305 v h) (by intro d hd; cases hd)))
def cl_29284 : CNF.NClause := [(49,false),(69,true),(18,false),(65,true),(73,false),(77,false),(91,false)]
theorem der_29284 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29284 :=
  CNF.rup_sound cl_29284 [cl_6311,cl_29278] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6311 v h) (hints_cons _ _ _ (der_29278 v h) (by intro d hd; cases hd)))
def cl_29285 : CNF.NClause := [(49,false),(65,true),(18,false),(91,false),(69,false),(77,false),(73,true)]
theorem der_29285 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29285 :=
  CNF.rup_sound cl_29285 [cl_6315,cl_29277] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6315 v h) (hints_cons _ _ _ (der_29277 v h) (by intro d hd; cases hd)))
def cl_29286 : CNF.NClause := [(49,false),(69,true),(18,false),(65,true),(73,true),(77,false),(91,false)]
theorem der_29286 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29286 :=
  CNF.rup_sound cl_29286 [cl_6319,cl_29278] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6319 v h) (hints_cons _ _ _ (der_29278 v h) (by intro d hd; cases hd)))
def cl_29287 : CNF.NClause := [(49,false),(18,false),(91,false),(73,false),(77,true),(69,false),(86,true)]
theorem der_29287 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29287 :=
  CNF.rup_sound cl_29287 [cl_6323,cl_29051] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6323 v h) (hints_cons _ _ _ (der_29051 v h) (by intro d hd; cases hd)))
def cl_29288 : CNF.NClause := [(49,false),(69,true),(18,false),(65,true),(73,false),(77,true),(91,false)]
theorem der_29288 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29288 :=
  CNF.rup_sound cl_29288 [cl_6327,cl_29280] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6327 v h) (hints_cons _ _ _ (der_29280 v h) (by intro d hd; cases hd)))
def cl_29289 : CNF.NClause := [(49,false),(77,true),(18,false),(65,true),(69,false),(73,true),(91,false)]
theorem der_29289 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29289 :=
  CNF.rup_sound cl_29289 [cl_6331,cl_29281] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6331 v h) (hints_cons _ _ _ (der_29281 v h) (by intro d hd; cases hd)))
def cl_29290 : CNF.NClause := [(49,false),(69,true),(18,false),(65,true),(73,true),(77,true),(91,false)]
theorem der_29290 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29290 :=
  CNF.rup_sound cl_29290 [cl_6335,cl_29282] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6335 v h) (hints_cons _ _ _ (der_29282 v h) (by intro d hd; cases hd)))
def cl_29291 : CNF.NClause := [(49,false),(18,false),(69,false),(73,false),(77,false),(86,false),(91,true)]
theorem der_29291 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29291 :=
  CNF.rup_sound cl_29291 [cl_6339,cl_29038] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6339 v h) (hints_cons _ _ _ (der_29038 v h) (by intro d hd; cases hd)))
def cl_29292 : CNF.NClause := [(49,false),(69,true),(18,false),(65,true),(73,false),(77,false),(86,false)]
theorem der_29292 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29292 :=
  CNF.rup_sound cl_29292 [cl_6343,cl_29278] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6343 v h) (hints_cons _ _ _ (der_29278 v h) (by intro d hd; cases hd)))
def cl_29293 : CNF.NClause := [(49,false),(18,false),(65,true),(69,false),(77,false),(86,false),(73,true)]
theorem der_29293 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29293 :=
  CNF.rup_sound cl_29293 [cl_6347,cl_29277] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6347 v h) (hints_cons _ _ _ (der_29277 v h) (by intro d hd; cases hd)))
def cl_29294 : CNF.NClause := [(49,false),(69,true),(18,false),(65,true),(73,true),(77,false),(86,false)]
theorem der_29294 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29294 :=
  CNF.rup_sound cl_29294 [cl_6351,cl_29278] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6351 v h) (hints_cons _ _ _ (der_29278 v h) (by intro d hd; cases hd)))
def cl_29295 : CNF.NClause := [(49,false),(65,true),(18,false),(73,false),(77,true),(86,false),(69,false)]
theorem der_29295 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29295 :=
  CNF.rup_sound cl_29295 [cl_6355,cl_29279] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6355 v h) (hints_cons _ _ _ (der_29279 v h) (by intro d hd; cases hd)))
def cl_29296 : CNF.NClause := [(49,false),(69,true),(18,false),(65,true),(73,false),(77,true),(86,false)]
theorem der_29296 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29296 :=
  CNF.rup_sound cl_29296 [cl_6359,cl_29280] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6359 v h) (hints_cons _ _ _ (der_29280 v h) (by intro d hd; cases hd)))
def cl_29297 : CNF.NClause := [(49,false),(77,true),(18,false),(65,true),(69,false),(73,true),(86,false)]
theorem der_29297 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29297 :=
  CNF.rup_sound cl_29297 [cl_6363,cl_29281] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6363 v h) (hints_cons _ _ _ (der_29281 v h) (by intro d hd; cases hd)))
def cl_29298 : CNF.NClause := [(49,false),(69,true),(18,false),(65,true),(73,true),(77,true),(86,false)]
theorem der_29298 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29298 :=
  CNF.rup_sound cl_29298 [cl_6367,cl_29282] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6367 v h) (hints_cons _ _ _ (der_29282 v h) (by intro d hd; cases hd)))
def cl_29299 : CNF.NClause := [(49,false),(86,true),(18,false),(73,false),(77,false),(69,false),(91,true)]
theorem der_29299 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29299 :=
  CNF.rup_sound cl_29299 [cl_6371,cl_29041] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6371 v h) (hints_cons _ _ _ (der_29041 v h) (by intro d hd; cases hd)))
def cl_29300 : CNF.NClause := [(49,false),(69,true),(18,false),(65,true),(73,false),(77,false),(86,true)]
theorem der_29300 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29300 :=
  CNF.rup_sound cl_29300 [cl_6375,cl_29284] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6375 v h) (hints_cons _ _ _ (der_29284 v h) (by intro d hd; cases hd)))
def cl_29301 : CNF.NClause := [(49,false),(86,true),(18,false),(65,true),(69,false),(77,false),(73,true)]
theorem der_29301 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29301 :=
  CNF.rup_sound cl_29301 [cl_6379,cl_29285] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6379 v h) (hints_cons _ _ _ (der_29285 v h) (by intro d hd; cases hd)))
def cl_29302 : CNF.NClause := [(49,false),(69,true),(18,false),(65,true),(73,true),(77,false),(86,true)]
theorem der_29302 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29302 :=
  CNF.rup_sound cl_29302 [cl_6383,cl_29286] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6383 v h) (hints_cons _ _ _ (der_29286 v h) (by intro d hd; cases hd)))
def cl_29303 : CNF.NClause := [(49,false),(86,true),(18,false),(73,false),(77,true),(69,false),(91,true)]
theorem der_29303 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29303 :=
  CNF.rup_sound cl_29303 [cl_6387,cl_29052] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6387 v h) (hints_cons _ _ _ (der_29052 v h) (by intro d hd; cases hd)))
def cl_29304 : CNF.NClause := [(49,false),(69,true),(18,false),(65,true),(73,false),(77,true),(86,true)]
theorem der_29304 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29304 :=
  CNF.rup_sound cl_29304 [cl_6391,cl_29288] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6391 v h) (hints_cons _ _ _ (der_29288 v h) (by intro d hd; cases hd)))
def cl_29306 : CNF.NClause := [(49,false),(69,true),(18,false),(65,true),(73,true),(77,true),(86,true)]
theorem der_29306 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29306 :=
  CNF.rup_sound cl_29306 [cl_6399,cl_29290] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6399 v h) (hints_cons _ _ _ (der_29290 v h) (by intro d hd; cases hd)))
def cl_29307 : CNF.NClause := [(44,false),(65,true),(84,false),(78,false),(88,false),(71,false),(72,false)]
theorem der_29307 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29307 :=
  CNF.rup_sound cl_29307 [cl_5635,cl_29244] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5635 v h) (hints_cons _ _ _ (der_29244 v h) (by intro d hd; cases hd)))
def cl_29308 : CNF.NClause := [(44,false),(65,true),(71,true),(72,false),(88,false),(84,false),(78,false)]
theorem der_29308 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29308 :=
  CNF.rup_sound cl_29308 [cl_5639,cl_29249] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5639 v h) (hints_cons _ _ _ (der_29249 v h) (by intro d hd; cases hd)))
def cl_29309 : CNF.NClause := [(44,false),(72,true),(88,false),(65,true),(71,false),(78,false),(84,false)]
theorem der_29309 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29309 :=
  CNF.rup_sound cl_29309 [cl_5643,cl_29246] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5643 v h) (hints_cons _ _ _ (der_29246 v h) (by intro d hd; cases hd)))
def cl_29310 : CNF.NClause := [(44,false),(72,true),(65,true),(71,true),(78,false),(84,false),(88,false)]
theorem der_29310 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29310 :=
  CNF.rup_sound cl_29310 [cl_5647,cl_29247] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5647 v h) (hints_cons _ _ _ (der_29247 v h) (by intro d hd; cases hd)))
def cl_29311 : CNF.NClause := [(44,false),(78,true),(13,false),(72,false),(71,false),(84,false),(88,false)]
theorem der_29311 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29311 :=
  CNF.rup_sound cl_29311 [cl_5651,cl_29086] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5651 v h) (hints_cons _ _ _ (der_29086 v h) (by intro d hd; cases hd)))
def cl_29312 : CNF.NClause := [(44,false),(78,true),(65,true),(72,false),(71,true),(84,false),(88,false)]
theorem der_29312 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29312 :=
  CNF.rup_sound cl_29312 [cl_5655,cl_29249] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5655 v h) (hints_cons _ _ _ (der_29249 v h) (by intro d hd; cases hd)))
def cl_29313 : CNF.NClause := [(44,false),(78,true),(65,true),(72,true),(71,false),(84,false),(88,false)]
theorem der_29313 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29313 :=
  CNF.rup_sound cl_29313 [cl_5659,cl_29250] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5659 v h) (hints_cons _ _ _ (der_29250 v h) (by intro d hd; cases hd)))
def cl_29314 : CNF.NClause := [(44,false),(78,true),(65,true),(71,true),(72,true),(84,false),(88,false)]
theorem der_29314 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29314 :=
  CNF.rup_sound cl_29314 [cl_5663,cl_29251] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5663 v h) (hints_cons _ _ _ (der_29251 v h) (by intro d hd; cases hd)))
def cl_29315 : CNF.NClause := [(44,false),(13,false),(78,false),(72,false),(71,false),(88,false),(84,true)]
theorem der_29315 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29315 :=
  CNF.rup_sound cl_29315 [cl_5667,cl_29058] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5667 v h) (hints_cons _ _ _ (der_29058 v h) (by intro d hd; cases hd)))
def cl_29316 : CNF.NClause := [(44,false),(84,true),(71,true),(65,true),(78,false),(72,false),(88,false)]
theorem der_29316 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29316 :=
  CNF.rup_sound cl_29316 [cl_5671,cl_29253] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5671 v h) (hints_cons _ _ _ (der_29253 v h) (by intro d hd; cases hd)))
def cl_29317 : CNF.NClause := [(44,false),(72,true),(78,false),(65,true),(71,false),(88,false),(84,true)]
theorem der_29317 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29317 :=
  CNF.rup_sound cl_29317 [cl_5675,cl_29254] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5675 v h) (hints_cons _ _ _ (der_29254 v h) (by intro d hd; cases hd)))
def cl_29318 : CNF.NClause := [(44,false),(84,true),(65,true),(71,true),(78,false),(72,true),(88,false)]
theorem der_29318 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29318 :=
  CNF.rup_sound cl_29318 [cl_5679,cl_29255] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5679 v h) (hints_cons _ _ _ (der_29255 v h) (by intro d hd; cases hd)))
def cl_29319 : CNF.NClause := [(44,false),(78,true),(65,true),(72,false),(71,false),(84,true),(88,false)]
theorem der_29319 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29319 :=
  CNF.rup_sound cl_29319 [cl_5683,cl_29272] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5683 v h) (hints_cons _ _ _ (der_29272 v h) (by intro d hd; cases hd)))
def cl_29320 : CNF.NClause := [(44,false),(78,true),(65,true),(72,false),(71,true),(84,true),(88,false)]
theorem der_29320 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29320 :=
  CNF.rup_sound cl_29320 [cl_5687,cl_29257] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5687 v h) (hints_cons _ _ _ (der_29257 v h) (by intro d hd; cases hd)))
def cl_29321 : CNF.NClause := [(44,false),(78,true),(65,true),(72,true),(71,false),(84,true),(88,false)]
theorem der_29321 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29321 :=
  CNF.rup_sound cl_29321 [cl_5691,cl_29258] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5691 v h) (hints_cons _ _ _ (der_29258 v h) (by intro d hd; cases hd)))
def cl_29322 : CNF.NClause := [(44,false),(78,true),(65,true),(71,true),(72,true),(84,true),(88,false)]
theorem der_29322 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29322 :=
  CNF.rup_sound cl_29322 [cl_5695,cl_29259] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5695 v h) (hints_cons _ _ _ (der_29259 v h) (by intro d hd; cases hd)))
def cl_29323 : CNF.NClause := [(44,false),(13,false),(65,true),(72,false),(71,false),(84,false),(78,false)]
theorem der_29323 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29323 :=
  CNF.rup_sound cl_29323 [cl_5699,cl_29307] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5699 v h) (hints_cons _ _ _ (der_29307 v h) (by intro d hd; cases hd)))
def cl_29324 : CNF.NClause := [(44,false),(88,true),(65,true),(72,false),(78,false),(71,true),(84,false)]
theorem der_29324 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29324 :=
  CNF.rup_sound cl_29324 [cl_5703,cl_29261] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5703 v h) (hints_cons _ _ _ (der_29261 v h) (by intro d hd; cases hd)))
def cl_29325 : CNF.NClause := [(44,false),(13,false),(65,true),(72,true),(71,false),(78,false),(84,false)]
theorem der_29325 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29325 :=
  CNF.rup_sound cl_29325 [cl_5707,cl_29309] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5707 v h) (hints_cons _ _ _ (der_29309 v h) (by intro d hd; cases hd)))
def cl_29326 : CNF.NClause := [(44,false),(88,true),(65,true),(71,true),(78,false),(84,false),(72,true)]
theorem der_29326 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29326 :=
  CNF.rup_sound cl_29326 [cl_5711,cl_29263] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5711 v h) (hints_cons _ _ _ (der_29263 v h) (by intro d hd; cases hd)))
def cl_29327 : CNF.NClause := [(44,false),(78,true),(65,true),(72,false),(71,false),(84,false),(88,true)]
theorem der_29327 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29327 :=
  CNF.rup_sound cl_29327 [cl_5715,cl_29264] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5715 v h) (hints_cons _ _ _ (der_29264 v h) (by intro d hd; cases hd)))
def cl_29328 : CNF.NClause := [(44,false),(78,true),(65,true),(72,false),(71,true),(84,false),(88,true)]
theorem der_29328 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29328 :=
  CNF.rup_sound cl_29328 [cl_5719,cl_29265] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5719 v h) (hints_cons _ _ _ (der_29265 v h) (by intro d hd; cases hd)))
def cl_29329 : CNF.NClause := [(44,false),(78,true),(65,true),(72,true),(71,false),(84,false),(88,true)]
theorem der_29329 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29329 :=
  CNF.rup_sound cl_29329 [cl_5723,cl_29266] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5723 v h) (hints_cons _ _ _ (der_29266 v h) (by intro d hd; cases hd)))
def cl_29330 : CNF.NClause := [(44,false),(78,true),(65,true),(71,true),(72,true),(84,false),(88,true)]
theorem der_29330 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29330 :=
  CNF.rup_sound cl_29330 [cl_5727,cl_29267] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5727 v h) (hints_cons _ _ _ (der_29267 v h) (by intro d hd; cases hd)))
def cl_29331 : CNF.NClause := [(44,false),(88,true),(65,true),(72,false),(71,false),(84,true),(78,false)]
theorem der_29331 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29331 :=
  CNF.rup_sound cl_29331 [cl_5731,cl_29268] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5731 v h) (hints_cons _ _ _ (der_29268 v h) (by intro d hd; cases hd)))
def cl_29333 : CNF.NClause := [(44,false),(13,false),(65,true),(72,true),(71,false),(84,true),(78,false)]
theorem der_29333 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29333 :=
  CNF.rup_sound cl_29333 [cl_5739,cl_29317] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5739 v h) (hints_cons _ _ _ (der_29317 v h) (by intro d hd; cases hd)))
def cl_29334 : CNF.NClause := [(44,false),(84,true),(13,false),(65,true),(71,true),(78,false),(72,true)]
theorem der_29334 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29334 :=
  CNF.rup_sound cl_29334 [cl_5743,cl_29318] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5743 v h) (hints_cons _ _ _ (der_29318 v h) (by intro d hd; cases hd)))
def cl_29335 : CNF.NClause := [(44,false),(78,true),(65,true),(72,false),(71,false),(84,true),(88,true)]
theorem der_29335 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29335 :=
  CNF.rup_sound cl_29335 [cl_5747,cl_29272] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5747 v h) (hints_cons _ _ _ (der_29272 v h) (by intro d hd; cases hd)))
def cl_29336 : CNF.NClause := [(44,false),(78,true),(65,true),(72,false),(71,true),(84,true),(88,true)]
theorem der_29336 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29336 :=
  CNF.rup_sound cl_29336 [cl_5751,cl_29273] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5751 v h) (hints_cons _ _ _ (der_29273 v h) (by intro d hd; cases hd)))
def cl_29338 : CNF.NClause := [(44,false),(78,true),(65,true),(71,true),(72,true),(84,true),(88,true)]
theorem der_29338 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29338 :=
  CNF.rup_sound cl_29338 [cl_5759,cl_29275] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5759 v h) (hints_cons _ _ _ (der_29275 v h) (by intro d hd; cases hd)))
def cl_29339 : CNF.NClause := [(49,false),(65,true),(69,false),(91,false),(77,false),(86,false),(73,false)]
theorem der_29339 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29339 :=
  CNF.rup_sound cl_29339 [cl_6276,cl_6275] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6276 v h) (hints_cons _ _ _ (inp_6275 v h) (by intro d hd; cases hd)))
def cl_29340 : CNF.NClause := [(49,false),(69,true),(65,true),(73,false),(77,false),(86,false),(91,false)]
theorem der_29340 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29340 :=
  CNF.rup_sound cl_29340 [cl_6280,cl_29278] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6280 v h) (hints_cons _ _ _ (der_29278 v h) (by intro d hd; cases hd)))
def cl_29341 : CNF.NClause := [(49,false),(65,true),(69,false),(73,true),(91,false),(86,false),(77,false)]
theorem der_29341 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29341 :=
  CNF.rup_sound cl_29341 [cl_6284,cl_29277] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6284 v h) (hints_cons _ _ _ (der_29277 v h) (by intro d hd; cases hd)))
def cl_29342 : CNF.NClause := [(49,false),(69,true),(65,true),(73,true),(77,false),(86,false),(91,false)]
theorem der_29342 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29342 :=
  CNF.rup_sound cl_29342 [cl_6288,cl_29278] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6288 v h) (hints_cons _ _ _ (der_29278 v h) (by intro d hd; cases hd)))
def cl_29343 : CNF.NClause := [(49,false),(77,true),(18,true),(69,false),(73,false),(86,false),(91,false)]
theorem der_29343 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29343 :=
  CNF.rup_sound cl_29343 [cl_6292,cl_26729] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6292 v h) (hints_cons _ _ _ (der_26729 v h) (by intro d hd; cases hd)))
def cl_29344 : CNF.NClause := [(49,false),(69,true),(65,true),(73,false),(77,true),(86,false),(91,false)]
theorem der_29344 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29344 :=
  CNF.rup_sound cl_29344 [cl_6296,cl_29280] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6296 v h) (hints_cons _ _ _ (der_29280 v h) (by intro d hd; cases hd)))
def cl_29345 : CNF.NClause := [(49,false),(77,true),(69,false),(73,true),(65,true),(86,false),(91,false)]
theorem der_29345 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29345 :=
  CNF.rup_sound cl_29345 [cl_6300,cl_29281] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6300 v h) (hints_cons _ _ _ (der_29281 v h) (by intro d hd; cases hd)))
def cl_29346 : CNF.NClause := [(49,false),(69,true),(65,true),(73,true),(77,true),(86,false),(91,false)]
theorem der_29346 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29346 :=
  CNF.rup_sound cl_29346 [cl_6304,cl_29282] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6304 v h) (hints_cons _ _ _ (der_29282 v h) (by intro d hd; cases hd)))
def cl_29347 : CNF.NClause := [(49,false),(65,true),(69,false),(86,true),(77,false),(73,false),(91,false)]
theorem der_29347 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29347 :=
  CNF.rup_sound cl_29347 [cl_6308,cl_29283] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6308 v h) (hints_cons _ _ _ (der_29283 v h) (by intro d hd; cases hd)))
def cl_29348 : CNF.NClause := [(49,false),(69,true),(65,true),(73,false),(77,false),(86,true),(91,false)]
theorem der_29348 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29348 :=
  CNF.rup_sound cl_29348 [cl_6312,cl_29284] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6312 v h) (hints_cons _ _ _ (der_29284 v h) (by intro d hd; cases hd)))
def cl_29349 : CNF.NClause := [(49,false),(65,true),(69,false),(73,true),(77,false),(86,true),(91,false)]
theorem der_29349 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29349 :=
  CNF.rup_sound cl_29349 [cl_6316,cl_29285] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6316 v h) (hints_cons _ _ _ (der_29285 v h) (by intro d hd; cases hd)))
def cl_29350 : CNF.NClause := [(49,false),(69,true),(65,true),(73,true),(77,false),(86,true),(91,false)]
theorem der_29350 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29350 :=
  CNF.rup_sound cl_29350 [cl_6320,cl_29286] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6320 v h) (hints_cons _ _ _ (der_29286 v h) (by intro d hd; cases hd)))
def cl_29351 : CNF.NClause := [(49,false),(77,true),(18,true),(69,false),(73,false),(86,true),(91,false)]
theorem der_29351 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29351 :=
  CNF.rup_sound cl_29351 [cl_6324,cl_29051] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6324 v h) (hints_cons _ _ _ (der_29051 v h) (by intro d hd; cases hd)))
def cl_29352 : CNF.NClause := [(49,false),(69,true),(65,true),(73,false),(77,true),(86,true),(91,false)]
theorem der_29352 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29352 :=
  CNF.rup_sound cl_29352 [cl_6328,cl_29288] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6328 v h) (hints_cons _ _ _ (der_29288 v h) (by intro d hd; cases hd)))
def cl_29353 : CNF.NClause := [(49,false),(77,true),(18,true),(69,false),(73,true),(65,true),(91,false)]
theorem der_29353 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29353 :=
  CNF.rup_sound cl_29353 [cl_6332,cl_29345] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6332 v h) (hints_cons _ _ _ (der_29345 v h) (by intro d hd; cases hd)))
def cl_29354 : CNF.NClause := [(49,false),(69,true),(65,true),(73,true),(77,true),(86,true),(91,false)]
theorem der_29354 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29354 :=
  CNF.rup_sound cl_29354 [cl_6336,cl_29290] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6336 v h) (hints_cons _ _ _ (der_29290 v h) (by intro d hd; cases hd)))
def cl_29355 : CNF.NClause := [(49,false),(18,true),(86,false),(69,false),(77,false),(73,false),(91,true)]
theorem der_29355 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29355 :=
  CNF.rup_sound cl_29355 [cl_6340,cl_29038] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6340 v h) (hints_cons _ _ _ (der_29038 v h) (by intro d hd; cases hd)))
def cl_29356 : CNF.NClause := [(49,false),(69,true),(65,true),(73,false),(77,false),(86,false),(91,true)]
theorem der_29356 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29356 :=
  CNF.rup_sound cl_29356 [cl_6344,cl_29292] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6344 v h) (hints_cons _ _ _ (der_29292 v h) (by intro d hd; cases hd)))
def cl_29357 : CNF.NClause := [(49,false),(65,true),(69,false),(73,true),(77,false),(86,false),(91,true)]
theorem der_29357 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29357 :=
  CNF.rup_sound cl_29357 [cl_6348,cl_29293] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6348 v h) (hints_cons _ _ _ (der_29293 v h) (by intro d hd; cases hd)))
def cl_29358 : CNF.NClause := [(49,false),(69,true),(65,true),(73,true),(77,false),(86,false),(91,true)]
theorem der_29358 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29358 :=
  CNF.rup_sound cl_29358 [cl_6352,cl_29294] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6352 v h) (hints_cons _ _ _ (der_29294 v h) (by intro d hd; cases hd)))
def cl_29359 : CNF.NClause := [(49,false),(77,true),(18,true),(69,false),(73,false),(86,false),(91,true)]
theorem der_29359 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29359 :=
  CNF.rup_sound cl_29359 [cl_6356,cl_26729] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6356 v h) (hints_cons _ _ _ (der_26729 v h) (by intro d hd; cases hd)))
def cl_29360 : CNF.NClause := [(49,false),(69,true),(65,true),(73,false),(77,true),(86,false),(91,true)]
theorem der_29360 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29360 :=
  CNF.rup_sound cl_29360 [cl_6360,cl_29296] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6360 v h) (hints_cons _ _ _ (der_29296 v h) (by intro d hd; cases hd)))
def cl_29361 : CNF.NClause := [(49,false),(77,true),(18,true),(69,false),(73,true),(65,true),(86,false)]
theorem der_29361 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29361 :=
  CNF.rup_sound cl_29361 [cl_6364,cl_29345] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6364 v h) (hints_cons _ _ _ (der_29345 v h) (by intro d hd; cases hd)))
def cl_29362 : CNF.NClause := [(49,false),(69,true),(65,true),(73,true),(77,true),(86,false),(91,true)]
theorem der_29362 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29362 :=
  CNF.rup_sound cl_29362 [cl_6368,cl_29298] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6368 v h) (hints_cons _ _ _ (der_29298 v h) (by intro d hd; cases hd)))
def cl_29363 : CNF.NClause := [(49,false),(69,false),(86,true),(65,true),(77,false),(73,false),(91,true)]
theorem der_29363 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29363 :=
  CNF.rup_sound cl_29363 [cl_6372,cl_29299] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6372 v h) (hints_cons _ _ _ (der_29299 v h) (by intro d hd; cases hd)))
def cl_29364 : CNF.NClause := [(49,false),(69,true),(65,true),(73,false),(77,false),(86,true),(91,true)]
theorem der_29364 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29364 :=
  CNF.rup_sound cl_29364 [cl_6376,cl_29300] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6376 v h) (hints_cons _ _ _ (der_29300 v h) (by intro d hd; cases hd)))
def cl_29365 : CNF.NClause := [(49,false),(65,true),(69,false),(73,true),(77,false),(86,true),(91,true)]
theorem der_29365 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29365 :=
  CNF.rup_sound cl_29365 [cl_6380,cl_29301] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6380 v h) (hints_cons _ _ _ (der_29301 v h) (by intro d hd; cases hd)))
def cl_29366 : CNF.NClause := [(49,false),(69,true),(18,true),(65,true),(73,true),(77,false),(86,true)]
theorem der_29366 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29366 :=
  CNF.rup_sound cl_29366 [cl_6384,cl_29350] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6384 v h) (hints_cons _ _ _ (der_29350 v h) (by intro d hd; cases hd)))
def cl_29367 : CNF.NClause := [(49,false),(77,true),(69,false),(65,true),(73,false),(86,true),(91,true)]
theorem der_29367 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29367 :=
  CNF.rup_sound cl_29367 [cl_6388,cl_29303] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6388 v h) (hints_cons _ _ _ (der_29303 v h) (by intro d hd; cases hd)))
def cl_29368 : CNF.NClause := [(49,false),(69,true),(18,true),(65,true),(73,false),(77,true),(91,true)]
theorem der_29368 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29368 :=
  CNF.rup_sound cl_29368 [cl_6392,cl_29360] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6392 v h) (hints_cons _ _ _ (der_29360 v h) (by intro d hd; cases hd)))
def cl_29369 : CNF.NClause := [(49,false),(77,true),(18,true),(69,false),(73,true),(65,true),(86,true)]
theorem der_29369 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_29369 :=
  CNF.rup_sound cl_29369 [cl_6396,cl_29353] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6396 v h) (hints_cons _ _ _ (der_29353 v h) (by intro d hd; cases hd)))
def chunk013 : List CNF.NClause := [cl_28855,cl_28856,cl_28857,cl_28858,cl_28859,cl_28860,cl_28861,cl_28862,cl_28863,cl_28864,cl_28865,cl_28866,cl_28867,cl_28868,cl_28869,cl_28870,cl_28871,cl_28872,cl_28873,cl_28874,cl_28875,cl_28876,cl_28877,cl_28878,cl_28879,cl_28880,cl_28881,cl_28882,cl_28883,cl_28884,cl_28885,cl_28886,cl_28887,cl_28888,cl_28889,cl_28890,cl_28891,cl_28892,cl_28893,cl_28894,cl_28895,cl_28896,cl_28897,cl_28898,cl_28899,cl_28900,cl_28901,cl_28903,cl_28904,cl_28905,cl_28906,cl_28907,cl_28908,cl_28909,cl_28910,cl_28911,cl_28912,cl_28914,cl_28916,cl_28917,cl_28918,cl_28919,cl_28920,cl_28921,cl_28922,cl_28923,cl_28924,cl_28925,cl_28926,cl_28927,cl_28928,cl_28929,cl_28930,cl_28931,cl_28932,cl_28933,cl_28934,cl_28935,cl_28936,cl_28937,cl_28939,cl_28940,cl_28941,cl_28942,cl_28943,cl_28944,cl_28945,cl_28946,cl_28947,cl_28948,cl_28949,cl_28950,cl_28951,cl_28952,cl_28953,cl_28954,cl_28955,cl_28956,cl_28957,cl_28958,cl_28959,cl_28960,cl_28961,cl_28962,cl_28963,cl_28964,cl_28966,cl_28967,cl_28968,cl_28971,cl_28972,cl_28973,cl_28974,cl_28975,cl_28976,cl_28977,cl_28978,cl_28979,cl_28980,cl_28981,cl_28982,cl_28983,cl_28984,cl_28985,cl_28986,cl_28987,cl_28988,cl_28989,cl_28990,cl_28991,cl_28992,cl_28993,cl_28994,cl_28995,cl_28996,cl_28997,cl_28998,cl_28999,cl_29000,cl_29001,cl_29002,cl_29003,cl_29004,cl_29005,cl_29006,cl_29007,cl_29008,cl_29009,cl_29010,cl_29011,cl_29012,cl_29013,cl_29014,cl_29015,cl_29016,cl_29017,cl_29018,cl_29019,cl_29020,cl_29021,cl_29022,cl_29023,cl_29024,cl_29025,cl_29026,cl_29027,cl_29028,cl_29029,cl_29030,cl_29031,cl_29034,cl_29035,cl_29036,cl_29037,cl_29038,cl_29039,cl_29040,cl_29041,cl_29042,cl_29043,cl_29044,cl_29045,cl_29046,cl_29047,cl_29048,cl_29049,cl_29050,cl_29051,cl_29052,cl_29053,cl_29054,cl_29055,cl_29056,cl_29057,cl_29058,cl_29059,cl_29060,cl_29061,cl_29062,cl_29063,cl_29064,cl_29065,cl_29066,cl_29067,cl_29068,cl_29069,cl_29070,cl_29071,cl_29072,cl_29073,cl_29074,cl_29075,cl_29076,cl_29077,cl_29078,cl_29079,cl_29080,cl_29081,cl_29082,cl_29083,cl_29084,cl_29085,cl_29086,cl_29087,cl_29088,cl_29089,cl_29090,cl_29091,cl_29092,cl_29093,cl_29094,cl_29095,cl_29096,cl_29097,cl_29098,cl_29099,cl_29100,cl_29101,cl_29102,cl_29103,cl_29104,cl_29105,cl_29106,cl_29107,cl_29108,cl_29110,cl_29111,cl_29112,cl_29113,cl_29114,cl_29115,cl_29116,cl_29117,cl_29118,cl_29119,cl_29120,cl_29121,cl_29122,cl_29123,cl_29124,cl_29125,cl_29126,cl_29127,cl_29128,cl_29129,cl_29130,cl_29131,cl_29132,cl_29133,cl_29134,cl_29135,cl_29136,cl_29137,cl_29138,cl_29139,cl_29140,cl_29141,cl_29142,cl_29143,cl_29144,cl_29145,cl_29146,cl_29147,cl_29148,cl_29149,cl_29150,cl_29151,cl_29152,cl_29153,cl_29154,cl_29155,cl_29156,cl_29157,cl_29158,cl_29159,cl_29160,cl_29161,cl_29162,cl_29163,cl_29164,cl_29165,cl_29166,cl_29167,cl_29168,cl_29169,cl_29170,cl_29171,cl_29172,cl_29173,cl_29174,cl_29175,cl_29176,cl_29177,cl_29179,cl_29180,cl_29181,cl_29182,cl_29183,cl_29184,cl_29185,cl_29187,cl_29188,cl_29189,cl_29190,cl_29191,cl_29192,cl_29193,cl_29194,cl_29195,cl_29196,cl_29197,cl_29198,cl_29199,cl_29200,cl_29201,cl_29202,cl_29203,cl_29204,cl_29205,cl_29206,cl_29207,cl_29208,cl_29209,cl_29210,cl_29211,cl_29212,cl_29213,cl_29214,cl_29215,cl_29216,cl_29217,cl_29218,cl_29219,cl_29220,cl_29221,cl_29222,cl_29223,cl_29224,cl_29225,cl_29226,cl_29227,cl_29228,cl_29229,cl_29230,cl_29231,cl_29232,cl_29233,cl_29234,cl_29235,cl_29236,cl_29237,cl_29238,cl_29239,cl_29240,cl_29241,cl_29242,cl_29243,cl_29244,cl_29245,cl_29246,cl_29247,cl_29248,cl_29249,cl_29250,cl_29251,cl_29252,cl_29253,cl_29254,cl_29255,cl_29256,cl_29257,cl_29258,cl_29259,cl_29260,cl_29261,cl_29262,cl_29263,cl_29264,cl_29265,cl_29266,cl_29267,cl_29268,cl_29269,cl_29270,cl_29271,cl_29272,cl_29273,cl_29274,cl_29275,cl_29276,cl_29277,cl_29278,cl_29279,cl_29280,cl_29281,cl_29282,cl_29283,cl_29284,cl_29285,cl_29286,cl_29287,cl_29288,cl_29289,cl_29290,cl_29291,cl_29292,cl_29293,cl_29294,cl_29295,cl_29296,cl_29297,cl_29298,cl_29299,cl_29300,cl_29301,cl_29302,cl_29303,cl_29304,cl_29306,cl_29307,cl_29308,cl_29309,cl_29310,cl_29311,cl_29312,cl_29313,cl_29314,cl_29315,cl_29316,cl_29317,cl_29318,cl_29319,cl_29320,cl_29321,cl_29322,cl_29323,cl_29324,cl_29325,cl_29326,cl_29327,cl_29328,cl_29329,cl_29330,cl_29331,cl_29333,cl_29334,cl_29335,cl_29336,cl_29338,cl_29339,cl_29340,cl_29341,cl_29342,cl_29343,cl_29344,cl_29345,cl_29346,cl_29347,cl_29348,cl_29349,cl_29350,cl_29351,cl_29352,cl_29353,cl_29354,cl_29355,cl_29356,cl_29357,cl_29358,cl_29359,cl_29360,cl_29361,cl_29362,cl_29363,cl_29364,cl_29365,cl_29366,cl_29367,cl_29368,cl_29369]
theorem chunk_sound013 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : ∀ c ∈ chunk013, CNF.Holds (v ∘ decodeVar) c :=
  (hints_cons _ _ _ (der_28855 v h) (hints_cons _ _ _ (der_28856 v h) (hints_cons _ _ _ (der_28857 v h) (hints_cons _ _ _ (der_28858 v h) (hints_cons _ _ _ (der_28859 v h) (hints_cons _ _ _ (der_28860 v h) (hints_cons _ _ _ (der_28861 v h) (hints_cons _ _ _ (der_28862 v h) (hints_cons _ _ _ (der_28863 v h) (hints_cons _ _ _ (der_28864 v h) (hints_cons _ _ _ (der_28865 v h) (hints_cons _ _ _ (der_28866 v h) (hints_cons _ _ _ (der_28867 v h) (hints_cons _ _ _ (der_28868 v h) (hints_cons _ _ _ (der_28869 v h) (hints_cons _ _ _ (der_28870 v h) (hints_cons _ _ _ (der_28871 v h) (hints_cons _ _ _ (der_28872 v h) (hints_cons _ _ _ (der_28873 v h) (hints_cons _ _ _ (der_28874 v h) (hints_cons _ _ _ (der_28875 v h) (hints_cons _ _ _ (der_28876 v h) (hints_cons _ _ _ (der_28877 v h) (hints_cons _ _ _ (der_28878 v h) (hints_cons _ _ _ (der_28879 v h) (hints_cons _ _ _ (der_28880 v h) (hints_cons _ _ _ (der_28881 v h) (hints_cons _ _ _ (der_28882 v h) (hints_cons _ _ _ (der_28883 v h) (hints_cons _ _ _ (der_28884 v h) (hints_cons _ _ _ (der_28885 v h) (hints_cons _ _ _ (der_28886 v h) (hints_cons _ _ _ (der_28887 v h) (hints_cons _ _ _ (der_28888 v h) (hints_cons _ _ _ (der_28889 v h) (hints_cons _ _ _ (der_28890 v h) (hints_cons _ _ _ (der_28891 v h) (hints_cons _ _ _ (der_28892 v h) (hints_cons _ _ _ (der_28893 v h) (hints_cons _ _ _ (der_28894 v h) (hints_cons _ _ _ (der_28895 v h) (hints_cons _ _ _ (der_28896 v h) (hints_cons _ _ _ (der_28897 v h) (hints_cons _ _ _ (der_28898 v h) (hints_cons _ _ _ (der_28899 v h) (hints_cons _ _ _ (der_28900 v h) (hints_cons _ _ _ (der_28901 v h) (hints_cons _ _ _ (der_28903 v h) (hints_cons _ _ _ (der_28904 v h) (hints_cons _ _ _ (der_28905 v h) (hints_cons _ _ _ (der_28906 v h) (hints_cons _ _ _ (der_28907 v h) (hints_cons _ _ _ (der_28908 v h) (hints_cons _ _ _ (der_28909 v h) (hints_cons _ _ _ (der_28910 v h) (hints_cons _ _ _ (der_28911 v h) (hints_cons _ _ _ (der_28912 v h) (hints_cons _ _ _ (der_28914 v h) (hints_cons _ _ _ (der_28916 v h) (hints_cons _ _ _ (der_28917 v h) (hints_cons _ _ _ (der_28918 v h) (hints_cons _ _ _ (der_28919 v h) (hints_cons _ _ _ (der_28920 v h) (hints_cons _ _ _ (der_28921 v h) (hints_cons _ _ _ (der_28922 v h) (hints_cons _ _ _ (der_28923 v h) (hints_cons _ _ _ (der_28924 v h) (hints_cons _ _ _ (der_28925 v h) (hints_cons _ _ _ (der_28926 v h) (hints_cons _ _ _ (der_28927 v h) (hints_cons _ _ _ (der_28928 v h) (hints_cons _ _ _ (der_28929 v h) (hints_cons _ _ _ (der_28930 v h) (hints_cons _ _ _ (der_28931 v h) (hints_cons _ _ _ (der_28932 v h) (hints_cons _ _ _ (der_28933 v h) (hints_cons _ _ _ (der_28934 v h) (hints_cons _ _ _ (der_28935 v h) (hints_cons _ _ _ (der_28936 v h) (hints_cons _ _ _ (der_28937 v h) (hints_cons _ _ _ (der_28939 v h) (hints_cons _ _ _ (der_28940 v h) (hints_cons _ _ _ (der_28941 v h) (hints_cons _ _ _ (der_28942 v h) (hints_cons _ _ _ (der_28943 v h) (hints_cons _ _ _ (der_28944 v h) (hints_cons _ _ _ (der_28945 v h) (hints_cons _ _ _ (der_28946 v h) (hints_cons _ _ _ (der_28947 v h) (hints_cons _ _ _ (der_28948 v h) (hints_cons _ _ _ (der_28949 v h) (hints_cons _ _ _ (der_28950 v h) (hints_cons _ _ _ (der_28951 v h) (hints_cons _ _ _ (der_28952 v h) (hints_cons _ _ _ (der_28953 v h) (hints_cons _ _ _ (der_28954 v h) (hints_cons _ _ _ (der_28955 v h) (hints_cons _ _ _ (der_28956 v h) (hints_cons _ _ _ (der_28957 v h) (hints_cons _ _ _ (der_28958 v h) (hints_cons _ _ _ (der_28959 v h) (hints_cons _ _ _ (der_28960 v h) (hints_cons _ _ _ (der_28961 v h) (hints_cons _ _ _ (der_28962 v h) (hints_cons _ _ _ (der_28963 v h) (hints_cons _ _ _ (der_28964 v h) (hints_cons _ _ _ (der_28966 v h) (hints_cons _ _ _ (der_28967 v h) (hints_cons _ _ _ (der_28968 v h) (hints_cons _ _ _ (der_28971 v h) (hints_cons _ _ _ (der_28972 v h) (hints_cons _ _ _ (der_28973 v h) (hints_cons _ _ _ (der_28974 v h) (hints_cons _ _ _ (der_28975 v h) (hints_cons _ _ _ (der_28976 v h) (hints_cons _ _ _ (der_28977 v h) (hints_cons _ _ _ (der_28978 v h) (hints_cons _ _ _ (der_28979 v h) (hints_cons _ _ _ (der_28980 v h) (hints_cons _ _ _ (der_28981 v h) (hints_cons _ _ _ (der_28982 v h) (hints_cons _ _ _ (der_28983 v h) (hints_cons _ _ _ (der_28984 v h) (hints_cons _ _ _ (der_28985 v h) (hints_cons _ _ _ (der_28986 v h) (hints_cons _ _ _ (der_28987 v h) (hints_cons _ _ _ (der_28988 v h) (hints_cons _ _ _ (der_28989 v h) (hints_cons _ _ _ (der_28990 v h) (hints_cons _ _ _ (der_28991 v h) (hints_cons _ _ _ (der_28992 v h) (hints_cons _ _ _ (der_28993 v h) (hints_cons _ _ _ (der_28994 v h) (hints_cons _ _ _ (der_28995 v h) (hints_cons _ _ _ (der_28996 v h) (hints_cons _ _ _ (der_28997 v h) (hints_cons _ _ _ (der_28998 v h) (hints_cons _ _ _ (der_28999 v h) (hints_cons _ _ _ (der_29000 v h) (hints_cons _ _ _ (der_29001 v h) (hints_cons _ _ _ (der_29002 v h) (hints_cons _ _ _ (der_29003 v h) (hints_cons _ _ _ (der_29004 v h) (hints_cons _ _ _ (der_29005 v h) (hints_cons _ _ _ (der_29006 v h) (hints_cons _ _ _ (der_29007 v h) (hints_cons _ _ _ (der_29008 v h) (hints_cons _ _ _ (der_29009 v h) (hints_cons _ _ _ (der_29010 v h) (hints_cons _ _ _ (der_29011 v h) (hints_cons _ _ _ (der_29012 v h) (hints_cons _ _ _ (der_29013 v h) (hints_cons _ _ _ (der_29014 v h) (hints_cons _ _ _ (der_29015 v h) (hints_cons _ _ _ (der_29016 v h) (hints_cons _ _ _ (der_29017 v h) (hints_cons _ _ _ (der_29018 v h) (hints_cons _ _ _ (der_29019 v h) (hints_cons _ _ _ (der_29020 v h) (hints_cons _ _ _ (der_29021 v h) (hints_cons _ _ _ (der_29022 v h) (hints_cons _ _ _ (der_29023 v h) (hints_cons _ _ _ (der_29024 v h) (hints_cons _ _ _ (der_29025 v h) (hints_cons _ _ _ (der_29026 v h) (hints_cons _ _ _ (der_29027 v h) (hints_cons _ _ _ (der_29028 v h) (hints_cons _ _ _ (der_29029 v h) (hints_cons _ _ _ (der_29030 v h) (hints_cons _ _ _ (der_29031 v h) (hints_cons _ _ _ (der_29034 v h) (hints_cons _ _ _ (der_29035 v h) (hints_cons _ _ _ (der_29036 v h) (hints_cons _ _ _ (der_29037 v h) (hints_cons _ _ _ (der_29038 v h) (hints_cons _ _ _ (der_29039 v h) (hints_cons _ _ _ (der_29040 v h) (hints_cons _ _ _ (der_29041 v h) (hints_cons _ _ _ (der_29042 v h) (hints_cons _ _ _ (der_29043 v h) (hints_cons _ _ _ (der_29044 v h) (hints_cons _ _ _ (der_29045 v h) (hints_cons _ _ _ (der_29046 v h) (hints_cons _ _ _ (der_29047 v h) (hints_cons _ _ _ (der_29048 v h) (hints_cons _ _ _ (der_29049 v h) (hints_cons _ _ _ (der_29050 v h) (hints_cons _ _ _ (der_29051 v h) (hints_cons _ _ _ (der_29052 v h) (hints_cons _ _ _ (der_29053 v h) (hints_cons _ _ _ (der_29054 v h) (hints_cons _ _ _ (der_29055 v h) (hints_cons _ _ _ (der_29056 v h) (hints_cons _ _ _ (der_29057 v h) (hints_cons _ _ _ (der_29058 v h) (hints_cons _ _ _ (der_29059 v h) (hints_cons _ _ _ (der_29060 v h) (hints_cons _ _ _ (der_29061 v h) (hints_cons _ _ _ (der_29062 v h) (hints_cons _ _ _ (der_29063 v h) (hints_cons _ _ _ (der_29064 v h) (hints_cons _ _ _ (der_29065 v h) (hints_cons _ _ _ (der_29066 v h) (hints_cons _ _ _ (der_29067 v h) (hints_cons _ _ _ (der_29068 v h) (hints_cons _ _ _ (der_29069 v h) (hints_cons _ _ _ (der_29070 v h) (hints_cons _ _ _ (der_29071 v h) (hints_cons _ _ _ (der_29072 v h) (hints_cons _ _ _ (der_29073 v h) (hints_cons _ _ _ (der_29074 v h) (hints_cons _ _ _ (der_29075 v h) (hints_cons _ _ _ (der_29076 v h) (hints_cons _ _ _ (der_29077 v h) (hints_cons _ _ _ (der_29078 v h) (hints_cons _ _ _ (der_29079 v h) (hints_cons _ _ _ (der_29080 v h) (hints_cons _ _ _ (der_29081 v h) (hints_cons _ _ _ (der_29082 v h) (hints_cons _ _ _ (der_29083 v h) (hints_cons _ _ _ (der_29084 v h) (hints_cons _ _ _ (der_29085 v h) (hints_cons _ _ _ (der_29086 v h) (hints_cons _ _ _ (der_29087 v h) (hints_cons _ _ _ (der_29088 v h) (hints_cons _ _ _ (der_29089 v h) (hints_cons _ _ _ (der_29090 v h) (hints_cons _ _ _ (der_29091 v h) (hints_cons _ _ _ (der_29092 v h) (hints_cons _ _ _ (der_29093 v h) (hints_cons _ _ _ (der_29094 v h) (hints_cons _ _ _ (der_29095 v h) (hints_cons _ _ _ (der_29096 v h) (hints_cons _ _ _ (der_29097 v h) (hints_cons _ _ _ (der_29098 v h) (hints_cons _ _ _ (der_29099 v h) (hints_cons _ _ _ (der_29100 v h) (hints_cons _ _ _ (der_29101 v h) (hints_cons _ _ _ (der_29102 v h) (hints_cons _ _ _ (der_29103 v h) (hints_cons _ _ _ (der_29104 v h) (hints_cons _ _ _ (der_29105 v h) (hints_cons _ _ _ (der_29106 v h) (hints_cons _ _ _ (der_29107 v h) (hints_cons _ _ _ (der_29108 v h) (hints_cons _ _ _ (der_29110 v h) (hints_cons _ _ _ (der_29111 v h) (hints_cons _ _ _ (der_29112 v h) (hints_cons _ _ _ (der_29113 v h) (hints_cons _ _ _ (der_29114 v h) (hints_cons _ _ _ (der_29115 v h) (hints_cons _ _ _ (der_29116 v h) (hints_cons _ _ _ (der_29117 v h) (hints_cons _ _ _ (der_29118 v h) (hints_cons _ _ _ (der_29119 v h) (hints_cons _ _ _ (der_29120 v h) (hints_cons _ _ _ (der_29121 v h) (hints_cons _ _ _ (der_29122 v h) (hints_cons _ _ _ (der_29123 v h) (hints_cons _ _ _ (der_29124 v h) (hints_cons _ _ _ (der_29125 v h) (hints_cons _ _ _ (der_29126 v h) (hints_cons _ _ _ (der_29127 v h) (hints_cons _ _ _ (der_29128 v h) (hints_cons _ _ _ (der_29129 v h) (hints_cons _ _ _ (der_29130 v h) (hints_cons _ _ _ (der_29131 v h) (hints_cons _ _ _ (der_29132 v h) (hints_cons _ _ _ (der_29133 v h) (hints_cons _ _ _ (der_29134 v h) (hints_cons _ _ _ (der_29135 v h) (hints_cons _ _ _ (der_29136 v h) (hints_cons _ _ _ (der_29137 v h) (hints_cons _ _ _ (der_29138 v h) (hints_cons _ _ _ (der_29139 v h) (hints_cons _ _ _ (der_29140 v h) (hints_cons _ _ _ (der_29141 v h) (hints_cons _ _ _ (der_29142 v h) (hints_cons _ _ _ (der_29143 v h) (hints_cons _ _ _ (der_29144 v h) (hints_cons _ _ _ (der_29145 v h) (hints_cons _ _ _ (der_29146 v h) (hints_cons _ _ _ (der_29147 v h) (hints_cons _ _ _ (der_29148 v h) (hints_cons _ _ _ (der_29149 v h) (hints_cons _ _ _ (der_29150 v h) (hints_cons _ _ _ (der_29151 v h) (hints_cons _ _ _ (der_29152 v h) (hints_cons _ _ _ (der_29153 v h) (hints_cons _ _ _ (der_29154 v h) (hints_cons _ _ _ (der_29155 v h) (hints_cons _ _ _ (der_29156 v h) (hints_cons _ _ _ (der_29157 v h) (hints_cons _ _ _ (der_29158 v h) (hints_cons _ _ _ (der_29159 v h) (hints_cons _ _ _ (der_29160 v h) (hints_cons _ _ _ (der_29161 v h) (hints_cons _ _ _ (der_29162 v h) (hints_cons _ _ _ (der_29163 v h) (hints_cons _ _ _ (der_29164 v h) (hints_cons _ _ _ (der_29165 v h) (hints_cons _ _ _ (der_29166 v h) (hints_cons _ _ _ (der_29167 v h) (hints_cons _ _ _ (der_29168 v h) (hints_cons _ _ _ (der_29169 v h) (hints_cons _ _ _ (der_29170 v h) (hints_cons _ _ _ (der_29171 v h) (hints_cons _ _ _ (der_29172 v h) (hints_cons _ _ _ (der_29173 v h) (hints_cons _ _ _ (der_29174 v h) (hints_cons _ _ _ (der_29175 v h) (hints_cons _ _ _ (der_29176 v h) (hints_cons _ _ _ (der_29177 v h) (hints_cons _ _ _ (der_29179 v h) (hints_cons _ _ _ (der_29180 v h) (hints_cons _ _ _ (der_29181 v h) (hints_cons _ _ _ (der_29182 v h) (hints_cons _ _ _ (der_29183 v h) (hints_cons _ _ _ (der_29184 v h) (hints_cons _ _ _ (der_29185 v h) (hints_cons _ _ _ (der_29187 v h) (hints_cons _ _ _ (der_29188 v h) (hints_cons _ _ _ (der_29189 v h) (hints_cons _ _ _ (der_29190 v h) (hints_cons _ _ _ (der_29191 v h) (hints_cons _ _ _ (der_29192 v h) (hints_cons _ _ _ (der_29193 v h) (hints_cons _ _ _ (der_29194 v h) (hints_cons _ _ _ (der_29195 v h) (hints_cons _ _ _ (der_29196 v h) (hints_cons _ _ _ (der_29197 v h) (hints_cons _ _ _ (der_29198 v h) (hints_cons _ _ _ (der_29199 v h) (hints_cons _ _ _ (der_29200 v h) (hints_cons _ _ _ (der_29201 v h) (hints_cons _ _ _ (der_29202 v h) (hints_cons _ _ _ (der_29203 v h) (hints_cons _ _ _ (der_29204 v h) (hints_cons _ _ _ (der_29205 v h) (hints_cons _ _ _ (der_29206 v h) (hints_cons _ _ _ (der_29207 v h) (hints_cons _ _ _ (der_29208 v h) (hints_cons _ _ _ (der_29209 v h) (hints_cons _ _ _ (der_29210 v h) (hints_cons _ _ _ (der_29211 v h) (hints_cons _ _ _ (der_29212 v h) (hints_cons _ _ _ (der_29213 v h) (hints_cons _ _ _ (der_29214 v h) (hints_cons _ _ _ (der_29215 v h) (hints_cons _ _ _ (der_29216 v h) (hints_cons _ _ _ (der_29217 v h) (hints_cons _ _ _ (der_29218 v h) (hints_cons _ _ _ (der_29219 v h) (hints_cons _ _ _ (der_29220 v h) (hints_cons _ _ _ (der_29221 v h) (hints_cons _ _ _ (der_29222 v h) (hints_cons _ _ _ (der_29223 v h) (hints_cons _ _ _ (der_29224 v h) (hints_cons _ _ _ (der_29225 v h) (hints_cons _ _ _ (der_29226 v h) (hints_cons _ _ _ (der_29227 v h) (hints_cons _ _ _ (der_29228 v h) (hints_cons _ _ _ (der_29229 v h) (hints_cons _ _ _ (der_29230 v h) (hints_cons _ _ _ (der_29231 v h) (hints_cons _ _ _ (der_29232 v h) (hints_cons _ _ _ (der_29233 v h) (hints_cons _ _ _ (der_29234 v h) (hints_cons _ _ _ (der_29235 v h) (hints_cons _ _ _ (der_29236 v h) (hints_cons _ _ _ (der_29237 v h) (hints_cons _ _ _ (der_29238 v h) (hints_cons _ _ _ (der_29239 v h) (hints_cons _ _ _ (der_29240 v h) (hints_cons _ _ _ (der_29241 v h) (hints_cons _ _ _ (der_29242 v h) (hints_cons _ _ _ (der_29243 v h) (hints_cons _ _ _ (der_29244 v h) (hints_cons _ _ _ (der_29245 v h) (hints_cons _ _ _ (der_29246 v h) (hints_cons _ _ _ (der_29247 v h) (hints_cons _ _ _ (der_29248 v h) (hints_cons _ _ _ (der_29249 v h) (hints_cons _ _ _ (der_29250 v h) (hints_cons _ _ _ (der_29251 v h) (hints_cons _ _ _ (der_29252 v h) (hints_cons _ _ _ (der_29253 v h) (hints_cons _ _ _ (der_29254 v h) (hints_cons _ _ _ (der_29255 v h) (hints_cons _ _ _ (der_29256 v h) (hints_cons _ _ _ (der_29257 v h) (hints_cons _ _ _ (der_29258 v h) (hints_cons _ _ _ (der_29259 v h) (hints_cons _ _ _ (der_29260 v h) (hints_cons _ _ _ (der_29261 v h) (hints_cons _ _ _ (der_29262 v h) (hints_cons _ _ _ (der_29263 v h) (hints_cons _ _ _ (der_29264 v h) (hints_cons _ _ _ (der_29265 v h) (hints_cons _ _ _ (der_29266 v h) (hints_cons _ _ _ (der_29267 v h) (hints_cons _ _ _ (der_29268 v h) (hints_cons _ _ _ (der_29269 v h) (hints_cons _ _ _ (der_29270 v h) (hints_cons _ _ _ (der_29271 v h) (hints_cons _ _ _ (der_29272 v h) (hints_cons _ _ _ (der_29273 v h) (hints_cons _ _ _ (der_29274 v h) (hints_cons _ _ _ (der_29275 v h) (hints_cons _ _ _ (der_29276 v h) (hints_cons _ _ _ (der_29277 v h) (hints_cons _ _ _ (der_29278 v h) (hints_cons _ _ _ (der_29279 v h) (hints_cons _ _ _ (der_29280 v h) (hints_cons _ _ _ (der_29281 v h) (hints_cons _ _ _ (der_29282 v h) (hints_cons _ _ _ (der_29283 v h) (hints_cons _ _ _ (der_29284 v h) (hints_cons _ _ _ (der_29285 v h) (hints_cons _ _ _ (der_29286 v h) (hints_cons _ _ _ (der_29287 v h) (hints_cons _ _ _ (der_29288 v h) (hints_cons _ _ _ (der_29289 v h) (hints_cons _ _ _ (der_29290 v h) (hints_cons _ _ _ (der_29291 v h) (hints_cons _ _ _ (der_29292 v h) (hints_cons _ _ _ (der_29293 v h) (hints_cons _ _ _ (der_29294 v h) (hints_cons _ _ _ (der_29295 v h) (hints_cons _ _ _ (der_29296 v h) (hints_cons _ _ _ (der_29297 v h) (hints_cons _ _ _ (der_29298 v h) (hints_cons _ _ _ (der_29299 v h) (hints_cons _ _ _ (der_29300 v h) (hints_cons _ _ _ (der_29301 v h) (hints_cons _ _ _ (der_29302 v h) (hints_cons _ _ _ (der_29303 v h) (hints_cons _ _ _ (der_29304 v h) (hints_cons _ _ _ (der_29306 v h) (hints_cons _ _ _ (der_29307 v h) (hints_cons _ _ _ (der_29308 v h) (hints_cons _ _ _ (der_29309 v h) (hints_cons _ _ _ (der_29310 v h) (hints_cons _ _ _ (der_29311 v h) (hints_cons _ _ _ (der_29312 v h) (hints_cons _ _ _ (der_29313 v h) (hints_cons _ _ _ (der_29314 v h) (hints_cons _ _ _ (der_29315 v h) (hints_cons _ _ _ (der_29316 v h) (hints_cons _ _ _ (der_29317 v h) (hints_cons _ _ _ (der_29318 v h) (hints_cons _ _ _ (der_29319 v h) (hints_cons _ _ _ (der_29320 v h) (hints_cons _ _ _ (der_29321 v h) (hints_cons _ _ _ (der_29322 v h) (hints_cons _ _ _ (der_29323 v h) (hints_cons _ _ _ (der_29324 v h) (hints_cons _ _ _ (der_29325 v h) (hints_cons _ _ _ (der_29326 v h) (hints_cons _ _ _ (der_29327 v h) (hints_cons _ _ _ (der_29328 v h) (hints_cons _ _ _ (der_29329 v h) (hints_cons _ _ _ (der_29330 v h) (hints_cons _ _ _ (der_29331 v h) (hints_cons _ _ _ (der_29333 v h) (hints_cons _ _ _ (der_29334 v h) (hints_cons _ _ _ (der_29335 v h) (hints_cons _ _ _ (der_29336 v h) (hints_cons _ _ _ (der_29338 v h) (hints_cons _ _ _ (der_29339 v h) (hints_cons _ _ _ (der_29340 v h) (hints_cons _ _ _ (der_29341 v h) (hints_cons _ _ _ (der_29342 v h) (hints_cons _ _ _ (der_29343 v h) (hints_cons _ _ _ (der_29344 v h) (hints_cons _ _ _ (der_29345 v h) (hints_cons _ _ _ (der_29346 v h) (hints_cons _ _ _ (der_29347 v h) (hints_cons _ _ _ (der_29348 v h) (hints_cons _ _ _ (der_29349 v h) (hints_cons _ _ _ (der_29350 v h) (hints_cons _ _ _ (der_29351 v h) (hints_cons _ _ _ (der_29352 v h) (hints_cons _ _ _ (der_29353 v h) (hints_cons _ _ _ (der_29354 v h) (hints_cons _ _ _ (der_29355 v h) (hints_cons _ _ _ (der_29356 v h) (hints_cons _ _ _ (der_29357 v h) (hints_cons _ _ _ (der_29358 v h) (hints_cons _ _ _ (der_29359 v h) (hints_cons _ _ _ (der_29360 v h) (hints_cons _ _ _ (der_29361 v h) (hints_cons _ _ _ (der_29362 v h) (hints_cons _ _ _ (der_29363 v h) (hints_cons _ _ _ (der_29364 v h) (hints_cons _ _ _ (der_29365 v h) (hints_cons _ _ _ (der_29366 v h) (hints_cons _ _ _ (der_29367 v h) (hints_cons _ _ _ (der_29368 v h) (hints_cons _ _ _ (der_29369 v h) (by intro d hd; cases hd)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def prefix013 := prefix012 ++ chunk013
theorem prefix_sound013 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : ∀ c ∈ prefix013, CNF.Holds (v ∘ decodeVar) c := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact prefix_sound012 v h c hc
  · exact chunk_sound013 v h c hc
end Percolation.NReplay
