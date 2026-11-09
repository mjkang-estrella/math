import NReplay021
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_34008 : CNF.NClause := [(50,false),(77,false),(71,true),(19,true),(63,true),(90,false)]
theorem der_34008 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34008 :=
  CNF.rup_sound cl_34008 [cl_28844,cl_34001] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28844 v h) (hints_cons _ _ _ (der_34001 v h) (by intro d hd; cases hd)))
def cl_34009 : CNF.NClause := [(50,false),(74,false),(63,false),(90,false),(71,false),(19,true)]
theorem der_34009 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34009 :=
  CNF.rup_sound cl_34009 [cl_28846,cl_32382] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28846 v h) (hints_cons _ _ _ (der_32382 v h) (by intro d hd; cases hd)))
def cl_34010 : CNF.NClause := [(50,false),(77,true),(63,true),(90,false),(71,false),(74,false)]
theorem der_34010 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34010 :=
  CNF.rup_sound cl_34010 [cl_28848,cl_28847] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28848 v h) (hints_cons _ _ _ (der_28847 v h) (by intro d hd; cases hd)))
def cl_34011 : CNF.NClause := [(50,false),(71,true),(19,false),(63,false),(90,false),(74,false)]
theorem der_34011 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34011 :=
  CNF.rup_sound cl_34011 [cl_28849,cl_33999] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28849 v h) (hints_cons _ _ _ (der_33999 v h) (by intro d hd; cases hd)))
def cl_34012 : CNF.NClause := [(50,false),(74,false),(63,false),(90,false),(71,true),(85,true)]
theorem der_34012 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34012 :=
  CNF.rup_sound cl_34012 [cl_28850,cl_33999] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28850 v h) (hints_cons _ _ _ (der_33999 v h) (by intro d hd; cases hd)))
def cl_34013 : CNF.NClause := [(50,false),(90,false),(19,false),(63,true),(71,true),(74,false)]
theorem der_34013 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34013 :=
  CNF.rup_sound cl_34013 [cl_28851,cl_34000] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28851 v h) (hints_cons _ _ _ (der_34000 v h) (by intro d hd; cases hd)))
def cl_34014 : CNF.NClause := [(50,false),(74,false),(71,true),(63,true),(19,true),(90,false)]
theorem der_34014 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34014 :=
  CNF.rup_sound cl_34014 [cl_28852,cl_34001] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28852 v h) (hints_cons _ _ _ (der_34001 v h) (by intro d hd; cases hd)))
def cl_34015 : CNF.NClause := [(50,false),(74,true),(19,false),(63,false),(90,false),(71,false)]
theorem der_34015 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34015 :=
  CNF.rup_sound cl_34015 [cl_28853,cl_34002] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28853 v h) (hints_cons _ _ _ (der_34002 v h) (by intro d hd; cases hd)))
def cl_34016 : CNF.NClause := [(50,false),(74,true),(19,false),(63,true),(90,false),(71,false)]
theorem der_34016 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34016 :=
  CNF.rup_sound cl_34016 [cl_28854,cl_34003] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28854 v h) (hints_cons _ _ _ (der_34003 v h) (by intro d hd; cases hd)))
def cl_34017 : CNF.NClause := [(50,false),(71,false),(74,true),(77,true),(63,true),(90,false)]
theorem der_34017 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34017 :=
  CNF.rup_sound cl_34017 [cl_28855,cl_34016] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28855 v h) (hints_cons _ _ _ (der_34016 v h) (by intro d hd; cases hd)))
def cl_34018 : CNF.NClause := [(50,false),(74,true),(71,true),(19,false),(63,false),(90,false)]
theorem der_34018 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34018 :=
  CNF.rup_sound cl_34018 [cl_28856,cl_34005] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28856 v h) (hints_cons _ _ _ (der_34005 v h) (by intro d hd; cases hd)))
def cl_34019 : CNF.NClause := [(50,false),(77,true),(74,true),(71,true),(63,false),(90,false)]
theorem der_34019 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34019 :=
  CNF.rup_sound cl_34019 [cl_28857,cl_34018] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28857 v h) (hints_cons _ _ _ (der_34018 v h) (by intro d hd; cases hd)))
def cl_34020 : CNF.NClause := [(50,false),(74,true),(19,false),(77,true),(63,true),(90,false)]
theorem der_34020 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34020 :=
  CNF.rup_sound cl_34020 [cl_28858,cl_34016] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28858 v h) (hints_cons _ _ _ (der_34016 v h) (by intro d hd; cases hd)))
def cl_34021 : CNF.NClause := [(50,false),(77,true),(74,true),(19,true),(63,true),(90,false)]
theorem der_34021 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34021 :=
  CNF.rup_sound cl_34021 [cl_28859,cl_34017] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28859 v h) (hints_cons _ _ _ (der_34017 v h) (by intro d hd; cases hd)))
def cl_34022 : CNF.NClause := [(50,false),(63,false),(85,false),(71,false),(74,false),(90,true)]
theorem der_34022 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34022 :=
  CNF.rup_sound cl_34022 [cl_28860,cl_32448] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28860 v h) (hints_cons _ _ _ (der_32448 v h) (by intro d hd; cases hd)))
def cl_34023 : CNF.NClause := [(50,false),(77,false),(19,true),(85,false),(71,false),(74,false)]
theorem der_34023 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34023 :=
  CNF.rup_sound cl_34023 [cl_28862,cl_26753] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28862 v h) (hints_cons _ _ _ (der_26753 v h) (by intro d hd; cases hd)))
def cl_34024 : CNF.NClause := [(50,false),(77,false),(19,true),(63,false),(85,false),(74,false)]
theorem der_34024 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34024 :=
  CNF.rup_sound cl_34024 [cl_28864,cl_26753] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28864 v h) (hints_cons _ _ _ (der_26753 v h) (by intro d hd; cases hd)))
def cl_34025 : CNF.NClause := [(50,false),(77,false),(19,false),(63,true),(85,false),(74,false)]
theorem der_34025 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34025 :=
  CNF.rup_sound cl_34025 [cl_28865,cl_28861] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28865 v h) (hints_cons _ _ _ (der_28861 v h) (by intro d hd; cases hd)))
def cl_34026 : CNF.NClause := [(50,false),(71,true),(63,true),(77,false),(85,false),(74,false)]
theorem der_34026 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34026 :=
  CNF.rup_sound cl_34026 [cl_28866,cl_34025] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28866 v h) (hints_cons _ _ _ (der_34025 v h) (by intro d hd; cases hd)))
def cl_34027 : CNF.NClause := [(50,false),(74,true),(77,false),(63,false),(85,false),(71,false)]
theorem der_34027 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34027 :=
  CNF.rup_sound cl_34027 [cl_28867,cl_32384] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28867 v h) (hints_cons _ _ _ (der_32384 v h) (by intro d hd; cases hd)))
def cl_34029 : CNF.NClause := [(50,false),(74,true),(63,true),(77,false),(85,false),(71,false)]
theorem der_34029 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34029 :=
  CNF.rup_sound cl_34029 [cl_28869,cl_33983] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28869 v h) (hints_cons _ _ _ (der_33983 v h) (by intro d hd; cases hd)))
def cl_34030 : CNF.NClause := [(50,false),(77,false),(74,true),(19,true),(63,false),(85,false)]
theorem der_34030 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34030 :=
  CNF.rup_sound cl_34030 [cl_28871,cl_32384] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28871 v h) (hints_cons _ _ _ (der_32384 v h) (by intro d hd; cases hd)))
def cl_34031 : CNF.NClause := [(50,false),(71,true),(19,false),(63,true),(77,false),(85,false)]
theorem der_34031 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34031 :=
  CNF.rup_sound cl_34031 [cl_28872,cl_34025] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28872 v h) (hints_cons _ _ _ (der_34025 v h) (by intro d hd; cases hd)))
def cl_34032 : CNF.NClause := [(50,false),(77,false),(74,true),(19,true),(63,true),(85,false)]
theorem der_34032 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34032 :=
  CNF.rup_sound cl_34032 [cl_28873,cl_34029] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28873 v h) (hints_cons _ _ _ (der_34029 v h) (by intro d hd; cases hd)))
def cl_34033 : CNF.NClause := [(50,false),(19,false),(63,true),(85,false),(71,false),(74,false)]
theorem der_34033 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34033 :=
  CNF.rup_sound cl_34033 [cl_28874,cl_34025] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28874 v h) (hints_cons _ _ _ (der_34025 v h) (by intro d hd; cases hd)))
def cl_34034 : CNF.NClause := [(50,false),(74,false),(85,false),(71,false),(77,true),(90,true)]
theorem der_34034 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34034 :=
  CNF.rup_sound cl_34034 [cl_28875,cl_34022] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28875 v h) (hints_cons _ _ _ (der_34022 v h) (by intro d hd; cases hd)))
def cl_34035 : CNF.NClause := [(50,false),(71,true),(19,false),(63,false),(85,false),(74,false)]
theorem der_34035 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34035 :=
  CNF.rup_sound cl_34035 [cl_28876,cl_28863] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28876 v h) (hints_cons _ _ _ (der_28863 v h) (by intro d hd; cases hd)))
def cl_34036 : CNF.NClause := [(50,false),(74,false),(77,true),(63,false),(85,false),(90,true)]
theorem der_34036 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34036 :=
  CNF.rup_sound cl_34036 [cl_28877,cl_32448] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28877 v h) (hints_cons _ _ _ (der_32448 v h) (by intro d hd; cases hd)))
def cl_34037 : CNF.NClause := [(50,false),(85,false),(19,false),(63,true),(71,true),(74,false)]
theorem der_34037 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34037 :=
  CNF.rup_sound cl_34037 [cl_28878,cl_34025] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28878 v h) (hints_cons _ _ _ (der_34025 v h) (by intro d hd; cases hd)))
def cl_34038 : CNF.NClause := [(50,false),(85,false),(71,true),(77,true),(63,true),(74,false)]
theorem der_34038 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34038 :=
  CNF.rup_sound cl_34038 [cl_28879,cl_34037] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28879 v h) (hints_cons _ _ _ (der_34037 v h) (by intro d hd; cases hd)))
def cl_34039 : CNF.NClause := [(50,false),(19,false),(77,true),(63,false),(85,false),(71,false)]
theorem der_34039 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34039 :=
  CNF.rup_sound cl_34039 [cl_28880,cl_32448] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28880 v h) (hints_cons _ _ _ (der_32448 v h) (by intro d hd; cases hd)))
def cl_34040 : CNF.NClause := [(50,false),(74,true),(19,false),(63,true),(85,false),(71,false)]
theorem der_34040 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34040 :=
  CNF.rup_sound cl_34040 [cl_28881,cl_34029] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28881 v h) (hints_cons _ _ _ (der_34029 v h) (by intro d hd; cases hd)))
def cl_34041 : CNF.NClause := [(50,false),(85,false),(74,true),(63,true),(19,true),(71,false)]
theorem der_34041 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34041 :=
  CNF.rup_sound cl_34041 [cl_28882,cl_34029] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28882 v h) (hints_cons _ _ _ (der_34029 v h) (by intro d hd; cases hd)))
def cl_34042 : CNF.NClause := [(50,false),(71,true),(19,false),(77,true),(63,false),(85,false)]
theorem der_34042 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34042 :=
  CNF.rup_sound cl_34042 [cl_28883,cl_34035] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28883 v h) (hints_cons _ _ _ (der_34035 v h) (by intro d hd; cases hd)))
def cl_34043 : CNF.NClause := [(50,false),(77,true),(74,true),(71,true),(63,false),(85,false)]
theorem der_34043 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34043 :=
  CNF.rup_sound cl_34043 [cl_28884,cl_34042] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28884 v h) (hints_cons _ _ _ (der_34042 v h) (by intro d hd; cases hd)))
def cl_34044 : CNF.NClause := [(50,false),(74,true),(19,false),(63,true),(85,false),(90,true)]
theorem der_34044 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34044 :=
  CNF.rup_sound cl_34044 [cl_28885,cl_34040] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28885 v h) (hints_cons _ _ _ (der_34040 v h) (by intro d hd; cases hd)))
def cl_34045 : CNF.NClause := [(50,false),(71,false),(77,false),(63,false),(19,true),(74,false)]
theorem der_34045 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34045 :=
  CNF.rup_sound cl_34045 [cl_28888,cl_26753] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28888 v h) (hints_cons _ _ _ (der_26753 v h) (by intro d hd; cases hd)))
def cl_34046 : CNF.NClause := [(50,false),(77,false),(19,false),(63,true),(71,false),(74,false)]
theorem der_34046 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34046 :=
  CNF.rup_sound cl_34046 [cl_28889,cl_34025] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28889 v h) (hints_cons _ _ _ (der_34025 v h) (by intro d hd; cases hd)))
def cl_34047 : CNF.NClause := [(50,false),(77,false),(63,true),(71,false),(74,false),(85,true)]
theorem der_34047 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34047 :=
  CNF.rup_sound cl_34047 [cl_28890,cl_34046] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28890 v h) (hints_cons _ _ _ (der_34046 v h) (by intro d hd; cases hd)))
def cl_34048 : CNF.NClause := [(50,false),(77,false),(71,true),(19,false),(63,false),(74,false)]
theorem der_34048 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34048 :=
  CNF.rup_sound cl_34048 [cl_28891,cl_34035] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28891 v h) (hints_cons _ _ _ (der_34035 v h) (by intro d hd; cases hd)))
def cl_34049 : CNF.NClause := [(50,false),(77,false),(71,true),(63,false),(74,false),(85,true)]
theorem der_34049 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34049 :=
  CNF.rup_sound cl_34049 [cl_28892,cl_33999] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28892 v h) (hints_cons _ _ _ (der_33999 v h) (by intro d hd; cases hd)))
def cl_34050 : CNF.NClause := [(50,false),(77,false),(71,true),(19,false),(63,true),(74,false)]
theorem der_34050 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34050 :=
  CNF.rup_sound cl_34050 [cl_28893,cl_34025] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28893 v h) (hints_cons _ _ _ (der_34025 v h) (by intro d hd; cases hd)))
def cl_34051 : CNF.NClause := [(50,false),(71,true),(19,true),(77,false),(74,false),(85,true)]
theorem der_34051 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34051 :=
  CNF.rup_sound cl_34051 [cl_28894,cl_34049] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28894 v h) (hints_cons _ _ _ (der_34049 v h) (by intro d hd; cases hd)))
def cl_34052 : CNF.NClause := [(50,false),(74,true),(19,false),(77,false),(63,false),(71,false)]
theorem der_34052 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34052 :=
  CNF.rup_sound cl_34052 [cl_28895,cl_34002] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28895 v h) (hints_cons _ _ _ (der_34002 v h) (by intro d hd; cases hd)))
def cl_34053 : CNF.NClause := [(50,false),(74,true),(19,false),(63,true),(77,false),(71,false)]
theorem der_34053 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34053 :=
  CNF.rup_sound cl_34053 [cl_28896,cl_34029] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28896 v h) (hints_cons _ _ _ (der_34029 v h) (by intro d hd; cases hd)))
def cl_34054 : CNF.NClause := [(50,false),(74,true),(19,true),(63,true),(77,false),(71,false)]
theorem der_34054 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34054 :=
  CNF.rup_sound cl_34054 [cl_28897,cl_34029] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28897 v h) (hints_cons _ _ _ (der_34029 v h) (by intro d hd; cases hd)))
def cl_34055 : CNF.NClause := [(50,false),(74,true),(19,false),(77,false),(63,false),(85,true)]
theorem der_34055 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34055 :=
  CNF.rup_sound cl_34055 [cl_28898,cl_34052] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28898 v h) (hints_cons _ _ _ (der_34052 v h) (by intro d hd; cases hd)))
def cl_34056 : CNF.NClause := [(50,false),(77,false),(74,true),(19,true),(63,false),(85,true)]
theorem der_34056 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34056 :=
  CNF.rup_sound cl_34056 [cl_28899,cl_32387] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28899 v h) (hints_cons _ _ _ (der_32387 v h) (by intro d hd; cases hd)))
def cl_34058 : CNF.NClause := [(50,false),(63,false),(71,false),(74,false),(19,true),(90,true)]
theorem der_34058 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34058 :=
  CNF.rup_sound cl_34058 [cl_28903,cl_34022] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28903 v h) (hints_cons _ _ _ (der_34022 v h) (by intro d hd; cases hd)))
def cl_34059 : CNF.NClause := [(50,false),(71,false),(19,false),(63,true),(74,false),(90,true)]
theorem der_34059 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34059 :=
  CNF.rup_sound cl_34059 [cl_28904,cl_34033] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28904 v h) (hints_cons _ _ _ (der_34033 v h) (by intro d hd; cases hd)))
def cl_34060 : CNF.NClause := [(50,false),(74,false),(77,true),(63,true),(71,false),(19,true)]
theorem der_34060 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34060 :=
  CNF.rup_sound cl_34060 [cl_28905,cl_34010] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28905 v h) (hints_cons _ _ _ (der_34010 v h) (by intro d hd; cases hd)))
def cl_34061 : CNF.NClause := [(50,false),(77,true),(71,true),(19,false),(63,false),(74,false)]
theorem der_34061 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34061 :=
  CNF.rup_sound cl_34061 [cl_28906,cl_34035] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28906 v h) (hints_cons _ _ _ (der_34035 v h) (by intro d hd; cases hd)))
def cl_34062 : CNF.NClause := [(50,false),(85,true),(77,true),(63,false),(74,false),(71,true)]
theorem der_34062 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34062 :=
  CNF.rup_sound cl_34062 [cl_28907,cl_34012] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28907 v h) (hints_cons _ _ _ (der_34012 v h) (by intro d hd; cases hd)))
def cl_34063 : CNF.NClause := [(50,false),(74,false),(19,false),(77,true),(71,true),(90,true)]
theorem der_34063 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34063 :=
  CNF.rup_sound cl_34063 [cl_28908,cl_34061] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28908 v h) (hints_cons _ _ _ (der_34061 v h) (by intro d hd; cases hd)))
def cl_34064 : CNF.NClause := [(50,false),(85,true),(71,true),(63,true),(74,false),(19,true)]
theorem der_34064 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34064 :=
  CNF.rup_sound cl_34064 [cl_28909,cl_34014] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28909 v h) (hints_cons _ _ _ (der_34014 v h) (by intro d hd; cases hd)))
def cl_34065 : CNF.NClause := [(50,false),(74,true),(19,false),(63,false),(71,false),(85,true)]
theorem der_34065 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34065 :=
  CNF.rup_sound cl_34065 [cl_28910,cl_34052] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28910 v h) (hints_cons _ _ _ (der_34052 v h) (by intro d hd; cases hd)))
def cl_34067 : CNF.NClause := [(50,false),(74,true),(77,true),(63,true),(71,false),(85,true)]
theorem der_34067 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34067 :=
  CNF.rup_sound cl_34067 [cl_28912,cl_34017] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28912 v h) (hints_cons _ _ _ (der_34017 v h) (by intro d hd; cases hd)))
def cl_34071 : CNF.NClause := [(50,false),(74,true),(71,true),(19,true),(77,true),(90,true)]
theorem der_34071 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34071 :=
  CNF.rup_sound cl_34071 [cl_28916,cl_28886] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28916 v h) (hints_cons _ _ _ (der_28886 v h) (by intro d hd; cases hd)))
def cl_34076 : CNF.NClause := [(32,false),(57,false),(51,false),(38,false),(44,true),(102,true)]
theorem der_34076 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34076 :=
  CNF.rup_sound cl_34076 [cl_2573,cl_23918] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2573 v h) (hints_cons _ _ _ (der_23918 v h) (by intro d hd; cases hd)))
def cl_34077 : CNF.NClause := [(32,false),(86,false),(66,true),(87,false),(81,false),(76,false)]
theorem der_34077 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34077 :=
  CNF.rup_sound cl_34077 [cl_28921,cl_28920] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28921 v h) (hints_cons _ _ _ (der_28920 v h) (by intro d hd; cases hd)))
def cl_34078 : CNF.NClause := [(32,false),(86,false),(66,true),(87,false),(71,false),(81,false)]
theorem der_34078 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34078 :=
  CNF.rup_sound cl_34078 [cl_28924,cl_28923] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28924 v h) (hints_cons _ _ _ (der_28923 v h) (by intro d hd; cases hd)))
def cl_34079 : CNF.NClause := [(32,false),(66,true),(1,true),(87,false),(86,false),(81,false)]
theorem der_34079 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34079 :=
  CNF.rup_sound cl_34079 [cl_28928,cl_34077] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28928 v h) (hints_cons _ _ _ (der_34077 v h) (by intro d hd; cases hd)))
def cl_34080 : CNF.NClause := [(32,false),(71,false),(66,true),(87,false),(86,false),(76,false)]
theorem der_34080 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34080 :=
  CNF.rup_sound cl_34080 [cl_28931,cl_28930] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28931 v h) (hints_cons _ _ _ (der_28930 v h) (by intro d hd; cases hd)))
def cl_34081 : CNF.NClause := [(32,false),(81,true),(71,true),(87,false),(86,false),(76,false)]
theorem der_34081 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34081 :=
  CNF.rup_sound cl_34081 [cl_28935,cl_28934] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28935 v h) (hints_cons _ _ _ (der_28934 v h) (by intro d hd; cases hd)))
def cl_34083 : CNF.NClause := [(32,false),(86,false),(76,true),(1,false),(87,false),(66,false)]
theorem der_34083 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34083 :=
  CNF.rup_sound cl_34083 [cl_28940,cl_28936] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28940 v h) (hints_cons _ _ _ (der_28936 v h) (by intro d hd; cases hd)))
def cl_34084 : CNF.NClause := [(32,false),(86,false),(71,true),(76,true),(87,false),(66,false)]
theorem der_34084 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34084 :=
  CNF.rup_sound cl_34084 [cl_28941,cl_34083] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28941 v h) (hints_cons _ _ _ (der_34083 v h) (by intro d hd; cases hd)))
def cl_34087 : CNF.NClause := [(32,false),(71,false),(66,true),(87,false),(81,false),(76,false)]
theorem der_34087 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34087 :=
  CNF.rup_sound cl_34087 [cl_28946,cl_28945] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28946 v h) (hints_cons _ _ _ (der_28945 v h) (by intro d hd; cases hd)))
def cl_34088 : CNF.NClause := [(32,false),(66,true),(1,false),(87,false),(81,false),(76,false)]
theorem der_34088 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34088 :=
  CNF.rup_sound cl_34088 [cl_28949,cl_34077] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28949 v h) (hints_cons _ _ _ (der_34077 v h) (by intro d hd; cases hd)))
def cl_34089 : CNF.NClause := [(32,false),(1,false),(66,true),(87,false),(71,false),(81,false)]
theorem der_34089 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34089 :=
  CNF.rup_sound cl_34089 [cl_28953,cl_34078] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28953 v h) (hints_cons _ _ _ (der_34078 v h) (by intro d hd; cases hd)))
def cl_34090 : CNF.NClause := [(32,false),(66,true),(1,true),(87,false),(71,false),(81,false)]
theorem der_34090 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34090 :=
  CNF.rup_sound cl_34090 [cl_28954,cl_34087] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28954 v h) (hints_cons _ _ _ (der_34087 v h) (by intro d hd; cases hd)))
def cl_34091 : CNF.NClause := [(32,false),(76,true),(1,false),(87,false),(66,false),(81,false)]
theorem der_34091 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34091 :=
  CNF.rup_sound cl_34091 [cl_28955,cl_28951] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28955 v h) (hints_cons _ _ _ (der_28951 v h) (by intro d hd; cases hd)))
def cl_34092 : CNF.NClause := [(32,false),(81,false),(71,true),(76,true),(87,false),(66,false)]
theorem der_34092 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34092 :=
  CNF.rup_sound cl_34092 [cl_28956,cl_34091] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28956 v h) (hints_cons _ _ _ (der_34091 v h) (by intro d hd; cases hd)))
def cl_34094 : CNF.NClause := [(32,false),(71,true),(76,true),(86,true),(87,false),(81,false)]
theorem der_34094 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34094 :=
  CNF.rup_sound cl_34094 [cl_28958,cl_34092] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28958 v h) (hints_cons _ _ _ (der_34092 v h) (by intro d hd; cases hd)))
def cl_34096 : CNF.NClause := [(32,false),(76,false),(66,true),(81,true),(87,false),(71,false)]
theorem der_34096 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34096 :=
  CNF.rup_sound cl_34096 [cl_28962,cl_34080] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28962 v h) (hints_cons _ _ _ (der_34080 v h) (by intro d hd; cases hd)))
def cl_34097 : CNF.NClause := [(32,false),(76,false),(1,false),(87,false),(66,false),(71,true)]
theorem der_34097 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34097 :=
  CNF.rup_sound cl_34097 [cl_28963,cl_28947] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28963 v h) (hints_cons _ _ _ (der_28947 v h) (by intro d hd; cases hd)))
def cl_34098 : CNF.NClause := [(32,false),(76,false),(71,true),(81,true),(87,false),(66,false)]
theorem der_34098 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34098 :=
  CNF.rup_sound cl_34098 [cl_28964,cl_34097] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28964 v h) (hints_cons _ _ _ (der_34097 v h) (by intro d hd; cases hd)))
def cl_34100 : CNF.NClause := [(32,false),(76,false),(71,true),(81,true),(87,false),(1,true)]
theorem der_34100 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34100 :=
  CNF.rup_sound cl_34100 [cl_28966,cl_34098] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28966 v h) (hints_cons _ _ _ (der_34098 v h) (by intro d hd; cases hd)))
def cl_34101 : CNF.NClause := [(32,false),(76,true),(1,false),(87,false),(71,false),(66,false)]
theorem der_34101 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34101 :=
  CNF.rup_sound cl_34101 [cl_28967,cl_28951] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28967 v h) (hints_cons _ _ _ (der_28951 v h) (by intro d hd; cases hd)))
def cl_34102 : CNF.NClause := [(32,false),(71,false),(76,true),(81,true),(87,false),(66,false)]
theorem der_34102 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34102 :=
  CNF.rup_sound cl_34102 [cl_28968,cl_34101] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28968 v h) (hints_cons _ _ _ (der_34101 v h) (by intro d hd; cases hd)))
def cl_34105 : CNF.NClause := [(32,false),(71,true),(76,true),(1,false),(87,false),(66,false)]
theorem der_34105 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34105 :=
  CNF.rup_sound cl_34105 [cl_28971,cl_34092] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28971 v h) (hints_cons _ _ _ (der_34092 v h) (by intro d hd; cases hd)))
def cl_34106 : CNF.NClause := [(32,false),(71,true),(76,true),(86,true),(87,false),(66,false)]
theorem der_34106 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34106 :=
  CNF.rup_sound cl_34106 [cl_28972,cl_34092] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28972 v h) (hints_cons _ _ _ (der_34092 v h) (by intro d hd; cases hd)))
def cl_34107 : CNF.NClause := [(32,false),(81,true),(76,true),(71,true),(1,false),(87,false)]
theorem der_34107 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34107 :=
  CNF.rup_sound cl_34107 [cl_28973,cl_34105] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28973 v h) (hints_cons _ _ _ (der_34105 v h) (by intro d hd; cases hd)))
def cl_34108 : CNF.NClause := [(32,false),(81,true),(71,true),(76,true),(66,true),(87,false)]
theorem der_34108 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34108 :=
  CNF.rup_sound cl_34108 [cl_28974,cl_34107] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28974 v h) (hints_cons _ _ _ (der_34107 v h) (by intro d hd; cases hd)))
def cl_34109 : CNF.NClause := [(32,false),(71,false),(1,true),(86,false),(81,false),(76,false)]
theorem der_34109 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34109 :=
  CNF.rup_sound cl_34109 [cl_28977,cl_28975] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28977 v h) (hints_cons _ _ _ (der_28975 v h) (by intro d hd; cases hd)))
def cl_34110 : CNF.NClause := [(32,false),(1,true),(86,false),(66,false),(81,false),(76,false)]
theorem der_34110 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34110 :=
  CNF.rup_sound cl_34110 [cl_28979,cl_28975] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28979 v h) (hints_cons _ _ _ (der_28975 v h) (by intro d hd; cases hd)))
def cl_34111 : CNF.NClause := [(32,false),(1,false),(66,true),(86,false),(81,false),(76,false)]
theorem der_34111 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34111 :=
  CNF.rup_sound cl_34111 [cl_28980,cl_28976] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28980 v h) (hints_cons _ _ _ (der_28976 v h) (by intro d hd; cases hd)))
def cl_34112 : CNF.NClause := [(32,false),(86,false),(71,true),(66,true),(81,false),(76,false)]
theorem der_34112 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34112 :=
  CNF.rup_sound cl_34112 [cl_28981,cl_34111] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28981 v h) (hints_cons _ _ _ (der_34111 v h) (by intro d hd; cases hd)))
def cl_34113 : CNF.NClause := [(32,false),(81,false),(71,false),(86,false),(66,false),(1,true)]
theorem der_34113 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34113 :=
  CNF.rup_sound cl_34113 [cl_28983,cl_28922] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28983 v h) (hints_cons _ _ _ (der_28922 v h) (by intro d hd; cases hd)))
def cl_34114 : CNF.NClause := [(32,false),(71,false),(1,true),(66,true),(86,false),(81,false)]
theorem der_34114 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34114 :=
  CNF.rup_sound cl_34114 [cl_28985,cl_34109] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28985 v h) (hints_cons _ _ _ (der_34109 v h) (by intro d hd; cases hd)))
def cl_34115 : CNF.NClause := [(32,false),(76,true),(1,false),(86,false),(66,false),(81,false)]
theorem der_34115 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34115 :=
  CNF.rup_sound cl_34115 [cl_28986,cl_28982] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28986 v h) (hints_cons _ _ _ (der_28982 v h) (by intro d hd; cases hd)))
def cl_34116 : CNF.NClause := [(32,false),(71,true),(1,true),(86,false),(66,false),(81,false)]
theorem der_34116 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34116 :=
  CNF.rup_sound cl_34116 [cl_28987,cl_34110] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28987 v h) (hints_cons _ _ _ (der_34110 v h) (by intro d hd; cases hd)))
def cl_34117 : CNF.NClause := [(32,false),(86,false),(71,true),(1,false),(66,true),(81,false)]
theorem der_34117 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34117 :=
  CNF.rup_sound cl_34117 [cl_28988,cl_34111] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28988 v h) (hints_cons _ _ _ (der_34111 v h) (by intro d hd; cases hd)))
def cl_34118 : CNF.NClause := [(32,false),(86,false),(71,true),(1,true),(66,true),(81,false)]
theorem der_34118 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34118 :=
  CNF.rup_sound cl_34118 [cl_28989,cl_34079] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28989 v h) (hints_cons _ _ _ (der_34079 v h) (by intro d hd; cases hd)))
def cl_34119 : CNF.NClause := [(32,false),(86,false),(66,true),(71,false),(1,false),(76,false)]
theorem der_34119 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34119 :=
  CNF.rup_sound cl_34119 [cl_28992,cl_28976] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28992 v h) (hints_cons _ _ _ (der_28976 v h) (by intro d hd; cases hd)))
def cl_34120 : CNF.NClause := [(32,false),(66,true),(81,true),(71,false),(86,false),(76,false)]
theorem der_34120 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34120 :=
  CNF.rup_sound cl_34120 [cl_28993,cl_34080] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28993 v h) (hints_cons _ _ _ (der_34080 v h) (by intro d hd; cases hd)))
def cl_34121 : CNF.NClause := [(32,false),(76,false),(1,false),(81,true),(86,false),(66,false)]
theorem der_34121 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34121 :=
  CNF.rup_sound cl_34121 [cl_28994,cl_28990] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28994 v h) (hints_cons _ _ _ (der_28990 v h) (by intro d hd; cases hd)))
def cl_34122 : CNF.NClause := [(32,false),(76,false),(71,true),(81,true),(86,false),(66,false)]
theorem der_34122 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34122 :=
  CNF.rup_sound cl_34122 [cl_28995,cl_34121] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28995 v h) (hints_cons _ _ _ (der_34121 v h) (by intro d hd; cases hd)))
def cl_34123 : CNF.NClause := [(32,false),(81,true),(1,false),(86,false),(76,false),(87,true)]
theorem der_34123 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34123 :=
  CNF.rup_sound cl_34123 [cl_28996,cl_34121] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28996 v h) (hints_cons _ _ _ (der_34121 v h) (by intro d hd; cases hd)))
def cl_34125 : CNF.NClause := [(32,false),(1,false),(81,true),(71,false),(86,false),(66,false)]
theorem der_34125 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34125 :=
  CNF.rup_sound cl_34125 [cl_28998,cl_34121] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28998 v h) (hints_cons _ _ _ (der_34121 v h) (by intro d hd; cases hd)))
def cl_34126 : CNF.NClause := [(32,false),(86,false),(76,true),(81,true),(71,false),(66,false)]
theorem der_34126 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34126 :=
  CNF.rup_sound cl_34126 [cl_28999,cl_34125] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28999 v h) (hints_cons _ _ _ (der_34125 v h) (by intro d hd; cases hd)))
def cl_34127 : CNF.NClause := [(32,false),(71,false),(81,true),(1,false),(86,false),(87,true)]
theorem der_34127 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34127 :=
  CNF.rup_sound cl_34127 [cl_29000,cl_34125] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29000 v h) (hints_cons _ _ _ (der_34125 v h) (by intro d hd; cases hd)))
def cl_34128 : CNF.NClause := [(32,false),(71,false),(66,true),(81,true),(1,true),(86,false)]
theorem der_34128 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34128 :=
  CNF.rup_sound cl_34128 [cl_29001,cl_34120] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29001 v h) (hints_cons _ _ _ (der_34120 v h) (by intro d hd; cases hd)))
def cl_34130 : CNF.NClause := [(32,false),(71,true),(76,true),(81,true),(86,false),(66,false)]
theorem der_34130 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34130 :=
  CNF.rup_sound cl_34130 [cl_29003,cl_34084] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29003 v h) (hints_cons _ _ _ (der_34084 v h) (by intro d hd; cases hd)))
def cl_34131 : CNF.NClause := [(32,false),(81,true),(76,true),(71,true),(1,false),(86,false)]
theorem der_34131 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34131 :=
  CNF.rup_sound cl_34131 [cl_29004,cl_34130] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29004 v h) (hints_cons _ _ _ (der_34130 v h) (by intro d hd; cases hd)))
def cl_34132 : CNF.NClause := [(32,false),(81,true),(71,true),(76,true),(1,true),(86,false)]
theorem der_34132 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34132 :=
  CNF.rup_sound cl_34132 [cl_29005,cl_34130] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29005 v h) (hints_cons _ _ _ (der_34130 v h) (by intro d hd; cases hd)))
def cl_34133 : CNF.NClause := [(32,false),(71,false),(1,true),(66,false),(81,false),(76,false)]
theorem der_34133 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34133 :=
  CNF.rup_sound cl_34133 [cl_29007,cl_28975] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29007 v h) (hints_cons _ _ _ (der_28975 v h) (by intro d hd; cases hd)))
def cl_34134 : CNF.NClause := [(32,false),(81,false),(1,false),(66,true),(71,false),(76,false)]
theorem der_34134 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34134 :=
  CNF.rup_sound cl_34134 [cl_29008,cl_28976] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29008 v h) (hints_cons _ _ _ (der_28976 v h) (by intro d hd; cases hd)))
def cl_34135 : CNF.NClause := [(32,false),(71,false),(1,true),(66,true),(81,false),(76,false)]
theorem der_34135 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34135 :=
  CNF.rup_sound cl_34135 [cl_29009,cl_34109] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29009 v h) (hints_cons _ _ _ (der_34109 v h) (by intro d hd; cases hd)))
def cl_34136 : CNF.NClause := [(32,false),(81,false),(71,true),(86,true),(66,false),(76,false)]
theorem der_34136 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34136 :=
  CNF.rup_sound cl_34136 [cl_29011,cl_29010] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29011 v h) (hints_cons _ _ _ (der_29010 v h) (by intro d hd; cases hd)))
def cl_34137 : CNF.NClause := [(32,false),(81,false),(71,true),(1,false),(66,true),(76,false)]
theorem der_34137 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34137 :=
  CNF.rup_sound cl_34137 [cl_29012,cl_34111] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29012 v h) (hints_cons _ _ _ (der_34111 v h) (by intro d hd; cases hd)))
def cl_34138 : CNF.NClause := [(32,false),(76,false),(71,true),(66,true),(81,false),(1,true)]
theorem der_34138 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34138 :=
  CNF.rup_sound cl_34138 [cl_29013,cl_34112] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29013 v h) (hints_cons _ _ _ (der_34112 v h) (by intro d hd; cases hd)))
def cl_34139 : CNF.NClause := [(32,false),(76,true),(1,false),(71,false),(66,false),(81,false)]
theorem der_34139 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34139 :=
  CNF.rup_sound cl_34139 [cl_29014,cl_28982] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29014 v h) (hints_cons _ _ _ (der_28982 v h) (by intro d hd; cases hd)))
def cl_34140 : CNF.NClause := [(32,false),(76,true),(86,true),(71,false),(66,false),(81,false)]
theorem der_34140 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34140 :=
  CNF.rup_sound cl_34140 [cl_29015,cl_34139] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29015 v h) (hints_cons _ _ _ (der_34139 v h) (by intro d hd; cases hd)))
def cl_34141 : CNF.NClause := [(32,false),(76,true),(86,true),(1,false),(71,false),(81,false)]
theorem der_34141 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34141 :=
  CNF.rup_sound cl_34141 [cl_29016,cl_34139] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29016 v h) (hints_cons _ _ _ (der_34139 v h) (by intro d hd; cases hd)))
def cl_34143 : CNF.NClause := [(32,false),(76,true),(71,true),(1,false),(66,false),(81,false)]
theorem der_34143 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34143 :=
  CNF.rup_sound cl_34143 [cl_29018,cl_34092] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29018 v h) (hints_cons _ _ _ (der_34092 v h) (by intro d hd; cases hd)))
def cl_34144 : CNF.NClause := [(32,false),(71,true),(1,true),(66,false),(81,false),(87,true)]
theorem der_34144 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34144 :=
  CNF.rup_sound cl_34144 [cl_29019,cl_34116] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29019 v h) (hints_cons _ _ _ (der_34116 v h) (by intro d hd; cases hd)))
def cl_34145 : CNF.NClause := [(32,false),(76,true),(86,true),(1,false),(66,true),(81,false)]
theorem der_34145 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34145 :=
  CNF.rup_sound cl_34145 [cl_29020,cl_34141] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29020 v h) (hints_cons _ _ _ (der_34141 v h) (by intro d hd; cases hd)))
def cl_34146 : CNF.NClause := [(32,false),(66,true),(76,true),(86,true),(81,false),(87,true)]
theorem der_34146 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34146 :=
  CNF.rup_sound cl_34146 [cl_29021,cl_34145] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29021 v h) (hints_cons _ _ _ (der_34145 v h) (by intro d hd; cases hd)))
def cl_34147 : CNF.NClause := [(32,false),(76,false),(1,false),(81,true),(71,false),(66,false)]
theorem der_34147 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34147 :=
  CNF.rup_sound cl_34147 [cl_29022,cl_34121] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29022 v h) (hints_cons _ _ _ (der_34121 v h) (by intro d hd; cases hd)))
def cl_34149 : CNF.NClause := [(32,false),(71,false),(1,false),(66,true),(81,true),(76,false)]
theorem der_34149 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34149 :=
  CNF.rup_sound cl_34149 [cl_29024,cl_34120] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29024 v h) (hints_cons _ _ _ (der_34120 v h) (by intro d hd; cases hd)))
def cl_34150 : CNF.NClause := [(32,false),(76,false),(86,true),(1,false),(81,true),(66,false)]
theorem der_34150 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34150 :=
  CNF.rup_sound cl_34150 [cl_29026,cl_34147] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29026 v h) (hints_cons _ _ _ (der_34147 v h) (by intro d hd; cases hd)))
def cl_34151 : CNF.NClause := [(32,false),(86,true),(87,true),(81,true),(66,false),(76,false)]
theorem der_34151 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34151 :=
  CNF.rup_sound cl_34151 [cl_29027,cl_34150] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29027 v h) (hints_cons _ _ _ (der_34150 v h) (by intro d hd; cases hd)))
def cl_34152 : CNF.NClause := [(32,false),(81,true),(71,true),(1,false),(76,false),(87,true)]
theorem der_34152 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34152 :=
  CNF.rup_sound cl_34152 [cl_29028,cl_34123] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29028 v h) (hints_cons _ _ _ (der_34123 v h) (by intro d hd; cases hd)))
def cl_34153 : CNF.NClause := [(32,false),(76,false),(71,true),(66,true),(1,true),(87,true)]
theorem der_34153 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34153 :=
  CNF.rup_sound cl_34153 [cl_29029,cl_34138] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29029 v h) (hints_cons _ _ _ (der_34138 v h) (by intro d hd; cases hd)))
def cl_34154 : CNF.NClause := [(32,false),(76,true),(86,true),(1,false),(71,false),(66,false)]
theorem der_34154 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34154 :=
  CNF.rup_sound cl_34154 [cl_29030,cl_34139] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29030 v h) (hints_cons _ _ _ (der_34139 v h) (by intro d hd; cases hd)))
def cl_34156 : CNF.NClause := [(32,false),(81,true),(76,true),(1,false),(71,true),(66,false)]
theorem der_34156 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34156 :=
  CNF.rup_sound cl_34156 [cl_29034,cl_34130] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29034 v h) (hints_cons _ _ _ (der_34130 v h) (by intro d hd; cases hd)))
def cl_34157 : CNF.NClause := [(32,false),(66,false),(86,true),(81,true),(1,true),(87,true)]
theorem der_34157 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34157 :=
  CNF.rup_sound cl_34157 [cl_29035,cl_29031] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29035 v h) (hints_cons _ _ _ (der_29031 v h) (by intro d hd; cases hd)))
def cl_34159 : CNF.NClause := [(32,false),(81,true),(76,true),(86,true),(66,true),(71,true)]
theorem der_34159 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34159 :=
  CNF.rup_sound cl_34159 [cl_29037,cl_34108] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29037 v h) (hints_cons _ _ _ (der_34108 v h) (by intro d hd; cases hd)))
def cl_34160 : CNF.NClause := [(36,true),(43,true),(58,true),(34,true),(50,true),(116,false)]
theorem der_34160 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34160 :=
  CNF.rup_sound cl_34160 [cl_3504,cl_23919] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3504 v h) (hints_cons _ _ _ (der_23919 v h) (by intro d hd; cases hd)))
def cl_34161 : CNF.NClause := [(36,true),(43,true),(52,true),(58,true),(34,true),(116,false)]
theorem der_34161 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34161 :=
  CNF.rup_sound cl_34161 [cl_3512,cl_23919] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3512 v h) (hints_cons _ _ _ (der_23919 v h) (by intro d hd; cases hd)))
def cl_34162 : CNF.NClause := [(36,true),(50,true),(52,true),(58,true),(34,true),(116,false)]
theorem der_34162 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34162 :=
  CNF.rup_sound cl_34162 [cl_3516,cl_23919] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3516 v h) (hints_cons _ _ _ (der_23919 v h) (by intro d hd; cases hd)))
def cl_34163 : CNF.NClause := [(43,true),(52,true),(58,true),(34,true),(50,true),(116,false)]
theorem der_34163 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34163 :=
  CNF.rup_sound cl_34163 [cl_3518,cl_23919] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3518 v h) (hints_cons _ _ _ (der_23919 v h) (by intro d hd; cases hd)))
def cl_34164 : CNF.NClause := [(36,true),(43,true),(52,true),(58,true),(50,true),(116,false)]
theorem der_34164 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34164 :=
  CNF.rup_sound cl_34164 [cl_3519,cl_23919] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3519 v h) (hints_cons _ _ _ (der_23919 v h) (by intro d hd; cases hd)))
def cl_34165 : CNF.NClause := [(31,true),(46,true),(36,true),(56,true),(41,true),(123,false)]
theorem der_34165 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34165 :=
  CNF.rup_sound cl_34165 [cl_3952,cl_23920] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3952 v h) (hints_cons _ _ _ (der_23920 v h) (by intro d hd; cases hd)))
def cl_34166 : CNF.NClause := [(31,true),(36,true),(56,true),(41,true),(51,true),(123,false)]
theorem der_34166 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34166 :=
  CNF.rup_sound cl_34166 [cl_3960,cl_23920] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3960 v h) (hints_cons _ _ _ (der_23920 v h) (by intro d hd; cases hd)))
def cl_34167 : CNF.NClause := [(31,true),(46,true),(36,true),(56,true),(51,true),(123,false)]
theorem der_34167 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34167 :=
  CNF.rup_sound cl_34167 [cl_3964,cl_23920] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3964 v h) (hints_cons _ _ _ (der_23920 v h) (by intro d hd; cases hd)))
def cl_34168 : CNF.NClause := [(31,true),(46,true),(56,true),(41,true),(51,true),(123,false)]
theorem der_34168 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34168 :=
  CNF.rup_sound cl_34168 [cl_3966,cl_23920] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3966 v h) (hints_cons _ _ _ (der_23920 v h) (by intro d hd; cases hd)))
def cl_34170 : CNF.NClause := [(47,true),(44,true),(36,true),(33,true),(59,true),(115,false)]
theorem der_34170 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34170 :=
  CNF.rup_sound cl_34170 [cl_3440,cl_23921] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3440 v h) (hints_cons _ _ _ (der_23921 v h) (by intro d hd; cases hd)))
def cl_34171 : CNF.NClause := [(44,true),(36,true),(55,true),(33,true),(59,true),(115,false)]
theorem der_34171 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34171 :=
  CNF.rup_sound cl_34171 [cl_3448,cl_23921] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3448 v h) (hints_cons _ _ _ (der_23921 v h) (by intro d hd; cases hd)))
def cl_34172 : CNF.NClause := [(47,true),(36,true),(55,true),(33,true),(59,true),(115,false)]
theorem der_34172 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34172 :=
  CNF.rup_sound cl_34172 [cl_3452,cl_23921] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3452 v h) (hints_cons _ _ _ (der_23921 v h) (by intro d hd; cases hd)))
def cl_34173 : CNF.NClause := [(47,true),(44,true),(55,true),(33,true),(59,true),(115,false)]
theorem der_34173 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34173 :=
  CNF.rup_sound cl_34173 [cl_3454,cl_23921] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3454 v h) (hints_cons _ _ _ (der_23921 v h) (by intro d hd; cases hd)))
def cl_34174 : CNF.NClause := [(47,true),(44,true),(36,true),(55,true),(59,true),(115,false)]
theorem der_34174 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34174 :=
  CNF.rup_sound cl_34174 [cl_3455,cl_23921] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3455 v h) (hints_cons _ _ _ (der_23921 v h) (by intro d hd; cases hd)))
def cl_34175 : CNF.NClause := [(42,true),(48,true),(36,true),(57,true),(35,true),(114,false)]
theorem der_34175 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34175 :=
  CNF.rup_sound cl_34175 [cl_3376,cl_23922] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3376 v h) (hints_cons _ _ _ (der_23922 v h) (by intro d hd; cases hd)))
def cl_34176 : CNF.NClause := [(42,true),(36,true),(54,true),(57,true),(35,true),(114,false)]
theorem der_34176 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34176 :=
  CNF.rup_sound cl_34176 [cl_3384,cl_23922] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3384 v h) (hints_cons _ _ _ (der_23922 v h) (by intro d hd; cases hd)))
def cl_34177 : CNF.NClause := [(114,false),(36,true),(54,true),(57,true),(35,true),(48,true)]
theorem der_34177 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34177 :=
  CNF.rup_sound cl_34177 [cl_3388,cl_34175] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3388 v h) (hints_cons _ _ _ (der_34175 v h) (by intro d hd; cases hd)))
def cl_34178 : CNF.NClause := [(42,true),(48,true),(54,true),(57,true),(35,true),(114,false)]
theorem der_34178 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34178 :=
  CNF.rup_sound cl_34178 [cl_3390,cl_23922] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3390 v h) (hints_cons _ _ _ (der_23922 v h) (by intro d hd; cases hd)))
def cl_34179 : CNF.NClause := [(42,true),(48,true),(36,true),(54,true),(57,true),(114,false)]
theorem der_34179 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34179 :=
  CNF.rup_sound cl_34179 [cl_3391,cl_23922] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3391 v h) (hints_cons _ _ _ (der_23922 v h) (by intro d hd; cases hd)))
def cl_34180 : CNF.NClause := [(45,true),(49,true),(53,true),(36,true),(32,true),(117,false)]
theorem der_34180 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34180 :=
  CNF.rup_sound cl_34180 [cl_3552,cl_23923] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3552 v h) (hints_cons _ _ _ (der_23923 v h) (by intro d hd; cases hd)))
def cl_34181 : CNF.NClause := [(45,true),(53,true),(36,true),(60,true),(32,true),(117,false)]
theorem der_34181 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34181 :=
  CNF.rup_sound cl_34181 [cl_3576,cl_23923] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3576 v h) (hints_cons _ _ _ (der_23923 v h) (by intro d hd; cases hd)))
def cl_34182 : CNF.NClause := [(49,true),(53,true),(36,true),(60,true),(32,true),(117,false)]
theorem der_34182 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34182 :=
  CNF.rup_sound cl_34182 [cl_3580,cl_23923] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3580 v h) (hints_cons _ _ _ (der_23923 v h) (by intro d hd; cases hd)))
def cl_34184 : CNF.NClause := [(45,true),(49,true),(53,true),(36,true),(60,true),(117,false)]
theorem der_34184 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34184 :=
  CNF.rup_sound cl_34184 [cl_3583,cl_23923] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3583 v h) (hints_cons _ _ _ (der_23923 v h) (by intro d hd; cases hd)))
def cl_34185 : CNF.NClause := [(39,true),(38,true),(37,true),(36,true),(61,true),(113,false)]
theorem der_34185 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34185 :=
  CNF.rup_sound cl_34185 [cl_3312,cl_23924] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3312 v h) (hints_cons _ _ _ (der_23924 v h) (by intro d hd; cases hd)))
def cl_34186 : CNF.NClause := [(37,true),(38,true),(40,true),(36,true),(61,true),(113,false)]
theorem der_34186 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34186 :=
  CNF.rup_sound cl_34186 [cl_3320,cl_23924] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3320 v h) (hints_cons _ _ _ (der_23924 v h) (by intro d hd; cases hd)))
def cl_34187 : CNF.NClause := [(39,true),(37,true),(40,true),(36,true),(61,true),(113,false)]
theorem der_34187 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34187 :=
  CNF.rup_sound cl_34187 [cl_3324,cl_23924] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3324 v h) (hints_cons _ _ _ (der_23924 v h) (by intro d hd; cases hd)))
def cl_34188 : CNF.NClause := [(39,true),(38,true),(40,true),(36,true),(61,true),(113,false)]
theorem der_34188 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34188 :=
  CNF.rup_sound cl_34188 [cl_3326,cl_23924] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3326 v h) (hints_cons _ _ _ (der_23924 v h) (by intro d hd; cases hd)))
def cl_34189 : CNF.NClause := [(39,true),(38,true),(37,true),(40,true),(61,true),(113,false)]
theorem der_34189 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34189 :=
  CNF.rup_sound cl_34189 [cl_3327,cl_23924] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3327 v h) (hints_cons _ _ _ (der_23924 v h) (by intro d hd; cases hd)))
def cl_34190 : CNF.NClause := [(40,true),(46,true),(43,true),(59,true),(32,true),(112,false)]
theorem der_34190 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34190 :=
  CNF.rup_sound cl_34190 [cl_3248,cl_23925] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3248 v h) (hints_cons _ _ _ (der_23925 v h) (by intro d hd; cases hd)))
def cl_34191 : CNF.NClause := [(40,true),(43,true),(54,true),(59,true),(32,true),(112,false)]
theorem der_34191 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34191 :=
  CNF.rup_sound cl_34191 [cl_3256,cl_23925] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3256 v h) (hints_cons _ _ _ (der_23925 v h) (by intro d hd; cases hd)))
def cl_34192 : CNF.NClause := [(40,true),(112,false),(46,true),(54,true),(59,true),(32,true)]
theorem der_34192 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34192 :=
  CNF.rup_sound cl_34192 [cl_3260,cl_23925] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3260 v h) (hints_cons _ _ _ (der_23925 v h) (by intro d hd; cases hd)))
def cl_34193 : CNF.NClause := [(46,true),(43,true),(54,true),(59,true),(32,true),(112,false)]
theorem der_34193 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34193 :=
  CNF.rup_sound cl_34193 [cl_3262,cl_23925] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3262 v h) (hints_cons _ _ _ (der_23925 v h) (by intro d hd; cases hd)))
def cl_34194 : CNF.NClause := [(40,true),(46,true),(43,true),(54,true),(59,true),(112,false)]
theorem der_34194 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34194 :=
  CNF.rup_sound cl_34194 [cl_3263,cl_23925] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3263 v h) (hints_cons _ _ _ (der_23925 v h) (by intro d hd; cases hd)))
def cl_34196 : CNF.NClause := [(38,true),(56,true),(48,true),(43,true),(33,true),(95,false)]
theorem der_34196 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34196 :=
  CNF.rup_sound cl_34196 [cl_2160,cl_23926] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2160 v h) (hints_cons _ _ _ (der_23926 v h) (by intro d hd; cases hd)))
def cl_34197 : CNF.NClause := [(38,true),(53,true),(43,true),(56,true),(33,true),(95,false)]
theorem der_34197 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34197 :=
  CNF.rup_sound cl_34197 [cl_2168,cl_23926] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2168 v h) (hints_cons _ _ _ (der_23926 v h) (by intro d hd; cases hd)))
def cl_34198 : CNF.NClause := [(38,true),(48,true),(53,true),(56,true),(33,true),(95,false)]
theorem der_34198 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34198 :=
  CNF.rup_sound cl_34198 [cl_2172,cl_23926] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2172 v h) (hints_cons _ _ _ (der_23926 v h) (by intro d hd; cases hd)))
def cl_34199 : CNF.NClause := [(48,true),(53,true),(43,true),(56,true),(33,true),(95,false)]
theorem der_34199 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34199 :=
  CNF.rup_sound cl_34199 [cl_2174,cl_23926] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2174 v h) (hints_cons _ _ _ (der_23926 v h) (by intro d hd; cases hd)))
def cl_34200 : CNF.NClause := [(47,true),(39,true),(43,true),(60,true),(35,true),(99,false)]
theorem der_34200 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34200 :=
  CNF.rup_sound cl_34200 [cl_2416,cl_23927] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2416 v h) (hints_cons _ _ _ (der_23927 v h) (by intro d hd; cases hd)))
def cl_34201 : CNF.NClause := [(39,true),(43,true),(60,true),(51,true),(35,true),(99,false)]
theorem der_34201 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34201 :=
  CNF.rup_sound cl_34201 [cl_2424,cl_23927] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2424 v h) (hints_cons _ _ _ (der_23927 v h) (by intro d hd; cases hd)))
def cl_34202 : CNF.NClause := [(47,true),(39,true),(60,true),(51,true),(35,true),(99,false)]
theorem der_34202 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34202 :=
  CNF.rup_sound cl_34202 [cl_2428,cl_23927] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2428 v h) (hints_cons _ _ _ (der_23927 v h) (by intro d hd; cases hd)))
def cl_34203 : CNF.NClause := [(47,true),(43,true),(60,true),(51,true),(35,true),(99,false)]
theorem der_34203 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34203 :=
  CNF.rup_sound cl_34203 [cl_2430,cl_23927] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2430 v h) (hints_cons _ _ _ (der_23927 v h) (by intro d hd; cases hd)))
def cl_34204 : CNF.NClause := [(47,true),(39,true),(43,true),(60,true),(51,true),(99,false)]
theorem der_34204 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34204 :=
  CNF.rup_sound cl_34204 [cl_2431,cl_23927] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2431 v h) (hints_cons _ _ _ (der_23927 v h) (by intro d hd; cases hd)))
def cl_34206 : CNF.NClause := [(44,true),(42,true),(43,true),(41,true),(61,true),(103,false)]
theorem der_34206 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34206 :=
  CNF.rup_sound cl_34206 [cl_2672,cl_23931] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2672 v h) (hints_cons _ _ _ (der_23931 v h) (by intro d hd; cases hd)))
def cl_34207 : CNF.NClause := [(45,true),(42,true),(43,true),(41,true),(61,true),(103,false)]
theorem der_34207 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34207 :=
  CNF.rup_sound cl_34207 [cl_2680,cl_23931] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2680 v h) (hints_cons _ _ _ (der_23931 v h) (by intro d hd; cases hd)))
def cl_34208 : CNF.NClause := [(45,true),(44,true),(42,true),(41,true),(61,true),(103,false)]
theorem der_34208 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34208 :=
  CNF.rup_sound cl_34208 [cl_2684,cl_23931] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2684 v h) (hints_cons _ _ _ (der_23931 v h) (by intro d hd; cases hd)))
def cl_34209 : CNF.NClause := [(45,true),(44,true),(43,true),(41,true),(61,true),(103,false)]
theorem der_34209 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34209 :=
  CNF.rup_sound cl_34209 [cl_2686,cl_23931] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2686 v h) (hints_cons _ _ _ (der_23931 v h) (by intro d hd; cases hd)))
def cl_34210 : CNF.NClause := [(37,true),(44,true),(46,true),(58,true),(35,true),(109,false)]
theorem der_34210 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34210 :=
  CNF.rup_sound cl_34210 [cl_3056,cl_23936] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3056 v h) (hints_cons _ _ _ (der_23936 v h) (by intro d hd; cases hd)))
def cl_34211 : CNF.NClause := [(37,true),(44,true),(53,true),(58,true),(35,true),(109,false)]
theorem der_34211 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34211 :=
  CNF.rup_sound cl_34211 [cl_3064,cl_23936] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3064 v h) (hints_cons _ _ _ (der_23936 v h) (by intro d hd; cases hd)))
def cl_34212 : CNF.NClause := [(37,true),(53,true),(46,true),(58,true),(35,true),(109,false)]
theorem der_34212 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34212 :=
  CNF.rup_sound cl_34212 [cl_3068,cl_23936] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3068 v h) (hints_cons _ _ _ (der_23936 v h) (by intro d hd; cases hd)))
def cl_34213 : CNF.NClause := [(44,true),(53,true),(46,true),(58,true),(35,true),(109,false)]
theorem der_34213 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34213 :=
  CNF.rup_sound cl_34213 [cl_3070,cl_23936] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3070 v h) (hints_cons _ _ _ (der_23936 v h) (by intro d hd; cases hd)))
def cl_34214 : CNF.NClause := [(37,true),(44,true),(53,true),(46,true),(58,true),(109,false)]
theorem der_34214 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34214 :=
  CNF.rup_sound cl_34214 [cl_3071,cl_23936] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3071 v h) (hints_cons _ _ _ (der_23936 v h) (by intro d hd; cases hd)))
def cl_34215 : CNF.NClause := [(45,true),(39,true),(46,true),(52,true),(33,true),(110,false)]
theorem der_34215 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34215 :=
  CNF.rup_sound cl_34215 [cl_3104,cl_23938] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3104 v h) (hints_cons _ _ _ (der_23938 v h) (by intro d hd; cases hd)))
def cl_34216 : CNF.NClause := [(45,true),(39,true),(46,true),(33,true),(57,true),(110,false)]
theorem der_34216 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34216 :=
  CNF.rup_sound cl_34216 [cl_3120,cl_23938] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3120 v h) (hints_cons _ _ _ (der_23938 v h) (by intro d hd; cases hd)))
def cl_34217 : CNF.NClause := [(46,true),(42,true),(38,true),(55,true),(34,true),(111,false)]
theorem der_34217 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34217 :=
  CNF.rup_sound cl_34217 [cl_3168,cl_23939] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3168 v h) (hints_cons _ _ _ (der_23939 v h) (by intro d hd; cases hd)))
def cl_34218 : CNF.NClause := [(60,true),(42,true),(46,true),(38,true),(34,true),(111,false)]
theorem der_34218 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34218 :=
  CNF.rup_sound cl_34218 [cl_3184,cl_23939] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3184 v h) (hints_cons _ _ _ (der_23939 v h) (by intro d hd; cases hd)))
def cl_34219 : CNF.NClause := [(111,false),(42,true),(55,true),(60,true),(34,true),(38,true)]
theorem der_34219 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34219 :=
  CNF.rup_sound cl_34219 [cl_3192,cl_23939] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3192 v h) (hints_cons _ _ _ (der_23939 v h) (by intro d hd; cases hd)))
def cl_34220 : CNF.NClause := [(111,false),(46,true),(55,true),(60,true),(34,true),(38,true)]
theorem der_34220 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34220 :=
  CNF.rup_sound cl_34220 [cl_3196,cl_23939] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3196 v h) (hints_cons _ _ _ (der_23939 v h) (by intro d hd; cases hd)))
def cl_34221 : CNF.NClause := [(42,true),(46,true),(55,true),(60,true),(34,true),(111,false)]
theorem der_34221 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34221 :=
  CNF.rup_sound cl_34221 [cl_3198,cl_23939] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3198 v h) (hints_cons _ _ _ (der_23939 v h) (by intro d hd; cases hd)))
def cl_34222 : CNF.NClause := [(47,true),(106,false),(40,true),(34,true),(41,true),(57,true)]
theorem der_34222 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34222 :=
  CNF.rup_sound cl_34222 [cl_2864,cl_23940] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2864 v h) (hints_cons _ _ _ (der_23940 v h) (by intro d hd; cases hd)))
def cl_34223 : CNF.NClause := [(40,true),(53,true),(34,true),(41,true),(57,true),(106,false)]
theorem der_34223 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34223 :=
  CNF.rup_sound cl_34223 [cl_2872,cl_23940] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2872 v h) (hints_cons _ _ _ (der_23940 v h) (by intro d hd; cases hd)))
def cl_34224 : CNF.NClause := [(47,true),(40,true),(53,true),(34,true),(57,true),(106,false)]
theorem der_34224 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34224 :=
  CNF.rup_sound cl_34224 [cl_2876,cl_23940] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2876 v h) (hints_cons _ _ _ (der_23940 v h) (by intro d hd; cases hd)))
def cl_34225 : CNF.NClause := [(47,true),(53,true),(34,true),(41,true),(57,true),(106,false)]
theorem der_34225 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34225 :=
  CNF.rup_sound cl_34225 [cl_2878,cl_23940] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2878 v h) (hints_cons _ _ _ (der_23940 v h) (by intro d hd; cases hd)))
def cl_34226 : CNF.NClause := [(47,true),(40,true),(53,true),(41,true),(57,true),(106,false)]
theorem der_34226 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34226 :=
  CNF.rup_sound cl_34226 [cl_2879,cl_23940] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2879 v h) (hints_cons _ _ _ (der_23940 v h) (by intro d hd; cases hd)))
def cl_34227 : CNF.NClause := [(47,true),(37,true),(42,true),(56,true),(32,true),(97,false)]
theorem der_34227 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34227 :=
  CNF.rup_sound cl_34227 [cl_2288,cl_23941] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2288 v h) (hints_cons _ _ _ (der_23941 v h) (by intro d hd; cases hd)))
def cl_34228 : CNF.NClause := [(37,true),(42,true),(56,true),(52,true),(32,true),(97,false)]
theorem der_34228 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34228 :=
  CNF.rup_sound cl_34228 [cl_2296,cl_23941] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2296 v h) (hints_cons _ _ _ (der_23941 v h) (by intro d hd; cases hd)))
def cl_34229 : CNF.NClause := [(47,true),(37,true),(56,true),(52,true),(32,true),(97,false)]
theorem der_34229 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34229 :=
  CNF.rup_sound cl_34229 [cl_2300,cl_23941] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2300 v h) (hints_cons _ _ _ (der_23941 v h) (by intro d hd; cases hd)))
def cl_34230 : CNF.NClause := [(47,true),(42,true),(56,true),(52,true),(32,true),(97,false)]
theorem der_34230 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34230 :=
  CNF.rup_sound cl_34230 [cl_2302,cl_23941] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2302 v h) (hints_cons _ _ _ (der_23941 v h) (by intro d hd; cases hd)))
def cl_34231 : CNF.NClause := [(47,true),(37,true),(42,true),(56,true),(52,true),(97,false)]
theorem der_34231 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34231 :=
  CNF.rup_sound cl_34231 [cl_2303,cl_23941] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2303 v h) (hints_cons _ _ _ (der_23941 v h) (by intro d hd; cases hd)))
def cl_34232 : CNF.NClause := [(49,true),(38,true),(52,true),(41,true),(35,true),(104,false)]
theorem der_34232 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34232 :=
  CNF.rup_sound cl_34232 [cl_2720,cl_23943] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2720 v h) (hints_cons _ _ _ (der_23943 v h) (by intro d hd; cases hd)))
def cl_34233 : CNF.NClause := [(49,true),(38,true),(41,true),(59,true),(35,true),(104,false)]
theorem der_34233 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34233 :=
  CNF.rup_sound cl_34233 [cl_2736,cl_23943] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2736 v h) (hints_cons _ _ _ (der_23943 v h) (by intro d hd; cases hd)))
def cl_34234 : CNF.NClause := [(35,true),(52,true),(41,true),(59,true),(38,true),(104,false)]
theorem der_34234 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34234 :=
  CNF.rup_sound cl_34234 [cl_2744,cl_23943] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2744 v h) (hints_cons _ _ _ (der_23943 v h) (by intro d hd; cases hd)))
def cl_34235 : CNF.NClause := [(49,true),(38,true),(52,true),(59,true),(35,true),(104,false)]
theorem der_34235 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34235 :=
  CNF.rup_sound cl_34235 [cl_2748,cl_23943] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2748 v h) (hints_cons _ _ _ (der_23943 v h) (by intro d hd; cases hd)))
def cl_34236 : CNF.NClause := [(49,true),(52,true),(41,true),(59,true),(35,true),(104,false)]
theorem der_34236 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34236 :=
  CNF.rup_sound cl_34236 [cl_2750,cl_23943] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2750 v h) (hints_cons _ _ _ (der_23943 v h) (by intro d hd; cases hd)))
def cl_34237 : CNF.NClause := [(31,true),(34,true),(33,true),(61,true),(32,true),(118,false)]
theorem der_34237 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34237 :=
  CNF.rup_sound cl_34237 [cl_3632,cl_23944] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3632 v h) (hints_cons _ _ _ (der_23944 v h) (by intro d hd; cases hd)))
def cl_34238 : CNF.NClause := [(31,true),(33,true),(61,true),(32,true),(35,true),(118,false)]
theorem der_34238 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34238 :=
  CNF.rup_sound cl_34238 [cl_3640,cl_23944] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3640 v h) (hints_cons _ _ _ (der_23944 v h) (by intro d hd; cases hd)))
def cl_34239 : CNF.NClause := [(31,true),(35,true),(34,true),(61,true),(32,true),(118,false)]
theorem der_34239 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34239 :=
  CNF.rup_sound cl_34239 [cl_3644,cl_23944] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3644 v h) (hints_cons _ _ _ (der_23944 v h) (by intro d hd; cases hd)))
def cl_34240 : CNF.NClause := [(31,true),(34,true),(33,true),(61,true),(35,true),(118,false)]
theorem der_34240 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34240 :=
  CNF.rup_sound cl_34240 [cl_3646,cl_23944] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3646 v h) (hints_cons _ _ _ (der_23944 v h) (by intro d hd; cases hd)))
def cl_34243 : CNF.NClause := [(45,true),(40,true),(56,true),(50,true),(35,true),(94,false)]
theorem der_34243 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34243 :=
  CNF.rup_sound cl_34243 [cl_2096,cl_23945] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2096 v h) (hints_cons _ _ _ (der_23945 v h) (by intro d hd; cases hd)))
def cl_34244 : CNF.NClause := [(45,true),(40,true),(56,true),(55,true),(35,true),(94,false)]
theorem der_34244 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34244 :=
  CNF.rup_sound cl_34244 [cl_2104,cl_23945] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2104 v h) (hints_cons _ _ _ (der_23945 v h) (by intro d hd; cases hd)))
def cl_34245 : CNF.NClause := [(40,true),(56,true),(55,true),(50,true),(35,true),(94,false)]
theorem der_34245 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34245 :=
  CNF.rup_sound cl_34245 [cl_2108,cl_23945] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2108 v h) (hints_cons _ _ _ (der_23945 v h) (by intro d hd; cases hd)))
def cl_34246 : CNF.NClause := [(45,true),(56,true),(55,true),(50,true),(35,true),(94,false)]
theorem der_34246 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34246 :=
  CNF.rup_sound cl_34246 [cl_2110,cl_23945] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2110 v h) (hints_cons _ _ _ (der_23945 v h) (by intro d hd; cases hd)))
def cl_34248 : CNF.NClause := [(53,true),(54,true),(52,true),(61,true),(51,true),(98,false)]
theorem der_34248 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34248 :=
  CNF.rup_sound cl_34248 [cl_2352,cl_23950] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2352 v h) (hints_cons _ _ _ (der_23950 v h) (by intro d hd; cases hd)))
def cl_34249 : CNF.NClause := [(53,true),(55,true),(52,true),(61,true),(51,true),(98,false)]
theorem der_34249 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34249 :=
  CNF.rup_sound cl_34249 [cl_2360,cl_23950] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2360 v h) (hints_cons _ _ _ (der_23950 v h) (by intro d hd; cases hd)))
def cl_34250 : CNF.NClause := [(55,true),(52,true),(54,true),(61,true),(51,true),(98,false)]
theorem der_34250 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34250 :=
  CNF.rup_sound cl_34250 [cl_2364,cl_23950] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2364 v h) (hints_cons _ _ _ (der_23950 v h) (by intro d hd; cases hd)))
def cl_34251 : CNF.NClause := [(53,true),(55,true),(54,true),(61,true),(51,true),(98,false)]
theorem der_34251 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34251 :=
  CNF.rup_sound cl_34251 [cl_2366,cl_23950] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2366 v h) (hints_cons _ _ _ (der_23950 v h) (by intro d hd; cases hd)))
def cl_34252 : CNF.NClause := [(45,true),(37,true),(48,true),(34,true),(59,true),(101,false)]
theorem der_34252 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34252 :=
  CNF.rup_sound cl_34252 [cl_2544,cl_23951] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2544 v h) (hints_cons _ _ _ (der_23951 v h) (by intro d hd; cases hd)))
def cl_34253 : CNF.NClause := [(45,true),(37,true),(34,true),(59,true),(51,true),(101,false)]
theorem der_34253 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34253 :=
  CNF.rup_sound cl_34253 [cl_2552,cl_23951] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2552 v h) (hints_cons _ _ _ (der_23951 v h) (by intro d hd; cases hd)))
def cl_34254 : CNF.NClause := [(37,true),(48,true),(34,true),(59,true),(51,true),(101,false)]
theorem der_34254 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34254 :=
  CNF.rup_sound cl_34254 [cl_2556,cl_23951] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2556 v h) (hints_cons _ _ _ (der_23951 v h) (by intro d hd; cases hd)))
def cl_34255 : CNF.NClause := [(45,true),(48,true),(34,true),(59,true),(51,true),(101,false)]
theorem der_34255 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34255 :=
  CNF.rup_sound cl_34255 [cl_2558,cl_23951] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2558 v h) (hints_cons _ _ _ (der_23951 v h) (by intro d hd; cases hd)))
def cl_34256 : CNF.NClause := [(45,true),(37,true),(48,true),(59,true),(51,true),(101,false)]
theorem der_34256 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34256 :=
  CNF.rup_sound cl_34256 [cl_2559,cl_23951] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2559 v h) (hints_cons _ _ _ (der_23951 v h) (by intro d hd; cases hd)))
def cl_34257 : CNF.NClause := [(57,true),(58,true),(61,true),(59,true),(56,true),(93,false)]
theorem der_34257 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34257 :=
  CNF.rup_sound cl_34257 [cl_2032,cl_23952] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2032 v h) (hints_cons _ _ _ (der_23952 v h) (by intro d hd; cases hd)))
def cl_34258 : CNF.NClause := [(61,true),(58,true),(60,true),(56,true),(57,true),(93,false)]
theorem der_34258 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34258 :=
  CNF.rup_sound cl_34258 [cl_2040,cl_23952] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2040 v h) (hints_cons _ _ _ (der_23952 v h) (by intro d hd; cases hd)))
def cl_34259 : CNF.NClause := [(61,true),(60,true),(56,true),(59,true),(57,true),(93,false)]
theorem der_34259 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34259 :=
  CNF.rup_sound cl_34259 [cl_2044,cl_23952] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2044 v h) (hints_cons _ _ _ (der_23952 v h) (by intro d hd; cases hd)))
def cl_34260 : CNF.NClause := [(59,true),(58,true),(60,true),(61,true),(56,true),(93,false)]
theorem der_34260 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34260 :=
  CNF.rup_sound cl_34260 [cl_2046,cl_23952] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2046 v h) (hints_cons _ _ _ (der_23952 v h) (by intro d hd; cases hd)))
def cl_34262 : CNF.NClause := [(37,true),(60,true),(41,true),(50,true),(33,true),(105,false)]
theorem der_34262 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34262 :=
  CNF.rup_sound cl_34262 [cl_2800,cl_23953] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2800 v h) (hints_cons _ _ _ (der_23953 v h) (by intro d hd; cases hd)))
def cl_34263 : CNF.NClause := [(37,true),(54,true),(60,true),(41,true),(33,true),(105,false)]
theorem der_34263 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34263 :=
  CNF.rup_sound cl_34263 [cl_2808,cl_23953] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2808 v h) (hints_cons _ _ _ (der_23953 v h) (by intro d hd; cases hd)))
def cl_34264 : CNF.NClause := [(37,true),(54,true),(60,true),(50,true),(33,true),(105,false)]
theorem der_34264 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34264 :=
  CNF.rup_sound cl_34264 [cl_2812,cl_23953] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2812 v h) (hints_cons _ _ _ (der_23953 v h) (by intro d hd; cases hd)))
def cl_34265 : CNF.NClause := [(54,true),(60,true),(41,true),(50,true),(33,true),(105,false)]
theorem der_34265 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34265 :=
  CNF.rup_sound cl_34265 [cl_2814,cl_23953] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2814 v h) (hints_cons _ _ _ (der_23953 v h) (by intro d hd; cases hd)))
def cl_34266 : CNF.NClause := [(37,true),(41,true),(54,true),(60,true),(50,true),(105,false)]
theorem der_34266 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34266 :=
  CNF.rup_sound cl_34266 [cl_2815,cl_23953] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2815 v h) (hints_cons _ _ _ (der_23953 v h) (by intro d hd; cases hd)))
def cl_34267 : CNF.NClause := [(49,true),(40,true),(42,true),(58,true),(33,true),(100,false)]
theorem der_34267 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34267 :=
  CNF.rup_sound cl_34267 [cl_2480,cl_23954] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2480 v h) (hints_cons _ _ _ (der_23954 v h) (by intro d hd; cases hd)))
def cl_34268 : CNF.NClause := [(40,true),(42,true),(58,true),(33,true),(51,true),(100,false)]
theorem der_34268 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34268 :=
  CNF.rup_sound cl_34268 [cl_2488,cl_23954] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2488 v h) (hints_cons _ _ _ (der_23954 v h) (by intro d hd; cases hd)))
def cl_34269 : CNF.NClause := [(49,true),(40,true),(58,true),(33,true),(51,true),(100,false)]
theorem der_34269 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34269 :=
  CNF.rup_sound cl_34269 [cl_2492,cl_23954] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2492 v h) (hints_cons _ _ _ (der_23954 v h) (by intro d hd; cases hd)))
def cl_34270 : CNF.NClause := [(49,true),(42,true),(58,true),(33,true),(51,true),(100,false)]
theorem der_34270 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34270 :=
  CNF.rup_sound cl_34270 [cl_2494,cl_23954] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2494 v h) (hints_cons _ _ _ (der_23954 v h) (by intro d hd; cases hd)))
def cl_34271 : CNF.NClause := [(49,true),(40,true),(42,true),(58,true),(51,true),(100,false)]
theorem der_34271 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34271 :=
  CNF.rup_sound cl_34271 [cl_2495,cl_23954] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2495 v h) (hints_cons _ _ _ (der_23954 v h) (by intro d hd; cases hd)))
def cl_34273 : CNF.NClause := [(39,true),(55,true),(58,true),(41,true),(32,true),(107,false)]
theorem der_34273 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34273 :=
  CNF.rup_sound cl_34273 [cl_2936,cl_23955] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2936 v h) (hints_cons _ _ _ (der_23955 v h) (by intro d hd; cases hd)))
def cl_34275 : CNF.NClause := [(32,true),(55,true),(58,true),(41,true),(48,true),(107,false)]
theorem der_34275 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34275 :=
  CNF.rup_sound cl_34275 [cl_2942,cl_23955] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2942 v h) (hints_cons _ _ _ (der_23955 v h) (by intro d hd; cases hd)))
def cl_34276 : CNF.NClause := [(39,true),(48,true),(55,true),(58,true),(41,true),(107,false)]
theorem der_34276 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34276 :=
  CNF.rup_sound cl_34276 [cl_2943,cl_23955] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2943 v h) (hints_cons _ _ _ (der_23955 v h) (by intro d hd; cases hd)))
def cl_34278 : CNF.NClause := [(49,true),(39,true),(44,true),(56,true),(34,true),(96,false)]
theorem der_34278 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34278 :=
  CNF.rup_sound cl_34278 [cl_2224,cl_23956] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2224 v h) (hints_cons _ _ _ (der_23956 v h) (by intro d hd; cases hd)))
def cl_34279 : CNF.NClause := [(39,true),(44,true),(56,true),(54,true),(34,true),(96,false)]
theorem der_34279 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34279 :=
  CNF.rup_sound cl_34279 [cl_2232,cl_23956] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2232 v h) (hints_cons _ _ _ (der_23956 v h) (by intro d hd; cases hd)))
def cl_34280 : CNF.NClause := [(49,true),(39,true),(56,true),(54,true),(34,true),(96,false)]
theorem der_34280 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34280 :=
  CNF.rup_sound cl_34280 [cl_2236,cl_23956] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2236 v h) (hints_cons _ _ _ (der_23956 v h) (by intro d hd; cases hd)))
def cl_34281 : CNF.NClause := [(49,true),(44,true),(56,true),(54,true),(34,true),(96,false)]
theorem der_34281 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34281 :=
  CNF.rup_sound cl_34281 [cl_2238,cl_23956] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2238 v h) (hints_cons _ _ _ (der_23956 v h) (by intro d hd; cases hd)))
def cl_34282 : CNF.NClause := [(102,false),(44,true),(50,true),(51,true),(32,true),(38,true)]
theorem der_34282 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34282 :=
  CNF.rup_sound cl_34282 [cl_2592,cl_23957] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2592 v h) (hints_cons _ _ _ (der_23957 v h) (by intro d hd; cases hd)))
def cl_34283 : CNF.NClause := [(50,true),(44,true),(38,true),(32,true),(57,true),(102,false)]
theorem der_34283 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34283 :=
  CNF.rup_sound cl_34283 [cl_2608,cl_23957] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2608 v h) (hints_cons _ _ _ (der_23957 v h) (by intro d hd; cases hd)))
def cl_34284 : CNF.NClause := [(32,true),(44,true),(51,true),(38,true),(57,true),(102,false)]
theorem der_34284 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34284 :=
  CNF.rup_sound cl_34284 [cl_2616,cl_23957] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2616 v h) (hints_cons _ _ _ (der_23957 v h) (by intro d hd; cases hd)))
def cl_34285 : CNF.NClause := [(32,true),(50,true),(51,true),(38,true),(57,true),(102,false)]
theorem der_34285 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34285 :=
  CNF.rup_sound cl_34285 [cl_2620,cl_23957] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2620 v h) (hints_cons _ _ _ (der_23957 v h) (by intro d hd; cases hd)))
def cl_34286 : CNF.NClause := [(44,true),(50,true),(51,true),(32,true),(57,true),(102,false)]
theorem der_34286 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34286 :=
  CNF.rup_sound cl_34286 [cl_2622,cl_23957] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2622 v h) (hints_cons _ _ _ (der_23957 v h) (by intro d hd; cases hd)))
def cl_34287 : CNF.NClause := [(19,false),(3,false),(27,false),(12,false),(85,true),(5,true)]
theorem der_34287 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34287 :=
  CNF.rup_sound cl_34287 [cl_1475,cl_24094] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1475 v h) (hints_cons _ _ _ (der_24094 v h) (by intro d hd; cases hd)))
def cl_34288 : CNF.NClause := [(49,false),(86,false),(69,false),(73,false),(65,false),(91,true)]
theorem der_34288 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34288 :=
  CNF.rup_sound cl_34288 [cl_29038,cl_26319] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29038 v h) (hints_cons _ _ _ (der_26319 v h) (by intro d hd; cases hd)))
def cl_34290 : CNF.NClause := [(31,false),(90,true),(88,false),(89,true),(91,true),(87,true)]
theorem der_34290 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34290 :=
  CNF.rup_sound cl_34290 [cl_15454,cl_30708] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15454 v h) (hints_cons _ _ _ (der_30708 v h) (by intro d hd; cases hd)))
def cl_34291 : CNF.NClause := [(31,false),(91,false),(88,false),(89,false),(90,true),(87,true)]
theorem der_34291 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34291 :=
  CNF.rup_sound cl_34291 [cl_15434,cl_30711] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15434 v h) (hints_cons _ _ _ (der_30711 v h) (by intro d hd; cases hd)))
def cl_34292 : CNF.NClause := [(53,false),(67,false),(64,false),(78,false),(75,false),(90,true)]
theorem der_34292 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34292 :=
  CNF.rup_sound cl_34292 [cl_29043,cl_32413] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29043 v h) (hints_cons _ _ _ (der_32413 v h) (by intro d hd; cases hd)))
def cl_34293 : CNF.NClause := [(45,false),(63,false),(86,true),(72,false),(79,false),(70,false)]
theorem der_34293 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34293 :=
  CNF.rup_sound cl_34293 [cl_29045,cl_26765] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29045 v h) (hints_cons _ _ _ (der_26765 v h) (by intro d hd; cases hd)))
def cl_34294 : CNF.NClause := [(53,false),(67,false),(22,true),(78,false),(75,false),(90,true)]
theorem der_34294 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34294 :=
  CNF.rup_sound cl_34294 [cl_29048,cl_34292] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29048 v h) (hints_cons _ _ _ (der_34292 v h) (by intro d hd; cases hd)))
def cl_34296 : CNF.NClause := [(49,false),(77,true),(69,false),(73,false),(18,false),(65,false)]
theorem der_34296 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34296 :=
  CNF.rup_sound cl_34296 [cl_29052,cl_26728] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29052 v h) (hints_cons _ _ _ (der_26728 v h) (by intro d hd; cases hd)))
def cl_34297 : CNF.NClause := [(49,false),(69,false),(18,true),(91,false),(73,false),(65,false)]
theorem der_34297 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34297 :=
  CNF.rup_sound cl_34297 [cl_29053,cl_32364] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29053 v h) (hints_cons _ _ _ (der_32364 v h) (by intro d hd; cases hd)))
def cl_34298 : CNF.NClause := [(49,false),(69,false),(77,false),(73,false),(65,false),(91,true)]
theorem der_34298 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34298 :=
  CNF.rup_sound cl_34298 [cl_29054,cl_29041] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29054 v h) (hints_cons _ _ _ (der_29041 v h) (by intro d hd; cases hd)))
def cl_34299 : CNF.NClause := [(52,false),(67,false),(79,false),(66,false),(73,false),(85,true)]
theorem der_34299 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34299 :=
  CNF.rup_sound cl_34299 [cl_29057,cl_29055] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29057 v h) (hints_cons _ _ _ (der_29055 v h) (by intro d hd; cases hd)))
def cl_34300 : CNF.NClause := [(44,false),(84,true),(72,false),(78,false),(71,false),(65,false)]
theorem der_34300 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34300 :=
  CNF.rup_sound cl_34300 [cl_29059,cl_26747] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29059 v h) (hints_cons _ _ _ (der_26747 v h) (by intro d hd; cases hd)))
def cl_34301 : CNF.NClause := [(47,false),(84,true),(77,false),(66,false),(75,false),(68,false)]
theorem der_34301 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34301 :=
  CNF.rup_sound cl_34301 [cl_29062,cl_29060] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29062 v h) (hints_cons _ _ _ (der_29060 v h) (by intro d hd; cases hd)))
def cl_34303 : CNF.NClause := [(47,false),(75,false),(84,true),(89,false),(66,false),(16,true)]
theorem der_34303 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34303 :=
  CNF.rup_sound cl_34303 [cl_29065,cl_32028] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29065 v h) (hints_cons _ _ _ (der_32028 v h) (by intro d hd; cases hd)))
def cl_34305 : CNF.NClause := [(52,false),(67,false),(66,false),(73,false),(85,true),(21,false)]
theorem der_34305 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34305 :=
  CNF.rup_sound cl_34305 [cl_29069,cl_29067] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29069 v h) (hints_cons _ _ _ (der_29067 v h) (by intro d hd; cases hd)))
def cl_34306 : CNF.NClause := [(45,false),(63,false),(86,true),(72,false),(14,false),(70,false)]
theorem der_34306 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34306 :=
  CNF.rup_sound cl_34306 [cl_29072,cl_29070] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29072 v h) (hints_cons _ _ _ (der_29070 v h) (by intro d hd; cases hd)))
def cl_34307 : CNF.NClause := [(52,false),(73,false),(88,false),(66,false),(21,true),(85,true)]
theorem der_34307 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34307 :=
  CNF.rup_sound cl_34307 [cl_29075,cl_32096] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29075 v h) (hints_cons _ _ _ (der_32096 v h) (by intro d hd; cases hd)))
def cl_34308 : CNF.NClause := [(52,false),(73,false),(79,true),(85,false),(21,true),(66,false)]
theorem der_34308 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34308 :=
  CNF.rup_sound cl_34308 [cl_29076,cl_32099] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29076 v h) (hints_cons _ _ _ (der_32099 v h) (by intro d hd; cases hd)))
def cl_34309 : CNF.NClause := [(52,false),(85,true),(67,false),(66,false),(73,false),(88,true)]
theorem der_34309 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34309 :=
  CNF.rup_sound cl_34309 [cl_29077,cl_34299] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29077 v h) (hints_cons _ _ _ (der_34299 v h) (by intro d hd; cases hd)))
def cl_34310 : CNF.NClause := [(45,false),(86,true),(63,false),(72,false),(89,false),(14,true)]
theorem der_34310 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34310 :=
  CNF.rup_sound cl_34310 [cl_29079,cl_32440] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29079 v h) (hints_cons _ _ _ (der_32440 v h) (by intro d hd; cases hd)))
def cl_34311 : CNF.NClause := [(45,false),(79,true),(63,false),(72,false),(86,false),(14,true)]
theorem der_34311 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34311 :=
  CNF.rup_sound cl_34311 [cl_29080,cl_32442] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29080 v h) (hints_cons _ _ _ (der_32442 v h) (by intro d hd; cases hd)))
def cl_34313 : CNF.NClause := [(75,false),(53,false),(90,false),(67,false),(64,false),(86,true)]
theorem der_34313 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34313 :=
  CNF.rup_sound cl_34313 [cl_29083,cl_32408] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29083 v h) (hints_cons _ _ _ (der_32408 v h) (by intro d hd; cases hd)))
def cl_34314 : CNF.NClause := [(53,false),(67,false),(64,false),(86,false),(75,false),(90,true)]
theorem der_34314 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34314 :=
  CNF.rup_sound cl_34314 [cl_29084,cl_32411] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29084 v h) (hints_cons _ _ _ (der_32411 v h) (by intro d hd; cases hd)))
def cl_34316 : CNF.NClause := [(44,false),(78,true),(72,false),(71,false),(84,false),(65,false)]
theorem der_34316 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34316 :=
  CNF.rup_sound cl_34316 [cl_29088,cl_26746] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29088 v h) (hints_cons _ _ _ (der_26746 v h) (by intro d hd; cases hd)))
def cl_34317 : CNF.NClause := [(44,false),(84,true),(72,false),(71,false),(65,false),(13,false)]
theorem der_34317 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34317 :=
  CNF.rup_sound cl_34317 [cl_29089,cl_29087] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29089 v h) (hints_cons _ _ _ (der_29087 v h) (by intro d hd; cases hd)))
def cl_34318 : CNF.NClause := [(75,false),(53,false),(86,true),(90,false),(67,false),(22,true)]
theorem der_34318 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34318 :=
  CNF.rup_sound cl_34318 [cl_29091,cl_34313] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29091 v h) (hints_cons _ _ _ (der_34313 v h) (by intro d hd; cases hd)))
def cl_34319 : CNF.NClause := [(53,false),(22,true),(67,false),(86,false),(75,false),(90,true)]
theorem der_34319 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34319 :=
  CNF.rup_sound cl_34319 [cl_29092,cl_29040] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29092 v h) (hints_cons _ _ _ (der_29040 v h) (by intro d hd; cases hd)))
def cl_34320 : CNF.NClause := [(90,true),(53,false),(86,true),(67,false),(75,false),(22,true)]
theorem der_34320 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34320 :=
  CNF.rup_sound cl_34320 [cl_29093,cl_34294] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29093 v h) (hints_cons _ _ _ (der_34294 v h) (by intro d hd; cases hd)))
def cl_34321 : CNF.NClause := [(45,false),(70,true),(63,false),(89,false),(79,false),(86,false)]
theorem der_34321 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34321 :=
  CNF.rup_sound cl_34321 [cl_29095,cl_32441] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29095 v h) (hints_cons _ _ _ (der_32441 v h) (by intro d hd; cases hd)))
def cl_34322 : CNF.NClause := [(45,false),(86,false),(63,false),(72,false),(89,false),(79,true)]
theorem der_34322 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34322 :=
  CNF.rup_sound cl_34322 [cl_29096,cl_34311] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29096 v h) (hints_cons _ _ _ (der_34311 v h) (by intro d hd; cases hd)))
def cl_34323 : CNF.NClause := [(45,false),(86,false),(72,true),(63,false),(89,false),(70,true)]
theorem der_34323 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34323 :=
  CNF.rup_sound cl_34323 [cl_29097,cl_32436] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29097 v h) (hints_cons _ _ _ (der_32436 v h) (by intro d hd; cases hd)))
def cl_34324 : CNF.NClause := [(45,false),(86,true),(63,false),(72,false),(89,false),(79,false)]
theorem der_34324 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34324 :=
  CNF.rup_sound cl_34324 [cl_29098,cl_32437] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29098 v h) (hints_cons _ _ _ (der_32437 v h) (by intro d hd; cases hd)))
def cl_34325 : CNF.NClause := [(45,false),(70,true),(72,true),(63,false),(89,false),(79,false)]
theorem der_34325 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34325 :=
  CNF.rup_sound cl_34325 [cl_29099,cl_32438] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29099 v h) (hints_cons _ _ _ (der_32438 v h) (by intro d hd; cases hd)))
def cl_34327 : CNF.NClause := [(45,false),(89,false),(86,true),(79,true),(63,false),(70,true)]
theorem der_34327 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34327 :=
  CNF.rup_sound cl_34327 [cl_29101,cl_32440] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29101 v h) (hints_cons _ _ _ (der_32440 v h) (by intro d hd; cases hd)))
def cl_34328 : CNF.NClause := [(45,false),(63,false),(70,true),(72,false),(79,false),(86,false)]
theorem der_34328 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34328 :=
  CNF.rup_sound cl_34328 [cl_29102,cl_32441] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29102 v h) (hints_cons _ _ _ (der_32441 v h) (by intro d hd; cases hd)))
def cl_34329 : CNF.NClause := [(45,false),(70,true),(63,false),(79,false),(86,false),(14,false)]
theorem der_34329 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34329 :=
  CNF.rup_sound cl_34329 [cl_29103,cl_34328] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29103 v h) (hints_cons _ _ _ (der_34328 v h) (by intro d hd; cases hd)))
def cl_34330 : CNF.NClause := [(45,false),(79,true),(63,false),(72,false),(86,false),(14,false)]
theorem der_34330 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34330 :=
  CNF.rup_sound cl_34330 [cl_29104,cl_34322] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29104 v h) (hints_cons _ _ _ (der_34322 v h) (by intro d hd; cases hd)))
def cl_34331 : CNF.NClause := [(45,false),(70,true),(72,true),(63,false),(86,false),(14,false)]
theorem der_34331 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34331 :=
  CNF.rup_sound cl_34331 [cl_29105,cl_34323] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29105 v h) (hints_cons _ _ _ (der_34323 v h) (by intro d hd; cases hd)))
def cl_34332 : CNF.NClause := [(45,false),(89,true),(86,true),(63,false),(72,false),(79,false)]
theorem der_34332 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34332 :=
  CNF.rup_sound cl_34332 [cl_29106,cl_34293] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29106 v h) (hints_cons _ _ _ (der_34293 v h) (by intro d hd; cases hd)))
def cl_34333 : CNF.NClause := [(45,false),(72,true),(63,false),(79,false),(14,false),(70,true)]
theorem der_34333 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34333 :=
  CNF.rup_sound cl_34333 [cl_29107,cl_34325] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29107 v h) (hints_cons _ _ _ (der_34325 v h) (by intro d hd; cases hd)))
def cl_34334 : CNF.NClause := [(45,false),(86,true),(63,false),(72,false),(14,false),(89,true)]
theorem der_34334 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34334 :=
  CNF.rup_sound cl_34334 [cl_29108,cl_34332] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29108 v h) (hints_cons _ _ _ (der_34332 v h) (by intro d hd; cases hd)))
def cl_34336 : CNF.NClause := [(45,false),(79,false),(70,true),(14,true),(89,false),(86,false)]
theorem der_34336 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34336 :=
  CNF.rup_sound cl_34336 [cl_29111,cl_29110] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29111 v h) (hints_cons _ _ _ (der_29110 v h) (by intro d hd; cases hd)))
def cl_34337 : CNF.NClause := [(45,false),(86,false),(79,true),(72,false),(14,true),(89,false)]
theorem der_34337 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34337 :=
  CNF.rup_sound cl_34337 [cl_29112,cl_34322] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29112 v h) (hints_cons _ _ _ (der_34322 v h) (by intro d hd; cases hd)))
def cl_34338 : CNF.NClause := [(45,false),(89,false),(70,true),(14,true),(72,true),(86,false)]
theorem der_34338 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34338 :=
  CNF.rup_sound cl_34338 [cl_29113,cl_34336] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29113 v h) (hints_cons _ _ _ (der_34336 v h) (by intro d hd; cases hd)))
def cl_34339 : CNF.NClause := [(45,false),(72,false),(14,true),(86,true),(89,false),(79,false)]
theorem der_34339 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34339 :=
  CNF.rup_sound cl_34339 [cl_29114,cl_29046] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29114 v h) (hints_cons _ _ _ (der_29046 v h) (by intro d hd; cases hd)))
def cl_34340 : CNF.NClause := [(45,false),(89,false),(70,true),(14,true),(72,true),(79,false)]
theorem der_34340 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34340 :=
  CNF.rup_sound cl_34340 [cl_29115,cl_32438] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29115 v h) (hints_cons _ _ _ (der_32438 v h) (by intro d hd; cases hd)))
def cl_34341 : CNF.NClause := [(45,false),(89,false),(70,true),(79,true),(14,true),(72,false)]
theorem der_34341 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34341 :=
  CNF.rup_sound cl_34341 [cl_29116,cl_34337] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29116 v h) (hints_cons _ _ _ (der_34337 v h) (by intro d hd; cases hd)))
def cl_34342 : CNF.NClause := [(45,false),(79,true),(70,true),(14,true),(72,true),(89,false)]
theorem der_34342 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34342 :=
  CNF.rup_sound cl_34342 [cl_29117,cl_34338] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29117 v h) (hints_cons _ _ _ (der_34338 v h) (by intro d hd; cases hd)))
def cl_34343 : CNF.NClause := [(45,false),(79,false),(70,true),(14,true),(72,false),(86,false)]
theorem der_34343 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34343 :=
  CNF.rup_sound cl_34343 [cl_29118,cl_34328] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29118 v h) (hints_cons _ _ _ (der_34328 v h) (by intro d hd; cases hd)))
def cl_34344 : CNF.NClause := [(45,false),(79,false),(70,true),(63,true),(14,true),(86,false)]
theorem der_34344 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34344 :=
  CNF.rup_sound cl_34344 [cl_29119,cl_34343] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29119 v h) (hints_cons _ _ _ (der_34343 v h) (by intro d hd; cases hd)))
def cl_34345 : CNF.NClause := [(45,false),(86,false),(70,true),(63,true),(14,true),(72,false)]
theorem der_34345 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34345 :=
  CNF.rup_sound cl_34345 [cl_29120,cl_34343] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29120 v h) (hints_cons _ _ _ (der_34343 v h) (by intro d hd; cases hd)))
def cl_34346 : CNF.NClause := [(45,false),(86,false),(70,true),(79,true),(14,true),(89,true)]
theorem der_34346 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34346 :=
  CNF.rup_sound cl_34346 [cl_29121,cl_32443] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29121 v h) (hints_cons _ _ _ (der_32443 v h) (by intro d hd; cases hd)))
def cl_34348 : CNF.NClause := [(45,false),(79,false),(70,true),(86,true),(14,true),(89,true)]
theorem der_34348 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34348 :=
  CNF.rup_sound cl_34348 [cl_29123,cl_32445] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29123 v h) (hints_cons _ _ _ (der_32445 v h) (by intro d hd; cases hd)))
def cl_34350 : CNF.NClause := [(45,false),(70,true),(86,true),(14,true),(63,true),(89,true)]
theorem der_34350 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34350 :=
  CNF.rup_sound cl_34350 [cl_29125,cl_34348] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29125 v h) (hints_cons _ _ _ (der_34348 v h) (by intro d hd; cases hd)))
def cl_34351 : CNF.NClause := [(47,false),(68,true),(77,false),(89,false),(66,false),(84,false)]
theorem der_34351 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34351 :=
  CNF.rup_sound cl_34351 [cl_29127,cl_32027] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29127 v h) (hints_cons _ _ _ (der_32027 v h) (by intro d hd; cases hd)))
def cl_34352 : CNF.NClause := [(47,false),(68,true),(89,false),(66,false),(75,false),(84,false)]
theorem der_34352 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34352 :=
  CNF.rup_sound cl_34352 [cl_29128,cl_26304] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29128 v h) (hints_cons _ _ _ (der_26304 v h) (by intro d hd; cases hd)))
def cl_34353 : CNF.NClause := [(47,false),(68,true),(16,false),(89,false),(66,false),(84,false)]
theorem der_34353 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34353 :=
  CNF.rup_sound cl_34353 [cl_29129,cl_34352] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29129 v h) (hints_cons _ _ _ (der_34352 v h) (by intro d hd; cases hd)))
def cl_34354 : CNF.NClause := [(47,false),(84,true),(77,false),(89,false),(66,false),(75,false)]
theorem der_34354 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34354 :=
  CNF.rup_sound cl_34354 [cl_29130,cl_34303] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29130 v h) (hints_cons _ _ _ (der_34303 v h) (by intro d hd; cases hd)))
def cl_34355 : CNF.NClause := [(47,false),(68,true),(77,false),(16,false),(89,false),(66,false)]
theorem der_34355 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34355 :=
  CNF.rup_sound cl_34355 [cl_29131,cl_34351] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29131 v h) (hints_cons _ _ _ (der_34351 v h) (by intro d hd; cases hd)))
def cl_34357 : CNF.NClause := [(47,false),(68,true),(77,true),(16,false),(89,false),(66,false)]
theorem der_34357 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34357 :=
  CNF.rup_sound cl_34357 [cl_29133,cl_34353] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29133 v h) (hints_cons _ _ _ (der_34353 v h) (by intro d hd; cases hd)))
def cl_34358 : CNF.NClause := [(47,false),(68,true),(77,false),(66,false),(75,false),(84,false)]
theorem der_34358 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34358 :=
  CNF.rup_sound cl_34358 [cl_29134,cl_32031] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29134 v h) (hints_cons _ _ _ (der_32031 v h) (by intro d hd; cases hd)))
def cl_34359 : CNF.NClause := [(47,false),(68,true),(77,false),(16,false),(66,false),(84,false)]
theorem der_34359 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34359 :=
  CNF.rup_sound cl_34359 [cl_29135,cl_34351] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29135 v h) (hints_cons _ _ _ (der_34351 v h) (by intro d hd; cases hd)))
def cl_34361 : CNF.NClause := [(47,false),(68,true),(77,true),(16,false),(66,false),(84,false)]
theorem der_34361 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34361 :=
  CNF.rup_sound cl_34361 [cl_29137,cl_34353] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29137 v h) (hints_cons _ _ _ (der_34353 v h) (by intro d hd; cases hd)))
def cl_34362 : CNF.NClause := [(47,false),(84,true),(77,false),(16,false),(66,false),(75,false)]
theorem der_34362 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34362 :=
  CNF.rup_sound cl_34362 [cl_29138,cl_34301] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29138 v h) (hints_cons _ _ _ (der_34301 v h) (by intro d hd; cases hd)))
def cl_34363 : CNF.NClause := [(47,false),(68,true),(84,true),(77,false),(16,false),(66,false)]
theorem der_34363 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34363 :=
  CNF.rup_sound cl_34363 [cl_29139,cl_34355] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29139 v h) (hints_cons _ _ _ (der_34355 v h) (by intro d hd; cases hd)))
def cl_34365 : CNF.NClause := [(47,false),(68,true),(77,true),(84,true),(16,false),(66,false)]
theorem der_34365 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34365 :=
  CNF.rup_sound cl_34365 [cl_29141,cl_34357] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29141 v h) (hints_cons _ _ _ (der_34357 v h) (by intro d hd; cases hd)))
def cl_34367 : CNF.NClause := [(47,false),(68,true),(16,true),(89,false),(75,false),(84,false)]
theorem der_34367 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34367 :=
  CNF.rup_sound cl_34367 [cl_29144,cl_34352] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29144 v h) (hints_cons _ _ _ (der_34352 v h) (by intro d hd; cases hd)))
def cl_34368 : CNF.NClause := [(47,false),(68,true),(16,true),(66,true),(89,false),(84,false)]
theorem der_34368 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34368 :=
  CNF.rup_sound cl_34368 [cl_29145,cl_34367] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29145 v h) (hints_cons _ _ _ (der_34367 v h) (by intro d hd; cases hd)))
def cl_34369 : CNF.NClause := [(47,false),(77,false),(68,true),(16,true),(89,false),(75,false)]
theorem der_34369 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34369 :=
  CNF.rup_sound cl_34369 [cl_29146,cl_32027] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29146 v h) (hints_cons _ _ _ (der_32027 v h) (by intro d hd; cases hd)))
def cl_34370 : CNF.NClause := [(47,false),(68,true),(16,true),(66,true),(77,false),(89,false)]
theorem der_34370 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34370 :=
  CNF.rup_sound cl_34370 [cl_29147,cl_34369] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29147 v h) (hints_cons _ _ _ (der_34369 v h) (by intro d hd; cases hd)))
def cl_34371 : CNF.NClause := [(47,false),(68,true),(16,true),(77,true),(89,false),(75,false)]
theorem der_34371 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34371 :=
  CNF.rup_sound cl_34371 [cl_29148,cl_34367] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29148 v h) (hints_cons _ _ _ (der_34367 v h) (by intro d hd; cases hd)))
def cl_34372 : CNF.NClause := [(47,false),(68,true),(16,true),(77,true),(84,true),(89,false)]
theorem der_34372 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34372 :=
  CNF.rup_sound cl_34372 [cl_29149,cl_34371] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29149 v h) (hints_cons _ _ _ (der_34371 v h) (by intro d hd; cases hd)))
def cl_34373 : CNF.NClause := [(47,false),(77,false),(68,true),(16,true),(75,false),(84,false)]
theorem der_34373 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34373 :=
  CNF.rup_sound cl_34373 [cl_29150,cl_34358] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29150 v h) (hints_cons _ _ _ (der_34358 v h) (by intro d hd; cases hd)))
def cl_34376 : CNF.NClause := [(47,false),(77,true),(68,true),(16,true),(66,true),(84,false)]
theorem der_34376 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34376 :=
  CNF.rup_sound cl_34376 [cl_29153,cl_34368] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29153 v h) (hints_cons _ _ _ (der_34368 v h) (by intro d hd; cases hd)))
def cl_34378 : CNF.NClause := [(47,false),(84,true),(68,true),(16,true),(66,true),(77,false)]
theorem der_34378 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34378 :=
  CNF.rup_sound cl_34378 [cl_29155,cl_34370] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29155 v h) (hints_cons _ _ _ (der_34370 v h) (by intro d hd; cases hd)))
def cl_34379 : CNF.NClause := [(47,false),(77,true),(68,true),(16,true),(66,true),(75,false)]
theorem der_34379 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34379 :=
  CNF.rup_sound cl_34379 [cl_29156,cl_34371] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29156 v h) (hints_cons _ _ _ (der_34371 v h) (by intro d hd; cases hd)))
def cl_34380 : CNF.NClause := [(47,false),(77,true),(68,true),(16,true),(66,true),(84,true)]
theorem der_34380 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34380 :=
  CNF.rup_sound cl_34380 [cl_29157,cl_34372] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29157 v h) (hints_cons _ _ _ (der_34372 v h) (by intro d hd; cases hd)))
def cl_34381 : CNF.NClause := [(47,false),(68,true),(77,false),(89,false),(75,false),(84,false)]
theorem der_34381 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34381 :=
  CNF.rup_sound cl_34381 [cl_29158,cl_29142] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29158 v h) (hints_cons _ _ _ (der_29142 v h) (by intro d hd; cases hd)))
def cl_34382 : CNF.NClause := [(47,false),(68,true),(75,true),(77,false),(89,false),(84,false)]
theorem der_34382 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34382 :=
  CNF.rup_sound cl_34382 [cl_29160,cl_34351] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29160 v h) (hints_cons _ _ _ (der_34351 v h) (by intro d hd; cases hd)))
def cl_34383 : CNF.NClause := [(47,false),(68,true),(77,true),(89,false),(75,false),(84,false)]
theorem der_34383 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34383 :=
  CNF.rup_sound cl_34383 [cl_29162,cl_34352] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29162 v h) (hints_cons _ _ _ (der_34352 v h) (by intro d hd; cases hd)))
def cl_34384 : CNF.NClause := [(47,false),(84,false),(66,true),(16,false),(89,false),(68,false)]
theorem der_34384 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34384 :=
  CNF.rup_sound cl_34384 [cl_29163,cl_29159] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29163 v h) (hints_cons _ _ _ (der_29159 v h) (by intro d hd; cases hd)))
def cl_34386 : CNF.NClause := [(47,false),(68,true),(84,true),(77,false),(89,false),(75,false)]
theorem der_34386 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34386 :=
  CNF.rup_sound cl_34386 [cl_29166,cl_34369] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29166 v h) (hints_cons _ _ _ (der_34369 v h) (by intro d hd; cases hd)))
def cl_34387 : CNF.NClause := [(47,false),(77,false),(66,true),(16,false),(89,false),(68,false)]
theorem der_34387 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34387 :=
  CNF.rup_sound cl_34387 [cl_29167,cl_29159] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29167 v h) (hints_cons _ _ _ (der_29159 v h) (by intro d hd; cases hd)))
def cl_34388 : CNF.NClause := [(47,false),(84,true),(16,false),(89,false),(75,false),(68,false)]
theorem der_34388 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34388 :=
  CNF.rup_sound cl_34388 [cl_29169,cl_29063] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29169 v h) (hints_cons _ _ _ (der_29063 v h) (by intro d hd; cases hd)))
def cl_34389 : CNF.NClause := [(47,false),(68,true),(77,true),(84,true),(89,false),(75,false)]
theorem der_34389 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34389 :=
  CNF.rup_sound cl_34389 [cl_29170,cl_34371] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29170 v h) (hints_cons _ _ _ (der_34371 v h) (by intro d hd; cases hd)))
def cl_34390 : CNF.NClause := [(47,false),(75,true),(66,true),(16,false),(89,false),(68,false)]
theorem der_34390 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34390 :=
  CNF.rup_sound cl_34390 [cl_29171,cl_34384] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29171 v h) (hints_cons _ _ _ (der_34384 v h) (by intro d hd; cases hd)))
def cl_34391 : CNF.NClause := [(47,false),(68,true),(75,true),(77,true),(16,false),(89,false)]
theorem der_34391 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34391 :=
  CNF.rup_sound cl_34391 [cl_29172,cl_34357] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29172 v h) (hints_cons _ _ _ (der_34357 v h) (by intro d hd; cases hd)))
def cl_34392 : CNF.NClause := [(47,false),(68,true),(77,false),(75,false),(84,false),(89,true)]
theorem der_34392 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34392 :=
  CNF.rup_sound cl_34392 [cl_29174,cl_34373] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29174 v h) (hints_cons _ _ _ (der_34373 v h) (by intro d hd; cases hd)))
def cl_34393 : CNF.NClause := [(47,false),(77,false),(66,true),(16,false),(84,false),(68,false)]
theorem der_34393 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34393 :=
  CNF.rup_sound cl_34393 [cl_29175,cl_34387] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29175 v h) (hints_cons _ _ _ (der_34387 v h) (by intro d hd; cases hd)))
def cl_34394 : CNF.NClause := [(47,false),(68,true),(75,true),(66,true),(77,false),(84,false)]
theorem der_34394 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34394 :=
  CNF.rup_sound cl_34394 [cl_29176,cl_34382] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29176 v h) (hints_cons _ _ _ (der_34382 v h) (by intro d hd; cases hd)))
def cl_34395 : CNF.NClause := [(47,false),(75,false),(16,false),(66,true),(84,false),(68,false)]
theorem der_34395 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34395 :=
  CNF.rup_sound cl_34395 [cl_29177,cl_34384] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29177 v h) (hints_cons _ _ _ (der_34384 v h) (by intro d hd; cases hd)))
def cl_34398 : CNF.NClause := [(47,false),(68,true),(75,true),(77,true),(66,true),(84,false)]
theorem der_34398 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34398 :=
  CNF.rup_sound cl_34398 [cl_29180,cl_34376] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29180 v h) (hints_cons _ _ _ (der_34376 v h) (by intro d hd; cases hd)))
def cl_34399 : CNF.NClause := [(47,false),(84,true),(77,false),(16,false),(75,false),(68,false)]
theorem der_34399 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34399 :=
  CNF.rup_sound cl_34399 [cl_29181,cl_34301] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29181 v h) (hints_cons _ _ _ (der_34301 v h) (by intro d hd; cases hd)))
def cl_34400 : CNF.NClause := [(47,false),(84,true),(77,false),(16,false),(75,false),(89,true)]
theorem der_34400 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34400 :=
  CNF.rup_sound cl_34400 [cl_29182,cl_34399] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29182 v h) (hints_cons _ _ _ (der_34399 v h) (by intro d hd; cases hd)))
def cl_34402 : CNF.NClause := [(47,false),(68,true),(75,true),(66,true),(77,false),(89,true)]
theorem der_34402 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34402 :=
  CNF.rup_sound cl_34402 [cl_29184,cl_34394] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29184 v h) (hints_cons _ _ _ (der_34394 v h) (by intro d hd; cases hd)))
def cl_34403 : CNF.NClause := [(47,false),(75,false),(84,true),(16,false),(68,false),(89,true)]
theorem der_34403 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34403 :=
  CNF.rup_sound cl_34403 [cl_29185,cl_34399] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29185 v h) (hints_cons _ _ _ (der_34399 v h) (by intro d hd; cases hd)))
def cl_34405 : CNF.NClause := [(47,false),(75,true),(77,true),(66,true),(16,false),(68,false)]
theorem der_34405 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34405 :=
  CNF.rup_sound cl_34405 [cl_29187,cl_34390] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29187 v h) (hints_cons _ _ _ (der_34390 v h) (by intro d hd; cases hd)))
def cl_34406 : CNF.NClause := [(47,false),(68,true),(75,true),(77,true),(66,true),(89,true)]
theorem der_34406 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34406 :=
  CNF.rup_sound cl_34406 [cl_29188,cl_34398] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29188 v h) (hints_cons _ _ _ (der_34398 v h) (by intro d hd; cases hd)))
def cl_34407 : CNF.NClause := [(52,false),(67,false),(88,false),(79,true),(73,false),(21,false)]
theorem der_34407 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34407 :=
  CNF.rup_sound cl_34407 [cl_29194,cl_29190] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29194 v h) (hints_cons _ _ _ (der_29190 v h) (by intro d hd; cases hd)))
def cl_34410 : CNF.NClause := [(52,false),(67,false),(85,false),(79,true),(73,false),(21,false)]
theorem der_34410 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34410 :=
  CNF.rup_sound cl_34410 [cl_29198,cl_29190] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29198 v h) (hints_cons _ _ _ (der_29190 v h) (by intro d hd; cases hd)))
def cl_34412 : CNF.NClause := [(52,false),(73,false),(79,false),(67,false),(85,true),(21,false)]
theorem der_34412 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34412 :=
  CNF.rup_sound cl_34412 [cl_29200,cl_29192] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29200 v h) (hints_cons _ _ _ (der_29192 v h) (by intro d hd; cases hd)))
def cl_34414 : CNF.NClause := [(52,false),(73,false),(67,false),(79,true),(85,true),(21,false)]
theorem der_34414 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34414 :=
  CNF.rup_sound cl_34414 [cl_29202,cl_34407] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29202 v h) (hints_cons _ _ _ (der_34407 v h) (by intro d hd; cases hd)))
def cl_34416 : CNF.NClause := [(47,false),(77,false),(66,true),(89,false),(75,false),(84,false)]
theorem der_34416 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34416 :=
  CNF.rup_sound cl_34416 [cl_29204,cl_34381] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29204 v h) (hints_cons _ _ _ (der_34381 v h) (by intro d hd; cases hd)))
def cl_34417 : CNF.NClause := [(47,false),(84,false),(66,true),(89,false),(75,false),(16,true)]
theorem der_34417 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34417 :=
  CNF.rup_sound cl_34417 [cl_29205,cl_34416] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29205 v h) (hints_cons _ _ _ (der_34416 v h) (by intro d hd; cases hd)))
def cl_34418 : CNF.NClause := [(47,false),(75,false),(84,true),(77,false),(89,false),(68,false)]
theorem der_34418 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34418 :=
  CNF.rup_sound cl_34418 [cl_29206,cl_34399] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29206 v h) (hints_cons _ _ _ (der_34399 v h) (by intro d hd; cases hd)))
def cl_34419 : CNF.NClause := [(47,false),(77,true),(84,true),(89,false),(75,false),(16,true)]
theorem der_34419 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34419 :=
  CNF.rup_sound cl_34419 [cl_29207,cl_34389] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29207 v h) (hints_cons _ _ _ (der_34389 v h) (by intro d hd; cases hd)))
def cl_34420 : CNF.NClause := [(47,false),(84,false),(77,false),(75,false),(66,true),(68,false)]
theorem der_34420 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34420 :=
  CNF.rup_sound cl_34420 [cl_29208,cl_34416] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29208 v h) (hints_cons _ _ _ (der_34416 v h) (by intro d hd; cases hd)))
def cl_34421 : CNF.NClause := [(47,false),(75,false),(77,true),(66,true),(16,true),(84,false)]
theorem der_34421 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34421 :=
  CNF.rup_sound cl_34421 [cl_29209,cl_34417] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29209 v h) (hints_cons _ _ _ (der_34417 v h) (by intro d hd; cases hd)))
def cl_34422 : CNF.NClause := [(47,false),(84,true),(66,true),(77,false),(75,false),(89,true)]
theorem der_34422 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34422 :=
  CNF.rup_sound cl_34422 [cl_29210,cl_34400] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29210 v h) (hints_cons _ _ _ (der_34400 v h) (by intro d hd; cases hd)))
def cl_34423 : CNF.NClause := [(47,false),(84,true),(16,true),(77,true),(75,false),(68,false)]
theorem der_34423 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34423 :=
  CNF.rup_sound cl_34423 [cl_29211,cl_34419] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29211 v h) (hints_cons _ _ _ (der_34419 v h) (by intro d hd; cases hd)))
def cl_34424 : CNF.NClause := [(52,false),(85,false),(66,true),(88,false),(67,false),(79,false)]
theorem der_34424 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34424 :=
  CNF.rup_sound cl_34424 [cl_29214,cl_29212] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29214 v h) (hints_cons _ _ _ (der_29212 v h) (by intro d hd; cases hd)))
def cl_34425 : CNF.NClause := [(52,false),(85,false),(21,true),(88,false),(79,false),(67,true)]
theorem der_34425 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34425 :=
  CNF.rup_sound cl_34425 [cl_29215,cl_29213] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29215 v h) (hints_cons _ _ _ (der_29213 v h) (by intro d hd; cases hd)))
def cl_34426 : CNF.NClause := [(52,false),(73,false),(79,true),(85,false),(88,false),(67,false)]
theorem der_34426 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34426 :=
  CNF.rup_sound cl_34426 [cl_29216,cl_29190] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29216 v h) (hints_cons _ _ _ (der_29190 v h) (by intro d hd; cases hd)))
def cl_34427 : CNF.NClause := [(52,false),(73,false),(85,false),(88,false),(21,true),(67,true)]
theorem der_34427 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34427 :=
  CNF.rup_sound cl_34427 [cl_29217,cl_26350] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29217 v h) (hints_cons _ _ _ (der_26350 v h) (by intro d hd; cases hd)))
def cl_34428 : CNF.NClause := [(52,false),(79,true),(66,true),(85,false),(88,false),(67,false)]
theorem der_34428 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34428 :=
  CNF.rup_sound cl_34428 [cl_29218,cl_34426] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29218 v h) (hints_cons _ _ _ (der_34426 v h) (by intro d hd; cases hd)))
def cl_34429 : CNF.NClause := [(52,false),(67,true),(73,true),(85,false),(21,true),(88,false)]
theorem der_34429 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34429 :=
  CNF.rup_sound cl_34429 [cl_29219,cl_32094] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29219 v h) (hints_cons _ _ _ (der_32094 v h) (by intro d hd; cases hd)))
def cl_34430 : CNF.NClause := [(52,false),(67,false),(88,false),(79,false),(73,false),(85,true)]
theorem der_34430 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34430 :=
  CNF.rup_sound cl_34430 [cl_29220,cl_29192] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29220 v h) (hints_cons _ _ _ (der_29192 v h) (by intro d hd; cases hd)))
def cl_34431 : CNF.NClause := [(52,false),(88,false),(21,true),(79,false),(73,false),(67,true)]
theorem der_34431 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34431 :=
  CNF.rup_sound cl_34431 [cl_29221,cl_32095] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29221 v h) (hints_cons _ _ _ (der_32095 v h) (by intro d hd; cases hd)))
def cl_34432 : CNF.NClause := [(52,false),(66,true),(88,false),(67,false),(79,false),(85,true)]
theorem der_34432 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34432 :=
  CNF.rup_sound cl_34432 [cl_29222,cl_34430] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29222 v h) (hints_cons _ _ _ (der_34430 v h) (by intro d hd; cases hd)))
def cl_34433 : CNF.NClause := [(52,false),(88,false),(73,true),(21,true),(79,false),(67,true)]
theorem der_34433 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34433 :=
  CNF.rup_sound cl_34433 [cl_29223,cl_34425] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29223 v h) (hints_cons _ _ _ (der_34425 v h) (by intro d hd; cases hd)))
def cl_34434 : CNF.NClause := [(52,false),(88,false),(66,true),(79,true),(67,false),(73,false)]
theorem der_34434 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34434 :=
  CNF.rup_sound cl_34434 [cl_29224,cl_34426] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29224 v h) (hints_cons _ _ _ (der_34426 v h) (by intro d hd; cases hd)))
def cl_34435 : CNF.NClause := [(52,false),(73,false),(79,true),(66,true),(88,false),(21,true)]
theorem der_34435 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34435 :=
  CNF.rup_sound cl_34435 [cl_29225,cl_34434] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29225 v h) (hints_cons _ _ _ (der_34434 v h) (by intro d hd; cases hd)))
def cl_34436 : CNF.NClause := [(52,false),(79,true),(66,true),(88,false),(67,false),(85,true)]
theorem der_34436 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34436 :=
  CNF.rup_sound cl_34436 [cl_29226,cl_34434] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29226 v h) (hints_cons _ _ _ (der_34434 v h) (by intro d hd; cases hd)))
def cl_34438 : CNF.NClause := [(52,false),(67,false),(85,false),(66,true),(79,false),(73,false)]
theorem der_34438 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34438 :=
  CNF.rup_sound cl_34438 [cl_29228,cl_29212] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29228 v h) (hints_cons _ _ _ (der_29212 v h) (by intro d hd; cases hd)))
def cl_34439 : CNF.NClause := [(52,false),(66,true),(85,false),(67,false),(79,false),(88,true)]
theorem der_34439 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34439 :=
  CNF.rup_sound cl_34439 [cl_29230,cl_34438] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29230 v h) (hints_cons _ _ _ (der_34438 v h) (by intro d hd; cases hd)))
def cl_34440 : CNF.NClause := [(52,false),(21,true),(66,true),(85,false),(79,false),(88,true)]
theorem der_34440 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34440 :=
  CNF.rup_sound cl_34440 [cl_29231,cl_29229] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29231 v h) (hints_cons _ _ _ (der_29229 v h) (by intro d hd; cases hd)))
def cl_34441 : CNF.NClause := [(52,false),(73,false),(79,true),(85,false),(21,true),(67,true)]
theorem der_34441 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34441 :=
  CNF.rup_sound cl_34441 [cl_29233,cl_32099] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29233 v h) (hints_cons _ _ _ (der_32099 v h) (by intro d hd; cases hd)))
def cl_34442 : CNF.NClause := [(52,false),(73,true),(79,true),(66,true),(85,false),(67,false)]
theorem der_34442 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34442 :=
  CNF.rup_sound cl_34442 [cl_29234,cl_34428] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29234 v h) (hints_cons _ _ _ (der_34428 v h) (by intro d hd; cases hd)))
def cl_34443 : CNF.NClause := [(52,false),(85,false),(73,true),(66,true),(21,true),(88,true)]
theorem der_34443 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34443 :=
  CNF.rup_sound cl_34443 [cl_29235,cl_34440] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29235 v h) (hints_cons _ _ _ (der_34440 v h) (by intro d hd; cases hd)))
def cl_34444 : CNF.NClause := [(52,false),(73,false),(21,true),(79,false),(85,true),(67,true)]
theorem der_34444 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34444 :=
  CNF.rup_sound cl_34444 [cl_29237,cl_32103] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29237 v h) (hints_cons _ _ _ (der_32103 v h) (by intro d hd; cases hd)))
def cl_34445 : CNF.NClause := [(52,false),(73,true),(66,true),(67,false),(79,false),(85,true)]
theorem der_34445 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34445 :=
  CNF.rup_sound cl_34445 [cl_29238,cl_34432] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29238 v h) (hints_cons _ _ _ (der_34432 v h) (by intro d hd; cases hd)))
def cl_34446 : CNF.NClause := [(52,false),(73,true),(21,true),(66,true),(79,false),(88,true)]
theorem der_34446 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34446 :=
  CNF.rup_sound cl_34446 [cl_29239,cl_34440] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29239 v h) (hints_cons _ _ _ (der_34440 v h) (by intro d hd; cases hd)))
def cl_34447 : CNF.NClause := [(52,false),(73,false),(79,true),(67,false),(85,true),(88,true)]
theorem der_34447 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34447 :=
  CNF.rup_sound cl_34447 [cl_29240,cl_34414] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29240 v h) (hints_cons _ _ _ (der_34414 v h) (by intro d hd; cases hd)))
def cl_34448 : CNF.NClause := [(52,false),(85,true),(79,true),(66,true),(73,false),(21,true)]
theorem der_34448 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34448 :=
  CNF.rup_sound cl_34448 [cl_29241,cl_34435] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29241 v h) (hints_cons _ _ _ (der_34435 v h) (by intro d hd; cases hd)))
def cl_34449 : CNF.NClause := [(52,false),(79,true),(66,true),(67,false),(73,true),(88,true)]
theorem der_34449 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34449 :=
  CNF.rup_sound cl_34449 [cl_29242,cl_34442] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29242 v h) (hints_cons _ _ _ (der_34442 v h) (by intro d hd; cases hd)))
def cl_34450 : CNF.NClause := [(52,false),(85,true),(79,true),(66,true),(21,true),(67,true)]
theorem der_34450 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34450 :=
  CNF.rup_sound cl_34450 [cl_29243,cl_34448] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29243 v h) (hints_cons _ _ _ (der_34448 v h) (by intro d hd; cases hd)))
def cl_34451 : CNF.NClause := [(44,false),(78,false),(65,true),(13,true),(88,false),(84,false)]
theorem der_34451 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34451 :=
  CNF.rup_sound cl_34451 [cl_29247,cl_29246] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29247 v h) (hints_cons _ _ _ (der_29246 v h) (by intro d hd; cases hd)))
def cl_34452 : CNF.NClause := [(44,false),(13,true),(72,false),(88,false),(71,false),(84,false)]
theorem der_34452 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34452 :=
  CNF.rup_sound cl_34452 [cl_29248,cl_29244] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29248 v h) (hints_cons _ _ _ (der_29244 v h) (by intro d hd; cases hd)))
def cl_34453 : CNF.NClause := [(44,false),(88,false),(65,true),(13,true),(72,false),(84,false)]
theorem der_34453 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34453 :=
  CNF.rup_sound cl_34453 [cl_29249,cl_34452] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29249 v h) (hints_cons _ _ _ (der_34452 v h) (by intro d hd; cases hd)))
def cl_34454 : CNF.NClause := [(44,false),(88,false),(65,true),(13,true),(71,false),(84,false)]
theorem der_34454 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34454 :=
  CNF.rup_sound cl_34454 [cl_29250,cl_34452] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29250 v h) (hints_cons _ _ _ (der_34452 v h) (by intro d hd; cases hd)))
def cl_34455 : CNF.NClause := [(44,false),(84,false),(71,true),(65,true),(13,true),(88,false)]
theorem der_34455 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34455 :=
  CNF.rup_sound cl_34455 [cl_29251,cl_34451] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29251 v h) (hints_cons _ _ _ (der_34451 v h) (by intro d hd; cases hd)))
def cl_34456 : CNF.NClause := [(44,false),(71,false),(72,false),(88,false),(78,false),(13,true)]
theorem der_34456 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34456 :=
  CNF.rup_sound cl_34456 [cl_29252,cl_29244] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29252 v h) (hints_cons _ _ _ (der_29244 v h) (by intro d hd; cases hd)))
def cl_34457 : CNF.NClause := [(44,false),(78,false),(65,true),(72,false),(88,false),(13,true)]
theorem der_34457 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34457 :=
  CNF.rup_sound cl_34457 [cl_29253,cl_34456] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29253 v h) (hints_cons _ _ _ (der_34456 v h) (by intro d hd; cases hd)))
def cl_34458 : CNF.NClause := [(44,false),(88,false),(65,true),(13,true),(78,false),(71,false)]
theorem der_34458 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34458 :=
  CNF.rup_sound cl_34458 [cl_29254,cl_34457] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29254 v h) (hints_cons _ _ _ (der_34457 v h) (by intro d hd; cases hd)))
def cl_34459 : CNF.NClause := [(44,false),(78,false),(71,true),(65,true),(88,false),(13,true)]
theorem der_34459 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34459 :=
  CNF.rup_sound cl_34459 [cl_29255,cl_34451] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29255 v h) (hints_cons _ _ _ (der_34451 v h) (by intro d hd; cases hd)))
def cl_34460 : CNF.NClause := [(44,false),(71,false),(65,true),(72,false),(88,false),(13,true)]
theorem der_34460 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34460 :=
  CNF.rup_sound cl_34460 [cl_29256,cl_34457] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29256 v h) (hints_cons _ _ _ (der_34457 v h) (by intro d hd; cases hd)))
def cl_34461 : CNF.NClause := [(44,false),(71,true),(88,false),(65,true),(72,false),(13,true)]
theorem der_34461 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34461 :=
  CNF.rup_sound cl_34461 [cl_29257,cl_34457] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29257 v h) (hints_cons _ _ _ (der_34457 v h) (by intro d hd; cases hd)))
def cl_34463 : CNF.NClause := [(44,false),(88,false),(71,true),(65,true),(13,true),(72,true)]
theorem der_34463 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34463 :=
  CNF.rup_sound cl_34463 [cl_29259,cl_34459] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29259 v h) (hints_cons _ _ _ (der_34459 v h) (by intro d hd; cases hd)))
def cl_34464 : CNF.NClause := [(44,false),(78,false),(65,true),(13,true),(72,false),(84,false)]
theorem der_34464 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34464 :=
  CNF.rup_sound cl_34464 [cl_29261,cl_29260] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29261 v h) (hints_cons _ _ _ (der_29260 v h) (by intro d hd; cases hd)))
def cl_34465 : CNF.NClause := [(44,false),(78,false),(65,true),(13,true),(71,false),(84,false)]
theorem der_34465 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34465 :=
  CNF.rup_sound cl_34465 [cl_29262,cl_34464] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29262 v h) (hints_cons _ _ _ (der_34464 v h) (by intro d hd; cases hd)))
def cl_34466 : CNF.NClause := [(44,false),(65,true),(71,true),(13,true),(78,false),(84,false)]
theorem der_34466 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34466 :=
  CNF.rup_sound cl_34466 [cl_29263,cl_34459] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29263 v h) (hints_cons _ _ _ (der_34459 v h) (by intro d hd; cases hd)))
def cl_34467 : CNF.NClause := [(44,false),(78,true),(13,true),(72,false),(71,false),(84,false)]
theorem der_34467 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34467 :=
  CNF.rup_sound cl_34467 [cl_29264,cl_34316] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29264 v h) (hints_cons _ _ _ (der_34316 v h) (by intro d hd; cases hd)))
def cl_34468 : CNF.NClause := [(44,false),(71,true),(13,true),(65,true),(72,false),(84,false)]
theorem der_34468 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34468 :=
  CNF.rup_sound cl_34468 [cl_29265,cl_34464] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29265 v h) (hints_cons _ _ _ (der_34464 v h) (by intro d hd; cases hd)))
def cl_34469 : CNF.NClause := [(44,false),(13,true),(65,true),(72,true),(71,false),(84,false)]
theorem der_34469 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34469 :=
  CNF.rup_sound cl_34469 [cl_29266,cl_34465] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29266 v h) (hints_cons _ _ _ (der_34465 v h) (by intro d hd; cases hd)))
def cl_34470 : CNF.NClause := [(44,false),(84,false),(71,true),(65,true),(13,true),(72,true)]
theorem der_34470 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34470 :=
  CNF.rup_sound cl_34470 [cl_29267,cl_34466] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29267 v h) (hints_cons _ _ _ (der_34466 v h) (by intro d hd; cases hd)))
def cl_34471 : CNF.NClause := [(44,false),(84,true),(13,true),(72,false),(78,false),(71,false)]
theorem der_34471 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34471 :=
  CNF.rup_sound cl_34471 [cl_29268,cl_34300] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29268 v h) (hints_cons _ _ _ (der_34300 v h) (by intro d hd; cases hd)))
def cl_34473 : CNF.NClause := [(44,false),(65,true),(13,true),(72,true),(78,false),(71,false)]
theorem der_34473 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34473 :=
  CNF.rup_sound cl_34473 [cl_29270,cl_34465] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29270 v h) (hints_cons _ _ _ (der_34465 v h) (by intro d hd; cases hd)))
def cl_34474 : CNF.NClause := [(44,false),(78,false),(71,true),(65,true),(72,true),(13,true)]
theorem der_34474 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34474 :=
  CNF.rup_sound cl_34474 [cl_29271,cl_34466] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29271 v h) (hints_cons _ _ _ (der_34466 v h) (by intro d hd; cases hd)))
def cl_34475 : CNF.NClause := [(44,false),(71,false),(78,true),(84,true),(72,false),(13,true)]
theorem der_34475 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34475 :=
  CNF.rup_sound cl_34475 [cl_29272,cl_32381] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29272 v h) (hints_cons _ _ _ (der_32381 v h) (by intro d hd; cases hd)))
def cl_34477 : CNF.NClause := [(44,false),(71,true),(78,true),(65,true),(13,true),(72,true)]
theorem der_34477 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34477 :=
  CNF.rup_sound cl_34477 [cl_29275,cl_34470] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29275 v h) (hints_cons _ _ _ (der_34470 v h) (by intro d hd; cases hd)))
def cl_34480 : CNF.NClause := [(49,false),(65,true),(91,false),(86,false),(69,false),(18,false)]
theorem der_34480 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34480 :=
  CNF.rup_sound cl_34480 [cl_29281,cl_29279] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29281 v h) (hints_cons _ _ _ (der_29279 v h) (by intro d hd; cases hd)))
def cl_34483 : CNF.NClause := [(49,false),(91,false),(86,true),(69,false),(73,false),(18,false)]
theorem der_34483 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34483 :=
  CNF.rup_sound cl_34483 [cl_29287,cl_29283] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29287 v h) (hints_cons _ _ _ (der_29283 v h) (by intro d hd; cases hd)))
def cl_34484 : CNF.NClause := [(49,false),(69,true),(65,true),(91,false),(73,false),(18,false)]
theorem der_34484 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34484 :=
  CNF.rup_sound cl_34484 [cl_29288,cl_29284] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29288 v h) (hints_cons _ _ _ (der_29284 v h) (by intro d hd; cases hd)))
def cl_34485 : CNF.NClause := [(49,false),(65,true),(18,false),(91,false),(69,false),(73,true)]
theorem der_34485 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34485 :=
  CNF.rup_sound cl_34485 [cl_29289,cl_29285] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29289 v h) (hints_cons _ _ _ (der_29285 v h) (by intro d hd; cases hd)))
def cl_34488 : CNF.NClause := [(49,false),(86,false),(77,true),(69,false),(73,false),(18,false)]
theorem der_34488 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34488 :=
  CNF.rup_sound cl_34488 [cl_29295,cl_26728] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29295 v h) (hints_cons _ _ _ (der_26728 v h) (by intro d hd; cases hd)))
def cl_34490 : CNF.NClause := [(49,false),(73,true),(65,true),(86,false),(69,false),(18,false)]
theorem der_34490 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34490 :=
  CNF.rup_sound cl_34490 [cl_29297,cl_29293] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29297 v h) (hints_cons _ _ _ (der_29293 v h) (by intro d hd; cases hd)))
def cl_34492 : CNF.NClause := [(49,false),(77,false),(86,true),(69,false),(73,false),(18,false)]
theorem der_34492 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34492 :=
  CNF.rup_sound cl_34492 [cl_29299,cl_29283] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29299 v h) (hints_cons _ _ _ (der_29283 v h) (by intro d hd; cases hd)))
def cl_34493 : CNF.NClause := [(49,false),(86,true),(65,true),(77,false),(73,false),(18,false)]
theorem der_34493 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34493 :=
  CNF.rup_sound cl_34493 [cl_29300,cl_34492] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29300 v h) (hints_cons _ _ _ (der_34492 v h) (by intro d hd; cases hd)))
def cl_34494 : CNF.NClause := [(49,false),(73,true),(65,true),(77,false),(69,false),(18,false)]
theorem der_34494 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34494 :=
  CNF.rup_sound cl_34494 [cl_29301,cl_29293] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29301 v h) (hints_cons _ _ _ (der_29293 v h) (by intro d hd; cases hd)))
def cl_34495 : CNF.NClause := [(49,false),(73,true),(86,true),(65,true),(77,false),(18,false)]
theorem der_34495 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34495 :=
  CNF.rup_sound cl_34495 [cl_29302,cl_34494] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29302 v h) (hints_cons _ _ _ (der_34494 v h) (by intro d hd; cases hd)))
def cl_34496 : CNF.NClause := [(49,false),(77,true),(86,true),(69,false),(73,false),(18,false)]
theorem der_34496 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34496 :=
  CNF.rup_sound cl_34496 [cl_29303,cl_34483] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29303 v h) (hints_cons _ _ _ (der_34483 v h) (by intro d hd; cases hd)))
def cl_34497 : CNF.NClause := [(49,false),(86,true),(65,true),(77,true),(73,false),(18,false)]
theorem der_34497 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34497 :=
  CNF.rup_sound cl_34497 [cl_29304,cl_34496] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29304 v h) (hints_cons _ _ _ (der_34496 v h) (by intro d hd; cases hd)))
def cl_34499 : CNF.NClause := [(44,false),(65,true),(72,false),(88,false),(78,false),(84,false)]
theorem der_34499 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34499 :=
  CNF.rup_sound cl_34499 [cl_29308,cl_29307] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29308 v h) (hints_cons _ _ _ (der_29307 v h) (by intro d hd; cases hd)))
def cl_34500 : CNF.NClause := [(44,false),(78,false),(88,false),(65,true),(71,false),(84,false)]
theorem der_34500 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34500 :=
  CNF.rup_sound cl_34500 [cl_29309,cl_34499] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29309 v h) (hints_cons _ _ _ (der_34499 v h) (by intro d hd; cases hd)))
def cl_34501 : CNF.NClause := [(44,false),(71,true),(65,true),(88,false),(78,false),(84,false)]
theorem der_34501 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34501 :=
  CNF.rup_sound cl_34501 [cl_29310,cl_34499] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29310 v h) (hints_cons _ _ _ (der_34499 v h) (by intro d hd; cases hd)))
def cl_34502 : CNF.NClause := [(44,false),(78,true),(72,false),(88,false),(71,false),(84,false)]
theorem der_34502 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34502 :=
  CNF.rup_sound cl_34502 [cl_29311,cl_34452] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29311 v h) (hints_cons _ _ _ (der_34452 v h) (by intro d hd; cases hd)))
def cl_34503 : CNF.NClause := [(44,false),(71,true),(65,true),(72,false),(88,false),(84,false)]
theorem der_34503 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34503 :=
  CNF.rup_sound cl_34503 [cl_29312,cl_34499] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29312 v h) (hints_cons _ _ _ (der_34499 v h) (by intro d hd; cases hd)))
def cl_34504 : CNF.NClause := [(44,false),(65,true),(72,true),(88,false),(71,false),(84,false)]
theorem der_34504 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34504 :=
  CNF.rup_sound cl_34504 [cl_29313,cl_34500] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29313 v h) (hints_cons _ _ _ (der_34500 v h) (by intro d hd; cases hd)))
def cl_34506 : CNF.NClause := [(44,false),(84,true),(72,false),(88,false),(78,false),(71,false)]
theorem der_34506 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34506 :=
  CNF.rup_sound cl_34506 [cl_29315,cl_34456] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29315 v h) (hints_cons _ _ _ (der_34456 v h) (by intro d hd; cases hd)))
def cl_34507 : CNF.NClause := [(44,false),(78,false),(65,true),(72,false),(88,false),(71,true)]
theorem der_34507 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34507 :=
  CNF.rup_sound cl_34507 [cl_29316,cl_34499] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29316 v h) (hints_cons _ _ _ (der_34499 v h) (by intro d hd; cases hd)))
def cl_34508 : CNF.NClause := [(44,false),(65,true),(72,true),(88,false),(78,false),(71,false)]
theorem der_34508 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34508 :=
  CNF.rup_sound cl_34508 [cl_29317,cl_34504] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29317 v h) (hints_cons _ _ _ (der_34504 v h) (by intro d hd; cases hd)))
def cl_34510 : CNF.NClause := [(44,false),(78,true),(65,true),(72,false),(88,false),(71,false)]
theorem der_34510 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34510 :=
  CNF.rup_sound cl_34510 [cl_29319,cl_34502] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29319 v h) (hints_cons _ _ _ (der_34502 v h) (by intro d hd; cases hd)))
def cl_34511 : CNF.NClause := [(44,false),(71,true),(65,true),(84,true),(72,false),(88,false)]
theorem der_34511 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34511 :=
  CNF.rup_sound cl_34511 [cl_29320,cl_34507] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29320 v h) (hints_cons _ _ _ (der_34507 v h) (by intro d hd; cases hd)))
def cl_34512 : CNF.NClause := [(44,false),(78,true),(65,true),(72,true),(88,false),(71,false)]
theorem der_34512 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34512 :=
  CNF.rup_sound cl_34512 [cl_29321,cl_34504] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29321 v h) (hints_cons _ _ _ (der_34504 v h) (by intro d hd; cases hd)))
def cl_34513 : CNF.NClause := [(44,false),(84,true),(78,true),(65,true),(71,true),(88,false)]
theorem der_34513 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34513 :=
  CNF.rup_sound cl_34513 [cl_29322,cl_34511] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29322 v h) (hints_cons _ _ _ (der_34511 v h) (by intro d hd; cases hd)))
def cl_34514 : CNF.NClause := [(44,false),(65,true),(72,false),(78,false),(71,false),(84,false)]
theorem der_34514 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34514 :=
  CNF.rup_sound cl_34514 [cl_29323,cl_34464] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29323 v h) (hints_cons _ _ _ (der_34464 v h) (by intro d hd; cases hd)))
def cl_34515 : CNF.NClause := [(44,false),(71,true),(65,true),(72,false),(78,false),(84,false)]
theorem der_34515 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34515 :=
  CNF.rup_sound cl_34515 [cl_29324,cl_34499] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29324 v h) (hints_cons _ _ _ (der_34499 v h) (by intro d hd; cases hd)))
def cl_34518 : CNF.NClause := [(44,false),(78,true),(72,false),(71,false),(84,false),(88,true)]
theorem der_34518 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34518 :=
  CNF.rup_sound cl_34518 [cl_29327,cl_34316] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29327 v h) (hints_cons _ _ _ (der_34316 v h) (by intro d hd; cases hd)))
def cl_34519 : CNF.NClause := [(44,false),(78,true),(71,true),(65,true),(72,false),(84,false)]
theorem der_34519 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34519 :=
  CNF.rup_sound cl_34519 [cl_29328,cl_34503] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29328 v h) (hints_cons _ _ _ (der_34503 v h) (by intro d hd; cases hd)))
def cl_34520 : CNF.NClause := [(44,false),(78,true),(65,true),(72,true),(71,false),(84,false)]
theorem der_34520 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34520 :=
  CNF.rup_sound cl_34520 [cl_29329,cl_34504] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29329 v h) (hints_cons _ _ _ (der_34504 v h) (by intro d hd; cases hd)))
def cl_34522 : CNF.NClause := [(44,false),(84,true),(72,false),(78,false),(71,false),(88,true)]
theorem der_34522 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34522 :=
  CNF.rup_sound cl_34522 [cl_29331,cl_34300] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29331 v h) (hints_cons _ _ _ (der_34300 v h) (by intro d hd; cases hd)))
def cl_34524 : CNF.NClause := [(44,false),(65,true),(72,true),(84,true),(78,false),(71,false)]
theorem der_34524 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34524 :=
  CNF.rup_sound cl_34524 [cl_29333,cl_34473] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29333 v h) (hints_cons _ _ _ (der_34473 v h) (by intro d hd; cases hd)))
def cl_34526 : CNF.NClause := [(44,false),(78,true),(65,true),(84,true),(72,false),(71,false)]
theorem der_34526 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34526 :=
  CNF.rup_sound cl_34526 [cl_29335,cl_34510] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29335 v h) (hints_cons _ _ _ (der_34510 v h) (by intro d hd; cases hd)))
def cl_34529 : CNF.NClause := [(44,false),(84,true),(78,true),(65,true),(72,true),(71,true)]
theorem der_34529 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34529 :=
  CNF.rup_sound cl_34529 [cl_29338,cl_34513] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29338 v h) (hints_cons _ _ _ (der_34513 v h) (by intro d hd; cases hd)))
def cl_34530 : CNF.NClause := [(49,false),(65,true),(77,false),(91,false),(86,false),(73,false)]
theorem der_34530 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34530 :=
  CNF.rup_sound cl_34530 [cl_29340,cl_29339] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29340 v h) (hints_cons _ _ _ (der_29339 v h) (by intro d hd; cases hd)))
def cl_34531 : CNF.NClause := [(49,false),(65,true),(77,false),(91,false),(86,false),(69,false)]
theorem der_34531 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34531 :=
  CNF.rup_sound cl_34531 [cl_29341,cl_29339] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29341 v h) (hints_cons _ _ _ (der_29339 v h) (by intro d hd; cases hd)))
def cl_34532 : CNF.NClause := [(49,false),(73,true),(65,true),(77,false),(91,false),(86,false)]
theorem der_34532 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34532 :=
  CNF.rup_sound cl_34532 [cl_29342,cl_34531] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29342 v h) (hints_cons _ _ _ (der_34531 v h) (by intro d hd; cases hd)))
def cl_34533 : CNF.NClause := [(49,false),(86,false),(77,true),(91,false),(69,false),(73,false)]
theorem der_34533 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34533 :=
  CNF.rup_sound cl_34533 [cl_29343,cl_34488] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29343 v h) (hints_cons _ _ _ (der_34488 v h) (by intro d hd; cases hd)))
def cl_34534 : CNF.NClause := [(49,false),(69,true),(65,true),(91,false),(86,false),(73,false)]
theorem der_34534 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34534 :=
  CNF.rup_sound cl_34534 [cl_29344,cl_34530] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29344 v h) (hints_cons _ _ _ (der_34530 v h) (by intro d hd; cases hd)))
def cl_34536 : CNF.NClause := [(49,false),(69,true),(65,true),(77,true),(91,false),(86,false)]
theorem der_34536 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34536 :=
  CNF.rup_sound cl_34536 [cl_29346,cl_34534] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29346 v h) (hints_cons _ _ _ (der_34534 v h) (by intro d hd; cases hd)))
def cl_34537 : CNF.NClause := [(49,false),(91,false),(65,true),(77,false),(69,false),(73,false)]
theorem der_34537 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34537 :=
  CNF.rup_sound cl_34537 [cl_29347,cl_34531] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29347 v h) (hints_cons _ _ _ (der_34531 v h) (by intro d hd; cases hd)))
def cl_34538 : CNF.NClause := [(49,false),(69,true),(65,true),(77,false),(91,false),(73,false)]
theorem der_34538 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34538 :=
  CNF.rup_sound cl_34538 [cl_29348,cl_34534] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29348 v h) (hints_cons _ _ _ (der_34534 v h) (by intro d hd; cases hd)))
def cl_34539 : CNF.NClause := [(49,false),(69,false),(65,true),(77,false),(91,false),(73,true)]
theorem der_34539 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34539 :=
  CNF.rup_sound cl_34539 [cl_29349,cl_34531] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29349 v h) (hints_cons _ _ _ (der_34531 v h) (by intro d hd; cases hd)))
def cl_34541 : CNF.NClause := [(49,false),(73,false),(86,true),(77,true),(91,false),(69,false)]
theorem der_34541 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34541 :=
  CNF.rup_sound cl_34541 [cl_29351,cl_34483] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29351 v h) (hints_cons _ _ _ (der_34483 v h) (by intro d hd; cases hd)))
def cl_34542 : CNF.NClause := [(49,false),(69,true),(65,true),(77,true),(91,false),(73,false)]
theorem der_34542 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34542 :=
  CNF.rup_sound cl_34542 [cl_29352,cl_34534] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29352 v h) (hints_cons _ _ _ (der_34534 v h) (by intro d hd; cases hd)))
def cl_34543 : CNF.NClause := [(49,false),(69,false),(73,true),(65,true),(77,true),(91,false)]
theorem der_34543 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34543 :=
  CNF.rup_sound cl_34543 [cl_29353,cl_34485] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29353 v h) (hints_cons _ _ _ (der_34485 v h) (by intro d hd; cases hd)))
def cl_34544 : CNF.NClause := [(49,false),(73,true),(86,true),(65,true),(77,true),(91,false)]
theorem der_34544 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34544 :=
  CNF.rup_sound cl_34544 [cl_29354,cl_34543] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29354 v h) (hints_cons _ _ _ (der_34543 v h) (by intro d hd; cases hd)))
def cl_34545 : CNF.NClause := [(49,false),(86,false),(77,false),(69,false),(73,false),(91,true)]
theorem der_34545 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34545 :=
  CNF.rup_sound cl_34545 [cl_29355,cl_29291] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29355 v h) (hints_cons _ _ _ (der_29291 v h) (by intro d hd; cases hd)))
def cl_34546 : CNF.NClause := [(49,false),(69,true),(65,true),(77,false),(86,false),(73,false)]
theorem der_34546 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34546 :=
  CNF.rup_sound cl_34546 [cl_29356,cl_34534] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29356 v h) (hints_cons _ _ _ (der_34534 v h) (by intro d hd; cases hd)))
def cl_34547 : CNF.NClause := [(49,false),(73,true),(65,true),(77,false),(86,false),(69,false)]
theorem der_34547 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34547 :=
  CNF.rup_sound cl_34547 [cl_29357,cl_34531] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29357 v h) (hints_cons _ _ _ (der_34531 v h) (by intro d hd; cases hd)))
def cl_34548 : CNF.NClause := [(49,false),(69,true),(65,true),(77,false),(86,false),(91,true)]
theorem der_34548 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34548 :=
  CNF.rup_sound cl_34548 [cl_29358,cl_34546] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29358 v h) (hints_cons _ _ _ (der_34546 v h) (by intro d hd; cases hd)))
def cl_34549 : CNF.NClause := [(49,false),(69,false),(77,true),(86,false),(73,false),(91,true)]
theorem der_34549 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34549 :=
  CNF.rup_sound cl_34549 [cl_29359,cl_34488] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29359 v h) (hints_cons _ _ _ (der_34488 v h) (by intro d hd; cases hd)))
def cl_34550 : CNF.NClause := [(49,false),(69,true),(65,true),(77,true),(86,false),(73,false)]
theorem der_34550 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34550 :=
  CNF.rup_sound cl_34550 [cl_29360,cl_34534] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29360 v h) (hints_cons _ _ _ (der_34534 v h) (by intro d hd; cases hd)))
def cl_34551 : CNF.NClause := [(49,false),(86,false),(73,true),(65,true),(77,true),(69,false)]
theorem der_34551 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34551 :=
  CNF.rup_sound cl_34551 [cl_29361,cl_34490] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29361 v h) (hints_cons _ _ _ (der_34490 v h) (by intro d hd; cases hd)))
def cl_34552 : CNF.NClause := [(49,false),(69,true),(65,true),(77,true),(86,false),(91,true)]
theorem der_34552 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34552 :=
  CNF.rup_sound cl_34552 [cl_29362,cl_34550] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29362 v h) (hints_cons _ _ _ (der_34550 v h) (by intro d hd; cases hd)))
def cl_34553 : CNF.NClause := [(49,false),(77,false),(86,true),(69,false),(73,false),(91,true)]
theorem der_34553 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34553 :=
  CNF.rup_sound cl_34553 [cl_29363,cl_34298] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29363 v h) (hints_cons _ _ _ (der_34298 v h) (by intro d hd; cases hd)))
def cl_34554 : CNF.NClause := [(49,false),(69,true),(65,true),(77,false),(73,false),(91,true)]
theorem der_34554 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34554 :=
  CNF.rup_sound cl_34554 [cl_29364,cl_34546] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29364 v h) (hints_cons _ _ _ (der_34546 v h) (by intro d hd; cases hd)))
def cl_34555 : CNF.NClause := [(49,false),(73,true),(86,true),(65,true),(77,false),(69,false)]
theorem der_34555 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34555 :=
  CNF.rup_sound cl_34555 [cl_29365,cl_34539] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29365 v h) (hints_cons _ _ _ (der_34539 v h) (by intro d hd; cases hd)))
def cl_34556 : CNF.NClause := [(49,false),(73,true),(18,true),(86,true),(65,true),(77,false)]
theorem der_34556 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34556 :=
  CNF.rup_sound cl_34556 [cl_29366,cl_34555] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29366 v h) (hints_cons _ _ _ (der_34555 v h) (by intro d hd; cases hd)))
def cl_34557 : CNF.NClause := [(49,false),(91,true),(65,true),(77,true),(69,false),(73,false)]
theorem der_34557 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34557 :=
  CNF.rup_sound cl_34557 [cl_29367,cl_34549] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29367 v h) (hints_cons _ _ _ (der_34549 v h) (by intro d hd; cases hd)))
def cl_34558 : CNF.NClause := [(49,false),(65,true),(69,true),(18,true),(73,false),(91,true)]
theorem der_34558 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34558 :=
  CNF.rup_sound cl_34558 [cl_29368,cl_34554] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29368 v h) (hints_cons _ _ _ (der_34554 v h) (by intro d hd; cases hd)))
def cl_34559 : CNF.NClause := [(49,false),(69,false),(73,true),(86,true),(65,true),(18,true)]
theorem der_34559 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34559 :=
  CNF.rup_sound cl_34559 [cl_29369,cl_34555] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29369 v h) (hints_cons _ _ _ (der_34555 v h) (by intro d hd; cases hd)))
def cl_34560 : CNF.NClause := [(49,false),(73,true),(69,true),(86,true),(65,true),(77,true)]
theorem der_34560 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34560 :=
  CNF.rup_sound cl_34560 [cl_29370,cl_34544] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29370 v h) (hints_cons _ _ _ (der_34544 v h) (by intro d hd; cases hd)))
def cl_34564 : CNF.NClause := [(122,true),(49,false),(31,true),(37,true),(55,true),(43,false)]
theorem der_34564 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34564 :=
  CNF.rup_sound cl_34564 [cl_3860,cl_24839] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3860 v h) (hints_cons _ _ _ (der_24839 v h) (by intro d hd; cases hd)))
def cl_34566 : CNF.NClause := [(51,false),(46,false),(31,true),(36,true),(56,true),(123,true)]
theorem der_34566 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34566 :=
  CNF.rup_sound cl_34566 [cl_3944,cl_31118] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3944 v h) (hints_cons _ _ _ (der_31118 v h) (by intro d hd; cases hd)))
def cl_34568 : CNF.NClause := [(49,false),(77,true),(91,false),(86,false),(69,false),(18,false)]
theorem der_34568 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34568 :=
  CNF.rup_sound cl_34568 [cl_29372,cl_34488] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29372 v h) (hints_cons _ _ _ (der_34488 v h) (by intro d hd; cases hd)))
def cl_34569 : CNF.NClause := [(49,false),(65,false),(91,false),(69,false),(18,false),(86,true)]
theorem der_34569 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34569 :=
  CNF.rup_sound cl_34569 [cl_29374,cl_29373] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29374 v h) (hints_cons _ _ _ (der_29373 v h) (by intro d hd; cases hd)))
def cl_34570 : CNF.NClause := [(49,false),(77,true),(86,false),(69,false),(18,false),(91,true)]
theorem der_34570 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34570 :=
  CNF.rup_sound cl_34570 [cl_29376,cl_34488] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29376 v h) (hints_cons _ _ _ (der_34488 v h) (by intro d hd; cases hd)))
def cl_34571 : CNF.NClause := [(49,false),(77,false),(86,true),(69,false),(18,false),(65,false)]
theorem der_34571 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34571 :=
  CNF.rup_sound cl_34571 [cl_29377,cl_29373] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29377 v h) (hints_cons _ _ _ (der_29373 v h) (by intro d hd; cases hd)))
def cl_34573 : CNF.NClause := [(52,false),(79,true),(85,false),(88,false),(67,false),(21,false)]
theorem der_34573 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34573 :=
  CNF.rup_sound cl_34573 [cl_29380,cl_34428] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29380 v h) (hints_cons _ _ _ (der_34428 v h) (by intro d hd; cases hd)))
def cl_34574 : CNF.NClause := [(52,false),(85,true),(67,false),(79,false),(88,false),(21,false)]
theorem der_34574 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34574 :=
  CNF.rup_sound cl_34574 [cl_29381,cl_34432] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29381 v h) (hints_cons _ _ _ (der_34432 v h) (by intro d hd; cases hd)))
def cl_34575 : CNF.NClause := [(52,false),(85,true),(79,true),(88,false),(67,false),(21,false)]
theorem der_34575 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34575 :=
  CNF.rup_sound cl_34575 [cl_29382,cl_34407] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29382 v h) (hints_cons _ _ _ (der_34407 v h) (by intro d hd; cases hd)))
def cl_34576 : CNF.NClause := [(52,false),(85,false),(73,true),(67,false),(79,false),(21,false)]
theorem der_34576 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34576 :=
  CNF.rup_sound cl_34576 [cl_29383,cl_29379] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29383 v h) (hints_cons _ _ _ (der_29379 v h) (by intro d hd; cases hd)))
def cl_34577 : CNF.NClause := [(52,false),(79,true),(85,false),(67,false),(21,false),(88,true)]
theorem der_34577 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34577 :=
  CNF.rup_sound cl_34577 [cl_29384,cl_34410] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29384 v h) (hints_cons _ _ _ (der_34410 v h) (by intro d hd; cases hd)))
def cl_34578 : CNF.NClause := [(52,false),(67,false),(79,false),(66,false),(85,true),(21,false)]
theorem der_34578 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34578 :=
  CNF.rup_sound cl_34578 [cl_29385,cl_34574] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29385 v h) (hints_cons _ _ _ (der_34574 v h) (by intro d hd; cases hd)))
def cl_34579 : CNF.NClause := [(52,false),(67,false),(66,false),(85,true),(79,true),(21,false)]
theorem der_34579 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34579 :=
  CNF.rup_sound cl_34579 [cl_29386,cl_34575] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29386 v h) (hints_cons _ _ _ (der_34575 v h) (by intro d hd; cases hd)))
def cl_34580 : CNF.NClause := [(52,false),(85,false),(73,true),(88,false),(67,false),(79,false)]
theorem der_34580 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34580 :=
  CNF.rup_sound cl_34580 [cl_29387,cl_34424] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29387 v h) (hints_cons _ _ _ (der_34424 v h) (by intro d hd; cases hd)))
def cl_34581 : CNF.NClause := [(52,false),(79,true),(85,false),(88,false),(21,true),(66,false)]
theorem der_34581 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34581 :=
  CNF.rup_sound cl_34581 [cl_29388,cl_32094] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29388 v h) (hints_cons _ _ _ (der_32094 v h) (by intro d hd; cases hd)))
def cl_34582 : CNF.NClause := [(52,false),(85,true),(88,false),(67,false),(79,false),(21,true)]
theorem der_34582 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34582 :=
  CNF.rup_sound cl_34582 [cl_29389,cl_34432] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29389 v h) (hints_cons _ _ _ (der_34432 v h) (by intro d hd; cases hd)))
def cl_34583 : CNF.NClause := [(52,false),(85,true),(73,true),(79,true),(88,false),(67,false)]
theorem der_34583 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34583 :=
  CNF.rup_sound cl_34583 [cl_29390,cl_34575] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29390 v h) (hints_cons _ _ _ (der_34575 v h) (by intro d hd; cases hd)))
def cl_34584 : CNF.NClause := [(52,false),(85,false),(21,true),(73,true),(67,false),(79,false)]
theorem der_34584 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34584 :=
  CNF.rup_sound cl_34584 [cl_29391,cl_34580] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29391 v h) (hints_cons _ _ _ (der_34580 v h) (by intro d hd; cases hd)))
def cl_34585 : CNF.NClause := [(52,false),(67,false),(73,true),(79,true),(85,false),(88,true)]
theorem der_34585 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34585 :=
  CNF.rup_sound cl_34585 [cl_29392,cl_34577] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29392 v h) (hints_cons _ _ _ (der_34577 v h) (by intro d hd; cases hd)))
def cl_34586 : CNF.NClause := [(52,false),(73,true),(21,true),(67,false),(79,false),(88,true)]
theorem der_34586 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34586 :=
  CNF.rup_sound cl_34586 [cl_29393,cl_34446] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29393 v h) (hints_cons _ _ _ (der_34446 v h) (by intro d hd; cases hd)))
def cl_34587 : CNF.NClause := [(52,false),(85,true),(79,true),(66,false),(21,true),(88,true)]
theorem der_34587 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34587 :=
  CNF.rup_sound cl_34587 [cl_29394,cl_32104] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29394 v h) (hints_cons _ _ _ (der_32104 v h) (by intro d hd; cases hd)))
def cl_34588 : CNF.NClause := [(49,false),(69,false),(77,false),(91,false),(86,false),(18,true)]
theorem der_34588 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34588 :=
  CNF.rup_sound cl_34588 [cl_29395,cl_34531] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29395 v h) (hints_cons _ _ _ (der_34531 v h) (by intro d hd; cases hd)))
def cl_34589 : CNF.NClause := [(49,false),(86,false),(77,true),(18,true),(91,false),(69,false)]
theorem der_34589 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34589 :=
  CNF.rup_sound cl_34589 [cl_29396,cl_34533] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29396 v h) (hints_cons _ _ _ (der_34533 v h) (by intro d hd; cases hd)))
def cl_34590 : CNF.NClause := [(49,false),(69,false),(77,false),(91,false),(18,true),(65,false)]
theorem der_34590 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34590 :=
  CNF.rup_sound cl_34590 [cl_29397,cl_34588] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29397 v h) (hints_cons _ _ _ (der_34588 v h) (by intro d hd; cases hd)))
def cl_34591 : CNF.NClause := [(49,false),(65,false),(86,true),(77,true),(91,false),(69,false)]
theorem der_34591 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34591 :=
  CNF.rup_sound cl_34591 [cl_29398,cl_34569] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29398 v h) (hints_cons _ _ _ (der_34569 v h) (by intro d hd; cases hd)))
def cl_34592 : CNF.NClause := [(49,false),(77,false),(91,true),(86,false),(69,false),(65,false)]
theorem der_34592 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34592 :=
  CNF.rup_sound cl_34592 [cl_29399,cl_29375] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29399 v h) (hints_cons _ _ _ (der_29375 v h) (by intro d hd; cases hd)))
def cl_34593 : CNF.NClause := [(49,false),(86,false),(77,true),(69,false),(65,false),(91,true)]
theorem der_34593 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34593 :=
  CNF.rup_sound cl_34593 [cl_29400,cl_34570] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29400 v h) (hints_cons _ _ _ (der_34570 v h) (by intro d hd; cases hd)))
def cl_34594 : CNF.NClause := [(49,false),(69,false),(86,true),(77,false),(18,true),(91,true)]
theorem der_34594 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34594 :=
  CNF.rup_sound cl_34594 [cl_29401,cl_34553] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29401 v h) (hints_cons _ _ _ (der_34553 v h) (by intro d hd; cases hd)))
def cl_34595 : CNF.NClause := [(49,false),(86,true),(77,true),(69,false),(65,false),(18,true)]
theorem der_34595 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34595 :=
  CNF.rup_sound cl_34595 [cl_29402,cl_34591] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29402 v h) (hints_cons _ _ _ (der_34591 v h) (by intro d hd; cases hd)))
def cl_34596 : CNF.NClause := [(47,false),(75,false),(16,false),(66,false),(77,false),(89,true)]
theorem der_34596 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34596 :=
  CNF.rup_sound cl_34596 [cl_29404,cl_34362] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29404 v h) (hints_cons _ _ _ (der_34362 v h) (by intro d hd; cases hd)))
def cl_34597 : CNF.NClause := [(47,false),(66,false),(75,false),(77,false),(68,false),(89,true)]
theorem der_34597 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34597 :=
  CNF.rup_sound cl_34597 [cl_29405,cl_34301] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29405 v h) (hints_cons _ _ _ (der_34301 v h) (by intro d hd; cases hd)))
def cl_34598 : CNF.NClause := [(47,false),(16,false),(66,false),(75,false),(68,false),(89,true)]
theorem der_34598 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34598 :=
  CNF.rup_sound cl_34598 [cl_29406,cl_34596] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29406 v h) (hints_cons _ _ _ (der_34596 v h) (by intro d hd; cases hd)))
def cl_34599 : CNF.NClause := [(47,false),(89,true),(66,false),(75,false),(16,true),(68,false)]
theorem der_34599 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34599 :=
  CNF.rup_sound cl_34599 [cl_29407,cl_34597] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29407 v h) (hints_cons _ _ _ (der_34597 v h) (by intro d hd; cases hd)))
def chunk022 : List CNF.NClause := [cl_34008,cl_34009,cl_34010,cl_34011,cl_34012,cl_34013,cl_34014,cl_34015,cl_34016,cl_34017,cl_34018,cl_34019,cl_34020,cl_34021,cl_34022,cl_34023,cl_34024,cl_34025,cl_34026,cl_34027,cl_34029,cl_34030,cl_34031,cl_34032,cl_34033,cl_34034,cl_34035,cl_34036,cl_34037,cl_34038,cl_34039,cl_34040,cl_34041,cl_34042,cl_34043,cl_34044,cl_34045,cl_34046,cl_34047,cl_34048,cl_34049,cl_34050,cl_34051,cl_34052,cl_34053,cl_34054,cl_34055,cl_34056,cl_34058,cl_34059,cl_34060,cl_34061,cl_34062,cl_34063,cl_34064,cl_34065,cl_34067,cl_34071,cl_34076,cl_34077,cl_34078,cl_34079,cl_34080,cl_34081,cl_34083,cl_34084,cl_34087,cl_34088,cl_34089,cl_34090,cl_34091,cl_34092,cl_34094,cl_34096,cl_34097,cl_34098,cl_34100,cl_34101,cl_34102,cl_34105,cl_34106,cl_34107,cl_34108,cl_34109,cl_34110,cl_34111,cl_34112,cl_34113,cl_34114,cl_34115,cl_34116,cl_34117,cl_34118,cl_34119,cl_34120,cl_34121,cl_34122,cl_34123,cl_34125,cl_34126,cl_34127,cl_34128,cl_34130,cl_34131,cl_34132,cl_34133,cl_34134,cl_34135,cl_34136,cl_34137,cl_34138,cl_34139,cl_34140,cl_34141,cl_34143,cl_34144,cl_34145,cl_34146,cl_34147,cl_34149,cl_34150,cl_34151,cl_34152,cl_34153,cl_34154,cl_34156,cl_34157,cl_34159,cl_34160,cl_34161,cl_34162,cl_34163,cl_34164,cl_34165,cl_34166,cl_34167,cl_34168,cl_34170,cl_34171,cl_34172,cl_34173,cl_34174,cl_34175,cl_34176,cl_34177,cl_34178,cl_34179,cl_34180,cl_34181,cl_34182,cl_34184,cl_34185,cl_34186,cl_34187,cl_34188,cl_34189,cl_34190,cl_34191,cl_34192,cl_34193,cl_34194,cl_34196,cl_34197,cl_34198,cl_34199,cl_34200,cl_34201,cl_34202,cl_34203,cl_34204,cl_34206,cl_34207,cl_34208,cl_34209,cl_34210,cl_34211,cl_34212,cl_34213,cl_34214,cl_34215,cl_34216,cl_34217,cl_34218,cl_34219,cl_34220,cl_34221,cl_34222,cl_34223,cl_34224,cl_34225,cl_34226,cl_34227,cl_34228,cl_34229,cl_34230,cl_34231,cl_34232,cl_34233,cl_34234,cl_34235,cl_34236,cl_34237,cl_34238,cl_34239,cl_34240,cl_34243,cl_34244,cl_34245,cl_34246,cl_34248,cl_34249,cl_34250,cl_34251,cl_34252,cl_34253,cl_34254,cl_34255,cl_34256,cl_34257,cl_34258,cl_34259,cl_34260,cl_34262,cl_34263,cl_34264,cl_34265,cl_34266,cl_34267,cl_34268,cl_34269,cl_34270,cl_34271,cl_34273,cl_34275,cl_34276,cl_34278,cl_34279,cl_34280,cl_34281,cl_34282,cl_34283,cl_34284,cl_34285,cl_34286,cl_34287,cl_34288,cl_34290,cl_34291,cl_34292,cl_34293,cl_34294,cl_34296,cl_34297,cl_34298,cl_34299,cl_34300,cl_34301,cl_34303,cl_34305,cl_34306,cl_34307,cl_34308,cl_34309,cl_34310,cl_34311,cl_34313,cl_34314,cl_34316,cl_34317,cl_34318,cl_34319,cl_34320,cl_34321,cl_34322,cl_34323,cl_34324,cl_34325,cl_34327,cl_34328,cl_34329,cl_34330,cl_34331,cl_34332,cl_34333,cl_34334,cl_34336,cl_34337,cl_34338,cl_34339,cl_34340,cl_34341,cl_34342,cl_34343,cl_34344,cl_34345,cl_34346,cl_34348,cl_34350,cl_34351,cl_34352,cl_34353,cl_34354,cl_34355,cl_34357,cl_34358,cl_34359,cl_34361,cl_34362,cl_34363,cl_34365,cl_34367,cl_34368,cl_34369,cl_34370,cl_34371,cl_34372,cl_34373,cl_34376,cl_34378,cl_34379,cl_34380,cl_34381,cl_34382,cl_34383,cl_34384,cl_34386,cl_34387,cl_34388,cl_34389,cl_34390,cl_34391,cl_34392,cl_34393,cl_34394,cl_34395,cl_34398,cl_34399,cl_34400,cl_34402,cl_34403,cl_34405,cl_34406,cl_34407,cl_34410,cl_34412,cl_34414,cl_34416,cl_34417,cl_34418,cl_34419,cl_34420,cl_34421,cl_34422,cl_34423,cl_34424,cl_34425,cl_34426,cl_34427,cl_34428,cl_34429,cl_34430,cl_34431,cl_34432,cl_34433,cl_34434,cl_34435,cl_34436,cl_34438,cl_34439,cl_34440,cl_34441,cl_34442,cl_34443,cl_34444,cl_34445,cl_34446,cl_34447,cl_34448,cl_34449,cl_34450,cl_34451,cl_34452,cl_34453,cl_34454,cl_34455,cl_34456,cl_34457,cl_34458,cl_34459,cl_34460,cl_34461,cl_34463,cl_34464,cl_34465,cl_34466,cl_34467,cl_34468,cl_34469,cl_34470,cl_34471,cl_34473,cl_34474,cl_34475,cl_34477,cl_34480,cl_34483,cl_34484,cl_34485,cl_34488,cl_34490,cl_34492,cl_34493,cl_34494,cl_34495,cl_34496,cl_34497,cl_34499,cl_34500,cl_34501,cl_34502,cl_34503,cl_34504,cl_34506,cl_34507,cl_34508,cl_34510,cl_34511,cl_34512,cl_34513,cl_34514,cl_34515,cl_34518,cl_34519,cl_34520,cl_34522,cl_34524,cl_34526,cl_34529,cl_34530,cl_34531,cl_34532,cl_34533,cl_34534,cl_34536,cl_34537,cl_34538,cl_34539,cl_34541,cl_34542,cl_34543,cl_34544,cl_34545,cl_34546,cl_34547,cl_34548,cl_34549,cl_34550,cl_34551,cl_34552,cl_34553,cl_34554,cl_34555,cl_34556,cl_34557,cl_34558,cl_34559,cl_34560,cl_34564,cl_34566,cl_34568,cl_34569,cl_34570,cl_34571,cl_34573,cl_34574,cl_34575,cl_34576,cl_34577,cl_34578,cl_34579,cl_34580,cl_34581,cl_34582,cl_34583,cl_34584,cl_34585,cl_34586,cl_34587,cl_34588,cl_34589,cl_34590,cl_34591,cl_34592,cl_34593,cl_34594,cl_34595,cl_34596,cl_34597,cl_34598,cl_34599]
theorem chunk_sound022 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : ∀ c ∈ chunk022, CNF.Holds (v ∘ decodeVar) c :=
  (hints_cons _ _ _ (der_34008 v h) (hints_cons _ _ _ (der_34009 v h) (hints_cons _ _ _ (der_34010 v h) (hints_cons _ _ _ (der_34011 v h) (hints_cons _ _ _ (der_34012 v h) (hints_cons _ _ _ (der_34013 v h) (hints_cons _ _ _ (der_34014 v h) (hints_cons _ _ _ (der_34015 v h) (hints_cons _ _ _ (der_34016 v h) (hints_cons _ _ _ (der_34017 v h) (hints_cons _ _ _ (der_34018 v h) (hints_cons _ _ _ (der_34019 v h) (hints_cons _ _ _ (der_34020 v h) (hints_cons _ _ _ (der_34021 v h) (hints_cons _ _ _ (der_34022 v h) (hints_cons _ _ _ (der_34023 v h) (hints_cons _ _ _ (der_34024 v h) (hints_cons _ _ _ (der_34025 v h) (hints_cons _ _ _ (der_34026 v h) (hints_cons _ _ _ (der_34027 v h) (hints_cons _ _ _ (der_34029 v h) (hints_cons _ _ _ (der_34030 v h) (hints_cons _ _ _ (der_34031 v h) (hints_cons _ _ _ (der_34032 v h) (hints_cons _ _ _ (der_34033 v h) (hints_cons _ _ _ (der_34034 v h) (hints_cons _ _ _ (der_34035 v h) (hints_cons _ _ _ (der_34036 v h) (hints_cons _ _ _ (der_34037 v h) (hints_cons _ _ _ (der_34038 v h) (hints_cons _ _ _ (der_34039 v h) (hints_cons _ _ _ (der_34040 v h) (hints_cons _ _ _ (der_34041 v h) (hints_cons _ _ _ (der_34042 v h) (hints_cons _ _ _ (der_34043 v h) (hints_cons _ _ _ (der_34044 v h) (hints_cons _ _ _ (der_34045 v h) (hints_cons _ _ _ (der_34046 v h) (hints_cons _ _ _ (der_34047 v h) (hints_cons _ _ _ (der_34048 v h) (hints_cons _ _ _ (der_34049 v h) (hints_cons _ _ _ (der_34050 v h) (hints_cons _ _ _ (der_34051 v h) (hints_cons _ _ _ (der_34052 v h) (hints_cons _ _ _ (der_34053 v h) (hints_cons _ _ _ (der_34054 v h) (hints_cons _ _ _ (der_34055 v h) (hints_cons _ _ _ (der_34056 v h) (hints_cons _ _ _ (der_34058 v h) (hints_cons _ _ _ (der_34059 v h) (hints_cons _ _ _ (der_34060 v h) (hints_cons _ _ _ (der_34061 v h) (hints_cons _ _ _ (der_34062 v h) (hints_cons _ _ _ (der_34063 v h) (hints_cons _ _ _ (der_34064 v h) (hints_cons _ _ _ (der_34065 v h) (hints_cons _ _ _ (der_34067 v h) (hints_cons _ _ _ (der_34071 v h) (hints_cons _ _ _ (der_34076 v h) (hints_cons _ _ _ (der_34077 v h) (hints_cons _ _ _ (der_34078 v h) (hints_cons _ _ _ (der_34079 v h) (hints_cons _ _ _ (der_34080 v h) (hints_cons _ _ _ (der_34081 v h) (hints_cons _ _ _ (der_34083 v h) (hints_cons _ _ _ (der_34084 v h) (hints_cons _ _ _ (der_34087 v h) (hints_cons _ _ _ (der_34088 v h) (hints_cons _ _ _ (der_34089 v h) (hints_cons _ _ _ (der_34090 v h) (hints_cons _ _ _ (der_34091 v h) (hints_cons _ _ _ (der_34092 v h) (hints_cons _ _ _ (der_34094 v h) (hints_cons _ _ _ (der_34096 v h) (hints_cons _ _ _ (der_34097 v h) (hints_cons _ _ _ (der_34098 v h) (hints_cons _ _ _ (der_34100 v h) (hints_cons _ _ _ (der_34101 v h) (hints_cons _ _ _ (der_34102 v h) (hints_cons _ _ _ (der_34105 v h) (hints_cons _ _ _ (der_34106 v h) (hints_cons _ _ _ (der_34107 v h) (hints_cons _ _ _ (der_34108 v h) (hints_cons _ _ _ (der_34109 v h) (hints_cons _ _ _ (der_34110 v h) (hints_cons _ _ _ (der_34111 v h) (hints_cons _ _ _ (der_34112 v h) (hints_cons _ _ _ (der_34113 v h) (hints_cons _ _ _ (der_34114 v h) (hints_cons _ _ _ (der_34115 v h) (hints_cons _ _ _ (der_34116 v h) (hints_cons _ _ _ (der_34117 v h) (hints_cons _ _ _ (der_34118 v h) (hints_cons _ _ _ (der_34119 v h) (hints_cons _ _ _ (der_34120 v h) (hints_cons _ _ _ (der_34121 v h) (hints_cons _ _ _ (der_34122 v h) (hints_cons _ _ _ (der_34123 v h) (hints_cons _ _ _ (der_34125 v h) (hints_cons _ _ _ (der_34126 v h) (hints_cons _ _ _ (der_34127 v h) (hints_cons _ _ _ (der_34128 v h) (hints_cons _ _ _ (der_34130 v h) (hints_cons _ _ _ (der_34131 v h) (hints_cons _ _ _ (der_34132 v h) (hints_cons _ _ _ (der_34133 v h) (hints_cons _ _ _ (der_34134 v h) (hints_cons _ _ _ (der_34135 v h) (hints_cons _ _ _ (der_34136 v h) (hints_cons _ _ _ (der_34137 v h) (hints_cons _ _ _ (der_34138 v h) (hints_cons _ _ _ (der_34139 v h) (hints_cons _ _ _ (der_34140 v h) (hints_cons _ _ _ (der_34141 v h) (hints_cons _ _ _ (der_34143 v h) (hints_cons _ _ _ (der_34144 v h) (hints_cons _ _ _ (der_34145 v h) (hints_cons _ _ _ (der_34146 v h) (hints_cons _ _ _ (der_34147 v h) (hints_cons _ _ _ (der_34149 v h) (hints_cons _ _ _ (der_34150 v h) (hints_cons _ _ _ (der_34151 v h) (hints_cons _ _ _ (der_34152 v h) (hints_cons _ _ _ (der_34153 v h) (hints_cons _ _ _ (der_34154 v h) (hints_cons _ _ _ (der_34156 v h) (hints_cons _ _ _ (der_34157 v h) (hints_cons _ _ _ (der_34159 v h) (hints_cons _ _ _ (der_34160 v h) (hints_cons _ _ _ (der_34161 v h) (hints_cons _ _ _ (der_34162 v h) (hints_cons _ _ _ (der_34163 v h) (hints_cons _ _ _ (der_34164 v h) (hints_cons _ _ _ (der_34165 v h) (hints_cons _ _ _ (der_34166 v h) (hints_cons _ _ _ (der_34167 v h) (hints_cons _ _ _ (der_34168 v h) (hints_cons _ _ _ (der_34170 v h) (hints_cons _ _ _ (der_34171 v h) (hints_cons _ _ _ (der_34172 v h) (hints_cons _ _ _ (der_34173 v h) (hints_cons _ _ _ (der_34174 v h) (hints_cons _ _ _ (der_34175 v h) (hints_cons _ _ _ (der_34176 v h) (hints_cons _ _ _ (der_34177 v h) (hints_cons _ _ _ (der_34178 v h) (hints_cons _ _ _ (der_34179 v h) (hints_cons _ _ _ (der_34180 v h) (hints_cons _ _ _ (der_34181 v h) (hints_cons _ _ _ (der_34182 v h) (hints_cons _ _ _ (der_34184 v h) (hints_cons _ _ _ (der_34185 v h) (hints_cons _ _ _ (der_34186 v h) (hints_cons _ _ _ (der_34187 v h) (hints_cons _ _ _ (der_34188 v h) (hints_cons _ _ _ (der_34189 v h) (hints_cons _ _ _ (der_34190 v h) (hints_cons _ _ _ (der_34191 v h) (hints_cons _ _ _ (der_34192 v h) (hints_cons _ _ _ (der_34193 v h) (hints_cons _ _ _ (der_34194 v h) (hints_cons _ _ _ (der_34196 v h) (hints_cons _ _ _ (der_34197 v h) (hints_cons _ _ _ (der_34198 v h) (hints_cons _ _ _ (der_34199 v h) (hints_cons _ _ _ (der_34200 v h) (hints_cons _ _ _ (der_34201 v h) (hints_cons _ _ _ (der_34202 v h) (hints_cons _ _ _ (der_34203 v h) (hints_cons _ _ _ (der_34204 v h) (hints_cons _ _ _ (der_34206 v h) (hints_cons _ _ _ (der_34207 v h) (hints_cons _ _ _ (der_34208 v h) (hints_cons _ _ _ (der_34209 v h) (hints_cons _ _ _ (der_34210 v h) (hints_cons _ _ _ (der_34211 v h) (hints_cons _ _ _ (der_34212 v h) (hints_cons _ _ _ (der_34213 v h) (hints_cons _ _ _ (der_34214 v h) (hints_cons _ _ _ (der_34215 v h) (hints_cons _ _ _ (der_34216 v h) (hints_cons _ _ _ (der_34217 v h) (hints_cons _ _ _ (der_34218 v h) (hints_cons _ _ _ (der_34219 v h) (hints_cons _ _ _ (der_34220 v h) (hints_cons _ _ _ (der_34221 v h) (hints_cons _ _ _ (der_34222 v h) (hints_cons _ _ _ (der_34223 v h) (hints_cons _ _ _ (der_34224 v h) (hints_cons _ _ _ (der_34225 v h) (hints_cons _ _ _ (der_34226 v h) (hints_cons _ _ _ (der_34227 v h) (hints_cons _ _ _ (der_34228 v h) (hints_cons _ _ _ (der_34229 v h) (hints_cons _ _ _ (der_34230 v h) (hints_cons _ _ _ (der_34231 v h) (hints_cons _ _ _ (der_34232 v h) (hints_cons _ _ _ (der_34233 v h) (hints_cons _ _ _ (der_34234 v h) (hints_cons _ _ _ (der_34235 v h) (hints_cons _ _ _ (der_34236 v h) (hints_cons _ _ _ (der_34237 v h) (hints_cons _ _ _ (der_34238 v h) (hints_cons _ _ _ (der_34239 v h) (hints_cons _ _ _ (der_34240 v h) (hints_cons _ _ _ (der_34243 v h) (hints_cons _ _ _ (der_34244 v h) (hints_cons _ _ _ (der_34245 v h) (hints_cons _ _ _ (der_34246 v h) (hints_cons _ _ _ (der_34248 v h) (hints_cons _ _ _ (der_34249 v h) (hints_cons _ _ _ (der_34250 v h) (hints_cons _ _ _ (der_34251 v h) (hints_cons _ _ _ (der_34252 v h) (hints_cons _ _ _ (der_34253 v h) (hints_cons _ _ _ (der_34254 v h) (hints_cons _ _ _ (der_34255 v h) (hints_cons _ _ _ (der_34256 v h) (hints_cons _ _ _ (der_34257 v h) (hints_cons _ _ _ (der_34258 v h) (hints_cons _ _ _ (der_34259 v h) (hints_cons _ _ _ (der_34260 v h) (hints_cons _ _ _ (der_34262 v h) (hints_cons _ _ _ (der_34263 v h) (hints_cons _ _ _ (der_34264 v h) (hints_cons _ _ _ (der_34265 v h) (hints_cons _ _ _ (der_34266 v h) (hints_cons _ _ _ (der_34267 v h) (hints_cons _ _ _ (der_34268 v h) (hints_cons _ _ _ (der_34269 v h) (hints_cons _ _ _ (der_34270 v h) (hints_cons _ _ _ (der_34271 v h) (hints_cons _ _ _ (der_34273 v h) (hints_cons _ _ _ (der_34275 v h) (hints_cons _ _ _ (der_34276 v h) (hints_cons _ _ _ (der_34278 v h) (hints_cons _ _ _ (der_34279 v h) (hints_cons _ _ _ (der_34280 v h) (hints_cons _ _ _ (der_34281 v h) (hints_cons _ _ _ (der_34282 v h) (hints_cons _ _ _ (der_34283 v h) (hints_cons _ _ _ (der_34284 v h) (hints_cons _ _ _ (der_34285 v h) (hints_cons _ _ _ (der_34286 v h) (hints_cons _ _ _ (der_34287 v h) (hints_cons _ _ _ (der_34288 v h) (hints_cons _ _ _ (der_34290 v h) (hints_cons _ _ _ (der_34291 v h) (hints_cons _ _ _ (der_34292 v h) (hints_cons _ _ _ (der_34293 v h) (hints_cons _ _ _ (der_34294 v h) (hints_cons _ _ _ (der_34296 v h) (hints_cons _ _ _ (der_34297 v h) (hints_cons _ _ _ (der_34298 v h) (hints_cons _ _ _ (der_34299 v h) (hints_cons _ _ _ (der_34300 v h) (hints_cons _ _ _ (der_34301 v h) (hints_cons _ _ _ (der_34303 v h) (hints_cons _ _ _ (der_34305 v h) (hints_cons _ _ _ (der_34306 v h) (hints_cons _ _ _ (der_34307 v h) (hints_cons _ _ _ (der_34308 v h) (hints_cons _ _ _ (der_34309 v h) (hints_cons _ _ _ (der_34310 v h) (hints_cons _ _ _ (der_34311 v h) (hints_cons _ _ _ (der_34313 v h) (hints_cons _ _ _ (der_34314 v h) (hints_cons _ _ _ (der_34316 v h) (hints_cons _ _ _ (der_34317 v h) (hints_cons _ _ _ (der_34318 v h) (hints_cons _ _ _ (der_34319 v h) (hints_cons _ _ _ (der_34320 v h) (hints_cons _ _ _ (der_34321 v h) (hints_cons _ _ _ (der_34322 v h) (hints_cons _ _ _ (der_34323 v h) (hints_cons _ _ _ (der_34324 v h) (hints_cons _ _ _ (der_34325 v h) (hints_cons _ _ _ (der_34327 v h) (hints_cons _ _ _ (der_34328 v h) (hints_cons _ _ _ (der_34329 v h) (hints_cons _ _ _ (der_34330 v h) (hints_cons _ _ _ (der_34331 v h) (hints_cons _ _ _ (der_34332 v h) (hints_cons _ _ _ (der_34333 v h) (hints_cons _ _ _ (der_34334 v h) (hints_cons _ _ _ (der_34336 v h) (hints_cons _ _ _ (der_34337 v h) (hints_cons _ _ _ (der_34338 v h) (hints_cons _ _ _ (der_34339 v h) (hints_cons _ _ _ (der_34340 v h) (hints_cons _ _ _ (der_34341 v h) (hints_cons _ _ _ (der_34342 v h) (hints_cons _ _ _ (der_34343 v h) (hints_cons _ _ _ (der_34344 v h) (hints_cons _ _ _ (der_34345 v h) (hints_cons _ _ _ (der_34346 v h) (hints_cons _ _ _ (der_34348 v h) (hints_cons _ _ _ (der_34350 v h) (hints_cons _ _ _ (der_34351 v h) (hints_cons _ _ _ (der_34352 v h) (hints_cons _ _ _ (der_34353 v h) (hints_cons _ _ _ (der_34354 v h) (hints_cons _ _ _ (der_34355 v h) (hints_cons _ _ _ (der_34357 v h) (hints_cons _ _ _ (der_34358 v h) (hints_cons _ _ _ (der_34359 v h) (hints_cons _ _ _ (der_34361 v h) (hints_cons _ _ _ (der_34362 v h) (hints_cons _ _ _ (der_34363 v h) (hints_cons _ _ _ (der_34365 v h) (hints_cons _ _ _ (der_34367 v h) (hints_cons _ _ _ (der_34368 v h) (hints_cons _ _ _ (der_34369 v h) (hints_cons _ _ _ (der_34370 v h) (hints_cons _ _ _ (der_34371 v h) (hints_cons _ _ _ (der_34372 v h) (hints_cons _ _ _ (der_34373 v h) (hints_cons _ _ _ (der_34376 v h) (hints_cons _ _ _ (der_34378 v h) (hints_cons _ _ _ (der_34379 v h) (hints_cons _ _ _ (der_34380 v h) (hints_cons _ _ _ (der_34381 v h) (hints_cons _ _ _ (der_34382 v h) (hints_cons _ _ _ (der_34383 v h) (hints_cons _ _ _ (der_34384 v h) (hints_cons _ _ _ (der_34386 v h) (hints_cons _ _ _ (der_34387 v h) (hints_cons _ _ _ (der_34388 v h) (hints_cons _ _ _ (der_34389 v h) (hints_cons _ _ _ (der_34390 v h) (hints_cons _ _ _ (der_34391 v h) (hints_cons _ _ _ (der_34392 v h) (hints_cons _ _ _ (der_34393 v h) (hints_cons _ _ _ (der_34394 v h) (hints_cons _ _ _ (der_34395 v h) (hints_cons _ _ _ (der_34398 v h) (hints_cons _ _ _ (der_34399 v h) (hints_cons _ _ _ (der_34400 v h) (hints_cons _ _ _ (der_34402 v h) (hints_cons _ _ _ (der_34403 v h) (hints_cons _ _ _ (der_34405 v h) (hints_cons _ _ _ (der_34406 v h) (hints_cons _ _ _ (der_34407 v h) (hints_cons _ _ _ (der_34410 v h) (hints_cons _ _ _ (der_34412 v h) (hints_cons _ _ _ (der_34414 v h) (hints_cons _ _ _ (der_34416 v h) (hints_cons _ _ _ (der_34417 v h) (hints_cons _ _ _ (der_34418 v h) (hints_cons _ _ _ (der_34419 v h) (hints_cons _ _ _ (der_34420 v h) (hints_cons _ _ _ (der_34421 v h) (hints_cons _ _ _ (der_34422 v h) (hints_cons _ _ _ (der_34423 v h) (hints_cons _ _ _ (der_34424 v h) (hints_cons _ _ _ (der_34425 v h) (hints_cons _ _ _ (der_34426 v h) (hints_cons _ _ _ (der_34427 v h) (hints_cons _ _ _ (der_34428 v h) (hints_cons _ _ _ (der_34429 v h) (hints_cons _ _ _ (der_34430 v h) (hints_cons _ _ _ (der_34431 v h) (hints_cons _ _ _ (der_34432 v h) (hints_cons _ _ _ (der_34433 v h) (hints_cons _ _ _ (der_34434 v h) (hints_cons _ _ _ (der_34435 v h) (hints_cons _ _ _ (der_34436 v h) (hints_cons _ _ _ (der_34438 v h) (hints_cons _ _ _ (der_34439 v h) (hints_cons _ _ _ (der_34440 v h) (hints_cons _ _ _ (der_34441 v h) (hints_cons _ _ _ (der_34442 v h) (hints_cons _ _ _ (der_34443 v h) (hints_cons _ _ _ (der_34444 v h) (hints_cons _ _ _ (der_34445 v h) (hints_cons _ _ _ (der_34446 v h) (hints_cons _ _ _ (der_34447 v h) (hints_cons _ _ _ (der_34448 v h) (hints_cons _ _ _ (der_34449 v h) (hints_cons _ _ _ (der_34450 v h) (hints_cons _ _ _ (der_34451 v h) (hints_cons _ _ _ (der_34452 v h) (hints_cons _ _ _ (der_34453 v h) (hints_cons _ _ _ (der_34454 v h) (hints_cons _ _ _ (der_34455 v h) (hints_cons _ _ _ (der_34456 v h) (hints_cons _ _ _ (der_34457 v h) (hints_cons _ _ _ (der_34458 v h) (hints_cons _ _ _ (der_34459 v h) (hints_cons _ _ _ (der_34460 v h) (hints_cons _ _ _ (der_34461 v h) (hints_cons _ _ _ (der_34463 v h) (hints_cons _ _ _ (der_34464 v h) (hints_cons _ _ _ (der_34465 v h) (hints_cons _ _ _ (der_34466 v h) (hints_cons _ _ _ (der_34467 v h) (hints_cons _ _ _ (der_34468 v h) (hints_cons _ _ _ (der_34469 v h) (hints_cons _ _ _ (der_34470 v h) (hints_cons _ _ _ (der_34471 v h) (hints_cons _ _ _ (der_34473 v h) (hints_cons _ _ _ (der_34474 v h) (hints_cons _ _ _ (der_34475 v h) (hints_cons _ _ _ (der_34477 v h) (hints_cons _ _ _ (der_34480 v h) (hints_cons _ _ _ (der_34483 v h) (hints_cons _ _ _ (der_34484 v h) (hints_cons _ _ _ (der_34485 v h) (hints_cons _ _ _ (der_34488 v h) (hints_cons _ _ _ (der_34490 v h) (hints_cons _ _ _ (der_34492 v h) (hints_cons _ _ _ (der_34493 v h) (hints_cons _ _ _ (der_34494 v h) (hints_cons _ _ _ (der_34495 v h) (hints_cons _ _ _ (der_34496 v h) (hints_cons _ _ _ (der_34497 v h) (hints_cons _ _ _ (der_34499 v h) (hints_cons _ _ _ (der_34500 v h) (hints_cons _ _ _ (der_34501 v h) (hints_cons _ _ _ (der_34502 v h) (hints_cons _ _ _ (der_34503 v h) (hints_cons _ _ _ (der_34504 v h) (hints_cons _ _ _ (der_34506 v h) (hints_cons _ _ _ (der_34507 v h) (hints_cons _ _ _ (der_34508 v h) (hints_cons _ _ _ (der_34510 v h) (hints_cons _ _ _ (der_34511 v h) (hints_cons _ _ _ (der_34512 v h) (hints_cons _ _ _ (der_34513 v h) (hints_cons _ _ _ (der_34514 v h) (hints_cons _ _ _ (der_34515 v h) (hints_cons _ _ _ (der_34518 v h) (hints_cons _ _ _ (der_34519 v h) (hints_cons _ _ _ (der_34520 v h) (hints_cons _ _ _ (der_34522 v h) (hints_cons _ _ _ (der_34524 v h) (hints_cons _ _ _ (der_34526 v h) (hints_cons _ _ _ (der_34529 v h) (hints_cons _ _ _ (der_34530 v h) (hints_cons _ _ _ (der_34531 v h) (hints_cons _ _ _ (der_34532 v h) (hints_cons _ _ _ (der_34533 v h) (hints_cons _ _ _ (der_34534 v h) (hints_cons _ _ _ (der_34536 v h) (hints_cons _ _ _ (der_34537 v h) (hints_cons _ _ _ (der_34538 v h) (hints_cons _ _ _ (der_34539 v h) (hints_cons _ _ _ (der_34541 v h) (hints_cons _ _ _ (der_34542 v h) (hints_cons _ _ _ (der_34543 v h) (hints_cons _ _ _ (der_34544 v h) (hints_cons _ _ _ (der_34545 v h) (hints_cons _ _ _ (der_34546 v h) (hints_cons _ _ _ (der_34547 v h) (hints_cons _ _ _ (der_34548 v h) (hints_cons _ _ _ (der_34549 v h) (hints_cons _ _ _ (der_34550 v h) (hints_cons _ _ _ (der_34551 v h) (hints_cons _ _ _ (der_34552 v h) (hints_cons _ _ _ (der_34553 v h) (hints_cons _ _ _ (der_34554 v h) (hints_cons _ _ _ (der_34555 v h) (hints_cons _ _ _ (der_34556 v h) (hints_cons _ _ _ (der_34557 v h) (hints_cons _ _ _ (der_34558 v h) (hints_cons _ _ _ (der_34559 v h) (hints_cons _ _ _ (der_34560 v h) (hints_cons _ _ _ (der_34564 v h) (hints_cons _ _ _ (der_34566 v h) (hints_cons _ _ _ (der_34568 v h) (hints_cons _ _ _ (der_34569 v h) (hints_cons _ _ _ (der_34570 v h) (hints_cons _ _ _ (der_34571 v h) (hints_cons _ _ _ (der_34573 v h) (hints_cons _ _ _ (der_34574 v h) (hints_cons _ _ _ (der_34575 v h) (hints_cons _ _ _ (der_34576 v h) (hints_cons _ _ _ (der_34577 v h) (hints_cons _ _ _ (der_34578 v h) (hints_cons _ _ _ (der_34579 v h) (hints_cons _ _ _ (der_34580 v h) (hints_cons _ _ _ (der_34581 v h) (hints_cons _ _ _ (der_34582 v h) (hints_cons _ _ _ (der_34583 v h) (hints_cons _ _ _ (der_34584 v h) (hints_cons _ _ _ (der_34585 v h) (hints_cons _ _ _ (der_34586 v h) (hints_cons _ _ _ (der_34587 v h) (hints_cons _ _ _ (der_34588 v h) (hints_cons _ _ _ (der_34589 v h) (hints_cons _ _ _ (der_34590 v h) (hints_cons _ _ _ (der_34591 v h) (hints_cons _ _ _ (der_34592 v h) (hints_cons _ _ _ (der_34593 v h) (hints_cons _ _ _ (der_34594 v h) (hints_cons _ _ _ (der_34595 v h) (hints_cons _ _ _ (der_34596 v h) (hints_cons _ _ _ (der_34597 v h) (hints_cons _ _ _ (der_34598 v h) (hints_cons _ _ _ (der_34599 v h) (by intro d hd; cases hd)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def prefix022 := prefix021 ++ chunk022
theorem prefix_sound022 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : ∀ c ∈ prefix022, CNF.Holds (v ∘ decodeVar) c := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact prefix_sound021 v h c hc
  · exact chunk_sound022 v h c hc
end Percolation.NReplay
