import NReplay074
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_76662 : CNF.NClause := [(122,true),(57,false),(55,false)]
theorem der_76662 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76662 :=
  CNF.rup_sound cl_76662 [cl_64182,cl_64209] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_64182 v h) (hints_cons _ _ _ (der_64209 v h) (by intro d hd; cases hd)))
def cl_76663 : CNF.NClause := [(49,false),(122,true),(43,false)]
theorem der_76663 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76663 :=
  CNF.rup_sound cl_76663 [cl_64183,cl_64187] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_64183 v h) (hints_cons _ _ _ (der_64187 v h) (by intro d hd; cases hd)))
def cl_76664 : CNF.NClause := [(122,true),(49,false),(57,false)]
theorem der_76664 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76664 :=
  CNF.rup_sound cl_76664 [cl_64184,cl_50048] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_64184 v h) (hints_cons _ _ _ (der_50048 v h) (by intro d hd; cases hd)))
def cl_76665 : CNF.NClause := [(49,false),(122,true),(55,false)]
theorem der_76665 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76665 :=
  CNF.rup_sound cl_76665 [cl_64186,cl_76663] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_64186 v h) (hints_cons _ _ _ (der_76663 v h) (by intro d hd; cases hd)))
def cl_76667 : CNF.NClause := [(113,true),(39,false),(37,false)]
theorem der_76667 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76667 :=
  CNF.rup_sound cl_76667 [cl_64191,cl_76661] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_64191 v h) (hints_cons _ _ _ (der_76661 v h) (by intro d hd; cases hd)))
def cl_76668 : CNF.NClause := [(59,false),(115,true),(33,false)]
theorem der_76668 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76668 :=
  CNF.rup_sound cl_76668 [cl_50221,cl_49880] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50221 v h) (hints_cons _ _ _ (der_49880 v h) (by intro d hd; cases hd)))
def cl_76669 : CNF.NClause := [(115,true),(33,false),(55,false)]
theorem der_76669 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76669 :=
  CNF.rup_sound cl_76669 [cl_50222,cl_49851] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50222 v h) (hints_cons _ _ _ (der_49851 v h) (by intro d hd; cases hd)))
def cl_76670 : CNF.NClause := [(32,false),(117,true),(60,false)]
theorem der_76670 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76670 :=
  CNF.rup_sound cl_76670 [cl_50225,cl_49896] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50225 v h) (hints_cons _ _ _ (der_49896 v h) (by intro d hd; cases hd)))
def cl_76671 : CNF.NClause := [(114,true),(35,false),(57,false)]
theorem der_76671 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76671 :=
  CNF.rup_sound cl_76671 [cl_50226,cl_49724] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50226 v h) (hints_cons _ _ _ (der_49724 v h) (by intro d hd; cases hd)))
def cl_76672 : CNF.NClause := [(116,true),(50,false),(34,false)]
theorem der_76672 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76672 :=
  CNF.rup_sound cl_76672 [cl_50229,cl_49981] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50229 v h) (hints_cons _ _ _ (der_49981 v h) (by intro d hd; cases hd)))
def cl_76673 : CNF.NClause := [(48,false),(119,true),(40,false)]
theorem der_76673 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76673 :=
  CNF.rup_sound cl_76673 [cl_36020,cl_64221] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_36020 v h) (hints_cons _ _ _ (der_64221 v h) (by intro d hd; cases hd)))
def cl_76675 : CNF.NClause := [(120,true),(38,false),(45,false)]
theorem der_76675 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76675 :=
  CNF.rup_sound cl_76675 [cl_50250,cl_64198] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50250 v h) (hints_cons _ _ _ (der_64198 v h) (by intro d hd; cases hd)))
def cl_76677 : CNF.NClause := [(94,true),(50,false),(35,false)]
theorem der_76677 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76677 :=
  CNF.rup_sound cl_76677 [cl_54924,cl_54971] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_54924 v h) (hints_cons _ _ _ (der_54971 v h) (by intro d hd; cases hd)))
def cl_76678 : CNF.NClause := [(108,true),(50,false),(47,false)]
theorem der_76678 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76678 :=
  CNF.rup_sound cl_76678 [cl_50265,cl_64302] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50265 v h) (hints_cons _ _ _ (der_64302 v h) (by intro d hd; cases hd)))
def cl_76679 : CNF.NClause := [(108,true),(49,false),(47,false)]
theorem der_76679 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76679 :=
  CNF.rup_sound cl_76679 [cl_50266,cl_64131] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50266 v h) (hints_cons _ _ _ (der_64131 v h) (by intro d hd; cases hd)))
def cl_76680 : CNF.NClause := [(108,true),(48,false),(47,false)]
theorem der_76680 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76680 :=
  CNF.rup_sound cl_76680 [cl_35584,cl_64219] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35584 v h) (hints_cons _ _ _ (der_64219 v h) (by intro d hd; cases hd)))
def cl_76681 : CNF.NClause := [(114,true),(35,false),(36,false)]
theorem der_76681 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76681 :=
  CNF.rup_sound cl_76681 [cl_50268,cl_37440] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50268 v h) (hints_cons _ _ _ (der_37440 v h) (by intro d hd; cases hd)))
def cl_76682 : CNF.NClause := [(100,true),(51,false),(33,false)]
theorem der_76682 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76682 :=
  CNF.rup_sound cl_76682 [cl_50270,cl_49843] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50270 v h) (hints_cons _ _ _ (der_49843 v h) (by intro d hd; cases hd)))
def cl_76683 : CNF.NClause := [(97,true),(37,false),(32,false)]
theorem der_76683 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76683 :=
  CNF.rup_sound cl_76683 [cl_54927,cl_55136] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_54927 v h) (hints_cons _ _ _ (der_55136 v h) (by intro d hd; cases hd)))
def cl_76684 : CNF.NClause := [(96,true),(39,false),(54,false)]
theorem der_76684 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76684 :=
  CNF.rup_sound cl_76684 [cl_35627,cl_76566] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35627 v h) (hints_cons _ _ _ (der_76566 v h) (by intro d hd; cases hd)))
def cl_76685 : CNF.NClause := [(96,true),(54,false),(44,false)]
theorem der_76685 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76685 :=
  CNF.rup_sound cl_76685 [cl_54929,cl_69034] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_54929 v h) (hints_cons _ _ _ (der_69034 v h) (by intro d hd; cases hd)))
def cl_76686 : CNF.NClause := [(49,false),(96,true),(44,false)]
theorem der_76686 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76686 :=
  CNF.rup_sound cl_76686 [cl_54931,cl_69034] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_54931 v h) (hints_cons _ _ _ (der_69034 v h) (by intro d hd; cases hd)))
def cl_76687 : CNF.NClause := [(96,true),(49,false),(39,false)]
theorem der_76687 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76687 :=
  CNF.rup_sound cl_76687 [cl_50272,cl_67115] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50272 v h) (hints_cons _ _ _ (der_67115 v h) (by intro d hd; cases hd)))
def cl_76688 : CNF.NClause := [(59,false),(48,false),(101,true)]
theorem der_76688 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76688 :=
  CNF.rup_sound cl_76688 [cl_50274,cl_49845] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50274 v h) (hints_cons _ _ _ (der_49845 v h) (by intro d hd; cases hd)))
def cl_76689 : CNF.NClause := [(59,false),(101,true),(37,false)]
theorem der_76689 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76689 :=
  CNF.rup_sound cl_76689 [cl_50275,cl_50033] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50275 v h) (hints_cons _ _ _ (der_50033 v h) (by intro d hd; cases hd)))
def cl_76690 : CNF.NClause := [(48,false),(51,false),(101,true)]
theorem der_76690 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76690 :=
  CNF.rup_sound cl_76690 [cl_50276,cl_50002] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50276 v h) (hints_cons _ _ _ (der_50002 v h) (by intro d hd; cases hd)))
def cl_76691 : CNF.NClause := [(101,true),(51,false),(37,false)]
theorem der_76691 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76691 :=
  CNF.rup_sound cl_76691 [cl_50277,cl_49845] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50277 v h) (hints_cons _ _ _ (der_49845 v h) (by intro d hd; cases hd)))
def cl_76692 : CNF.NClause := [(101,true),(37,false),(45,false)]
theorem der_76692 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76692 :=
  CNF.rup_sound cl_76692 [cl_50279,cl_49845] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50279 v h) (hints_cons _ _ _ (der_49845 v h) (by intro d hd; cases hd)))
def cl_76693 : CNF.NClause := [(106,true),(57,false),(47,false)]
theorem der_76693 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76693 :=
  CNF.rup_sound cl_76693 [cl_50280,cl_43027] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50280 v h) (hints_cons _ _ _ (der_43027 v h) (by intro d hd; cases hd)))
def cl_76694 : CNF.NClause := [(106,true),(57,false),(41,false)]
theorem der_76694 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76694 :=
  CNF.rup_sound cl_76694 [cl_50281,cl_76693] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50281 v h) (hints_cons _ _ _ (der_76693 v h) (by intro d hd; cases hd)))
def cl_76695 : CNF.NClause := [(106,true),(47,false),(53,false)]
theorem der_76695 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76695 :=
  CNF.rup_sound cl_76695 [cl_50283,cl_49905] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50283 v h) (hints_cons _ _ _ (der_49905 v h) (by intro d hd; cases hd)))
def cl_76696 : CNF.NClause := [(106,true),(41,false),(53,false)]
theorem der_76696 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76696 :=
  CNF.rup_sound cl_76696 [cl_50284,cl_50017] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50284 v h) (hints_cons _ _ _ (der_50017 v h) (by intro d hd; cases hd)))
def cl_76697 : CNF.NClause := [(111,true),(60,false),(55,false)]
theorem der_76697 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76697 :=
  CNF.rup_sound cl_76697 [cl_50286,cl_50063] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50286 v h) (hints_cons _ _ _ (der_50063 v h) (by intro d hd; cases hd)))
def cl_76698 : CNF.NClause := [(38,false),(111,true),(60,false)]
theorem der_76698 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76698 :=
  CNF.rup_sound cl_76698 [cl_50288,cl_49846] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50288 v h) (hints_cons _ _ _ (der_49846 v h) (by intro d hd; cases hd)))
def cl_76699 : CNF.NClause := [(42,false),(111,true),(55,false)]
theorem der_76699 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76699 :=
  CNF.rup_sound cl_76699 [cl_50290,cl_49846] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50290 v h) (hints_cons _ _ _ (der_49846 v h) (by intro d hd; cases hd)))
def cl_76700 : CNF.NClause := [(116,true),(36,false),(52,false)]
theorem der_76700 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76700 :=
  CNF.rup_sound cl_76700 [cl_35208,cl_49954] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35208 v h) (hints_cons _ _ _ (der_49954 v h) (by intro d hd; cases hd)))
def cl_76701 : CNF.NClause := [(116,true),(50,false),(58,false)]
theorem der_76701 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76701 :=
  CNF.rup_sound cl_76701 [cl_50293,cl_49847] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50293 v h) (hints_cons _ _ _ (der_49847 v h) (by intro d hd; cases hd)))
def cl_76702 : CNF.NClause := [(116,true),(50,false),(52,false)]
theorem der_76702 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76702 :=
  CNF.rup_sound cl_76702 [cl_35325,cl_71308] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35325 v h) (hints_cons _ _ _ (der_71308 v h) (by intro d hd; cases hd)))
def cl_76703 : CNF.NClause := [(116,true),(50,false),(36,false)]
theorem der_76703 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76703 :=
  CNF.rup_sound cl_76703 [cl_50295,cl_63674] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50295 v h) (hints_cons _ _ _ (der_63674 v h) (by intro d hd; cases hd)))
def cl_76704 : CNF.NClause := [(118,true),(35,false),(32,false)]
theorem der_76704 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76704 :=
  CNF.rup_sound cl_76704 [cl_50297,cl_64271] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50297 v h) (hints_cons _ _ _ (der_64271 v h) (by intro d hd; cases hd)))
def cl_76705 : CNF.NClause := [(108,true),(50,false),(46,false)]
theorem der_76705 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76705 :=
  CNF.rup_sound cl_76705 [cl_50300,cl_64131] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50300 v h) (hints_cons _ _ _ (der_64131 v h) (by intro d hd; cases hd)))
def cl_76706 : CNF.NClause := [(108,true),(46,false),(47,false)]
theorem der_76706 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76706 :=
  CNF.rup_sound cl_76706 [cl_64207,cl_64219] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_64207 v h) (hints_cons _ _ _ (der_64219 v h) (by intro d hd; cases hd)))
def cl_76707 : CNF.NClause := [(95,true),(38,false),(33,false)]
theorem der_76707 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76707 :=
  CNF.rup_sound cl_76707 [cl_50301,cl_55076] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50301 v h) (hints_cons _ _ _ (der_55076 v h) (by intro d hd; cases hd)))
def cl_76708 : CNF.NClause := [(116,true),(50,false),(34,false)]
theorem der_76708 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76708 :=
  CNF.rup_sound cl_76708 [cl_62165,cl_42810] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62165 v h) (hints_cons _ _ _ (der_42810 v h) (by intro d hd; cases hd)))
def cl_76709 : CNF.NClause := [(103,true),(41,false),(44,false)]
theorem der_76709 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76709 :=
  CNF.rup_sound cl_76709 [cl_53768,cl_64213] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_53768 v h) (hints_cons _ _ _ (der_64213 v h) (by intro d hd; cases hd)))
def cl_76710 : CNF.NClause := [(59,false),(112,true),(32,false)]
theorem der_76710 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76710 :=
  CNF.rup_sound cl_76710 [cl_50305,cl_49939] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50305 v h) (hints_cons _ _ _ (der_49939 v h) (by intro d hd; cases hd)))
def cl_76711 : CNF.NClause := [(95,true),(38,false),(53,false)]
theorem der_76711 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76711 :=
  CNF.rup_sound cl_76711 [cl_42910,cl_55115] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_42910 v h) (hints_cons _ _ _ (der_55115 v h) (by intro d hd; cases hd)))
def cl_76712 : CNF.NClause := [(43,false),(95,true),(53,false)]
theorem der_76712 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76712 :=
  CNF.rup_sound cl_76712 [cl_54934,cl_55114] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_54934 v h) (hints_cons _ _ _ (der_55114 v h) (by intro d hd; cases hd)))
def cl_76713 : CNF.NClause := [(95,true),(48,false),(38,false)]
theorem der_76713 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76713 :=
  CNF.rup_sound cl_76713 [cl_50309,cl_55115] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50309 v h) (hints_cons _ _ _ (der_55115 v h) (by intro d hd; cases hd)))
def cl_76714 : CNF.NClause := [(95,true),(38,false),(43,false)]
theorem der_76714 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76714 :=
  CNF.rup_sound cl_76714 [cl_54935,cl_63458] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_54935 v h) (hints_cons _ _ _ (der_63458 v h) (by intro d hd; cases hd)))
def cl_76715 : CNF.NClause := [(49,false),(100,true),(40,false)]
theorem der_76715 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76715 :=
  CNF.rup_sound cl_76715 [cl_50313,cl_49843] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50313 v h) (hints_cons _ _ _ (der_49843 v h) (by intro d hd; cases hd)))
def cl_76716 : CNF.NClause := [(105,true),(60,false),(37,false)]
theorem der_76716 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76716 :=
  CNF.rup_sound cl_76716 [cl_50317,cl_49984] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50317 v h) (hints_cons _ _ _ (der_49984 v h) (by intro d hd; cases hd)))
def cl_76717 : CNF.NClause := [(105,true),(50,false),(41,false)]
theorem der_76717 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76717 :=
  CNF.rup_sound cl_76717 [cl_37918,cl_49931] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_37918 v h) (hints_cons _ _ _ (der_49931 v h) (by intro d hd; cases hd)))
def cl_76718 : CNF.NClause := [(105,true),(50,false),(37,false)]
theorem der_76718 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76718 :=
  CNF.rup_sound cl_76718 [cl_50320,cl_49913] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50320 v h) (hints_cons _ _ _ (der_49913 v h) (by intro d hd; cases hd)))
def cl_76719 : CNF.NClause := [(110,true),(45,false),(57,false)]
theorem der_76719 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76719 :=
  CNF.rup_sound cl_76719 [cl_50323,cl_71720] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50323 v h) (hints_cons _ _ _ (der_71720 v h) (by intro d hd; cases hd)))
def cl_76720 : CNF.NClause := [(110,true),(39,false),(57,false)]
theorem der_76720 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76720 :=
  CNF.rup_sound cl_76720 [cl_50324,cl_64022] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50324 v h) (hints_cons _ _ _ (der_64022 v h) (by intro d hd; cases hd)))
def cl_76721 : CNF.NClause := [(110,true),(39,false),(46,false)]
theorem der_76721 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76721 :=
  CNF.rup_sound cl_76721 [cl_50325,cl_49930] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50325 v h) (hints_cons _ _ _ (der_49930 v h) (by intro d hd; cases hd)))
def cl_76722 : CNF.NClause := [(59,false),(115,true),(55,false)]
theorem der_76722 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76722 :=
  CNF.rup_sound cl_76722 [cl_50326,cl_58527] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50326 v h) (hints_cons _ _ _ (der_58527 v h) (by intro d hd; cases hd)))
def cl_76723 : CNF.NClause := [(115,true),(36,false),(44,false)]
theorem der_76723 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76723 :=
  CNF.rup_sound cl_76723 [cl_50329,cl_50055] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50329 v h) (hints_cons _ _ _ (der_50055 v h) (by intro d hd; cases hd)))
def cl_76724 : CNF.NClause := [(121,true),(50,false),(53,false)]
theorem der_76724 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76724 :=
  CNF.rup_sound cl_76724 [cl_64210,cl_64269] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_64210 v h) (hints_cons _ _ _ (der_64269 v h) (by intro d hd; cases hd)))
def cl_76725 : CNF.NClause := [(51,false),(101,true),(34,false)]
theorem der_76725 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76725 :=
  CNF.rup_sound cl_76725 [cl_50330,cl_69996] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50330 v h) (hints_cons _ _ _ (der_69996 v h) (by intro d hd; cases hd)))
def cl_76726 : CNF.NClause := [(110,true),(39,false),(52,false)]
theorem der_76726 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76726 :=
  CNF.rup_sound cl_76726 [cl_50331,cl_49894] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50331 v h) (hints_cons _ _ _ (der_49894 v h) (by intro d hd; cases hd)))
def cl_76727 : CNF.NClause := [(119,true),(60,false),(52,false)]
theorem der_76727 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76727 :=
  CNF.rup_sound cl_76727 [cl_35329,cl_64135] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35329 v h) (hints_cons _ _ _ (der_64135 v h) (by intro d hd; cases hd)))
def cl_76729 : CNF.NClause := [(42,false),(103,true),(45,false)]
theorem der_76729 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76729 :=
  CNF.rup_sound cl_76729 [cl_36476,cl_43523] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_36476 v h) (hints_cons _ _ _ (der_43523 v h) (by intro d hd; cases hd)))
def cl_76730 : CNF.NClause := [(103,true),(42,false),(43,false)]
theorem der_76730 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76730 :=
  CNF.rup_sound cl_76730 [cl_38433,cl_41521] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_38433 v h) (hints_cons _ _ _ (der_41521 v h) (by intro d hd; cases hd)))
def cl_76731 : CNF.NClause := [(103,true),(45,false),(43,false)]
theorem der_76731 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76731 :=
  CNF.rup_sound cl_76731 [cl_63464,cl_64460] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_63464 v h) (hints_cons _ _ _ (der_64460 v h) (by intro d hd; cases hd)))
def cl_76732 : CNF.NClause := [(39,false),(107,true),(32,false)]
theorem der_76732 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76732 :=
  CNF.rup_sound cl_76732 [cl_38002,cl_54086] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_38002 v h) (hints_cons _ _ _ (der_54086 v h) (by intro d hd; cases hd)))
def cl_76733 : CNF.NClause := [(105,true),(60,false),(33,false)]
theorem der_76733 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76733 :=
  CNF.rup_sound cl_76733 [cl_50332,cl_49855] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50332 v h) (hints_cons _ _ _ (der_49855 v h) (by intro d hd; cases hd)))
def cl_76734 : CNF.NClause := [(106,true),(53,false),(57,false)]
theorem der_76734 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76734 :=
  CNF.rup_sound cl_76734 [cl_50333,cl_49915] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50333 v h) (hints_cons _ _ _ (der_49915 v h) (by intro d hd; cases hd)))
def cl_76735 : CNF.NClause := [(57,false),(34,false),(106,true)]
theorem der_76735 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76735 :=
  CNF.rup_sound cl_76735 [cl_50334,cl_60657] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50334 v h) (hints_cons _ _ _ (der_60657 v h) (by intro d hd; cases hd)))
def cl_76736 : CNF.NClause := [(106,true),(40,false),(53,false)]
theorem der_76736 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76736 :=
  CNF.rup_sound cl_76736 [cl_42818,cl_49893] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_42818 v h) (hints_cons _ _ _ (der_49893 v h) (by intro d hd; cases hd)))
def cl_76737 : CNF.NClause := [(106,true),(53,false),(34,false)]
theorem der_76737 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76737 :=
  CNF.rup_sound cl_76737 [cl_50335,cl_50017] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50335 v h) (hints_cons _ _ _ (der_50017 v h) (by intro d hd; cases hd)))
def cl_76738 : CNF.NClause := [(106,true),(47,false),(34,false)]
theorem der_76738 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76738 :=
  CNF.rup_sound cl_76738 [cl_50337,cl_49856] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50337 v h) (hints_cons _ _ _ (der_49856 v h) (by intro d hd; cases hd)))
def cl_76739 : CNF.NClause := [(59,false),(35,false),(104,true)]
theorem der_76739 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76739 :=
  CNF.rup_sound cl_76739 [cl_50338,cl_42498] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50338 v h) (hints_cons _ _ _ (der_42498 v h) (by intro d hd; cases hd)))
def cl_76740 : CNF.NClause := [(94,true),(50,false),(45,false)]
theorem der_76740 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76740 :=
  CNF.rup_sound cl_76740 [cl_54938,cl_54940] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_54938 v h) (hints_cons _ _ _ (der_54940 v h) (by intro d hd; cases hd)))
def cl_76741 : CNF.NClause := [(99,true),(60,false),(43,false)]
theorem der_76741 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76741 :=
  CNF.rup_sound cl_76741 [cl_57196,cl_57209] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_57196 v h) (hints_cons _ _ _ (der_57209 v h) (by intro d hd; cases hd)))
def cl_76742 : CNF.NClause := [(99,true),(51,false),(43,false)]
theorem der_76742 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76742 :=
  CNF.rup_sound cl_76742 [cl_50340,cl_49857] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50340 v h) (hints_cons _ _ _ (der_49857 v h) (by intro d hd; cases hd)))
def cl_76743 : CNF.NClause := [(99,true),(39,false),(51,false)]
theorem der_76743 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76743 :=
  CNF.rup_sound cl_76743 [cl_50341,cl_76742] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50341 v h) (hints_cons _ _ _ (der_76742 v h) (by intro d hd; cases hd)))
def cl_76744 : CNF.NClause := [(59,false),(104,true),(52,false)]
theorem der_76744 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76744 :=
  CNF.rup_sound cl_76744 [cl_50342,cl_49912] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50342 v h) (hints_cons _ _ _ (der_49912 v h) (by intro d hd; cases hd)))
def cl_76745 : CNF.NClause := [(104,true),(49,false),(59,false)]
theorem der_76745 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76745 :=
  CNF.rup_sound cl_76745 [cl_50343,cl_42482] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50343 v h) (hints_cons _ _ _ (der_42482 v h) (by intro d hd; cases hd)))
def cl_76746 : CNF.NClause := [(104,true),(49,false),(38,false)]
theorem der_76746 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76746 :=
  CNF.rup_sound cl_76746 [cl_50346,cl_50022] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50346 v h) (hints_cons _ _ _ (der_50022 v h) (by intro d hd; cases hd)))
def cl_76747 : CNF.NClause := [(109,true),(58,false),(44,false)]
theorem der_76747 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76747 :=
  CNF.rup_sound cl_76747 [cl_50349,cl_61791] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50349 v h) (hints_cons _ _ _ (der_61791 v h) (by intro d hd; cases hd)))
def cl_76748 : CNF.NClause := [(109,true),(37,false),(58,false)]
theorem der_76748 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76748 :=
  CNF.rup_sound cl_76748 [cl_50350,cl_76747] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50350 v h) (hints_cons _ _ _ (der_76747 v h) (by intro d hd; cases hd)))
def cl_76749 : CNF.NClause := [(109,true),(44,false),(53,false)]
theorem der_76749 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76749 :=
  CNF.rup_sound cl_76749 [cl_50351,cl_35634] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50351 v h) (hints_cons _ _ _ (der_35634 v h) (by intro d hd; cases hd)))
def cl_76750 : CNF.NClause := [(109,true),(37,false),(53,false)]
theorem der_76750 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76750 :=
  CNF.rup_sound cl_76750 [cl_50352,cl_76749] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50352 v h) (hints_cons _ _ _ (der_76749 v h) (by intro d hd; cases hd)))
def cl_76751 : CNF.NClause := [(46,false),(109,true),(44,false)]
theorem der_76751 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76751 :=
  CNF.rup_sound cl_76751 [cl_50353,cl_44574] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50353 v h) (hints_cons _ _ _ (der_44574 v h) (by intro d hd; cases hd)))
def cl_76752 : CNF.NClause := [(109,true),(37,false),(44,false)]
theorem der_76752 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76752 :=
  CNF.rup_sound cl_76752 [cl_50354,cl_76749] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50354 v h) (hints_cons _ _ _ (der_76749 v h) (by intro d hd; cases hd)))
def cl_76753 : CNF.NClause := [(42,false),(114,true),(57,false)]
theorem der_76753 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76753 :=
  CNF.rup_sound cl_76753 [cl_50356,cl_49903] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50356 v h) (hints_cons _ _ _ (der_49903 v h) (by intro d hd; cases hd)))
def cl_76754 : CNF.NClause := [(114,true),(57,false),(36,false)]
theorem der_76754 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76754 :=
  CNF.rup_sound cl_76754 [cl_50357,cl_49903] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50357 v h) (hints_cons _ _ _ (der_49903 v h) (by intro d hd; cases hd)))
def cl_76755 : CNF.NClause := [(110,true),(33,false),(45,false)]
theorem der_76755 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76755 :=
  CNF.rup_sound cl_76755 [cl_50361,cl_49930] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50361 v h) (hints_cons _ _ _ (der_49930 v h) (by intro d hd; cases hd)))
def cl_76756 : CNF.NClause := [(98,true),(55,false),(52,false)]
theorem der_76756 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76756 :=
  CNF.rup_sound cl_76756 [cl_50367,cl_62910] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50367 v h) (hints_cons _ _ _ (der_62910 v h) (by intro d hd; cases hd)))
def cl_76757 : CNF.NClause := [(98,true),(54,false),(52,false)]
theorem der_76757 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76757 :=
  CNF.rup_sound cl_76757 [cl_50368,cl_62910] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50368 v h) (hints_cons _ _ _ (der_62910 v h) (by intro d hd; cases hd)))
def cl_76758 : CNF.NClause := [(42,false),(100,true),(33,false)]
theorem der_76758 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76758 :=
  CNF.rup_sound cl_76758 [cl_50370,cl_49934] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50370 v h) (hints_cons _ _ _ (der_49934 v h) (by intro d hd; cases hd)))
def cl_76759 : CNF.NClause := [(101,true),(37,false),(34,false)]
theorem der_76759 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76759 :=
  CNF.rup_sound cl_76759 [cl_50371,cl_42866] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50371 v h) (hints_cons _ _ _ (der_42866 v h) (by intro d hd; cases hd)))
def cl_76760 : CNF.NClause := [(94,true),(55,false),(45,false)]
theorem der_76760 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76760 :=
  CNF.rup_sound cl_76760 [cl_54941,cl_54940] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_54941 v h) (hints_cons _ _ _ (der_54940 v h) (by intro d hd; cases hd)))
def cl_76761 : CNF.NClause := [(94,true),(35,false),(55,false)]
theorem der_76761 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76761 :=
  CNF.rup_sound cl_76761 [cl_36383,cl_55045] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_36383 v h) (hints_cons _ _ _ (der_55045 v h) (by intro d hd; cases hd)))
def cl_76763 : CNF.NClause := [(119,true),(40,false),(60,false)]
theorem der_76763 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76763 :=
  CNF.rup_sound cl_76763 [cl_36075,cl_64135] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_36075 v h) (hints_cons _ _ _ (der_64135 v h) (by intro d hd; cases hd)))
def cl_76764 : CNF.NClause := [(119,true),(44,false),(60,false)]
theorem der_76764 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76764 :=
  CNF.rup_sound cl_76764 [cl_35719,cl_64358] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35719 v h) (hints_cons _ _ _ (der_64358 v h) (by intro d hd; cases hd)))
def cl_76765 : CNF.NClause := [(42,false),(97,true),(37,false)]
theorem der_76765 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76765 :=
  CNF.rup_sound cl_76765 [cl_54947,cl_54945] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_54947 v h) (hints_cons _ _ _ (der_54945 v h) (by intro d hd; cases hd)))
def cl_76766 : CNF.NClause := [(38,false),(51,false),(102,true)]
theorem der_76766 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76766 :=
  CNF.rup_sound cl_76766 [cl_42952,cl_62204] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_42952 v h) (hints_cons _ _ _ (der_62204 v h) (by intro d hd; cases hd)))
def cl_76767 : CNF.NClause := [(102,true),(51,false),(57,false)]
theorem der_76767 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76767 :=
  CNF.rup_sound cl_76767 [cl_67844,cl_76766] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_67844 v h) (hints_cons _ _ _ (der_76766 v h) (by intro d hd; cases hd)))
def cl_76768 : CNF.NClause := [(102,true),(50,false),(57,false)]
theorem der_76768 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76768 :=
  CNF.rup_sound cl_76768 [cl_66321,cl_62204] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_66321 v h) (hints_cons _ _ _ (der_62204 v h) (by intro d hd; cases hd)))
def cl_76769 : CNF.NClause := [(102,true),(50,false),(38,false)]
theorem der_76769 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76769 :=
  CNF.rup_sound cl_76769 [cl_50377,cl_66589] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50377 v h) (hints_cons _ _ _ (der_66589 v h) (by intro d hd; cases hd)))
def cl_76770 : CNF.NClause := [(102,true),(38,false),(44,false)]
theorem der_76770 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76770 :=
  CNF.rup_sound cl_76770 [cl_50378,cl_66589] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50378 v h) (hints_cons _ _ _ (der_66589 v h) (by intro d hd; cases hd)))
def cl_76771 : CNF.NClause := [(39,false),(107,true),(58,false)]
theorem der_76771 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76771 :=
  CNF.rup_sound cl_76771 [cl_34992,cl_38119] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34992 v h) (hints_cons _ _ _ (der_38119 v h) (by intro d hd; cases hd)))
def cl_76772 : CNF.NClause := [(107,true),(48,false),(55,false)]
theorem der_76772 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76772 :=
  CNF.rup_sound cl_76772 [cl_48712,cl_42515] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_48712 v h) (hints_cons _ _ _ (der_42515 v h) (by intro d hd; cases hd)))
def cl_76773 : CNF.NClause := [(107,true),(41,false),(55,false)]
theorem der_76773 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76773 :=
  CNF.rup_sound cl_76773 [cl_38559,cl_38119] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_38559 v h) (hints_cons _ _ _ (der_38119 v h) (by intro d hd; cases hd)))
def cl_76774 : CNF.NClause := [(59,false),(112,true),(43,false)]
theorem der_76774 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76774 :=
  CNF.rup_sound cl_76774 [cl_50381,cl_59167] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50381 v h) (hints_cons _ _ _ (der_59167 v h) (by intro d hd; cases hd)))
def cl_76775 : CNF.NClause := [(59,false),(112,true),(40,false)]
theorem der_76775 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76775 :=
  CNF.rup_sound cl_76775 [cl_50382,cl_49939] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50382 v h) (hints_cons _ _ _ (der_49939 v h) (by intro d hd; cases hd)))
def cl_76776 : CNF.NClause := [(112,true),(40,false),(43,false)]
theorem der_76776 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76776 :=
  CNF.rup_sound cl_76776 [cl_50383,cl_48333] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50383 v h) (hints_cons _ _ _ (der_48333 v h) (by intro d hd; cases hd)))
def cl_76777 : CNF.NClause := [(49,false),(117,true),(45,false)]
theorem der_76777 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76777 :=
  CNF.rup_sound cl_76777 [cl_50386,cl_50052] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50386 v h) (hints_cons _ _ _ (der_50052 v h) (by intro d hd; cases hd)))
def cl_76778 : CNF.NClause := [(117,true),(49,false),(36,false)]
theorem der_76778 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76778 :=
  CNF.rup_sound cl_76778 [cl_50387,cl_50052] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50387 v h) (hints_cons _ _ _ (der_50052 v h) (by intro d hd; cases hd)))
def cl_76779 : CNF.NClause := [(118,true),(35,false),(34,false)]
theorem der_76779 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76779 :=
  CNF.rup_sound cl_76779 [cl_64224,cl_64225] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_64224 v h) (hints_cons _ _ _ (der_64225 v h) (by intro d hd; cases hd)))
def cl_76780 : CNF.NClause := [(67,true),(24,false),(22,false)]
theorem der_76780 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76780 :=
  CNF.rup_sound cl_76780 [cl_29796,cl_49872] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29796 v h) (hints_cons _ _ _ (der_49872 v h) (by intro d hd; cases hd)))
def cl_76781 : CNF.NClause := [(26,false),(15,false),(79,true)]
theorem der_76781 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76781 :=
  CNF.rup_sound cl_76781 [cl_50388,cl_65781] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50388 v h) (hints_cons _ _ _ (der_65781 v h) (by intro d hd; cases hd)))
def cl_76783 : CNF.NClause := [(5,false),(86,true),(22,false)]
theorem der_76783 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76783 :=
  CNF.rup_sound cl_76783 [cl_50392,cl_49797] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50392 v h) (hints_cons _ _ _ (der_49797 v h) (by intro d hd; cases hd)))
def cl_76784 : CNF.NClause := [(79,true),(8,false),(15,false)]
theorem der_76784 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76784 :=
  CNF.rup_sound cl_76784 [cl_50393,cl_42466] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50393 v h) (hints_cons _ _ _ (der_42466 v h) (by intro d hd; cases hd)))
def cl_76785 : CNF.NClause := [(75,true),(16,false),(9,false)]
theorem der_76785 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76785 :=
  CNF.rup_sound cl_76785 [cl_50394,cl_49811] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50394 v h) (hints_cons _ _ _ (der_49811 v h) (by intro d hd; cases hd)))
def cl_76787 : CNF.NClause := [(4,false),(73,true),(28,false)]
theorem der_76787 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76787 :=
  CNF.rup_sound cl_76787 [cl_50397,cl_62641] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50397 v h) (hints_cons _ _ _ (der_62641 v h) (by intro d hd; cases hd)))
def cl_76788 : CNF.NClause := [(9,false),(81,true),(23,false)]
theorem der_76788 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76788 :=
  CNF.rup_sound cl_76788 [cl_50399,cl_76611] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50399 v h) (hints_cons _ _ _ (der_76611 v h) (by intro d hd; cases hd)))
def cl_76789 : CNF.NClause := [(115,true),(55,false),(44,false)]
theorem der_76789 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76789 :=
  CNF.rup_sound cl_76789 [cl_50402,cl_49880] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50402 v h) (hints_cons _ _ _ (der_49880 v h) (by intro d hd; cases hd)))
def cl_76791 : CNF.NClause := [(42,false),(121,true),(53,false)]
theorem der_76791 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76791 :=
  CNF.rup_sound cl_76791 [cl_50405,cl_64116] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50405 v h) (hints_cons _ _ _ (der_64116 v h) (by intro d hd; cases hd)))
def cl_76792 : CNF.NClause := [(117,true),(53,false),(36,false)]
theorem der_76792 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76792 :=
  CNF.rup_sound cl_76792 [cl_50406,cl_50052] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50406 v h) (hints_cons _ _ _ (der_50052 v h) (by intro d hd; cases hd)))
def cl_76793 : CNF.NClause := [(123,true),(46,false),(36,false)]
theorem der_76793 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76793 :=
  CNF.rup_sound cl_76793 [cl_54956,cl_55056] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_54956 v h) (hints_cons _ _ _ (der_55056 v h) (by intro d hd; cases hd)))
def cl_76794 : CNF.NClause := [(3,false),(20,false),(70,true)]
theorem der_76794 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76794 :=
  CNF.rup_sound cl_76794 [cl_50409,cl_54024] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50409 v h) (hints_cons _ _ _ (der_54024 v h) (by intro d hd; cases hd)))
def cl_76795 : CNF.NClause := [(20,false),(13,false),(71,true)]
theorem der_76795 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76795 :=
  CNF.rup_sound cl_76795 [cl_50410,cl_42582] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50410 v h) (hints_cons _ _ _ (der_42582 v h) (by intro d hd; cases hd)))
def cl_76796 : CNF.NClause := [(4,false),(6,false),(78,true)]
theorem der_76796 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76796 :=
  CNF.rup_sound cl_76796 [cl_50412,cl_76642] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50412 v h) (hints_cons _ _ _ (der_76642 v h) (by intro d hd; cases hd)))
def cl_76805 : CNF.NClause := [(15,false),(77,true),(914,false)]
theorem der_76805 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76805 :=
  CNF.rup_sound cl_76805 [cl_50426,cl_49764] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50426 v h) (hints_cons _ _ _ (der_49764 v h) (by intro d hd; cases hd)))
def cl_76806 : CNF.NClause := [(112,true),(32,false),(40,false)]
theorem der_76806 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76806 :=
  CNF.rup_sound cl_76806 [cl_50429,cl_69289] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50429 v h) (hints_cons _ _ _ (der_69289 v h) (by intro d hd; cases hd)))
def cl_76807 : CNF.NClause := [(35,false),(94,true),(45,false)]
theorem der_76807 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76807 :=
  CNF.rup_sound cl_76807 [cl_54973,cl_76761] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_54973 v h) (hints_cons _ _ _ (der_76761 v h) (by intro d hd; cases hd)))
def cl_76808 : CNF.NClause := [(116,true),(43,false),(36,false)]
theorem der_76808 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76808 :=
  CNF.rup_sound cl_76808 [cl_50431,cl_50035] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50431 v h) (hints_cons _ _ _ (der_50035 v h) (by intro d hd; cases hd)))
def cl_76812 : CNF.NClause := [(1060,false),(91,true),(6,false)]
theorem der_76812 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76812 :=
  CNF.rup_sound cl_76812 [cl_50440,cl_49794] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50440 v h) (hints_cons _ _ _ (der_49794 v h) (by intro d hd; cases hd)))
def cl_76817 : CNF.NClause := [(14,false),(89,true),(138,true)]
theorem der_76817 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76817 :=
  CNF.rup_sound cl_76817 [cl_50447,cl_37439] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50447 v h) (hints_cons _ _ _ (der_37439 v h) (by intro d hd; cases hd)))
def cl_76819 : CNF.NClause := [(97,true),(47,false),(32,false)]
theorem der_76819 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76819 :=
  CNF.rup_sound cl_76819 [cl_54990,cl_76658] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_54990 v h) (hints_cons _ _ _ (der_76658 v h) (by intro d hd; cases hd)))
def cl_76820 : CNF.NClause := [(48,false),(114,true),(35,false)]
theorem der_76820 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76820 :=
  CNF.rup_sound cl_76820 [cl_50452,cl_42767] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50452 v h) (hints_cons _ _ _ (der_42767 v h) (by intro d hd; cases hd)))
def cl_76824 : CNF.NClause := [(81,true),(1,false),(23,false)]
theorem der_76824 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76824 :=
  CNF.rup_sound cl_76824 [cl_50456,cl_50008] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50456 v h) (hints_cons _ _ _ (der_50008 v h) (by intro d hd; cases hd)))
def cl_76827 : CNF.NClause := [(1059,false),(12,true),(85,true)]
theorem der_76827 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76827 :=
  CNF.rup_sound cl_76827 [cl_50459,cl_15911] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50459 v h) (hints_cons _ _ _ (der_15911 v h) (by intro d hd; cases hd)))
def cl_76830 : CNF.NClause := [(113,true),(36,false),(37,false)]
theorem der_76830 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76830 :=
  CNF.rup_sound cl_76830 [cl_39346,cl_62857] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_39346 v h) (hints_cons _ _ _ (der_62857 v h) (by intro d hd; cases hd)))
def cl_76831 : CNF.NClause := [(112,true),(54,false),(32,false)]
theorem der_76831 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76831 :=
  CNF.rup_sound cl_76831 [cl_50463,cl_69289] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50463 v h) (hints_cons _ _ _ (der_69289 v h) (by intro d hd; cases hd)))
def cl_76832 : CNF.NClause := [(126,false),(64,true),(131,true)]
theorem der_76832 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76832 :=
  CNF.rup_sound cl_76832 [cl_50464,cl_15768] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50464 v h) (hints_cons _ _ _ (der_15768 v h) (by intro d hd; cases hd)))
def cl_76833 : CNF.NClause := [(116,true),(34,false),(36,false)]
theorem der_76833 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76833 :=
  CNF.rup_sound cl_76833 [cl_50465,cl_76808] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50465 v h) (hints_cons _ _ _ (der_76808 v h) (by intro d hd; cases hd)))
def cl_76836 : CNF.NClause := [(75,true),(10,false),(22,false)]
theorem der_76836 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76836 :=
  CNF.rup_sound cl_76836 [cl_50468,cl_40899] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50468 v h) (hints_cons _ _ _ (der_40899 v h) (by intro d hd; cases hd)))
def cl_76837 : CNF.NClause := [(908,false),(912,true),(88,true)]
theorem der_76837 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76837 :=
  CNF.rup_sound cl_76837 [cl_50470,cl_15875] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50470 v h) (hints_cons _ _ _ (der_15875 v h) (by intro d hd; cases hd)))
def cl_76838 : CNF.NClause := [(107,true),(58,false),(41,false)]
theorem der_76838 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76838 :=
  CNF.rup_sound cl_76838 [cl_38818,cl_38119] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_38818 v h) (hints_cons _ _ _ (der_38119 v h) (by intro d hd; cases hd)))
def cl_76840 : CNF.NClause := [(95,true),(53,false),(33,false)]
theorem der_76840 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76840 :=
  CNF.rup_sound cl_76840 [cl_55058,cl_63458] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_55058 v h) (hints_cons _ _ _ (der_63458 v h) (by intro d hd; cases hd)))
def cl_76841 : CNF.NClause := [(17,false),(70,true),(28,false)]
theorem der_76841 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76841 :=
  CNF.rup_sound cl_76841 [cl_62030,cl_54024] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62030 v h) (hints_cons _ _ _ (der_54024 v h) (by intro d hd; cases hd)))
def cl_76842 : CNF.NClause := [(23,false),(89,true),(147,true)]
theorem der_76842 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76842 :=
  CNF.rup_sound cl_76842 [cl_50473,cl_49761] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50473 v h) (hints_cons _ _ _ (der_49761 v h) (by intro d hd; cases hd)))
def cl_76846 : CNF.NClause := [(81,true),(1,false),(23,false)]
theorem der_76846 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76846 :=
  CNF.rup_sound cl_76846 [cl_50479,cl_76788] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50479 v h) (hints_cons _ _ _ (der_76788 v h) (by intro d hd; cases hd)))
def cl_76847 : CNF.NClause := [(27,false),(69,true),(11,false)]
theorem der_76847 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76847 :=
  CNF.rup_sound cl_76847 [cl_42647,cl_76613] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_42647 v h) (hints_cons _ _ _ (der_76613 v h) (by intro d hd; cases hd)))
def cl_76849 : CNF.NClause := [(64,true),(141,false),(17,false)]
theorem der_76849 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76849 :=
  CNF.rup_sound cl_76849 [cl_50482,cl_71136] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50482 v h) (hints_cons _ _ _ (der_71136 v h) (by intro d hd; cases hd)))
def cl_76850 : CNF.NClause := [(102,true),(51,false),(32,false)]
theorem der_76850 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76850 :=
  CNF.rup_sound cl_76850 [cl_42316,cl_76766] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_42316 v h) (hints_cons _ _ _ (der_76766 v h) (by intro d hd; cases hd)))
def cl_76852 : CNF.NClause := [(100,true),(51,false),(58,false)]
theorem der_76852 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76852 :=
  CNF.rup_sound cl_76852 [cl_50485,cl_49933] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50485 v h) (hints_cons _ _ _ (der_49933 v h) (by intro d hd; cases hd)))
def cl_76855 : CNF.NClause := [(97,true),(47,false),(52,false)]
theorem der_76855 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76855 :=
  CNF.rup_sound cl_76855 [cl_55123,cl_57663] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_55123 v h) (hints_cons _ _ _ (der_57663 v h) (by intro d hd; cases hd)))
def cl_76857 : CNF.NClause := [(4,false),(16,false),(68,true)]
theorem der_76857 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76857 :=
  CNF.rup_sound cl_76857 [cl_50497,cl_76637] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50497 v h) (hints_cons _ _ _ (der_76637 v h) (by intro d hd; cases hd)))
def cl_76864 : CNF.NClause := [(1067,false),(28,true),(84,true)]
theorem der_76864 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76864 :=
  CNF.rup_sound cl_76864 [cl_50508,cl_15919] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50508 v h) (hints_cons _ _ _ (der_15919 v h) (by intro d hd; cases hd)))
def cl_76865 : CNF.NClause := [(1068,false),(22,true),(86,true)]
theorem der_76865 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76865 :=
  CNF.rup_sound cl_76865 [cl_50509,cl_15920] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50509 v h) (hints_cons _ _ _ (der_15920 v h) (by intro d hd; cases hd)))
def cl_76866 : CNF.NClause := [(102,true),(51,false),(44,false)]
theorem der_76866 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76866 :=
  CNF.rup_sound cl_76866 [cl_45342,cl_76850] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_45342 v h) (hints_cons _ _ _ (der_76850 v h) (by intro d hd; cases hd)))
def cl_76867 : CNF.NClause := [(99,true),(47,false),(43,false)]
theorem der_76867 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76867 :=
  CNF.rup_sound cl_76867 [cl_50510,cl_49857] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50510 v h) (hints_cons _ _ _ (der_49857 v h) (by intro d hd; cases hd)))
def cl_76868 : CNF.NClause := [(579,false),(66,true),(14,true)]
theorem der_76868 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76868 :=
  CNF.rup_sound cl_76868 [cl_50511,cl_14206] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50511 v h) (hints_cons _ _ _ (inp_14206 v h) (by intro d hd; cases hd)))
def cl_76870 : CNF.NClause := [(20,false),(70,true),(28,false)]
theorem der_76870 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76870 :=
  CNF.rup_sound cl_76870 [cl_54640,cl_76580] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_54640 v h) (hints_cons _ _ _ (der_76580 v h) (by intro d hd; cases hd)))
def cl_76871 : CNF.NClause := [(70,true),(28,false),(152,false)]
theorem der_76871 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76871 :=
  CNF.rup_sound cl_76871 [cl_54846,cl_76841] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_54846 v h) (hints_cons _ _ _ (der_76841 v h) (by intro d hd; cases hd)))
def cl_76874 : CNF.NClause := [(29,false),(24,false),(80,true)]
theorem der_76874 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76874 :=
  CNF.rup_sound cl_76874 [cl_53756,cl_72305] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_53756 v h) (hints_cons _ _ _ (der_72305 v h) (by intro d hd; cases hd)))
def cl_76875 : CNF.NClause := [(133,false),(75,true),(150,true)]
theorem der_76875 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76875 :=
  CNF.rup_sound cl_76875 [cl_54647,cl_15775] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_54647 v h) (hints_cons _ _ _ (der_15775 v h) (by intro d hd; cases hd)))
def cl_76876 : CNF.NClause := [(1,false),(8,false),(76,true)]
theorem der_76876 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76876 :=
  CNF.rup_sound cl_76876 [cl_50535,cl_76592] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50535 v h) (hints_cons _ _ _ (der_76592 v h) (by intro d hd; cases hd)))
def cl_76877 : CNF.NClause := [(9,false),(69,true),(18,false)]
theorem der_76877 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76877 :=
  CNF.rup_sound cl_76877 [cl_54728,cl_54627] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_54728 v h) (hints_cons _ _ _ (der_54627 v h) (by intro d hd; cases hd)))
def cl_76879 : CNF.NClause := [(117,true),(60,false),(36,false)]
theorem der_76879 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76879 :=
  CNF.rup_sound cl_76879 [cl_50516,cl_49896] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50516 v h) (hints_cons _ _ _ (der_49896 v h) (by intro d hd; cases hd)))
def cl_76881 : CNF.NClause := [(107,true),(32,false),(55,false)]
theorem der_76881 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76881 :=
  CNF.rup_sound cl_76881 [cl_54764,cl_76732] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_54764 v h) (hints_cons _ _ _ (der_76732 v h) (by intro d hd; cases hd)))
def cl_76882 : CNF.NClause := [(103,true),(45,false),(44,false)]
theorem der_76882 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76882 :=
  CNF.rup_sound cl_76882 [cl_64332,cl_64459] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_64332 v h) (hints_cons _ _ _ (der_64459 v h) (by intro d hd; cases hd)))
def cl_76887 : CNF.NClause := [(48,false),(32,false),(107,true)]
theorem der_76887 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76887 :=
  CNF.rup_sound cl_76887 [cl_49471,cl_73143] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49471 v h) (hints_cons _ _ _ (der_73143 v h) (by intro d hd; cases hd)))
def cl_76888 : CNF.NClause := [(127,false),(75,true),(150,true)]
theorem der_76888 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76888 :=
  CNF.rup_sound cl_76888 [cl_54135,cl_62576] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_54135 v h) (hints_cons _ _ _ (der_62576 v h) (by intro d hd; cases hd)))
def cl_76889 : CNF.NClause := [(1,false),(71,true),(13,false)]
theorem der_76889 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76889 :=
  CNF.rup_sound cl_76889 [cl_54068,cl_61981] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_54068 v h) (hints_cons _ _ _ (der_61981 v h) (by intro d hd; cases hd)))
def cl_76890 : CNF.NClause := [(19,false),(6,false),(74,true)]
theorem der_76890 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76890 :=
  CNF.rup_sound cl_76890 [cl_49555,cl_63459] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49555 v h) (hints_cons _ _ _ (der_63459 v h) (by intro d hd; cases hd)))
def cl_76892 : CNF.NClause := [(12,false),(19,false),(85,true)]
theorem der_76892 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76892 :=
  CNF.rup_sound cl_76892 [cl_49138,cl_56362] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49138 v h) (hints_cons _ _ _ (der_56362 v h) (by intro d hd; cases hd)))
def cl_76893 : CNF.NClause := [(105,true),(50,false),(60,false)]
theorem der_76893 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76893 :=
  CNF.rup_sound cl_76893 [cl_54399,cl_49931] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_54399 v h) (hints_cons _ _ _ (der_49931 v h) (by intro d hd; cases hd)))
def cl_76895 : CNF.NClause := [(113,true),(39,false),(38,false)]
theorem der_76895 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76895 :=
  CNF.rup_sound cl_76895 [cl_64346,cl_64190] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_64346 v h) (hints_cons _ _ _ (der_64190 v h) (by intro d hd; cases hd)))
def cl_76898 : CNF.NClause := [(48,false),(114,true),(36,false)]
theorem der_76898 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76898 :=
  CNF.rup_sound cl_76898 [cl_48025,cl_76754] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_48025 v h) (hints_cons _ _ _ (der_76754 v h) (by intro d hd; cases hd)))
def cl_76899 : CNF.NClause := [(48,false),(114,true),(57,false)]
theorem der_76899 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76899 :=
  CNF.rup_sound cl_76899 [cl_49585,cl_76754] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49585 v h) (hints_cons _ _ _ (der_76754 v h) (by intro d hd; cases hd)))
def cl_76901 : CNF.NClause := [(21,false),(28,false),(73,true)]
theorem der_76901 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76901 :=
  CNF.rup_sound cl_76901 [cl_49691,cl_50172] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49691 v h) (hints_cons _ _ _ (der_50172 v h) (by intro d hd; cases hd)))
def cl_76902 : CNF.NClause := [(10,false),(73,true),(28,false)]
theorem der_76902 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76902 :=
  CNF.rup_sound cl_76902 [cl_54236,cl_76542] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_54236 v h) (hints_cons _ _ _ (der_76542 v h) (by intro d hd; cases hd)))
def cl_76904 : CNF.NClause := [(904,false),(926,true),(85,true)]
theorem der_76904 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76904 :=
  CNF.rup_sound cl_76904 [cl_50537,cl_15871] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50537 v h) (hints_cons _ _ _ (der_15871 v h) (by intro d hd; cases hd)))
def cl_76912 : CNF.NClause := [(72,true),(135,false),(137,true)]
theorem der_76912 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76912 :=
  CNF.rup_sound cl_76912 [cl_50514,cl_15777] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50514 v h) (hints_cons _ _ _ (der_15777 v h) (by intro d hd; cases hd)))
def cl_76915 : CNF.NClause := [(9,false),(69,true),(11,false)]
theorem der_76915 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76915 :=
  CNF.rup_sound cl_76915 [cl_49557,cl_56877] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49557 v h) (hints_cons _ _ _ (der_56877 v h) (by intro d hd; cases hd)))
def cl_76916 : CNF.NClause := [(27,false),(9,false),(69,true)]
theorem der_76916 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76916 :=
  CNF.rup_sound cl_76916 [cl_53736,cl_54627] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_53736 v h) (hints_cons _ _ _ (der_54627 v h) (by intro d hd; cases hd)))
def cl_76917 : CNF.NClause := [(119,true),(44,false),(40,false)]
theorem der_76917 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76917 :=
  CNF.rup_sound cl_76917 [cl_49590,cl_64223] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49590 v h) (hints_cons _ _ _ (der_64223 v h) (by intro d hd; cases hd)))
def cl_76918 : CNF.NClause := [(102,true),(32,false),(44,false)]
theorem der_76918 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76918 :=
  CNF.rup_sound cl_76918 [cl_49198,cl_76866] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49198 v h) (hints_cons _ _ _ (der_76866 v h) (by intro d hd; cases hd)))
def cl_76920 : CNF.NClause := [(1076,false),(1073,true),(90,true)]
theorem der_76920 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76920 :=
  CNF.rup_sound cl_76920 [cl_50539,cl_15928] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50539 v h) (hints_cons _ _ _ (der_15928 v h) (by intro d hd; cases hd)))
def cl_76922 : CNF.NClause := [(117,true),(60,false),(45,false)]
theorem der_76922 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76922 :=
  CNF.rup_sound cl_76922 [cl_49632,cl_50052] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49632 v h) (hints_cons _ _ _ (der_50052 v h) (by intro d hd; cases hd)))
def cl_76923 : CNF.NClause := [(94,true),(40,false),(55,false)]
theorem der_76923 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76923 :=
  CNF.rup_sound cl_76923 [cl_54573,cl_68523] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_54573 v h) (hints_cons _ _ _ (der_68523 v h) (by intro d hd; cases hd)))
def cl_76925 : CNF.NClause := [(134,false),(7,true),(73,true)]
theorem der_76925 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76925 :=
  CNF.rup_sound cl_76925 [cl_59301,cl_76526] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_59301 v h) (hints_cons _ _ _ (der_76526 v h) (by intro d hd; cases hd)))
def cl_76926 : CNF.NClause := [(76,true),(151,false),(148,true)]
theorem der_76926 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76926 :=
  CNF.rup_sound cl_76926 [cl_56852,cl_65746] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_56852 v h) (hints_cons _ _ _ (der_65746 v h) (by intro d hd; cases hd)))
def cl_76929 : CNF.NClause := [(6,false),(78,true),(22,false)]
theorem der_76929 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76929 :=
  CNF.rup_sound cl_76929 [cl_57843,cl_76642] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_57843 v h) (hints_cons _ _ _ (der_76642 v h) (by intro d hd; cases hd)))
def cl_76930 : CNF.NClause := [(13,false),(22,false),(78,true)]
theorem der_76930 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76930 :=
  CNF.rup_sound cl_76930 [cl_57850,cl_76642] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_57850 v h) (hints_cons _ _ _ (der_76642 v h) (by intro d hd; cases hd)))
def cl_76931 : CNF.NClause := [(145,false),(7,true),(73,true)]
theorem der_76931 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76931 :=
  CNF.rup_sound cl_76931 [cl_56860,cl_62171] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_56860 v h) (hints_cons _ _ _ (der_62171 v h) (by intro d hd; cases hd)))
def cl_76935 : CNF.NClause := [(12,false),(21,false),(85,true)]
theorem der_76935 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76935 :=
  CNF.rup_sound cl_76935 [cl_56560,cl_60483] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_56560 v h) (hints_cons _ _ _ (der_60483 v h) (by intro d hd; cases hd)))
def cl_76940 : CNF.NClause := [(82,true),(133,false),(131,true)]
theorem der_76940 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76940 :=
  CNF.rup_sound cl_76940 [cl_57267,cl_62455] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_57267 v h) (hints_cons _ _ _ (der_62455 v h) (by intro d hd; cases hd)))
def cl_76942 : CNF.NClause := [(27,false),(13,false),(78,true)]
theorem der_76942 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76942 :=
  CNF.rup_sound cl_76942 [cl_57854,cl_43213] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_57854 v h) (hints_cons _ _ _ (der_43213 v h) (by intro d hd; cases hd)))
def cl_76944 : CNF.NClause := [(96,true),(49,false),(34,false)]
theorem der_76944 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76944 :=
  CNF.rup_sound cl_76944 [cl_57879,cl_54928] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_57879 v h) (hints_cons _ _ _ (der_54928 v h) (by intro d hd; cases hd)))
def cl_76949 : CNF.NClause := [(4,true),(137,false),(78,true)]
theorem der_76949 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76949 :=
  CNF.rup_sound cl_76949 [cl_57865,cl_15770] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_57865 v h) (hints_cons _ _ _ (der_15770 v h) (by intro d hd; cases hd)))
def cl_76952 : CNF.NClause := [(63,true),(143,false),(138,true)]
theorem der_76952 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76952 :=
  CNF.rup_sound cl_76952 [cl_57498,cl_62565] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_57498 v h) (hints_cons _ _ _ (der_62565 v h) (by intro d hd; cases hd)))
def cl_76959 : CNF.NClause := [(7,false),(29,false),(80,true)]
theorem der_76959 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76959 :=
  CNF.rup_sound cl_76959 [cl_63372,cl_62338] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_63372 v h) (hints_cons _ _ _ (der_62338 v h) (by intro d hd; cases hd)))
def cl_76960 : CNF.NClause := [(4,false),(23,false),(83,true)]
theorem der_76960 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76960 :=
  CNF.rup_sound cl_76960 [cl_63594,cl_62292] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_63594 v h) (hints_cons _ _ _ (der_62292 v h) (by intro d hd; cases hd)))
def cl_76961 : CNF.NClause := [(81,true),(28,false),(23,false)]
theorem der_76961 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76961 :=
  CNF.rup_sound cl_76961 [cl_61627,cl_76846] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_61627 v h) (hints_cons _ _ _ (der_76846 v h) (by intro d hd; cases hd)))
def cl_76963 : CNF.NClause := [(13,false),(4,false),(78,true)]
theorem der_76963 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76963 :=
  CNF.rup_sound cl_76963 [cl_61545,cl_76796] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_61545 v h) (hints_cons _ _ _ (der_76796 v h) (by intro d hd; cases hd)))
def cl_76964 : CNF.NClause := [(21,false),(3,false),(85,true)]
theorem der_76964 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76964 :=
  CNF.rup_sound cl_76964 [cl_61344,cl_60483] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_61344 v h) (hints_cons _ _ _ (der_60483 v h) (by intro d hd; cases hd)))
def cl_76965 : CNF.NClause := [(64,true),(136,false),(126,true)]
theorem der_76965 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76965 :=
  CNF.rup_sound cl_76965 [cl_62139,cl_71136] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62139 v h) (hints_cons _ _ _ (der_71136 v h) (by intro d hd; cases hd)))
def cl_76968 : CNF.NClause := [(207,true),(21,false),(79,true)]
theorem der_76968 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76968 :=
  CNF.rup_sound cl_76968 [cl_60540,cl_76569] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_60540 v h) (hints_cons _ _ _ (der_76569 v h) (by intro d hd; cases hd)))
def cl_76969 : CNF.NClause := [(62,true),(150,false),(152,true)]
theorem der_76969 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76969 :=
  CNF.rup_sound cl_76969 [cl_60729,cl_15791] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_60729 v h) (hints_cons _ _ _ (der_15791 v h) (by intro d hd; cases hd)))
def cl_76971 : CNF.NClause := [(210,true),(24,false),(84,true)]
theorem der_76971 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76971 :=
  CNF.rup_sound cl_76971 [cl_63714,cl_76583] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_63714 v h) (hints_cons _ _ _ (der_76583 v h) (by intro d hd; cases hd)))
def cl_76973 : CNF.NClause := [(94,true),(50,false),(55,false)]
theorem der_76973 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76973 :=
  CNF.rup_sound cl_76973 [cl_62747,cl_57585] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62747 v h) (hints_cons _ _ _ (der_57585 v h) (by intro d hd; cases hd)))
def cl_76975 : CNF.NClause := [(102,true),(57,false),(32,false)]
theorem der_76975 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76975 :=
  CNF.rup_sound cl_76975 [cl_64065,cl_76568] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_64065 v h) (hints_cons _ _ _ (der_76568 v h) (by intro d hd; cases hd)))
def cl_76977 : CNF.NClause := [(71,true),(19,false),(7,false)]
theorem der_76977 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76977 :=
  CNF.rup_sound cl_76977 [cl_61933,cl_76588] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_61933 v h) (hints_cons _ _ _ (der_76588 v h) (by intro d hd; cases hd)))
def cl_76978 : CNF.NClause := [(83,true),(128,false),(17,true)]
theorem der_76978 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76978 :=
  CNF.rup_sound cl_76978 [cl_62234,cl_63963] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62234 v h) (hints_cons _ _ _ (der_63963 v h) (by intro d hd; cases hd)))
def cl_76981 : CNF.NClause := [(15,false),(9,false),(81,true)]
theorem der_76981 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76981 :=
  CNF.rup_sound cl_76981 [cl_60478,cl_76543] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_60478 v h) (hints_cons _ _ _ (der_76543 v h) (by intro d hd; cases hd)))
def cl_76982 : CNF.NClause := [(7,false),(80,true),(15,false)]
theorem der_76982 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76982 :=
  CNF.rup_sound cl_76982 [cl_61117,cl_43611] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_61117 v h) (hints_cons _ _ _ (der_43611 v h) (by intro d hd; cases hd)))
def cl_76983 : CNF.NClause := [(83,true),(128,false),(26,true)]
theorem der_76983 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76983 :=
  CNF.rup_sound cl_76983 [cl_62357,cl_76978] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62357 v h) (hints_cons _ _ _ (der_76978 v h) (by intro d hd; cases hd)))
def cl_76985 : CNF.NClause := [(148,false),(80,true),(7,true)]
theorem der_76985 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76985 :=
  CNF.rup_sound cl_76985 [cl_60950,cl_15790] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_60950 v h) (hints_cons _ _ _ (der_15790 v h) (by intro d hd; cases hd)))
def cl_76988 : CNF.NClause := [(9,false),(81,true),(28,false)]
theorem der_76988 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76988 :=
  CNF.rup_sound cl_76988 [cl_61226,cl_61656] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_61226 v h) (hints_cons _ _ _ (der_61656 v h) (by intro d hd; cases hd)))
def cl_76991 : CNF.NClause := [(21,false),(79,true),(67,true)]
theorem der_76991 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76991 :=
  CNF.rup_sound cl_76991 [cl_62098,cl_76607] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62098 v h) (hints_cons _ _ _ (der_76607 v h) (by intro d hd; cases hd)))
def cl_76994 : CNF.NClause := [(103,true),(41,false),(45,false)]
theorem der_76994 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76994 :=
  CNF.rup_sound cl_76994 [cl_65113,cl_41521] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_65113 v h) (hints_cons _ _ _ (der_41521 v h) (by intro d hd; cases hd)))
def cl_76996 : CNF.NClause := [(160,true),(86,true),(5,false)]
theorem der_76996 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76996 :=
  CNF.rup_sound cl_76996 [cl_60599,cl_49797] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_60599 v h) (hints_cons _ _ _ (der_49797 v h) (by intro d hd; cases hd)))
def cl_76998 : CNF.NClause := [(94,true),(50,false),(40,false)]
theorem der_76998 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76998 :=
  CNF.rup_sound cl_76998 [cl_61489,cl_54940] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_61489 v h) (hints_cons _ _ _ (der_54940 v h) (by intro d hd; cases hd)))
def cl_76999 : CNF.NClause := [(73,true),(142,false),(7,true)]
theorem der_76999 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_76999 :=
  CNF.rup_sound cl_76999 [cl_66607,cl_15784] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_66607 v h) (hints_cons _ _ _ (der_15784 v h) (by intro d hd; cases hd)))
def cl_77000 : CNF.NClause := [(70,true),(144,false),(141,true)]
theorem der_77000 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77000 :=
  CNF.rup_sound cl_77000 [cl_68324,cl_69297] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_68324 v h) (hints_cons _ _ _ (der_69297 v h) (by intro d hd; cases hd)))
def cl_77003 : CNF.NClause := [(83,true),(150,false),(11,true)]
theorem der_77003 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77003 :=
  CNF.rup_sound cl_77003 [cl_68541,cl_63585] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_68541 v h) (hints_cons _ _ _ (der_63585 v h) (by intro d hd; cases hd)))
def cl_77007 : CNF.NClause := [(241,false),(3,true),(63,true)]
theorem der_77007 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77007 :=
  CNF.rup_sound cl_77007 [cl_66828,cl_13879] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_66828 v h) (hints_cons _ _ _ (inp_13879 v h) (by intro d hd; cases hd)))
def cl_77008 : CNF.NClause := [(68,true),(136,false),(140,true)]
theorem der_77008 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77008 :=
  CNF.rup_sound cl_77008 [cl_68045,cl_61595] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_68045 v h) (hints_cons _ _ _ (der_61595 v h) (by intro d hd; cases hd)))
def cl_77009 : CNF.NClause := [(9,false),(133,false),(81,true)]
theorem der_77009 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77009 :=
  CNF.rup_sound cl_77009 [cl_65773,cl_76981] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_65773 v h) (hints_cons _ _ _ (der_76981 v h) (by intro d hd; cases hd)))
def cl_77011 : CNF.NClause := [(71,true),(131,false),(19,true)]
theorem der_77011 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77011 :=
  CNF.rup_sound cl_77011 [cl_72255,cl_66628] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_72255 v h) (hints_cons _ _ _ (der_66628 v h) (by intro d hd; cases hd)))
def cl_77014 : CNF.NClause := [(472,true),(7,false),(80,true)]
theorem der_77014 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77014 :=
  CNF.rup_sound cl_77014 [cl_71080,cl_76615] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_71080 v h) (hints_cons _ _ _ (der_76615 v h) (by intro d hd; cases hd)))
def cl_77015 : CNF.NClause := [(65,true),(13,false),(71,true)]
theorem der_77015 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77015 :=
  CNF.rup_sound cl_77015 [cl_74706,cl_76889] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_74706 v h) (hints_cons _ _ _ (der_76889 v h) (by intro d hd; cases hd)))
def cl_77016 : CNF.NClause := [(38,false),(113,true),(36,false)]
theorem der_77016 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77016 :=
  CNF.rup_sound cl_77016 [cl_72689,cl_76661] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_72689 v h) (hints_cons _ _ _ (der_76661 v h) (by intro d hd; cases hd)))
def cl_77020 : CNF.NClause := [(67,true),(148,false),(22,true)]
theorem der_77020 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77020 :=
  CNF.rup_sound cl_77020 [cl_76420,cl_63071] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_76420 v h) (hints_cons _ _ _ (der_63071 v h) (by intro d hd; cases hd)))
def cl_77021 : CNF.NClause := [(6,false),(10,false),(74,true),(19,true)]
theorem der_77021 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77021 :=
  CNF.rup_sound cl_77021 [cl_50554,cl_42426] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50554 v h) (hints_cons _ _ _ (der_42426 v h) (by intro d hd; cases hd)))
def cl_77025 : CNF.NClause := [(47,false),(16,true),(66,false),(68,true)]
theorem der_77025 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77025 :=
  CNF.rup_sound cl_77025 [cl_50567,cl_50566] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50567 v h) (hints_cons _ _ _ (der_50566 v h) (by intro d hd; cases hd)))
def cl_77028 : CNF.NClause := [(9,false),(20,false),(11,true),(69,true)]
theorem der_77028 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77028 :=
  CNF.rup_sound cl_77028 [cl_50573,cl_76877] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50573 v h) (hints_cons _ _ _ (der_76877 v h) (by intro d hd; cases hd)))
def cl_77029 : CNF.NClause := [(20,false),(69,true),(27,true),(11,false)]
theorem der_77029 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77029 :=
  CNF.rup_sound cl_77029 [cl_50574,cl_56878] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50574 v h) (hints_cons _ _ _ (der_56878 v h) (by intro d hd; cases hd)))
def cl_77030 : CNF.NClause := [(52,false),(67,true),(66,false),(21,true)]
theorem der_77030 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77030 :=
  CNF.rup_sound cl_77030 [cl_50595,cl_50591] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50595 v h) (hints_cons _ _ _ (der_50591 v h) (by intro d hd; cases hd)))
def cl_77031 : CNF.NClause := [(39,false),(65,false),(76,false),(68,true)]
theorem der_77031 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77031 :=
  CNF.rup_sound cl_77031 [cl_56335,cl_60245] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_56335 v h) (hints_cons _ _ _ (der_60245 v h) (by intro d hd; cases hd)))
def cl_77032 : CNF.NClause := [(39,false),(79,false),(90,false),(8,true)]
theorem der_77032 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77032 :=
  CNF.rup_sound cl_77032 [cl_50601,cl_50599] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50601 v h) (hints_cons _ _ _ (der_50599 v h) (by intro d hd; cases hd)))
def cl_77033 : CNF.NClause := [(39,false),(8,true),(65,false),(76,false)]
theorem der_77033 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77033 :=
  CNF.rup_sound cl_77033 [cl_50603,cl_60238] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50603 v h) (hints_cons _ _ _ (der_60238 v h) (by intro d hd; cases hd)))
def cl_77034 : CNF.NClause := [(39,false),(90,false),(8,true),(68,false)]
theorem der_77034 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77034 :=
  CNF.rup_sound cl_77034 [cl_50605,cl_77032] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50605 v h) (hints_cons _ _ _ (der_77032 v h) (by intro d hd; cases hd)))
def cl_77036 : CNF.NClause := [(39,false),(82,true),(8,true),(90,false)]
theorem der_77036 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77036 :=
  CNF.rup_sound cl_77036 [cl_50608,cl_77034] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50608 v h) (hints_cons _ _ _ (der_77034 v h) (by intro d hd; cases hd)))
def cl_77037 : CNF.NClause := [(39,false),(65,false),(79,true),(76,false)]
theorem der_77037 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77037 :=
  CNF.rup_sound cl_77037 [cl_50612,cl_60245] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50612 v h) (hints_cons _ _ _ (der_60245 v h) (by intro d hd; cases hd)))
def cl_77039 : CNF.NClause := [(39,false),(90,true),(65,false),(79,false)]
theorem der_77039 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77039 :=
  CNF.rup_sound cl_77039 [cl_50620,cl_61568] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50620 v h) (hints_cons _ _ _ (der_61568 v h) (by intro d hd; cases hd)))
def cl_77041 : CNF.NClause := [(39,false),(8,true),(65,false),(68,false)]
theorem der_77041 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77041 :=
  CNF.rup_sound cl_77041 [cl_50629,cl_56337] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50629 v h) (hints_cons _ _ _ (der_56337 v h) (by intro d hd; cases hd)))
def cl_77042 : CNF.NClause := [(39,false),(8,false),(79,true),(65,false)]
theorem der_77042 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77042 :=
  CNF.rup_sound cl_77042 [cl_50631,cl_77037] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50631 v h) (hints_cons _ _ _ (der_77037 v h) (by intro d hd; cases hd)))
def cl_77043 : CNF.NClause := [(37,false),(66,true),(70,false),(91,false)]
theorem der_77043 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77043 :=
  CNF.rup_sound cl_77043 [cl_50645,cl_50642] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50645 v h) (hints_cons _ _ _ (der_50642 v h) (by intro d hd; cases hd)))
def cl_77044 : CNF.NClause := [(70,true),(37,false),(91,false),(66,false)]
theorem der_77044 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77044 :=
  CNF.rup_sound cl_77044 [cl_50646,cl_50639] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50646 v h) (hints_cons _ _ _ (der_50639 v h) (by intro d hd; cases hd)))
def cl_77045 : CNF.NClause := [(37,false),(78,false),(70,false),(82,true)]
theorem der_77045 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77045 :=
  CNF.rup_sound cl_77045 [cl_50663,cl_50662] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50663 v h) (hints_cons _ _ _ (der_50662 v h) (by intro d hd; cases hd)))
def cl_77046 : CNF.NClause := [(37,false),(82,true),(78,false),(91,true)]
theorem der_77046 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77046 :=
  CNF.rup_sound cl_77046 [cl_50667,cl_50666] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50667 v h) (hints_cons _ _ _ (der_50666 v h) (by intro d hd; cases hd)))
def cl_77047 : CNF.NClause := [(37,false),(66,true),(70,false),(74,false)]
theorem der_77047 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77047 :=
  CNF.rup_sound cl_77047 [cl_50668,cl_50549] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50668 v h) (hints_cons _ _ _ (der_50549 v h) (by intro d hd; cases hd)))
def cl_77048 : CNF.NClause := [(37,false),(66,true),(82,true),(70,false)]
theorem der_77048 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77048 :=
  CNF.rup_sound cl_77048 [cl_50671,cl_77047] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50671 v h) (hints_cons _ _ _ (der_77047 v h) (by intro d hd; cases hd)))
def cl_77050 : CNF.NClause := [(36,false),(86,false),(85,true),(83,true)]
theorem der_77050 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77050 :=
  CNF.rup_sound cl_77050 [cl_50689,cl_50688] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50689 v h) (hints_cons _ _ _ (der_50688 v h) (by intro d hd; cases hd)))
def cl_77051 : CNF.NClause := [(36,false),(5,true),(85,false),(82,false)]
theorem der_77051 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77051 :=
  CNF.rup_sound cl_77051 [cl_50695,cl_50691] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50695 v h) (hints_cons _ _ _ (der_50691 v h) (by intro d hd; cases hd)))
def cl_77053 : CNF.NClause := [(57,false),(79,false),(26,true),(62,true)]
theorem der_77053 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77053 :=
  CNF.rup_sound cl_77053 [cl_50709,cl_50708] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50709 v h) (hints_cons _ _ _ (der_50708 v h) (by intro d hd; cases hd)))
def cl_77055 : CNF.NClause := [(22,true),(64,false),(53,false),(67,false)]
theorem der_77055 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77055 :=
  CNF.rup_sound cl_77055 [cl_50724,cl_50721] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50724 v h) (hints_cons _ _ _ (der_50721 v h) (by intro d hd; cases hd)))
def cl_77056 : CNF.NClause := [(40,false),(9,true),(82,false),(69,false)]
theorem der_77056 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77056 :=
  CNF.rup_sound cl_77056 [cl_50729,cl_56340] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50729 v h) (hints_cons _ _ _ (der_56340 v h) (by intro d hd; cases hd)))
def cl_77057 : CNF.NClause := [(45,false),(70,true),(14,true),(63,false)]
theorem der_77057 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77057 :=
  CNF.rup_sound cl_77057 [cl_50738,cl_50736] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50738 v h) (hints_cons _ _ _ (der_50736 v h) (by intro d hd; cases hd)))
def cl_77058 : CNF.NClause := [(58,false),(27,true),(85,false),(89,false)]
theorem der_77058 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77058 :=
  CNF.rup_sound cl_77058 [cl_62006,cl_62008] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_62006 v h) (hints_cons _ _ _ (der_62008 v h) (by intro d hd; cases hd)))
def cl_77059 : CNF.NClause := [(58,false),(89,false),(76,false),(85,true)]
theorem der_77059 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77059 :=
  CNF.rup_sound cl_77059 [cl_54045,cl_54044] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_54045 v h) (hints_cons _ _ _ (der_54044 v h) (by intro d hd; cases hd)))
def cl_77061 : CNF.NClause := [(58,false),(62,false),(27,true),(69,false)]
theorem der_77061 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77061 :=
  CNF.rup_sound cl_77061 [cl_50767,cl_62008] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50767 v h) (hints_cons _ _ _ (der_62008 v h) (by intro d hd; cases hd)))
def cl_77063 : CNF.NClause := [(54,false),(23,false),(81,false),(74,true)]
theorem der_77063 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77063 :=
  CNF.rup_sound cl_77063 [cl_50782,cl_57003] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50782 v h) (hints_cons _ _ _ (der_57003 v h) (by intro d hd; cases hd)))
def cl_77064 : CNF.NClause := [(54,false),(81,true),(65,true),(23,false)]
theorem der_77064 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77064 :=
  CNF.rup_sound cl_77064 [cl_50788,cl_56354] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50788 v h) (hints_cons _ _ _ (der_56354 v h) (by intro d hd; cases hd)))
def cl_77065 : CNF.NClause := [(54,false),(23,false),(67,true),(81,false)]
theorem der_77065 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77065 :=
  CNF.rup_sound cl_77065 [cl_50791,cl_77063] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50791 v h) (hints_cons _ _ _ (der_77063 v h) (by intro d hd; cases hd)))
def cl_77066 : CNF.NClause := [(54,false),(65,true),(67,true),(81,false)]
theorem der_77066 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77066 :=
  CNF.rup_sound cl_77066 [cl_50798,cl_77065] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50798 v h) (hints_cons _ _ _ (der_77065 v h) (by intro d hd; cases hd)))
def cl_77069 : CNF.NClause := [(40,false),(75,true),(81,false),(88,false)]
theorem der_77069 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77069 :=
  CNF.rup_sound cl_77069 [cl_50831,cl_50829] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50831 v h) (hints_cons _ _ _ (der_50829 v h) (by intro d hd; cases hd)))
def cl_77070 : CNF.NClause := [(40,false),(75,true),(88,false),(69,false)]
theorem der_77070 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77070 :=
  CNF.rup_sound cl_77070 [cl_50836,cl_50835] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50836 v h) (hints_cons _ _ _ (der_50835 v h) (by intro d hd; cases hd)))
def cl_77072 : CNF.NClause := [(40,false),(75,true),(9,false),(88,false)]
theorem der_77072 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77072 :=
  CNF.rup_sound cl_77072 [cl_50838,cl_77070] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50838 v h) (hints_cons _ _ _ (der_77070 v h) (by intro d hd; cases hd)))
def cl_77073 : CNF.NClause := [(40,false),(82,true),(88,false),(75,true)]
theorem der_77073 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77073 :=
  CNF.rup_sound cl_77073 [cl_50839,cl_77070] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50839 v h) (hints_cons _ _ _ (der_77070 v h) (by intro d hd; cases hd)))
def cl_77074 : CNF.NClause := [(40,false),(81,true),(82,false),(69,false)]
theorem der_77074 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77074 :=
  CNF.rup_sound cl_77074 [cl_50846,cl_56340] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50846 v h) (hints_cons _ _ _ (der_56340 v h) (by intro d hd; cases hd)))
def cl_77075 : CNF.NClause := [(40,false),(69,true),(63,false),(82,false)]
theorem der_77075 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77075 :=
  CNF.rup_sound cl_77075 [cl_50848,cl_50841] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50848 v h) (hints_cons _ _ _ (der_50841 v h) (by intro d hd; cases hd)))
def cl_77076 : CNF.NClause := [(40,false),(9,false),(82,false),(81,true)]
theorem der_77076 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77076 :=
  CNF.rup_sound cl_77076 [cl_50849,cl_77074] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50849 v h) (hints_cons _ _ _ (der_77074 v h) (by intro d hd; cases hd)))
def cl_77077 : CNF.NClause := [(40,false),(75,true),(81,true),(82,false)]
theorem der_77077 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77077 :=
  CNF.rup_sound cl_77077 [cl_50850,cl_77074] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50850 v h) (hints_cons _ _ _ (der_77074 v h) (by intro d hd; cases hd)))
def cl_77078 : CNF.NClause := [(40,false),(69,true),(81,false),(75,false)]
theorem der_77078 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77078 :=
  CNF.rup_sound cl_77078 [cl_50854,cl_50840] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50854 v h) (hints_cons _ _ _ (der_50840 v h) (by intro d hd; cases hd)))
def cl_77080 : CNF.NClause := [(40,false),(69,true),(9,true),(75,false)]
theorem der_77080 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77080 :=
  CNF.rup_sound cl_77080 [cl_50858,cl_77078] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50858 v h) (hints_cons _ _ _ (der_77078 v h) (by intro d hd; cases hd)))
def cl_77081 : CNF.NClause := [(40,false),(81,true),(63,false),(69,true)]
theorem der_77081 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77081 :=
  CNF.rup_sound cl_77081 [cl_50860,cl_77075] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50860 v h) (hints_cons _ _ _ (der_77075 v h) (by intro d hd; cases hd)))
def cl_77082 : CNF.NClause := [(55,false),(91,false),(63,false),(76,true)]
theorem der_77082 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77082 :=
  CNF.rup_sound cl_77082 [cl_50877,cl_50870] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50877 v h) (hints_cons _ _ _ (der_50870 v h) (by intro d hd; cases hd)))
def cl_77083 : CNF.NClause := [(55,false),(24,true),(80,false),(84,false)]
theorem der_77083 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77083 :=
  CNF.rup_sound cl_77083 [cl_50881,cl_50879] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50881 v h) (hints_cons _ _ _ (der_50879 v h) (by intro d hd; cases hd)))
def cl_77084 : CNF.NClause := [(55,false),(24,true),(63,false),(76,true)]
theorem der_77084 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77084 :=
  CNF.rup_sound cl_77084 [cl_50897,cl_77082] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50897 v h) (hints_cons _ _ _ (der_77082 v h) (by intro d hd; cases hd)))
def cl_77086 : CNF.NClause := [(42,false),(66,true),(83,false),(69,false)]
theorem der_77086 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77086 :=
  CNF.rup_sound cl_77086 [cl_50942,cl_50938] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50942 v h) (hints_cons _ _ _ (der_50938 v h) (by intro d hd; cases hd)))
def cl_77092 : CNF.NClause := [(34,false),(85,true),(80,false),(75,false)]
theorem der_77092 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77092 :=
  CNF.rup_sound cl_77092 [cl_50980,cl_74082] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50980 v h) (hints_cons _ _ _ (der_74082 v h) (by intro d hd; cases hd)))
def cl_77093 : CNF.NClause := [(34,false),(80,true),(75,false),(3,false)]
theorem der_77093 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77093 :=
  CNF.rup_sound cl_77093 [cl_50988,cl_50987] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_50988 v h) (hints_cons _ _ _ (der_50987 v h) (by intro d hd; cases hd)))
def cl_77098 : CNF.NClause := [(43,false),(72,false),(64,true),(91,false)]
theorem der_77098 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77098 :=
  CNF.rup_sound cl_77098 [cl_51045,cl_51043] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51045 v h) (hints_cons _ _ _ (der_51043 v h) (by intro d hd; cases hd)))
def cl_77099 : CNF.NClause := [(43,false),(12,false),(72,true),(64,false)]
theorem der_77099 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77099 :=
  CNF.rup_sound cl_77099 [cl_51047,cl_62741] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51047 v h) (hints_cons _ _ _ (der_62741 v h) (by intro d hd; cases hd)))
def cl_77102 : CNF.NClause := [(43,false),(64,true),(68,false),(85,false)]
theorem der_77102 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77102 :=
  CNF.rup_sound cl_77102 [cl_51062,cl_51051] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51062 v h) (hints_cons _ _ _ (der_51051 v h) (by intro d hd; cases hd)))
def cl_77104 : CNF.NClause := [(91,true),(43,false),(64,true),(85,false)]
theorem der_77104 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77104 :=
  CNF.rup_sound cl_77104 [cl_51066,cl_77102] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51066 v h) (hints_cons _ _ _ (der_77102 v h) (by intro d hd; cases hd)))
def cl_77105 : CNF.NClause := [(43,false),(64,true),(81,false),(72,false)]
theorem der_77105 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77105 :=
  CNF.rup_sound cl_77105 [cl_51069,cl_51068] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51069 v h) (hints_cons _ _ _ (der_51068 v h) (by intro d hd; cases hd)))
def cl_77108 : CNF.NClause := [(68,true),(72,false),(43,false),(64,true)]
theorem der_77108 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77108 :=
  CNF.rup_sound cl_77108 [cl_51076,cl_77105] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51076 v h) (hints_cons _ _ _ (der_77105 v h) (by intro d hd; cases hd)))
def cl_77109 : CNF.NClause := [(43,false),(68,false),(12,true),(64,true)]
theorem der_77109 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77109 :=
  CNF.rup_sound cl_77109 [cl_51079,cl_60853] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51079 v h) (hints_cons _ _ _ (der_60853 v h) (by intro d hd; cases hd)))
def cl_77111 : CNF.NClause := [(33,false),(87,false),(84,false),(74,true)]
theorem der_77111 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77111 :=
  CNF.rup_sound cl_77111 [cl_51086,cl_50545] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51086 v h) (hints_cons _ _ _ (der_50545 v h) (by intro d hd; cases hd)))
def cl_77112 : CNF.NClause := [(33,false),(87,false),(74,true),(79,false)]
theorem der_77112 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77112 :=
  CNF.rup_sound cl_77112 [cl_45654,cl_50544] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_45654 v h) (hints_cons _ _ _ (der_50544 v h) (by intro d hd; cases hd)))
def cl_77113 : CNF.NClause := [(33,false),(2,false),(87,false),(64,true)]
theorem der_77113 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77113 :=
  CNF.rup_sound cl_77113 [cl_51094,cl_51089] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51094 v h) (hints_cons _ _ _ (der_51089 v h) (by intro d hd; cases hd)))
def cl_77114 : CNF.NClause := [(33,false),(2,false),(87,false),(79,true)]
theorem der_77114 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77114 :=
  CNF.rup_sound cl_77114 [cl_51095,cl_77113] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51095 v h) (hints_cons _ _ _ (der_77113 v h) (by intro d hd; cases hd)))
def cl_77116 : CNF.NClause := [(33,false),(69,true),(84,false),(79,false)]
theorem der_77116 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77116 :=
  CNF.rup_sound cl_77116 [cl_51099,cl_50545] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51099 v h) (hints_cons _ _ _ (der_50545 v h) (by intro d hd; cases hd)))
def cl_77117 : CNF.NClause := [(33,false),(74,true),(84,false),(79,false)]
theorem der_77117 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77117 :=
  CNF.rup_sound cl_77117 [cl_51100,cl_50545] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51100 v h) (hints_cons _ _ _ (der_50545 v h) (by intro d hd; cases hd)))
def cl_77118 : CNF.NClause := [(33,false),(69,true),(84,false),(79,true)]
theorem der_77118 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77118 :=
  CNF.rup_sound cl_77118 [cl_51108,cl_50545] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51108 v h) (hints_cons _ _ _ (der_50545 v h) (by intro d hd; cases hd)))
def cl_77119 : CNF.NClause := [(33,false),(74,true),(84,false),(64,true)]
theorem der_77119 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77119 :=
  CNF.rup_sound cl_77119 [cl_51111,cl_77117] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51111 v h) (hints_cons _ _ _ (der_77117 v h) (by intro d hd; cases hd)))
def cl_77120 : CNF.NClause := [(33,false),(2,false),(69,true),(64,false)]
theorem der_77120 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77120 :=
  CNF.rup_sound cl_77120 [cl_51113,cl_49995] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51113 v h) (hints_cons _ _ _ (der_49995 v h) (by intro d hd; cases hd)))
def cl_77122 : CNF.NClause := [(33,false),(87,true),(79,false),(69,true)]
theorem der_77122 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77122 :=
  CNF.rup_sound cl_77122 [cl_51116,cl_77116] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51116 v h) (hints_cons _ _ _ (der_77116 v h) (by intro d hd; cases hd)))
def cl_77124 : CNF.NClause := [(33,false),(74,true),(69,true),(64,false)]
theorem der_77124 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77124 :=
  CNF.rup_sound cl_77124 [cl_51119,cl_50545] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51119 v h) (hints_cons _ _ _ (der_50545 v h) (by intro d hd; cases hd)))
def cl_77125 : CNF.NClause := [(33,false),(79,true),(74,false),(64,false)]
theorem der_77125 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77125 :=
  CNF.rup_sound cl_77125 [cl_51122,cl_50546] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51122 v h) (hints_cons _ _ _ (der_50546 v h) (by intro d hd; cases hd)))
def cl_77127 : CNF.NClause := [(33,false),(79,true),(74,false),(69,true)]
theorem der_77127 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77127 :=
  CNF.rup_sound cl_77127 [cl_51125,cl_50546] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51125 v h) (hints_cons _ _ _ (der_50546 v h) (by intro d hd; cases hd)))
def cl_77131 : CNF.NClause := [(33,false),(74,true),(79,true),(69,true)]
theorem der_77131 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77131 :=
  CNF.rup_sound cl_77131 [cl_51129,cl_77118] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51129 v h) (hints_cons _ _ _ (der_77118 v h) (by intro d hd; cases hd)))
def cl_77132 : CNF.NClause := [(38,false),(71,false),(89,false),(73,true)]
theorem der_77132 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77132 :=
  CNF.rup_sound cl_77132 [cl_51137,cl_51136] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51137 v h) (hints_cons _ _ _ (der_51136 v h) (by intro d hd; cases hd)))
def cl_77133 : CNF.NClause := [(38,false),(80,false),(82,false),(64,true)]
theorem der_77133 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77133 :=
  CNF.rup_sound cl_77133 [cl_51142,cl_51141] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51142 v h) (hints_cons _ _ _ (der_51141 v h) (by intro d hd; cases hd)))
def cl_77134 : CNF.NClause := [(38,false),(7,false),(64,true),(82,false)]
theorem der_77134 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77134 :=
  CNF.rup_sound cl_77134 [cl_51148,cl_51131] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51148 v h) (hints_cons _ _ _ (der_51131 v h) (by intro d hd; cases hd)))
def cl_77135 : CNF.NClause := [(38,false),(82,false),(64,true),(73,true)]
theorem der_77135 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77135 :=
  CNF.rup_sound cl_77135 [cl_51149,cl_77134] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51149 v h) (hints_cons _ _ _ (der_77134 v h) (by intro d hd; cases hd)))
def cl_77136 : CNF.NClause := [(38,false),(7,false),(73,true),(64,true)]
theorem der_77136 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77136 :=
  CNF.rup_sound cl_77136 [cl_51156,cl_77134] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51156 v h) (hints_cons _ _ _ (der_77134 v h) (by intro d hd; cases hd)))
def cl_77137 : CNF.NClause := [(59,false),(90,false),(81,false),(70,true)]
theorem der_77137 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77137 :=
  CNF.rup_sound cl_77137 [cl_51165,cl_51163] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51165 v h) (hints_cons _ _ _ (der_51163 v h) (by intro d hd; cases hd)))
def cl_77138 : CNF.NClause := [(59,false),(70,true),(90,false),(73,false)]
theorem der_77138 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77138 :=
  CNF.rup_sound cl_77138 [cl_51169,cl_51167] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51169 v h) (hints_cons _ _ _ (der_51167 v h) (by intro d hd; cases hd)))
def cl_77139 : CNF.NClause := [(59,false),(70,true),(90,false),(62,false)]
theorem der_77139 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77139 :=
  CNF.rup_sound cl_77139 [cl_51173,cl_51167] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51173 v h) (hints_cons _ _ _ (der_51167 v h) (by intro d hd; cases hd)))
def cl_77141 : CNF.NClause := [(81,true),(70,true),(90,false),(59,false)]
theorem der_77141 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77141 :=
  CNF.rup_sound cl_77141 [cl_51175,cl_77138] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51175 v h) (hints_cons _ _ _ (der_77138 v h) (by intro d hd; cases hd)))
def cl_77142 : CNF.NClause := [(59,false),(70,true),(62,false),(81,false)]
theorem der_77142 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77142 :=
  CNF.rup_sound cl_77142 [cl_51193,cl_51188] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51193 v h) (hints_cons _ _ _ (der_51188 v h) (by intro d hd; cases hd)))
def cl_77143 : CNF.NClause := [(59,false),(70,false),(73,false),(28,true)]
theorem der_77143 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77143 :=
  CNF.rup_sound cl_77143 [cl_51194,cl_51166] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51194 v h) (hints_cons _ _ _ (der_51166 v h) (by intro d hd; cases hd)))
def cl_77151 : CNF.NClause := [(41,false),(74,true),(76,false),(75,false)]
theorem der_77151 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77151 :=
  CNF.rup_sound cl_77151 [cl_51237,cl_51236] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51237 v h) (hints_cons _ _ _ (der_51236 v h) (by intro d hd; cases hd)))
def cl_77152 : CNF.NClause := [(41,false),(76,false),(74,true),(10,false)]
theorem der_77152 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77152 :=
  CNF.rup_sound cl_77152 [cl_51245,cl_77151] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51245 v h) (hints_cons _ _ _ (der_77151 v h) (by intro d hd; cases hd)))
def cl_77153 : CNF.NClause := [(72,true),(41,false),(75,false),(73,false)]
theorem der_77153 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77153 :=
  CNF.rup_sound cl_77153 [cl_51246,cl_62349] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51246 v h) (hints_cons _ _ _ (der_62349 v h) (by intro d hd; cases hd)))
def cl_77154 : CNF.NClause := [(41,false),(72,true),(74,false),(75,false)]
theorem der_77154 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77154 :=
  CNF.rup_sound cl_77154 [cl_51249,cl_51248] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51249 v h) (hints_cons _ _ _ (der_51248 v h) (by intro d hd; cases hd)))
def cl_77155 : CNF.NClause := [(72,true),(41,false),(10,true),(75,false)]
theorem der_77155 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77155 :=
  CNF.rup_sound cl_77155 [cl_51256,cl_77153] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51256 v h) (hints_cons _ _ _ (der_77153 v h) (by intro d hd; cases hd)))
def cl_77156 : CNF.NClause := [(41,false),(72,true),(73,false),(10,false)]
theorem der_77156 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77156 :=
  CNF.rup_sound cl_77156 [cl_51264,cl_51258] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51264 v h) (hints_cons _ _ _ (der_51258 v h) (by intro d hd; cases hd)))
def cl_77157 : CNF.NClause := [(35,false),(63,true),(87,false),(83,false)]
theorem der_77157 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77157 :=
  CNF.rup_sound cl_77157 [cl_51276,cl_51275] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51276 v h) (hints_cons _ _ _ (der_51275 v h) (by intro d hd; cases hd)))
def cl_77158 : CNF.NClause := [(35,false),(87,false),(78,false),(73,true)]
theorem der_77158 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77158 :=
  CNF.rup_sound cl_77158 [cl_51280,cl_51277] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51280 v h) (hints_cons _ _ _ (der_51277 v h) (by intro d hd; cases hd)))
def cl_77159 : CNF.NClause := [(35,false),(87,false),(68,false),(78,true)]
theorem der_77159 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77159 :=
  CNF.rup_sound cl_77159 [cl_51287,cl_51286] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51287 v h) (hints_cons _ _ _ (der_51286 v h) (by intro d hd; cases hd)))
def cl_77161 : CNF.NClause := [(35,false),(73,true),(78,false),(68,false)]
theorem der_77161 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77161 :=
  CNF.rup_sound cl_77161 [cl_51303,cl_51302] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51303 v h) (hints_cons _ _ _ (der_51302 v h) (by intro d hd; cases hd)))
def cl_77163 : CNF.NClause := [(35,false),(63,true),(73,false),(4,false)]
theorem der_77163 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77163 :=
  CNF.rup_sound cl_77163 [cl_51308,cl_51283] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51308 v h) (hints_cons _ _ _ (der_51283 v h) (by intro d hd; cases hd)))
def cl_77164 : CNF.NClause := [(35,false),(63,true),(78,true),(73,false)]
theorem der_77164 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77164 :=
  CNF.rup_sound cl_77164 [cl_51309,cl_51284] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51309 v h) (hints_cons _ _ _ (der_51284 v h) (by intro d hd; cases hd)))
def cl_77167 : CNF.NClause := [(57,false),(62,true),(91,false),(79,false)]
theorem der_77167 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77167 :=
  CNF.rup_sound cl_77167 [cl_51330,cl_51327] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51330 v h) (hints_cons _ _ _ (der_51327 v h) (by intro d hd; cases hd)))
def cl_77168 : CNF.NClause := [(57,false),(91,false),(75,false),(71,true)]
theorem der_77168 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77168 :=
  CNF.rup_sound cl_77168 [cl_51334,cl_51333] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51334 v h) (hints_cons _ _ _ (der_51333 v h) (by intro d hd; cases hd)))
def cl_77170 : CNF.NClause := [(57,false),(91,false),(62,false),(71,true)]
theorem der_77170 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77170 :=
  CNF.rup_sound cl_77170 [cl_51338,cl_51337] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51338 v h) (hints_cons _ _ _ (der_51337 v h) (by intro d hd; cases hd)))
def cl_77172 : CNF.NClause := [(57,false),(62,true),(83,false),(71,false)]
theorem der_77172 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77172 :=
  CNF.rup_sound cl_77172 [cl_51348,cl_51341] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51348 v h) (hints_cons _ _ _ (der_51341 v h) (by intro d hd; cases hd)))
def cl_77173 : CNF.NClause := [(57,false),(71,true),(62,false),(83,false)]
theorem der_77173 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77173 :=
  CNF.rup_sound cl_77173 [cl_51350,cl_51345] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51350 v h) (hints_cons _ _ _ (der_51345 v h) (by intro d hd; cases hd)))
def cl_77177 : CNF.NClause := [(57,false),(83,true),(79,false),(26,true)]
theorem der_77177 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77177 :=
  CNF.rup_sound cl_77177 [cl_51359,cl_51353] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51359 v h) (hints_cons _ _ _ (der_51353 v h) (by intro d hd; cases hd)))
def cl_77178 : CNF.NClause := [(57,false),(62,true),(79,false),(71,false)]
theorem der_77178 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77178 :=
  CNF.rup_sound cl_77178 [cl_51360,cl_77053] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51360 v h) (hints_cons _ _ _ (der_77053 v h) (by intro d hd; cases hd)))
def cl_77182 : CNF.NClause := [(57,false),(71,true),(62,false),(75,false)]
theorem der_77182 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77182 :=
  CNF.rup_sound cl_77182 [cl_51365,cl_77173] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51365 v h) (hints_cons _ _ _ (der_77173 v h) (by intro d hd; cases hd)))
def cl_77184 : CNF.NClause := [(57,false),(62,true),(71,false),(91,true)]
theorem der_77184 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77184 :=
  CNF.rup_sound cl_77184 [cl_51368,cl_77178] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51368 v h) (hints_cons _ _ _ (der_77178 v h) (by intro d hd; cases hd)))
def cl_77189 : CNF.NClause := [(51,false),(92,false),(68,false),(69,true)]
theorem der_77189 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77189 :=
  CNF.rup_sound cl_77189 [cl_51386,cl_51385] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51386 v h) (hints_cons _ _ _ (der_51385 v h) (by intro d hd; cases hd)))
def cl_77191 : CNF.NClause := [(51,false),(20,false),(71,false),(67,true)]
theorem der_77191 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77191 :=
  CNF.rup_sound cl_77191 [cl_51396,cl_51395] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51396 v h) (hints_cons _ _ _ (der_51395 v h) (by intro d hd; cases hd)))
def cl_77192 : CNF.NClause := [(51,false),(68,true),(71,false),(67,true)]
theorem der_77192 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77192 :=
  CNF.rup_sound cl_77192 [cl_51397,cl_77191] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51397 v h) (hints_cons _ _ _ (der_77191 v h) (by intro d hd; cases hd)))
def cl_77195 : CNF.NClause := [(51,false),(20,false),(67,false),(69,true)]
theorem der_77195 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77195 :=
  CNF.rup_sound cl_77195 [cl_51412,cl_51403] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51412 v h) (hints_cons _ _ _ (der_51403 v h) (by intro d hd; cases hd)))
def cl_77196 : CNF.NClause := [(50,false),(77,false),(90,false),(71,true)]
theorem der_77196 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77196 :=
  CNF.rup_sound cl_77196 [cl_51424,cl_51423] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51424 v h) (hints_cons _ _ _ (der_51423 v h) (by intro d hd; cases hd)))
def cl_77198 : CNF.NClause := [(50,false),(74,true),(90,false),(63,false)]
theorem der_77198 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77198 :=
  CNF.rup_sound cl_77198 [cl_51432,cl_51428] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51432 v h) (hints_cons _ _ _ (der_51428 v h) (by intro d hd; cases hd)))
def cl_77199 : CNF.NClause := [(50,false),(77,true),(90,false),(74,true)]
theorem der_77199 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77199 :=
  CNF.rup_sound cl_77199 [cl_51434,cl_77198] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51434 v h) (hints_cons _ _ _ (der_77198 v h) (by intro d hd; cases hd)))
def cl_77201 : CNF.NClause := [(50,false),(77,false),(74,false),(71,true)]
theorem der_77201 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77201 :=
  CNF.rup_sound cl_77201 [cl_51449,cl_51448] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51449 v h) (hints_cons _ _ _ (der_51448 v h) (by intro d hd; cases hd)))
def cl_77202 : CNF.NClause := [(50,false),(77,false),(71,false),(74,true)]
theorem der_77202 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77202 :=
  CNF.rup_sound cl_77202 [cl_51452,cl_51451] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51452 v h) (hints_cons _ _ _ (der_51451 v h) (by intro d hd; cases hd)))
def cl_77204 : CNF.NClause := [(50,false),(74,false),(71,true),(19,false)]
theorem der_77204 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77204 :=
  CNF.rup_sound cl_77204 [cl_51458,cl_51426] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51458 v h) (hints_cons _ _ _ (der_51426 v h) (by intro d hd; cases hd)))
def cl_77205 : CNF.NClause := [(50,false),(63,true),(71,true),(74,false)]
theorem der_77205 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77205 :=
  CNF.rup_sound cl_77205 [cl_51459,cl_77204] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51459 v h) (hints_cons _ _ _ (der_77204 v h) (by intro d hd; cases hd)))
def cl_77206 : CNF.NClause := [(50,false),(71,false),(85,true),(74,true)]
theorem der_77206 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77206 :=
  CNF.rup_sound cl_77206 [cl_51462,cl_77202] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51462 v h) (hints_cons _ _ _ (der_77202 v h) (by intro d hd; cases hd)))
def cl_77216 : CNF.NClause := [(32,false),(81,false),(86,false),(1,true)]
theorem der_77216 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77216 :=
  CNF.rup_sound cl_77216 [cl_51484,cl_51483] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51484 v h) (hints_cons _ _ _ (der_51483 v h) (by intro d hd; cases hd)))
def cl_77217 : CNF.NClause := [(32,false),(66,true),(81,false),(76,false)]
theorem der_77217 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77217 :=
  CNF.rup_sound cl_77217 [cl_51490,cl_51489] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51490 v h) (hints_cons _ _ _ (der_51489 v h) (by intro d hd; cases hd)))
def cl_77226 : CNF.NClause := [(29,false),(20,false),(68,true),(8,true)]
theorem der_77226 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77226 :=
  CNF.rup_sound cl_77226 [cl_30147,cl_76570] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30147 v h) (hints_cons _ _ _ (der_76570 v h) (by intro d hd; cases hd)))
def cl_77228 : CNF.NClause := [(1,false),(24,false),(8,true),(76,true)]
theorem der_77228 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77228 :=
  CNF.rup_sound cl_77228 [cl_30154,cl_63467] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30154 v h) (hints_cons _ _ _ (der_63467 v h) (by intro d hd; cases hd)))
def cl_77236 : CNF.NClause := [(21,true),(3,false),(27,false),(85,true)]
theorem der_77236 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77236 :=
  CNF.rup_sound cl_77236 [cl_30219,cl_54252] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30219 v h) (hints_cons _ _ _ (der_54252 v h) (by intro d hd; cases hd)))
def cl_77237 : CNF.NClause := [(12,false),(21,false),(85,true),(5,true)]
theorem der_77237 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77237 :=
  CNF.rup_sound cl_77237 [cl_51526,cl_76892] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51526 v h) (hints_cons _ _ _ (der_76892 v h) (by intro d hd; cases hd)))
def cl_77238 : CNF.NClause := [(17,false),(23,false),(11,true),(83,true)]
theorem der_77238 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77238 :=
  CNF.rup_sound cl_77238 [cl_51527,cl_54211] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51527 v h) (hints_cons _ _ _ (der_54211 v h) (by intro d hd; cases hd)))
def cl_77239 : CNF.NClause := [(83,true),(26,false),(11,false),(5,true)]
theorem der_77239 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77239 :=
  CNF.rup_sound cl_77239 [cl_30246,cl_54213] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30246 v h) (hints_cons _ _ _ (der_54213 v h) (by intro d hd; cases hd)))
def cl_77240 : CNF.NClause := [(83,true),(23,false),(5,true),(11,false)]
theorem der_77240 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77240 :=
  CNF.rup_sound cl_77240 [cl_30248,cl_76586] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30248 v h) (hints_cons _ _ _ (der_76586 v h) (by intro d hd; cases hd)))
def cl_77242 : CNF.NClause := [(1,false),(7,true),(13,false),(71,true)]
theorem der_77242 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77242 :=
  CNF.rup_sound cl_77242 [cl_51532,cl_61646] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51532 v h) (hints_cons _ _ _ (der_61646 v h) (by intro d hd; cases hd)))
def cl_77243 : CNF.NClause := [(4,false),(16,false),(68,true),(29,true)]
theorem der_77243 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77243 :=
  CNF.rup_sound cl_77243 [cl_51534,cl_42497] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51534 v h) (hints_cons _ _ _ (der_42497 v h) (by intro d hd; cases hd)))
def cl_77248 : CNF.NClause := [(12,false),(81,true),(15,true),(23,false)]
theorem der_77248 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77248 :=
  CNF.rup_sound cl_77248 [cl_51540,cl_49533] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51540 v h) (hints_cons _ _ _ (der_49533 v h) (by intro d hd; cases hd)))
def cl_77250 : CNF.NClause := [(15,false),(9,false),(81,true),(12,true)]
theorem der_77250 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77250 :=
  CNF.rup_sound cl_77250 [cl_51542,cl_76543] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51542 v h) (hints_cons _ _ _ (der_76543 v h) (by intro d hd; cases hd)))
def cl_77251 : CNF.NClause := [(24,false),(80,true),(7,true),(11,false)]
theorem der_77251 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77251 :=
  CNF.rup_sound cl_77251 [cl_30415,cl_62000] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30415 v h) (hints_cons _ _ _ (der_62000 v h) (by intro d hd; cases hd)))
def cl_77253 : CNF.NClause := [(5,false),(26,false),(11,true),(83,true)]
theorem der_77253 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77253 :=
  CNF.rup_sound cl_77253 [cl_30424,cl_61589] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30424 v h) (hints_cons _ _ _ (der_61589 v h) (by intro d hd; cases hd)))
def cl_77254 : CNF.NClause := [(17,false),(4,false),(26,true),(83,true)]
theorem der_77254 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77254 :=
  CNF.rup_sound cl_77254 [cl_30428,cl_76586] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30428 v h) (hints_cons _ _ _ (der_76586 v h) (by intro d hd; cases hd)))
def cl_77255 : CNF.NClause := [(24,true),(80,true),(29,false),(3,false)]
theorem der_77255 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77255 :=
  CNF.rup_sound cl_77255 [cl_30433,cl_43611] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30433 v h) (hints_cons _ _ _ (der_43611 v h) (by intro d hd; cases hd)))
def cl_77256 : CNF.NClause := [(3,false),(24,false),(80,true),(11,true)]
theorem der_77256 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77256 :=
  CNF.rup_sound cl_77256 [cl_30435,cl_43611] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30435 v h) (hints_cons _ _ _ (der_43611 v h) (by intro d hd; cases hd)))
def cl_77257 : CNF.NClause := [(7,false),(3,false),(80,true),(15,true)]
theorem der_77257 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77257 :=
  CNF.rup_sound cl_77257 [cl_30437,cl_76959] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30437 v h) (hints_cons _ _ _ (der_76959 v h) (by intro d hd; cases hd)))
def cl_77258 : CNF.NClause := [(9,false),(69,true),(18,false),(20,true)]
theorem der_77258 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77258 :=
  CNF.rup_sound cl_77258 [cl_30448,cl_54627] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30448 v h) (hints_cons _ _ _ (der_54627 v h) (by intro d hd; cases hd)))
def cl_77259 : CNF.NClause := [(29,false),(24,false),(80,true),(7,true)]
theorem der_77259 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77259 :=
  CNF.rup_sound cl_77259 [cl_30449,cl_77251] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30449 v h) (hints_cons _ _ _ (der_77251 v h) (by intro d hd; cases hd)))
def cl_77260 : CNF.NClause := [(80,true),(15,false),(29,true),(24,false)]
theorem der_77260 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77260 :=
  CNF.rup_sound cl_77260 [cl_30451,cl_72305] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30451 v h) (hints_cons _ _ _ (der_72305 v h) (by intro d hd; cases hd)))
def cl_77261 : CNF.NClause := [(29,false),(80,true),(15,false),(24,true)]
theorem der_77261 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77261 :=
  CNF.rup_sound cl_77261 [cl_30460,cl_62000] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30460 v h) (hints_cons _ _ _ (der_62000 v h) (by intro d hd; cases hd)))
def cl_77262 : CNF.NClause := [(7,false),(15,true),(80,true),(24,false)]
theorem der_77262 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77262 :=
  CNF.rup_sound cl_77262 [cl_30464,cl_77257] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30464 v h) (hints_cons _ _ _ (der_77257 v h) (by intro d hd; cases hd)))
def cl_77263 : CNF.NClause := [(1,false),(8,false),(76,true),(24,true)]
theorem der_77263 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77263 :=
  CNF.rup_sound cl_77263 [cl_51557,cl_63467] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51557 v h) (hints_cons _ _ _ (der_63467 v h) (by intro d hd; cases hd)))
def cl_77264 : CNF.NClause := [(29,false),(2,true),(74,true),(19,false)]
theorem der_77264 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77264 :=
  CNF.rup_sound cl_77264 [cl_30543,cl_61744] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30543 v h) (hints_cons _ _ _ (der_61744 v h) (by intro d hd; cases hd)))
def cl_77265 : CNF.NClause := [(75,true),(16,false),(9,false),(26,true)]
theorem der_77265 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77265 :=
  CNF.rup_sound cl_77265 [cl_51559,cl_49811] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51559 v h) (hints_cons _ _ _ (der_49811 v h) (by intro d hd; cases hd)))
def cl_77266 : CNF.NClause := [(26,false),(83,true),(5,false),(4,true)]
theorem der_77266 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77266 :=
  CNF.rup_sound cl_77266 [cl_30584,cl_61589] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30584 v h) (hints_cons _ _ _ (der_61589 v h) (by intro d hd; cases hd)))
def cl_77267 : CNF.NClause := [(83,true),(26,true),(17,false),(11,false)]
theorem der_77267 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77267 :=
  CNF.rup_sound cl_77267 [cl_30585,cl_62292] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30585 v h) (hints_cons _ _ _ (der_62292 v h) (by intro d hd; cases hd)))
def cl_77268 : CNF.NClause := [(4,false),(17,true),(83,true),(26,false)]
theorem der_77268 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77268 :=
  CNF.rup_sound cl_77268 [cl_30603,cl_61589] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30603 v h) (hints_cons _ _ _ (der_61589 v h) (by intro d hd; cases hd)))
def cl_77269 : CNF.NClause := [(4,false),(23,false),(83,true),(5,true)]
theorem der_77269 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77269 :=
  CNF.rup_sound cl_77269 [cl_30604,cl_54213] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30604 v h) (hints_cons _ _ _ (der_54213 v h) (by intro d hd; cases hd)))
def cl_77271 : CNF.NClause := [(10,false),(24,false),(8,true),(76,true)]
theorem der_77271 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77271 :=
  CNF.rup_sound cl_77271 [cl_30620,cl_56755] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30620 v h) (hints_cons _ _ _ (der_56755 v h) (by intro d hd; cases hd)))
def cl_77272 : CNF.NClause := [(1,false),(19,false),(71,true),(13,true)]
theorem der_77272 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77272 :=
  CNF.rup_sound cl_77272 [cl_51568,cl_61646] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51568 v h) (hints_cons _ _ _ (der_61646 v h) (by intro d hd; cases hd)))
def cl_77273 : CNF.NClause := [(45,false),(14,true),(89,false),(79,false)]
theorem der_77273 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77273 :=
  CNF.rup_sound cl_77273 [cl_51593,cl_49538] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51593 v h) (hints_cons _ _ _ (der_49538 v h) (by intro d hd; cases hd)))
def cl_77274 : CNF.NClause := [(45,false),(70,true),(89,false),(14,true)]
theorem der_77274 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77274 :=
  CNF.rup_sound cl_77274 [cl_51595,cl_51594] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51595 v h) (hints_cons _ _ _ (der_51594 v h) (by intro d hd; cases hd)))
def cl_77278 : CNF.NClause := [(70,true),(86,true),(14,true),(45,false)]
theorem der_77278 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77278 :=
  CNF.rup_sound cl_77278 [cl_51602,cl_77274] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51602 v h) (hints_cons _ _ _ (der_77274 v h) (by intro d hd; cases hd)))
def cl_77280 : CNF.NClause := [(47,false),(68,true),(66,false),(84,false)]
theorem der_77280 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77280 :=
  CNF.rup_sound cl_77280 [cl_51609,cl_77025] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51609 v h) (hints_cons _ _ _ (der_77025 v h) (by intro d hd; cases hd)))
def cl_77281 : CNF.NClause := [(47,false),(77,false),(68,true),(66,false)]
theorem der_77281 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77281 :=
  CNF.rup_sound cl_77281 [cl_51610,cl_50565] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51610 v h) (hints_cons _ _ _ (der_50565 v h) (by intro d hd; cases hd)))
def cl_77282 : CNF.NClause := [(47,false),(66,false),(16,false),(68,true)]
theorem der_77282 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77282 :=
  CNF.rup_sound cl_77282 [cl_51611,cl_77281] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51611 v h) (hints_cons _ _ _ (der_77281 v h) (by intro d hd; cases hd)))
def cl_77283 : CNF.NClause := [(47,false),(16,true),(68,true),(89,false)]
theorem der_77283 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77283 :=
  CNF.rup_sound cl_77283 [cl_51615,cl_51612] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51615 v h) (hints_cons _ _ _ (der_51612 v h) (by intro d hd; cases hd)))
def cl_77287 : CNF.NClause := [(47,false),(68,true),(84,true),(16,true)]
theorem der_77287 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77287 :=
  CNF.rup_sound cl_77287 [cl_51622,cl_77025] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51622 v h) (hints_cons _ _ _ (der_77025 v h) (by intro d hd; cases hd)))
def cl_77290 : CNF.NClause := [(47,false),(77,true),(89,false),(68,true)]
theorem der_77290 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77290 :=
  CNF.rup_sound cl_77290 [cl_51629,cl_77283] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51629 v h) (hints_cons _ _ _ (der_77283 v h) (by intro d hd; cases hd)))
def cl_77293 : CNF.NClause := [(47,false),(84,false),(68,true),(75,true)]
theorem der_77293 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77293 :=
  CNF.rup_sound cl_77293 [cl_51634,cl_77280] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51634 v h) (hints_cons _ _ _ (der_77280 v h) (by intro d hd; cases hd)))
def cl_77295 : CNF.NClause := [(52,false),(21,false),(73,false),(79,true)]
theorem der_77295 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77295 :=
  CNF.rup_sound cl_77295 [cl_51640,cl_76991] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51640 v h) (hints_cons _ _ _ (der_76991 v h) (by intro d hd; cases hd)))
def cl_77296 : CNF.NClause := [(47,false),(16,true),(75,false),(89,false)]
theorem der_77296 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77296 :=
  CNF.rup_sound cl_77296 [cl_51644,cl_51642] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51644 v h) (hints_cons _ _ _ (der_51642 v h) (by intro d hd; cases hd)))
def cl_77297 : CNF.NClause := [(47,false),(66,true),(75,false),(77,false)]
theorem der_77297 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77297 :=
  CNF.rup_sound cl_77297 [cl_51647,cl_51645] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51647 v h) (hints_cons _ _ _ (der_51645 v h) (by intro d hd; cases hd)))
def cl_77298 : CNF.NClause := [(52,false),(88,false),(73,false),(79,true)]
theorem der_77298 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77298 :=
  CNF.rup_sound cl_77298 [cl_51654,cl_77295] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51654 v h) (hints_cons _ _ _ (der_77295 v h) (by intro d hd; cases hd)))
def cl_77299 : CNF.NClause := [(52,false),(66,true),(88,false),(67,false)]
theorem der_77299 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77299 :=
  CNF.rup_sound cl_77299 [cl_51655,cl_51649] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51655 v h) (hints_cons _ _ _ (der_51649 v h) (by intro d hd; cases hd)))
def cl_77300 : CNF.NClause := [(52,false),(66,true),(67,false),(73,true)]
theorem der_77300 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77300 :=
  CNF.rup_sound cl_77300 [cl_51660,cl_77299] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51660 v h) (hints_cons _ _ _ (der_77299 v h) (by intro d hd; cases hd)))
def cl_77303 : CNF.NClause := [(65,true),(44,false),(88,false),(71,true)]
theorem der_77303 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77303 :=
  CNF.rup_sound cl_77303 [cl_51667,cl_77015] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51667 v h) (hints_cons _ _ _ (der_77015 v h) (by intro d hd; cases hd)))
def cl_77304 : CNF.NClause := [(44,false),(13,true),(78,false),(84,false)]
theorem der_77304 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77304 :=
  CNF.rup_sound cl_77304 [cl_51668,cl_49673] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51668 v h) (hints_cons _ _ _ (der_49673 v h) (by intro d hd; cases hd)))
def cl_77308 : CNF.NClause := [(44,false),(13,true),(72,false),(71,false)]
theorem der_77308 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77308 :=
  CNF.rup_sound cl_77308 [cl_51676,cl_51671] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51676 v h) (hints_cons _ _ _ (der_51671 v h) (by intro d hd; cases hd)))
def cl_77310 : CNF.NClause := [(44,false),(13,true),(71,false),(84,true)]
theorem der_77310 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77310 :=
  CNF.rup_sound cl_77310 [cl_54391,cl_54393] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_54391 v h) (hints_cons _ _ _ (der_54393 v h) (by intro d hd; cases hd)))
def cl_77311 : CNF.NClause := [(44,false),(72,true),(65,true),(71,true)]
theorem der_77311 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77311 :=
  CNF.rup_sound cl_77311 [cl_51678,cl_77015] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51678 v h) (hints_cons _ _ _ (der_77015 v h) (by intro d hd; cases hd)))
def cl_77312 : CNF.NClause := [(44,false),(84,true),(88,false),(71,false)]
theorem der_77312 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77312 :=
  CNF.rup_sound cl_77312 [cl_73630,cl_56341] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_73630 v h) (hints_cons _ _ _ (der_56341 v h) (by intro d hd; cases hd)))
def cl_77313 : CNF.NClause := [(44,false),(72,true),(88,false),(71,false)]
theorem der_77313 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77313 :=
  CNF.rup_sound cl_77313 [cl_51691,cl_56341] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51691 v h) (hints_cons _ _ _ (der_56341 v h) (by intro d hd; cases hd)))
def cl_77315 : CNF.NClause := [(44,false),(65,true),(72,false),(84,false)]
theorem der_77315 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77315 :=
  CNF.rup_sound cl_77315 [cl_51697,cl_54284] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51697 v h) (hints_cons _ _ _ (der_54284 v h) (by intro d hd; cases hd)))
def cl_77318 : CNF.NClause := [(44,false),(84,false),(71,false),(65,true)]
theorem der_77318 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77318 :=
  CNF.rup_sound cl_77318 [cl_51701,cl_77315] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51701 v h) (hints_cons _ _ _ (der_77315 v h) (by intro d hd; cases hd)))
def cl_77320 : CNF.NClause := [(44,false),(72,true),(65,true),(78,false)]
theorem der_77320 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77320 :=
  CNF.rup_sound cl_77320 [cl_51705,cl_77311] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51705 v h) (hints_cons _ _ _ (der_77311 v h) (by intro d hd; cases hd)))
def cl_77322 : CNF.NClause := [(44,false),(84,true),(72,false),(71,false)]
theorem der_77322 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77322 :=
  CNF.rup_sound cl_77322 [cl_51707,cl_51581] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51707 v h) (hints_cons _ _ _ (der_51581 v h) (by intro d hd; cases hd)))
def cl_77326 : CNF.NClause := [(49,false),(86,false),(65,true),(91,false)]
theorem der_77326 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77326 :=
  CNF.rup_sound cl_77326 [cl_51714,cl_51711] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51714 v h) (hints_cons _ _ _ (der_51711 v h) (by intro d hd; cases hd)))
def cl_77328 : CNF.NClause := [(49,false),(65,true),(69,false),(91,false)]
theorem der_77328 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77328 :=
  CNF.rup_sound cl_77328 [cl_51719,cl_51716] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51719 v h) (hints_cons _ _ _ (der_51716 v h) (by intro d hd; cases hd)))
def cl_77330 : CNF.NClause := [(49,false),(86,false),(77,false),(65,true)]
theorem der_77330 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77330 :=
  CNF.rup_sound cl_77330 [cl_51723,cl_51711] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51723 v h) (hints_cons _ _ _ (der_51711 v h) (by intro d hd; cases hd)))
def cl_77332 : CNF.NClause := [(49,false),(86,false),(65,true),(69,false)]
theorem der_77332 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77332 :=
  CNF.rup_sound cl_77332 [cl_51725,cl_77330] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51725 v h) (hints_cons _ _ _ (der_77330 v h) (by intro d hd; cases hd)))
def cl_77333 : CNF.NClause := [(49,false),(86,false),(65,true),(69,true)]
theorem der_77333 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77333 :=
  CNF.rup_sound cl_77333 [cl_51726,cl_77326] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51726 v h) (hints_cons _ _ _ (der_77326 v h) (by intro d hd; cases hd)))
def cl_77334 : CNF.NClause := [(77,false),(73,false),(49,false),(65,true)]
theorem der_77334 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77334 :=
  CNF.rup_sound cl_77334 [cl_51728,cl_51715] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51728 v h) (hints_cons _ _ _ (der_51715 v h) (by intro d hd; cases hd)))
def cl_77335 : CNF.NClause := [(77,false),(49,false),(69,false),(65,true)]
theorem der_77335 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77335 :=
  CNF.rup_sound cl_77335 [cl_51729,cl_77334] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51729 v h) (hints_cons _ _ _ (der_77334 v h) (by intro d hd; cases hd)))
def cl_77336 : CNF.NClause := [(49,false),(65,true),(69,false),(73,false)]
theorem der_77336 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77336 :=
  CNF.rup_sound cl_77336 [cl_51730,cl_77334] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51730 v h) (hints_cons _ _ _ (der_77334 v h) (by intro d hd; cases hd)))
def cl_77340 : CNF.NClause := [(107,true),(32,false),(48,true),(41,false)]
theorem der_77340 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77340 :=
  CNF.rup_sound cl_77340 [cl_30743,cl_38119] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30743 v h) (hints_cons _ _ _ (der_38119 v h) (by intro d hd; cases hd)))
def cl_77343 : CNF.NClause := [(97,true),(47,false),(42,true),(32,false)]
theorem der_77343 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77343 :=
  CNF.rup_sound cl_77343 [cl_30777,cl_57663] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30777 v h) (hints_cons _ _ _ (der_57663 v h) (by intro d hd; cases hd)))
def cl_77347 : CNF.NClause := [(52,false),(21,false),(88,false),(79,true)]
theorem der_77347 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77347 :=
  CNF.rup_sound cl_77347 [cl_51763,cl_76991] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51763 v h) (hints_cons _ _ _ (der_76991 v h) (by intro d hd; cases hd)))
def cl_77349 : CNF.NClause := [(52,false),(21,false),(79,true),(66,false)]
theorem der_77349 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77349 :=
  CNF.rup_sound cl_77349 [cl_51765,cl_76991] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51765 v h) (hints_cons _ _ _ (der_76991 v h) (by intro d hd; cases hd)))
def cl_77350 : CNF.NClause := [(49,false),(77,false),(69,false),(18,true)]
theorem der_77350 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77350 :=
  CNF.rup_sound cl_77350 [cl_36361,cl_77335] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_36361 v h) (hints_cons _ _ _ (der_77335 v h) (by intro d hd; cases hd)))
def cl_77352 : CNF.NClause := [(91,true),(69,false),(49,false),(86,false)]
theorem der_77352 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77352 :=
  CNF.rup_sound cl_77352 [cl_51772,cl_77332] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51772 v h) (hints_cons _ _ _ (der_77332 v h) (by intro d hd; cases hd)))
def cl_77354 : CNF.NClause := [(44,false),(78,false),(84,false),(71,true)]
theorem der_77354 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77354 :=
  CNF.rup_sound cl_77354 [cl_51777,cl_77304] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51777 v h) (hints_cons _ _ _ (der_77304 v h) (by intro d hd; cases hd)))
def cl_77358 : CNF.NClause := [(44,false),(72,true),(13,true),(88,false)]
theorem der_77358 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77358 :=
  CNF.rup_sound cl_77358 [cl_51788,cl_77313] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51788 v h) (hints_cons _ _ _ (der_77313 v h) (by intro d hd; cases hd)))
def cl_77359 : CNF.NClause := [(71,true),(78,true),(84,false),(44,false)]
theorem der_77359 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77359 :=
  CNF.rup_sound cl_77359 [cl_51791,cl_54284] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51791 v h) (hints_cons _ _ _ (der_54284 v h) (by intro d hd; cases hd)))
def cl_77360 : CNF.NClause := [(78,true),(64,false),(53,false),(67,false)]
theorem der_77360 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77360 :=
  CNF.rup_sound cl_77360 [cl_51807,cl_77055] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51807 v h) (hints_cons _ _ _ (der_77055 v h) (by intro d hd; cases hd)))
def cl_77361 : CNF.NClause := [(90,false),(22,true),(53,false),(67,false)]
theorem der_77361 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77361 :=
  CNF.rup_sound cl_77361 [cl_51813,cl_51812] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51813 v h) (hints_cons _ _ _ (der_51812 v h) (by intro d hd; cases hd)))
def cl_77365 : CNF.NClause := [(44,false),(72,true),(84,true),(88,false)]
theorem der_77365 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77365 :=
  CNF.rup_sound cl_77365 [cl_51825,cl_77358] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51825 v h) (hints_cons _ _ _ (der_77358 v h) (by intro d hd; cases hd)))
def cl_77367 : CNF.NClause := [(45,false),(14,true),(72,true),(89,false)]
theorem der_77367 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77367 :=
  CNF.rup_sound cl_77367 [cl_51828,cl_77274] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51828 v h) (hints_cons _ _ _ (der_77274 v h) (by intro d hd; cases hd)))
def cl_77368 : CNF.NClause := [(45,false),(14,true),(86,false),(63,false)]
theorem der_77368 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77368 :=
  CNF.rup_sound cl_77368 [cl_51829,cl_49540] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51829 v h) (hints_cons _ _ _ (der_49540 v h) (by intro d hd; cases hd)))
def cl_77369 : CNF.NClause := [(45,false),(89,true),(14,true),(63,false)]
theorem der_77369 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77369 :=
  CNF.rup_sound cl_77369 [cl_51830,cl_77368] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51830 v h) (hints_cons _ _ _ (der_77368 v h) (by intro d hd; cases hd)))
def cl_77372 : CNF.NClause := [(44,false),(71,false),(78,true),(65,false)]
theorem der_77372 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77372 :=
  CNF.rup_sound cl_77372 [cl_51836,cl_56341] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51836 v h) (hints_cons _ _ _ (der_56341 v h) (by intro d hd; cases hd)))
def cl_77373 : CNF.NClause := [(49,false),(77,true),(18,false),(86,false)]
theorem der_77373 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77373 :=
  CNF.rup_sound cl_77373 [cl_51840,cl_51760] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51840 v h) (hints_cons _ _ _ (der_51760 v h) (by intro d hd; cases hd)))
def cl_77376 : CNF.NClause := [(49,false),(77,true),(73,false),(86,false)]
theorem der_77376 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77376 :=
  CNF.rup_sound cl_77376 [cl_51848,cl_51712] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51848 v h) (hints_cons _ _ _ (der_51712 v h) (by intro d hd; cases hd)))
def cl_77380 : CNF.NClause := [(64,true),(53,false),(75,true),(22,true)]
theorem der_77380 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77380 :=
  CNF.rup_sound cl_77380 [cl_51874,cl_51873] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51874 v h) (hints_cons _ _ _ (der_51873 v h) (by intro d hd; cases hd)))
def cl_77381 : CNF.NClause := [(45,false),(79,false),(86,false),(70,true)]
theorem der_77381 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77381 :=
  CNF.rup_sound cl_77381 [cl_51891,cl_51882] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51891 v h) (hints_cons _ _ _ (der_51882 v h) (by intro d hd; cases hd)))
def cl_77383 : CNF.NClause := [(45,false),(14,true),(86,false),(79,false)]
theorem der_77383 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77383 :=
  CNF.rup_sound cl_77383 [cl_51901,cl_49538] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51901 v h) (hints_cons _ _ _ (der_49538 v h) (by intro d hd; cases hd)))
def cl_77384 : CNF.NClause := [(45,false),(14,true),(86,false),(72,false)]
theorem der_77384 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77384 :=
  CNF.rup_sound cl_77384 [cl_51902,cl_49538] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51902 v h) (hints_cons _ _ _ (der_49538 v h) (by intro d hd; cases hd)))
def cl_77385 : CNF.NClause := [(45,false),(72,true),(14,true),(86,false)]
theorem der_77385 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77385 :=
  CNF.rup_sound cl_77385 [cl_51903,cl_77383] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51903 v h) (hints_cons _ _ _ (der_77383 v h) (by intro d hd; cases hd)))
def cl_77386 : CNF.NClause := [(45,false),(86,true),(14,true),(79,false)]
theorem der_77386 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77386 :=
  CNF.rup_sound cl_77386 [cl_51904,cl_77273] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51904 v h) (hints_cons _ _ _ (der_77273 v h) (by intro d hd; cases hd)))
def cl_77387 : CNF.NClause := [(45,false),(89,true),(72,false),(14,true)]
theorem der_77387 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77387 :=
  CNF.rup_sound cl_77387 [cl_51905,cl_77384] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51905 v h) (hints_cons _ _ _ (der_77384 v h) (by intro d hd; cases hd)))
def cl_77395 : CNF.NClause := [(78,true),(90,false),(67,false),(53,false)]
theorem der_77395 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77395 :=
  CNF.rup_sound cl_77395 [cl_51961,cl_77361] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51961 v h) (hints_cons _ _ _ (der_77361 v h) (by intro d hd; cases hd)))
def cl_77396 : CNF.NClause := [(78,true),(75,true),(90,false),(53,false)]
theorem der_77396 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77396 :=
  CNF.rup_sound cl_77396 [cl_51962,cl_77395] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51962 v h) (hints_cons _ _ _ (der_77395 v h) (by intro d hd; cases hd)))
def cl_77397 : CNF.NClause := [(75,true),(67,false),(86,false),(53,false)]
theorem der_77397 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77397 :=
  CNF.rup_sound cl_77397 [cl_51965,cl_51963] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_51965 v h) (hints_cons _ _ _ (der_51963 v h) (by intro d hd; cases hd)))
def cl_77401 : CNF.NClause := [(118,true),(32,false),(34,false),(35,true)]
theorem der_77401 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77401 :=
  CNF.rup_sound cl_77401 [cl_31554,cl_64215] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31554 v h) (hints_cons _ _ _ (der_64215 v h) (by intro d hd; cases hd)))
def cl_77407 : CNF.NClause := [(103,true),(42,false),(41,true),(44,false)]
theorem der_77407 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77407 :=
  CNF.rup_sound cl_77407 [cl_31629,cl_64213] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31629 v h) (hints_cons _ _ _ (der_64213 v h) (by intro d hd; cases hd)))
def cl_77409 : CNF.NClause := [(94,true),(50,false),(55,false),(40,true)]
theorem der_77409 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77409 :=
  CNF.rup_sound cl_77409 [cl_31688,cl_57585] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31688 v h) (hints_cons _ _ _ (der_57585 v h) (by intro d hd; cases hd)))
def cl_77410 : CNF.NClause := [(94,true),(40,false),(55,false),(35,true)]
theorem der_77410 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77410 :=
  CNF.rup_sound cl_77410 [cl_31691,cl_54940] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31691 v h) (hints_cons _ _ _ (der_54940 v h) (by intro d hd; cases hd)))
def cl_77411 : CNF.NClause := [(94,true),(50,false),(55,true),(40,false)]
theorem der_77411 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77411 :=
  CNF.rup_sound cl_77411 [cl_31694,cl_54940] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31694 v h) (hints_cons _ _ _ (der_54940 v h) (by intro d hd; cases hd)))
def cl_77416 : CNF.NClause := [(102,true),(38,false),(57,false),(44,true)]
theorem der_77416 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77416 :=
  CNF.rup_sound cl_77416 [cl_31934,cl_62204] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31934 v h) (hints_cons _ _ _ (der_62204 v h) (by intro d hd; cases hd)))
def cl_77423 : CNF.NClause := [(47,false),(66,false),(84,false),(89,true)]
theorem der_77423 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77423 :=
  CNF.rup_sound cl_77423 [cl_52014,cl_77280] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52014 v h) (hints_cons _ _ _ (der_77280 v h) (by intro d hd; cases hd)))
def cl_77424 : CNF.NClause := [(113,true),(39,false),(36,false),(38,true)]
theorem der_77424 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77424 :=
  CNF.rup_sound cl_77424 [cl_64227,cl_64190] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_64227 v h) (hints_cons _ _ _ (der_64190 v h) (by intro d hd; cases hd)))
def cl_77425 : CNF.NClause := [(55,false),(24,true),(84,false),(76,false)]
theorem der_77425 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77425 :=
  CNF.rup_sound cl_77425 [cl_52017,cl_77083] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52017 v h) (hints_cons _ _ _ (der_77083 v h) (by intro d hd; cases hd)))
def cl_77426 : CNF.NClause := [(14,false),(70,true),(17,true),(28,false)]
theorem der_77426 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77426 :=
  CNF.rup_sound cl_77426 [cl_52019,cl_49773] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52019 v h) (hints_cons _ _ _ (der_49773 v h) (by intro d hd; cases hd)))
def cl_77427 : CNF.NClause := [(75,true),(9,false),(26,false),(22,true)]
theorem der_77427 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77427 :=
  CNF.rup_sound cl_77427 [cl_52020,cl_49811] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52020 v h) (hints_cons _ _ _ (der_49811 v h) (by intro d hd; cases hd)))
def cl_77431 : CNF.NClause := [(912,false),(1,true),(71,true),(7,true)]
theorem der_77431 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77431 :=
  CNF.rup_sound cl_77431 [cl_37070,cl_15879] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_37070 v h) (hints_cons _ _ _ (der_15879 v h) (by intro d hd; cases hd)))
def cl_77433 : CNF.NClause := [(907,false),(10,true),(1,true),(76,true)]
theorem der_77433 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77433 :=
  CNF.rup_sound cl_77433 [cl_37245,cl_15874] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_37245 v h) (hints_cons _ _ _ (der_15874 v h) (by intro d hd; cases hd)))
def cl_77434 : CNF.NClause := [(907,false),(10,true),(916,true),(76,true)]
theorem der_77434 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77434 :=
  CNF.rup_sound cl_77434 [cl_52031,cl_15874] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52031 v h) (hints_cons _ _ _ (der_15874 v h) (by intro d hd; cases hd)))
def cl_77436 : CNF.NClause := [(1065,false),(80,true),(1057,true),(7,true)]
theorem der_77436 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77436 :=
  CNF.rup_sound cl_77436 [cl_36073,cl_15917] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_36073 v h) (hints_cons _ _ _ (der_15917 v h) (by intro d hd; cases hd)))
def cl_77437 : CNF.NClause := [(170,false),(171,true),(77,true),(1,true)]
theorem der_77437 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77437 :=
  CNF.rup_sound cl_77437 [cl_52035,cl_13810] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52035 v h) (hints_cons _ _ _ (inp_13810 v h) (by intro d hd; cases hd)))
def cl_77438 : CNF.NClause := [(925,false),(71,true),(912,true),(7,true)]
theorem der_77438 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77438 :=
  CNF.rup_sound cl_77438 [cl_52036,cl_15891] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52036 v h) (hints_cons _ _ _ (der_15891 v h) (by intro d hd; cases hd)))
def cl_77441 : CNF.NClause := [(38,false),(80,true),(64,true),(82,false)]
theorem der_77441 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77441 :=
  CNF.rup_sound cl_77441 [cl_52040,cl_77135] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52040 v h) (hints_cons _ _ _ (der_77135 v h) (by intro d hd; cases hd)))
def cl_77442 : CNF.NClause := [(38,false),(80,true),(89,false),(82,false)]
theorem der_77442 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77442 :=
  CNF.rup_sound cl_77442 [cl_52041,cl_77441] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52041 v h) (hints_cons _ _ _ (der_77441 v h) (by intro d hd; cases hd)))
def cl_77443 : CNF.NClause := [(48,false),(107,true),(55,true),(41,false)]
theorem der_77443 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77443 :=
  CNF.rup_sound cl_77443 [cl_37761,cl_38119] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_37761 v h) (hints_cons _ _ _ (der_38119 v h) (by intro d hd; cases hd)))
def cl_77445 : CNF.NClause := [(102,true),(32,false),(51,false),(57,true)]
theorem der_77445 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77445 :=
  CNF.rup_sound cl_77445 [cl_52046,cl_76766] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52046 v h) (hints_cons _ _ _ (der_76766 v h) (by intro d hd; cases hd)))
def cl_77447 : CNF.NClause := [(116,true),(34,false),(36,false),(43,true)]
theorem der_77447 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77447 :=
  CNF.rup_sound cl_77447 [cl_52048,cl_49954] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52048 v h) (hints_cons _ _ _ (der_49954 v h) (by intro d hd; cases hd)))
def cl_77448 : CNF.NClause := [(45,false),(14,true),(89,false),(63,false)]
theorem der_77448 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77448 :=
  CNF.rup_sound cl_77448 [cl_52052,cl_77057] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52052 v h) (hints_cons _ _ _ (der_77057 v h) (by intro d hd; cases hd)))
def cl_77450 : CNF.NClause := [(84,true),(152,false),(2,true),(28,false)]
theorem der_77450 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77450 :=
  CNF.rup_sound cl_77450 [cl_57912,cl_61980] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_57912 v h) (hints_cons _ _ _ (der_61980 v h) (by intro d hd; cases hd)))
def cl_77451 : CNF.NClause := [(345,false),(8,true),(68,true),(7,true)]
theorem der_77451 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77451 :=
  CNF.rup_sound cl_77451 [cl_52053,cl_13980] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52053 v h) (hints_cons _ _ _ (inp_13980 v h) (by intro d hd; cases hd)))
def cl_77452 : CNF.NClause := [(41,false),(10,true),(74,false),(76,false)]
theorem der_77452 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77452 :=
  CNF.rup_sound cl_77452 [cl_47556,cl_51241] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_47556 v h) (hints_cons _ _ _ (der_51241 v h) (by intro d hd; cases hd)))
def cl_77453 : CNF.NClause := [(116,true),(58,false),(50,true),(34,false)]
theorem der_77453 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77453 :=
  CNF.rup_sound cl_77453 [cl_52057,cl_49847] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52057 v h) (hints_cons _ _ _ (der_49847 v h) (by intro d hd; cases hd)))
def cl_77457 : CNF.NClause := [(40,false),(9,true),(63,false),(75,false)]
theorem der_77457 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77457 :=
  CNF.rup_sound cl_77457 [cl_52064,cl_77080] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52064 v h) (hints_cons _ _ _ (der_77080 v h) (by intro d hd; cases hd)))
def cl_77464 : CNF.NClause := [(1059,true),(5,false),(1060,true),(82,true)]
theorem der_77464 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77464 :=
  CNF.rup_sound cl_77464 [cl_45928,cl_76573] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_45928 v h) (hints_cons _ _ _ (der_76573 v h) (by intro d hd; cases hd)))
def cl_77466 : CNF.NClause := [(102,true),(50,false),(51,false),(57,true)]
theorem der_77466 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77466 :=
  CNF.rup_sound cl_77466 [cl_44021,cl_66589] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_44021 v h) (hints_cons _ _ _ (der_66589 v h) (by intro d hd; cases hd)))
def cl_77467 : CNF.NClause := [(1059,false),(2,true),(84,true),(28,true)]
theorem der_77467 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77467 :=
  CNF.rup_sound cl_77467 [cl_45881,cl_76864] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_45881 v h) (hints_cons _ _ _ (der_76864 v h) (by intro d hd; cases hd)))
def cl_77468 : CNF.NClause := [(234,true),(17,false),(3,true),(70,true)]
theorem der_77468 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77468 :=
  CNF.rup_sound cl_77468 [cl_53793,cl_76621] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_53793 v h) (hints_cons _ _ _ (der_76621 v h) (by intro d hd; cases hd)))
def cl_77470 : CNF.NClause := [(134,false),(3,true),(75,true),(150,true)]
theorem der_77470 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77470 :=
  CNF.rup_sound cl_77470 [cl_52083,cl_15776] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52083 v h) (hints_cons _ _ _ (der_15776 v h) (by intro d hd; cases hd)))
def cl_77471 : CNF.NClause := [(41,false),(10,true),(75,false),(76,false)]
theorem der_77471 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77471 :=
  CNF.rup_sound cl_77471 [cl_49751,cl_77155] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49751 v h) (hints_cons _ _ _ (der_77155 v h) (by intro d hd; cases hd)))
def cl_77472 : CNF.NClause := [(33,false),(2,true),(64,false),(74,true)]
theorem der_77472 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77472 :=
  CNF.rup_sound cl_77472 [cl_49694,cl_77124] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49694 v h) (hints_cons _ _ _ (der_77124 v h) (by intro d hd; cases hd)))
def cl_77473 : CNF.NClause := [(65,false),(91,false),(18,true),(49,false)]
theorem der_77473 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77473 :=
  CNF.rup_sound cl_77473 [cl_49717,cl_50551] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49717 v h) (hints_cons _ _ _ (der_50551 v h) (by intro d hd; cases hd)))
def cl_77474 : CNF.NClause := [(241,false),(3,true),(6,true),(91,true)]
theorem der_77474 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77474 :=
  CNF.rup_sound cl_77474 [cl_52088,cl_13879] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52088 v h) (hints_cons _ _ _ (inp_13879 v h) (by intro d hd; cases hd)))
def cl_77479 : CNF.NClause := [(49,false),(65,true),(18,true),(73,false)]
theorem der_77479 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77479 :=
  CNF.rup_sound cl_77479 [cl_49712,cl_77336] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49712 v h) (hints_cons _ _ _ (der_77336 v h) (by intro d hd; cases hd)))
def cl_77481 : CNF.NClause := [(49,false),(86,false),(69,false),(18,true)]
theorem der_77481 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77481 :=
  CNF.rup_sound cl_77481 [cl_49716,cl_77352] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_49716 v h) (hints_cons _ _ _ (der_77352 v h) (by intro d hd; cases hd)))
def cl_77484 : CNF.NClause := [(50,false),(63,true),(90,false),(74,false)]
theorem der_77484 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77484 :=
  CNF.rup_sound cl_77484 [cl_54216,cl_77205] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_54216 v h) (hints_cons _ _ _ (der_77205 v h) (by intro d hd; cases hd)))
def cl_77490 : CNF.NClause := [(39,false),(65,false),(68,true),(79,false)]
theorem der_77490 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77490 :=
  CNF.rup_sound cl_77490 [cl_52095,cl_77039] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_52095 v h) (hints_cons _ _ _ (der_77039 v h) (by intro d hd; cases hd)))
def cl_77494 : CNF.NClause := [(103,true),(41,false),(43,false),(42,true)]
theorem der_77494 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77494 :=
  CNF.rup_sound cl_77494 [cl_48629,cl_64213] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_48629 v h) (hints_cons _ _ _ (der_64213 v h) (by intro d hd; cases hd)))
def cl_77495 : CNF.NClause := [(49,false),(73,true),(69,false),(86,false)]
theorem der_77495 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77495 :=
  CNF.rup_sound cl_77495 [cl_56063,cl_77352] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_56063 v h) (hints_cons _ _ _ (der_77352 v h) (by intro d hd; cases hd)))
def cl_77496 : CNF.NClause := [(140,false),(75,true),(127,true),(150,true)]
theorem der_77496 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77496 :=
  CNF.rup_sound cl_77496 [cl_56347,cl_60497] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_56347 v h) (hints_cons _ _ _ (der_60497 v h) (by intro d hd; cases hd)))
def cl_77498 : CNF.NClause := [(103,true),(45,false),(42,true),(43,false)]
theorem der_77498 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77498 :=
  CNF.rup_sound cl_77498 [cl_57712,cl_64213] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_57712 v h) (hints_cons _ _ _ (der_64213 v h) (by intro d hd; cases hd)))
def cl_77499 : CNF.NClause := [(138,false),(45,true),(89,false),(129,true)]
theorem der_77499 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77499 :=
  CNF.rup_sound cl_77499 [cl_58306,cl_76534] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_58306 v h) (hints_cons _ _ _ (der_76534 v h) (by intro d hd; cases hd)))
def cl_77502 : CNF.NClause := [(1075,false),(85,true),(19,true),(5,true)]
theorem der_77502 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77502 :=
  CNF.rup_sound cl_77502 [cl_57141,cl_15927] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_57141 v h) (hints_cons _ _ _ (der_15927 v h) (by intro d hd; cases hd)))
def cl_77503 : CNF.NClause := [(75,true),(1063,false),(1080,true),(1076,true)]
theorem der_77503 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77503 :=
  CNF.rup_sound cl_77503 [cl_55984,cl_15915] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_55984 v h) (hints_cons _ _ _ (der_15915 v h) (by intro d hd; cases hd)))
def cl_77507 : CNF.NClause := [(77,true),(1070,true),(1072,true),(18,false)]
theorem der_77507 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77507 :=
  CNF.rup_sound cl_77507 [cl_57676,cl_76608] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_57676 v h) (hints_cons _ _ _ (der_76608 v h) (by intro d hd; cases hd)))
def cl_77508 : CNF.NClause := [(927,false),(920,true),(73,true),(7,true)]
theorem der_77508 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77508 :=
  CNF.rup_sound cl_77508 [cl_56137,cl_62084] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_56137 v h) (hints_cons _ _ _ (der_62084 v h) (by intro d hd; cases hd)))
def cl_77510 : CNF.NClause := [(927,false),(73,true),(903,true),(7,true)]
theorem der_77510 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77510 :=
  CNF.rup_sound cl_77510 [cl_56490,cl_15893] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_56490 v h) (hints_cons _ _ _ (der_15893 v h) (by intro d hd; cases hd)))
def cl_77511 : CNF.NClause := [(39,false),(76,true),(82,false),(68,false)]
theorem der_77511 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77511 :=
  CNF.rup_sound cl_77511 [cl_57533,cl_50613] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_57533 v h) (hints_cons _ _ _ (der_50613 v h) (by intro d hd; cases hd)))
def cl_77513 : CNF.NClause := [(1082,false),(1065,true),(90,true),(22,true)]
theorem der_77513 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77513 :=
  CNF.rup_sound cl_77513 [cl_57200,cl_15933] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_57200 v h) (hints_cons _ _ _ (der_15933 v h) (by intro d hd; cases hd)))
def cl_77514 : CNF.NClause := [(1076,false),(1071,true),(1061,true),(64,true)]
theorem der_77514 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77514 :=
  CNF.rup_sound cl_77514 [cl_56497,cl_15928] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_56497 v h) (hints_cons _ _ _ (der_15928 v h) (by intro d hd; cases hd)))
def cl_77517 : CNF.NClause := [(4,false),(5,false),(11,true),(83,true)]
theorem der_77517 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77517 :=
  CNF.rup_sound cl_77517 [cl_60488,cl_54211] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_60488 v h) (hints_cons _ _ _ (der_54211 v h) (by intro d hd; cases hd)))
def cl_77519 : CNF.NClause := [(16,false),(140,true),(147,true),(89,true)]
theorem der_77519 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77519 :=
  CNF.rup_sound cl_77519 [cl_63439,cl_76599] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_63439 v h) (hints_cons _ _ _ (der_76599 v h) (by intro d hd; cases hd)))
def cl_77526 : CNF.NClause := [(17,false),(26,false),(11,true),(83,true)]
theorem der_77526 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_77526 :=
  CNF.rup_sound cl_77526 [cl_63367,cl_77238] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_63367 v h) (hints_cons _ _ _ (der_77238 v h) (by intro d hd; cases hd)))
def chunk075 : List CNF.NClause := [cl_76662,cl_76663,cl_76664,cl_76665,cl_76667,cl_76668,cl_76669,cl_76670,cl_76671,cl_76672,cl_76673,cl_76675,cl_76677,cl_76678,cl_76679,cl_76680,cl_76681,cl_76682,cl_76683,cl_76684,cl_76685,cl_76686,cl_76687,cl_76688,cl_76689,cl_76690,cl_76691,cl_76692,cl_76693,cl_76694,cl_76695,cl_76696,cl_76697,cl_76698,cl_76699,cl_76700,cl_76701,cl_76702,cl_76703,cl_76704,cl_76705,cl_76706,cl_76707,cl_76708,cl_76709,cl_76710,cl_76711,cl_76712,cl_76713,cl_76714,cl_76715,cl_76716,cl_76717,cl_76718,cl_76719,cl_76720,cl_76721,cl_76722,cl_76723,cl_76724,cl_76725,cl_76726,cl_76727,cl_76729,cl_76730,cl_76731,cl_76732,cl_76733,cl_76734,cl_76735,cl_76736,cl_76737,cl_76738,cl_76739,cl_76740,cl_76741,cl_76742,cl_76743,cl_76744,cl_76745,cl_76746,cl_76747,cl_76748,cl_76749,cl_76750,cl_76751,cl_76752,cl_76753,cl_76754,cl_76755,cl_76756,cl_76757,cl_76758,cl_76759,cl_76760,cl_76761,cl_76763,cl_76764,cl_76765,cl_76766,cl_76767,cl_76768,cl_76769,cl_76770,cl_76771,cl_76772,cl_76773,cl_76774,cl_76775,cl_76776,cl_76777,cl_76778,cl_76779,cl_76780,cl_76781,cl_76783,cl_76784,cl_76785,cl_76787,cl_76788,cl_76789,cl_76791,cl_76792,cl_76793,cl_76794,cl_76795,cl_76796,cl_76805,cl_76806,cl_76807,cl_76808,cl_76812,cl_76817,cl_76819,cl_76820,cl_76824,cl_76827,cl_76830,cl_76831,cl_76832,cl_76833,cl_76836,cl_76837,cl_76838,cl_76840,cl_76841,cl_76842,cl_76846,cl_76847,cl_76849,cl_76850,cl_76852,cl_76855,cl_76857,cl_76864,cl_76865,cl_76866,cl_76867,cl_76868,cl_76870,cl_76871,cl_76874,cl_76875,cl_76876,cl_76877,cl_76879,cl_76881,cl_76882,cl_76887,cl_76888,cl_76889,cl_76890,cl_76892,cl_76893,cl_76895,cl_76898,cl_76899,cl_76901,cl_76902,cl_76904,cl_76912,cl_76915,cl_76916,cl_76917,cl_76918,cl_76920,cl_76922,cl_76923,cl_76925,cl_76926,cl_76929,cl_76930,cl_76931,cl_76935,cl_76940,cl_76942,cl_76944,cl_76949,cl_76952,cl_76959,cl_76960,cl_76961,cl_76963,cl_76964,cl_76965,cl_76968,cl_76969,cl_76971,cl_76973,cl_76975,cl_76977,cl_76978,cl_76981,cl_76982,cl_76983,cl_76985,cl_76988,cl_76991,cl_76994,cl_76996,cl_76998,cl_76999,cl_77000,cl_77003,cl_77007,cl_77008,cl_77009,cl_77011,cl_77014,cl_77015,cl_77016,cl_77020,cl_77021,cl_77025,cl_77028,cl_77029,cl_77030,cl_77031,cl_77032,cl_77033,cl_77034,cl_77036,cl_77037,cl_77039,cl_77041,cl_77042,cl_77043,cl_77044,cl_77045,cl_77046,cl_77047,cl_77048,cl_77050,cl_77051,cl_77053,cl_77055,cl_77056,cl_77057,cl_77058,cl_77059,cl_77061,cl_77063,cl_77064,cl_77065,cl_77066,cl_77069,cl_77070,cl_77072,cl_77073,cl_77074,cl_77075,cl_77076,cl_77077,cl_77078,cl_77080,cl_77081,cl_77082,cl_77083,cl_77084,cl_77086,cl_77092,cl_77093,cl_77098,cl_77099,cl_77102,cl_77104,cl_77105,cl_77108,cl_77109,cl_77111,cl_77112,cl_77113,cl_77114,cl_77116,cl_77117,cl_77118,cl_77119,cl_77120,cl_77122,cl_77124,cl_77125,cl_77127,cl_77131,cl_77132,cl_77133,cl_77134,cl_77135,cl_77136,cl_77137,cl_77138,cl_77139,cl_77141,cl_77142,cl_77143,cl_77151,cl_77152,cl_77153,cl_77154,cl_77155,cl_77156,cl_77157,cl_77158,cl_77159,cl_77161,cl_77163,cl_77164,cl_77167,cl_77168,cl_77170,cl_77172,cl_77173,cl_77177,cl_77178,cl_77182,cl_77184,cl_77189,cl_77191,cl_77192,cl_77195,cl_77196,cl_77198,cl_77199,cl_77201,cl_77202,cl_77204,cl_77205,cl_77206,cl_77216,cl_77217,cl_77226,cl_77228,cl_77236,cl_77237,cl_77238,cl_77239,cl_77240,cl_77242,cl_77243,cl_77248,cl_77250,cl_77251,cl_77253,cl_77254,cl_77255,cl_77256,cl_77257,cl_77258,cl_77259,cl_77260,cl_77261,cl_77262,cl_77263,cl_77264,cl_77265,cl_77266,cl_77267,cl_77268,cl_77269,cl_77271,cl_77272,cl_77273,cl_77274,cl_77278,cl_77280,cl_77281,cl_77282,cl_77283,cl_77287,cl_77290,cl_77293,cl_77295,cl_77296,cl_77297,cl_77298,cl_77299,cl_77300,cl_77303,cl_77304,cl_77308,cl_77310,cl_77311,cl_77312,cl_77313,cl_77315,cl_77318,cl_77320,cl_77322,cl_77326,cl_77328,cl_77330,cl_77332,cl_77333,cl_77334,cl_77335,cl_77336,cl_77340,cl_77343,cl_77347,cl_77349,cl_77350,cl_77352,cl_77354,cl_77358,cl_77359,cl_77360,cl_77361,cl_77365,cl_77367,cl_77368,cl_77369,cl_77372,cl_77373,cl_77376,cl_77380,cl_77381,cl_77383,cl_77384,cl_77385,cl_77386,cl_77387,cl_77395,cl_77396,cl_77397,cl_77401,cl_77407,cl_77409,cl_77410,cl_77411,cl_77416,cl_77423,cl_77424,cl_77425,cl_77426,cl_77427,cl_77431,cl_77433,cl_77434,cl_77436,cl_77437,cl_77438,cl_77441,cl_77442,cl_77443,cl_77445,cl_77447,cl_77448,cl_77450,cl_77451,cl_77452,cl_77453,cl_77457,cl_77464,cl_77466,cl_77467,cl_77468,cl_77470,cl_77471,cl_77472,cl_77473,cl_77474,cl_77479,cl_77481,cl_77484,cl_77490,cl_77494,cl_77495,cl_77496,cl_77498,cl_77499,cl_77502,cl_77503,cl_77507,cl_77508,cl_77510,cl_77511,cl_77513,cl_77514,cl_77517,cl_77519,cl_77526]
theorem chunk_sound075 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : ∀ c ∈ chunk075, CNF.Holds (v ∘ decodeVar) c :=
  (hints_cons _ _ _ (der_76662 v h) (hints_cons _ _ _ (der_76663 v h) (hints_cons _ _ _ (der_76664 v h) (hints_cons _ _ _ (der_76665 v h) (hints_cons _ _ _ (der_76667 v h) (hints_cons _ _ _ (der_76668 v h) (hints_cons _ _ _ (der_76669 v h) (hints_cons _ _ _ (der_76670 v h) (hints_cons _ _ _ (der_76671 v h) (hints_cons _ _ _ (der_76672 v h) (hints_cons _ _ _ (der_76673 v h) (hints_cons _ _ _ (der_76675 v h) (hints_cons _ _ _ (der_76677 v h) (hints_cons _ _ _ (der_76678 v h) (hints_cons _ _ _ (der_76679 v h) (hints_cons _ _ _ (der_76680 v h) (hints_cons _ _ _ (der_76681 v h) (hints_cons _ _ _ (der_76682 v h) (hints_cons _ _ _ (der_76683 v h) (hints_cons _ _ _ (der_76684 v h) (hints_cons _ _ _ (der_76685 v h) (hints_cons _ _ _ (der_76686 v h) (hints_cons _ _ _ (der_76687 v h) (hints_cons _ _ _ (der_76688 v h) (hints_cons _ _ _ (der_76689 v h) (hints_cons _ _ _ (der_76690 v h) (hints_cons _ _ _ (der_76691 v h) (hints_cons _ _ _ (der_76692 v h) (hints_cons _ _ _ (der_76693 v h) (hints_cons _ _ _ (der_76694 v h) (hints_cons _ _ _ (der_76695 v h) (hints_cons _ _ _ (der_76696 v h) (hints_cons _ _ _ (der_76697 v h) (hints_cons _ _ _ (der_76698 v h) (hints_cons _ _ _ (der_76699 v h) (hints_cons _ _ _ (der_76700 v h) (hints_cons _ _ _ (der_76701 v h) (hints_cons _ _ _ (der_76702 v h) (hints_cons _ _ _ (der_76703 v h) (hints_cons _ _ _ (der_76704 v h) (hints_cons _ _ _ (der_76705 v h) (hints_cons _ _ _ (der_76706 v h) (hints_cons _ _ _ (der_76707 v h) (hints_cons _ _ _ (der_76708 v h) (hints_cons _ _ _ (der_76709 v h) (hints_cons _ _ _ (der_76710 v h) (hints_cons _ _ _ (der_76711 v h) (hints_cons _ _ _ (der_76712 v h) (hints_cons _ _ _ (der_76713 v h) (hints_cons _ _ _ (der_76714 v h) (hints_cons _ _ _ (der_76715 v h) (hints_cons _ _ _ (der_76716 v h) (hints_cons _ _ _ (der_76717 v h) (hints_cons _ _ _ (der_76718 v h) (hints_cons _ _ _ (der_76719 v h) (hints_cons _ _ _ (der_76720 v h) (hints_cons _ _ _ (der_76721 v h) (hints_cons _ _ _ (der_76722 v h) (hints_cons _ _ _ (der_76723 v h) (hints_cons _ _ _ (der_76724 v h) (hints_cons _ _ _ (der_76725 v h) (hints_cons _ _ _ (der_76726 v h) (hints_cons _ _ _ (der_76727 v h) (hints_cons _ _ _ (der_76729 v h) (hints_cons _ _ _ (der_76730 v h) (hints_cons _ _ _ (der_76731 v h) (hints_cons _ _ _ (der_76732 v h) (hints_cons _ _ _ (der_76733 v h) (hints_cons _ _ _ (der_76734 v h) (hints_cons _ _ _ (der_76735 v h) (hints_cons _ _ _ (der_76736 v h) (hints_cons _ _ _ (der_76737 v h) (hints_cons _ _ _ (der_76738 v h) (hints_cons _ _ _ (der_76739 v h) (hints_cons _ _ _ (der_76740 v h) (hints_cons _ _ _ (der_76741 v h) (hints_cons _ _ _ (der_76742 v h) (hints_cons _ _ _ (der_76743 v h) (hints_cons _ _ _ (der_76744 v h) (hints_cons _ _ _ (der_76745 v h) (hints_cons _ _ _ (der_76746 v h) (hints_cons _ _ _ (der_76747 v h) (hints_cons _ _ _ (der_76748 v h) (hints_cons _ _ _ (der_76749 v h) (hints_cons _ _ _ (der_76750 v h) (hints_cons _ _ _ (der_76751 v h) (hints_cons _ _ _ (der_76752 v h) (hints_cons _ _ _ (der_76753 v h) (hints_cons _ _ _ (der_76754 v h) (hints_cons _ _ _ (der_76755 v h) (hints_cons _ _ _ (der_76756 v h) (hints_cons _ _ _ (der_76757 v h) (hints_cons _ _ _ (der_76758 v h) (hints_cons _ _ _ (der_76759 v h) (hints_cons _ _ _ (der_76760 v h) (hints_cons _ _ _ (der_76761 v h) (hints_cons _ _ _ (der_76763 v h) (hints_cons _ _ _ (der_76764 v h) (hints_cons _ _ _ (der_76765 v h) (hints_cons _ _ _ (der_76766 v h) (hints_cons _ _ _ (der_76767 v h) (hints_cons _ _ _ (der_76768 v h) (hints_cons _ _ _ (der_76769 v h) (hints_cons _ _ _ (der_76770 v h) (hints_cons _ _ _ (der_76771 v h) (hints_cons _ _ _ (der_76772 v h) (hints_cons _ _ _ (der_76773 v h) (hints_cons _ _ _ (der_76774 v h) (hints_cons _ _ _ (der_76775 v h) (hints_cons _ _ _ (der_76776 v h) (hints_cons _ _ _ (der_76777 v h) (hints_cons _ _ _ (der_76778 v h) (hints_cons _ _ _ (der_76779 v h) (hints_cons _ _ _ (der_76780 v h) (hints_cons _ _ _ (der_76781 v h) (hints_cons _ _ _ (der_76783 v h) (hints_cons _ _ _ (der_76784 v h) (hints_cons _ _ _ (der_76785 v h) (hints_cons _ _ _ (der_76787 v h) (hints_cons _ _ _ (der_76788 v h) (hints_cons _ _ _ (der_76789 v h) (hints_cons _ _ _ (der_76791 v h) (hints_cons _ _ _ (der_76792 v h) (hints_cons _ _ _ (der_76793 v h) (hints_cons _ _ _ (der_76794 v h) (hints_cons _ _ _ (der_76795 v h) (hints_cons _ _ _ (der_76796 v h) (hints_cons _ _ _ (der_76805 v h) (hints_cons _ _ _ (der_76806 v h) (hints_cons _ _ _ (der_76807 v h) (hints_cons _ _ _ (der_76808 v h) (hints_cons _ _ _ (der_76812 v h) (hints_cons _ _ _ (der_76817 v h) (hints_cons _ _ _ (der_76819 v h) (hints_cons _ _ _ (der_76820 v h) (hints_cons _ _ _ (der_76824 v h) (hints_cons _ _ _ (der_76827 v h) (hints_cons _ _ _ (der_76830 v h) (hints_cons _ _ _ (der_76831 v h) (hints_cons _ _ _ (der_76832 v h) (hints_cons _ _ _ (der_76833 v h) (hints_cons _ _ _ (der_76836 v h) (hints_cons _ _ _ (der_76837 v h) (hints_cons _ _ _ (der_76838 v h) (hints_cons _ _ _ (der_76840 v h) (hints_cons _ _ _ (der_76841 v h) (hints_cons _ _ _ (der_76842 v h) (hints_cons _ _ _ (der_76846 v h) (hints_cons _ _ _ (der_76847 v h) (hints_cons _ _ _ (der_76849 v h) (hints_cons _ _ _ (der_76850 v h) (hints_cons _ _ _ (der_76852 v h) (hints_cons _ _ _ (der_76855 v h) (hints_cons _ _ _ (der_76857 v h) (hints_cons _ _ _ (der_76864 v h) (hints_cons _ _ _ (der_76865 v h) (hints_cons _ _ _ (der_76866 v h) (hints_cons _ _ _ (der_76867 v h) (hints_cons _ _ _ (der_76868 v h) (hints_cons _ _ _ (der_76870 v h) (hints_cons _ _ _ (der_76871 v h) (hints_cons _ _ _ (der_76874 v h) (hints_cons _ _ _ (der_76875 v h) (hints_cons _ _ _ (der_76876 v h) (hints_cons _ _ _ (der_76877 v h) (hints_cons _ _ _ (der_76879 v h) (hints_cons _ _ _ (der_76881 v h) (hints_cons _ _ _ (der_76882 v h) (hints_cons _ _ _ (der_76887 v h) (hints_cons _ _ _ (der_76888 v h) (hints_cons _ _ _ (der_76889 v h) (hints_cons _ _ _ (der_76890 v h) (hints_cons _ _ _ (der_76892 v h) (hints_cons _ _ _ (der_76893 v h) (hints_cons _ _ _ (der_76895 v h) (hints_cons _ _ _ (der_76898 v h) (hints_cons _ _ _ (der_76899 v h) (hints_cons _ _ _ (der_76901 v h) (hints_cons _ _ _ (der_76902 v h) (hints_cons _ _ _ (der_76904 v h) (hints_cons _ _ _ (der_76912 v h) (hints_cons _ _ _ (der_76915 v h) (hints_cons _ _ _ (der_76916 v h) (hints_cons _ _ _ (der_76917 v h) (hints_cons _ _ _ (der_76918 v h) (hints_cons _ _ _ (der_76920 v h) (hints_cons _ _ _ (der_76922 v h) (hints_cons _ _ _ (der_76923 v h) (hints_cons _ _ _ (der_76925 v h) (hints_cons _ _ _ (der_76926 v h) (hints_cons _ _ _ (der_76929 v h) (hints_cons _ _ _ (der_76930 v h) (hints_cons _ _ _ (der_76931 v h) (hints_cons _ _ _ (der_76935 v h) (hints_cons _ _ _ (der_76940 v h) (hints_cons _ _ _ (der_76942 v h) (hints_cons _ _ _ (der_76944 v h) (hints_cons _ _ _ (der_76949 v h) (hints_cons _ _ _ (der_76952 v h) (hints_cons _ _ _ (der_76959 v h) (hints_cons _ _ _ (der_76960 v h) (hints_cons _ _ _ (der_76961 v h) (hints_cons _ _ _ (der_76963 v h) (hints_cons _ _ _ (der_76964 v h) (hints_cons _ _ _ (der_76965 v h) (hints_cons _ _ _ (der_76968 v h) (hints_cons _ _ _ (der_76969 v h) (hints_cons _ _ _ (der_76971 v h) (hints_cons _ _ _ (der_76973 v h) (hints_cons _ _ _ (der_76975 v h) (hints_cons _ _ _ (der_76977 v h) (hints_cons _ _ _ (der_76978 v h) (hints_cons _ _ _ (der_76981 v h) (hints_cons _ _ _ (der_76982 v h) (hints_cons _ _ _ (der_76983 v h) (hints_cons _ _ _ (der_76985 v h) (hints_cons _ _ _ (der_76988 v h) (hints_cons _ _ _ (der_76991 v h) (hints_cons _ _ _ (der_76994 v h) (hints_cons _ _ _ (der_76996 v h) (hints_cons _ _ _ (der_76998 v h) (hints_cons _ _ _ (der_76999 v h) (hints_cons _ _ _ (der_77000 v h) (hints_cons _ _ _ (der_77003 v h) (hints_cons _ _ _ (der_77007 v h) (hints_cons _ _ _ (der_77008 v h) (hints_cons _ _ _ (der_77009 v h) (hints_cons _ _ _ (der_77011 v h) (hints_cons _ _ _ (der_77014 v h) (hints_cons _ _ _ (der_77015 v h) (hints_cons _ _ _ (der_77016 v h) (hints_cons _ _ _ (der_77020 v h) (hints_cons _ _ _ (der_77021 v h) (hints_cons _ _ _ (der_77025 v h) (hints_cons _ _ _ (der_77028 v h) (hints_cons _ _ _ (der_77029 v h) (hints_cons _ _ _ (der_77030 v h) (hints_cons _ _ _ (der_77031 v h) (hints_cons _ _ _ (der_77032 v h) (hints_cons _ _ _ (der_77033 v h) (hints_cons _ _ _ (der_77034 v h) (hints_cons _ _ _ (der_77036 v h) (hints_cons _ _ _ (der_77037 v h) (hints_cons _ _ _ (der_77039 v h) (hints_cons _ _ _ (der_77041 v h) (hints_cons _ _ _ (der_77042 v h) (hints_cons _ _ _ (der_77043 v h) (hints_cons _ _ _ (der_77044 v h) (hints_cons _ _ _ (der_77045 v h) (hints_cons _ _ _ (der_77046 v h) (hints_cons _ _ _ (der_77047 v h) (hints_cons _ _ _ (der_77048 v h) (hints_cons _ _ _ (der_77050 v h) (hints_cons _ _ _ (der_77051 v h) (hints_cons _ _ _ (der_77053 v h) (hints_cons _ _ _ (der_77055 v h) (hints_cons _ _ _ (der_77056 v h) (hints_cons _ _ _ (der_77057 v h) (hints_cons _ _ _ (der_77058 v h) (hints_cons _ _ _ (der_77059 v h) (hints_cons _ _ _ (der_77061 v h) (hints_cons _ _ _ (der_77063 v h) (hints_cons _ _ _ (der_77064 v h) (hints_cons _ _ _ (der_77065 v h) (hints_cons _ _ _ (der_77066 v h) (hints_cons _ _ _ (der_77069 v h) (hints_cons _ _ _ (der_77070 v h) (hints_cons _ _ _ (der_77072 v h) (hints_cons _ _ _ (der_77073 v h) (hints_cons _ _ _ (der_77074 v h) (hints_cons _ _ _ (der_77075 v h) (hints_cons _ _ _ (der_77076 v h) (hints_cons _ _ _ (der_77077 v h) (hints_cons _ _ _ (der_77078 v h) (hints_cons _ _ _ (der_77080 v h) (hints_cons _ _ _ (der_77081 v h) (hints_cons _ _ _ (der_77082 v h) (hints_cons _ _ _ (der_77083 v h) (hints_cons _ _ _ (der_77084 v h) (hints_cons _ _ _ (der_77086 v h) (hints_cons _ _ _ (der_77092 v h) (hints_cons _ _ _ (der_77093 v h) (hints_cons _ _ _ (der_77098 v h) (hints_cons _ _ _ (der_77099 v h) (hints_cons _ _ _ (der_77102 v h) (hints_cons _ _ _ (der_77104 v h) (hints_cons _ _ _ (der_77105 v h) (hints_cons _ _ _ (der_77108 v h) (hints_cons _ _ _ (der_77109 v h) (hints_cons _ _ _ (der_77111 v h) (hints_cons _ _ _ (der_77112 v h) (hints_cons _ _ _ (der_77113 v h) (hints_cons _ _ _ (der_77114 v h) (hints_cons _ _ _ (der_77116 v h) (hints_cons _ _ _ (der_77117 v h) (hints_cons _ _ _ (der_77118 v h) (hints_cons _ _ _ (der_77119 v h) (hints_cons _ _ _ (der_77120 v h) (hints_cons _ _ _ (der_77122 v h) (hints_cons _ _ _ (der_77124 v h) (hints_cons _ _ _ (der_77125 v h) (hints_cons _ _ _ (der_77127 v h) (hints_cons _ _ _ (der_77131 v h) (hints_cons _ _ _ (der_77132 v h) (hints_cons _ _ _ (der_77133 v h) (hints_cons _ _ _ (der_77134 v h) (hints_cons _ _ _ (der_77135 v h) (hints_cons _ _ _ (der_77136 v h) (hints_cons _ _ _ (der_77137 v h) (hints_cons _ _ _ (der_77138 v h) (hints_cons _ _ _ (der_77139 v h) (hints_cons _ _ _ (der_77141 v h) (hints_cons _ _ _ (der_77142 v h) (hints_cons _ _ _ (der_77143 v h) (hints_cons _ _ _ (der_77151 v h) (hints_cons _ _ _ (der_77152 v h) (hints_cons _ _ _ (der_77153 v h) (hints_cons _ _ _ (der_77154 v h) (hints_cons _ _ _ (der_77155 v h) (hints_cons _ _ _ (der_77156 v h) (hints_cons _ _ _ (der_77157 v h) (hints_cons _ _ _ (der_77158 v h) (hints_cons _ _ _ (der_77159 v h) (hints_cons _ _ _ (der_77161 v h) (hints_cons _ _ _ (der_77163 v h) (hints_cons _ _ _ (der_77164 v h) (hints_cons _ _ _ (der_77167 v h) (hints_cons _ _ _ (der_77168 v h) (hints_cons _ _ _ (der_77170 v h) (hints_cons _ _ _ (der_77172 v h) (hints_cons _ _ _ (der_77173 v h) (hints_cons _ _ _ (der_77177 v h) (hints_cons _ _ _ (der_77178 v h) (hints_cons _ _ _ (der_77182 v h) (hints_cons _ _ _ (der_77184 v h) (hints_cons _ _ _ (der_77189 v h) (hints_cons _ _ _ (der_77191 v h) (hints_cons _ _ _ (der_77192 v h) (hints_cons _ _ _ (der_77195 v h) (hints_cons _ _ _ (der_77196 v h) (hints_cons _ _ _ (der_77198 v h) (hints_cons _ _ _ (der_77199 v h) (hints_cons _ _ _ (der_77201 v h) (hints_cons _ _ _ (der_77202 v h) (hints_cons _ _ _ (der_77204 v h) (hints_cons _ _ _ (der_77205 v h) (hints_cons _ _ _ (der_77206 v h) (hints_cons _ _ _ (der_77216 v h) (hints_cons _ _ _ (der_77217 v h) (hints_cons _ _ _ (der_77226 v h) (hints_cons _ _ _ (der_77228 v h) (hints_cons _ _ _ (der_77236 v h) (hints_cons _ _ _ (der_77237 v h) (hints_cons _ _ _ (der_77238 v h) (hints_cons _ _ _ (der_77239 v h) (hints_cons _ _ _ (der_77240 v h) (hints_cons _ _ _ (der_77242 v h) (hints_cons _ _ _ (der_77243 v h) (hints_cons _ _ _ (der_77248 v h) (hints_cons _ _ _ (der_77250 v h) (hints_cons _ _ _ (der_77251 v h) (hints_cons _ _ _ (der_77253 v h) (hints_cons _ _ _ (der_77254 v h) (hints_cons _ _ _ (der_77255 v h) (hints_cons _ _ _ (der_77256 v h) (hints_cons _ _ _ (der_77257 v h) (hints_cons _ _ _ (der_77258 v h) (hints_cons _ _ _ (der_77259 v h) (hints_cons _ _ _ (der_77260 v h) (hints_cons _ _ _ (der_77261 v h) (hints_cons _ _ _ (der_77262 v h) (hints_cons _ _ _ (der_77263 v h) (hints_cons _ _ _ (der_77264 v h) (hints_cons _ _ _ (der_77265 v h) (hints_cons _ _ _ (der_77266 v h) (hints_cons _ _ _ (der_77267 v h) (hints_cons _ _ _ (der_77268 v h) (hints_cons _ _ _ (der_77269 v h) (hints_cons _ _ _ (der_77271 v h) (hints_cons _ _ _ (der_77272 v h) (hints_cons _ _ _ (der_77273 v h) (hints_cons _ _ _ (der_77274 v h) (hints_cons _ _ _ (der_77278 v h) (hints_cons _ _ _ (der_77280 v h) (hints_cons _ _ _ (der_77281 v h) (hints_cons _ _ _ (der_77282 v h) (hints_cons _ _ _ (der_77283 v h) (hints_cons _ _ _ (der_77287 v h) (hints_cons _ _ _ (der_77290 v h) (hints_cons _ _ _ (der_77293 v h) (hints_cons _ _ _ (der_77295 v h) (hints_cons _ _ _ (der_77296 v h) (hints_cons _ _ _ (der_77297 v h) (hints_cons _ _ _ (der_77298 v h) (hints_cons _ _ _ (der_77299 v h) (hints_cons _ _ _ (der_77300 v h) (hints_cons _ _ _ (der_77303 v h) (hints_cons _ _ _ (der_77304 v h) (hints_cons _ _ _ (der_77308 v h) (hints_cons _ _ _ (der_77310 v h) (hints_cons _ _ _ (der_77311 v h) (hints_cons _ _ _ (der_77312 v h) (hints_cons _ _ _ (der_77313 v h) (hints_cons _ _ _ (der_77315 v h) (hints_cons _ _ _ (der_77318 v h) (hints_cons _ _ _ (der_77320 v h) (hints_cons _ _ _ (der_77322 v h) (hints_cons _ _ _ (der_77326 v h) (hints_cons _ _ _ (der_77328 v h) (hints_cons _ _ _ (der_77330 v h) (hints_cons _ _ _ (der_77332 v h) (hints_cons _ _ _ (der_77333 v h) (hints_cons _ _ _ (der_77334 v h) (hints_cons _ _ _ (der_77335 v h) (hints_cons _ _ _ (der_77336 v h) (hints_cons _ _ _ (der_77340 v h) (hints_cons _ _ _ (der_77343 v h) (hints_cons _ _ _ (der_77347 v h) (hints_cons _ _ _ (der_77349 v h) (hints_cons _ _ _ (der_77350 v h) (hints_cons _ _ _ (der_77352 v h) (hints_cons _ _ _ (der_77354 v h) (hints_cons _ _ _ (der_77358 v h) (hints_cons _ _ _ (der_77359 v h) (hints_cons _ _ _ (der_77360 v h) (hints_cons _ _ _ (der_77361 v h) (hints_cons _ _ _ (der_77365 v h) (hints_cons _ _ _ (der_77367 v h) (hints_cons _ _ _ (der_77368 v h) (hints_cons _ _ _ (der_77369 v h) (hints_cons _ _ _ (der_77372 v h) (hints_cons _ _ _ (der_77373 v h) (hints_cons _ _ _ (der_77376 v h) (hints_cons _ _ _ (der_77380 v h) (hints_cons _ _ _ (der_77381 v h) (hints_cons _ _ _ (der_77383 v h) (hints_cons _ _ _ (der_77384 v h) (hints_cons _ _ _ (der_77385 v h) (hints_cons _ _ _ (der_77386 v h) (hints_cons _ _ _ (der_77387 v h) (hints_cons _ _ _ (der_77395 v h) (hints_cons _ _ _ (der_77396 v h) (hints_cons _ _ _ (der_77397 v h) (hints_cons _ _ _ (der_77401 v h) (hints_cons _ _ _ (der_77407 v h) (hints_cons _ _ _ (der_77409 v h) (hints_cons _ _ _ (der_77410 v h) (hints_cons _ _ _ (der_77411 v h) (hints_cons _ _ _ (der_77416 v h) (hints_cons _ _ _ (der_77423 v h) (hints_cons _ _ _ (der_77424 v h) (hints_cons _ _ _ (der_77425 v h) (hints_cons _ _ _ (der_77426 v h) (hints_cons _ _ _ (der_77427 v h) (hints_cons _ _ _ (der_77431 v h) (hints_cons _ _ _ (der_77433 v h) (hints_cons _ _ _ (der_77434 v h) (hints_cons _ _ _ (der_77436 v h) (hints_cons _ _ _ (der_77437 v h) (hints_cons _ _ _ (der_77438 v h) (hints_cons _ _ _ (der_77441 v h) (hints_cons _ _ _ (der_77442 v h) (hints_cons _ _ _ (der_77443 v h) (hints_cons _ _ _ (der_77445 v h) (hints_cons _ _ _ (der_77447 v h) (hints_cons _ _ _ (der_77448 v h) (hints_cons _ _ _ (der_77450 v h) (hints_cons _ _ _ (der_77451 v h) (hints_cons _ _ _ (der_77452 v h) (hints_cons _ _ _ (der_77453 v h) (hints_cons _ _ _ (der_77457 v h) (hints_cons _ _ _ (der_77464 v h) (hints_cons _ _ _ (der_77466 v h) (hints_cons _ _ _ (der_77467 v h) (hints_cons _ _ _ (der_77468 v h) (hints_cons _ _ _ (der_77470 v h) (hints_cons _ _ _ (der_77471 v h) (hints_cons _ _ _ (der_77472 v h) (hints_cons _ _ _ (der_77473 v h) (hints_cons _ _ _ (der_77474 v h) (hints_cons _ _ _ (der_77479 v h) (hints_cons _ _ _ (der_77481 v h) (hints_cons _ _ _ (der_77484 v h) (hints_cons _ _ _ (der_77490 v h) (hints_cons _ _ _ (der_77494 v h) (hints_cons _ _ _ (der_77495 v h) (hints_cons _ _ _ (der_77496 v h) (hints_cons _ _ _ (der_77498 v h) (hints_cons _ _ _ (der_77499 v h) (hints_cons _ _ _ (der_77502 v h) (hints_cons _ _ _ (der_77503 v h) (hints_cons _ _ _ (der_77507 v h) (hints_cons _ _ _ (der_77508 v h) (hints_cons _ _ _ (der_77510 v h) (hints_cons _ _ _ (der_77511 v h) (hints_cons _ _ _ (der_77513 v h) (hints_cons _ _ _ (der_77514 v h) (hints_cons _ _ _ (der_77517 v h) (hints_cons _ _ _ (der_77519 v h) (hints_cons _ _ _ (der_77526 v h) (by intro d hd; cases hd)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def prefix075 := prefix074 ++ chunk075
theorem prefix_sound075 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : ∀ c ∈ prefix075, CNF.Holds (v ∘ decodeVar) c := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact prefix_sound074 v h c hc
  · exact chunk_sound075 v h c hc
end Percolation.NReplay
